// SSA Conversion Implementation
export const convertToSSA = (ast) => {
  const ssa = [];
  const variables = {};
  const phi = [];

  // Helper to create a new version of a variable
  const createNewVersion = (varName) => {
    if (!variables[varName]) {
      variables[varName] = 0;
    } else {
      variables[varName]++;
    }
    return `${varName}_${variables[varName]}`;
  };

  // Helper to get the current version of a variable
  const getCurrentVersion = (varName) => {
    if (!variables[varName] && variables[varName] !== 0) {
      // First use, initialize to 0
      variables[varName] = 0;
      return `${varName}_0`;
    }
    return `${varName}_${variables[varName]}`;
  };

  // Recursive function to process each node in the AST
  const processNode = (node) => {
    if (!node) return null;

    switch (node.type) {
      case "Program":
        for (const statement of node.body) {
          processNode(statement);
        }
        return null;

      case "Assignment": {
        const varName = node.left;
        const rightValue = processExpression(node.right);
        const newVar = createNewVersion(varName);

        ssa.push({
          type: "Assignment",
          left: newVar,
          right: rightValue,
        });
        return null;
      }

      case "IfStatement": {
        const condition = processExpression(node.condition);

        // Save the variable state before if branch
        const beforeIfState = { ...variables };

        // Process if branch
        for (const statement of node.ifBody) {
          processNode(statement);
        }

        // Save the variable state after if branch
        const afterIfState = { ...variables };

        // Restore the variable state before if for else branch
        Object.assign(variables, beforeIfState);

        // Process else branch
        for (const statement of node.elseBody) {
          processNode(statement);
        }

        // Create phi nodes for variables modified in either branch
        const modifiedVars = new Set([...Object.keys(afterIfState), ...Object.keys(variables)]);

        for (const varName of modifiedVars) {
          const ifVersion = afterIfState[varName] !== undefined ? `${varName}_${afterIfState[varName]}` : null;

          const elseVersion = variables[varName] !== undefined ? `${varName}_${variables[varName]}` : null;

          if (ifVersion !== elseVersion && ifVersion && elseVersion) {
            const newVar = createNewVersion(varName);
            ssa.push({
              type: "Phi",
              result: newVar,
              operands: [ifVersion, elseVersion],
              condition,
            });
          }
        }

        return null;
      }

      case "WhileLoop": {
        // Process loop condition
        const condition = processExpression(node.condition);

        // Save variable state before loop
        const beforeLoopState = { ...variables };

        // Create initial phi nodes for loop entry
        for (const varName of Object.keys(beforeLoopState)) {
          phi.push({
            type: "Phi",
            result: `${varName}_loop`,
            operands: [getCurrentVersion(varName)],
            loopVar: true,
          });

          // Update the current version to use the loop version
          variables[varName] = "loop";
        }

        // Process loop body
        for (const statement of node.body) {
          processNode(statement);
        }

        // Update phi nodes with the final versions from the loop body
        for (const phiNode of phi) {
          if (phiNode.loopVar) {
            const varName = phiNode.result.split("_")[0];
            const endVersion = getCurrentVersion(varName);
            if (!phiNode.operands.includes(endVersion)) {
              phiNode.operands.push(endVersion);
            }
          }
        }

        // Add phi nodes to the SSA
        for (const phiNode of phi) {
          if (phiNode.loopVar) {
            delete phiNode.loopVar;
            ssa.push(phiNode);
          }
        }

        // Create exit phi nodes for variables modified in the loop
        for (const varName of Object.keys(variables)) {
          if (variables[varName] !== beforeLoopState[varName]) {
            const newVar = createNewVersion(varName);
            ssa.push({
              type: "Phi",
              result: newVar,
              operands: [
                beforeLoopState[varName] !== undefined ? `${varName}_${beforeLoopState[varName]}` : `${varName}_0`,
                getCurrentVersion(varName),
              ],
              condition: {
                type: "UnaryOperation",
                operator: "!",
                operand: condition,
              },
            });
          }
        }

        return null;
      }

      case "ForLoop": {
        // Process initialization
        processNode(node.init);

        // Handle as a while loop
        const whileLoop = {
          type: "WhileLoop",
          condition: node.condition,
          body: [...node.body, node.update],
        };

        processNode(whileLoop);
        return null;
      }

      case "Assert": {
        const condition = processExpression(node.condition);
        ssa.push({
          type: "Assert",
          condition,
        });
        return null;
      }

      default:
        throw new Error(`Unknown node type: ${node.type}`);
    }
  };

  const processExpression = (expr) => {
    if (!expr) return null;

    switch (expr.type) {
      case "BinaryOperation":
        return {
          type: "BinaryOperation",
          operator: expr.operator,
          left: processExpression(expr.left),
          right: processExpression(expr.right),
        };

      case "UnaryOperation":
        return {
          type: "UnaryOperation",
          operator: expr.operator,
          operand: processExpression(expr.operand),
        };

      case "Variable":
        return {
          type: "Variable",
          name: getCurrentVersion(expr.name),
        };

      case "ArrayAccess":
        return {
          type: "ArrayAccess",
          array: getCurrentVersion(expr.array),
          index: processExpression(expr.index),
        };

      case "Literal":
        return expr;

      default:
        throw new Error(`Unknown expression type: ${expr.type}`);
    }
  };

  processNode(ast);

  return { ssa, variables };
};

export const optimizeSSA = (ssaNodes) => {
  const optimized = [...ssaNodes];
  const constants = {};
  const useCounts = {};

  // First pass: Identify constants and count uses
  for (const node of optimized) {
    if (node.type === "Assignment" && node.right && node.right.type === "Literal") {
      constants[node.left] = node.right.value;
    }

    // Count variable uses
    const countUses = (expr) => {
      if (!expr) return;

      if (expr.type === "Variable") {
        useCounts[expr.name] = (useCounts[expr.name] || 0) + 1;
      } else if (expr.type === "BinaryOperation") {
        countUses(expr.left);
        countUses(expr.right);
      } else if (expr.type === "ArrayAccess") {
        useCounts[expr.array] = (useCounts[expr.array] || 0) + 1;
        countUses(expr.index);
      }
    };

    if (node.type === "Assignment" || node.type === "Assert") {
      countUses(node.right);
    } else if (node.type === "Phi") {
      for (const operand of node.operands) {
        if (typeof operand === 'string') {
          useCounts[operand] = (useCounts[operand] || 0) + 1;
        } else if (operand && operand.name) {
          useCounts[operand.name] = (useCounts[operand.name] || 0) + 1;
        }
      }
    }
  }

  // Second pass: Constant propagation and dead code elimination
  const newOptimized = [];

  for (const node of optimized) {
    const propagateConstants = (expr) => {
      if (!expr) return expr;

      if (expr.type === "Variable" && constants[expr.name] !== undefined) {
        return {
          type: "Literal",
          value: constants[expr.name],
        };
      } else if (expr.type === "BinaryOperation") {
        const left = propagateConstants(expr.left);
        const right = propagateConstants(expr.right);

        // Evaluate constant expressions
        if (left.type === "Literal" && right.type === "Literal") {
          try {
            // Safe evaluation of binary operation
            let value;
            switch (expr.operator) {
              case "+": value = left.value + right.value; break;
              case "-": value = left.value - right.value; break;
              case "*": value = left.value * right.value; break;
              case "/": value = left.value / right.value; break;
              case "%": value = left.value % right.value; break;
              case "<": value = left.value < right.value; break;
              case ">": value = left.value > right.value; break;
              case "<=": value = left.value <= right.value; break;
              case ">=": value = left.value >= right.value; break;
              case "==": value = left.value === right.value; break;
              case "!=": value = left.value !== right.value; break;
              default: return { ...expr, left, right };
            }
            return { type: "Literal", value };
          } catch {
            return { ...expr, left, right };
          }
        }
        return { ...expr, left, right };
      }
      return expr;
    };

    // Skip dead assignments (assigned but never used)
    if (node.type === "Assignment" && useCounts[node.left] === 0) {
      continue;
    }

    const newNode = { ...node };

    if (newNode.right) {
      newNode.right = propagateConstants(newNode.right);
    }

    if (newNode.condition) {
      newNode.condition = propagateConstants(newNode.condition);
    }

    if (newNode.operands) {
      newNode.operands = newNode.operands.map(operand => {
        if (typeof operand === 'string') {
          return operand;
        }
        return propagateConstants(operand);
      });
    }

    newOptimized.push(newNode);
  }

  return newOptimized;
};