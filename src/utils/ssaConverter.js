// Corrected SSA Conversion Implementation
export const convertToSSA = (ast) => {
  const ssa = [];
  const variables = {};

  // Helper to create a new version of a variable
  const createNewVersion = (varName) => {
    if (!variables[varName] && variables[varName] !== 0) {
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

        // Save the initial state of variables before branching
        const initialVersions = {};
        for (const varName in variables) {
          initialVersions[varName] = getCurrentVersion(varName);
        }

        // Process if branch
        const ifVersions = {};
        variables[node.left] = variables[node.left] || 0;
        const ifBranchState = { ...variables };
        for (const statement of node.ifBody) {
          processNode(statement);
          
          // Track changes in variables specific to if branch
          for (const varName in variables) {
            if (variables[varName] !== ifBranchState[varName]) {
              ifVersions[varName] = getCurrentVersion(varName);
            }
          }
        }

        // Restore to initial state for else branch
        Object.assign(variables, ifBranchState);

        // Process else branch
        const elseVersions = {};
        for (const statement of node.elseBody) {
          processNode(statement);
          
          // Track changes in variables specific to else branch
          for (const varName in variables) {
            if (variables[varName] !== ifBranchState[varName]) {
              elseVersions[varName] = getCurrentVersion(varName);
            }
          }
        }

        // Create phi nodes for modified variables
        const modifiedVars = new Set([
          ...Object.keys(ifVersions),
          ...Object.keys(elseVersions)
        ]);

        for (const varName of modifiedVars) {
          const ifVersion = ifVersions[varName] || initialVersions[varName];
          const elseVersion = elseVersions[varName] || initialVersions[varName];

          const newVar = createNewVersion(varName);
          ssa.push({
            type: "Phi",
            result: newVar,
            operands: [ifVersion, elseVersion],
            condition,
          });
        }

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

      case "Literal":
        return expr;

      default:
        throw new Error(`Unknown expression type: ${expr.type}`);
    }
  };

  processNode(ast);

  return { ssa, variables };
};

// Example AST for the given code
const exampleAST = {
  type: "Program",
  body: [
    {
      type: "Assignment",
      left: "x",
      right: { type: "Literal", value: 3 }
    },
    {
      type: "IfStatement",
      condition: {
        type: "BinaryOperation",
        operator: "<",
        left: { type: "Variable", name: "x" },
        right: { type: "Literal", value: 5 }
      },
      ifBody: [
        {
          type: "Assignment",
          left: "y",
          right: {
            type: "BinaryOperation",
            operator: "+",
            left: { type: "Variable", name: "x" },
            right: { type: "Literal", value: 1 }
          }
        }
      ],
      elseBody: [
        {
          type: "Assignment",
          left: "y",
          right: {
            type: "BinaryOperation",
            operator: "-",
            left: { type: "Variable", name: "x" },
            right: { type: "Literal", value: 1 }
          }
        }
      ]
    },
    {
      type: "Assert",
      condition: {
        type: "BinaryOperation",
        operator: ">",
        left: { type: "Variable", name: "y" },
        right: { type: "Literal", value: 0 }
      }
    }
  ]
};

// Usage example
const result = convertToSSA(exampleAST);
console.log(JSON.stringify(result.ssa, null, 2));