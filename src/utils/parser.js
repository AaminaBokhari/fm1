// Parser implementation
export const parseProgram = (programText) => {
  // This is a simplified parser for demonstration
  // In a real implementation, you would use a proper parser library

  const lines = programText.split("\n");
  const ast = { type: "Program", body: [] };

  let i = 0;
  while (i < lines.length) {
    const line = lines[i].trim();

    if (!line || line.startsWith("//")) {
      i++;
      continue;
    }

    // Assignment statement
    if (line.includes(":=")) {
      const [left, right] = line.split(":=");
      ast.body.push({
        type: "Assignment",
        left: left.trim(),
        right: parseExpression(right.replace(/;$/, "").trim()),
      });
    }
    // If statement
    else if (line.startsWith("if")) {
      const condMatch = line.match(/if\s*\((.*)\)\s*\{/);
      if (!condMatch) throw new Error(`Invalid if statement: ${line}`);

      const condition = parseExpression(condMatch[1].trim());
      const ifBody = [];

      // Find the matching closing brace
      let depth = 1;
      let j = i + 1;

      while (j < lines.length && depth > 0) {
        const currentLine = lines[j].trim();

        if (currentLine.includes("{")) depth++;
        if (currentLine.includes("}")) depth--;

        if (depth > 0 && currentLine) {
          ifBody.push(currentLine);
        }

        j++;
      }

      // Check for else
      const elseBody = [];
      if (j < lines.length && lines[j].trim().startsWith("else")) {
        j++; // Skip the else line

        // Find the matching closing brace for else
        depth = 1;
        j++; // Move to first line inside else

        while (j < lines.length && depth > 0) {
          const currentLine = lines[j].trim();

          if (currentLine.includes("{")) depth++;
          if (currentLine.includes("}")) depth--;

          if (depth > 0 && currentLine) {
            elseBody.push(currentLine);
          }

          j++;
        }
      }

      ast.body.push({
        type: "IfStatement",
        condition,
        ifBody: parseProgram(ifBody.join("\n")).body,
        elseBody: parseProgram(elseBody.join("\n")).body,
      });

      i = j;
      continue;
    }
    // While loop
    else if (line.startsWith("while")) {
      const condMatch = line.match(/while\s*\((.*)\)\s*\{/);
      if (!condMatch) throw new Error(`Invalid while statement: ${line}`);

      const condition = parseExpression(condMatch[1].trim());
      const loopBody = [];

      // Find the matching closing brace
      let depth = 1;
      let j = i + 1;

      while (j < lines.length && depth > 0) {
        const currentLine = lines[j].trim();

        if (currentLine.includes("{")) depth++;
        if (currentLine.includes("}")) depth--;

        if (depth > 0 && currentLine) {
          loopBody.push(currentLine);
        }

        j++;
      }

      ast.body.push({
        type: "WhileLoop",
        condition,
        body: parseProgram(loopBody.join("\n")).body,
      });

      i = j;
      continue;
    }
    // For loop
    else if (line.startsWith("for")) {
      const forMatch = line.match(/for\s*\((.*);(.*);(.*)\)\s*\{/);
      if (!forMatch) throw new Error(`Invalid for statement: ${line}`);

      const initialization = forMatch[1].trim();
      const condition = parseExpression(forMatch[2].trim());
      const update = forMatch[3].trim();

      const loopBody = [];

      // Find the matching closing brace
      let depth = 1;
      let j = i + 1;

      while (j < lines.length && depth > 0) {
        const currentLine = lines[j].trim();

        if (currentLine.includes("{")) depth++;
        if (currentLine.includes("}")) depth--;

        if (depth > 0 && currentLine) {
          loopBody.push(currentLine);
        }

        j++;
      }

      // Parse initialization part (typically assignment)
      const initParts = initialization.split(":=");
      const initAssign = {
        type: "Assignment",
        left: initParts[0].trim(),
        right: parseExpression(initParts[1].trim()),
      };

      // Parse update part (typically assignment)
      const updateParts = update.split(":=");
      const updateAssign = {
        type: "Assignment",
        left: updateParts[0].trim(),
        right: parseExpression(updateParts[1].trim()),
      };

      ast.body.push({
        type: "ForLoop",
        init: initAssign,
        condition,
        update: updateAssign,
        body: parseProgram(loopBody.join("\n")).body,
      });

      i = j;
      continue;
    }
    // Assert statement
    else if (line.startsWith("assert")) {
      const assertMatch = line.match(/assert\((.*)\);/);
      if (!assertMatch) throw new Error(`Invalid assert statement: ${line}`);

      ast.body.push({
        type: "Assert",
        condition: parseExpression(assertMatch[1].trim()),
      });
    }

    i++;
  }

  return ast;
};

const parseExpression = (expr) => {
  // This is a very simplified expression parser
  // In a real implementation, you would use a proper parser with precedence rules

  // Check for array access
  if (expr.includes("[") && expr.includes("]")) {
    const match = expr.match(/(.*)[(.*)]/)
    if (match) {
      return {
        type: "ArrayAccess",
        array: match[1].trim(),
        index: parseExpression(match[2].trim()),
      };
    }
  }

  // Check for binary operations
  const operators = ["==", "!=", "<=", ">=", "<", ">", "+", "-", "*", "/", "%"];
  for (const op of operators) {
    if (expr.includes(op)) {
      const [left, right] = expr.split(op);
      return {
        type: "BinaryOperation",
        operator: op,
        left: parseExpression(left.trim()),
        right: parseExpression(right.trim()),
      };
    }
  }

  // Check if it's a number
  if (!isNaN(expr)) {
    return {
      type: "Literal",
      value: parseInt(expr),
    };
  }

  // Otherwise assume it's a variable
  return {
    type: "Variable",
    name: expr,
  };
};

export const generateCFG = (ast) => {
  const nodes = [];
  const edges = [];
  let nodeId = 0;

  const processNode = (node, parentId = null) => {
    const currentNodeId = nodeId++;
    let label = "";

    switch (node.type) {
      case "Program":
        label = "Program Start";
        nodes.push({ id: currentNodeId, label });
        node.body.forEach((child) => processNode(child, currentNodeId));
        break;

      case "Assignment":
        label = `${node.left} := ${formatExpression(node.right)}`;
        nodes.push({ id: currentNodeId, label });
        if (parentId !== null) {
          edges.push({ from: parentId, to: currentNodeId });
        }
        break;

      case "IfStatement":
        label = `If (${formatExpression(node.condition)})`;
        nodes.push({ id: currentNodeId, label });
        if (parentId !== null) {
          edges.push({ from: parentId, to: currentNodeId });
        }

        // True branch
        const trueBranchId = nodeId++;
        nodes.push({ id: trueBranchId, label: "Then" });
        edges.push({ from: currentNodeId, to: trueBranchId, label: "T" });
        node.ifBody.forEach((child) => processNode(child, trueBranchId));

        // False branch
        const falseBranchId = nodeId++;
        nodes.push({ id: falseBranchId, label: "Else" });
        edges.push({ from: currentNodeId, to: falseBranchId, label: "F" });
        node.elseBody.forEach((child) => processNode(child, falseBranchId));
        break;

      case "WhileLoop":
        label = `While (${formatExpression(node.condition)})`;
        nodes.push({ id: currentNodeId, label });
        if (parentId !== null) {
          edges.push({ from: parentId, to: currentNodeId });
        }

        // Loop body
        const loopBodyId = nodeId++;
        nodes.push({ id: loopBodyId, label: "Loop Body" });
        edges.push({ from: currentNodeId, to: loopBodyId, label: "T" });
        node.body.forEach((child) => processNode(child, loopBodyId));

        // Back edge
        edges.push({ from: loopBodyId, to: currentNodeId });
        break;

      case "Assert":
        label = `Assert (${formatExpression(node.condition)})`;
        nodes.push({ id: currentNodeId, label });
        if (parentId !== null) {
          edges.push({ from: parentId, to: currentNodeId });
        }
        break;

      default:
        label = node.type;
        nodes.push({ id: currentNodeId, label });
        if (parentId !== null) {
          edges.push({ from: parentId, to: currentNodeId });
        }
    }
  };

  processNode(ast);
  return { nodes, edges };
};

const formatExpression = (expr) => {
  if (!expr) return "";
  switch (expr.type) {
    case "BinaryOperation":
      return `${formatExpression(expr.left)} ${expr.operator} ${formatExpression(expr.right)}`;
    case "Variable":
      return expr.name;
    case "Literal":
      return expr.value;
    default:
      return expr.type;
  }
};