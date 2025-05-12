// Format utility functions

export const formatSSA = (ssa) => {
  if (!ssa || ssa.length === 0) {
    return "";
  }
  
  return ssa
    .map((node) => {
      switch (node.type) {
        case "Assignment":
          return `${node.left} = ${formatSSAExpression(node.right)}`;
        case "Assert":
          return `assert(${formatSSAExpression(node.condition)})`;
        case "Phi":
          const operands = node.operands.map(op => 
            typeof op === 'string' ? op : formatSSAExpression(op)
          ).join(", ");
          
          const condition = node.condition 
            ? ` [${formatSSAExpression(node.condition)}]` 
            : '';
            
          return `${node.result} = φ(${operands})${condition}`;
        default:
          return JSON.stringify(node);
      }
    })
    .join("\n");
};

const formatSSAExpression = (expr) => {
  if (!expr) return "";
  
  switch (expr.type) {
    case "BinaryOperation":
      return `(${formatSSAExpression(expr.left)} ${expr.operator} ${formatSSAExpression(expr.right)})`;
    case "Variable":
      return expr.name;
    case "Literal":
      return expr.value;
    case "Phi":
      const ops = expr.operands.map(op => 
        typeof op === 'string' ? op : formatSSAExpression(op)
      ).join(", ");
      
      return `φ(${ops})`;
    default:
      try {
        return JSON.stringify(expr);
      } catch {
        return `[Complex Expression]`;
      }
  }
};

export const formatSMT = (smt) => {
  if (!smt) return "";
  
  // Enhanced formatting with syntax highlighting (via CSS classes in pre tags)
  const lines = smt.split("\n").map(line => {
    // Add proper indentation
    if (line.startsWith("(declare-const")) {
      return `  ${line}`;
    }
    if (line.startsWith("(assert")) {
      return `  ${line}`;
    }
    
    // Add comments for readability
    if (line === "(check-sat)") {
      return "\n  ; Check if the constraints are satisfiable\n  " + line;
    }
    if (line === "(get-model)") {
      return "\n  ; Get variable assignments if satisfiable\n  " + line;
    }
    if (line === "(set-logic QF_LIA)") {
      return line + "\n  ; Using Linear Integer Arithmetic\n";
    }
    
    return line;
  }).join("\n");
  
  // Further enhance with syntax highlighting hints
  return lines
    .replace(/\(declare-const/g, "(declare-const")
    .replace(/\(assert/g, "(assert")
    .replace(/\(check-sat\)/g, "(check-sat)")
    .replace(/\(get-model\)/g, "(get-model)");
};