"""Deductive Inference Engine and SMT Inequality Leap Verification (Feature 10).

Validates formal deductive steps and algebraic leaps using Z3 SMT Real arithmetic.
Proves soundness by refuting the negation of the conclusion (unsat) and extracts
concrete counter-example valuations when steps are fallacious non-sequiturs (sat).
"""

from __future__ import annotations

import ast
import re
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple, Union

import z3
from pydantic import BaseModel, ConfigDict, Field


class LeapValidationResult(BaseModel):
    """Result of verifying an algebraic or deductive step via Z3 SMT."""

    model_config = ConfigDict(extra="allow", arbitrary_types_allowed=True)

    is_valid: bool
    counter_model: Optional[Dict[str, Any]] = None
    details: Optional[str] = None

    @property
    def is_sound(self) -> bool:
        """Alias indicating whether the logical leap is verified valid."""
        return self.is_valid

    @property
    def has_counterexample(self) -> bool:
        """True if a counter-example valuation was extracted."""
        return self.counter_model is not None


class DeductiveInferenceEngine:
    """Automated reasoning engine verifying deductive steps via Z3 SMT."""

    def __init__(self, timeout_ms: int = 5000) -> None:
        """Initialize engine with configurable Z3 solver timeout in milliseconds."""
        self.timeout_ms = timeout_ms

    def normalize_string(self, s: str) -> str:
        """Normalize mathematical and LaTeX notation into Python AST syntax."""
        s = s.strip().strip("$")

        # Symbol & relation substitutions
        replacements = [
            (r"\le", "<="),
            (r"\leq", "<="),
            (r"\ge", ">="),
            (r"\geq", ">="),
            (r"\ne", "!="),
            (r"\neq", "!="),
            (r"\cdot", "*"),
            (r"\times", "*"),
            (r"\left", ""),
            (r"\right", ""),
            (r"\text{Greedy}(G)", "Greedy"),
            (r"\text{Greedy}", "Greedy"),
            (r"Greedy(G)", "Greedy"),
            (r"\chi(G)", "chi"),
            (r"\chi", "chi"),
            (r"\omega(G)", "omega"),
            (r"\omega", "omega"),
            (r"\alpha(G)", "alpha"),
            (r"\alpha", "alpha"),
            (r"\Delta(G)", "Delta"),
            (r"\Delta", "Delta"),
            (r"\delta(G)", "delta"),
            (r"\delta", "delta"),
            (r"\lambda_1", "lambda_1"),
            (r"\lambda_n", "lambda_n"),
            (r"\mu_2", "mu_2"),
        ]
        for old, new in replacements:
            s = s.replace(old, new)

        # Handle LaTeX fractions \frac{a}{b} -> ((a)/(b))
        frac_pattern = re.compile(r"\\frac\{([^{}]+)\}\{([^{}]+)\}")
        while r"\frac" in s:
            new_s = frac_pattern.sub(r"((\1)/(\2))", s)
            if new_s == s:
                break
            s = new_s

        # Strip remaining command backslashes
        s = re.sub(r"\\([a-zA-Z]+)", r"\1", s)
        s = s.replace("{", "(").replace("}", ")")

        # Normalize single '=' to '==' when not part of comparison operator
        s = re.sub(r"(?<![<>=!])=(?!=)", "==", s)

        return s.strip()

    def _ast_to_z3(
        self, node: ast.AST, vars_dict: Dict[str, z3.ArithRef]
    ) -> Any:
        """Recursively translate a Python AST expression node to a Z3 Real expression."""
        if isinstance(node, ast.Expression):
            return self._ast_to_z3(node.body, vars_dict)

        elif isinstance(node, ast.Constant):
            return z3.RealVal(node.value)

        elif isinstance(node, ast.Name):
            name = node.id
            if name not in vars_dict:
                vars_dict[name] = z3.Real(name)
            return vars_dict[name]

        elif isinstance(node, ast.Call):
            # Map invariant function calls e.g. chi(G) to real variable
            func_name = node.func.id if isinstance(node.func, ast.Name) else "f"
            if func_name not in vars_dict:
                vars_dict[func_name] = z3.Real(func_name)
            return vars_dict[func_name]

        elif isinstance(node, ast.UnaryOp):
            operand = self._ast_to_z3(node.operand, vars_dict)
            if isinstance(node.op, ast.USub):
                return -operand
            elif isinstance(node.op, ast.UAdd):
                return operand
            elif isinstance(node.op, ast.Not):
                return z3.Not(operand)
            raise ValueError(f"Unsupported unary operator: {type(node.op).__name__}")

        elif isinstance(node, ast.BinOp):
            left = self._ast_to_z3(node.left, vars_dict)
            right = self._ast_to_z3(node.right, vars_dict)
            if isinstance(node.op, ast.Add):
                return left + right
            elif isinstance(node.op, ast.Sub):
                return left - right
            elif isinstance(node.op, ast.Mult):
                return left * right
            elif isinstance(node.op, ast.Div):
                return left / right
            elif isinstance(node.op, ast.Pow):
                return left ** right
            raise ValueError(f"Unsupported binary operator: {type(node.op).__name__}")

        elif isinstance(node, ast.Compare):
            left = self._ast_to_z3(node.left, vars_dict)
            comparisons = []
            curr = left
            for op, right_node in zip(node.ops, node.comparators):
                right = self._ast_to_z3(right_node, vars_dict)
                if isinstance(op, ast.Lt):
                    comparisons.append(curr < right)
                elif isinstance(op, ast.LtE):
                    comparisons.append(curr <= right)
                elif isinstance(op, ast.Gt):
                    comparisons.append(curr > right)
                elif isinstance(op, ast.GtE):
                    comparisons.append(curr >= right)
                elif isinstance(op, ast.Eq):
                    comparisons.append(curr == right)
                elif isinstance(op, ast.NotEq):
                    comparisons.append(curr != right)
                else:
                    raise ValueError(f"Unsupported comparison operator: {type(op).__name__}")
                curr = right
            return z3.And(*comparisons) if len(comparisons) > 1 else comparisons[0]

        raise ValueError(f"Unsupported AST node type: {type(node).__name__}")

    def verify_inequality_leap(
        self, premises: List[str], conclusion: str
    ) -> LeapValidationResult:
        """Verify if conclusion logically follows from premises via Z3 SMT solver.

        Algorithm:
        1. Parse all premises as Z3 constraints.
        2. Assert Not(conclusion).
        3. Check satisfiability:
           - UNSAT: conclusion holds universally under premises (is_valid=True).
           - SAT: logical leap is a non-sequitur; extract counter_model valuation.
           - UNKNOWN: solver timeout or boundary condition.
        """
        solver = z3.Solver()
        solver.set("timeout", self.timeout_ms)
        vars_dict: Dict[str, z3.ArithRef] = {}

        try:
            for premise_str in premises:
                norm_p = self.normalize_string(premise_str)
                tree_p = ast.parse(norm_p, mode="eval")
                z3_p = self._ast_to_z3(tree_p.body, vars_dict)
                solver.add(z3_p)

            norm_c = self.normalize_string(conclusion)
            tree_c = ast.parse(norm_c, mode="eval")
            z3_c = self._ast_to_z3(tree_c.body, vars_dict)
            solver.add(z3.Not(z3_c))

        except Exception as err:
            return LeapValidationResult(
                is_valid=False,
                counter_model=None,
                details=f"Constraint parsing error: {err}",
            )

        check_status = solver.check()

        if check_status == z3.unsat:
            return LeapValidationResult(
                is_valid=True,
                counter_model=None,
                details="Unsat: logical leap is rigorously sound under premises.",
            )

        elif check_status == z3.sat:
            model = solver.model()
            counter_model: Dict[str, Any] = {}
            for name, var_ref in vars_dict.items():
                val = model.eval(var_ref, model_completion=True)
                if z3.is_rational_value(val):
                    frac = val.as_fraction()
                    if frac.denominator == 1:
                        counter_model[name] = frac.numerator
                    else:
                        counter_model[name] = float(frac)
                else:
                    counter_model[name] = str(val)

            return LeapValidationResult(
                is_valid=False,
                counter_model=counter_model,
                details="Sat: logical leap is an invalid non-sequitur (counter-example model exists).",
            )

        else:
            reason = solver.reason_unknown()
            return LeapValidationResult(
                is_valid=False,
                counter_model=None,
                details=f"Solver returned unknown: {reason}",
            )
