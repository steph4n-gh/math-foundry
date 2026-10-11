"""Abstract Syntax Tree models for graph theory expressions and conjectures.

Defines AST nodes for graph invariants, constants, unary/binary operators,
relational comparisons, guards, and conjectures.
Provides symbolic SymPy evaluation, LaTeX formatting, Lean 4 formalization,
and JSON serialization adhering to pipeline interface contracts.
"""

from __future__ import annotations

import math
from fractions import Fraction
from typing import Any, Dict, List, Literal, Optional, Set, Tuple, Union
import networkx as nx
from pydantic import BaseModel, ConfigDict, Field
import sympy as sp

from autonomous_math.core.graph_types import GraphInstance
from autonomous_math.core.invariants import (
    INVARIANT_ALIASES,
    GraphInvariantEvaluator,
)

# LaTeX symbol formatting dictionary
INVARIANT_LATEX_MAP: Dict[str, str] = {
    "order": "n",
    "size": "m",
    "max_degree": r"\Delta(G)",
    "min_degree": r"\delta(G)",
    "average_degree": r"\bar{d}(G)",
    "density": r"\rho(G)",
    "chromatic_number": r"\chi(G)",
    "clique_number": r"\omega(G)",
    "independence_number": r"\alpha(G)",
    "parity_code_distance": r"d_{\mathrm{adj}}(G)",
    "parity_code_dimension": r"k_{\mathrm{adj}}(G)",
    "unique_neighbor_radius": r"u_{\mathrm{adj}}(G)",
    "girth": r"g(G)",
    "diameter": r"\operatorname{diam}(G)",
    "radius": r"\operatorname{rad}(G)",
    "triangle_count": r"T(G)",
    "spectral_radius": r"\lambda_1(G)",
    "smallest_adjacency_eigenvalue": r"\lambda_n(G)",
    "algebraic_connectivity": r"\mu_2(G)",
    "laplacian_spectral_radius": r"\mu_n(G)",
    "hoffman_bound": r"H(G)",
    "wilf_bound": r"W(G)",
    "signless_laplacian_spectral_radius": r"q_1(G)",
    "normalized_laplacian_spectral_gap": r"\lambda_2^{\mathcal{L}}(G)",
    "normalized_laplacian_spectral_radius": r"\lambda_n^{\mathcal{L}}(G)",
    "estrada_index": r"EE(G)",
    "graph_energy": r"\mathcal{E}(G)",
    "spectral_spread": r"s(G)",
    "complement_spectral_radius": r"\lambda_1(\overline{G})",
    "nordhaus_gaddum_spectral_sum": r"\lambda_1(G) + \lambda_1(\overline{G})",
    "nordhaus_gaddum_spectral_product": r"\lambda_1(G) \cdot \lambda_1(\overline{G})",
}

# Lean 4 Mathlib representation dictionary
INVARIANT_LEAN_MAP: Dict[str, str] = {
    "order": "(Fintype.card V : ℝ)",
    "size": "(G.edgeFinset.card : ℝ)",
    "max_degree": "(G.maxDegree : ℝ)",
    "min_degree": "(G.minDegree : ℝ)",
    "average_degree": "(averageDegree G)",
    "density": "(G.density : ℝ)",
    "chromatic_number": "(G.chromaticNumber : ℝ)",
    "clique_number": "(G.cliqueNum : ℝ)",
    "independence_number": "(G.indepNum : ℝ)",
    "girth": "(G.girth : ℝ)",
    "diameter": "(G.diameter : ℝ)",
    "radius": "(G.radius : ℝ)",
    "triangle_count": "(G.triangleCount : ℝ)",
    "spectral_radius": "(G.spectralRadius : ℝ)",
    "smallest_adjacency_eigenvalue": "(G.smallestAdjacencyEigenvalue : ℝ)",
    "spectral_spread": "(G.spectralSpread : ℝ)",
    "algebraic_connectivity": "(G.fiedlerValue : ℝ)",
    "laplacian_spectral_radius": "(G.laplacianRadius : ℝ)",
    "hoffman_bound": "(G.hoffmanBound : ℝ)",
    "wilf_bound": "(G.wilfBound : ℝ)",
    "signless_laplacian_spectral_radius": "(G.signlessLaplacianRadius : ℝ)",
    "normalized_laplacian_spectral_gap": "(G.normalizedLaplacianGap : ℝ)",
    "normalized_laplacian_spectral_radius": "(G.normalizedLaplacianRadius : ℝ)",
    "estrada_index": "(G.estradaIndex : ℝ)",
    "graph_energy": "(G.energy : ℝ)",
    "complement_spectral_radius": "(G.complement.spectralRadius : ℝ)",
    "nordhaus_gaddum_spectral_sum": "(G.spectralRadius + G.complement.spectralRadius : ℝ)",
    "nordhaus_gaddum_spectral_product": "(G.spectralRadius * G.complement.spectralRadius : ℝ)",
}

INTEGER_VALUED_INVARIANTS: Set[str] = {
    "order",
    "size",
    "max_degree",
    "min_degree",
    "chromatic_number",
    "clique_number",
    "independence_number",
    "parity_code_distance",
    "parity_code_dimension",
    "unique_neighbor_radius",
    "girth",
    "diameter",
    "radius",
    "triangle_count",
}


class ASTBase(BaseModel):
    """Base class for all AST nodes with immutability."""

    model_config = ConfigDict(frozen=True, extra="allow")


class InvariantNode(ASTBase):
    """AST leaf representing a graph invariant."""

    node_type: Literal["invariant"] = "invariant"
    name: str

    def __init__(self, name: Optional[str] = None, **kwargs: Any) -> None:
        if name is not None:
            kwargs["name"] = name
        super().__init__(**kwargs)

    def canonical_name(self) -> str:
        return INVARIANT_ALIASES.get(self.name, self.name)

    def evaluate(self, invariants: Dict[str, Union[int, float]]) -> float:
        cname = self.canonical_name()
        if cname in invariants:
            return float(invariants[cname])
        if self.name in invariants:
            return float(invariants[self.name])
        # Try finding alias
        for k, v in invariants.items():
            if INVARIANT_ALIASES.get(k) == cname:
                return float(v)
        raise KeyError(
            f"Invariant '{self.name}' (canonical: '{cname}') not found in evaluation dict."
        )

    def to_sympy(self) -> sp.Symbol:
        return sp.Symbol(self.canonical_name(), real=True, nonnegative=True)

    def to_latex(self) -> str:
        return INVARIANT_LATEX_MAP.get(self.canonical_name(), self.canonical_name())

    def to_lean(self) -> str:
        return INVARIANT_LEAN_MAP.get(
            self.canonical_name(), f"(G.{self.canonical_name()} : ℝ)"
        )

    def get_invariant_names(self) -> Set[str]:
        return {self.canonical_name()}

    @property
    def variables(self) -> Set[str]:
        return {self.canonical_name()}

    @property
    def complexity(self) -> int:
        return 1

    @property
    def depth(self) -> int:
        return 1

    @property
    def canonical_key(self) -> str:
        return f"inv:{self.canonical_name()}"

    def to_dict(self) -> Dict[str, Any]:
        return {"node_type": "invariant", "name": self.name}


class ConstantNode(ASTBase):
    """AST leaf representing a constant rational/real number."""

    node_type: Literal["constant"] = "constant"
    value: float

    def __init__(self, value: Optional[Union[float, int]] = None, **kwargs: Any) -> None:
        if value is not None:
            kwargs["value"] = float(value)
        super().__init__(**kwargs)

    def evaluate(self, invariants: Dict[str, Union[int, float]]) -> float:
        return float(self.value)

    def to_sympy(self) -> sp.Expr:
        value = Fraction(str(self.value))
        return sp.Rational(value.numerator, value.denominator)

    def to_latex(self) -> str:
        if self.value.is_integer():
            return str(int(self.value))
        if self.value == 0.5:
            return r"\frac{1}{2}"
        if self.value == 0.25:
            return r"\frac{1}{4}"
        return str(self.value)

    def to_lean(self) -> str:
        value = Fraction(str(self.value))
        if value.denominator == 1:
            return f"({value.numerator} : ℝ)"
        return f"({value.numerator} / {value.denominator} : ℝ)"

    def get_invariant_names(self) -> Set[str]:
        return set()

    @property
    def variables(self) -> Set[str]:
        return set()

    @property
    def complexity(self) -> int:
        return 1

    @property
    def depth(self) -> int:
        return 1

    @property
    def canonical_key(self) -> str:
        # The trusted translator interprets the round-trippable decimal as an
        # exact rational. Use the same value here: :g silently merged distinct
        # statements at six significant digits. Rational form also equates -0
        # with 0 without changing any stored AST value or theorem statement.
        value = Fraction(str(self.value))
        return f"c:{value.numerator}" if value.denominator == 1 else f"c:{value.numerator}/{value.denominator}"

    def to_dict(self) -> Dict[str, Any]:
        return {"node_type": "constant", "value": self.value}


class UnaryOpNode(ASTBase):
    """AST node for unary mathematical operations."""

    node_type: Literal["unary_op"] = "unary_op"
    op: Literal["sqrt", "sqr", "floor", "ceil", "neg", "inv", "abs", "log1p", "exp"]
    child: ExpressionNode

    def __init__(
        self,
        op: Optional[str] = None,
        child: Optional[ExpressionNode] = None,
        **kwargs: Any,
    ) -> None:
        if op is not None:
            kwargs["op"] = op
        if child is not None:
            kwargs["child"] = child
        super().__init__(**kwargs)

    def evaluate(self, invariants: Dict[str, Union[int, float]]) -> float:
        c = self.child.evaluate(invariants)
        if self.op == "sqrt":
            if c < -1e-9:
                raise ValueError(f"Domain error: sqrt of negative value {c}")
            return math.sqrt(max(0.0, c))
        elif self.op == "sqr":
            return c * c
        elif self.op == "floor":
            return float(math.floor(c))
        elif self.op == "ceil":
            return float(math.ceil(c))
        elif self.op == "neg":
            return -c
        elif self.op == "inv":
            if abs(c) < 1e-12:
                raise ZeroDivisionError("Domain error: division by zero in inv()")
            return 1.0 / c
        elif self.op == "abs":
            return abs(c)
        elif self.op == "log1p":
            if c <= -1.0:
                raise ValueError(
                    f"Domain error: log1p of non-positive argument {1.0 + c}"
                )
            return math.log1p(c)
        elif self.op == "exp":
            return math.exp(c)
        raise ValueError(f"Unknown unary operator '{self.op}'")

    def to_sympy(self) -> sp.Expr:
        c = self.child.to_sympy()
        if self.op == "sqrt":
            return sp.sqrt(c)
        elif self.op == "sqr":
            return c**2
        elif self.op == "floor":
            return sp.floor(c)
        elif self.op == "ceil":
            return sp.ceiling(c)
        elif self.op == "neg":
            return -c
        elif self.op == "inv":
            return 1 / c
        elif self.op == "abs":
            return sp.Abs(c)
        elif self.op == "log1p":
            return sp.log(1 + c)
        elif self.op == "exp":
            return sp.exp(c)
        raise ValueError(f"Unknown unary operator '{self.op}'")

    def to_latex(self) -> str:
        c_tex = self.child.to_latex()
        if self.op == "sqrt":
            return rf"\sqrt{{{c_tex}}}"
        elif self.op == "sqr":
            return f"({c_tex})^2"
        elif self.op == "floor":
            return rf"\left\lfloor {c_tex} \right\rfloor"
        elif self.op == "ceil":
            return rf"\left\lceil {c_tex} \right\rceil"
        elif self.op == "neg":
            return f"-({c_tex})"
        elif self.op == "inv":
            return rf"\frac{{1}}{{{c_tex}}}"
        elif self.op == "abs":
            return rf"\left| {c_tex} \right|"
        elif self.op == "log1p":
            return rf"\ln(1 + {c_tex})"
        elif self.op == "exp":
            return rf"\exp\left({c_tex}\right)"
        raise ValueError(f"Unknown unary operator '{self.op}'")

    def to_lean(self) -> str:
        c_lean = self.child.to_lean()
        if self.op == "sqrt":
            return f"(Real.sqrt ({c_lean}))"
        elif self.op == "sqr":
            return f"(({c_lean}) ^ 2)"
        elif self.op == "floor":
            return f"(⌊{c_lean}⌋ : ℝ)"
        elif self.op == "ceil":
            return f"(⌈{c_lean}⌉ : ℝ)"
        elif self.op == "neg":
            return f"(-({c_lean}))"
        elif self.op == "inv":
            return f"(({c_lean})⁻¹)"
        elif self.op == "abs":
            return f"(|{c_lean}|)"
        elif self.op == "log1p":
            return f"(Real.log (1 + {c_lean}))"
        elif self.op == "exp":
            return f"(Real.exp ({c_lean}))"
        raise ValueError(f"Unknown unary operator '{self.op}'")

    def get_invariant_names(self) -> Set[str]:
        return self.child.get_invariant_names()

    @property
    def variables(self) -> Set[str]:
        return self.child.variables

    @property
    def complexity(self) -> int:
        return self.child.complexity + 1

    @property
    def depth(self) -> int:
        return self.child.depth + 1

    @property
    def canonical_key(self) -> str:
        return f"u:{self.op}({self.child.canonical_key})"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "node_type": "unary_op",
            "op": self.op,
            "child": self.child.to_dict(),
        }


class BinaryOpNode(ASTBase):
    """AST node for binary mathematical operations."""

    node_type: Literal["binary_op"] = "binary_op"
    op: Literal["+", "-", "*", "/", "max", "min", "^"]
    left: ExpressionNode
    right: ExpressionNode

    def __init__(
        self,
        op: Optional[str] = None,
        left: Optional[ExpressionNode] = None,
        right: Optional[ExpressionNode] = None,
        **kwargs: Any,
    ) -> None:
        if op is not None:
            kwargs["op"] = op
        if left is not None:
            kwargs["left"] = left
        if right is not None:
            kwargs["right"] = right
        super().__init__(**kwargs)

    def evaluate(self, invariants: Dict[str, Union[int, float]]) -> float:
        l = self.left.evaluate(invariants)
        r = self.right.evaluate(invariants)
        if self.op == "+":
            return l + r
        elif self.op == "-":
            return l - r
        elif self.op == "*":
            return l * r
        elif self.op == "/":
            if abs(r) < 1e-12:
                raise ZeroDivisionError("Domain error: division by zero in '/'")
            return l / r
        elif self.op == "max":
            return max(l, r)
        elif self.op == "min":
            return min(l, r)
        elif self.op == "^":
            return l**r
        raise ValueError(f"Unknown binary operator '{self.op}'")

    def to_sympy(self) -> sp.Expr:
        l = self.left.to_sympy()
        r = self.right.to_sympy()
        if self.op == "+":
            return l + r
        elif self.op == "-":
            return l - r
        elif self.op == "*":
            return l * r
        elif self.op == "/":
            return l / r
        elif self.op == "max":
            return sp.Max(l, r)
        elif self.op == "min":
            return sp.Min(l, r)
        elif self.op == "^":
            return l**r
        raise ValueError(f"Unknown binary operator '{self.op}'")

    def to_latex(self) -> str:
        l_tex = self.left.to_latex()
        r_tex = self.right.to_latex()
        if self.op == "+":
            return f"{l_tex} + {r_tex}"
        elif self.op == "-":
            return f"{l_tex} - ({r_tex})"
        elif self.op == "*":
            if isinstance(self.left, BinaryOpNode) and self.left.op in {"+", "-"}:
                l_tex = rf"\left({l_tex}\right)"
            if isinstance(self.right, BinaryOpNode) and self.right.op in {"+", "-"}:
                r_tex = rf"\left({r_tex}\right)"
            return f"{l_tex} \\cdot {r_tex}"
        elif self.op == "/":
            return rf"\frac{{{l_tex}}}{{{r_tex}}}"
        elif self.op == "max":
            return rf"\max({l_tex}, {r_tex})"
        elif self.op == "min":
            return rf"\min({l_tex}, {r_tex})"
        elif self.op == "^":
            return f"({l_tex})^{{{r_tex}}}"
        raise ValueError(f"Unknown binary operator '{self.op}'")

    def to_lean(self) -> str:
        l_lean = self.left.to_lean()
        r_lean = self.right.to_lean()
        if self.op == "+":
            return f"({l_lean} + {r_lean})"
        elif self.op == "-":
            return f"({l_lean} - {r_lean})"
        elif self.op == "*":
            return f"({l_lean} * {r_lean})"
        elif self.op == "/":
            return f"({l_lean} / {r_lean})"
        elif self.op == "max":
            return f"(max ({l_lean}) ({r_lean}))"
        elif self.op == "min":
            return f"(min ({l_lean}) ({r_lean}))"
        elif self.op == "^":
            return f"(({l_lean}) ^ ({r_lean}))"
        raise ValueError(f"Unknown binary operator '{self.op}'")

    def get_invariant_names(self) -> Set[str]:
        return self.left.get_invariant_names() | self.right.get_invariant_names()

    @property
    def variables(self) -> Set[str]:
        return self.left.variables | self.right.variables

    @property
    def complexity(self) -> int:
        return self.left.complexity + self.right.complexity + 1

    @property
    def depth(self) -> int:
        return max(self.left.depth, self.right.depth) + 1

    @property
    def canonical_key(self) -> str:
        if (
            self.op in {"+", "*", "max", "min"}
            and self.left.canonical_key > self.right.canonical_key
        ):
            return f"b:{self.op}({self.right.canonical_key},{self.left.canonical_key})"
        return f"b:{self.op}({self.left.canonical_key},{self.right.canonical_key})"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "node_type": "binary_op",
            "op": self.op,
            "left": self.left.to_dict(),
            "right": self.right.to_dict(),
        }


# Union type for expressions
ExpressionNode = Union[InvariantNode, ConstantNode, UnaryOpNode, BinaryOpNode]
UnaryOpNode.model_rebuild()
BinaryOpNode.model_rebuild()


def deserialize_expression(data: Union[Dict[str, Any], ExpressionNode]) -> ExpressionNode:
    """Deserialize dictionary into an ExpressionNode instance."""
    if isinstance(data, (InvariantNode, ConstantNode, UnaryOpNode, BinaryOpNode)):
        return data
    nt = data.get("node_type")
    if nt == "invariant":
        return InvariantNode(name=data["name"])
    elif nt == "constant":
        return ConstantNode(value=float(data["value"]))
    elif nt == "unary_op":
        return UnaryOpNode(
            op=data["op"],
            child=deserialize_expression(data["child"]),
        )
    elif nt == "binary_op":
        return BinaryOpNode(
            op=data["op"],
            left=deserialize_expression(data["left"]),
            right=deserialize_expression(data["right"]),
        )
    raise ValueError(f"Unknown node_type '{nt}' in expression data: {data}")


class RelationNode(ASTBase):
    """AST node for relational comparisons (<=, >=, ==, <, >)."""

    node_type: Literal["relation"] = "relation"
    op: Literal["<=", ">=", "==", "<", ">"]
    left: ExpressionNode
    right: ExpressionNode

    def __init__(
        self,
        op: Optional[str] = None,
        left: Optional[ExpressionNode] = None,
        right: Optional[ExpressionNode] = None,
        **kwargs: Any,
    ) -> None:
        if op is not None:
            kwargs["op"] = op
        if left is not None:
            kwargs["left"] = left
        if right is not None:
            kwargs["right"] = right
        super().__init__(**kwargs)

    def evaluate(
        self,
        invariants: Dict[str, Union[int, float]],
        tol: float = 1e-7,
    ) -> Tuple[bool, float, float]:
        l = self.left.evaluate(invariants)
        r = self.right.evaluate(invariants)
        if self.op == "<=":
            holds = l <= r + tol
        elif self.op == ">=":
            holds = l >= r - tol
        elif self.op == "==":
            holds = abs(l - r) <= tol
        elif self.op == "<":
            holds = l < r - tol
        elif self.op == ">":
            holds = l > r + tol
        else:
            raise ValueError(f"Unknown relational op '{self.op}'")
        return bool(holds), float(l), float(r)

    def to_sympy(self) -> sp.Rel:
        return sp.Rel(self.left.to_sympy(), self.right.to_sympy(), self.op)

    def to_latex(self) -> str:
        op_map = {"<=": r"\le", ">=": r"\ge", "==": "=", "<": "<", ">": ">"}
        return f"{self.left.to_latex()} {op_map[self.op]} {self.right.to_latex()}"

    def to_lean(self) -> str:
        op_map = {"<=": "≤", ">=": "≥", "==": "=", "<": "<", ">": ">"}
        return f"{self.left.to_lean()} {op_map[self.op]} {self.right.to_lean()}"

    def get_invariant_names(self) -> Set[str]:
        return self.left.get_invariant_names() | self.right.get_invariant_names()

    @property
    def variables(self) -> Set[str]:
        return self.left.variables | self.right.variables

    @property
    def complexity(self) -> int:
        return self.left.complexity + self.right.complexity + 1

    @property
    def depth(self) -> int:
        return max(self.left.depth, self.right.depth) + 1

    def to_dict(self) -> Dict[str, Any]:
        return {
            "node_type": "relation",
            "op": self.op,
            "left": self.left.to_dict(),
            "right": self.right.to_dict(),
        }


class GuardPredicate(ASTBase):
    """Premise guard predicate restricting the domain of graphs for a conjecture."""

    node_type: Literal["guard"] = "guard"
    predicate_type: Literal["property", "comparison", "conjunction", "universal"] = "universal"
    property_name: Optional[str] = None
    negated: bool = False
    invariant: Optional[str] = None
    op: Optional[Literal["<=", ">=", "==", "<", ">"]] = None
    threshold: Optional[float] = None
    guards: Optional[List[GuardPredicate]] = None

    def __init__(self, property_name_or_type: Optional[str] = None, **kwargs: Any) -> None:
        if property_name_or_type is not None:
            if property_name_or_type in {"universal", "property", "comparison", "conjunction"}:
                kwargs["predicate_type"] = property_name_or_type
            else:
                kwargs["predicate_type"] = "property"
                kwargs["property_name"] = property_name_or_type
        if "predicate_type" not in kwargs:
            if kwargs.get("property_name"):
                kwargs["predicate_type"] = "property"
            elif kwargs.get("invariant"):
                kwargs["predicate_type"] = "comparison"
            elif kwargs.get("guards"):
                kwargs["predicate_type"] = "conjunction"
        if kwargs.get("predicate_type") == "universal" and any(kwargs.get(k) for k in ("property_name", "invariant", "guards")):
            raise ValueError("Universal guard cannot carry an ignored condition")
        super().__init__(**kwargs)

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, str):
            if self.predicate_type == "property":
                return self.property_name == other
            elif self.predicate_type == "universal":
                return other in {"universal", "True", "true"}
            return False
        return super().__eq__(other)

    def evaluate(
        self,
        G: Union[nx.Graph, GraphInstance],
        invariants: Optional[Dict[str, Union[int, float]]] = None,
    ) -> bool:
        if self.predicate_type == "universal":
            return True

        nx_g = G.to_networkx() if isinstance(G, GraphInstance) else G
        n = nx_g.number_of_nodes()

        if self.predicate_type == "property":
            prop = self.property_name
            val = False
            if prop == "is_connected":
                val = n >= 1 and nx.is_connected(nx_g)
            elif prop == "is_triangle_free":
                if invariants and "triangles" in invariants:
                    val = invariants["triangles"] == 0
                elif invariants and "triangle_count" in invariants:
                    val = invariants["triangle_count"] == 0
                else:
                    val = sum(nx.triangles(nx_g).values()) == 0
            elif prop == "is_bipartite":
                val = nx.is_bipartite(nx_g)
            elif prop == "is_regular":
                if n == 0:
                    val = True
                else:
                    degs = list(dict(nx_g.degree()).values())
                    val = min(degs) == max(degs)
            elif prop == "is_tree":
                val = n >= 1 and nx.is_tree(nx_g)
            elif prop == "is_planar":
                val = nx.check_planarity(nx_g)[0] if n > 0 else True
            else:
                # Check via GraphInvariantEvaluator
                val = bool(GraphInvariantEvaluator.evaluate_single(nx_g, prop))
            return (not val) if self.negated else val

        elif self.predicate_type == "comparison":
            inv_name = self.invariant or "order"
            if invariants and inv_name in invariants:
                val = float(invariants[inv_name])
            else:
                val = float(GraphInvariantEvaluator.evaluate_single(nx_g, inv_name))
            thresh = float(self.threshold or 0.0)
            tol = 1e-7
            if self.op == "<=":
                return val <= thresh + tol
            elif self.op == ">=":
                return val >= thresh - tol
            elif self.op == "==":
                return abs(val - thresh) <= tol
            elif self.op == "<":
                return val < thresh - tol
            elif self.op == ">":
                return val > thresh + tol

        elif self.predicate_type == "conjunction":
            if not self.guards:
                return True
            return all(g.evaluate(nx_g, invariants) for g in self.guards)

        return True

    def to_latex(self) -> str:
        if self.predicate_type == "universal":
            return r"\text{True}"
        if self.predicate_type == "property":
            prefix = r"\neg " if self.negated else ""
            labels = {
                "is_connected": r"\text{connected}",
                "is_triangle_free": r"\text{triangle-free}",
                "is_bipartite": r"\text{bipartite}",
                "is_regular": r"\text{regular}",
                "is_tree": r"\text{tree}",
                "is_planar": r"\text{planar}",
            }
            label = labels.get(self.property_name, self.property_name)
            return f"{prefix}G \\in \\mathcal{{G}}_{{{label}}}"
        if self.predicate_type == "comparison":
            op_tex = {"<=": r"\le", ">=": r"\ge", "==": "=", "<": "<", ">": ">"}.get(
                self.op, self.op
            )
            inv_tex = INVARIANT_LATEX_MAP.get(self.invariant, self.invariant)
            return f"{inv_tex} {op_tex} {self.threshold:g}"
        if self.predicate_type == "conjunction":
            return r" \land ".join(g.to_latex() for g in (self.guards or []))
        return r"\text{True}"

    def to_lean(self) -> str:
        if self.predicate_type == "universal":
            return "True"
        if self.predicate_type == "property":
            lean_props = {
                "is_connected": "G.Connected",
                "is_triangle_free": "G.CliqueFree 3",
                "is_bipartite": "G.Colorable 2",
                "is_regular": "(∃ d : ℕ, G.IsRegular d)",
                "is_tree": "G.IsTree",
                "is_planar": "G.IsPlanar",
            }
            stmt = lean_props.get(self.property_name, f"G.{self.property_name}")
            return f"(¬ {stmt})" if self.negated else stmt
        if self.predicate_type == "comparison":
            op_lean = {"<=": "≤", ">=": "≥", "==": "=", "<": "<", ">": ">"}.get(
                self.op, self.op
            )
            inv_lean = INVARIANT_LEAN_MAP.get(
                self.invariant, f"(G.{self.invariant} : ℝ)"
            )
            return f"({inv_lean} {op_lean} {self.threshold:g})"
        if self.predicate_type == "conjunction":
            return " ∧ ".join(g.to_lean() for g in (self.guards or []))
        return "True"

    @property
    def complexity(self) -> int:
        if self.predicate_type == "conjunction" and self.guards:
            return sum(g.complexity for g in self.guards) + 1
        return 1

    @property
    def variables(self) -> Set[str]:
        if self.predicate_type == "comparison" and self.invariant:
            return {INVARIANT_ALIASES.get(self.invariant, self.invariant)}
        if self.predicate_type == "conjunction" and self.guards:
            res: Set[str] = set()
            for g in self.guards:
                res |= g.variables
            return res
        return set()

    def to_dict(self) -> Dict[str, Any]:
        return {
            "node_type": "guard",
            "predicate_type": self.predicate_type,
            "property_name": self.property_name,
            "negated": self.negated,
            "invariant": self.invariant,
            "op": self.op,
            "threshold": self.threshold,
            "guards": [g.to_dict() for g in self.guards] if self.guards else None,
        }

    @classmethod
    def from_dict(cls, data: Union[Dict[str, Any], str]) -> GuardPredicate:
        if isinstance(data, str):
            return cls(property_name_or_type=data)
        guards = (
            [cls.from_dict(g) for g in data["guards"]]
            if data.get("guards")
            else None
        )
        return cls(
            predicate_type=data.get("predicate_type", "universal"),
            property_name=data.get("property_name"),
            negated=bool(data.get("negated", False)),
            invariant=data.get("invariant"),
            op=data.get("op"),
            threshold=data.get("threshold"),
            guards=guards,
        )


GuardPredicate.model_rebuild()


class Conjecture(BaseModel):
    """Mathematical conjecture relating graph invariants."""

    model_config = ConfigDict(frozen=True, extra="allow")

    id: str
    statement: str
    lhs_expr: ExpressionNode
    rel: Literal["<=", ">=", "==", "<", ">"]
    rhs_expr: ExpressionNode
    guard_predicate: Optional[Union[GuardPredicate, str]] = None
    complexity: int = 1
    metadata: Dict[str, Any] = Field(default_factory=dict)

    @classmethod
    def create(
        cls,
        id: str,
        lhs: ExpressionNode,
        rel: Literal["<=", ">=", "==", "<", ">"],
        rhs: ExpressionNode,
        guard: Optional[Union[GuardPredicate, str]] = None,
        statement: Optional[str] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> Conjecture:
        if statement is None:
            rel_str = f"{lhs.to_latex()} {rel} {rhs.to_latex()}"
            if guard:
                guard_str = (
                    guard if isinstance(guard, str) else guard.to_latex()
                )
                statement = f"{guard_str} ==> {rel_str}"
            else:
                statement = rel_str
        comp = (
            lhs.complexity
            + rhs.complexity
            + 1
            + (
                (guard.complexity if isinstance(guard, GuardPredicate) else 1)
                if guard
                else 0
            )
        )
        return cls(
            id=id,
            statement=statement,
            lhs_expr=lhs,
            rel=rel,
            rhs_expr=rhs,
            guard_predicate=guard,
            complexity=comp,
            metadata=metadata or {},
        )

    def applies(
        self,
        G: Union[nx.Graph, GraphInstance],
        invariants: Optional[Dict[str, Union[int, float]]] = None,
    ) -> bool:
        if self.guard_predicate is None:
            return True
        if isinstance(self.guard_predicate, str):
            if self.guard_predicate == "universal":
                return True
            nx_g = G.to_networkx() if isinstance(G, GraphInstance) else G
            return bool(
                GraphInvariantEvaluator.evaluate_single(nx_g, self.guard_predicate)
            )
        return self.guard_predicate.evaluate(G, invariants)

    def evaluate(
        self,
        G: Union[nx.Graph, GraphInstance],
        invariants: Optional[Dict[str, Union[int, float]]] = None,
        evaluator: Optional[Any] = None,
    ) -> Tuple[bool, float, float]:
        """Evaluate conjecture on graph G.

        Returns (holds, lhs_val, rhs_val).
        Semantics:
        - If guard does not hold, returns (True, 0.0, 0.0) because premise does not apply.
        - If guard holds, returns (relation_holds, lhs_val, rhs_val).
        """
        nx_g = G.to_networkx() if isinstance(G, GraphInstance) else G

        # Build invariant environment if not provided
        env: Dict[str, Union[int, float]] = dict(invariants) if invariants is not None else {}

        # 1. Check premise guard applicability first; short-circuit if premise does not apply
        if not self.applies(nx_g, env):
            return (True, 0.0, 0.0)

        # 2. Only compute invariants needed by LHS and RHS if premise applies
        needed_vars = set(self.lhs_expr.variables) | set(self.rhs_expr.variables)
        missing_vars = [v for v in needed_vars if v not in env and INVARIANT_ALIASES.get(v) not in env]

        if missing_vars:
            eval_source = evaluator or GraphInvariantEvaluator
            computed = eval_source.evaluate(nx_g, missing_vars)
            env.update(computed)

        l_val = self.lhs_expr.evaluate(env)
        r_val = self.rhs_expr.evaluate(env)

        tol = 1e-7
        if self.rel == "<=":
            holds = l_val <= r_val + tol
        elif self.rel == ">=":
            holds = l_val >= r_val - tol
        elif self.rel == "==":
            holds = abs(l_val - r_val) <= tol
        elif self.rel == "<":
            holds = l_val < r_val - tol
        elif self.rel == ">":
            holds = l_val > r_val + tol
        else:
            raise ValueError(f"Unknown relation '{self.rel}'")

        return (bool(holds), float(l_val), float(r_val))

    def to_sympy(self) -> sp.Rel:
        return sp.Rel(self.lhs_expr.to_sympy(), self.rhs_expr.to_sympy(), self.rel)

    def is_tautology(self) -> bool:
        try:
            return bool(sp.simplify(self.to_sympy()) == True)  # noqa: E712
        except Exception:
            return False

    def is_contradiction(self) -> bool:
        try:
            return bool(sp.simplify(self.to_sympy()) == False)  # noqa: E712
        except Exception:
            return False

    def to_latex(self) -> str:
        rel_map = {"<=": r"\le", ">=": r"\ge", "==": "=", "<": "<", ">": ">"}
        body = f"{self.lhs_expr.to_latex()} {rel_map[self.rel]} {self.rhs_expr.to_latex()}"
        if self.guard_predicate:
            guard_tex = (
                self.guard_predicate
                if isinstance(self.guard_predicate, str)
                else self.guard_predicate.to_latex()
            )
            if guard_tex not in {r"\text{True}", "universal"}:
                return rf"\forall G \in \mathcal{{G}}, \quad {guard_tex} \implies {body}"
        return rf"\forall G \in \mathcal{{G}}, \quad {body}"

    def to_lean(
        self,
        challenge_module: str = "ExtremalBound",
        theorem_name: str = "main_theorem",
    ) -> str:
        rel_map = {"<=": "≤", ">=": "≥", "==": "=", "<": "<", ">": ">"}
        core_rel = (
            f"{self.lhs_expr.to_lean()} {rel_map[self.rel]} {self.rhs_expr.to_lean()}"
        )
        if self.guard_predicate:
            guard_lean = (
                self.guard_predicate
                if isinstance(self.guard_predicate, str)
                else self.guard_predicate.to_lean()
            )
            if guard_lean != "True":
                statement = f"{guard_lean} → {core_rel}"
            else:
                statement = core_rel
        else:
            statement = core_rel

        return (
            "import Mathlib\n\n"
            "namespace AutonomousMath\n\n"
            f"namespace {challenge_module}\n\n"
            f"theorem {theorem_name} {{V : Type*}} [Fintype V] [DecidableEq V] "
            f"(G : SimpleGraph V) [DecidableRel G.Adj] :\n"
            f"    {statement} := by\n"
            "  sorry\n\n"
            f"end {challenge_module}\n\n"
            "end AutonomousMath\n"
        )

    def to_comparator_json(
        self, challenge_module: str, solution_module: str, theorem_name: str
    ) -> Dict[str, Any]:
        return {
            "challenge_module": f"ComparatorChallenges.{challenge_module}",
            "solution_module": solution_module,
            "theorem_names": [f"AutonomousMath.{challenge_module}.{theorem_name}"],
            "definition_names": [],
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
            "enable_nanoda": False,
        }

    def to_dict(self) -> Dict[str, Any]:
        guard_val: Any = None
        if isinstance(self.guard_predicate, GuardPredicate):
            guard_val = self.guard_predicate.to_dict()
        elif isinstance(self.guard_predicate, str):
            guard_val = self.guard_predicate

        return {
            "id": self.id,
            "statement": self.statement,
            "lhs_expr": self.lhs_expr.to_dict(),
            "rel": self.rel,
            "rhs_expr": self.rhs_expr.to_dict(),
            "guard_predicate": guard_val,
            "complexity": self.complexity,
            "metadata": self.metadata,
        }

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> Conjecture:
        lhs = deserialize_expression(data["lhs_expr"])
        rhs = deserialize_expression(data["rhs_expr"])
        raw_guard = data.get("guard_predicate")
        guard: Optional[Union[GuardPredicate, str]] = None
        if isinstance(raw_guard, str):
            guard = raw_guard
        elif isinstance(raw_guard, dict):
            guard = GuardPredicate.from_dict(raw_guard)

        return cls(
            id=data["id"],
            statement=data["statement"],
            lhs_expr=lhs,
            rel=data["rel"],
            rhs_expr=rhs,
            guard_predicate=guard,
            complexity=int(data.get("complexity", 1)),
            metadata=data.get("metadata", {}),
        )
