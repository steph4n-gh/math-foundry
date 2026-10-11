"""Grammar production rules, depth-bounded generation, and validation.

Constructs well-formed ExpressionNode trees and candidate conjectures
subject to 6-tier algebraic and domain-specific pruning invariants.
"""

from __future__ import annotations

from typing import Dict, Iterator, List, Optional, Set, Tuple
from pydantic import BaseModel, ConfigDict, Field

from autonomous_math.core.ast import (
    INTEGER_VALUED_INVARIANTS,
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    ExpressionNode,
    GuardPredicate,
    InvariantNode,
    UnaryOpNode,
)
from autonomous_math.core.invariants import INVARIANT_ALIASES


class GrammarConfig(BaseModel):
    """Configuration for grammar production rules and depth limits."""

    model_config = ConfigDict(frozen=True)

    invariants: List[str] = Field(
        default_factory=lambda: [
            "order",
            "size",
            "max_degree",
            "min_degree",
            "average_degree",
            "density",
            "chromatic_number",
            "clique_number",
            "independence_number",
            "girth",
            "diameter",
            "radius",
            "spectral_radius",
            "smallest_adjacency_eigenvalue",
            "algebraic_connectivity",
            "laplacian_spectral_radius",
            "hoffman_bound",
            "wilf_bound",
            "triangle_count",
            "signless_laplacian_spectral_radius",
            "normalized_laplacian_spectral_gap",
            "normalized_laplacian_spectral_radius",
            "estrada_index",
            "graph_energy",
            "complement_spectral_radius",
            "nordhaus_gaddum_spectral_sum",
            "nordhaus_gaddum_spectral_product",
        ]
    )
    constants: List[float] = Field(default_factory=lambda: [1.0, 2.0, 0.5])
    unary_ops: List[str] = Field(
        default_factory=lambda: ["sqrt", "sqr", "floor", "ceil", "inv", "exp"]
    )
    binary_ops: List[str] = Field(
        default_factory=lambda: ["+", "-", "*", "/", "max", "min"]
    )
    relations: List[str] = Field(default_factory=lambda: ["<=", ">=", "=="])
    max_depth: int = 4
    max_complexity: int = 5


class ExpressionGenerator:
    """Systematically constructs valid ExpressionNode trees up to bounded depth."""

    def __init__(self, config: Optional[GrammarConfig] = None) -> None:
        self.config = config or GrammarConfig()

    def generate(self, max_depth: Optional[int] = None) -> List[ExpressionNode]:
        depth_limit = max_depth if max_depth is not None else self.config.max_depth
        expressions_by_depth: Dict[int, List[ExpressionNode]] = {1: []}

        # Level 1: Terminals (Invariants + Constants)
        for inv_name in self.config.invariants:
            expressions_by_depth[1].append(InvariantNode(name=inv_name))
        for c_val in self.config.constants:
            expressions_by_depth[1].append(ConstantNode(value=c_val))

        seen_keys: Set[str] = {e.canonical_key for e in expressions_by_depth[1]}

        # Level d: Inductive expansion
        for d in range(2, depth_limit + 1):
            expressions_by_depth[d] = []

            # 1. Unary Operations on expressions of depth d - 1
            for child in expressions_by_depth[d - 1]:
                for op in self.config.unary_ops:
                    if self._is_invalid_unary(op, child):
                        continue
                    u_node = UnaryOpNode(op=op, child=child)
                    if u_node.canonical_key not in seen_keys:
                        seen_keys.add(u_node.canonical_key)
                        expressions_by_depth[d].append(u_node)

            # 2. Binary Operations where max(depth(left), depth(right)) == d - 1
            prev_all = [e for k in range(1, d) for e in expressions_by_depth[k]]
            strictly_prev = expressions_by_depth[d - 1]

            for op in self.config.binary_ops:
                is_comm = op in {"+", "*", "max", "min"}
                for left in strictly_prev:
                    for right in prev_all:
                        if self._is_invalid_binary(op, left, right, is_comm):
                            continue
                        b_node = BinaryOpNode(op=op, left=left, right=right)
                        if b_node.canonical_key not in seen_keys:
                            seen_keys.add(b_node.canonical_key)
                            expressions_by_depth[d].append(b_node)

                # Reverse pairings where right is strictly depth d-1 and left is depth < d-1
                if not is_comm:
                    strictly_earlier = [
                        e for k in range(1, d - 1) for e in expressions_by_depth[k]
                    ]
                    for left in strictly_earlier:
                        for right in strictly_prev:
                            if self._is_invalid_binary(op, left, right, is_comm=False):
                                continue
                            b_node = BinaryOpNode(op=op, left=left, right=right)
                            if b_node.canonical_key not in seen_keys:
                                seen_keys.add(b_node.canonical_key)
                                expressions_by_depth[d].append(b_node)

        all_exprs = [
            e for d in range(1, depth_limit + 1) for e in expressions_by_depth[d]
        ]
        return [e for e in all_exprs if e.complexity <= self.config.max_complexity]

    def _is_invalid_unary(self, op: str, child: ExpressionNode) -> bool:
        # Constant folding
        if isinstance(child, ConstantNode):
            return True
        # Graph invariant non-negativity: abs is redundant
        if op == "abs":
            return True
        # Discrete invariants: floor/ceil are no-ops
        if op in {"floor", "ceil"}:
            if (
                isinstance(child, InvariantNode)
                and child.canonical_name() in INTEGER_VALUED_INVARIANTS
            ):
                return True
        # Inverse cancellations
        if isinstance(child, UnaryOpNode):
            if op == "neg" and child.op == "neg":
                return True
            if op == "inv" and child.op == "inv":
                return True
            if op == "sqr" and child.op == "sqrt":
                return True
            if op == "sqrt" and child.op == "sqr":
                return True
        return False

    def _is_invalid_binary(
        self, op: str, left: ExpressionNode, right: ExpressionNode, is_comm: bool
    ) -> bool:
        # Commutative canonical ordering
        if is_comm and left.canonical_key > right.canonical_key:
            return True
        # Constant folding: two constants combine into one
        if isinstance(left, ConstantNode) and isinstance(right, ConstantNode):
            return True
        # Identical nodes
        if left.canonical_key == right.canonical_key:
            if op in {"-", "/", "max", "min"}:
                return True
        # Division by zero
        if (
            op == "/"
            and isinstance(right, ConstantNode)
            and abs(right.value) < 1e-12
        ):
            return True
        # Trivial algebraic identities
        if op == "+" and (
            self._is_constant_val(left, 0.0) or self._is_constant_val(right, 0.0)
        ):
            return True
        if op == "-" and self._is_constant_val(right, 0.0):
            return True
        if op == "*" and (
            self._is_constant_val(left, 1.0) or self._is_constant_val(right, 1.0)
        ):
            return True
        if op == "*" and (
            self._is_constant_val(left, 0.0) or self._is_constant_val(right, 0.0)
        ):
            return True
        if op == "/" and self._is_constant_val(right, 1.0):
            return True
        return False

    def _is_constant_val(self, node: ExpressionNode, val: float) -> bool:
        return isinstance(node, ConstantNode) and abs(node.value - val) < 1e-9


class GuardGenerator:
    """Generates atomic and conjunction graph property guards."""

    @staticmethod
    def generate_property_guards() -> List[GuardPredicate]:
        props = [
            "is_connected",
            "is_triangle_free",
            "is_bipartite",
            "is_regular",
            "is_tree",
            "is_planar",
        ]
        return [
            GuardPredicate(predicate_type="property", property_name=p)
            for p in props
        ]

    @staticmethod
    def generate_threshold_guards() -> List[GuardPredicate]:
        return [
            GuardPredicate(
                predicate_type="comparison", invariant="order", op=">=", threshold=3.0
            ),
            GuardPredicate(
                predicate_type="comparison",
                invariant="min_degree",
                op=">=",
                threshold=1.0,
            ),
            GuardPredicate(
                predicate_type="comparison", invariant="girth", op=">=", threshold=4.0
            ),
            GuardPredicate(
                predicate_type="comparison", invariant="girth", op=">=", threshold=5.0
            ),
        ]

    @classmethod
    def generate_all_guards(cls) -> List[GuardPredicate]:
        guards = [GuardPredicate(predicate_type="universal")]
        guards.extend(cls.generate_property_guards())
        guards.extend(cls.generate_threshold_guards())

        # Compound pairs
        guards.append(
            GuardPredicate(
                predicate_type="conjunction",
                guards=[
                    GuardPredicate(
                        predicate_type="property", property_name="is_connected"
                    ),
                    GuardPredicate(
                        predicate_type="property", property_name="is_triangle_free"
                    ),
                ],
            )
        )
        return guards


class GrammarConjectureGenerator:
    """Generates candidate conjectures pairing target invariants with generated expressions."""

    def __init__(self, config: Optional[GrammarConfig] = None) -> None:
        self.config = config or GrammarConfig()
        self.expr_gen = ExpressionGenerator(self.config)

    def generate_for_target(
        self,
        target_invariant: str,
        relations: Optional[List[str]] = None,
        max_rhs_depth: int = 2,
        guards: Optional[List[GuardPredicate]] = None,
    ) -> Iterator[Conjecture]:
        lhs = InvariantNode(name=target_invariant)
        rels = relations or self.config.relations
        rhs_exprs = self.expr_gen.generate(max_depth=max_rhs_depth)
        guard_list = (
            guards
            if guards is not None
            else [GuardPredicate(predicate_type="universal")]
        )

        idx = 0
        for rhs in rhs_exprs:
            if rhs.canonical_key == lhs.canonical_key:
                continue
            for rel in rels:
                for g in guard_list:
                    idx += 1
                    conj_id = f"conj_{target_invariant}_{rel}_{idx}"
                    yield Conjecture.create(
                        id=conj_id,
                        lhs=lhs,
                        rel=rel,
                        rhs=rhs,
                        guard=g,
                    )


# Validation routines


def validate_expression(
    expr: ExpressionNode, config: Optional[GrammarConfig] = None
) -> List[str]:
    cfg = config or GrammarConfig()
    errors: List[str] = []

    if expr.depth > cfg.max_depth:
        errors.append(
            f"Depth {expr.depth} exceeds configured maximum depth {cfg.max_depth}."
        )

    allowed_vars = set(cfg.invariants)
    for k in list(allowed_vars):
        for alias, canon in INVARIANT_ALIASES.items():
            if canon == k:
                allowed_vars.add(alias)

    for v in expr.variables:
        canon_v = INVARIANT_ALIASES.get(v, v)
        if v not in allowed_vars and canon_v not in allowed_vars:
            errors.append(f"Invariant '{v}' is not recognized in grammar invariants.")

    if isinstance(expr, BinaryOpNode):
        if (
            expr.op == "/"
            and isinstance(expr.right, ConstantNode)
            and abs(expr.right.value) < 1e-12
        ):
            errors.append("Division by constant zero detected in expression.")
        errors.extend(validate_expression(expr.left, cfg))
        errors.extend(validate_expression(expr.right, cfg))
    elif isinstance(expr, UnaryOpNode):
        if (
            expr.op == "inv"
            and isinstance(expr.child, ConstantNode)
            and abs(expr.child.value) < 1e-12
        ):
            errors.append("Inverse of constant zero detected in expression.")
        if (
            expr.op == "sqrt"
            and isinstance(expr.child, ConstantNode)
            and expr.child.value < 0
        ):
            errors.append("Square root of negative constant detected in expression.")
        errors.extend(validate_expression(expr.child, cfg))

    return errors


def validate_conjecture(
    conj: Conjecture, config: Optional[GrammarConfig] = None
) -> List[str]:
    cfg = config or GrammarConfig()
    errors: List[str] = []

    errors.extend(validate_expression(conj.lhs_expr, cfg))
    errors.extend(validate_expression(conj.rhs_expr, cfg))

    if conj.rel not in {"<=", ">=", "==", "<", ">"}:
        errors.append(f"Relational operator '{conj.rel}' is not a valid relation.")

    if isinstance(conj.guard_predicate, GuardPredicate):
        if conj.guard_predicate.predicate_type == "property":
            valid_props = {
                "is_connected",
                "is_triangle_free",
                "is_bipartite",
                "is_regular",
                "is_tree",
                "is_planar",
            }
            if conj.guard_predicate.property_name not in valid_props:
                errors.append(
                    f"Property guard '{conj.guard_predicate.property_name}' is not in valid properties {valid_props}."
                )

    return errors
