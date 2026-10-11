"""Conjecture Filtration System based on Graffiti / TxGraffiti principles.

Provides:
- TrivialityFilter: Eliminates algebraic tautologies and contradictions via SymPy.
- DalmatiansFilter: Eliminates loose or non-sharp bounds via empirical envelope analysis.
- EchoFilter: Eliminates duplicates, constant weakenings, and transitive implications.
- ConjectureFilterPipeline: Composes filters into an end-to-end filtration pipeline.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Set, Tuple, Union
import networkx as nx
import numpy as np
import sympy as sp

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    ExpressionNode,
    GuardPredicate,
    InvariantNode,
)
from autonomous_math.core.graph_types import GraphInstance
from autonomous_math.core.invariants import GraphInvariantEvaluator


class TrivialityFilter:
    """Discards algebraically trivial conjectures using SymPy symbolic simplification."""

    @classmethod
    def is_trivial(cls, conj: Conjecture) -> bool:
        """Determines whether a conjecture is an algebraic tautology or contradiction."""
        # 1. Syntactic identity: LHS == RHS
        if conj.lhs_expr.canonical_key == conj.rhs_expr.canonical_key:
            if conj.rel in {"<=", ">=", "=="}:
                return True  # Reflexive tautology: x <= x
            elif conj.rel in {"<", ">"}:
                return True  # Self-contradiction: x < x

        # 2. SymPy Relational Simplification
        try:
            rel_sp = conj.to_sympy()
            simplified = sp.simplify(rel_sp)
            if simplified == True:  # noqa: E712
                return True
            if simplified == False:  # noqa: E712
                return True
        except Exception:
            pass

        # 3. Difference Analysis: diff = RHS - LHS
        try:
            lhs_sp = conj.lhs_expr.to_sympy()
            rhs_sp = conj.rhs_expr.to_sympy()
            diff = sp.simplify(rhs_sp - lhs_sp)

            if conj.rel == "<=":
                # If RHS - LHS >= 0 always holds identically
                if diff.is_number and float(diff) >= -1e-9:
                    return True
                if diff.is_number and float(diff) < -1e-9:
                    return True  # Contradiction: x <= x - c for c > 0
            elif conj.rel == ">=":
                if diff.is_number and float(diff) <= 1e-9:
                    return True
                if diff.is_number and float(diff) > 1e-9:
                    return True
            elif conj.rel == "==":
                if diff.is_number and abs(float(diff)) < 1e-9:
                    return True
        except Exception:
            pass

        # 4. Inherent Domain Trivialities (e.g. order >= 0)
        if conj.rel == ">=":
            if isinstance(conj.rhs_expr, ConstantNode) and conj.rhs_expr.value <= 0:
                if isinstance(conj.lhs_expr, InvariantNode):
                    return True

        return False

    @classmethod
    def filter(cls, conjectures: List[Conjecture]) -> List[Conjecture]:
        """Filters a list of conjectures, returning only non-trivial ones."""
        return [c for c in conjectures if not cls.is_trivial(c)]


class DalmatiansFilter:
    """Implements Fajtlowicz's Dalmatians sharpness heuristic.

    Discards candidate bounds that provide no improvement on any sample graph instance
    over previously accepted bounds for the same invariant and relation.
    Prunes previously accepted bounds that become strictly dominated by a newly accepted bound.
    """

    @classmethod
    def filter(
        cls,
        conjectures: List[Conjecture],
        test_instances: List[Union[nx.Graph, GraphInstance]],
        tol: float = 1e-5,
    ) -> List[Conjecture]:
        """Filters out strictly weaker or loose bounds across test instances."""
        if not test_instances:
            return conjectures

        accepted: List[Conjecture] = []
        # Key: (target_invariant_canonical, rel) -> List[Tuple[Conjecture, List[float]]]
        accepted_bounds: Dict[Tuple[str, str], List[Tuple[Conjecture, List[float]]]] = {}

        for conj in conjectures:
            # 1. Evaluate empirical validity on all instances
            valid_on_all = True
            eval_vals: List[float] = []

            for G in test_instances:
                try:
                    holds, l_val, r_val = conj.evaluate(G)
                    if not holds or np.isnan(r_val) or np.isinf(r_val):
                        valid_on_all = False
                        break
                    eval_vals.append(r_val)
                except Exception:
                    valid_on_all = False
                    break

            if not valid_on_all:
                continue

            # 2. Check strict envelope improvement
            key = (
                (
                    conj.lhs_expr.canonical_name()
                    if isinstance(conj.lhs_expr, InvariantNode)
                    else conj.lhs_expr.canonical_key
                ),
                conj.rel,
            )

            prior = accepted_bounds.get(key, [])
            if not prior:
                # First valid bound for this key is accepted
                accepted.append(conj)
                accepted_bounds[key] = [(conj, eval_vals)]
                continue

            pruned_ids: Set[int] = set()

            if conj.rel == "<=":
                # For upper bound: candidate is informative if it provides a strictly
                # tighter (smaller) upper bound on at least one instance
                # Check 1: Reject if ANY prior bound dominates candidate everywhere
                is_dominated = False
                for _, prev_vals in prior:
                    if all(prev_r <= cand_r + tol for cand_r, prev_r in zip(eval_vals, prev_vals)):
                        is_dominated = True
                        break
                if is_dominated:
                    continue

                # Check 2: Accept if candidate strictly improves the upper envelope on at least one instance
                # OR if candidate strictly dominates ANY existing prior bound everywhere
                has_envelope_improvement = any(
                    all(cand_r < prev_vals[k] - tol for _, prev_vals in prior)
                    for k, cand_r in enumerate(eval_vals)
                )
                dominates_prior = any(
                    all(cand_r <= prev_r + tol for cand_r, prev_r in zip(eval_vals, prev_vals))
                    and any(cand_r < prev_r - tol for cand_r, prev_r in zip(eval_vals, prev_vals))
                    for _, prev_vals in prior
                )
                if not (has_envelope_improvement or dominates_prior):
                    continue

                # Collective Pareto envelope pruning: an accepted bound is retained in the pool
                # iff it is strictly tighter than all other retained bounds on at least one instance.
                # Any prior bound collectively dominated by the pool is pruned.
                pool = list(prior) + [(conj, eval_vals)]
                for prev_conj, prev_vals in prior:
                    others = [
                        vals
                        for c, vals in pool
                        if id(c) != id(prev_conj) and id(c) not in pruned_ids
                    ]
                    if not others:
                        continue
                    is_strictly_tighter = any(
                        prev_r < min(o[k] for o in others) - tol
                        for k, prev_r in enumerate(prev_vals)
                    )
                    if not is_strictly_tighter:
                        pruned_ids.add(id(prev_conj))

            elif conj.rel in {">=", ">"}:
                # For lower bound: candidate is informative if it provides a strictly
                # larger lower bound on at least one instance
                # Check 1: Reject if ANY prior bound dominates candidate everywhere
                is_dominated = False
                for _, prev_vals in prior:
                    if all(prev_r >= cand_r - tol for cand_r, prev_r in zip(eval_vals, prev_vals)):
                        is_dominated = True
                        break
                if is_dominated:
                    continue

                # Check 2: Accept if candidate strictly improves the lower envelope on at least one instance
                # OR if candidate strictly dominates ANY existing prior bound everywhere
                has_envelope_improvement = any(
                    all(cand_r > prev_vals[k] + tol for _, prev_vals in prior)
                    for k, cand_r in enumerate(eval_vals)
                )
                dominates_prior = any(
                    all(cand_r >= prev_r - tol for cand_r, prev_r in zip(eval_vals, prev_vals))
                    and any(cand_r > prev_r + tol for cand_r, prev_r in zip(eval_vals, prev_vals))
                    for _, prev_vals in prior
                )
                if not (has_envelope_improvement or dominates_prior):
                    continue

                # Collective Pareto envelope pruning: an accepted bound is retained in the pool
                # iff it is strictly tighter than all other retained bounds on at least one instance.
                # Any prior bound collectively dominated by the pool is pruned.
                pool = list(prior) + [(conj, eval_vals)]
                for prev_conj, prev_vals in prior:
                    others = [
                        vals
                        for c, vals in pool
                        if id(c) != id(prev_conj) and id(c) not in pruned_ids
                    ]
                    if not others:
                        continue
                    is_strictly_tighter = any(
                        prev_r > max(o[k] for o in others) + tol
                        for k, prev_r in enumerate(prev_vals)
                    )
                    if not is_strictly_tighter:
                        pruned_ids.add(id(prev_conj))
            else:
                pruned_ids = set()

            # Evict pruned obsolete bounds and insert new bound
            accepted_bounds[key] = [
                (prev_conj, prev_vals)
                for prev_conj, prev_vals in prior
                if id(prev_conj) not in pruned_ids
            ]
            accepted_bounds[key].append((conj, eval_vals))

            accepted = [c for c in accepted if id(c) not in pruned_ids]
            accepted.append(conj)

        return accepted


def _fast_constant_diff(e_cand: ExpressionNode, e_t: ExpressionNode) -> Optional[float]:
    """Computes e_cand - e_t quickly if both expressions share linear invariant structure."""
    if isinstance(e_cand, ConstantNode) and isinstance(e_t, ConstantNode):
        return e_cand.value - e_t.value
    if (
        isinstance(e_cand, BinaryOpNode)
        and isinstance(e_t, BinaryOpNode)
        and e_cand.op == e_t.op
    ):
        if (
            e_cand.left.canonical_key == e_t.left.canonical_key
            and isinstance(e_cand.right, ConstantNode)
            and isinstance(e_t.right, ConstantNode)
        ):
            if e_cand.op == "+":
                return e_cand.right.value - e_t.right.value
            elif e_cand.op == "-":
                return -(e_cand.right.value - e_t.right.value)
        if (
            e_cand.right.canonical_key == e_t.right.canonical_key
            and isinstance(e_cand.left, ConstantNode)
            and isinstance(e_t.left, ConstantNode)
        ):
            if e_cand.op == "+":
                return e_cand.left.value - e_t.left.value
    return None


class EchoFilter:
    """Implements Graffiti's Echo heuristic to remove redundant or subsumed bounds."""

    @staticmethod
    def _guard_key(c: Conjecture) -> str:
        """Extracts canonical string representation of conjecture guard predicate."""
        g = c.guard_predicate
        if g is None or g == "universal":
            return ""
        if isinstance(g, str):
            return g
        if isinstance(g, GuardPredicate):
            return "" if g.predicate_type == "universal" else g.to_latex()
        return str(g)

    @classmethod
    def _guards_compatible(cls, t_guard: str, cand_guard: str) -> bool:
        """Determines if theorem guard subsumes candidate guard."""
        if not t_guard:
            return True
        return t_guard == cand_guard

    @classmethod
    def _is_duplicate_or_algebraically_equivalent(cls, t: Conjecture, cand: Conjecture) -> bool:
        """Checks if cand is an exact duplicate or algebraic syntactic equivalent of t."""
        if cand.id == t.id or cand.statement == t.statement:
            return True

        t_lhs = t.lhs_expr.canonical_key
        t_rhs = t.rhs_expr.canonical_key
        c_lhs = cand.lhs_expr.canonical_key
        c_rhs = cand.rhs_expr.canonical_key

        # Direct canonical AST match
        if t_lhs == c_lhs and t_rhs == c_rhs and t.rel == cand.rel:
            return True

        # Inverted relation canonical match: A <= B <=> B >= A
        if t.rel == "<=" and cand.rel == ">=" and t_lhs == c_rhs and t_rhs == c_lhs:
            return True
        if t.rel == ">=" and cand.rel == "<=" and t_lhs == c_rhs and t_rhs == c_lhs:
            return True

        # Equality symmetry: A == B <=> B == A
        if t.rel == "==" and cand.rel == "==" and (
            (t_lhs == c_lhs and t_rhs == c_rhs) or (t_lhs == c_rhs and t_rhs == c_lhs)
        ):
            return True

        # Equality subsumes inequality: A == B implies A <= B and B <= A
        if t.rel == "==" and cand.rel in {"<=", ">="} and (
            (t_lhs == c_lhs and t_rhs == c_rhs) or (t_lhs == c_rhs and t_rhs == c_lhs)
        ):
            return True

        # SymPy algebraic equality check (if canonical keys differ)
        if t.rel == cand.rel:
            fd_lhs = _fast_constant_diff(cand.lhs_expr, t.lhs_expr)
            fd_rhs = _fast_constant_diff(cand.rhs_expr, t.rhs_expr)
            if fd_lhs == 0.0 and fd_rhs == 0.0:
                return True
            try:
                diff_lhs = sp.simplify(cand.lhs_expr.to_sympy() - t.lhs_expr.to_sympy())
                diff_rhs = sp.simplify(cand.rhs_expr.to_sympy() - t.rhs_expr.to_sympy())
                if diff_lhs.is_zero and diff_rhs.is_zero:
                    return True
            except Exception:
                pass

        return False

    @classmethod
    def _is_constant_relaxation(cls, t: Conjecture, cand: Conjecture) -> bool:
        """Checks if cand is a constant relaxation (algebraic weakening) of theorem t."""
        t_lhs = t.lhs_expr.canonical_key
        c_lhs = cand.lhs_expr.canonical_key

        # 1. Standard orientation: same LHS and same relation
        if t_lhs == c_lhs and t.rel == cand.rel:
            fd = _fast_constant_diff(cand.rhs_expr, t.rhs_expr)
            if fd is not None:
                if cand.rel == "<=" and fd >= -1e-9:
                    return True
                elif cand.rel == ">=" and fd <= 1e-9:
                    return True
            else:
                try:
                    c_sym = cand.rhs_expr.to_sympy()
                    t_sym = t.rhs_expr.to_sympy()
                    diff = sp.simplify(c_sym - t_sym)
                    if cand.rel == "<=" and diff.is_number and float(diff) >= -1e-9:
                        return True
                    elif cand.rel == ">=" and diff.is_number and float(diff) <= 1e-9:
                        return True
                except Exception:
                    pass

        # 2. Inverted orientation: t: L <= R_t, cand: R_c >= L (cand is L <= R_c)
        if t.rel == "<=" and cand.rel == ">=" and t_lhs == cand.rhs_expr.canonical_key:
            fd = _fast_constant_diff(cand.lhs_expr, t.rhs_expr)
            if fd is not None and fd >= -1e-9:
                return True
            try:
                c_sym = cand.lhs_expr.to_sympy()
                t_sym = t.rhs_expr.to_sympy()
                diff = sp.simplify(c_sym - t_sym)
                if diff.is_number and float(diff) >= -1e-9:
                    return True
            except Exception:
                pass

        # 3. Inverted orientation: t: L >= R_t, cand: R_c <= L (cand is L >= R_c)
        if t.rel == ">=" and cand.rel == "<=" and t_lhs == cand.rhs_expr.canonical_key:
            fd = _fast_constant_diff(cand.lhs_expr, t.rhs_expr)
            if fd is not None and fd <= 1e-9:
                return True
            try:
                c_sym = cand.lhs_expr.to_sympy()
                t_sym = t.rhs_expr.to_sympy()
                diff = sp.simplify(c_sym - t_sym)
                if diff.is_number and float(diff) <= 1e-9:
                    return True
            except Exception:
                pass

        return False

    @classmethod
    def filter(
        cls,
        conjectures: List[Conjecture],
        existing_theorems: Optional[List[Conjecture]] = None,
    ) -> List[Conjecture]:
        """Filters out conjectures that are duplicates, constant weakenings, or transitivity subsumed."""
        theorems: List[Conjecture] = list(existing_theorems) if existing_theorems is not None else []
        accepted: List[Conjecture] = []

        dag = nx.DiGraph()

        def add_to_dag(c: Conjecture) -> None:
            u = c.lhs_expr.canonical_key
            v = c.rhs_expr.canonical_key
            g_key = cls._guard_key(c)

            if c.rel in {"<=", "<"}:
                dag.add_edge(u, v, guard=g_key)
            elif c.rel in {">=", ">"}:
                dag.add_edge(v, u, guard=g_key)
            elif c.rel == "==":
                dag.add_edge(u, v, guard=g_key)
                dag.add_edge(v, u, guard=g_key)

        for t in theorems:
            add_to_dag(t)

        def is_subsumed(cand: Conjecture) -> bool:
            cand_g = cls._guard_key(cand)

            # 1. Exact duplication and constant relaxation check against active theorems
            for t in theorems:
                t_g = cls._guard_key(t)
                if not cls._guards_compatible(t_g, cand_g):
                    continue
                if cls._is_duplicate_or_algebraically_equivalent(t, cand):
                    return True
                if cls._is_constant_relaxation(t, cand):
                    return True

            # 2. Transitive subsumption via active inequality DAG
            sub_edges = [
                (u, v)
                for u, v, d in dag.edges(data=True)
                if d.get("guard", "") in {"", cand_g}
            ]
            cand_dag = nx.DiGraph(sub_edges)

            u_le = (
                cand.lhs_expr.canonical_key
                if cand.rel in {"<=", "<"}
                else cand.rhs_expr.canonical_key
            )
            v_le = (
                cand.rhs_expr.canonical_key
                if cand.rel in {"<=", "<"}
                else cand.lhs_expr.canonical_key
            )

            if cand.rel in {"<=", "<", ">=", ">"}:
                if cand_dag.has_node(u_le) and cand_dag.has_node(v_le):
                    if u_le != v_le and nx.has_path(cand_dag, u_le, v_le):
                        return True
            elif cand.rel == "==":
                u = cand.lhs_expr.canonical_key
                v = cand.rhs_expr.canonical_key
                if cand_dag.has_node(u) and cand_dag.has_node(v):
                    if nx.has_path(cand_dag, u, v) and nx.has_path(cand_dag, v, u):
                        return True

            return False

        for cand in conjectures:
            if is_subsumed(cand):
                continue

            # Retroactive eviction: prune previously accepted candidates subsumed by tighter cand
            evicted: Set[str] = set()
            for prev in accepted:
                cand_g = cls._guard_key(cand)
                prev_g = cls._guard_key(prev)
                if cls._guards_compatible(cand_g, prev_g):
                    if (
                        cls._is_duplicate_or_algebraically_equivalent(cand, prev)
                        or cls._is_constant_relaxation(cand, prev)
                    ):
                        evicted.add(prev.id)

            if evicted:
                accepted = [c for c in accepted if c.id not in evicted]
                theorems = [t for t in theorems if t.id not in evicted]
                dag = nx.DiGraph()
                for t in theorems:
                    add_to_dag(t)

            accepted.append(cand)
            theorems.append(cand)
            add_to_dag(cand)

        # Final pass: Retroactive transitive reduction on accepted candidates within the batch
        final_accepted: List[Conjecture] = []
        for cand in accepted:
            if cand.rel not in {"<=", "<", ">=", ">"}:
                final_accepted.append(cand)
                continue

            cand_g = cls._guard_key(cand)
            sub_edges = [
                (u, v)
                for u, v, d in dag.edges(data=True)
                if d.get("guard", "") in {"", cand_g}
            ]
            active_dag = nx.DiGraph(sub_edges)

            u = (
                cand.lhs_expr.canonical_key
                if cand.rel in {"<=", "<"}
                else cand.rhs_expr.canonical_key
            )
            v = (
                cand.rhs_expr.canonical_key
                if cand.rel in {"<=", "<"}
                else cand.lhs_expr.canonical_key
            )

            if active_dag.has_node(u) and active_dag.has_node(v):
                H = active_dag.copy()
                if H.has_edge(u, v):
                    H.remove_edge(u, v)
                if u != v and nx.has_path(H, u, v):
                    if dag.has_edge(u, v):
                        dag.remove_edge(u, v)
                    continue

            final_accepted.append(cand)

        return final_accepted


class ConjectureFilterPipeline:
    """Unified sequential pipeline chaining Triviality, Dalmatians, and Echo filters."""

    def __init__(
        self,
        test_instances: Optional[List[Union[nx.Graph, GraphInstance]]] = None,
        existing_theorems: Optional[List[Conjecture]] = None,
    ) -> None:
        self.test_instances = test_instances or []
        self.existing_theorems = existing_theorems or []

    def run(self, candidates: List[Conjecture]) -> List[Conjecture]:
        """Runs candidate conjectures through all filtration stages."""
        # 1. Triviality Filter
        stage1 = TrivialityFilter.filter(candidates)
        # 2. Dalmatians Filter
        stage2 = (
            DalmatiansFilter.filter(stage1, self.test_instances)
            if self.test_instances
            else stage1
        )
        # 3. Echo Filter
        stage3 = EchoFilter.filter(stage2, existing_theorems=self.existing_theorems)
        return stage3
