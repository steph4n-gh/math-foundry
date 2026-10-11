"""Conjecture Generation Engine for Extremal Combinatorics and Graph Theory.

Provides recursive AST enumeration, parametric 2D convex hull extremal bound discovery,
and an archetypal conjecture library (Brooks, Turan, Ramsey, spectral, and C5 refutation benchmark).
"""

from __future__ import annotations

import math
from typing import Any, Dict, Iterator, List, Optional, Sequence, Set, Tuple, Union
import networkx as nx
import numpy as np
from scipy.spatial import ConvexHull
from scipy.spatial._qhull import QhullError

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    ExpressionNode,
    GuardPredicate,
    InvariantNode,
    UnaryOpNode,
)
from autonomous_math.core.graph_types import GraphInstance
from autonomous_math.core.invariants import GraphInvariantEvaluator
from autonomous_math.conjecturing.grammar import (
    ExpressionGenerator,
    GrammarConfig,
)


def _snap_rational(val: float, eps: float = 0.05) -> float:
    """Snaps a float to nearest integer or common fraction minimizing error within tolerance."""
    if math.isnan(val) or math.isinf(val):
        return val
    r = round(val)
    err_int = abs(val - r)
    if err_int < 1e-9:
        return float(r)

    best_candidate = val
    best_err = err_int if err_int < eps else float("inf")

    # Search common fraction denominators
    for denom in [2, 3, 4, 5, 6, 8, 10]:
        num = round(val * denom)
        candidate = num / denom
        err = abs(val - candidate)
        if err < best_err - 1e-7:
            best_err = err
            best_candidate = candidate

    if best_err < eps:
        return float(best_candidate)
    return float(val)


def _build_linear_rhs(
    var_names: Sequence[str],
    slopes: Sequence[float],
    intercept: float,
) -> ExpressionNode:
    """Constructs a canonical AST ExpressionNode for a linear combination sum(c_i * x_i) + c_0."""
    pos_terms: List[Tuple[str, float, ExpressionNode]] = []
    neg_terms: List[Tuple[str, float, ExpressionNode]] = []

    for var_name, slope in zip(var_names, slopes):
        if abs(slope) < 1e-9:
            continue
        v_node = InvariantNode(name=var_name)
        abs_slope = abs(slope)
        if abs(abs_slope - 1.0) < 1e-9:
            coeff_node: ExpressionNode = v_node
        else:
            coeff_node = BinaryOpNode("*", ConstantNode(value=abs_slope), v_node)

        if slope > 0:
            pos_terms.append((var_name, abs_slope, coeff_node))
        else:
            neg_terms.append((var_name, abs_slope, coeff_node))

    if not pos_terms and not neg_terms:
        return ConstantNode(value=intercept)

    if pos_terms:
        expr: ExpressionNode = pos_terms[0][2]
        for _, _, term_node in pos_terms[1:]:
            expr = BinaryOpNode("+", expr, term_node)
        for _, _, term_node in neg_terms:
            expr = BinaryOpNode("-", expr, term_node)
    else:
        first_var, first_abs, _ = neg_terms[0]
        if abs(first_abs - 1.0) < 1e-9:
            expr = BinaryOpNode("*", ConstantNode(value=-1.0), InvariantNode(name=first_var))
        else:
            expr = BinaryOpNode("*", ConstantNode(value=-first_abs), InvariantNode(name=first_var))
        for _, _, term_node in neg_terms[1:]:
            expr = BinaryOpNode("-", expr, term_node)

    if abs(intercept) > 1e-9:
        if intercept > 0:
            expr = BinaryOpNode("+", expr, ConstantNode(value=intercept))
        else:
            expr = BinaryOpNode("-", expr, ConstantNode(value=abs(intercept)))

    return expr


def _default_sample_graphs() -> List[nx.Graph]:
    """Generates a small representative atlas of extremal graphs."""
    graphs: List[nx.Graph] = [
        nx.cycle_graph(3),
        nx.cycle_graph(4),
        nx.cycle_graph(5),
        nx.cycle_graph(7),
        nx.path_graph(3),
        nx.path_graph(4),
        nx.complete_graph(1),
        nx.complete_graph(2),
        nx.complete_graph(3),
        nx.complete_graph(4),
        nx.complete_graph(5),
        nx.star_graph(3),
        nx.star_graph(4),
        nx.star_graph(5),
        nx.petersen_graph(),
        nx.complete_bipartite_graph(2, 3),
        nx.complete_bipartite_graph(3, 3),
    ]
    return graphs


class ConjectureGenerator:
    """Multi-strategy candidate conjecture generation engine."""

    def __init__(self, config: Optional[GrammarConfig] = None) -> None:
        self.config = config or GrammarConfig()
        self.expr_gen = ExpressionGenerator(self.config)

    def generate_exhaustive(
        self,
        max_depth: int = 2,
        limit: int = 10,
        relations: Optional[List[str]] = None,
        target_invariants: Optional[List[str]] = None,
    ) -> List[Conjecture]:
        """Exhaustively enumerates candidate conjectures pairing invariants with generated expressions."""
        targets = target_invariants or ["chromatic_number", "independence_number", "clique_number", "order"]
        rels = relations or ["<=", ">="]
        rhs_exprs = self.expr_gen.generate(max_depth=max_depth)

        conjectures: List[Conjecture] = []
        idx = 0

        for tgt in targets:
            lhs = InvariantNode(name=tgt)
            for rhs in rhs_exprs:
                if rhs.canonical_key == lhs.canonical_key:
                    continue
                for rel in rels:
                    idx += 1
                    conj_id = f"conj_ex_{tgt}_{rel}_{idx}"
                    conj = Conjecture.create(
                        id=conj_id,
                        lhs=lhs,
                        rel=rel,
                        rhs=rhs,
                    )
                    conjectures.append(conj)
                    if len(conjectures) >= limit:
                        return conjectures

        return conjectures

    def generate_recursive(
        self,
        target_invariant: str = "chromatic_number",
        relations: Optional[List[str]] = None,
        max_depth: int = 2,
        guards: Optional[List[GuardPredicate]] = None,
        limit: Optional[int] = None,
    ) -> List[Conjecture]:
        """Recursively generates candidate bounds for a specific target invariant."""
        lhs = InvariantNode(name=target_invariant)
        rels = relations or self.config.relations
        rhs_exprs = self.expr_gen.generate(max_depth=max_depth)
        guard_list = guards or [GuardPredicate(predicate_type="universal")]

        conjectures: List[Conjecture] = []
        idx = 0

        for rhs in rhs_exprs:
            if rhs.canonical_key == lhs.canonical_key:
                continue
            for rel in rels:
                for g in guard_list:
                    idx += 1
                    conj_id = f"conj_rec_{target_invariant}_{rel}_{idx}"
                    conj = Conjecture.create(
                        id=conj_id,
                        lhs=lhs,
                        rel=rel,
                        rhs=rhs,
                        guard=g,
                    )
                    conjectures.append(conj)
                    if limit is not None and len(conjectures) >= limit:
                        return conjectures

        return conjectures

    def generate_parametric_bounds(
        self,
        target_y: str = "chromatic_number",
        target_x: str = "max_degree",
        graphs: Optional[Sequence[nx.Graph]] = None,
        relations: Optional[List[str]] = None,
    ) -> List[Conjecture]:
        """Discovers linear extremal inequalities y <= a*x + b via 2D convex hull."""
        sample_graphs = list(graphs) if graphs is not None else _default_sample_graphs()
        rels = relations or ["<="]

        # Extract (x, y) coordinates
        pts_list: List[Tuple[float, float]] = []
        for G in sample_graphs:
            try:
                x_val = float(GraphInvariantEvaluator.evaluate_single(G, target_x))
                y_val = float(GraphInvariantEvaluator.evaluate_single(G, target_y))
                if math.isnan(x_val) or math.isnan(y_val) or math.isinf(x_val) or math.isinf(y_val):
                    continue
                pts_list.append((x_val, y_val))
            except Exception:
                continue

        if len(pts_list) < 2:
            return []

        # Remove duplicates and sort by x then y
        pts = sorted(set(pts_list))

        # Compute 2D Upper Convex Hull via Andrew's Monotone Chain
        upper_hull: List[Tuple[float, float]] = []
        for p in pts:
            while len(upper_hull) >= 2:
                p1, p2 = upper_hull[-2], upper_hull[-1]
                # Cross product: (p2.x - p1.x)*(p.y - p1.y) - (p2.y - p1.y)*(p.x - p1.x)
                cross = (p2[0] - p1[0]) * (p[1] - p1[1]) - (p2[1] - p1[1]) * (p[0] - p1[0])
                if cross >= 0:
                    upper_hull.pop()
                else:
                    break
            upper_hull.append(p)

        conjectures: List[Conjecture] = []
        seen_pairs: Set[Tuple[float, float]] = set()

        if "<=" in rels and len(upper_hull) >= 2:
            for i in range(len(upper_hull) - 1):
                p1 = upper_hull[i]
                p2 = upper_hull[i + 1]
                dx = p2[0] - p1[0]
                dy = p2[1] - p1[1]
                if abs(dx) < 1e-12 or math.isnan(dx) or math.isnan(dy):
                    continue
                slope = _snap_rational(dy / dx)
                if math.isnan(slope) or math.isinf(slope):
                    continue
                intercept = _snap_rational(p1[1] - slope * p1[0])
                if math.isnan(intercept) or math.isinf(intercept):
                    continue

                if (slope, intercept) in seen_pairs:
                    continue
                seen_pairs.add((slope, intercept))

                # Synthesize RHS: slope * x + intercept
                lhs = InvariantNode(name=target_y)
                var_x = InvariantNode(name=target_x)

                if abs(slope - 1.0) < 1e-9:
                    mult_node: ExpressionNode = var_x
                else:
                    mult_node = BinaryOpNode("*", ConstantNode(value=slope), var_x)

                if abs(intercept) < 1e-9:
                    rhs: ExpressionNode = mult_node
                elif intercept > 0:
                    rhs = BinaryOpNode("+", mult_node, ConstantNode(value=intercept))
                else:
                    rhs = BinaryOpNode("-", mult_node, ConstantNode(value=abs(intercept)))

                conj_id = f"hull_{target_y}_le_{slope:g}_{target_x}_{intercept:g}"
                conjectures.append(
                    Conjecture.create(
                        id=conj_id,
                        lhs=lhs,
                        rel="<=",
                        rhs=rhs,
                        metadata={"source": "parametric_convex_hull", "slope": slope, "intercept": intercept},
                    )
                )

        return conjectures

    def generate_multivariate_bounds(
        self,
        target_y: str,
        target_xs: Sequence[str],
        graphs: Optional[Sequence[nx.Graph]] = None,
        relations: Optional[List[str]] = None,
        guard: Optional[Union[GuardPredicate, str]] = None,
        snap_eps: float = 0.05,
        max_bounds: Optional[int] = None,
    ) -> List[Conjecture]:
        """Discovers multi-invariant extremal inequalities y <= sum(c_i * x_i) + c_0

        and lower bounds y >= sum(c_i * x_i) + c_0 via higher-dimensional convex hulls.
        Supports 3D triads (target_y vs [x1, x2]) and general N-D combinations,
        conditioned optionally on structural predicates (e.g. is_triangle_free, is_regular, is_bipartite).
        """
        # 1. Normalize Guard Predicate
        guard_obj: Optional[GuardPredicate] = None
        if guard is not None:
            if isinstance(guard, GuardPredicate):
                guard_obj = guard if guard.predicate_type != "universal" else None
            elif isinstance(guard, str) and guard != "universal":
                if guard in {"is_triangle_free", "is_bipartite", "is_regular", "is_connected", "is_tree", "is_planar"} or guard.startswith("is_"):
                    guard_obj = GuardPredicate(property_name_or_type=guard)
                else:
                    try:
                        guard_obj = GuardPredicate.from_dict(guard)
                    except Exception:
                        guard_obj = GuardPredicate(property_name_or_type=guard)

        # 2. 2D Fallback if single independent variable provided
        if len(target_xs) == 1:
            base_bounds = self.generate_parametric_bounds(
                target_y=target_y,
                target_x=target_xs[0],
                graphs=graphs,
                relations=relations,
            )
            if guard_obj is not None:
                updated: List[Conjecture] = []
                for b in base_bounds:
                    g_tag = f"_{guard_obj.property_name}" if guard_obj.property_name else ""
                    updated.append(
                        Conjecture.create(
                            id=f"{b.id}{g_tag}",
                            lhs=b.lhs_expr,
                            rel=b.rel,
                            rhs=b.rhs_expr,
                            guard=guard_obj,
                            metadata=b.metadata,
                        )
                    )
                return updated[:max_bounds] if max_bounds else updated
            return base_bounds[:max_bounds] if max_bounds else base_bounds

        # 3. Extract Multivariate Coordinates (from fast instance DB table or graph instances)
        pts_list: List[List[float]] = []
        rels = relations or ["<=", ">="]

        if graphs is None:
            try:
                from autonomous_math.sieve.instance_db import InstanceDatabase
                db = InstanceDatabase()
                table = db.get_invariants_table()
                all_invs = [target_y] + list(target_xs)
                if all(inv in table for inv in all_invs):
                    N = len(table[target_y])
                    mask = np.ones(N, dtype=bool)
                    if guard_obj is not None:
                        if guard_obj.predicate_type == "property" and guard_obj.property_name in table:
                            mask = table[guard_obj.property_name]
                            if guard_obj.negated:
                                mask = ~mask
                        elif guard_obj.predicate_type == "comparison" and guard_obj.invariant in table:
                            col = table[guard_obj.invariant]
                            thresh = float(guard_obj.threshold or 0.0)
                            op = guard_obj.op
                            if op == "<=":
                                mask = col <= thresh + 1e-7
                            elif op == ">=":
                                mask = col >= thresh - 1e-7
                            elif op == "==":
                                mask = np.abs(col - thresh) <= 1e-7
                            elif op == "<":
                                mask = col < thresh - 1e-7
                            elif op == ">":
                                mask = col > thresh + 1e-7
                        else:
                            insts = db.get_instances()
                            mask = np.array([guard_obj.evaluate(g) for g in insts], dtype=bool)

                    if np.any(mask):
                        x_cols = [table[x_inv][mask] for x_inv in target_xs]
                        y_col = table[target_y][mask]
                        pts_arr = np.column_stack(x_cols + [y_col])
                        pts_list = pts_arr.tolist()
            except Exception:
                pts_list = []

        if not pts_list:
            sample_graphs = list(graphs) if graphs is not None else _default_sample_graphs()
            for G in sample_graphs:
                if guard_obj is not None and not guard_obj.evaluate(G):
                    continue
                try:
                    row: List[float] = []
                    for x_inv in target_xs:
                        row.append(float(GraphInvariantEvaluator.evaluate_single(G, x_inv)))
                    row.append(float(GraphInvariantEvaluator.evaluate_single(G, target_y)))
                    pts_list.append(row)
                except Exception:
                    continue

        if len(pts_list) < 2:
            return []

        pts = np.array(pts_list, dtype=float)
        # Filter NaNs / Infs
        valid_rows = ~np.isnan(pts).any(axis=1) & ~np.isinf(pts).any(axis=1)
        pts = pts[valid_rows]
        if len(pts) < 2:
            return []

        pts = np.unique(pts, axis=0)
        D = pts.shape[1]

        # 4. Compute Facets via SciPy ConvexHull with SVD Affine Rank Protection
        equations: List[np.ndarray] = []
        centroid = np.mean(pts, axis=0)
        shifted = pts - centroid
        u, s, vt = np.linalg.svd(shifted, full_matrices=False)
        affine_rank = int(np.sum(s > 1e-4))

        if affine_rank <= 0:
            return []
        elif affine_rank == 1:
            # Collinear points in R^D (e.g. path graphs where size = order - 1)
            v1 = vt[0]
            v1_x = v1[:-1]
            v1_y = v1[-1]
            best_j = int(np.argmax(np.abs(v1_x)))
            if abs(v1_x[best_j]) > 1e-5:
                slope = v1_y / v1_x[best_j]
                intercept = centroid[-1] - slope * centroid[best_j]
                a_up = np.zeros(D - 1)
                a_up[best_j] = -slope
                eq_up = np.append(a_up, [1.0, -intercept])
                eq_low = -eq_up
                equations.extend([eq_up, eq_low])
        elif affine_rank < D:
            # Points lie on an affine hyperplane of dimension < D (e.g. coplanar in 3D)
            v_norm = vt[-1]
            c = v_norm[-1]
            if abs(c) > 1e-5:
                d = -float(np.dot(v_norm, centroid))
                eq_up = np.append(v_norm[:-1], [c, d]) if c > 0 else np.append(-v_norm[:-1], [-c, -d])
                eq_low = -eq_up
                equations.extend([eq_up, eq_low])
            else:
                # Predictors themselves are collinear/coplanar (e.g. x1 == x2 on regular graphs)
                try:
                    A = np.column_stack([pts[:, :-1], np.ones(len(pts))])
                    y_vec = pts[:, -1]
                    coefs, residuals, rank, _ = np.linalg.lstsq(A, y_vec, rcond=None)
                    err = float(np.abs(A @ coefs - y_vec).max())
                    if err < 1e-4:
                        eq_upper = np.append(-coefs[:-1], [1.0, -coefs[-1]])
                        eq_lower = np.append(coefs[:-1], [-1.0, coefs[-1]])
                        equations.append(eq_upper)
                        equations.append(eq_lower)
                except Exception:
                    pass
        else:
            # Full affine dimension: compute true convex hull facets
            if len(pts) >= D + 1:
                try:
                    hull = ConvexHull(pts)
                    equations.extend(hull.equations)
                except Exception:
                    try:
                        hull = ConvexHull(pts, qhull_options="QJ")
                        equations.extend(hull.equations)
                    except Exception:
                        pass

        if not equations:
            return []

        conjectures: List[Conjecture] = []
        seen: Set[Tuple[str, Tuple[float, ...], float]] = set()

        for eq in equations:
            a = eq[:-2]
            c = eq[-2]
            d = eq[-1]
            if abs(c) < 1e-6 or math.isnan(c) or math.isinf(c):
                continue

            rel = "<=" if c > 0 else ">="
            if rel not in rels:
                continue

            raw_slopes = [-ai / c for ai in a]
            raw_intercept = -d / c

            slopes = [_snap_rational(s, eps=snap_eps) for s in raw_slopes]
            intercept = _snap_rational(raw_intercept, eps=snap_eps)

            # Sanity bound filtering
            if any(math.isnan(s) or math.isinf(s) or abs(s) > 25.0 for s in slopes):
                continue
            if math.isnan(intercept) or math.isinf(intercept) or abs(intercept) > 100.0:
                continue

            # Ensure strict dataset validity after rational snapping
            x_mat = pts[:, :-1]
            y_actual = pts[:, -1]
            pred_y = x_mat @ np.array(slopes)

            if rel == "<=":
                diff = float(np.max(y_actual - pred_y))
                if intercept < diff - 1e-6:
                    candidate = _snap_rational(diff, eps=snap_eps)
                    if candidate >= diff - 1e-6:
                        intercept = candidate
                    else:
                        intercept = math.ceil(diff * 100.0) / 100.0
            else:
                diff = float(np.min(y_actual - pred_y))
                if intercept > diff + 1e-6:
                    candidate = _snap_rational(diff, eps=snap_eps)
                    if candidate <= diff + 1e-6:
                        intercept = candidate
                    else:
                        intercept = math.floor(diff * 100.0) / 100.0

            # Filter trivial all-zero slope bounds
            if all(abs(s) < 1e-9 for s in slopes):
                continue

            # Filter net-negative slopes on upper bounds (finite dataset boundary cut)
            if rel == "<=" and sum(slopes) < -1e-6:
                continue

            sig = (rel, tuple(round(s, 3) for s in slopes), round(intercept, 3))
            if sig in seen:
                continue
            seen.add(sig)

            rhs = _build_linear_rhs(target_xs, slopes, intercept)
            lhs = InvariantNode(name=target_y)

            # Generate unique identifier
            rel_name = "le" if rel == "<=" else "ge"
            slopes_str = "_".join(f"{s:g}" for s in slopes)
            vars_str = "_".join(target_xs)
            guard_str = f"_{guard_obj.property_name}" if guard_obj and guard_obj.property_name else ""
            conj_id = f"hull3d_{target_y}_{rel_name}_{slopes_str}_{vars_str}_{intercept:g}{guard_str}"

            metadata = {
                "source": "multivariate_convex_hull",
                "dimension": D,
                "target_y": target_y,
                "target_xs": list(target_xs),
                "slopes": slopes,
                "intercept": intercept,
            }

            conj = Conjecture.create(
                id=conj_id,
                lhs=lhs,
                rel=rel,
                rhs=rhs,
                guard=guard_obj,
                metadata=metadata,
            )
            conjectures.append(conj)
            if max_bounds is not None and len(conjectures) >= max_bounds:
                break

        # Sort so cleaner/simpler bounds appear first
        conjectures.sort(key=lambda c: (
            0 if c.rel == "<=" and all(s >= -1e-6 for s in c.metadata.get("slopes", [])) else 1,
            c.complexity,
        ))

        return conjectures[:max_bounds] if max_bounds is not None else conjectures

    def generate_nonlinear_bounds(
        self,
        target_y: str = "estrada_index",
        target_x: str = "size",
        envelope_type: str = "sqrt",
        graphs: Optional[Sequence[nx.Graph]] = None,
        relations: Optional[List[str]] = None,
    ) -> List[Conjecture]:
        """Discovers non-linear extremal inequalities (sqrt, quad, exp) via convex hull on transformed coordinates."""
        sample_graphs = list(graphs) if graphs is not None else _default_sample_graphs()
        rels = relations or ["<="]

        pts_list: List[Tuple[float, float]] = []
        for G in sample_graphs:
            try:
                x_raw = float(GraphInvariantEvaluator.evaluate_single(G, target_x))
                y_val = float(GraphInvariantEvaluator.evaluate_single(G, target_y))
                if math.isnan(x_raw) or math.isnan(y_val) or math.isinf(x_raw) or math.isinf(y_val):
                    continue
                if envelope_type == "sqrt":
                    if x_raw < 0:
                        continue
                    x_trans = math.sqrt(x_raw)
                elif envelope_type == "quad":
                    x_trans = x_raw * x_raw
                elif envelope_type == "exp":
                    x_trans = math.exp(min(20.0, x_raw))
                else:
                    x_trans = x_raw
                pts_list.append((x_trans, y_val))
            except Exception:
                continue

        if len(pts_list) < 2:
            return []

        pts = sorted(set(pts_list))
        upper_hull: List[Tuple[float, float]] = []
        for p in pts:
            while len(upper_hull) >= 2:
                p1, p2 = upper_hull[-2], upper_hull[-1]
                cross = (p2[0] - p1[0]) * (p[1] - p1[1]) - (p2[1] - p1[1]) * (p[0] - p1[0])
                if cross >= 0:
                    upper_hull.pop()
                else:
                    break
            upper_hull.append(p)

        conjectures: List[Conjecture] = []
        seen_pairs: Set[Tuple[float, float]] = set()

        if "<=" in rels and len(upper_hull) >= 2:
            for i in range(len(upper_hull) - 1):
                p1 = upper_hull[i]
                p2 = upper_hull[i + 1]
                dx = p2[0] - p1[0]
                dy = p2[1] - p1[1]
                if abs(dx) < 1e-12 or math.isnan(dx) or math.isnan(dy):
                    continue
                slope = _snap_rational(dy / dx)
                if math.isnan(slope) or math.isinf(slope) or slope <= 0:
                    continue
                intercept = _snap_rational(p1[1] - slope * p1[0])
                if math.isnan(intercept) or math.isinf(intercept):
                    continue

                if (slope, intercept) in seen_pairs:
                    continue
                seen_pairs.add((slope, intercept))

                lhs = InvariantNode(name=target_y)
                var_x: ExpressionNode = InvariantNode(name=target_x)
                if envelope_type == "sqrt":
                    trans_node: ExpressionNode = UnaryOpNode(op="sqrt", child=var_x)
                elif envelope_type == "quad":
                    trans_node = UnaryOpNode(op="sqr", child=var_x)
                elif envelope_type == "exp":
                    trans_node = UnaryOpNode(op="exp", child=var_x)
                else:
                    trans_node = var_x

                if abs(slope - 1.0) < 1e-9:
                    mult_node: ExpressionNode = trans_node
                else:
                    mult_node = BinaryOpNode("*", ConstantNode(value=slope), trans_node)

                if abs(intercept) < 1e-9:
                    rhs: ExpressionNode = mult_node
                elif intercept > 0:
                    rhs = BinaryOpNode("+", mult_node, ConstantNode(value=intercept))
                else:
                    rhs = BinaryOpNode("-", mult_node, ConstantNode(value=abs(intercept)))

                conj_id = f"hull_{target_y}_le_{slope:g}_{envelope_type}_{target_x}_{intercept:g}"
                conjectures.append(
                    Conjecture.create(
                        id=conj_id,
                        lhs=lhs,
                        rel="<=",
                        rhs=rhs,
                        metadata={
                            "source": "nonlinear_convex_hull",
                            "envelope_type": envelope_type,
                            "slope": slope,
                            "intercept": intercept,
                        },
                    )
                )

        return conjectures

    def generate_advanced_spectral_candidates(self) -> List[Conjecture]:
        """Synthesizes candidate bounds in higher-order and non-linear spectral graph theory.

        Targets:
        - Signless Laplacian Q-spectral radius (q_1)
        - Normalized Laplacian spectral gap (lambda_2^L)
        - Estrada index (EE)
        - Graph Energy (E(G))
        - Nordhaus-Gaddum eigenvalue inequalities
        """
        conjs: List[Conjecture] = []

        # 1. Signless Laplacian Q-Spectral Radius Bounds
        conjs.append(
            Conjecture.create(
                id="cvetkovic_signless_laplacian_max_deg",
                lhs=InvariantNode(name="signless_laplacian_spectral_radius"),
                rel="<=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="max_degree")),
                statement="q_1(G) <= 2 * max_degree(G)",
                metadata={"family": "Signless-Laplacian", "target": "q_1", "theorem": "Cvetkovic-2007"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="signless_laplacian_avg_deg_lower",
                lhs=InvariantNode(name="signless_laplacian_spectral_radius"),
                rel=">=",
                rhs=InvariantNode(name="average_degree"),
                statement="q_1(G) >= average_degree(G)",
                metadata={"family": "Signless-Laplacian", "target": "q_1", "theorem": "Rayleigh-Quotient"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="das_signless_laplacian_order_size",
                lhs=InvariantNode(name="signless_laplacian_spectral_radius"),
                rel="<=",
                rhs=BinaryOpNode(
                    "+",
                    BinaryOpNode(
                        "/",
                        BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="size")),
                        BinaryOpNode("-", InvariantNode(name="order"), ConstantNode(value=1.0)),
                    ),
                    BinaryOpNode("-", InvariantNode(name="order"), ConstantNode(value=2.0)),
                ),
                guard=GuardPredicate(predicate_type="comparison", invariant="order", op=">=", threshold=2.0),
                statement="order >= 2 ==> q_1(G) <= (2*m)/(n - 1) + n - 2",
                metadata={"family": "Signless-Laplacian", "target": "q_1", "theorem": "Das-2004"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="signless_laplacian_spectral_plus_max_deg",
                lhs=InvariantNode(name="signless_laplacian_spectral_radius"),
                rel="<=",
                rhs=BinaryOpNode("+", InvariantNode(name="spectral_radius"), InvariantNode(name="max_degree")),
                statement="q_1(G) <= spectral_radius(G) + max_degree(G)",
                metadata={"family": "Signless-Laplacian", "target": "q_1", "type": "spectral_envelope"},
            )
        )

        # 2. Normalized Laplacian Spectral Gap Bounds
        conjs.append(
            Conjecture.create(
                id="chung_normalized_laplacian_gap_upper",
                lhs=InvariantNode(name="normalized_laplacian_spectral_gap"),
                rel="<=",
                rhs=BinaryOpNode(
                    "/",
                    InvariantNode(name="order"),
                    BinaryOpNode("-", InvariantNode(name="order"), ConstantNode(value=1.0)),
                ),
                guard=GuardPredicate(predicate_type="comparison", invariant="order", op=">=", threshold=2.0),
                statement="order >= 2 ==> normalized_laplacian_spectral_gap <= order / (order - 1)",
                metadata={"family": "Normalized-Laplacian", "target": "lambda_2_norm", "theorem": "Chung-1997"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="normalized_laplacian_gap_bipartite",
                lhs=InvariantNode(name="normalized_laplacian_spectral_gap"),
                rel="<=",
                rhs=ConstantNode(value=1.0),
                guard=GuardPredicate(property_name_or_type="is_bipartite"),
                statement="is_bipartite ==> normalized_laplacian_spectral_gap <= 1.0",
                metadata={"family": "Normalized-Laplacian", "target": "lambda_2_norm", "type": "bipartite_gap"},
            )
        )

        # 3. Estrada Index Non-Linear Envelopes
        conjs.append(
            Conjecture.create(
                id="estrada_index_exp_upper_bound",
                lhs=InvariantNode(name="estrada_index"),
                rel="<=",
                rhs=BinaryOpNode(
                    "+",
                    BinaryOpNode("-", InvariantNode(name="order"), ConstantNode(value=1.0)),
                    UnaryOpNode(op="exp", child=InvariantNode(name="spectral_radius")),
                ),
                statement="estrada_index <= (order - 1) + exp(spectral_radius)",
                metadata={"family": "Estrada-Index", "target": "estrada_index", "theorem": "Estrada-2000"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="estrada_index_quadratic_lower_bound",
                lhs=InvariantNode(name="estrada_index"),
                rel=">=",
                rhs=BinaryOpNode(
                    "+",
                    InvariantNode(name="order"),
                    BinaryOpNode(
                        "/",
                        UnaryOpNode(op="sqr", child=InvariantNode(name="spectral_radius")),
                        ConstantNode(value=2.0),
                    ),
                ),
                statement="estrada_index >= order + (spectral_radius^2)/2",
                metadata={"family": "Estrada-Index", "target": "estrada_index", "type": "taylor_lower_bound"},
            )
        )

        # 4. Graph Energy Invariants
        conjs.append(
            Conjecture.create(
                id="mcclelland_graph_energy_upper",
                lhs=InvariantNode(name="graph_energy"),
                rel="<=",
                rhs=UnaryOpNode(
                    op="sqrt",
                    child=BinaryOpNode(
                        "*",
                        ConstantNode(value=2.0),
                        BinaryOpNode("*", InvariantNode(name="size"), InvariantNode(name="order")),
                    ),
                ),
                statement="graph_energy <= sqrt(2 * size * order)",
                metadata={"family": "Graph-Energy", "target": "graph_energy", "theorem": "McClelland-1971"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="graph_energy_spectral_radius_lower",
                lhs=InvariantNode(name="graph_energy"),
                rel=">=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="spectral_radius")),
                statement="graph_energy >= 2 * spectral_radius",
                metadata={"family": "Graph-Energy", "target": "graph_energy", "type": "spectral_lower_bound"},
            )
        )

        # 5. Nordhaus-Gaddum Eigenvalue Bounds
        conjs.append(
            Conjecture.create(
                id="nordhaus_gaddum_spectral_sum_bound",
                lhs=InvariantNode(name="nordhaus_gaddum_spectral_sum"),
                rel="<=",
                rhs=BinaryOpNode(
                    "*",
                    ConstantNode(value=1.41421356),
                    BinaryOpNode("-", InvariantNode(name="order"), ConstantNode(value=1.0)),
                ),
                guard=GuardPredicate(predicate_type="comparison", invariant="order", op=">=", threshold=2.0),
                statement="order >= 2 ==> nordhaus_gaddum_spectral_sum <= 1.4142 * (order - 1)",
                metadata={"family": "Nordhaus-Gaddum", "target": "ng_spectral_sum", "theorem": "Nosal-Nikiforov"},
            )
        )

        return conjs

    def generate_metric_candidates(self) -> List[Conjecture]:
        """Synthesizes candidate bounds in metric and topological graph theory.

        Targets:
        - Diameter vs Radius: rad(G) <= diam(G), diam(G) <= 2*rad(G)
        - Diameter vs Order: diam(G) <= order(G) - 1
        - Moore bounds: order(G) <= Delta(G)^2 + 1
        - Spectral spread: s(G) <= 2 * lambda_1(G), s(G) <= order(G)
        """
        conjs: List[Conjecture] = []

        conjs.append(
            Conjecture.create(
                id="radius_le_diameter",
                lhs=InvariantNode(name="radius"),
                rel="<=",
                rhs=InvariantNode(name="diameter"),
                guard=GuardPredicate(property_name_or_type="is_connected"),
                statement="is_connected ==> radius <= diameter",
                metadata={"family": "Metric", "theorem": "Classical-Metric"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="diameter_le_two_radius",
                lhs=InvariantNode(name="diameter"),
                rel="<=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="radius")),
                guard=GuardPredicate(property_name_or_type="is_connected"),
                statement="is_connected ==> diameter <= 2 * radius",
                metadata={"family": "Metric", "theorem": "Classical-Metric"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="diameter_le_order",
                lhs=InvariantNode(name="diameter"),
                rel="<=",
                rhs=BinaryOpNode("-", InvariantNode(name="order"), ConstantNode(value=1.0)),
                guard=GuardPredicate(property_name_or_type="is_connected"),
                statement="is_connected ==> diameter <= order - 1",
                metadata={"family": "Metric", "theorem": "Classical-Metric"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="spectral_spread_le_two_spectral_radius",
                lhs=InvariantNode(name="spectral_spread"),
                rel="<=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="spectral_radius")),
                statement="spectral_spread <= 2 * spectral_radius",
                metadata={"family": "Spectral-Spread", "theorem": "Gregory-Hershkowitz-Hoffman-2001"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="spectral_spread_le_order",
                lhs=InvariantNode(name="spectral_spread"),
                rel="<=",
                rhs=InvariantNode(name="order"),
                statement="spectral_spread <= order",
                metadata={"family": "Spectral-Spread", "theorem": "Gregory-Hershkowitz-Hoffman-2001"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="moore_bound_diameter_2",
                lhs=InvariantNode(name="order"),
                rel="<=",
                rhs=BinaryOpNode(
                    "+",
                    BinaryOpNode("*", InvariantNode(name="max_degree"), InvariantNode(name="max_degree")),
                    ConstantNode(value=1.0),
                ),
                guard=GuardPredicate(predicate_type="comparison", invariant="diameter", op="<=", threshold=2.0),
                statement="diameter <= 2 ==> order <= max_degree * max_degree + 1",
                metadata={"family": "Metric", "theorem": "Moore-Bound-D2"},
            )
        )
        return conjs

    def generate_chemical_candidates(self) -> List[Conjecture]:
        """Synthesizes candidate bounds in chemical graph theory and graph energy.

        Targets:
        - Gutman bounds: E(G) <= 2*m, E(G) >= 2*lambda_1, E(G) >= 2*d_bar
        - Estrada vs Energy: EE(G) >= E(G)
        - Koolen-Moulton bounds: E(G) <= (n/2)(1 + sqrt(n)), E(G) <= 2m/n + sqrt((n-1)(2m - (2m/n)^2))
        - Spectral spread: s(G) <= 2*lambda_1, s(G) <= n, s(G) <= 2*Delta
        - McClelland bound: E(G) <= sqrt(2*m*n)
        """
        conjs: List[Conjecture] = []

        # 1. Gutman Bounds
        conjs.append(
            Conjecture.create(
                id="gutman_energy_size_bound",
                lhs=InvariantNode(name="graph_energy"),
                rel="<=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="size")),
                statement="graph_energy <= 2 * size",
                metadata={"family": "Chemical-Energy", "theorem": "Gutman-1978-Size"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="graph_energy_spectral_radius_lower",
                lhs=InvariantNode(name="graph_energy"),
                rel=">=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="spectral_radius")),
                statement="graph_energy >= 2 * spectral_radius",
                metadata={"family": "Chemical-Energy", "theorem": "Gutman-1978-Spectral"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="gutman_energy_avg_deg_lower",
                lhs=InvariantNode(name="graph_energy"),
                rel=">=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="average_degree")),
                statement="graph_energy >= 2 * average_degree",
                metadata={"family": "Chemical-Energy", "theorem": "Gutman-1978-AvgDeg"},
            )
        )

        # 2. Estrada vs Energy
        conjs.append(
            Conjecture.create(
                id="estrada_ge_energy",
                lhs=InvariantNode(name="estrada_index"),
                rel=">=",
                rhs=InvariantNode(name="graph_energy"),
                statement="estrada_index >= graph_energy",
                metadata={"family": "Chemical-Energy", "theorem": "Estrada-Gutman-2000"},
            )
        )

        # 3. Koolen-Moulton Bounds
        conjs.append(
            Conjecture.create(
                id="koolen_moulton_order_2003",
                lhs=InvariantNode(name="graph_energy"),
                rel="<=",
                rhs=BinaryOpNode(
                    "*",
                    BinaryOpNode("/", InvariantNode(name="order"), ConstantNode(value=2.0)),
                    BinaryOpNode("+", ConstantNode(value=1.0), UnaryOpNode(op="sqrt", child=InvariantNode(name="order"))),
                ),
                statement="graph_energy <= (order / 2) * (1 + sqrt(order))",
                metadata={"family": "Chemical-Energy", "theorem": "Koolen-Moulton-2003"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="koolen_moulton_energy_bound",
                lhs=InvariantNode(name="graph_energy"),
                rel="<=",
                rhs=BinaryOpNode(
                    "+",
                    BinaryOpNode(
                        "/",
                        BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="size")),
                        InvariantNode(name="order"),
                    ),
                    UnaryOpNode(
                        op="sqrt",
                        child=BinaryOpNode(
                            "*",
                            BinaryOpNode("-", InvariantNode(name="order"), ConstantNode(value=1.0)),
                            BinaryOpNode(
                                "-",
                                BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="size")),
                                BinaryOpNode(
                                    "/",
                                    BinaryOpNode(
                                        "*",
                                        ConstantNode(value=4.0),
                                        BinaryOpNode("*", InvariantNode(name="size"), InvariantNode(name="size")),
                                    ),
                                    BinaryOpNode("*", InvariantNode(name="order"), InvariantNode(name="order")),
                                ),
                            ),
                        ),
                    ),
                ),
                guard=GuardPredicate(predicate_type="comparison", invariant="order", op=">=", threshold=2.0),
                statement="order >= 2 ==> graph_energy <= (2*m)/n + sqrt((n-1)*(2*m - (2*m/n)^2))",
                metadata={"family": "Chemical-Energy", "theorem": "Koolen-Moulton-2001"},
            )
        )

        # 4. Spectral Spread Bounds
        conjs.append(
            Conjecture.create(
                id="spectral_spread_le_two_spectral_radius",
                lhs=InvariantNode(name="spectral_spread"),
                rel="<=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="spectral_radius")),
                statement="spectral_spread <= 2 * spectral_radius",
                metadata={"family": "Spectral-Spread", "theorem": "Gregory-Hershkowitz-Hoffman-2001"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="spectral_spread_le_order",
                lhs=InvariantNode(name="spectral_spread"),
                rel="<=",
                rhs=InvariantNode(name="order"),
                statement="spectral_spread <= order",
                metadata={"family": "Spectral-Spread", "theorem": "Gregory-Hershkowitz-Hoffman-2001"},
            )
        )
        conjs.append(
            Conjecture.create(
                id="spectral_spread_le_two_max_degree",
                lhs=InvariantNode(name="spectral_spread"),
                rel="<=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="max_degree")),
                statement="spectral_spread <= 2 * max_degree",
                metadata={"family": "Spectral-Spread", "theorem": "Gregory-Hershkowitz-Hoffman-2001"},
            )
        )

        # 5. McClelland Bound
        conjs.append(
            Conjecture.create(
                id="mcclelland_graph_energy_upper",
                lhs=InvariantNode(name="graph_energy"),
                rel="<=",
                rhs=UnaryOpNode(
                    op="sqrt",
                    child=BinaryOpNode(
                        "*",
                        ConstantNode(value=2.0),
                        BinaryOpNode("*", InvariantNode(name="size"), InvariantNode(name="order")),
                    ),
                ),
                statement="graph_energy <= sqrt(2 * size * order)",
                metadata={"family": "Chemical-Energy", "theorem": "McClelland-1971"},
            )
        )

        return conjs


    def generate_archetypal(self) -> List[Conjecture]:
        """Returns the canonical library of archetypal graph-theoretic conjectures.

        Includes Brooks, Turan, Ramsey, spectral bounds, and the mandatory C5-falsifiable claim.
        """
        conjectures: List[Conjecture] = []

        # 1. Brooks Archetype
        # Bound: chi <= Delta + 1 (Universally true)
        conjectures.append(
            Conjecture.create(
                id="archetype_brooks_standard",
                lhs=InvariantNode(name="chromatic_number"),
                rel="<=",
                rhs=BinaryOpNode("+", InvariantNode(name="max_degree"), ConstantNode(value=1.0)),
                statement="chromatic_number <= max_degree + 1",
                metadata={"archetype": "Brooks", "ground_truth": True},
            )
        )
        # Naive Brooks: chi <= Delta (False, refuted by odd cycles C5 and complete graphs)
        conjectures.append(
            Conjecture.create(
                id="archetype_brooks_naive",
                lhs=InvariantNode(name="chromatic_number"),
                rel="<=",
                rhs=InvariantNode(name="max_degree"),
                statement="chromatic_number <= max_degree",
                metadata={"archetype": "Brooks", "ground_truth": False},
            )
        )

        # 2. Turan / Mantel Archetype
        # Mantel: is_triangle_free ==> size <= (order * order) / 4 (Universally true)
        mantel_rhs = BinaryOpNode(
            "/",
            BinaryOpNode("*", InvariantNode(name="order"), InvariantNode(name="order")),
            ConstantNode(value=4.0),
        )
        conjectures.append(
            Conjecture.create(
                id="archetype_mantel_triangle_free",
                lhs=InvariantNode(name="size"),
                rel="<=",
                rhs=mantel_rhs,
                guard=GuardPredicate(property_name_or_type="is_triangle_free"),
                statement="is_triangle_free ==> size <= (order * order) / 4",
                metadata={"archetype": "Turan", "ground_truth": True},
            )
        )

        # 3. Ramsey Archetype
        # Order bound: chi >= order / independence_number (Universally true)
        conjectures.append(
            Conjecture.create(
                id="archetype_ramsey_chi_alpha",
                lhs=InvariantNode(name="chromatic_number"),
                rel=">=",
                rhs=BinaryOpNode("/", InvariantNode(name="order"), InvariantNode(name="independence_number")),
                guard=GuardPredicate(predicate_type="comparison", invariant="order", op=">=", threshold=1.0),
                statement="order >= 1 ==> chromatic_number >= order / independence_number",
                metadata={"archetype": "Ramsey", "ground_truth": True},
            )
        )
        # False product bound: alpha * omega >= order (False, refuted by C5: 2 * 2 = 4 < 5)
        conjectures.append(
            Conjecture.create(
                id="archetype_ramsey_product_false",
                lhs=BinaryOpNode("*", InvariantNode(name="independence_number"), InvariantNode(name="clique_number")),
                rel=">=",
                rhs=InvariantNode(name="order"),
                statement="independence_number * clique_number >= order",
                metadata={"archetype": "Ramsey", "ground_truth": False},
            )
        )

        # 4. Spectral Bounds
        # Wilf bound: chi <= spectral_radius + 1 (Universally true)
        conjectures.append(
            Conjecture.create(
                id="archetype_spectral_wilf",
                lhs=InvariantNode(name="chromatic_number"),
                rel="<=",
                rhs=BinaryOpNode("+", InvariantNode(name="spectral_radius"), ConstantNode(value=1.0)),
                statement="chromatic_number <= spectral_radius + 1",
                metadata={"archetype": "Spectral", "ground_truth": True},
            )
        )
        # Clique lower bound: chi >= omega (Universally true)
        conjectures.append(
            Conjecture.create(
                id="archetype_chi_ge_omega",
                lhs=InvariantNode(name="chromatic_number"),
                rel=">=",
                rhs=InvariantNode(name="clique_number"),
                statement="chromatic_number >= clique_number",
                metadata={"archetype": "Basic", "ground_truth": True},
            )
        )

        # 5. Mandatory C5 Falsification Benchmark Target (Requirements R1, R2, Acceptance Criteria)
        # Claim: is_triangle_free(G) ==> chi(G) <= 2
        # (False; refuted on C5 which is triangle-free with chi=3)
        conjectures.append(
            Conjecture.create(
                id="benchmark_triangle_free_chromatic_at_most_2",
                lhs=InvariantNode(name="chromatic_number"),
                rel="<=",
                rhs=ConstantNode(value=2.0),
                guard=GuardPredicate(property_name_or_type="is_triangle_free"),
                statement="is_triangle_free ==> chromatic_number <= 2",
                metadata={"benchmark": "C5_refutation", "ground_truth": False},
            )
        )

        return conjectures
