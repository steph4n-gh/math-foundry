"""Conservative AST translation using genuine Mathlib finite graph definitions.

Unsupported invariants and partial operations are reported explicitly, never axiomatized.
"""
from fractions import Fraction
import re
from autonomous_math.core.ast import BinaryOpNode, ConstantNode, Conjecture, GuardPredicate, InvariantNode, UnaryOpNode
from autonomous_math.core.invariants import INVARIANT_ALIASES


_BASE_IMPORTS = (
    "Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex",
    "Mathlib.Combinatorics.SimpleGraph.DegreeSum",
    "Mathlib.Tactic",
)
_ADJ_EIGENVALUES = "(G.isHermitian_adjMatrix ℝ).eigenvalues"
_LAP_EIGENVALUES = "(G.isHermitian_lapMatrix ℝ).eigenvalues"
_SIGNLESS_EIGENVALUES = "((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues"
_NORMALIZED_HERMITIAN = "(Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ))"
_NORMALIZED_PREFIX = "let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); "


def _extremum(eigenvalues, kind="sSup"):
    # Real.sSup_empty and Real.sInf_empty are both zero. Keep the explicit branch
    # to make the evaluator's empty-graph convention visible in the statement.
    return f"(if Fintype.card V = 0 then (0 : ℝ) else {kind} (Set.range {eigenvalues}))"


def _second_smallest(hermitian):
    # Mathlib eigenvalues₀ are sorted descending, with multiplicity. A descending
    # vector's second-smallest entry is card V - 2. The branch supplies the bound.
    return ("(letI : Decidable G.Connected := Classical.propDecidable _; "
            f"if G.Connected then (if h : 2 ≤ Fintype.card V then {hermitian}.eigenvalues₀ "
            "⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))")


_RADIUS = _extremum(_ADJ_EIGENVALUES)
_MIN_EIGENVALUE = _extremum(_ADJ_EIGENVALUES, "sInf")
_DEFINITIONS = {
    "order": "(Fintype.card V : ℝ)",
    "size": "(G.edgeFinset.card : ℝ)",
    "chromatic_number": "(G.chromaticNumber.toNat : ℝ)",
    "clique_number": "(G.cliqueNum : ℝ)",
    "max_degree": "(G.maxDegree : ℝ)",
    "min_degree": "(G.minDegree : ℝ)",
    "average_degree": "(if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))",
    "density": "(if Fintype.card V < 2 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)))",
    "independence_number": "(Gᶜ.cliqueNum : ℝ)",
    "triangle_count": "((G.cliqueFinset 3).card : ℝ)",
    "spectral_radius": _RADIUS,
    "smallest_adjacency_eigenvalue": _MIN_EIGENVALUE,
    "spectral_spread": f"({_RADIUS} - {_MIN_EIGENVALUE})",
    "graph_energy": f"(∑ v : V, |{_ADJ_EIGENVALUES} v|)",
    "estrada_index": f"(∑ v : V, Real.exp ({_ADJ_EIGENVALUES} v))",
    "laplacian_spectral_radius": _extremum(_LAP_EIGENVALUES),
    "signless_laplacian_spectral_radius": _extremum(_SIGNLESS_EIGENVALUES),
    "normalized_laplacian_spectral_radius": f"({_NORMALIZED_PREFIX}{_extremum(_NORMALIZED_HERMITIAN + '.eigenvalues')})",
    "algebraic_connectivity": _second_smallest("(G.isHermitian_lapMatrix ℝ)"),
    "normalized_laplacian_spectral_gap": f"({_NORMALIZED_PREFIX}{_second_smallest(_NORMALIZED_HERMITIAN)})",
    "complement_spectral_radius": _extremum("(Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues"),
}
_DEFINITIONS.update({
    "nordhaus_gaddum_spectral_sum": f"({_RADIUS} + {_DEFINITIONS['complement_spectral_radius']})",
    "nordhaus_gaddum_spectral_product": f"({_RADIUS} * {_DEFINITIONS['complement_spectral_radius']})",
    "wilf_bound": f"(if Fintype.card V = 0 then (0 : ℝ) else (1 : ℝ) + {_RADIUS})",
    "hoffman_bound": (f"(if G.edgeFinset.card = 0 then (if Fintype.card V = 0 then (0 : ℝ) else 1) "
                      f"else if |{_MIN_EIGENVALUE}| < (1 / 1000000000000 : ℝ) then 1 "
                      f"else (1 : ℝ) - {_RADIUS} / {_MIN_EIGENVALUE})"),
})
_PARITY_WORDS = "((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0))"
_STOPPING_SETS = "((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w)))"
_CODE_INVARIANTS = {"parity_code_distance", "parity_code_dimension", "unique_neighbor_radius"}
_CODE_IMPORTS = {
    "Mathlib.Combinatorics.SimpleGraph.AdjMatrix",
    "Mathlib.Data.ZMod.Basic",
    "Mathlib.InformationTheory.Hamming",
    "Mathlib.LinearAlgebra.Matrix.ToLin",
    "Mathlib.LinearAlgebra.Dimension.Constructions",
}
_DEFINITIONS.update({
    "parity_code_distance": f"(let weights : Finset ℕ := {{Fintype.card V + 1}} ∪ {_PARITY_WORDS}.image hammingNorm; (weights.min' (by simp [weights]) : ℝ))",
    "parity_code_dimension": "(Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)",
    "unique_neighbor_radius": f"(let weights : Finset ℕ := {{Fintype.card V + 1}} ∪ {_STOPPING_SETS}.image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ))",
})
_SPECTRAL_INVARIANTS = set(_DEFINITIONS) - {
    "order", "size", "chromatic_number", "clique_number", "max_degree", "min_degree",
    "average_degree", "density", "independence_number", "triangle_count", *_CODE_INVARIANTS,
}
_INTEGER_INVARIANTS = {
    "order", "size", "chromatic_number", "clique_number", "max_degree", "min_degree",
    "independence_number", "triangle_count", *_CODE_INVARIANTS,
}
_NONNEGATIVE_INVARIANTS = _INTEGER_INVARIANTS | {"average_degree", "density", "graph_energy", "estrada_index"}
_PROPERTIES = {
    "is_connected": "G.Connected",
    "is_tree": "G.IsTree",
    "is_forest": "G.IsAcyclic",
    "is_bipartite": "G.Colorable 2",
    "is_triangle_free": "G.CliqueFree 3",
    "is_regular": "(∃ d : ℕ, G.IsRegularOfDegree d)",
    "is_empty": "G = ⊥",
    # Unlike Mathlib's top graph on an empty type, the numerical evaluator calls
    # the vertexless graph incomplete. Empty here means edge-free, not vertexless.
    "is_complete": "(Nonempty V ∧ G = ⊤)",
}
_GUARD_TOLERANCE = Fraction(1, 10000000)
_DIVISION_TOLERANCE = Fraction(1, 1000000000000)


class FormalizationError(ValueError):
    """An unsupported AST feature; callers can report its category without parsing text."""

    def __init__(self, category, feature, reason):
        self.category, self.feature, self.reason = category, feature, reason
        super().__init__(f"No trusted formalization for {category} {feature}: {reason}")


def capability_report():
    """The deterministic translator's actual scalar grammar, not proof-search promises."""
    return {
        "invariants": sorted(_DEFINITIONS),
        "properties": sorted(_PROPERTIES),
        "guard_types": ["universal", "property", "comparison", "conjunction"],
        "binary_operations": ["+", "-", "*", "/", "min", "max", "^"],
        "unary_operations": ["neg", "abs", "sqr", "sqrt", "inv", "floor", "ceil", "exp", "log1p"],
        "partial_operation_rules": {
            "division": "Denominator magnitude at least 1e-12 follows from constant arithmetic, nonnegative grammar, or explicit guard bounds; otherwise rejected.",
            "sqrt": "Input lower bound at least -1e-9 follows from grammar or guards; Real.sqrt agrees with the evaluator's clamp to zero.",
            "log1p": "Input lower bound strictly greater than -1 follows from grammar or guards.",
            "power": "Only constant nonnegative integer exponents are supported.",
        },
        "guard_comparisons": "Exact rational thresholds with the evaluator's 1e-7 tolerance; negated applies only to property guards, matching GuardPredicate.evaluate.",
        "spectral_semantics": "Native Hermitian matrix eigenvalues with multiplicity, sorted descending for second-smallest indices. Extrema and empty sums use zero. Exact PSD Laplacian spectra correspond to numerical clipping of roundoff.",
        "code_semantics": {
            "code": "Binary neighborhood parity code ker(A_G : F₂^V → F₂^V); variable and check nodes are separate copies of V.",
            "parity_code_distance": "Minimum Hamming weight of a nonzero kernel vector; n+1 for the zero code, including 1 at n=0.",
            "parity_code_dimension": "Dimension of the adjacency kernel over ZMod 2, equal to n minus its GF₂ rank.",
            "unique_neighbor_radius": "Smallest nonempty stopping-set size minus one; n when no stopping set exists. Equivalently every nonempty set of at most u variable nodes has a check with exactly one neighbor in it.",
            "numerical_scope": "Exact Python evaluation is bounded to graphs of order at most 16; larger cases are explicitly unsupported. Lean propositions quantify over all finite graphs.",
            "zero_code": "The zero code uses the explicit finite n+1 distance sentinel; check dimension before claiming a nontrivial code.",
        },
        "unsupported": {
            "diameter/radius/girth": "May be infinite; the current scalar proposition grammar is real-valued.",
            "is_planar/is_chordal": "No reviewed translation implemented.",
            "spectrum vectors": "The conjecture AST requires scalar invariants.",
            "floating_point_roundoff": "Lean statements concern exact mathematical invariants, not NumPy rounding or overflow.",
        },
    }


def _rational(value):
    try:
        result = Fraction(str(value))
    except (ValueError, ZeroDivisionError) as exc:
        raise FormalizationError("constant", value, "must be a finite rational number") from exc
    return result


def _real(value):
    value = _rational(value)
    if value.denominator == 1:
        return f"({value.numerator} : ℝ)"
    return f"({value.numerator} / {value.denominator} : ℝ)"


def _formal_invariant(name, imports):
    name = INVARIANT_ALIASES.get(name, name)
    if name not in _DEFINITIONS:
        raise FormalizationError("invariant", name, "not in the reviewed native Mathlib scalar definitions")
    if name in _SPECTRAL_INVARIANTS:
        imports.update(("Mathlib.Combinatorics.SimpleGraph.LapMatrix", "Mathlib.Analysis.Matrix.Spectrum", "Mathlib.Analysis.SpecialFunctions.Exp"))
    if name in _CODE_INVARIANTS:
        imports.update(_CODE_IMPORTS)
    return _DEFINITIONS[name]


def _render_guard(g, imports, bounds):
    if isinstance(g, str):
        g = GuardPredicate.from_dict(g)
    if g is None or g.predicate_type == "universal":
        return None
    if g.predicate_type == "property":
        name = g.property_name
        if name not in _PROPERTIES:
            raise FormalizationError("Guard", name, "property is not in the reviewed Mathlib graph predicates")
        if name in {"is_connected", "is_tree", "is_forest"}:
            imports.add("Mathlib.Combinatorics.SimpleGraph.Acyclic")
        if not g.negated and name in {"is_connected", "is_tree", "is_complete"}:
            bounds["order"] = (Fraction(1), None)
        p = _PROPERTIES[name]
        return f"(¬ ({p}))" if g.negated else f"({p})"
    if g.predicate_type == "comparison":
        name = INVARIANT_ALIASES.get(g.invariant or "order", g.invariant or "order")
        value, threshold = _formal_invariant(name, imports), _rational(g.threshold or 0)
        low, high = bounds.get(name, (Fraction(0) if name in _NONNEGATIVE_INVARIANTS else None, None))
        if g.op in {">=", ">", "=="}:
            new_low = threshold + _GUARD_TOLERANCE if g.op == ">" else threshold - _GUARD_TOLERANCE
            if name in _INTEGER_INVARIANTS:
                new_low = Fraction(-(-new_low.numerator // new_low.denominator))
            low = new_low if low is None else max(low, new_low)
        if g.op in {"<=", "<", "=="}:
            new_high = threshold - _GUARD_TOLERANCE if g.op == "<" else threshold + _GUARD_TOLERANCE
            if name in _INTEGER_INVARIANTS:
                new_high = Fraction(new_high.numerator // new_high.denominator)
            high = new_high if high is None else min(high, new_high)
        bounds[name] = low, high
        if g.op == "==":
            return f"(|{value} - {_real(threshold)}| ≤ {_real(_GUARD_TOLERANCE)})"
        shifts = {"<=": ("≤", threshold + _GUARD_TOLERANCE), ">=": ("≥", threshold - _GUARD_TOLERANCE),
                  "<": ("<", threshold - _GUARD_TOLERANCE), ">": (">", threshold + _GUARD_TOLERANCE)}
        if g.op not in shifts:
            raise FormalizationError("Guard comparison", g.op, "missing or unsupported relation")
        relation, shifted = shifts[g.op]
        return f"({value} {relation} {_real(shifted)})"
    if g.predicate_type == "conjunction":
        parts = [_render_guard(child, imports, bounds) for child in g.guards or []]
        return "(" + " ∧ ".join(part for part in parts if part) + ")" if any(parts) else None
    raise FormalizationError("Guard", g.predicate_type, "unsupported guard type")


def render_guard(guard):
    """Return the exact named premise text, or None for an unrestricted domain."""
    return _render_guard(guard, set(), {})


def render_challenge(conjecture):
    imports, bounds = set(), {}
    guard = conjecture.guard_predicate

    def invariant(name):
        return _formal_invariant(name, imports)

    guard_code = _render_guard(guard, imports, bounds)

    def interval(node):
        if isinstance(node, ConstantNode):
            value = _rational(node.value)
            return value, value
        if isinstance(node, InvariantNode):
            name = INVARIANT_ALIASES.get(node.name, node.name)
            low, high = bounds.get(name, (Fraction(0), None) if name in _NONNEGATIVE_INVARIANTS else (None, None))
            order_low, _ = bounds.get("order", (Fraction(0), None))
            if name in {"clique_number", "independence_number"} and order_low is not None and order_low >= 1:
                # A singleton is a clique in both G and its complement whenever
                # V is nonempty: Mathlib's cliqueNum_ne_zero_of_finite.
                low = max(low, Fraction(1))
            return low, high
        if isinstance(node, UnaryOpNode):
            low, high = interval(node.child)
            if node.op in {"-", "neg"}:
                return -high if high is not None else None, -low if low is not None else None
            if node.op == "abs":
                if low is not None and low >= 0:
                    return low, high
                if high is not None and high <= 0:
                    return -high, -low if low is not None else None
                return Fraction(0), max(abs(low), abs(high)) if low is not None and high is not None else None
            if node.op == "sqr":
                abs_low, abs_high = interval(UnaryOpNode("abs", node.child))
                return abs_low ** 2, abs_high ** 2 if abs_high is not None else None
            if node.op in {"sqrt", "exp"}:
                return Fraction(0), None
        if isinstance(node, BinaryOpNode):
            low, high = interval(node.left)
            other_low, other_high = interval(node.right)
            if node.op == "+":
                return low + other_low if low is not None and other_low is not None else None, high + other_high if high is not None and other_high is not None else None
            if node.op == "-":
                return low - other_high if low is not None and other_high is not None else None, high - other_low if high is not None and other_low is not None else None
            if node.op == "*":
                if None not in (low, high, other_low, other_high):
                    products = [low * other_low, low * other_high, high * other_low, high * other_high]
                    return min(products), max(products)
                if low is not None and other_low is not None and low >= 0 and other_low >= 0:
                    return low * other_low, None
            if node.op in {"min", "max"}:
                if node.op == "min":
                    return min(low, other_low) if low is not None and other_low is not None else None, min(x for x in (high, other_high) if x is not None) if high is not None or other_high is not None else None
                return max(x for x in (low, other_low) if x is not None) if low is not None or other_low is not None else None, max(high, other_high) if high is not None and other_high is not None else None
        return None, None

    def require_nonzero(node):
        low, high = interval(node)
        if (low is not None and low >= _DIVISION_TOLERANCE) or (high is not None and high <= -_DIVISION_TOLERANCE):
            return
        raise FormalizationError("division", node.canonical_key, "denominator magnitude ≥ 1e-12 is not guaranteed by the grammar or explicit guard")

    def expression(node):
        if isinstance(node, InvariantNode):
            return invariant(node.name)
        if isinstance(node, ConstantNode):
            return _real(node.value)
        if isinstance(node, UnaryOpNode):
            child = expression(node.child)
            if node.op in {"-", "neg"}:
                return f"(-{child})"
            if node.op == "abs":
                return f"|{child}|"
            if node.op == "sqr":
                return f"({child} ^ 2)"
            if node.op == "inv":
                require_nonzero(node.child)
                return f"({child})⁻¹"
            if node.op in {"sqrt", "log1p"}:
                low, _ = interval(node.child)
                permitted = low is not None and (low >= Fraction(-1, 1000000000) if node.op == "sqrt" else low > -1)
                if not permitted:
                    raise FormalizationError("partial operation", node.op, "input domain is not guaranteed by the grammar or explicit guard")
                return f"(Real.sqrt {child})" if node.op == "sqrt" else f"(Real.log (1 + {child}))"
            if node.op in {"floor", "ceil"}:
                return f"((Int.{node.op} {child}) : ℝ)"
            if node.op == "exp":
                return f"(Real.exp {child})"
        if isinstance(node, BinaryOpNode):
            left, right = expression(node.left), expression(node.right)
            if node.op in {"+", "-", "*"}:
                return f"({left} {node.op} {right})"
            if node.op in {"min", "max"}:
                return f"({node.op} {left} {right})"
            if node.op == "/":
                require_nonzero(node.right)
                return f"({left} / {right})"
            if node.op == "^" and isinstance(node.right, ConstantNode):
                power = _rational(node.right.value)
                if power.denominator == 1 and power >= 0:
                    return f"({left} ^ {power.numerator})"
        raise FormalizationError("expression", getattr(node, "op", type(node).__name__), "partial or unsupported operation")

    ident = re.sub(r"[^a-zA-Z0-9_]", "_", conjecture.id)
    if not ident or ident[0].isdigit():
        ident = "thm_" + ident
    relation = {"<=": "≤", ">=": "≥", "==": "=", "<": "<", ">": ">"}[conjecture.rel]
    proposition = f"{expression(conjecture.lhs_expr)} {relation} {expression(conjecture.rhs_expr)}"
    import_code = "".join(f"import {name}\n" for name in (*_BASE_IMPORTS, *sorted(imports)))
    if imports & {"Mathlib.Analysis.Matrix.Spectrum", "Mathlib.InformationTheory.Hamming"}:
        import_code += "\nopen scoped BigOperators\n"
    hypothesis = f" (h_guard : {guard_code})" if guard_code else ""
    code = (import_code + "\n"
            f"theorem {ident} {{V : Type*}} [Fintype V] [DecidableEq V]\n"
            f"    (G : SimpleGraph V) [DecidableRel G.Adj]{hypothesis} :\n    {proposition} := by\n  sorry\n")
    return code, ident


CHROMATIC_ORDER_TACTIC = "exact_mod_cast (ENat.toNat_le_of_le_natCast G.chromaticNumber_le_card)"
CLIQUE_CHROMATIC_TACTIC = "exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))"

DEGREE_SUM_TACTIC = """have hn : 2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
    calc
      2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
      _ ≤ ∑ _v : V, G.maxDegree := Finset.sum_le_sum fun v _ => G.degree_le_maxDegree v
      _ = Fintype.card V * G.maxDegree := by simp
  exact_mod_cast hn"""

CLIQUE_DEGREE_TACTIC = """obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hn : G.cliqueNum ≤ G.maxDegree + 1 := by
    by_cases he : s.Nonempty
    · obtain ⟨v, hv⟩ := he
      have hsubset : s.erase v ⊆ G.neighborFinset v := by
        intro w hw
        rw [G.mem_neighborFinset]
        exact hs.isClique hv (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1.symm
      have hcard := Finset.card_le_card hsubset
      rw [Finset.card_erase_of_mem hv, G.card_neighborFinset_eq_degree, hs.card_eq] at hcard
      have hmax := G.degree_le_maxDegree v
      have hpos : 0 < G.cliqueNum := hs.card_eq ▸ Finset.card_pos.mpr ⟨v,hv⟩
      omega
    · have : G.cliqueNum = 0 := by
        rw [← hs.card_eq]
        exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp he)
      omega
  exact_mod_cast hn"""

CLIQUE_EDGES_TACTIC = """classical
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hdv : ∀ v ∈ s, (G.cliqueNum : ℝ) - 1 ≤ (G.degree v : ℝ) := by
    intro v hv
    have hsubset : s.erase v ⊆ G.neighborFinset v := by
      intro w hw
      rw [G.mem_neighborFinset]
      exact hs.isClique hv (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1.symm
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_erase_of_mem hv, G.card_neighborFinset_eq_degree, hs.card_eq] at hcard
    have hpos : 0 < G.cliqueNum := hs.card_eq ▸ Finset.card_pos.mpr ⟨v,hv⟩
    have hn : G.cliqueNum ≤ G.degree v + 1 := by omega
    have hr : (G.cliqueNum : ℝ) ≤ (G.degree v : ℝ) + 1 := by exact_mod_cast hn
    linarith
  calc
    (G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - 1) = ∑ v ∈ s, ((G.cliqueNum : ℝ) - 1) := by
      simp [hs.card_eq]
      ring
    _ ≤ ∑ v ∈ s, (G.degree v : ℝ) := Finset.sum_le_sum hdv
    _ ≤ ∑ v : V, (G.degree v : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ s) (fun v _ _ => Nat.cast_nonneg _)
    _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by exact_mod_cast G.sum_degrees_eq_twice_card_edges"""

CODE_BRIDGE_TACTIC = """classical
  let words : Finset (V → ZMod 2) := Finset.univ.filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)
  let stops : Finset (Finset V) := Finset.univ.filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))
  let cw : Finset ℕ := {Fintype.card V + 1} ∪ words.image hammingNorm
  let sw : Finset ℕ := {Fintype.card V + 1} ∪ stops.image Finset.card
  have hcw : cw.Nonempty := by simp [cw]
  have hsw : sw.Nonempty := by simp [sw]
  change ((sw.min' hsw - 1 : ℕ) : ℝ) + 1 ≤ (cw.min' hcw : ℝ)
  have hpos : 1 ≤ sw.min' hsw := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      omega
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp hS).2.1.card_pos
  have hle : sw.min' hsw ≤ cw.min' hcw := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      subst a
      exact Finset.min'_le _ _ (by simp [sw])
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      have hxne : x ≠ 0 := (Finset.mem_filter.mp hx).2.1
      have hxcode := (Finset.mem_filter.mp hx).2.2
      let S : Finset V := Finset.univ.filter (fun w => x w ≠ 0)
      have hSnonempty : S.Nonempty := by
        apply Finset.card_pos.mp
        change 0 < hammingNorm x
        exact hammingNorm_pos_iff.mpr hxne
      have hSstop : S ∈ stops := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, hSnonempty, ?_⟩
        rintro ⟨v, w, hw, hvw, hu⟩
        have hxw : x w ≠ 0 := (Finset.mem_filter.mp hw).2
        have heq : ∑ a ∈ G.neighborFinset v, x a = x w := by
          apply Finset.sum_eq_single w
          · intro a ha hne
            by_contra hxa
            have haS : a ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxa⟩
            exact hne (hu a haS ((G.mem_neighborFinset v a).mp ha))
          · intro hnot
            exact (hnot ((G.mem_neighborFinset v w).mpr hvw)).elim
        have hzero : ∑ a ∈ G.neighborFinset v, x a = 0 := by
          simpa [Matrix.mulVecLin_apply] using congrFun hxcode v
        exact hxw (heq.symm.trans hzero)
      apply Finset.min'_le
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨S, hSstop, rfl⟩))
  have hn : sw.min' hsw - 1 + 1 ≤ cw.min' hcw := by omega
  exact_mod_cast hn"""

CODE_DIMENSION_TACTIC = """have hn : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) ≤ Fintype.card V := by
    calc
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  exact_mod_cast hn"""

CODE_NONZERO_DISTANCE_TACTIC = """classical
  let K := LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
  have hk : 0 < Module.finrank (ZMod 2) K := by
    have hr : (0 : ℝ) < (Module.finrank (ZMod 2) K : ℝ) := by
      dsimp [K]
      linarith [h_guard]
    exact_mod_cast hr
  obtain ⟨x, hx⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2) (M := K)).mp hk
  have hxne : (x : V → ZMod 2) ≠ 0 := by
    intro heq
    apply hx
    exact Subtype.ext heq
  have hxcode : (G.adjMatrix (ZMod 2)).mulVecLin (x : V → ZMod 2) = 0 := x.property
  let words : Finset (V → ZMod 2) := Finset.univ.filter (fun y => y ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin y = 0)
  let weights : Finset ℕ := {Fintype.card V + 1} ∪ words.image hammingNorm
  have hweights : weights.Nonempty := by simp [weights]
  have hxmem : (x : V → ZMod 2) ∈ words := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne, hxcode⟩
  have hle : weights.min' hweights ≤ Fintype.card V :=
    le_trans (Finset.min'_le _ _ (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨(x : V → ZMod 2), hxmem, rfl⟩)))) hammingNorm_le_card_fintype
  change (weights.min' hweights : ℝ) ≤ (Fintype.card V : ℝ)
  exact_mod_cast hle"""

GENERAL_TACTICS = ["positivity", "simp", "omega", "norm_num", "linarith", "nlinarith", "aesop"]
TRUSTED_TACTICS = [CHROMATIC_ORDER_TACTIC, CLIQUE_CHROMATIC_TACTIC,
                   DEGREE_SUM_TACTIC, CLIQUE_DEGREE_TACTIC, CLIQUE_EDGES_TACTIC, *GENERAL_TACTICS]


def bootstrap_candidates():
    """Known finite graph bounds to seed proof reuse, never claimed as novel."""
    n, m, delta, omega = map(InvariantNode, ("order", "size", "max_degree", "clique_number"))
    candidates = [
        ("degree_sum_density_bound", BinaryOpNode("*", ConstantNode(2), m),
         BinaryOpNode("*", n, delta),
         "Every edge contributes two to the total degree, while each of the n vertices has degree at most Δ, so 2m ≤ nΔ. This known density bound connects the total edge count to a local maximum degree. It provides a quick consistency check and a reusable bridge between edge-count and degree-based clique bounds; it does not assert that a new theorem was discovered."),
        ("clique_le_max_degree_plus_one", omega, BinaryOpNode("+", delta, ConstantNode(1)),
         "A clique of size ω forces each of its vertices to have at least ω−1 neighbors. Consequently ω ≤ Δ+1 for every finite simple graph, including an empty graph. This familiar bound turns the cheaply computed maximum degree into a certified ceiling on clique size, which an exact clique solver can use to rule out branches that cannot improve its best witness."),
        ("clique_edges_density_bound", BinaryOpNode("*", omega, BinaryOpNode("-", omega, ConstantNode(1))),
         BinaryOpNode("*", ConstantNode(2), m),
         "A clique of size ω contains every pair of its vertices as an edge, so the whole graph must contain at least ω(ω−1)/2 edges. The checked inequality ω(ω−1) ≤ 2m gives a global upper bound on clique size from the edge count alone. Its practical value is an inexpensive, sound pruning rule for sparse candidate subgraphs; this is a known combinatorial fact, and any solver speedup must still be measured."),
    ]
    return [Conjecture.create(id=ident, lhs=left, rel="<=", rhs=right, metadata={
        "origin": "known_foundational_bound", "novelty_status": "KNOWN_FOUNDATIONAL",
        "scope": "all finite simple undirected graphs", "writeup": writeup,
        "provenance": "degree counting using pinned genuine Mathlib finite graph definitions",
    }) for ident, left, right, writeup in candidates]


def expander_code_candidates():
    """Known binary neighborhood-code facts, isolated from ordinary bootstrap seeds."""
    n, d, k, u = map(InvariantNode, ("order", "parity_code_distance", "parity_code_dimension", "unique_neighbor_radius"))
    rows = [
        ("parity_code_unique_neighbor_distance", BinaryOpNode("+", u, ConstantNode(1)), d, None,
         "The binary neighborhood parity code uses two copies of the graph's vertices: variables on one side and parity checks on the other, with the graph adjacency matrix over GF(2) as the check matrix. Every nonzero codeword support is a stopping set because a check touching it exactly once would see nonzero parity. Consequently u+1 ≤ d: a graph whose small variable sets have a unique neighboring check cannot have a codeword supported on those sets. This familiar expander-to-code mechanism supports erasure-recovery guarantees; it does not establish a new code construction or cryptographic security."),
        ("parity_code_dimension_le_order", k, n, None,
         "The binary parity code is a linear subspace of the n-coordinate binary vector space, so its dimension cannot exceed n. Dimension measures how many independent information bits the code can carry and prevents a large distance for the zero code from being mistaken for a useful coding construction. This is a known linear-algebra bound over GF(2)."),
        ("nonzero_parity_code_distance_le_order", d, n,
         GuardPredicate(predicate_type="comparison", invariant="parity_code_dimension", op=">=", threshold=1),
         "A positive-dimensional binary neighborhood code contains a nonzero codeword, whose Hamming weight is at most its length n. Thus d ≤ n under the explicit premise that the code dimension is at least one. The premise matters: the zero code uses the finite distance sentinel n+1, so removing it would make the statement false."),
        ("unique_neighbor_radius_nonnegative", ConstantNode(0), u, None,
         "The unique-neighbor radius is the largest number u ≤ n for which every nonempty variable set of at most u vertices has a check touching it exactly once. It is always nonnegative, even when isolated vertices make the radius zero. This sanity bound accompanies the substantive code-distance bridge and is not a discovery claim."),
    ]
    return [Conjecture.create(id=ident, lhs=left, rel="<=", rhs=right, guard=guard,
        metadata={"origin": "known_foundational_bound", "novelty_status": "KNOWN_FOUNDATIONAL",
            "scope": "binary neighborhood parity codes of all finite simple undirected graphs",
            "writeup": writeup, "provenance": "native GF(2) adjacency kernel and unique-neighbor parity counting"})
        for ident, left, right, guard, writeup in rows]


def bound_signature(conjecture):
    """Identify the mathematical goal, independently of its label or metadata."""
    left, right, relation = conjecture.lhs_expr, conjecture.rhs_expr, conjecture.rel
    if relation == ">=":
        left, right, relation = right, left, "<="
    return left.canonical_key, relation, right.canonical_key


def goal_specific_tactics(conjecture):
    if conjecture is None:
        return []
    guard = conjecture.guard_predicate
    nonzero_code = expander_code_candidates()[2]
    if (bound_signature(nonzero_code) == bound_signature(conjecture)
            and render_guard(nonzero_code.guard_predicate) == render_guard(guard)):
        return [CODE_NONZERO_DISTANCE_TACTIC]
    if guard and guard != "universal" and getattr(guard, "predicate_type", None) != "universal":
        return []
    targets = [
        Conjecture.create(id="chromatic", lhs=InvariantNode("chromatic_number"), rel="<=", rhs=InvariantNode("order")),
        Conjecture.create(id="clique", lhs=InvariantNode("clique_number"), rel="<=", rhs=InvariantNode("chromatic_number")),
        *bootstrap_candidates(),
        expander_code_candidates()[0],
        expander_code_candidates()[1],
    ]
    tactics = [CHROMATIC_ORDER_TACTIC, CLIQUE_CHROMATIC_TACTIC,
               DEGREE_SUM_TACTIC, CLIQUE_DEGREE_TACTIC, CLIQUE_EDGES_TACTIC,
               CODE_BRIDGE_TACTIC, CODE_DIMENSION_TACTIC]
    return [tactic for target, tactic in zip(targets, tactics)
            if bound_signature(target) == bound_signature(conjecture)]
