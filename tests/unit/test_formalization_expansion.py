"""Exact AST translation, domain guards, and native Mathlib calibration checks."""
import json
import os
from pathlib import Path
import re
import subprocess

import networkx as nx
import pytest

from autonomous_math.core.ast import BinaryOpNode, ConstantNode, Conjecture, GuardPredicate, InvariantNode, UnaryOpNode
from autonomous_math.core.invariants import GraphInvariantEvaluator
from autonomous_math.prover.trusted_lean import FormalizationError, capability_report, render_challenge, render_guard


def goal(expression, guard=None, ident="translation_check", expected=None):
    return Conjecture.create(id=ident, lhs=expression, rel="==", rhs=expression if expected is None else ConstantNode(expected), guard=guard)


def compile_lean(source):
    workspace = Path(__file__).resolve().parents[2] / "certified_lean"
    environment = {key: value for key, value in os.environ.items() if key != "LEAN_PATH"}
    result = subprocess.run(
        [str(Path.home() / ".elan/bin/lake"), "env", "lean", "--stdin"],
        cwd=workspace, env=environment, input=source, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60,
    )
    assert result.returncode == 0, result.stdout
    assert "sorryAx" not in result.stdout and "Lean.ofReduceBool" not in result.stdout
    for axiom_list in re.findall(r"depends on axioms: \[([^\]]*)\]", result.stdout):
        assert set(axiom.strip() for axiom in axiom_list.split(",") if axiom.strip()) <= {"propext", "Classical.choice", "Quot.sound"}
    return result.stdout


def combine_sources(sources):
    imports = sorted({line for source in sources for line in source.splitlines() if line.startswith("import ")})
    bodies = ["\n".join(line for line in source.splitlines() if not line.startswith("import ") and line != "open scoped BigOperators") for source in sources]
    return "\n".join(imports) + "\nopen scoped BigOperators\n" + "\n".join(bodies)


@pytest.mark.parametrize("name,expression", [
    ("order", "(Fintype.card V : ℝ)"),
    ("size", "(G.edgeFinset.card : ℝ)"),
    ("chromatic_number", "(G.chromaticNumber.toNat : ℝ)"),
    ("clique_number", "(G.cliqueNum : ℝ)"),
    ("max_degree", "(G.maxDegree : ℝ)"),
])
def test_original_universal_challenge_signature_is_byte_identical(name, expression):
    source, ident = render_challenge(goal(InvariantNode(name)))
    assert ident == "translation_check"
    assert source == (
        "import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex\n"
        "import Mathlib.Combinatorics.SimpleGraph.DegreeSum\n"
        "import Mathlib.Tactic\n\n"
        "theorem translation_check {V : Type*} [Fintype V] [DecidableEq V]\n"
        "    (G : SimpleGraph V) [DecidableRel G.Adj] :\n"
        f"    {expression} = {expression} := by\n  sorry\n"
    )


def test_capability_report_is_explicit_and_json_serializable():
    report = capability_report()
    json.dumps(report)
    assert {"min_degree", "average_degree", "density", "independence_number", "triangle_count", "spectral_radius", "graph_energy", "estrada_index"} <= set(report["invariants"])
    assert {"is_connected", "is_tree", "is_forest", "is_bipartite", "is_triangle_free", "is_regular", "is_empty", "is_complete"} == set(report["properties"])
    assert "diameter" not in report["invariants"]
    assert "1e-12" in report["partial_operation_rules"]["division"]


@pytest.mark.parametrize("name", ["diameter", "radius", "girth", "adjacency_spectrum", "unknown_invariant"])
def test_unsupported_invariant_is_a_structured_support_error(name):
    with pytest.raises(FormalizationError) as error:
        render_challenge(goal(InvariantNode(name)))
    assert error.value.category == "invariant" and error.value.feature == name


@pytest.mark.parametrize("name", ["is_planar", "is_chordal", "unknown_property"])
def test_unsupported_guard_cannot_be_erased(name):
    with pytest.raises(FormalizationError) as error:
        render_challenge(goal(ConstantNode(0), GuardPredicate(name)))
    assert error.value.category == "Guard"


def test_named_composite_guard_is_exact_and_available_to_proofs():
    guard = GuardPredicate(predicate_type="conjunction", guards=[
        GuardPredicate("is_connected"),
        GuardPredicate("is_triangle_free", negated=True),
        GuardPredicate(predicate_type="comparison", invariant="n", op=">=", threshold=3),
    ])
    premise = render_guard(guard)
    assert "G.Connected" in premise and "¬ (G.CliqueFree 3)" in premise
    assert "(Fintype.card V : ℝ) ≥ (29999999 / 10000000 : ℝ)" in premise
    source, _ = render_challenge(goal(InvariantNode("order"), guard))
    assert f"(h_guard : {premise}) :\n    " in source
    assert render_guard("universal") is None
    assert render_guard(GuardPredicate(predicate_type="conjunction", guards=[])) is None


def test_numeric_guard_preserves_tolerance_and_evaluator_negation_behavior():
    numeric = GuardPredicate(predicate_type="comparison", invariant="density", op="==", threshold=.5, negated=True)
    assert render_guard(numeric) == render_guard(numeric.model_copy(update={"negated": False}))
    assert "≤ (1 / 10000000 : ℝ)" in render_guard(numeric)
    assert "- (1 / 2 : ℝ)" in render_guard(numeric)


@pytest.mark.parametrize("denominator", [ConstantNode(0), ConstantNode(1e-13), InvariantNode("order"), BinaryOpNode("-", InvariantNode("order"), ConstantNode(1))])
def test_division_does_not_silently_totalize_undefined_inputs(denominator):
    with pytest.raises(FormalizationError) as error:
        render_challenge(goal(BinaryOpNode("/", ConstantNode(1), denominator)))
    assert error.value.category == "division"


def test_division_domain_follows_from_grammar_or_exact_explicit_guard():
    safe_denominators = [ConstantNode(-2), ConstantNode(1e-12), BinaryOpNode("+", InvariantNode("order"), ConstantNode(1)), BinaryOpNode("max", InvariantNode("order"), ConstantNode(2))]
    for denominator in safe_denominators:
        render_challenge(goal(BinaryOpNode("/", ConstantNode(1), denominator)))
    positive_order = GuardPredicate(predicate_type="comparison", invariant="order", op=">=", threshold=1)
    source, _ = render_challenge(goal(BinaryOpNode("/", InvariantNode("size"), InvariantNode("order")), positive_order))
    assert "(h_guard :" in source and "(G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)" in source
    render_challenge(goal(BinaryOpNode("/", InvariantNode("order"), InvariantNode("independence_number")), positive_order))
    render_challenge(goal(UnaryOpNode("inv", InvariantNode("order")), GuardPredicate("is_connected")))
    negative_min = GuardPredicate(predicate_type="comparison", invariant="smallest_adjacency_eigenvalue", op="<=", threshold=-1)
    render_challenge(goal(BinaryOpNode("/", ConstantNode(1), UnaryOpNode("abs", InvariantNode("smallest_adjacency_eigenvalue"))), negative_min))
    near_zero = GuardPredicate(predicate_type="comparison", invariant="average_degree", op=">=", threshold=0)
    with pytest.raises(FormalizationError):
        render_challenge(goal(BinaryOpNode("/", ConstantNode(1), InvariantNode("average_degree")), near_zero))


def test_other_partial_operations_have_explicit_domain_checks():
    render_challenge(goal(UnaryOpNode("sqrt", InvariantNode("size"))))
    render_challenge(goal(UnaryOpNode("sqrt", ConstantNode(-1e-10))))
    render_challenge(goal(UnaryOpNode("log1p", InvariantNode("order"))))
    render_challenge(goal(BinaryOpNode("^", InvariantNode("order"), ConstantNode(3))))
    for expression in [UnaryOpNode("sqrt", ConstantNode(-1)), UnaryOpNode("log1p", ConstantNode(-1)), BinaryOpNode("^", InvariantNode("order"), ConstantNode(.5)), BinaryOpNode("^", InvariantNode("order"), ConstantNode(-1))]:
        with pytest.raises(FormalizationError):
            render_challenge(goal(expression))


@pytest.mark.parametrize("order,properties", [
    (0, {"is_connected": False, "is_tree": False, "is_forest": True, "is_bipartite": True, "is_triangle_free": True, "is_regular": True, "is_empty": True, "is_complete": False}),
    (1, {"is_connected": True, "is_tree": True, "is_forest": True, "is_bipartite": True, "is_triangle_free": True, "is_regular": True, "is_empty": True, "is_complete": True}),
])
def test_property_boundary_conventions_match_graph_evaluator(order, properties):
    graph = nx.empty_graph(order)
    for name, expected in properties.items():
        assert GuardPredicate(name).evaluate(graph) is expected
    assert render_guard("is_empty") == "(G = ⊥)"
    assert "Nonempty V" in render_guard("is_complete")


def test_every_advertised_native_expression_and_guard_really_compiles():
    sources = []
    report = capability_report()
    for name in report["invariants"]:
        source, ident = render_challenge(goal(InvariantNode(name), ident=f"typed_{name}"))
        sources.append(source.replace("  sorry", "  rfl") + f"\n#print axioms {ident}\n")
    for name in report["properties"]:
        source, ident = render_challenge(goal(ConstantNode(0), GuardPredicate(name), ident=f"typed_{name}"))
        sources.append(source.replace("  sorry", "  rfl") + f"\n#print axioms {ident}\n")
    for op in report["unary_operations"]:
        source, _ = render_challenge(goal(UnaryOpNode(op, ConstantNode(2)), ident=f"typed_op_{op}"))
        sources.append(source.replace("  sorry", "  rfl"))
    for index, op in enumerate(report["binary_operations"]):
        source, _ = render_challenge(goal(BinaryOpNode(op, ConstantNode(2), ConstantNode(3)), ident=f"typed_binary_{index}"))
        sources.append(source.replace("  sorry", "  rfl"))
    compile_lean(combine_sources(sources))


def concrete_source(name, order, expected, tactic, complete=False):
    source, _ = render_challenge(goal(InvariantNode(name), ident=f"sample_{name}_{order}", expected=expected))
    proposition = source.rsplit(" :\n    ", 1)[1].split(" := by", 1)[0]
    proposition = re.sub(r"(?<![A-Za-z0-9_])V(?![A-Za-z0-9_])", f"(Fin {order})", proposition)
    graph = f"({'⊤' if complete else '⊥'} : SimpleGraph (Fin {order}))"
    proposition = re.sub(r"(?<![A-Za-z0-9_])G(?![A-Za-z0-9_])", graph, proposition)
    imports = "\n".join(line for line in source.splitlines() if line.startswith("import "))
    return f"{imports}\nexample : {proposition} := by\n  {tactic}\n"


def test_native_boundary_values_counted_triangles_and_independence():
    sources = []
    empty_names = set(capability_report()["invariants"]) - {"order", "size", "chromatic_number", "clique_number", "max_degree"}
    for name in sorted(empty_names):
        expected = 1 if name == "parity_code_distance" else 0
        assert GraphInvariantEvaluator.evaluate_single(nx.empty_graph(0), name) == expected
        tactic = {
            "parity_code_distance": """have hf : ((Finset.univ : Finset (Fin 0 → ZMod 2)).filter (fun x => x ≠ 0 ∧ ((⊥ : SimpleGraph (Fin 0)).adjMatrix (ZMod 2)).mulVecLin x = 0)) = ∅ := by
    ext x
    simp [Subsingleton.elim x (0 : Fin 0 → ZMod 2)]
  dsimp only
  simp only [hf, Finset.image_empty, Finset.union_empty, Fintype.card_fin, Nat.zero_add, Finset.min'_singleton, Nat.sub_self, Nat.cast_one, Nat.cast_zero]""",
            "parity_code_dimension": "simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero]",
            "unique_neighbor_radius": """have hf : ((Finset.univ : Finset (Finset (Fin 0))).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ (⊥ : SimpleGraph (Fin 0)).Adj v w ∧ ∀ u ∈ S, (⊥ : SimpleGraph (Fin 0)).Adj v u → u = w))) = ∅ := by
    ext S
    simp [Subsingleton.elim S (∅ : Finset (Fin 0))]
  dsimp only
  simp only [hf, Finset.image_empty, Finset.union_empty, Fintype.card_fin, Nat.zero_add, Finset.min'_singleton, Nat.sub_self, Nat.cast_one, Nat.cast_zero]""",
        }.get(name, "simp")
        sources.append(concrete_source(name, 0, expected, tactic))
    sources.extend([
        concrete_source("min_degree", 3, 2, "simp", complete=True),
        concrete_source("triangle_count", 3, 1, "exact_mod_cast (show ((⊤ : SimpleGraph (Fin 3)).cliqueFinset 3).card = 1 by decide)", complete=True),
        concrete_source("independence_number", 3, 3, "simp [SimpleGraph.cliqueNum_top]"),
        concrete_source("density", 1, 0, "norm_num"),
        concrete_source("average_degree", 3, 2, "have h : (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 := by decide\n  norm_num only [Fintype.card_fin, h] <;> simp", complete=True),
        concrete_source("density", 3, 1, "have h : (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 := by decide\n  norm_num only [Fintype.card_fin, h] <;> simp", complete=True),
    ])
    sources.append(r"""
import Mathlib.Combinatorics.SimpleGraph.Acyclic
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 1 ≤ Fintype.card V) : 1 ≤ Gᶜ.cliqueNum := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact (Gᶜ.cliqueNum_ne_zero_of_finite).pos
example : ¬ (⊥ : SimpleGraph (Fin 0)).Connected := by simp [SimpleGraph.connected_iff]
example : ¬ (⊥ : SimpleGraph (Fin 0)).IsTree := by simp [SimpleGraph.isTree_iff, SimpleGraph.connected_iff]
example : (⊥ : SimpleGraph (Fin 0)).IsAcyclic := by simp
example : (⊥ : SimpleGraph (Fin 0)).Colorable 2 := by apply SimpleGraph.Colorable.of_isEmpty
example : (⊥ : SimpleGraph (Fin 0)).CliqueFree 3 := by apply SimpleGraph.cliqueFree_bot; decide
example : ∃ d : ℕ, (⊥ : SimpleGraph (Fin 0)).IsRegularOfDegree d := ⟨0, SimpleGraph.IsRegularOfDegree.bot⟩
example : ¬ (Nonempty (Fin 0) ∧ (⊥ : SimpleGraph (Fin 0)) = ⊤) := by simp
example : (⊥ : SimpleGraph (Fin 1)).Connected := by
  rw [SimpleGraph.connected_bot_iff]
  exact ⟨inferInstance, inferInstance⟩
example : (⊥ : SimpleGraph (Fin 1)).IsTree := by
  simp only [SimpleGraph.isTree_iff, SimpleGraph.isAcyclic_bot, and_true, SimpleGraph.connected_bot_iff]
  exact ⟨inferInstance, inferInstance⟩
example : (Nonempty (Fin 1) ∧ (⊥ : SimpleGraph (Fin 1)) = ⊤) := by
  constructor
  · exact inferInstance
  · ext u v
    simp [Subsingleton.elim u v]
""")
    compile_lean(combine_sources(sources))


def test_concrete_adjacency_spectrum_and_energy_have_native_kernel_semantics():
    # A concrete, nonzero calibration establishes eigenvalue multiplicity and
    # matrix meaning. Reflection/tautological typing alone would not check this.
    compile_lean(r"""
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic
open Polynomial Matrix
open scoped BigOperators
noncomputable section

theorem edge_charpoly : ((⊤ : SimpleGraph (Fin 2)).adjMatrix ℝ).charpoly =
    (X - C (1 : ℝ)) * (X - C (-1 : ℝ)) := by
  rw [Matrix.charpoly_fin_two]
  norm_num [Matrix.trace, Matrix.det_fin_two, SimpleGraph.adjMatrix]
  ring

theorem edge_roots : ((⊤ : SimpleGraph (Fin 2)).adjMatrix ℝ).charpoly.roots = {1, -1} := by
  rw [edge_charpoly, Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))]
  rw [roots_X_sub_C, roots_X_sub_C]
  rfl

theorem edge_sorted_eigenvalues :
  List.ofFn ((⊤ : SimpleGraph (Fin 2)).isHermitian_adjMatrix ℝ).eigenvalues₀ = [1, -1] := by
  rw [← Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀, edge_roots]
  norm_num
  rw [Multiset.sort_cons (1 : ℝ) {-1} (fun x y => y ≤ x) (by simp)]
  simp

theorem edge_energy : ∑ v : Fin 2, |((⊤ : SimpleGraph (Fin 2)).isHermitian_adjMatrix ℝ).eigenvalues v| = 2 := by
  let hA := (⊤ : SimpleGraph (Fin 2)).isHermitian_adjMatrix ℝ
  have hm : Finset.univ.val.map hA.eigenvalues = {1, -1} := by
    simpa using hA.roots_charpoly_eq_eigenvalues.symm.trans edge_roots
  calc
    _ = ((Finset.univ.val.map hA.eigenvalues).map abs).sum := by simp [Finset.sum]
    _ = 2 := by rw [hm]; norm_num
#print axioms edge_sorted_eigenvalues
#print axioms edge_energy
""")
    graph = nx.complete_graph(2)
    assert GraphInvariantEvaluator.evaluate_single(graph, "spectral_radius") == pytest.approx(1)
    assert GraphInvariantEvaluator.evaluate_single(graph, "smallest_adjacency_eigenvalue") == pytest.approx(-1)
    assert GraphInvariantEvaluator.evaluate_single(graph, "graph_energy") == pytest.approx(2)
