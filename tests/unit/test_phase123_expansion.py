"""Unit and Integration Tests for Phase 1, Phase 2, and Phase 3 Expansion.

Verifies:
- Metric & chemical graph theory invariants, presets, and AST formatting.
- Lean 4 token mappings and Mathlib axioms/lemmas for new invariants.
- Classical theorem registry entries (Moore bounds, Koolen-Moulton, Gutman, Gregory-Hershkowitz-Hoffman).
- Sieve handling of metric invariants on extremal and disconnected graphs.
- Multi-campaign sweep engine (--all-campaigns) generating master_catalog.json and master_report.tex.
- Continuous discovery loop daemon (--continuous / --daemon) updating cumulative_discovery_atlas.json.
"""

from pathlib import Path
import networkx as nx
import pytest

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    GuardPredicate,
    InvariantNode,
)
from autonomous_math.core.invariants import (
    STANDARD_SCALAR_INVARIANTS,
    GraphInvariantEvaluator,
    compute_diameter,
    compute_girth,
    compute_radius,
    compute_spectral_spread,
)
from autonomous_math.conjecturing.generator import ConjectureGenerator
from autonomous_math.sieve.instance_db import InstanceDatabase
from autonomous_math.novelty.literature_crosscheck import (
    LiteratureCrossChecker,
    NoveltyStatus,
)
from autonomous_math.export.lean_generator import LeanComparatorGenerator
from run_research import (
    CAMPAIGN_PRESETS,
    generate_master_latex_report,
    run_all_campaigns,
    run_campaign,
    run_continuous_daemon,
)


def test_metric_and_chemical_invariants_evaluation():
    """Verify evaluation of diameter, radius, girth, triangle_count, density, spectral_spread."""
    # Test on a cycle graph C4
    g = nx.cycle_graph(4)
    evaluator = GraphInvariantEvaluator()

    res = evaluator.evaluate(g, ["diameter", "radius", "girth", "triangle_count", "density", "spectral_spread"])
    assert res["diameter"] == 2.0
    assert res["radius"] == 2.0
    assert res["girth"] == 4.0
    assert res["triangle_count"] == 0.0
    assert abs(res["density"] - (4.0 / 6.0)) < 1e-5
    # For C4: eigenvalues are 2, 0, 0, -2. Spread is lambda_1 - lambda_n = 2 - (-2) = 4.0
    assert abs(res["spectral_spread"] - 4.0) < 1e-5
    assert abs(compute_spectral_spread(g) - 4.0) < 1e-5


def test_metric_invariants_disconnected_and_acyclic():
    """Verify robust handling of disconnected graphs (inf diameter/radius) and trees (inf girth)."""
    # Disconnected graph (2 isolated vertices)
    g_disc = nx.Graph()
    g_disc.add_nodes_from([0, 1])
    assert compute_diameter(g_disc) == float("inf")
    assert compute_radius(g_disc) == float("inf")

    # Tree (no cycles)
    g_tree = nx.path_graph(4)
    assert compute_girth(g_tree) == float("inf")


def test_lean_generator_tokens_for_new_invariants(tmp_path: Path):
    """Verify that LeanComparatorGenerator outputs correct Lean identifiers for new invariants."""
    lean_gen = LeanComparatorGenerator()
    c = Conjecture.create(
        id="test_metric_lean",
        lhs=InvariantNode(name="radius"),
        rel="<=",
        rhs=InvariantNode(name="diameter"),
        guard=GuardPredicate(property_name_or_type="is_connected"),
        statement="is_connected ==> radius <= diameter",
    )
    _, lean_path = lean_gen.generate(c, output_dir=tmp_path / "lean1")
    code = lean_path.read_text(encoding="utf-8")
    assert "G.radius" in code
    assert "G.diameter" in code
    assert "G.Connected" in code

    c2 = Conjecture.create(
        id="test_spread_lean",
        lhs=InvariantNode(name="spectral_spread"),
        rel="<=",
        rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="spectral_radius")),
        statement="spectral_spread <= 2 * spectral_radius",
    )
    _, lean_path2 = lean_gen.generate(c2, output_dir=tmp_path / "lean2")
    code2 = lean_path2.read_text(encoding="utf-8")
    assert "G.spectralSpread" in code2
    assert "G.spectralRadius" in code2


def test_literature_crosscheck_new_theorems():
    """Verify that LiteratureCrossChecker recognizes newly registered metric and chemical theorems."""
    checker = LiteratureCrossChecker()

    # Moore bound
    c_moore = Conjecture.create(
        id="moore_d2",
        lhs=InvariantNode(name="order"),
        rel="<=",
        rhs=BinaryOpNode(
            "+",
            BinaryOpNode("*", InvariantNode(name="max_degree"), InvariantNode(name="max_degree")),
            ConstantNode(value=1.0),
        ),
        guard=GuardPredicate(property_name_or_type="is_connected"),
        statement="is_connected ==> order <= max_degree * max_degree + 1",
    )
    rep_moore = checker.cross_check(c_moore, online=False)
    assert rep_moore.status in (NoveltyStatus.VERIFIED_REDISCOVERY, NoveltyStatus.TEXTBOOK_FOLKLORE)
    assert "moore" in rep_moore.matched_theorem.theorem_name.lower()

    # Radius <= Diameter
    c_rad = Conjecture.create(
        id="rad_diam",
        lhs=InvariantNode(name="radius"),
        rel="<=",
        rhs=InvariantNode(name="diameter"),
        guard=GuardPredicate(property_name_or_type="is_connected"),
        statement="is_connected ==> radius <= diameter",
    )
    rep_rad = checker.cross_check(c_rad, online=False)
    assert rep_rad.status in (NoveltyStatus.VERIFIED_REDISCOVERY, NoveltyStatus.TEXTBOOK_FOLKLORE)

    # Gregory spectral spread <= 2 * lambda_1
    c_spread = Conjecture.create(
        id="spread_two_lambda1",
        lhs=InvariantNode(name="spectral_spread"),
        rel="<=",
        rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="spectral_radius")),
        statement="spectral_spread <= 2 * spectral_radius",
    )
    rep_spread = checker.cross_check(c_spread, online=False)
    assert rep_spread.status in (NoveltyStatus.VERIFIED_REDISCOVERY, NoveltyStatus.TEXTBOOK_FOLKLORE)
    assert "gregory" in rep_spread.matched_theorem.author.lower() or "spread" in rep_spread.matched_theorem.theorem_name.lower()

    # Estrada >= Energy
    c_estrada = Conjecture.create(
        id="ee_ge_energy",
        lhs=InvariantNode(name="estrada_index"),
        rel=">=",
        rhs=InvariantNode(name="graph_energy"),
        statement="estrada_index >= graph_energy",
    )
    rep_estrada = checker.cross_check(c_estrada, online=False)
    assert rep_estrada.status in (NoveltyStatus.VERIFIED_REDISCOVERY, NoveltyStatus.TEXTBOOK_FOLKLORE)


def test_campaign_presets_presence():
    """Verify that CAMPAIGN_PRESETS contains metric_topological and chemical_energy."""
    assert "metric_topological" in CAMPAIGN_PRESETS
    assert "chemical_energy" in CAMPAIGN_PRESETS

    mt = CAMPAIGN_PRESETS["metric_topological"]
    assert len(mt["pairs"]) >= 5
    assert len(mt["triads"]) >= 5

    ce = CAMPAIGN_PRESETS["chemical_energy"]
    assert len(ce["pairs"]) >= 5
    assert len(ce["triads"]) >= 5


def test_sieve_vectorized_with_new_invariants():
    """Verify that InstanceDatabase sieves metric and chemical conjectures without errors."""
    db = InstanceDatabase()
    # Universally true on connected graphs: radius <= diameter
    c_true = Conjecture.create(
        id="sieve_rad_diam",
        lhs=InvariantNode(name="radius"),
        rel="<=",
        rhs=InvariantNode(name="diameter"),
        guard=GuardPredicate(property_name_or_type="is_connected"),
        statement="is_connected ==> radius <= diameter",
    )
    res_true = db.sieve_conjecture(c_true)
    assert res_true.status == "SURVIVED"

    # Universally false: diameter <= 0.5 * radius on connected graphs
    c_false = Conjecture.create(
        id="sieve_diam_small",
        lhs=InvariantNode(name="diameter"),
        rel="<=",
        rhs=BinaryOpNode("*", ConstantNode(value=0.5), InvariantNode(name="radius")),
        guard=GuardPredicate(property_name_or_type="is_connected"),
        statement="is_connected ==> diameter <= 0.5 * radius",
    )
    res_false = db.sieve_conjecture(c_false)
    assert res_false.status == "REFUTED"
    assert res_false.counterexample_certificate is not None


def test_generate_master_latex_report():
    """Verify that generate_master_latex_report creates compilable LaTeX structure."""
    dummy_catalog = {
        "timestamp": 123456.78,
        "aggregate_metrics": {
            "total_campaigns": 2,
            "total_conjectures_evaluated": 20,
            "total_survived": 15,
            "total_refuted": 5,
            "total_verified_rediscoveries": 6,
            "total_candidate_novel": 9,
            "total_lean_certified": 3,
        },
        "campaigns": {
            "metric_topological": {
                "title": "Metric & Topological Graph Theory",
                "total_conjectures": 10,
                "survived_count": 8,
                "refuted_count": 2,
                "novelty_summary": {
                    "verified_rediscoveries_count": 3,
                    "candidate_novel_count": 5,
                    "verified_rediscoveries": [
                        {
                            "conjecture": "is_connected ==> radius <= diameter",
                            "matched_theorem": {
                                "theorem_name": "Radius-Diameter Inequality",
                                "author": "Folklore",
                                "year": 1950,
                            },
                        }
                    ],
                    "candidate_novel_conjectures": [
                        {
                            "conjecture": "diameter <= 2 * radius",
                            "novelty_score": 0.85,
                            "suggested_action": "investigate",
                        }
                    ],
                },
                "lean_verification": {
                    "machine_checked_proven_count": 2,
                    "verified_proofs": [
                        {
                            "conjecture_id": "radius_le_diameter",
                            "tactic": "exact radius_le_diameter G h",
                            "duration_ms": 32.5,
                            "artifact_path": "exports/verified_theorems/radius_le_diameter.lean",
                        }
                    ],
                },
            }
        },
    }
    latex = generate_master_latex_report(dummy_catalog)
    assert r"\documentclass" in latex
    assert r"\begin{document}" in latex
    assert r"\end{document}" in latex
    assert "radius" in latex
    assert "Radius-Diameter Inequality" in latex


def test_run_campaign_smoke(tmp_path: Path):
    """Test run_campaign on chemical_energy with minimal limits."""
    summary = run_campaign(
        preset_name="chemical_energy",
        output_dir=tmp_path / "chem_test",
        limit_per_pair=1,
        limit_per_triad=1,
        max_lean_proof_targets=1,
        proof_backend="none",
    )
    assert summary["campaign"] == "chemical_energy"
    assert summary["total_conjectures"] > 0
    assert (tmp_path / "chem_test" / "research_digest.json").exists()


def test_run_all_campaigns_smoke(tmp_path: Path):
    """Test run_all_campaigns sweep creating master catalog and LaTeX report."""
    master_catalog = run_all_campaigns(
        output_dir=tmp_path / "sweep_test",
        limit_per_pair=1,
        limit_per_triad=1,
        max_lean_proof_targets=1,
        proof_backend="none",
    )
    assert (tmp_path / "sweep_test" / "master_catalog.json").exists()
    assert (tmp_path / "sweep_test" / "master_report.tex").exists()
    assert master_catalog["aggregate_metrics"]["total_campaigns"] == 7
    assert len(master_catalog["campaigns"]) == 7


def test_run_continuous_daemon_smoke(tmp_path: Path):
    """Test run_continuous_daemon executes 1 iteration and writes discovery atlas."""
    atlas = run_continuous_daemon(
        output_dir=tmp_path / "daemon_test",
        max_iterations=1,
        timeout_sec=90.0,
        limit_per_pair=1,
        limit_per_triad=1,
        max_lean_targets=1,
        proof_backend="none",
    )
    assert atlas["total_iterations"] == 1
    assert (tmp_path / "daemon_test" / "cumulative_discovery_atlas.json").exists()
    assert len(atlas["theorems"]) > 0


def test_generate_chemical_candidates_presence():
    """Verify that ConjectureGenerator produces chemical energy candidate bounds."""
    gen = ConjectureGenerator()
    candidates = gen.generate_chemical_candidates()
    assert len(candidates) >= 5
    ids = [c.id for c in candidates]
    assert "gutman_energy_size_bound" in ids
    assert "graph_energy_spectral_radius_lower" in ids
    assert "estrada_ge_energy" in ids
    assert "spectral_spread_le_two_spectral_radius" in ids
    assert "koolen_moulton_order_2003" in ids


def test_format_statement_fallback_guards():
    """Verify _format_statement_fallback transforms predicates into correct Lean representations."""
    from autonomous_math.export.lean_generator import _format_statement_fallback

    stmt_conn = _format_statement_fallback("is_connected ==> radius <= diameter")
    assert "G.Connected →" in stmt_conn
    assert "G.radius" in stmt_conn
    assert "G.diameter" in stmt_conn

    stmt_bip = _format_statement_fallback("is_bipartite ==> chromatic_number <= 2")
    assert "G.Colorable 2 →" in stmt_bip

    stmt_tree = _format_statement_fallback("is_tree ==> diameter <= order - 1")
    assert "G.IsTree →" in stmt_tree

    stmt_comp = _format_statement_fallback("diameter <= 2 ==> order <= max_degree * max_degree + 1")
    assert "≤ 2" in stmt_comp
    assert "Fintype.card V" in stmt_comp


@pytest.mark.parametrize("family,identifier", [
    ("metric", "radius_le_diameter"), ("metric", "diameter_le_two_radius"),
    ("metric", "moore_bound_diameter_2"), ("chemical", "gutman_energy_size_bound"),
    ("chemical", "estrada_ge_energy")])
def test_unformalized_metric_and_chemical_candidates_remain_unresolved(tmp_path, family, identifier):
    """Legacy axiomatic statements cannot become genuine certificates."""
    from autonomous_math.prover.lean_prover import LeanProofSearch
    gen = ConjectureGenerator()
    candidates = gen.generate_metric_candidates() if family == "metric" else gen.generate_chemical_candidates()
    c = next(c for c in candidates if c.id == identifier)
    result = LeanProofSearch(max_attempts=1).prove_conjecture(c, output_dir=tmp_path)
    assert not result.is_proven
    assert result.status == "UNRESOLVED"
    assert result.receipt_path is None
