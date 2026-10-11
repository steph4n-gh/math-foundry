"""Unit Tests for Expanded DIMACS Algorithmic Benchmarking Suite and Bitset Solvers.

Verifies:
1. Benchmark topology generators (Johnson, c-fat, Brockington-Culberson, Sanchis).
2. Extended benchmark suite compilation.
3. BitsetBaselineSolver vs. BitsetSpectralSolver soundness and head-to-head agreement.
4. DIMACS .clq file parsing.
"""

from pathlib import Path
import networkx as nx
import pytest

from spectral_pruning.benchmarks import (
    generate_brock_graph,
    generate_cfat_graph,
    generate_johnson_graph,
    generate_san_graph,
    get_extended_benchmark_suite,
    get_standard_benchmark_suite,
)
from spectral_pruning.bitset_solvers import (
    BitsetBaselineSolver,
    BitsetSpectralSolver,
    _parse_dimacs_clq,
)


class TestDIMACSBenchmarkGenerators:
    """Verifies graph generation properties for advanced DIMACS topologies."""

    def test_johnson_graph_generation(self) -> None:
        # J(8, 2, 4): subsets of size 2 from 8 elements.
        # Disjoint pairs have dist = 4. Number of disjoint pairs = 28 * 15 / 2 = 210.
        G = generate_johnson_graph(n=8, v=2, d=4)
        assert G.number_of_nodes() == 28
        assert G.number_of_edges() == 210
        assert G.name == "johnson8-2-4"

    def test_cfat_graph_generation(self) -> None:
        G = generate_cfat_graph(n=60, clique_size=8, seed=42)
        assert G.number_of_nodes() == 60
        assert G.number_of_edges() > 0
        assert "c-fat" in G.name

        # Verify planted clique vertices form a complete clique
        target_clique = list(range(8))
        sub = G.subgraph(target_clique)
        assert sub.number_of_edges() == (8 * 7) // 2

    def test_brock_graph_generation(self) -> None:
        G = generate_brock_graph(n=50, k_planted=7, p=0.40, seed=101)
        assert G.number_of_nodes() == 50
        assert G.number_of_edges() > 0
        assert "brock" in G.name

        # Planted vertices form a complete subgraph
        planted = list(range(7))
        sub = G.subgraph(planted)
        assert sub.number_of_edges() == (7 * 6) // 2

    def test_san_graph_generation(self) -> None:
        G = generate_san_graph(n=50, p=0.65, k_planted=8, seed=202)
        assert G.number_of_nodes() == 50
        assert G.number_of_edges() > 0
        assert "san" in G.name

        planted = list(range(8))
        sub = G.subgraph(planted)
        assert sub.number_of_edges() == (8 * 7) // 2

    def test_extended_benchmark_suite(self) -> None:
        std_suite = get_standard_benchmark_suite()
        ext_suite = get_extended_benchmark_suite()
        assert len(ext_suite) > len(std_suite)
        assert len(ext_suite) >= 18

        for g in ext_suite:
            assert isinstance(g, nx.Graph)
            assert hasattr(g, "name")
            assert len(g.name) > 0
            assert g.number_of_nodes() > 0


class TestBitsetSolvers:
    """Verifies correctness and agreement between BitsetBaselineSolver and BitsetSpectralSolver."""

    @pytest.fixture
    def baseline_solver(self) -> BitsetBaselineSolver:
        return BitsetBaselineSolver()

    @pytest.fixture
    def spectral_solver(self) -> BitsetSpectralSolver:
        return BitsetSpectralSolver()

    def test_complete_graph(
        self,
        baseline_solver: BitsetBaselineSolver,
        spectral_solver: BitsetSpectralSolver,
    ) -> None:
        G = nx.complete_graph(6)
        w_base, c_base, _ = baseline_solver.solve(G)
        w_spec, c_spec, _ = spectral_solver.solve(G)
        assert w_base == 6
        assert w_spec == 6
        assert len(c_base) == 6
        assert len(c_spec) == 6

    def test_cycle_c5(
        self,
        baseline_solver: BitsetBaselineSolver,
        spectral_solver: BitsetSpectralSolver,
    ) -> None:
        G = nx.cycle_graph(5)
        w_base, c_base, _ = baseline_solver.solve(G)
        w_spec, c_spec, _ = spectral_solver.solve(G)
        assert w_base == 2
        assert w_spec == 2

    def test_petersen_graph(
        self,
        baseline_solver: BitsetBaselineSolver,
        spectral_solver: BitsetSpectralSolver,
    ) -> None:
        G = nx.petersen_graph()
        w_base, c_base, _ = baseline_solver.solve(G)
        w_spec, c_spec, _ = spectral_solver.solve(G)
        assert w_base == 2
        assert w_spec == 2

    def test_johnson_small(
        self,
        baseline_solver: BitsetBaselineSolver,
        spectral_solver: BitsetSpectralSolver,
    ) -> None:
        # J(6, 2, 4): subsets of size 2 from {1..6}. Max mutually disjoint subsets = 6 / 2 = 3.
        G = generate_johnson_graph(n=6, v=2, d=4)
        w_base, c_base, _ = baseline_solver.solve(G)
        w_spec, c_spec, _ = spectral_solver.solve(G)
        assert w_base == 3
        assert w_spec == 3
        # Check that returned clique is actually an independent pairwise disjoint set
        sub = G.subgraph(c_spec)
        assert sub.number_of_edges() == 3

    def test_cfat_small(
        self,
        baseline_solver: BitsetBaselineSolver,
        spectral_solver: BitsetSpectralSolver,
    ) -> None:
        G = generate_cfat_graph(n=40, clique_size=10, seed=123)
        w_base, c_base, _ = baseline_solver.solve(G)
        w_spec, c_spec, _ = spectral_solver.solve(G)
        assert w_base == w_spec
        assert w_base >= 10


class TestDIMACSParser:
    """Verifies DIMACS format parser with edge lines and comments."""

    def test_parse_dimacs_content(self, tmp_path: Path) -> None:
        clq_content = """c Sample DIMACS File
p edge 4 5
e 1 2
e 1 3
e 1 4
e 2 3
e 3 4
"""
        clq_file = tmp_path / "sample.clq"
        clq_file.write_text(clq_content, encoding="utf-8")

        G = _parse_dimacs_clq(str(clq_file))
        assert G.number_of_nodes() == 4
        assert G.number_of_edges() == 5
        assert G.has_edge(0, 1)
        assert G.has_edge(0, 2)
        assert G.has_edge(0, 3)
        assert G.has_edge(1, 2)
        assert G.has_edge(2, 3)
        assert not G.has_edge(1, 3)
        assert G.name == "sample"
