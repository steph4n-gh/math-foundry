"""Graph Theory Axiom and Lemma Library.

Feature 9:
Provides:
- AxiomDefinition: Structured formal definition containing LaTeX and Lean 4 representations.
- AxiomLibrary: In-memory registry and query interface for graph theory axioms and bounds:
  Euler's Handshaking, Greedy Coloring Bound, Turan's Theorem, Mantel's Theorem,
  Brooks' Theorem, Caro-Wei Bound, Erdős-Szekeres Ramsey Bound, Hoffman Spectral Bound,
  Clique-Chromatic Bound, Independence Partition Bound, and Wilf Spectral Bound.
"""

from __future__ import annotations

import re
from typing import Any, Dict, List, Optional
from pydantic import BaseModel, ConfigDict, Field

from autonomous_math.prover.dag import ProofNode


class AxiomDefinition(BaseModel):
    """Specification of an axiomatic theorem in graph theory."""

    model_config = ConfigDict(extra="allow", arbitrary_types_allowed=True)

    axiom_id: str
    name: str
    description: str
    statement_latex: str
    statement_lean: str
    category: str = "general"
    challenge_module: str = "ComparatorChallenges.Axiom"
    solution_module: str = "OAI.Combinatorics.Main"
    theorem_name: str = "axiom_theorem"
    permitted_axioms: List[str] = Field(
        default_factory=lambda: ["propext", "Quot.sound", "Classical.choice"]
    )
    scope: Dict[str, Any] = Field(default_factory=lambda: {"assumptions": []})
    metadata: Dict[str, Any] = Field(default_factory=dict)

    def to_proof_node(self) -> ProofNode:
        """Instantiate as a ProofNode for insertion into a LemmaDAG."""
        return ProofNode(
            node_id=self.axiom_id,
            label=self.name,
            statement_latex=self.statement_latex,
            statement_lean=self.statement_lean,
            node_type="AXIOM",
            scope=dict(self.scope),
            confidence_score=1.0,
            is_proven=True,
            status="PROVEN",
            metadata={"description": self.description, "category": self.category},
        )

    def to_lean_source(self) -> str:
        """Generate a complete Lean 4 challenge file matching math/lean format."""
        mod = self.challenge_module.split(".")[-1]
        lines = [
            "import Mathlib",
            "",
            "namespace OAI",
            "",
            f"namespace {mod}",
            "",
            f"theorem {self.theorem_name} :",
            f"    {self.statement_lean} := by",
            "  sorry",
            "",
            f"end {mod}",
            "",
            "end OAI",
            "",
        ]
        return "\n".join(lines)

    def to_comparator_json(self) -> Dict[str, Any]:
        """Generate openai/math comparator challenge JSON metadata."""
        return {
            "challenge_module": self.challenge_module,
            "solution_module": self.solution_module,
            "theorem_names": [f"OAI.{self.challenge_module.split('.')[-1]}.{self.theorem_name}"],
            "definition_names": [],
            "permitted_axioms": list(self.permitted_axioms),
            "enable_nanoda": False,
        }


class AxiomLibrary:
    """Library of graph theory axioms, classical theorems, and extremal bounds."""

    def __init__(self) -> None:
        self._axioms: Dict[str, AxiomDefinition] = {}
        self._aliases: Dict[str, str] = {}
        self._populate_library()

    def _register(self, axiom: AxiomDefinition, aliases: Optional[List[str]] = None) -> None:
        self._axioms[axiom.axiom_id] = axiom
        self._aliases[axiom.axiom_id.lower()] = axiom.axiom_id
        if aliases:
            for al in aliases:
                self._aliases[al.lower()] = axiom.axiom_id

    def _populate_library(self) -> None:
        # 1. Euler's Handshaking Lemma
        self._register(
            AxiomDefinition(
                axiom_id="handshaking_lemma",
                name="Euler's Handshaking Lemma",
                description="The sum of vertex degrees equals twice the edge count: sum d(v) = 2m.",
                statement_latex=r"\sum_{v \in V(G)} \deg(v) = 2 |E(G)|",
                statement_lean="(∑ v : V, G.degree v : ℝ) = 2 * (G.edgeFinset.card : ℝ)",
                category="degree",
                challenge_module="ComparatorChallenges.HandshakingLemma",
                solution_module="OAI.Combinatorics.Handshaking.Main",
                theorem_name="handshaking_sum",
                scope={"assumptions": []},
            ),
            aliases=["handshaking", "euler_handshaking", "degree_sum_formula"],
        )

        # 2. Greedy Coloring Upper Bound
        self._register(
            AxiomDefinition(
                axiom_id="greedy_coloring_bound",
                name="Greedy Coloring Upper Bound",
                description="The chromatic number is bounded above by Delta(G) + 1.",
                statement_latex=r"\chi(G) \le \Delta(G) + 1",
                statement_lean="(G.chromaticNumber : ℝ) ≤ (G.maxDegree : ℝ) + 1",
                category="coloring",
                challenge_module="ComparatorChallenges.GreedyColoring",
                solution_module="OAI.Combinatorics.Coloring.Main",
                theorem_name="chromatic_le_max_degree_add_one",
                scope={"assumptions": []},
            ),
            aliases=["greedy_bound", "greedy_coloring", "greedy"],
        )

        # 3. Turán's Extremal Theorem
        self._register(
            AxiomDefinition(
                axiom_id="turan_theorem",
                name="Turán's Theorem",
                description="Any graph on n vertices with no K_{r+1} has at most (1 - 1/r) * (n^2 / 2) edges.",
                statement_latex=r"|E(G)| \le \left(1 - \frac{1}{\omega(G)}\right) \frac{n^2}{2}",
                statement_lean="(G.edgeFinset.card : ℝ) ≤ (1 - 1 / (G.cliqueNum : ℝ)) * ((Fintype.card V : ℝ)^2 / 2)",
                category="extremal",
                challenge_module="ComparatorChallenges.TuranTheorem",
                solution_module="OAI.Combinatorics.Extremal.Main",
                theorem_name="edge_card_le_turan_bound",
                scope={"assumptions": ["order >= 1", "clique_number >= 1"]},
            ),
            aliases=["turan", "turan_bound", "turans_theorem"],
        )

        # 4. Mantel's Theorem
        self._register(
            AxiomDefinition(
                axiom_id="mantel_theorem",
                name="Mantel's Theorem",
                description="A triangle-free graph of order n has at most floor(n^2 / 4) edges.",
                statement_latex=r"T(G) = 0 \implies |E(G)| \le \frac{n^2}{4}",
                statement_lean="G.CliqueFree 3 → (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ)^2 / 4",
                category="extremal",
                challenge_module="ComparatorChallenges.MantelTheorem",
                solution_module="OAI.Combinatorics.Extremal.Main",
                theorem_name="triangle_free_edge_bound",
                scope={"assumptions": ["is_triangle_free"]},
            ),
            aliases=["mantel", "mantels_theorem"],
        )

        # 5. Brooks' Theorem
        self._register(
            AxiomDefinition(
                axiom_id="brooks_theorem",
                name="Brooks' Theorem",
                description="For connected G not complete and not an odd cycle, chi(G) <= Delta(G).",
                statement_latex=r"G \text{ connected} \land G \not\cong K_n \land G \not\cong C_{2k+1} \implies \chi(G) \le \Delta(G)",
                statement_lean="G.Connected ∧ ¬ G.IsComplete ∧ ¬ G.IsOddCycle → (G.chromaticNumber : ℝ) ≤ (G.maxDegree : ℝ)",
                category="coloring",
                challenge_module="ComparatorChallenges.BrooksTheorem",
                solution_module="OAI.Combinatorics.Coloring.Main",
                theorem_name="brooks_bound",
                scope={"assumptions": ["is_connected", "not_complete", "not_odd_cycle"]},
            ),
            aliases=["brooks", "brooks_bound"],
        )

        # 6. Caro-Wei Lower Bound on Independence Number
        self._register(
            AxiomDefinition(
                axiom_id="caro_wei_theorem",
                name="Caro-Wei Theorem",
                description="The independence number is bounded below: alpha(G) >= n / (Delta(G) + 1).",
                statement_latex=r"\alpha(G) \ge \frac{n}{\Delta(G) + 1}",
                statement_lean="(G.indepNum : ℝ) ≥ (Fintype.card V : ℝ) / ((G.maxDegree : ℝ) + 1)",
                category="independence",
                challenge_module="ComparatorChallenges.CaroWei",
                solution_module="OAI.Combinatorics.Independence.Main",
                theorem_name="caro_wei_independence_bound",
                scope={"assumptions": ["order >= 1"]},
            ),
            aliases=["caro_wei", "caro_wei_bound", "caro-wei"],
        )

        # 7. Erdős-Szekeres Ramsey Bound
        self._register(
            AxiomDefinition(
                axiom_id="ramsey_bound",
                name="Erdős-Szekeres Ramsey Bound",
                description="Ramsey number R(s, t) is bounded above: R(s, t) <= choose(s+t-2, s-1).",
                statement_latex=r"R(s, t) \le \binom{s + t - 2}{s - 1}",
                statement_lean="ramseyNumber s t ≤ Nat.choose (s + t - 2) (s - 1)",
                category="extremal",
                challenge_module="ComparatorChallenges.RamseyBound",
                solution_module="OAI.Combinatorics.Ramsey.Main",
                theorem_name="erdos_szekeres_bound",
                scope={"assumptions": ["s >= 2", "t >= 2"]},
            ),
            aliases=["ramsey", "erdos_szekeres"],
        )

        # 8. Hoffman's Spectral Lower Bound on Chromatic Number
        self._register(
            AxiomDefinition(
                axiom_id="hoffman_spectral_bound",
                name="Hoffman's Spectral Bound",
                description="For graph G with lambda_n < 0, chi(G) >= 1 - lambda_1 / lambda_n.",
                statement_latex=r"\chi(G) \ge 1 - \frac{\lambda_1(G)}{\lambda_n(G)}",
                statement_lean="(G.chromaticNumber : ℝ) ≥ 1 - (G.spectralRadius / G.smallestAdjacencyEigenvalue)",
                category="spectral",
                challenge_module="ComparatorChallenges.HoffmanSpectral",
                solution_module="OAI.Combinatorics.Spectral.Main",
                theorem_name="hoffman_chromatic_lower_bound",
                scope={"assumptions": ["smallest_adjacency_eigenvalue < 0"]},
            ),
            aliases=["hoffman", "hoffman_bound", "hoffman_spectral"],
        )

        # 9. Clique-Chromatic Lower Bound
        self._register(
            AxiomDefinition(
                axiom_id="clique_chromatic_lower_bound",
                name="Clique-Chromatic Lower Bound",
                description="The chromatic number is always bounded below by the clique number: chi(G) >= omega(G).",
                statement_latex=r"\chi(G) \ge \omega(G)",
                statement_lean="(G.chromaticNumber : ℝ) ≥ (G.cliqueNum : ℝ)",
                category="coloring",
                challenge_module="ComparatorChallenges.CliqueChromatic",
                solution_module="OAI.Combinatorics.Coloring.Main",
                theorem_name="chromatic_ge_clique",
                scope={"assumptions": []},
            ),
            aliases=["clique_chromatic", "chi_ge_omega", "clique_chromatic_bound"],
        )

        # 10. Independence Partition Lower Bound
        self._register(
            AxiomDefinition(
                axiom_id="independence_chromatic_lower_bound",
                name="Independence Partition Lower Bound",
                description="Each color class has size at most alpha(G), hence chi(G) >= n / alpha(G).",
                statement_latex=r"\chi(G) \ge \frac{n}{\alpha(G)}",
                statement_lean="(G.chromaticNumber : ℝ) ≥ (Fintype.card V : ℝ) / (G.indepNum : ℝ)",
                category="coloring",
                challenge_module="ComparatorChallenges.IndependenceChromatic",
                solution_module="OAI.Combinatorics.Coloring.Main",
                theorem_name="chromatic_ge_order_div_alpha",
                scope={"assumptions": ["order >= 1", "alpha >= 1"]},
            ),
            aliases=["independence_chromatic", "chi_ge_n_div_alpha", "independence_partition_bound"],
        )

        # 11. Wilf's Spectral Upper Bound
        self._register(
            AxiomDefinition(
                axiom_id="wilf_spectral_bound",
                name="Wilf's Spectral Bound",
                description="The chromatic number is bounded above by spectral radius: chi(G) <= lambda_1(G) + 1.",
                statement_latex=r"\chi(G) \le \lambda_1(G) + 1",
                statement_lean="(G.chromaticNumber : ℝ) ≤ G.spectralRadius + 1",
                category="spectral",
                challenge_module="ComparatorChallenges.WilfSpectral",
                solution_module="OAI.Combinatorics.Spectral.Main",
                theorem_name="wilf_chromatic_bound",
                scope={"assumptions": []},
            ),
            aliases=["wilf", "wilf_bound"],
        )

        # 12. Average Degree Formula / Degree-Order Bound
        self._register(
            AxiomDefinition(
                axiom_id="average_degree_handshaking",
                name="Average Degree Formula",
                description="Average degree is 2m / n: d_avg(G) = 2 |E(G)| / n.",
                statement_latex=r"\bar{d}(G) = \frac{2 |E(G)|}{n}",
                statement_lean="averageDegree G = 2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)",
                category="degree",
                challenge_module="ComparatorChallenges.AverageDegree",
                solution_module="OAI.Combinatorics.Degree.Main",
                theorem_name="average_degree_eq_two_m_div_n",
                scope={"assumptions": ["order >= 1"]},
            ),
            aliases=["average_degree", "avg_deg", "degree_order_bound"],
        )

        # 13. Cvetković Signless Laplacian Degree Bound
        self._register(
            AxiomDefinition(
                axiom_id="cvetkovic_signless_laplacian_bound",
                name="Cvetković Signless Laplacian Bound",
                description="The signless Laplacian spectral radius is bounded by twice the maximum degree: q_1(G) <= 2 * Delta(G).",
                statement_latex=r"q_1(G) \le 2 \Delta(G)",
                statement_lean="(G.signlessLaplacianRadius : ℝ) ≤ 2 * (G.maxDegree : ℝ)",
                category="spectral",
                challenge_module="ComparatorChallenges.SignlessLaplacian",
                solution_module="OAI.Combinatorics.Spectral.Main",
                theorem_name="signless_laplacian_le_two_max_degree",
                scope={"assumptions": []},
            ),
            aliases=["cvetkovic_signless_laplacian", "q1_le_2_delta", "q_spectral_radius_bound"],
        )

        # 14. Collatz-Sinogowitz Spectral Radius Bound
        self._register(
            AxiomDefinition(
                axiom_id="collatz_sinogowitz_bound",
                name="Collatz-Sinogowitz Spectral Bound",
                description="The adjacency spectral radius is bounded by maximum degree: lambda_1(G) <= Delta(G).",
                statement_latex=r"\lambda_1(G) \le \Delta(G)",
                statement_lean="(G.spectralRadius : ℝ) ≤ (G.maxDegree : ℝ)",
                category="spectral",
                challenge_module="ComparatorChallenges.CollatzSinogowitz",
                solution_module="OAI.Combinatorics.Spectral.Main",
                theorem_name="spectral_radius_le_max_degree",
                scope={"assumptions": []},
            ),
            aliases=["collatz_sinogowitz", "lambda1_le_delta"],
        )

        # 15. McClelland Graph Energy Upper Bound
        self._register(
            AxiomDefinition(
                axiom_id="mcclelland_energy_bound",
                name="McClelland Energy Bound",
                description="Graph energy is bounded by square root of twice size times order: E(G) <= sqrt(2 * m * n).",
                statement_latex=r"\mathcal{E}(G) \le \sqrt{2 m n}",
                statement_lean="(G.energy : ℝ) ≤ Real.sqrt (2 * (G.edgeFinset.card : ℝ) * (Fintype.card V : ℝ))",
                category="spectral",
                challenge_module="ComparatorChallenges.GraphEnergy",
                solution_module="OAI.Combinatorics.Spectral.Main",
                theorem_name="energy_le_sqrt_two_m_n",
                scope={"assumptions": []},
            ),
            aliases=["mcclelland", "mcclelland_bound", "energy_upper_bound"],
        )


    def list_axioms(self) -> List[str]:
        """Return sorted list of canonical axiom IDs."""
        return sorted(self._axioms.keys())

    def _resolve_id(self, axiom_id: str) -> str:
        clean = axiom_id.strip().lower().replace("-", "_")
        if clean in self._aliases:
            return self._aliases[clean]
        # Partial match fallback
        for alias, canon in self._aliases.items():
            if clean in alias or alias in clean:
                return canon
        raise KeyError(f"Axiom '{axiom_id}' not found in AxiomLibrary. Available: {self.list_axioms()}")

    def has_axiom(self, axiom_id: str) -> bool:
        """Check if axiom exists by ID or alias."""
        try:
            self._resolve_id(axiom_id)
            return True
        except KeyError:
            return False

    def get_definition(self, axiom_id: str) -> AxiomDefinition:
        """Retrieve AxiomDefinition by ID or alias."""
        canon = self._resolve_id(axiom_id)
        return self._axioms[canon]

    def get_axiom(self, axiom_id: str) -> Optional[ProofNode]:
        """Retrieve ProofNode instance for the requested axiom, or None if not found."""
        try:
            defn = self.get_definition(axiom_id)
            return defn.to_proof_node()
        except KeyError:
            return None

    def get_latex(self, axiom_id: str) -> str:
        """Get LaTeX formula for the requested axiom."""
        return self.get_definition(axiom_id).statement_latex

    def get_lean(self, axiom_id: str) -> str:
        """Get Lean 4 expression for the requested axiom."""
        return self.get_definition(axiom_id).statement_lean

    def get_lean_template(self, axiom_id: str) -> str:
        """Get full Lean 4 challenge file for the requested axiom."""
        return self.get_definition(axiom_id).to_lean_source()

    def get_comparator_json(self, axiom_id: str) -> Dict[str, Any]:
        """Get openai/math comparator challenge JSON for the requested axiom."""
        return self.get_definition(axiom_id).to_comparator_json()

    def search(self, query: str) -> List[ProofNode]:
        """Search axioms by keyword across name, description, and formula."""
        q = query.lower()
        results: List[ProofNode] = []
        for ax in self._axioms.values():
            if (
                q in ax.axiom_id.lower()
                or q in ax.name.lower()
                or q in ax.description.lower()
                or q in ax.statement_latex.lower()
                or q in ax.statement_lean.lower()
            ):
                results.append(ax.to_proof_node())
        return results

    def get_all_axioms(self) -> Dict[str, ProofNode]:
        """Return dictionary mapping all canonical IDs to ProofNodes."""
        return {aid: ax.to_proof_node() for aid, ax in self._axioms.items()}

    def __contains__(self, item: str) -> bool:
        return self.has_axiom(item)

    def __len__(self) -> int:
        return len(self._axioms)
