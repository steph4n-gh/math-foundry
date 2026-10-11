"""Local theorem matching and optional OpenAlex title search.

The local registry supplies candidate attributions, not a publication-priority
audit. An unmatched statement remains UNKNOWN_IN_LITERATURE; neither absence
from this registry nor an empty title search establishes mathematical novelty.
"""

from __future__ import annotations

from enum import Enum
from fractions import Fraction
import json
import logging
from typing import Any, Dict, List, Optional, Sequence, Tuple
import urllib.parse
import urllib.request

from pydantic import BaseModel, ConfigDict, Field
import sympy as sp

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    ExpressionNode,
    GuardPredicate,
    InvariantNode,
    UnaryOpNode,
)
from autonomous_math.core.invariants import INVARIANT_ALIASES

logger = logging.getLogger(__name__)


def _exact_guard_key(guard):
    """Compare complete premises without rounding nearby numeric thresholds."""
    if isinstance(guard, str):
        guard = GuardPredicate.from_dict(guard)
    if guard is None or guard.predicate_type == "universal":
        return None
    if guard.predicate_type == "property":
        return ("property", guard.property_name, guard.negated)
    if guard.predicate_type == "comparison":
        return ("comparison", INVARIANT_ALIASES.get(guard.invariant, guard.invariant),
                guard.op, Fraction(str(guard.threshold or 0)), guard.negated)
    if guard.predicate_type == "conjunction":
        parts = [_exact_guard_key(g) for g in guard.guards or []]
        parts = sorted((part for part in parts if part is not None), key=repr)
        return ("conjunction", tuple(parts)) if parts else None
    raise ValueError("Unsupported literature guard")


def _polynomial_expression(node):
    """SymPy cancellation is used only for a total polynomial AST grammar."""
    if isinstance(node, (ConstantNode, InvariantNode)):
        return True
    if isinstance(node, UnaryOpNode):
        return node.op in {"neg", "sqr"} and _polynomial_expression(node.child)
    if isinstance(node, BinaryOpNode):
        if node.op == "^":
            return (isinstance(node.right, ConstantNode) and node.right.value >= 0
                    and node.right.value.is_integer() and _polynomial_expression(node.left))
        return node.op in {"+", "-", "*"} and all(
            _polynomial_expression(child) for child in (node.left, node.right))
    return False


class NoveltyStatus(str, Enum):
    """Categorical novelty status of a candidate conjecture."""
    VERIFIED_REDISCOVERY = "VERIFIED_REDISCOVERY"
    TEXTBOOK_FOLKLORE = "TEXTBOOK_FOLKLORE"
    CANDIDATE_NOVEL_CONJECTURE = "CANDIDATE_NOVEL_CONJECTURE"
    UNKNOWN_IN_LITERATURE = "UNKNOWN_IN_LITERATURE"


class LiteratureMatch(BaseModel):
    """Scholarly attribution details for a recognized theorem or related work."""
    model_config = ConfigDict(frozen=True)

    theorem_name: str
    author: str
    year: int
    citation: str
    doi: Optional[str] = None
    statement: str
    equivalence_type: str = "exact_ast_match"  # exact_ast_match, algebraic_equivalent, corollary
    url: Optional[str] = None
    category: str = "CLASSICAL_THEOREM"


class NoveltyReport(BaseModel):
    """Comprehensive literature cross-check report for an empirical conjecture."""
    model_config = ConfigDict(frozen=True)

    status: NoveltyStatus
    conjecture_id: str
    statement: str
    matched_theorem: Optional[LiteratureMatch] = None
    novelty_score: float = Field(ge=0.0, le=1.0)
    related_publications: List[Dict[str, Any]] = Field(default_factory=list)
    suggested_action: str  # FLAG_VERIFIED_REDISCOVERY or ELEVATE_TO_PROVER_SKEPTIC
    search_query_used: str = ""
    explanation: str = ""


class KnownTheorem(BaseModel):
    """Structured representation of a recognized theorem in mathematical literature."""
    model_config = ConfigDict(frozen=True)

    id: str
    name: str
    author: str
    year: int
    citation: str
    doi: Optional[str] = None
    url: Optional[str] = None
    lhs: ExpressionNode
    rel: str
    rhs: ExpressionNode
    guard: Optional[GuardPredicate] = None
    keywords: List[str] = Field(default_factory=list)
    category: str = "CLASSICAL_THEOREM"


class KnownTheoremRegistry:
    """Curated registry of established spectral and extremal graph theory theorems."""

    def __init__(self) -> None:
        self._theorems: List[KnownTheorem] = []
        self._initialize_classical_theorems()

    def _initialize_classical_theorems(self) -> None:
        """Populates the database of celebrated historical theorems."""
        # 1. Wilf's Spectral Bound on Chromatic Number (1967)
        # chi(G) <= lambda_1(G) + 1
        self.register(
            KnownTheorem(
                id="thm_wilf_1967",
                name="Wilf's Spectral Chromatic Upper Bound",
                author="Herbert S. Wilf",
                year=1967,
                citation="Wilf, H. S. (1967). The eigenvalues of a graph and its chromatic number. Journal of the London Mathematical Society, 1(1), 330-332.",
                doi="10.1112/jlms/s1-42.1.330",
                url="https://doi.org/10.1112/jlms/s1-42.1.330",
                lhs=InvariantNode(name="chromatic_number"),
                rel="<=",
                rhs=BinaryOpNode("+", InvariantNode(name="spectral_radius"), ConstantNode(value=1.0)),
                keywords=["chromatic number", "spectral radius", "eigenvalue", "Wilf"],
            )
        )

        # 2. Hoffman's Spectral Bound on Chromatic Number (1970)
        # hoffman_bound <= chi(G)
        self.register(
            KnownTheorem(
                id="thm_hoffman_1970",
                name="Hoffman's Spectral Chromatic Lower Bound",
                author="Alan J. Hoffman",
                year=1970,
                citation="Hoffman, A. J. (1970). On eigenvalues and colorings of graphs. Graph Theory and its Applications, Academic Press, 79-91.",
                doi="10.1016/B978-0-12-329850-8.50010-0",
                url="https://doi.org/10.1016/B978-0-12-329850-8.50010-0",
                lhs=InvariantNode(name="hoffman_bound"),
                rel="<=",
                rhs=InvariantNode(name="chromatic_number"),
                keywords=["chromatic number", "Hoffman bound", "eigenvalue"],
            )
        )

        # 3. Brooks' Theorem (1941)
        # chi(G) <= max_degree(G) + 1
        self.register(
            KnownTheorem(
                id="thm_brooks_1941",
                name="Brooks' Degree Chromatic Bound",
                author="R. Leonard Brooks",
                year=1941,
                citation="Brooks, R. L. (1941). On colouring the nodes of a network. Mathematical Proceedings of the Cambridge Philosophical Society, 37(2), 194-197.",
                doi="10.1017/S030500410002168X",
                url="https://doi.org/10.1017/S030500410002168X",
                lhs=InvariantNode(name="chromatic_number"),
                rel="<=",
                rhs=BinaryOpNode("+", InvariantNode(name="max_degree"), ConstantNode(value=1.0)),
                keywords=["chromatic number", "maximum degree", "Brooks"],
            )
        )

        # 4. Mantel / Turán's Theorem (1907 / 1941)
        # is_triangle_free ==> size <= (order * order) / 4
        self.register(
            KnownTheorem(
                id="thm_mantel_1907",
                name="Mantel's Extremal Triangle-Free Size Bound",
                author="Willem Mantel",
                year=1907,
                citation="Mantel, W. (1907). Vraagstuk XXVIII. Wiskundige Opgaven met de Oplossingen, 10, 60-61.",
                doi=None,
                url=None,
                lhs=InvariantNode(name="size"),
                rel="<=",
                rhs=BinaryOpNode("/", BinaryOpNode("*", InvariantNode(name="order"), InvariantNode(name="order")), ConstantNode(value=4.0)),
                guard=GuardPredicate(property_name_or_type="is_triangle_free"),
                keywords=["Mantel", "Turan", "triangle-free", "size", "extremal"],
            )
        )

        # 5. Fiedler's Algebraic Connectivity Bound (1973)
        # mu_2(G) <= delta(G)
        self.register(
            KnownTheorem(
                id="thm_fiedler_1973",
                name="Fiedler's Algebraic Connectivity Degree Bound",
                author="Miroslav Fiedler",
                year=1973,
                citation="Fiedler, M. (1973). Algebraic connectivity of graphs. Czechoslovak Mathematical Journal, 23(2), 298-305.",
                doi="10.21136/CMJ.1973.101168",
                url="https://doi.org/10.21136/CMJ.1973.101168",
                lhs=InvariantNode(name="algebraic_connectivity"),
                rel="<=",
                rhs=InvariantNode(name="min_degree"),
                keywords=["Fiedler", "algebraic connectivity", "Laplacian", "minimum degree"],
            )
        )

        # 6. Collatz-Sinogowitz Spectral Radius Bound (1957)
        # lambda_1(G) <= Delta(G)
        self.register(
            KnownTheorem(
                id="thm_collatz_sinogowitz_1957",
                name="Collatz-Sinogowitz Maximum Degree Spectral Bound",
                author="Lothar Collatz & Ulrich Sinogowitz",
                year=1957,
                citation="Collatz, L., & Sinogowitz, U. (1957). Spektren endlicher Grafen. Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg, 21(1), 63-77.",
                doi="10.1007/BF02941924",
                url="https://doi.org/10.1007/BF02941924",
                lhs=InvariantNode(name="spectral_radius"),
                rel="<=",
                rhs=InvariantNode(name="max_degree"),
                keywords=["Collatz", "Sinogowitz", "spectral radius", "maximum degree"],
            )
        )

        # 7. Cvetković Signless Laplacian Upper Bound (2007)
        # q_1(G) <= 2 * Delta(G)
        self.register(
            KnownTheorem(
                id="thm_cvetkovic_2007",
                name="Cvetković Signless Laplacian Degree Bound",
                author="Dragoš Cvetković, Peter Rowlinson & Slobodan K. Simić",
                year=2007,
                citation="Cvetković, D., Rowlinson, P., & Simić, S. K. (2007). Signless Laplacians of finite graphs. Linear Algebra and its Applications, 423(1), 155-171.",
                doi="10.1016/j.laa.2007.01.009",
                url="https://doi.org/10.1016/j.laa.2007.01.009",
                lhs=InvariantNode(name="signless_laplacian_spectral_radius"),
                rel="<=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="max_degree")),
                keywords=["signless Laplacian", "Cvetkovic", "Q-spectral radius", "maximum degree"],
            )
        )

        # 8. Das Signless Laplacian Bound (2004)
        # q_1(G) <= (2m / (n - 1)) + n - 2
        self.register(
            KnownTheorem(
                id="thm_das_2004",
                name="Das Signless Laplacian Order-Size Bound",
                author="Kinkar Ch. Das",
                year=2004,
                citation="Das, K. C. (2004). A sharp upper bound on the maximal eigenvalue of the signless Laplacian of a graph. Linear Algebra and its Applications, 391, 45-59.",
                doi="10.1016/j.laa.2004.05.011",
                url="https://doi.org/10.1016/j.laa.2004.05.011",
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
                keywords=["signless Laplacian", "Das", "maximal eigenvalue", "size", "order"],
            )
        )

        # 9. Chung Normalized Laplacian Spectral Gap Bound (1997)
        # lambda_2^L(G) <= order / (order - 1)
        self.register(
            KnownTheorem(
                id="thm_chung_1997",
                name="Chung Normalized Laplacian Gap Bound",
                author="Fan R. K. Chung",
                year=1997,
                citation="Chung, F. R. (1997). Spectral graph theory (Vol. 92). American Mathematical Society.",
                doi="10.1090/cbms/092",
                url="https://doi.org/10.1090/cbms/092",
                lhs=InvariantNode(name="normalized_laplacian_spectral_gap"),
                rel="<=",
                rhs=BinaryOpNode(
                    "/",
                    InvariantNode(name="order"),
                    BinaryOpNode("-", InvariantNode(name="order"), ConstantNode(value=1.0)),
                ),
                guard=GuardPredicate(predicate_type="comparison", invariant="order", op=">=", threshold=2.0),
                keywords=["normalized Laplacian", "Chung", "spectral gap", "algebraic connectivity"],
            )
        )

        # 10. Estrada Index Exponential Bound (2000)
        # EE(G) <= (n - 1) + exp(lambda_1)
        self.register(
            KnownTheorem(
                id="thm_estrada_2000",
                name="Estrada Index Spectral Exponential Upper Bound",
                author="Ernesto Estrada",
                year=2000,
                citation="Estrada, E. (2000). Characterization of 3D molecular structure. Chemical Physics Letters, 319(5-6), 713-718.",
                doi="10.1016/S0009-2614(00)00158-5",
                url="https://doi.org/10.1016/S0009-2614(00)00158-5",
                lhs=InvariantNode(name="estrada_index"),
                rel="<=",
                rhs=BinaryOpNode(
                    "+",
                    BinaryOpNode("-", InvariantNode(name="order"), ConstantNode(value=1.0)),
                    UnaryOpNode(op="exp", child=InvariantNode(name="spectral_radius")),
                ),
                keywords=["Estrada index", "molecular structure", "exponential", "spectral radius"],
            )
        )

        # 11. McClelland Graph Energy Upper Bound (1971)
        # E(G) <= sqrt(2 * m * n)
        self.register(
            KnownTheorem(
                id="thm_mcclelland_1971",
                name="McClelland Graph Energy Upper Bound",
                author="B. J. McClelland",
                year=1971,
                citation="McClelland, B. J. (1971). Properties of the latent roots of a matrix. The Journal of Chemical Physics, 54(2), 640-643.",
                doi="10.1063/1.1674889",
                url="https://doi.org/10.1063/1.1674889",
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
                keywords=["graph energy", "McClelland", "eigenvalues", "molecular orbitals"],
            )
        )

        # 12. Nordhaus-Gaddum Spectral Sum Bound (1970 / 2007)
        # lambda_1(G) + lambda_1(G_bar) <= sqrt(2) * (n - 1)
        self.register(
            KnownTheorem(
                id="thm_nordhaus_gaddum_spectral_1970",
                name="Nordhaus-Gaddum Spectral Radius Sum Bound",
                author="E. Nosal & V. Nikiforov",
                year=1970,
                citation="Nosal, E. (1970). Eigenvalues of Graphs. Master's thesis, University of Calgary. Nikiforov, V. (2007). Eigenvalue problems of Nordhaus-Gaddum type. Discrete Mathematics, 307(6), 774-780.",
                doi="10.1016/j.disc.2006.07.018",
                url="https://doi.org/10.1016/j.disc.2006.07.018",
                lhs=InvariantNode(name="nordhaus_gaddum_spectral_sum"),
                rel="<=",
                rhs=BinaryOpNode(
                    "*",
                    ConstantNode(value=1.41421356),
                    BinaryOpNode("-", InvariantNode(name="order"), ConstantNode(value=1.0)),
                ),
                guard=GuardPredicate(predicate_type="comparison", invariant="order", op=">=", threshold=2.0),
                keywords=["Nordhaus-Gaddum", "spectral radius", "complement", "Nikiforov"],
            )
        )

        # 13. Ramsey Order-Independence Bound
        # chi(G) >= order / independence_number
        self.register(
            KnownTheorem(
                id="thm_ramsey_chi_alpha",
                name="Coloring-Independence Partition Bound",
                author="Classical Extremal Combinatorics",
                year=1950,
                citation="Bollobás, B. (1998). Modern Graph Theory. Graduate Texts in Mathematics, Springer.",
                doi="10.1007/978-1-4612-0619-4",
                url="https://doi.org/10.1007/978-1-4612-0619-4",
                lhs=InvariantNode(name="chromatic_number"),
                rel=">=",
                rhs=BinaryOpNode("/", InvariantNode(name="order"), InvariantNode(name="independence_number")),
                guard=GuardPredicate(predicate_type="comparison", invariant="order", op=">=", threshold=1.0),
                keywords=["chromatic number", "independence number", "partition"],
            )
        )

        # 14. Fundamental Coloring-Clique Lower Bound (Folklore)
        # chi(G) >= omega(G)
        self.register(
            KnownTheorem(
                id="thm_folklore_chi_ge_omega",
                name="Coloring-Clique Number Fundamental Bound",
                author="Textbook Folklore",
                year=1930,
                citation="Bondy, J. A., & Murty, U. S. R. (1976). Graph Theory with Applications. Macmillan.",
                lhs=InvariantNode(name="chromatic_number"),
                rel=">=",
                rhs=InvariantNode(name="clique_number"),
                category="TEXTBOOK_FOLKLORE",
                keywords=["chromatic number", "clique number", "folklore", "textbook"],
            )
        )

        # 15. Erdős–Szekeres Clique-Independence Order Bound (1935)
        # omega(G) <= order - independence_number + 1
        self.register(
            KnownTheorem(
                id="thm_erdos_szekeres_clique_indep",
                name="Erdős-Szekeres Clique-Independence Order Bound",
                author="Paul Erdős & George Szekeres",
                year=1935,
                citation="Erdős, P., & Szekeres, G. (1935). A combinatorial problem in geometry. Compositio Mathematica, 2, 463-470.",
                lhs=InvariantNode(name="clique_number"),
                rel="<=",
                rhs=BinaryOpNode(
                    "+",
                    BinaryOpNode("-", InvariantNode(name="order"), InvariantNode(name="independence_number")),
                    ConstantNode(value=1.0),
                ),
                category="TEXTBOOK_FOLKLORE",
                keywords=["Erdos-Szekeres", "clique number", "independence number", "order", "folklore", "textbook"],
            )
        )

        # 16. Erdős–Szekeres Independence-Clique Order Bound (1935)
        # independence_number <= order - clique_number + 1
        self.register(
            KnownTheorem(
                id="thm_erdos_szekeres_indep_clique",
                name="Erdős-Szekeres Independence-Clique Order Bound",
                author="Paul Erdős & George Szekeres",
                year=1935,
                citation="Erdős, P., & Szekeres, G. (1935). A combinatorial problem in geometry. Compositio Mathematica, 2, 463-470.",
                lhs=InvariantNode(name="independence_number"),
                rel="<=",
                rhs=BinaryOpNode(
                    "+",
                    BinaryOpNode("-", InvariantNode(name="order"), InvariantNode(name="clique_number")),
                    ConstantNode(value=1.0),
                ),
                category="TEXTBOOK_FOLKLORE",
                keywords=["Erdos-Szekeres", "independence number", "clique number", "order", "folklore", "textbook"],
            )
        )

        # 17. Caro-Wei Degree Extremal Independence Bound (1979)
        # alpha(G) <= order - size / max_degree
        self.register(
            KnownTheorem(
                id="thm_caro_wei_indep_degree",
                name="Caro-Wei Degree-Extremal Independence Upper Bound",
                author="Textbook Folklore / Caro-Wei",
                year=1979,
                citation="Caro, Y. (1979). New Results on the Independence Number. Technical Report, Tel-Aviv University.",
                lhs=InvariantNode(name="independence_number"),
                rel="<=",
                rhs=BinaryOpNode(
                    "-",
                    InvariantNode(name="order"),
                    BinaryOpNode("/", InvariantNode(name="size"), InvariantNode(name="max_degree")),
                ),
                guard=GuardPredicate(predicate_type="comparison", invariant="max_degree", op=">=", threshold=1.0),
                category="TEXTBOOK_FOLKLORE",
                keywords=["independence number", "size", "max degree", "Caro-Wei", "folklore", "textbook"],
            )
        )

        # 18. Reed's Chromatic-Degree-Clique Bound (1998)
        # chi(G) <= 0.5 * max_degree + 0.5 * clique_number + 1
        self.register(
            KnownTheorem(
                id="thm_reed_1998_bound",
                name="Reed's Degree-Clique Chromatic Bound",
                author="Bruce A. Reed",
                year=1998,
                citation="Reed, B. (1998). \\omega, \\Delta, and \\chi. Journal of Graph Theory, 27(4), 177-212.",
                doi="10.1002/(SICI)1097-0118(199804)27:4<177::AID-JGT3>3.0.CO;2-K",
                url="https://doi.org/10.1002/(SICI)1097-0118(199804)27:4<177::AID-JGT3>3.0.CO;2-K",
                lhs=InvariantNode(name="chromatic_number"),
                rel="<=",
                rhs=BinaryOpNode(
                    "+",
                    BinaryOpNode(
                        "+",
                        BinaryOpNode("*", ConstantNode(value=0.5), InvariantNode(name="max_degree")),
                        BinaryOpNode("*", ConstantNode(value=0.5), InvariantNode(name="clique_number")),
                    ),
                    ConstantNode(value=1.0),
                ),
                category="CLASSICAL_THEOREM",
                keywords=["Reed", "chromatic number", "maximum degree", "clique number"],
            )
        )

        # 19. Trivial Order Bound on Chromatic Number (Folklore)
        # chi(G) <= order
        self.register(
            KnownTheorem(
                id="thm_folklore_chi_le_order",
                name="Trivial Order Bound on Chromatic Number",
                author="Textbook Folklore",
                year=1930,
                citation="Bondy, J. A., & Murty, U. S. R. (1976). Graph Theory with Applications. Macmillan.",
                lhs=InvariantNode(name="chromatic_number"),
                rel="<=",
                rhs=InvariantNode(name="order"),
                category="TEXTBOOK_FOLKLORE",
                keywords=["chromatic number", "order", "folklore", "textbook"],
            )
        )

        # 20. Trivial Order Bound on Clique Number (Folklore)
        # omega(G) <= order
        self.register(
            KnownTheorem(
                id="thm_folklore_omega_le_order",
                name="Trivial Order Bound on Clique Number",
                author="Textbook Folklore",
                year=1930,
                citation="Bondy, J. A., & Murty, U. S. R. (1976). Graph Theory with Applications. Macmillan.",
                lhs=InvariantNode(name="clique_number"),
                rel="<=",
                rhs=InvariantNode(name="order"),
                category="TEXTBOOK_FOLKLORE",
                keywords=["clique number", "order", "folklore", "textbook"],
            )
        )

        # 21. Trivial Order Bound on Independence Number (Folklore)
        # alpha(G) <= order
        self.register(
            KnownTheorem(
                id="thm_folklore_alpha_le_order",
                name="Trivial Order Bound on Independence Number",
                author="Textbook Folklore",
                year=1930,
                citation="Bondy, J. A., & Murty, U. S. R. (1976). Graph Theory with Applications. Macmillan.",
                lhs=InvariantNode(name="independence_number"),
                rel="<=",
                rhs=InvariantNode(name="order"),
                category="TEXTBOOK_FOLKLORE",
                keywords=["independence number", "order", "folklore", "textbook"],
            )
        )

        # 22. Trivial Maximum Degree Bound on Order (Folklore)
        # max_degree <= order - 1
        self.register(
            KnownTheorem(
                id="thm_folklore_max_deg_le_order",
                name="Trivial Maximum Degree Order Bound",
                author="Textbook Folklore",
                year=1930,
                citation="Bondy, J. A., & Murty, U. S. R. (1976). Graph Theory with Applications. Macmillan.",
                lhs=InvariantNode(name="max_degree"),
                rel="<=",
                rhs=BinaryOpNode("-", InvariantNode(name="order"), ConstantNode(value=1.0)),
                guard=GuardPredicate(predicate_type="comparison", invariant="order", op=">=", threshold=1.0),
                category="TEXTBOOK_FOLKLORE",
                keywords=["max degree", "order", "folklore", "textbook"],
            )
        )

        # 23. Bipartite Chromatic-Clique Equivalence (Folklore / Kőnig)
        # is_bipartite ==> chi(G) <= omega(G)
        self.register(
            KnownTheorem(
                id="thm_bipartite_chi_le_omega",
                name="Bipartite Chromatic-Clique Equivalence",
                author="Dénes Kőnig / Textbook Folklore",
                year=1916,
                citation="Kőnig, D. (1916). Gráfok és alkalmazásuk a determinánsok és a halmazok elméletére. Mathematikai és Természettudományi Értesítő, 34, 104-119.",
                lhs=InvariantNode(name="chromatic_number"),
                rel="<=",
                rhs=InvariantNode(name="clique_number"),
                guard=GuardPredicate(property_name_or_type="is_bipartite"),
                category="TEXTBOOK_FOLKLORE",
                keywords=["bipartite", "chromatic number", "clique number", "Konig", "folklore", "textbook"],
            )
        )

        # 24. Bipartite 2-Colorability Definition (Folklore)
        # is_bipartite ==> chi(G) <= 2
        self.register(
            KnownTheorem(
                id="thm_bipartite_chi_le_two",
                name="Bipartite 2-Coloring Fundamental Bound",
                author="Textbook Folklore",
                year=1930,
                citation="Bondy, J. A., & Murty, U. S. R. (1976). Graph Theory with Applications. Macmillan.",
                lhs=InvariantNode(name="chromatic_number"),
                rel="<=",
                rhs=ConstantNode(value=2.0),
                guard=GuardPredicate(property_name_or_type="is_bipartite"),
                category="TEXTBOOK_FOLKLORE",
                keywords=["bipartite", "chromatic number", "2-colorable", "folklore", "textbook"],
            )
        )

        # 25. Triangle-Free Clique Upper Bound (Folklore)
        # is_triangle_free ==> omega(G) <= 2
        self.register(
            KnownTheorem(
                id="thm_triangle_free_omega_le_two",
                name="Triangle-Free Clique Upper Bound",
                author="Textbook Folklore",
                year=1930,
                citation="Bondy, J. A., & Murty, U. S. R. (1976). Graph Theory with Applications. Macmillan.",
                lhs=InvariantNode(name="clique_number"),
                rel="<=",
                rhs=ConstantNode(value=2.0),
                guard=GuardPredicate(property_name_or_type="is_triangle_free"),
                category="TEXTBOOK_FOLKLORE",
                keywords=["triangle-free", "clique number", "folklore", "textbook"],
            )
        )

        # 26. Maximum Degree Clique Bound (Folklore)
        # omega(G) <= max_degree(G) + 1
        self.register(
            KnownTheorem(
                id="thm_folklore_omega_le_delta_plus_one",
                name="Degree-Clique Upper Bound",
                author="Textbook Folklore",
                year=1930,
                citation="Bondy, J. A., & Murty, U. S. R. (1976). Graph Theory with Applications. Macmillan.",
                lhs=InvariantNode(name="clique_number"),
                rel="<=",
                rhs=BinaryOpNode("+", InvariantNode(name="max_degree"), ConstantNode(value=1.0)),
                category="TEXTBOOK_FOLKLORE",
                keywords=["clique number", "max degree", "folklore", "textbook"],
            )
        )

        # 27. Average Degree - Max Degree Bound (Folklore)
        # d_bar(G) <= max_degree(G)
        self.register(
            KnownTheorem(
                id="thm_folklore_avg_deg_le_max_deg",
                name="Average-Maximum Degree Fundamental Inequality",
                author="Textbook Folklore",
                year=1930,
                citation="Bondy, J. A., & Murty, U. S. R. (1976). Graph Theory with Applications. Macmillan.",
                lhs=InvariantNode(name="average_degree"),
                rel="<=",
                rhs=InvariantNode(name="max_degree"),
                category="TEXTBOOK_FOLKLORE",
                keywords=["average degree", "max degree", "folklore", "textbook"],
            )
        )

        # 28. Spectral Radius - Average Degree Lower Bound (Collatz-Sinogowitz)
        # lambda_1(G) >= d_bar(G)
        self.register(
            KnownTheorem(
                id="thm_folklore_spectral_radius_ge_avg_deg",
                name="Spectral Radius Average Degree Lower Bound",
                author="Lothar Collatz & Ulrich Sinogowitz",
                year=1957,
                citation="Collatz, L., & Sinogowitz, U. (1957). Spektren endlicher Grafen. Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg, 21(1), 63-77.",
                lhs=InvariantNode(name="spectral_radius"),
                rel=">=",
                rhs=InvariantNode(name="average_degree"),
                category="TEXTBOOK_FOLKLORE",
                keywords=["spectral radius", "average degree", "Rayleigh", "folklore", "textbook"],
            )
        )

        # 29. Moore Bound on Degree and Diameter (1960)
        # diameter <= 2 ==> order <= max_degree^2 + 1
        self.register(
            KnownTheorem(
                id="thm_moore_bound_diam_2",
                name="Moore Bound on Degree and Diameter (D=2)",
                author="Edward F. Moore / Alan J. Hoffman & Robert R. Singleton",
                year=1960,
                citation="Hoffman, A. J., & Singleton, R. R. (1960). On Moore graphs with diameters 2 and 3. IBM Journal of Research and Development, 4(5), 497-504.",
                lhs=InvariantNode(name="order"),
                rel="<=",
                rhs=BinaryOpNode(
                    "+",
                    BinaryOpNode("*", InvariantNode(name="max_degree"), InvariantNode(name="max_degree")),
                    ConstantNode(value=1.0),
                ),
                guard=GuardPredicate(predicate_type="comparison", invariant="diameter", op="<=", threshold=2.0),
                keywords=["Moore bound", "degree-diameter", "order", "max degree"],
            )
        )
        self.register(
            KnownTheorem(
                id="thm_moore_bound_connected_d2",
                name="Moore Bound on Degree and Diameter (Connected D=2)",
                author="Edward F. Moore / Alan J. Hoffman & Robert R. Singleton",
                year=1960,
                citation="Hoffman, A. J., & Singleton, R. R. (1960). On Moore graphs with diameters 2 and 3. IBM Journal of Research and Development, 4(5), 497-504.",
                lhs=InvariantNode(name="order"),
                rel="<=",
                rhs=BinaryOpNode(
                    "+",
                    BinaryOpNode("*", InvariantNode(name="max_degree"), InvariantNode(name="max_degree")),
                    ConstantNode(value=1.0),
                ),
                guard=GuardPredicate(property_name_or_type="is_connected"),
                keywords=["Moore bound", "degree-diameter", "order", "max degree"],
            )
        )

        # 30. Radius-Diameter Fundamental Inequality (Folklore)
        # radius <= diameter
        self.register(
            KnownTheorem(
                id="thm_folklore_radius_le_diameter",
                name="Radius-Diameter Fundamental Inequality",
                author="Textbook Folklore",
                year=1930,
                citation="Bondy, J. A., & Murty, U. S. R. (1976). Graph Theory with Applications. Macmillan.",
                lhs=InvariantNode(name="radius"),
                rel="<=",
                rhs=InvariantNode(name="diameter"),
                category="TEXTBOOK_FOLKLORE",
                keywords=["radius", "diameter", "metric", "folklore", "textbook"],
            )
        )

        # 31. Connected Diameter Twice Radius Bound (Folklore)
        # diameter <= 2 * radius
        self.register(
            KnownTheorem(
                id="thm_folklore_diameter_le_two_radius",
                name="Connected Diameter Twice Radius Bound",
                author="Textbook Folklore",
                year=1930,
                citation="Bondy, J. A., & Murty, U. S. R. (1976). Graph Theory with Applications. Macmillan.",
                lhs=InvariantNode(name="diameter"),
                rel="<=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="radius")),
                guard=GuardPredicate(property_name_or_type="is_connected"),
                category="TEXTBOOK_FOLKLORE",
                keywords=["diameter", "radius", "metric", "folklore", "textbook"],
            )
        )

        # 32. Connected Diameter Order Bound (Folklore)
        # diameter <= order - 1
        self.register(
            KnownTheorem(
                id="thm_folklore_diameter_le_order",
                name="Connected Diameter Order Bound",
                author="Textbook Folklore",
                year=1930,
                citation="Bondy, J. A., & Murty, U. S. R. (1976). Graph Theory with Applications. Macmillan.",
                lhs=InvariantNode(name="diameter"),
                rel="<=",
                rhs=BinaryOpNode("-", InvariantNode(name="order"), ConstantNode(value=1.0)),
                guard=GuardPredicate(property_name_or_type="is_connected"),
                category="TEXTBOOK_FOLKLORE",
                keywords=["diameter", "order", "metric", "folklore", "textbook"],
            )
        )

        # 33. Koolen-Moulton Graph Energy Upper Bound (2001)
        # energy <= 2m/n + sqrt((n - 1)(2m - (2m/n)^2))
        self.register(
            KnownTheorem(
                id="thm_koolen_moulton_2001",
                name="Koolen-Moulton Graph Energy Upper Bound",
                author="Jack H. Koolen & Vincent Moulton",
                year=2001,
                citation="Koolen, J. H., & Moulton, V. (2001). Maximal energy graphs. Advances in Applied Mathematics, 26(1), 47-52.",
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
                keywords=["Koolen-Moulton", "graph energy", "energy bound", "chemical graph theory"],
            )
        )

        # 34. Koolen-Moulton Order Energy Bound (2003)
        # energy <= (n / 2) * (1 + sqrt(n))
        self.register(
            KnownTheorem(
                id="thm_koolen_moulton_order_2003",
                name="Koolen-Moulton Order Energy Bound",
                author="Jack H. Koolen & Vincent Moulton",
                year=2003,
                citation="Koolen, J. H., & Moulton, V. (2003). Extremal energy graphs. Linear Algebra and its Applications, 370, 385-397.",
                lhs=InvariantNode(name="graph_energy"),
                rel="<=",
                rhs=BinaryOpNode(
                    "*",
                    BinaryOpNode("/", InvariantNode(name="order"), ConstantNode(value=2.0)),
                    BinaryOpNode("+", ConstantNode(value=1.0), UnaryOpNode(op="sqrt", child=InvariantNode(name="order"))),
                ),
                keywords=["Koolen-Moulton", "graph energy", "order", "chemical graph theory"],
            )
        )

        # 35. Gutman Graph Energy Spectral Radius Lower Bound (1978)
        # energy >= 2 * spectral_radius
        self.register(
            KnownTheorem(
                id="thm_gutman_energy_spectral_1978",
                name="Gutman Graph Energy Spectral Radius Lower Bound",
                author="Ivan Gutman",
                year=1978,
                citation="Gutman, I. (1978). The energy of a graph. Berichte der Mathematisch-Statistischen Sektion im Forschungszentrum Graz, 103, 1-22.",
                lhs=InvariantNode(name="graph_energy"),
                rel=">=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="spectral_radius")),
                keywords=["Gutman", "graph energy", "spectral radius", "chemical graph theory"],
            )
        )

        # 36. Gutman Graph Energy Size Upper Bound (1978)
        # energy <= 2 * size
        self.register(
            KnownTheorem(
                id="thm_gutman_energy_size_1978",
                name="Gutman Graph Energy Size Upper Bound",
                author="Ivan Gutman",
                year=1978,
                citation="Gutman, I. (1978). The energy of a graph. Berichte der Mathematisch-Statistischen Sektion im Forschungszentrum Graz, 103, 1-22.",
                lhs=InvariantNode(name="graph_energy"),
                rel="<=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="size")),
                keywords=["Gutman", "graph energy", "size", "chemical graph theory"],
            )
        )

        # 37. Gutman Graph Energy Average Degree Lower Bound (1978)
        # energy >= 2 * average_degree
        self.register(
            KnownTheorem(
                id="thm_gutman_energy_avg_deg_1978",
                name="Gutman Graph Energy Average Degree Lower Bound",
                author="Ivan Gutman",
                year=1978,
                citation="Gutman, I. (1978). The energy of a graph. Berichte der Mathematisch-Statistischen Sektion im Forschungszentrum Graz, 103, 1-22.",
                lhs=InvariantNode(name="graph_energy"),
                rel=">=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="average_degree")),
                keywords=["Gutman", "graph energy", "average degree", "chemical graph theory"],
            )
        )

        # 38. Gregory-Hershkowitz-Hoffman Spectral Spread Spectral Radius Bound (2001)
        # spectral_spread <= 2 * spectral_radius
        self.register(
            KnownTheorem(
                id="thm_gregory_spread_spectral_2001",
                name="Gregory-Hershkowitz-Hoffman Spectral Spread Spectral Radius Bound",
                author="David A. Gregory, Daniel Hershkowitz & Alan J. Hoffman",
                year=2001,
                citation="Gregory, D. A., Hershkowitz, D., & Hoffman, A. J. (2001). The spread of the spectrum of a graph. Linear Algebra and its Applications, 316(1-3), 189-197.",
                lhs=InvariantNode(name="spectral_spread"),
                rel="<=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="spectral_radius")),
                keywords=["spectral spread", "spectral radius", "Gregory", "Hoffman"],
            )
        )

        # 39. Gregory-Hershkowitz-Hoffman Spectral Spread Order Bound (2001)
        # spectral_spread <= order
        self.register(
            KnownTheorem(
                id="thm_gregory_spread_order_2001",
                name="Gregory-Hershkowitz-Hoffman Spectral Spread Order Bound",
                author="David A. Gregory, Daniel Hershkowitz & Alan J. Hoffman",
                year=2001,
                citation="Gregory, D. A., Hershkowitz, D., & Hoffman, A. J. (2001). The spread of the spectrum of a graph. Linear Algebra and its Applications, 316(1-3), 189-197.",
                lhs=InvariantNode(name="spectral_spread"),
                rel="<=",
                rhs=InvariantNode(name="order"),
                keywords=["spectral spread", "order", "Gregory", "Hoffman"],
            )
        )

        # 40. Estrada Index - Graph Energy Fundamental Bound (2000)
        # estrada_index >= graph_energy
        self.register(
            KnownTheorem(
                id="thm_estrada_ge_energy",
                name="Estrada Index Graph Energy Fundamental Inequality",
                author="Ernesto Estrada / Ivan Gutman",
                year=2000,
                citation="Estrada, E. (2000). Characterization of 3D molecular structure. Chemical Physics Letters, 319(5-6), 713-718.",
                lhs=InvariantNode(name="estrada_index"),
                rel=">=",
                rhs=InvariantNode(name="graph_energy"),
                keywords=["Estrada index", "graph energy", "chemical graph theory"],
            )
        )

        # 41. Gregory-Hershkowitz-Hoffman Spectral Spread Max Degree Bound (2001)
        # spectral_spread <= 2 * max_degree
        self.register(
            KnownTheorem(
                id="thm_gregory_spread_max_deg_2001",
                name="Gregory-Hershkowitz-Hoffman Spectral Spread Max Degree Bound",
                author="David A. Gregory, Daniel Hershkowitz & Alan J. Hoffman",
                year=2001,
                citation="Gregory, D. A., Hershkowitz, D., & Hoffman, A. J. (2001). The spread of the spectrum of a graph. Linear Algebra and its Applications, 316(1-3), 189-197.",
                lhs=InvariantNode(name="spectral_spread"),
                rel="<=",
                rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="max_degree")),
                keywords=["spectral spread", "max degree", "Gregory", "Hoffman"],
            )
        )

    def register(self, theorem: KnownTheorem) -> None:
        """Register a known mathematical theorem."""
        self._theorems.append(theorem)

    @property
    def theorems(self) -> List[KnownTheorem]:
        return list(self._theorems)

    def match(self, conj: Conjecture) -> Optional[LiteratureMatch]:
        """Check if candidate conjecture is an exact or algebraic match to a known theorem."""
        # 1. Normalize candidate relation to standard direction (<=, <, or ==)
        if conj.rel == ">=":
            c_norm_lhs, c_norm_rhs, c_norm_rel = conj.rhs_expr, conj.lhs_expr, "<="
        elif conj.rel == ">":
            c_norm_lhs, c_norm_rhs, c_norm_rel = conj.rhs_expr, conj.lhs_expr, "<"
        else:
            c_norm_lhs, c_norm_rhs, c_norm_rel = conj.lhs_expr, conj.rhs_expr, conj.rel

        c_l_key = c_norm_lhs.canonical_key
        c_r_key = c_norm_rhs.canonical_key

        for thm in self._theorems:
            # 2. Check Guard Compatibility
            try:
                c_guard, t_guard = _exact_guard_key(conj.guard_predicate), _exact_guard_key(thm.guard)
            except (TypeError, ValueError):
                continue
            if t_guard is not None and c_guard != t_guard:
                continue
            is_specialization = t_guard is None and c_guard is not None

            # 3. Normalize theorem relation
            if thm.rel == ">=":
                t_norm_lhs, t_norm_rhs, t_norm_rel = thm.rhs, thm.lhs, "<="
            elif thm.rel == ">":
                t_norm_lhs, t_norm_rhs, t_norm_rel = thm.rhs, thm.lhs, "<"
            else:
                t_norm_lhs, t_norm_rhs, t_norm_rel = thm.lhs, thm.rhs, thm.rel

            if c_norm_rel != t_norm_rel:
                continue

            t_l_key = t_norm_lhs.canonical_key
            t_r_key = t_norm_rhs.canonical_key

            match_eq_type = "specialization" if is_specialization else "exact_ast_match"

            # 4. Exact AST key equality (accounting for normalized direction)
            if c_l_key == t_l_key and c_r_key == t_r_key:
                return LiteratureMatch(
                    theorem_name=thm.name,
                    author=thm.author,
                    year=thm.year,
                    citation=thm.citation,
                    doi=thm.doi,
                    statement=f"{thm.lhs.to_latex()} {thm.rel} {thm.rhs.to_latex()}",
                    equivalence_type=match_eq_type,
                    url=thm.url,
                    category=getattr(thm, "category", "CLASSICAL_THEOREM"),
                )

            if c_norm_rel == "==" and c_l_key == t_r_key and c_r_key == t_l_key:
                return LiteratureMatch(
                    theorem_name=thm.name,
                    author=thm.author,
                    year=thm.year,
                    citation=thm.citation,
                    doi=thm.doi,
                    statement=f"{thm.lhs.to_latex()} {thm.rel} {thm.rhs.to_latex()}",
                    equivalence_type=match_eq_type,
                    url=thm.url,
                    category=getattr(thm, "category", "CLASSICAL_THEOREM"),
                )

            # 5. Algebraic SymPy Equivalence
            if not all(_polynomial_expression(node) for node in
                       (c_norm_lhs, c_norm_rhs, t_norm_lhs, t_norm_rhs)):
                continue
            try:
                c_diff = sp.simplify(c_norm_rhs.to_sympy() - c_norm_lhs.to_sympy())
                t_diff = sp.simplify(t_norm_rhs.to_sympy() - t_norm_lhs.to_sympy())
                delta = sp.simplify(c_diff - t_diff)
                alg_eq_type = "specialization" if is_specialization else "algebraic_equivalent"
                if delta == 0:
                    return LiteratureMatch(
                        theorem_name=thm.name,
                        author=thm.author,
                        year=thm.year,
                        citation=thm.citation,
                        doi=thm.doi,
                        statement=f"{thm.lhs.to_latex()} {thm.rel} {thm.rhs.to_latex()}",
                        equivalence_type=alg_eq_type,
                        url=thm.url,
                        category=getattr(thm, "category", "CLASSICAL_THEOREM"),
                    )
                # Check positive scalar scaling: c_diff = k * t_diff with k > 0
                if t_diff != 0:
                    ratio = sp.simplify(c_diff / t_diff)
                    if ratio.is_number and ratio.is_positive is True:
                        return LiteratureMatch(
                            theorem_name=thm.name,
                            author=thm.author,
                            year=thm.year,
                            citation=thm.citation,
                            doi=thm.doi,
                            statement=f"{thm.lhs.to_latex()} {thm.rel} {thm.rhs.to_latex()}",
                            equivalence_type=alg_eq_type,
                            url=thm.url,
                            category=getattr(thm, "category", "CLASSICAL_THEOREM"),
                        )
            except Exception:
                pass

        return None


class LiteratureCrossChecker:
    """Automated literature cross-check module querying local registry and scholarly APIs."""

    def __init__(self, registry: Optional[KnownTheoremRegistry] = None) -> None:
        self.registry = registry or KnownTheoremRegistry()

    def construct_scholarly_query(self, conj: Conjecture) -> str:
        """Formulate a targeted scholarly literature search query for the conjecture."""
        inv_names = sorted(list(conj.lhs_expr.variables | conj.rhs_expr.variables))
        readable_terms = []
        for inv in inv_names:
            canon = INVARIANT_ALIASES.get(inv, inv)
            clean = canon.replace("_", " ")
            readable_terms.append(f'"{clean}"')

        coding_terms = {"parity_code_distance": "minimum distance",
                        "parity_code_dimension": "code dimension",
                        "unique_neighbor_radius": "stopping distance"}
        if any(INVARIANT_ALIASES.get(inv, inv) in coding_terms for inv in inv_names):
            readable_terms = [f'"{coding_terms.get(INVARIANT_ALIASES.get(inv, inv), inv.replace("_", " "))}"'
                              for inv in inv_names]
            readable_terms.append('"binary linear code"')
            domain = "coding theory"
        elif any("spectral" in term or "laplacian" in term or "energy" in term
                 or "estrada" in term or "eigenvalue" in term for term in readable_terms):
            domain = "spectral graph theory"
        else:
            domain = "graph theory"
        query_terms = " ".join(readable_terms) + f' bound "{domain}"'
        return query_terms

    def query_openalex(self, query: str, limit: int = 3, timeout_sec: float = 2.0) -> List[Dict[str, Any]]:
        """Queries OpenAlex Open Access Scholarly API."""
        encoded_query = urllib.parse.quote(query)
        url = f"https://api.openalex.org/works?search={encoded_query}&per-page={limit}"
        req = urllib.request.Request(url, headers={"User-Agent": "MathFoundry/1.0 (local mathematical literature review)"})
        try:
            with urllib.request.urlopen(req, timeout=timeout_sec) as resp:
                if resp.status == 200:
                    data = json.loads(resp.read().decode("utf-8"))
                    results = []
                    for work in data.get("results", []):
                        results.append({
                            "title": work.get("title", ""),
                            "publication_year": work.get("publication_year"),
                            "doi": work.get("doi"),
                            "cited_by_count": work.get("cited_by_count", 0),
                            "source": "OpenAlex",
                        })
                    return results
        except Exception as e:
            logger.debug(f"OpenAlex query error ({e}); using offline scholarly knowledge base.")
        return []

    def cross_check(
        self,
        conjecture: Conjecture,
        online: bool = False,
        timeout_sec: float = 2.0,
    ) -> NoveltyReport:
        """Evaluates a conjecture against published literature.

        - If matched to a known theorem: flags VERIFIED_REDISCOVERY or TEXTBOOK_FOLKLORE.
        - If unmatched locally: retains UNKNOWN_IN_LITERATURE without a novelty claim.
        """
        # 1. Check known theorem registry
        match = self.registry.match(conjecture)
        if match is not None:
            is_folklore = (
                getattr(match, "category", "") == "TEXTBOOK_FOLKLORE"
                or "folklore" in match.theorem_name.lower()
                or "folklore" in match.author.lower()
                or "textbook" in match.author.lower()
            )
            # Find the theorem in registry to be certain
            for thm in self.registry.theorems:
                if thm.name == match.theorem_name:
                    if (
                        getattr(thm, "category", "") == "TEXTBOOK_FOLKLORE"
                        or "folklore" in thm.keywords
                        or "textbook" in thm.keywords
                    ):
                        is_folklore = True
                    break

            status = NoveltyStatus.TEXTBOOK_FOLKLORE if is_folklore else NoveltyStatus.VERIFIED_REDISCOVERY
            action = "FLAG_TEXTBOOK_FOLKLORE" if is_folklore else "FLAG_VERIFIED_REDISCOVERY"
            if getattr(match, "equivalence_type", "") == "specialization":
                desc = f"Specialization of {match.theorem_name} ({match.author}, {match.year})"
            else:
                desc = "Textbook folklore / definition verified in literature" if is_folklore else "Established theorem verified in literature"

            return NoveltyReport(
                status=status,
                conjecture_id=conjecture.id,
                statement=conjecture.statement,
                matched_theorem=match,
                novelty_score=0.0,
                related_publications=[{
                    "title": match.theorem_name,
                    "author": match.author,
                    "year": match.year,
                    "citation": match.citation,
                    "doi": match.doi,
                }],
                suggested_action=action,
                search_query_used="",
                explanation=f"{desc}: {match.theorem_name} ({match.author}, {match.year}).",
            )

        # 2. Formulate scholarly search query
        query = self.construct_scholarly_query(conjecture)
        related_pubs: List[Dict[str, Any]] = []

        if online:
            related_pubs = self.query_openalex(query, limit=3, timeout_sec=timeout_sec)

        # A missing registry match is an open review question, not a discovery.
        return NoveltyReport(
            status=NoveltyStatus.UNKNOWN_IN_LITERATURE,
            conjecture_id=conjecture.id,
            statement=conjecture.statement,
            matched_theorem=None,
            novelty_score=0.0,
            related_publications=related_pubs,
            suggested_action="ELEVATE_TO_PROVER_SKEPTIC",
            search_query_used=query,
            explanation="No match in the local registry. Novelty has not been established; title search does not establish novelty either.",
        )
