"""Small, bounded source corpus for mathematical review; fetched text is data.

Only explicitly allowed public paper URLs are fetched. Cached failure is not an
empty literature search. Offline calls read existing files and never fetch.
"""
from __future__ import annotations

import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess
import sys
import time
import urllib.parse
import urllib.request

from autonomous_math.research_state import atomic_save_json, sha256

SOURCE_REVISION = "spectral-comparison-primary-papers-v4"
EXTRACTION_REVISION = "complete-html-statements-and-context-v2"
MATHLIB_PIN = "d13f23b723b8a846827a245b89c10fc7d3f11612"
MAX_PDF_BYTES = 4_000_000
MAX_PAGES = 32
MAX_PAGE_CHARS = 40_000
MAX_EXCERPT_CHARS = 3200
FETCH_RETRY_SEC = 3600
MAX_REQUESTED_PAPERS = 6
MAX_GUIDANCE_BYTES = 10_000
_CODING = {"parity_code_distance", "parity_code_dimension", "unique_neighbor_radius"}
_NONCODE_ROUTING_REVISION = "noncode-primary-and-mathlib-routing-v1"
EVIDENCE_TOPICS = frozenset({"alternating_rank", "forest_rank_matching", "clique_binary_rank", "locality",
    "chromatic_edges", "independent_edges", "degree_empty", "spectral_regular", "estrada", "forest_energy",
    "stopping_adjacency", "cycle_incidence", "signless_irregularity", "signless_local_refinements",
    "normalized_energy_bridge", "energy_lower_bounds", "adjacency_edge_envelope", "signless_clique_cut"})
MAX_EVIDENCE_REQUESTS = 4
_PAPERS = (
    {"title": "On the Stopping Distance and the Stopping Redundancy of Codes",
     "url": "https://arxiv.org/html/cs/0503058v2",
     "citation": "M. Schwartz and A. Vardy (2005), arXiv:cs/0503058v2 (16 December), accepted author preprint.",
     "selection": "Versioned arXiv author preprint HTML; MathML alttext preserves mathematical symbols.",
     "topics": ["stopping"], "preferred_anchors": ["Thmdefn1", "Thmthm1", "Thmthm2"]},
    {"title": "Expander Codes", "url": "https://www.cs.yale.edu/homes/spielman/PAPERS/expandersIT.pdf",
     "citation": "M. Sipser and D. A. Spielman (1996), IEEE Transactions on Information Theory 42(6), 1710–1722.",
     "selection": "Author-hosted published paper; verified public author publication URL.", "topics": ["expander"]},
    {"title": "On the Griesmer Bound for Systematic Codes", "url": "https://arxiv.org/html/1310.4060v1",
     "citation": "E. Bellini (2013), arXiv:1310.4060v1, Theorem 2.1 (Griesmer bound).",
     "selection": "Versioned primary author preprint; linear-code bound with prime-power field context.",
     "topics": ["griesmer"], "preferred_anchors": ["S2.Thmtheorem1"], "context_anchors": ["S2.p1"]},
    {"title": "On the Griesmer bound for nonlinear codes", "url": "https://arxiv.org/html/1502.07379v1",
     "citation": "E. Bellini, E. Guerrini, A. Meneghetti and M. Sala (2015), arXiv:1502.07379v1, Theorem 3.2 and Section 1.",
     "selection": "Versioned primary research paper restating the classical Plotkin and Singleton bounds; finite-field code notation retained.",
     "topics": ["singleton", "plotkin"], "preferred_anchors": ["S3.Thmtheorem2"],
     "context_anchors": ["S1.p1", "S1.p3"]},
    {"title": "Homological error correction: Classical and quantum codes", "url": "https://arxiv.org/html/quant-ph/0605094v1",
     "citation": "H. Bombin and M. A. Martin-Delgado (2006), arXiv:quant-ph/0605094v1, Section II.A, equation (3).",
     "selection": "Versioned primary paper; only the classical binary Hamming bound and its error-correction definitions are selected.",
     "topics": ["hamming"], "preferred_anchors": [], "context_anchors": ["S2.SS1.p4", "S2.SS1.p5"]},
    {"title": "Upper bounds on the k-forcing number of a graph", "url": "https://arxiv.org/html/1401.6206v1",
     "citation": "D. Amos, Y. Caro, R. Davila and R. Pepper (2014), arXiv:1401.6206v1, Corollary 4.6.",
     "selection": "Versioned primary author preprint; connectedness and maximum-degree hypotheses are retained.",
     "topics": ["zero_forcing"], "preferred_anchors": ["S4.Thmtheorem6"], "context_anchors": ["S1.p1"]},
    {"title": "Solving systems of linear equations through zero forcing set and application to lights out",
     "url": "https://arxiv.org/html/2208.09731v1",
     "citation": "J. Wang, C. Xu and S. Zhou (2022), arXiv:2208.09731v1, Theorem 2.3 and Section 2.",
     "selection": "Versioned primary paper; arbitrary-field matrix support and forcing definitions accompany independent columns outside a forcing set.",
     "topics": ["zero_forcing"], "preferred_anchors": ["S2.Thmtheorem3"], "context_anchors": ["S2.p4", "S2.p5"]},
    {"title": "Eigenvalue bounds and alternating rank-metric codes",
     "url": "https://arxiv.org/html/2405.09254v1",
     "citation": "A. Abiad, G. N. Alfarano and A. Ravagnani (2024), arXiv:2405.09254v1, Definition 2.1 and Section 2.1.",
     "selection": "Finite-field definition plus the complete even-rank observation; rank-metric bounds are not adjacency-code Hamming bounds. Positive matrix order is explicit; zero order needs a separate local argument.",
     "topics": ["alternating_rank"], "preferred_anchors": ["S2.Thmtheorem1"],
     "context_anchors": ["S2.p1", "S2.SS1.p3"]},
    {"title": "On the structure of the fundamental subspaces of acyclic matrices with 0 in the diagonal",
     "url": "https://arxiv.org/html/1802.10142v1",
     "citation": "D. A. Jaume and A. Pastine (2018), arXiv:1802.10142v1, Corollary 10.",
     "selection": "Forest rank equals twice maximum matching size over an arbitrary field. Matrix-pattern and zero-diagonal definitions remain with the corollary; it is not merely a real-spectrum claim.",
     "topics": ["forest_rank_matching", "forest_energy"], "preferred_anchors": ["Thmtheorem10"],
     "context_anchors": ["S1.p1", "S1.p2", "S1.p7"]},
    {"title": "On the Locality of Codeword Symbols", "url": "https://arxiv.org/html/1106.3625v1",
     "citation": "P. Gopalan, C. Huang, H. Simitci and S. Yekhanin (2011), arXiv:1106.3625v1, Theorem 5.",
     "selection": "Complete information-locality Singleton bound with generator-coordinate and locality definitions. Applicability to coordinates forced to zero must be checked, not assumed.",
     "topics": ["locality"], "preferred_anchors": ["Thmtheorem5", "Thmtheorem2", "Thmtheorem3"],
     "context_anchors": ["S2.p2"]},
    {"title": "Ore's Conjecture on color-critical graphs is almost true",
     "url": "https://arxiv.org/html/1209.1050v1",
     "citation": "A. Kostochka and M. Yancey (2012), arXiv:1209.1050v1, introduction and Theorem 3.",
     "selection": "Critical-subgraph reduction and the classical minimum-degree edge bound accompany the named theorem. Small chromatic numbers and empty graphs require their explicit elementary cases.",
     "topics": ["chromatic_edges"], "preferred_anchors": ["Thmtheorem3"],
     "context_anchors": ["S1.p2", "S1.p4"]},
    {"title": "The enhanced principal rank characteristic sequence over a field of characteristic 2",
     "url": "https://arxiv.org/html/1608.07871v1",
     "citation": "X. Martínez-Rivera (2016), arXiv:1608.07871v1, Proposition 2.2 and its proof.",
     "selection": "Characteristic-two complete-graph principal minors, their determinant calculation, and the sequence definition. The proposition requires n>=2; ranks and smaller orders need their own comparison.",
     "topics": ["clique_binary_rank"], "preferred_anchors": ["S2.Thmthm2"],
     "context_anchors": ["S1.p2", "S1.p4", "S2.p3"]},
    {"title": "Spectral radius minus average degree: a better bound",
     "url": "https://arxiv.org/html/1407.4285v1",
     "citation": "F. Goldberg (2014), arXiv:1407.4285v1, Lemma 4, restating Liu and Liu (MATCH 62, 2009), Theorem 2.1.",
     "selection": "Complete degree-square bound for Q=A+D, with its explicit extension beyond connected graphs. The aggregate irregularity corollary is a separate algebraic deduction, not a quotation.",
     "topics": ["signless_irregularity", "spectral_regular"], "preferred_anchors": ["Thmlem4"],
     "context_anchors": ["S3.p3", "S1.SS1.p1"], "comparison_role": "published_comparison",
     "comparison_baselines": {"Thmlem4": ["signless_degree_square"]}},
    {"title": "Energies of Hypergraphs", "url": "https://arxiv.org/html/1912.03224v2",
     "citation": "K. Cardoso and V. Trevisan (2020), Electronic Journal of Linear Algebra 36, 293–308, Lemma 3.20; arXiv v2 Lemma 17.",
     "selection": "Complete RMS bound and uniform-hypergraph, real matrix, incidence and Zagreb definitions. Ordinary graphs require k=2, giving Q=D+A. Positive order is implicit in division by n; empty graphs need a local case.",
     "topics": ["signless_irregularity"], "preferred_anchors": ["ThmTeo17"],
     "context_anchors": ["S2.p2", "S2.p3", "S2.p5", "S2.p6", "S3.SS1.p5"], "comparison_role": "published_comparison",
     "comparison_baselines": {"ThmTeo17": ["signless_rms"]}},
    {"title": "Eigenvalue bounds for the signless Laplacian",
     "url": "https://dspace.stir.ac.uk/bitstream/1893/18513/1/Eigenvalue%20bounds%20for%20the%20signless%20laplacian%202007.pdf",
     "citation": "D. Cvetković, P. Rowlinson and S. K. Simić (2007), Publ. Inst. Math. 81(95), 11–27, confirmed Conjecture 4, pp. 16 and 23.",
     "selection": "Complete published maximum-degree lower bound and confirmation proof, with simple-graph Q=D+A definitions. Its printed statement requires connectedness and n>=4; extensions need separate local arguments.",
     "topics": ["signless_irregularity", "spectral_regular"], "preferred_pdf_markers": [],
     "pdf_context_markers": [
         {"page": 1, "start": "Let G be a simple graph withn vertices.", "end": "2000 Mathematics"},
         {"page": 6, "start": "Conjecture 4(", "end": "is the star Sn.", "include_end": True,
          "evidence_kind": "body_statement", "marker": "Confirmed Conjecture 4"},
         {"page": 13, "start": "Next we conﬁrm Conjecture 4.", "end": "Alternatively,"}],
     "comparison_role": "published_comparison",
     "comparison_baselines": {"Confirmed Conjecture 4": ["signless_max_degree"]},
     "reviewed_comparison": {"source_sha256": "91207fe0f13d51a43071462c38c9c03f9e1b1bd8582e7f792245129868e7b1f4",
         "marker": "Confirmed Conjecture 4", "locator": "Separate Theorem 4.2, printed pp. 20–21; PDF pages 10–11",
         "premises": "Finite simple undirected unweighted graph, real Q=D+A; at least one edge for the adjacent-pair maximum. Connectedness is only required for its equality characterization, not the inequality.",
         "statement": "min_{uv in E}(d_u+d_v)<=q<=max_{uv in E}(d_u+d_v). Simplicity gives d_u+d_v<=m+1, hence q<=m+1; an edgeless graph has q=0. The adjacent degree-sum upper bound is stronger than its scalar corollary.",
         "comparison_baselines": ["signless_edge_degree_sum", "signless_edge_count_upper"],
         "fidelity": "Complete Theorem 4.2 formula transcribed from separately reviewed PDF pages 10–11; this is not a quotation from the accompanying lower-bound excerpt. Published 2007; no earliest attribution claim."}},
    {"title": "Graph energy estimates via the Chebyshev functional",
     "url": "https://arxiv.org/html/1407.7430v3",
     "citation": "F. Goldberg (2014), arXiv:1407.7430v3, Theorem 2.2, Corollary 3.2 and Theorem 3.4.",
     "selection": "Complete adjacency-energy bounds 2sqrt(m), 2m/rho and regular positive-degree n, with ordered eigenvalue and energy definitions. Division by rho requires an edge. The erroneous m=2pq in Remark 3.3 is not selected. Extra determinant/rank parameters are not silently substituted.",
     "topics": ["energy_lower_bounds"], "preferred_anchors": ["S2.Thmthm2", "S3.Thmthm2", "S3.Thmthm4"],
     "context_anchors": ["S1.p1", "S1.SS1.p1"], "comparison_role": "published_comparison",
     "comparison_baselines": {"S2.Thmthm2": ["energy_sqrt_edges"],
                              "S3.Thmthm2": ["energy_edges_over_radius"],
                              "S3.Thmthm4": ["energy_regular_order"]}},
    {"title": "Lectures on Spectral Graph Theory", "url": "https://www.math.ucsd.edu/~fan/cbms.pdf",
     "citation": "F. R. K. Chung, author-hosted chapter 1, Section 1.2, printed pages 2–3.",
     "selection": "Exact normalized Laplacian definition and regular affine matrix bridge, with isolated-vertex convention. The energy-gap inequality inferred from the bridge is not a printed theorem or a priority claim.",
     "topics": ["normalized_energy_bridge", "spectral_regular"], "preferred_pdf_markers": [],
     "pdf_context_markers": [
         {"page": 5, "start": "In a graph G,l e tdv denote the degree of the vertexv.",
          "end": "A graph is said to be nontrivial if it contains at least one edge.", "include_end": True},
         {"page": 6, "start": "When G is k-regular, it is easy to see that",
          "end": "For a general graph, we have", "marker": "Regular normalized Laplacian bridge"}],
     "comparison_role": "published_comparison",
     "comparison_baselines": {"Regular normalized Laplacian bridge": ["normalized_regular_bridge"]}},
    {"title": "A Very Short Proof for a Lower Bound for Energy of Graphs",
     "url": "https://match.pmf.kg.ac.rs/electronic_versions/Match84/n2/match84n2_345-347.pdf",
     "citation": "M. R. Oboudi (2020), MATCH 84, 345–347, Remark 1 and the proof of Theorem 3.",
     "selection": "Complete adjacency trace/positive-energy identity. It implies E>=2rho; the enclosing minimum-degree theorem has additional connectedness hypotheses.",
     "topics": ["energy_lower_bounds", "normalized_energy_bridge"], "preferred_pdf_markers": [],
     "pdf_context_markers": [
         {"page": 1, "start": "Throughout this paper we will consider only simple graphs",
          "end": "Since A(G) is symmetric, all of the eigenvalues of A(G) are real.", "include_end": True},
         {"page": 2, "start": "Remark 1. Let G be a graph", "end": "Now we state",
          "evidence_kind": "body_statement", "marker": "Remark 1"}],
     "comparison_role": "published_comparison",
     "comparison_baselines": {"Remark 1": ["energy_spectral_radius"]}},
    {"title": "A Bound on the Spectral Radius of Graphs with e Edges",
     "url": "https://math.mit.edu/~rstan/pubs/pubfiles/71.pdf",
     "citation": "R. P. Stanley (1987), Linear Algebra Appl. 87, 267–269, Theorem, equation (2), p. 268.",
     "selection": "Author-hosted published paper. The scan's formula is transcribed from the retained page image; extraction remains separate.",
     "topics": ["adjacency_edge_envelope"], "preferred_pdf_markers": [],
     "pdf_context_markers": [{"page": 2, "start": "THEOREM. Let A", "end": "Proof.",
         "evidence_kind": "body_statement", "marker": "Stanley Theorem"}],
     "comparison_role": "published_comparison",
     "comparison_baselines": {"Stanley Theorem": ["adjacency_stanley", "adjacency_linear_edge_envelope"]},
     "reviewed_comparison": {"source_sha256": "2408f536c0771e4f85cc4128cbe43823e1787c2e8bb69c5d94738db196738c11",
         "marker": "Stanley Theorem", "locator": "Theorem (2), printed p. 268; PDF page 2",
         "page_image_sha256": "82b0d88f22428f38def9326ae19258ab5265fc571fae418ceb8f5be8488f8e98",
         "premises": "Finite symmetric zero-diagonal (0,1) adjacency matrix with 2m ones; finite simple undirected graph, including disconnected graphs and isolates.",
         "statement": "rho <= (sqrt(1+8m)-1)/2. Equality: a complete graph together with isolated vertices.",
         "derivation": "Combined with the supplied Hong bound on each nontrivial component, this implies rho <= m/4+3/2 for every finite simple graph; that linear envelope is routine, not an improvement over Stanley/Hong.",
         "fidelity": "Page-image-checked formula transcription; not a verbatim quotation of the garbled PDF extraction. Published 1987; no earliest-priority claim."}},
    {"title": "The Spectral Radius of a Planar Graph",
     "url": "https://people.clas.ufl.edu/avince/files/Spectral.pdf",
     "citation": "D. Cao and A. Vince (1993), Linear Algebra Appl. 187, 251–257, Lemma 2 (Hong Yuan), p. 252.",
     "selection": "Author-hosted published reproduction of Hong's bound. Planarity is not a hypothesis of Lemma 2; the original 1988 paper was not accessed.",
     "topics": ["adjacency_edge_envelope"], "preferred_pdf_markers": [],
     "pdf_context_markers": [{"page": 2, "start": "LEMMA 2 (Hong Yuan)", "end": "LEMMA 3",
         "evidence_kind": "body_statement", "marker": "Hong Lemma 2"}],
     "comparison_role": "published_comparison", "comparison_baselines": {"Hong Lemma 2": ["adjacency_hong", "adjacency_linear_edge_envelope"]},
     "reviewed_comparison": {"source_sha256": "1801696229afa0481b62f298ad81023f6b96aec26aac8644f2865888259bffd4",
         "marker": "Hong Lemma 2", "locator": "Lemma 2, printed p. 252; PDF page 2",
         "page_image_sha256": "d2f988c10e40a1cb2d516b01d495382dbd4f0e4225e206ceab3da1677724048e",
         "premises": "Finite simple undirected graph with n vertices, m edges and no isolated vertices. Neither planarity nor connectedness is required for this lemma.",
         "statement": "rho <= sqrt(2m-n+1). Equality: disjoint union of either a star or a complete graph with copies of K2.",
         "derivation": "For a nontrivial component with n>=5, rho^2<=2m-4 and (m/4+3/2)^2-(2m-4)=(m-10)^2/16>=0. For n<=4, m<=6 and Stanley applies: (m/2+4)^2-(1+8m)=(m-6)(m-10)/4>=0. Take the maximum component radius and m_component<=m_total; edgeless radius is zero.",
         "fidelity": "Page-image-checked <= transcription; extracted '<' is a scan error. Read 1993 reproduction crediting Hong; original 1988 full text remains unaccessed."}},
    {"title": "A generalization for the clique and independence numbers",
     "url": "https://journals.uwyo.edu/index.php/ela/article/download/1025/1025/1025",
     "citation": "A. D. Maden (Gungor) and A. S. Cevik (2012), Electronic J. Linear Algebra 23, 164–170, Lemma 3.4, p. 168; DOI 10.13001/1081-3810.1512.",
     "selection": "Publisher full text, average block-row-sum quotient and complete symmetric-matrix interlacing lemma. Equitability is not required.",
     "topics": ["signless_clique_cut"], "preferred_pdf_markers": [],
     "pdf_context_markers": [{"page": 5, "start": "let us suppose", "end": "Liu et al.",
         "evidence_kind": "body_statement", "marker": "Quotient interlacing"}],
     "comparison_role": "published_comparison", "comparison_baselines": {"Quotient interlacing": ["signless_clique_quotient", "signless_clique_cut_scalar"]},
     "reviewed_comparison": {"source_sha256": "41ec583b0f7642b63c5489e97bca238ef49c75575df1b5c918ea33f61de05756",
         "marker": "Quotient interlacing", "locator": "Lemma 3.4 and preceding quotient definition, printed p. 168; PDF page 5",
         "premises": "Real symmetric matrix partitioned into nonempty blocks; quotient entries are average block row sums. Its eigenvalues interlace those of the matrix; no regular or equitable partition premise.",
         "statement": "Apply to Q=D+A of a finite simple graph and a maximum clique S of size s=omega<n, T=V\\S of size t=n-s, c=2(s-1), b=e(S,T), e_T=e(T): q>=lambda_max(C), C=[[c+b/s,b/sqrt(st)],[b/sqrt(st),(b+4e_T)/t]]. This is a graph-dependent baseline; b and e_T are comparison data, not supported proposal invariants.",
         "derivation": "Fiedler's cut inequality gives b>=b0=a*s*t/n. For B obtained by b=b0,e_T=0, C-B=(b-b0)*v*v^T+diag(0,4e_T/t) is PSD, v=(1/sqrt(s),1/sqrt(t)). trace(B)=c+a, det(B)=a*c*s/n. Hence q>=(c+a+sqrt((c+a)^2-4*a*c*s/n))/2 and n*q*(q-c)>=a*(n*q-c*s). Complete graphs s=n are a separate equality case. The combined scalar bound is a routine derivation, not a quotation or established earliest attribution.",
         "fidelity": "Formula is an explicit source-bound derivation from the complete quotient lemma plus Fiedler, not a printed combined theorem. Exact combined-form priority remains unresolved."}},
    {"title": "Algebraic connectivity of graphs",
     "url": "https://dml.cz/bitstream/handle/10338.dmlcz/101168/CzechMathJ_23-1973-2_11.pdf",
     "citation": "M. Fiedler (1973), Czechoslovak Math. J. 23, 298–305, variational principle pp. 298–299; DOI 10.21136/CMJ.1973.101168.",
     "selection": "Publisher-hosted primary full text. Unit vectors orthogonal to ones and the complete second-eigenvalue variational principle are retained together.",
     "topics": ["signless_clique_cut"], "preferred_pdf_markers": [],
     "pdf_context_markers": [
         {"page": 2, "start": "For our purpose it is convenient", "end": "298"},
         {"page": 3, "start": "eigenvalue О", "end": "Further,", "evidence_kind": "body_statement", "marker": "Laplacian variational principle"}],
     "comparison_role": "published_comparison", "comparison_baselines": {"Laplacian variational principle": ["laplacian_cut", "signless_clique_cut_scalar"]},
     "reviewed_comparison": {"source_sha256": "246c5f338dc4ed0f9c00bff68d8111b79b1cd9c625cffb1dc512fcea661a6958",
         "marker": "Laplacian variational principle", "locator": "Variational principle, printed pp. 298–299; PDF pages 2–3",
         "premises": "Finite simple undirected unweighted graph, n>=2, real Laplacian L=D-A. Algebraic connectivity a is the second smallest eigenvalue; unit vectors x orthogonal to ones give a=min x^T L x.",
         "statement": "For any nonempty proper S, with s=|S|, t=n-s and b=e(S,V\\S), the centered indicator Rayleigh quotient gives a<=n*b/(s*t), equivalently b>=a*s*t/n. This cut inequality is the review's substitution into the published variational principle, not a claimed verbatim paper formula.",
         "fidelity": "Source-bound transcription of the variational principle, followed by an explicitly labelled cut derivation; PDF glyphs remain separately unverified by extraction. No novelty or priority certificate."}},
    {"title": "Binary Cycle Codes Have Optimal Stopping Redundancy",
     "url": "https://www.jstage.jst.go.jp/article/transfun/E108.A/5/E108.A_2024EAL2062/_pdf",
     "citation": "Y. Qi, C. Tang, H. Liu and L. Ma (2025), IEICE Transactions on Fundamentals E108-A(5), 764–768, Definition 3 and Lemma 3.",
     "selection": "Construction contrast only: columns are graph edges and H is the vertex-edge incidence matrix. This is not prior art establishing equality for a fixed vertex-vertex adjacency matrix.",
     "topics": ["cycle_incidence", "stopping_adjacency"], "preferred_pdf_markers": ["Definition 3", "Lemma 3"],
     "pdf_end_markers": {"Definition 3": "Note that each column"},
     "construction": "vertex_edge_incidence", "comparison_role": "different_construction"},
)


def _digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, allow_nan=False).encode()).hexdigest()


def paper_url(url):
    """Accept an exact HTTPS paper location, never a general landing page."""
    if not isinstance(url, str) or len(url) > 1500:
        raise ValueError("Invalid bounded source URL")
    parsed = urllib.parse.urlsplit(url)
    if (parsed.scheme != "https" or parsed.username or parsed.password or parsed.port not in (None, 443)
            or parsed.query or parsed.fragment):
        raise ValueError("Source URL must be plain allowlisted HTTPS")
    host = parsed.hostname
    if host == "www.jstage.jst.go.jp" and parsed.path == "/article/transfun/E108.A/5/E108.A_2024EAL2062/_pdf":
        return url  # One reviewed publisher paper, not a general journal allowlist.
    if url in {
        "https://math.mit.edu/~rstan/pubs/pubfiles/71.pdf",
        "https://people.clas.ufl.edu/avince/files/Spectral.pdf",
        "https://journals.uwyo.edu/index.php/ela/article/download/1025/1025/1025",
        "https://dml.cz/bitstream/handle/10338.dmlcz/101168/CzechMathJ_23-1973-2_11.pdf",
        "https://www.math.ucsd.edu/~fan/cbms.pdf",
        "https://mathweb.ucsd.edu/~fan/cbms.pdf",
        "https://fanchung.ucsd.edu/cbms.pdf",
        "https://match.pmf.kg.ac.rs/electronic_versions/Match84/n2/match84n2_345-347.pdf",
        "https://dspace.stir.ac.uk/bitstream/1893/18513/1/Eigenvalue%20bounds%20for%20the%20signless%20laplacian%202007.pdf",
    }:
        return url  # Exact reviewed chapter/papers; no additional host-wide access.
    if host in {"arxiv.org", "www.arxiv.org", "export.arxiv.org"}:
        match = re.fullmatch(r"/(abs|pdf|html)/((?:[A-Za-z.-]+/)?\d{4}\.\d{4,5}(?:v\d+)?|[A-Za-z.-]+/\d{7}(?:v\d+)?)(?:\.pdf)?", parsed.path)
        if not match:
            raise ValueError("Only explicit arXiv paper identifiers are allowed")
        return "https://arxiv.org/" + ("html" if match[1]=="html" else "pdf") + "/" + match[2]
    permitted = ((host == "www.ece.mcmaster.ca" and parsed.path.startswith("/~schwam10/publications/"))
                 or (host in {"www.cs.yale.edu", "cs.yale.edu"} and parsed.path.startswith("/homes/spielman/PAPERS/")))
    if not permitted or not parsed.path.endswith(".pdf") or ".." in urllib.parse.unquote(parsed.path).split("/"):
        raise ValueError("Source host/path is outside the reviewed public paper allowlist")
    return urllib.parse.urlunsplit(("https", host, parsed.path, "", ""))


class _SafeRedirect(urllib.request.HTTPRedirectHandler):
    max_redirections = 3
    def redirect_request(self, request, fp, code, msg, headers, newurl):
        safe = paper_url(newurl)
        return super().redirect_request(request, fp, code, msg, headers, safe)


def _entry_path(directory, url):
    cache=Path(directory)/"novelty_sources"
    if cache.is_symlink():raise ValueError("Source cache directory is a symlink")
    return cache / (hashlib.sha256(url.encode()).hexdigest() + ".json")


def _load_entry(directory, url):
    try:
        path = _entry_path(directory, url)
        if path.is_symlink() or path.stat().st_size > 500_000:
            return {}
        entry = json.loads(path.read_text())
        return entry if entry.get("url") == url else {}
    except (OSError, ValueError, AttributeError):
        return {}


def evidence_requests(record, theorem=None):
    """Bounded source-routing requests, never endorsements or arbitrary URLs.

    A completed unresolved comparison can request a reviewed topic explicitly.
    Older comparisons receive conservative routing from their recorded gaps so
    the existing worker can acquire missing evidence without another AI call.
    """
    requests = []
    review = record.get("ai_review") or {}
    if not isinstance(review, dict):
        review = {}
    coverage = review.get("source_coverage") or {}
    if not isinstance(coverage, dict):
        coverage = {}
    for origin, values in (("record", record.get("evidence_requests", [])),
                           ("retained_request", coverage.get("evidence_requests", [])),
                           ("comparison", review.get("evidence_requests", []))):
        if not isinstance(values, list):
            continue
        for value in values[:MAX_EVIDENCE_REQUESTS]:
            if not isinstance(value, dict) or value.get("topic") not in EVIDENCE_TOPICS:
                continue
            detail = value.get("detail", "")
            if not isinstance(detail, str):
                continue
            if value["topic"] not in {item["topic"] for item in requests}:
                requests.append({"topic": value["topic"], "detail": detail[:700], "origin": origin})
    if review.get("status") == "complete" and review.get("outcome") == "unresolved":
        uncertainties = review.get("uncertainties", [])
        checks = review.get("checks", [])
        fragments = ([text[:1200] for text in uncertainties[:16] if isinstance(text, str)]
                     if isinstance(uncertainties, list) else [])
        if isinstance(checks, list):
            fragments.extend(item.get("detail", "")[:1200] for item in checks[:3]
                             if isinstance(item, dict) and isinstance(item.get("detail"), str))
        text = " ".join(fragments).lower()
        rules = (
            ("alternating_rank", "alternating" in text and ("rank" in text or "parity" in text)),
            ("forest_rank_matching", "forest" in text and ("rank" in text or "matching" in text)),
            ("clique_binary_rank", "complete-graph" in text or "complete graph" in text or "clique–rank" in text),
            ("locality", "locality" in text),
            ("chromatic_edges", "chromatic" in text and ("edge" in text or "critical" in text)),
            ("independent_edges", "independence/nonedge" in text or "clique-pair" in text or "α(h)" in text),
            ("degree_empty", "degree" in text and ("empty vertex" in text or "empty-case" in text)),
            ("spectral_regular", "spectral completeness" in text or "signless" in text),
            ("signless_irregularity", "signless" in text and any(word in text for word in ("irregular", "variance", "rms", "zagreb"))),
            ("energy_lower_bounds", "energy" in text and any(word in text for word in ("lower bound", "spectral radius", "stronger"))),
            ("normalized_energy_bridge", "energy" in text and "normalized" in text),
            ("estrada", "exponential" in text or "exp(ρ)" in text),
            ("forest_energy", "energy" in text and "rank" in text),
            ("stopping_adjacency", "unicyclic" in text or "adjacency stopping" in text or "minimum-row-weight stopping" in text),
        )
        for topic, applies in rules:
            if applies and topic not in {item["topic"] for item in requests}:
                requests.append({"topic": topic, "detail": "Recorded unresolved comparison requires this reviewed source topic.",
                                 "origin": "recorded_gap"})
    return requests[:MAX_EVIDENCE_REQUESTS]


def literature_topics(record, variables, theorem=None):
    """Deterministic routing hints, never a mathematical applicability verdict."""
    variables = set(variables)
    target = (theorem or {}).get("conjecture", theorem or {})
    text = json.dumps(target, sort_keys=True, allow_nan=False).lower()
    properties = set()
    def collect_guard(guard):
        if not isinstance(guard, dict):
            return
        if guard.get("predicate_type") == "property" and not guard.get("negated"):
            properties.add(guard.get("property_name"))
        if guard.get("predicate_type") == "conjunction":
            for child in guard.get("guards") or []:
                collect_guard(child)
    collect_guard(target.get("guard_predicate") if isinstance(target, dict) else None)
    leads = list(record.get("search", {}).get("results", []))[:5] + list(record.get("closest_results", []))[:5]
    lead_text = " ".join(str(lead.get("title", "")) + " " + str(lead.get("theorem_name", ""))
                         for lead in leads if isinstance(lead, dict)).lower()
    topics = [item["topic"] for item in evidence_requests(record, theorem)]
    def add(*names):
        for name in names:
            if name not in topics:
                topics.append(name)
    if not variables & _CODING:
        # Recorded gaps are routing hints, not permission to switch coefficient
        # fields or code constructions for a real spectral/combinatorial target.
        topics = [topic for topic in topics if topic not in {
            "alternating_rank", "clique_binary_rank", "locality", "stopping_adjacency", "cycle_incidence"}]
    if "is_forest" in properties and "parity_code_dimension" in variables:
        add("forest_rank_matching")
    if "is_forest" in properties and "graph_energy" in variables:
        add("forest_energy")
    if "clique_number" in variables and "parity_code_dimension" in variables:
        add("clique_binary_rank")
    if "chromatic_number" in variables and "size" in variables:
        add("chromatic_edges")
    if "independence_number" in variables and "size" in variables:
        add("independent_edges")
    if "estrada_index" in variables:
        add("estrada")
    if "graph_energy" in variables:
        if "normalized_laplacian_spectral_gap" in variables:
            add("normalized_energy_bridge")
        add("energy_lower_bounds")
    if {"spectral_radius", "size"} <= variables:
        add("adjacency_edge_envelope")
    if "signless_laplacian_spectral_radius" in variables and variables & {"clique_number", "algebraic_connectivity"}:
        add("signless_clique_cut")
    if "signless_laplacian_spectral_radius" in variables:
        add("signless_irregularity", "signless_local_refinements")
    if "is_regular" in properties and variables & {
            "signless_laplacian_spectral_radius", "normalized_laplacian_spectral_gap"}:
        add("spectral_regular")
    if "parity_code_dimension" in variables and ("parity_code_distance" not in variables or
            target and (variables & {"max_degree", "min_degree"} or "is_connected" in text)):
        add("zero_forcing")
    if "parity_code_distance" in variables:
        if not target:
            add("griesmer")
        if '"ceil"' in text:
            add("griesmer")
        if '"^"' in text or '"exp"' in text:
            add("plotkin", "hamming")
        if '"floor"' in text or '"log1p"' in text:
            add("hamming")
        if variables & {"order", "parity_code_dimension"}:
            add("singleton", "griesmer", "plotkin", "hamming")
    for name in ("griesmer", "singleton", "plotkin", "hamming", "zero_forcing", "stopping", "expander"):
        if name.replace("_", " ") in lead_text:
            add(name)
    if "unique_neighbor_radius" in variables:
        add("stopping", "expander")
    if variables & _CODING:
        add("griesmer", "singleton", "plotkin", "hamming", "stopping", "expander")
    if not target and "parity_code_dimension" in variables:
        add("zero_forcing")  # Family bridge variables do not displace distance bounds.
    return topics


def _paper_identity(value):
    parsed = urllib.parse.urlsplit(value)
    return re.sub(r"v\d+$", "", parsed.path.split("/", 2)[-1]) if parsed.hostname == "arxiv.org" else value


def _same_selection(entry, paper):
    return all(entry.get(key) == value for key, value in paper.items())


def _ranked_papers(topics):
    ranked = sorted(enumerate(_PAPERS), key=lambda pair: (min(
        (topics.index(topic) for topic in pair[1].get("topics", ["stopping"]) if topic in topics),
        default=len(topics)), pair[0]))
    return [dict(paper) for _, paper in ranked if set(paper.get("topics", ["stopping"])) & set(topics)]


def requested_papers(record, variables, theorem=None):
    papers = _ranked_papers(literature_topics(record, variables, theorem))
    leads = list(record.get("search", {}).get("results", []))[:5]
    leads += list(record.get("closest_results", []))[:5]
    for lead in leads:
        if not isinstance(lead, dict):
            continue
        try:
            url = paper_url(lead.get("url"))
        except ValueError:
            continue
        if _paper_identity(url) not in {_paper_identity(item["url"]) for item in papers}:
            papers.append({"url": url, "title": str(lead.get("title", "Public research paper"))[:300],
                           "citation": str(lead.get("citation", lead.get("doi", "")))[:500],
                           "selection": "Explicit allowlisted paper URL from a bibliographic lead; identity checked against extracted title text."})
    return papers[:MAX_REQUESTED_PAPERS]


def current_evidence_key(record, theorem, directory):
    """Cheap read-only queue identity. Failed fetch timestamps do not cause loops."""
    from autonomous_math.core.ast import Conjecture
    c = Conjecture.from_dict(theorem["conjecture"])
    variables = c.lhs_expr.variables | c.rhs_expr.variables
    variables |= getattr(c.guard_predicate, "variables", set())
    papers = requested_papers(record, variables, theorem)
    available = []
    for paper in papers:
        entry = _load_entry(directory, paper["url"])
        valid = False
        if entry.get("status") == "available":
            try:
                _read_pages(directory,entry,paper)
                valid = True
            except (OSError,ValueError,KeyError,TypeError):
                pass
        available.append((paper, entry.get("source_sha256") if valid else None,
                          entry.get("text_file_sha256") if valid else None))
    identity = [SOURCE_REVISION, record.get("fingerprint"), MATHLIB_PIN,
                [request["topic"] for request in evidence_requests(record, theorem)], available]
    previous_family = ("degree_and_structural_classes" if variables & {
        "min_degree", "max_degree", "average_degree", "density", "size"} else "coloring_and_independence")
    family = _mathlib_review_family(variables)
    if not variables & _CODING and family != previous_family:
        # Only corrected pinned-source selections require a new policy binding.
        # Paper selection changes already invalidate their existing identities.
        identity.append([_NONCODE_ROUTING_REVISION, family])
    return _digest(identity)


def source_refresh_due(record,theorem,directory,now=None):
    """A completed comparison can retry only due source acquisition, without a model."""
    from autonomous_math.core.ast import Conjecture
    c = Conjecture.from_dict(theorem["conjecture"])
    variables = c.lhs_expr.variables | c.rhs_expr.variables | getattr(c.guard_predicate, "variables", set())
    for paper in requested_papers(record, variables, theorem):
        entry = _load_entry(directory,paper["url"])
        if entry.get("status") == "available":
            try:
                _read_pages(directory, entry, paper)
                continue
            except (OSError, ValueError, KeyError, TypeError):
                return True
        if (entry.get("acquisition_revision") != SOURCE_REVISION or not _same_selection(entry, paper)
                or (now if now is not None else time.time()) >= entry.get("retry_at",0)):
            return True
    return False


def _fetch(url, deadline):
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise TimeoutError("Source preparation deadline exhausted")
    opener = urllib.request.build_opener(_SafeRedirect())
    request = urllib.request.Request(paper_url(url), headers={"User-Agent": "MathFoundry/1.0 (bounded mathematical source review)",
        "Accept": "text/html" if urllib.parse.urlsplit(url).path.startswith("/html/") else "application/pdf"})
    with opener.open(request, timeout=min(5, remaining)) as response:
        final = paper_url(response.geturl())
        raw = bytearray()
        while len(raw) <= MAX_PDF_BYTES:
            if time.monotonic() >= deadline:
                raise TimeoutError("Source download deadline exhausted")
            chunk = response.read(min(65536, MAX_PDF_BYTES + 1 - len(raw)))
            if not chunk:
                break
            raw.extend(chunk)
        headers = {key: response.headers.get(key) for key in ("ETag", "Last-Modified")}
    is_html = urllib.parse.urlsplit(final).path.startswith("/html/")
    if time.monotonic()>=deadline:
        raise TimeoutError("Source download deadline exhausted")
    if len(raw)>MAX_PDF_BYTES or (not is_html and not raw.startswith(b"%PDF-")) or (is_html and b"<html" not in raw[:2000].lower()):
        raise ValueError("Source is not a bounded paper PDF/HTML document")
    return bytes(raw), final, headers


def _extract_pdf(path, deadline):
    # Untrusted PDF parsing is killable and has no model/tool access.
    script = """import json,sys
from pypdf import PdfReader
r=PdfReader(sys.argv[1],strict=False)
if r.is_encrypted or len(r.pages)>32: raise ValueError('Encrypted or too many PDF pages')
pages=[]
for i,p in enumerate(r.pages):
 t=p.extract_text() or ''
 if len(t)>40000: raise ValueError('PDF page text exceeds cap')
 pages.append({'page':i+1,'text':t})
if sum(len(p['text']) for p in pages)>240000: raise ValueError('PDF text exceeds cap')
print(json.dumps(pages))
"""
    remaining = min(6, deadline - time.monotonic())
    if remaining <= 0:
        raise TimeoutError("Source extraction deadline exhausted")
    result = subprocess.run([sys.executable, "-c", script, str(path)], capture_output=True,
                            timeout=remaining, check=False)
    if result.returncode:
        raise ValueError("PDF extraction failed: " + result.stderr.decode(errors="replace")[-500:])
    if len(result.stdout) > 500_000:
        raise ValueError("Extracted PDF output exceeds cap")
    pages = json.loads(result.stdout)
    if not pages or not any(p["text"].strip() for p in pages):
        raise ValueError("PDF contains no accessible text")
    return pages


class _PaperHTML(HTMLParser):
    """Extract complete LaTeXML statement blocks, preserving math alttext."""
    def __init__(self, context_anchors=()):
        super().__init__(convert_charrefs=True)
        self.stack=[];self.parts=[];self.blocks=[];self.active=None;self.math_depth=0;self.full=[]
        self.context_anchors = set(context_anchors)
    def handle_starttag(self,tag,attrs):
        attrs=dict(attrs)
        if tag in {"br","hr","img","meta","link","input","source","wbr"}:
            return
        self.stack.append(tag)
        if len(self.stack)>128:raise ValueError("Primary HTML nesting exceeds bound")
        if tag=="math":
            self.math_depth+=1
            if self.math_depth==1:
                alt=attrs.get("alttext")
                if not alt:
                    if self.active:self.active["math_readable"]=False
                else:self._append(" $"+alt+"$ ")
        classes = attrs.get("class", "").split()
        context = "ltx_para" in classes and attrs.get("id") in self.context_anchors
        if self.active is None and ("ltx_theorem" in classes or context):
            self.active={"depth":len(self.stack),"anchor":attrs.get("id", ""),"math_readable":True,
                         "evidence_kind": "body_context" if context else "body_statement"};self.parts=[]
    def handle_endtag(self,tag):
        if tag in {"br","hr","img","meta","link","input","source","wbr"}:return
        if self.active and self.active["depth"]==len(self.stack):
            text=" ".join("".join(self.parts).split())
            self.blocks.append({"page":len(self.blocks)+1,"text":text,"anchor":self.active["anchor"],
                                "math_readable":self.active["math_readable"],"format":"html",
                                "evidence_kind": self.active["evidence_kind"]})
            self.active=None;self.parts=[]
        if tag=="math":self.math_depth=max(0,self.math_depth-1)
        if self.stack:self.stack.pop()
    def handle_data(self,data):
        if not self.math_depth and not {"script","style"}&set(self.stack):self._append(data)
    def _append(self,text):
        self.full.append(text)
        if self.active:self.parts.append(text)


def _extract_html(raw, context_anchors=()):
    parser=_PaperHTML(context_anchors);parser.feed(raw.decode("utf-8"));parser.close()
    if not parser.blocks or len(parser.blocks)>64 or sum(len(p["text"]) for p in parser.blocks)>240000:
        raise ValueError("No bounded complete primary body statements in HTML")
    return parser.blocks," ".join(parser.full)[:20000]


def _read_pages(directory, entry, paper=None):
    if entry.get("status") != "available":
        raise ValueError(entry.get("error", "Primary source text unavailable"))
    if entry.get("extraction_revision") != EXTRACTION_REVISION:
        raise ValueError("Cached source extraction policy changed; source preparation must refresh")
    if paper is not None and entry.get("context_anchors", []) != paper.get("context_anchors", []):
        raise ValueError("Cached source hypothesis-context selection changed; source preparation must refresh")
    files = []
    root = Path(directory).resolve()
    for key, maximum in (("pdf_path", MAX_PDF_BYTES), ("text_path", 500_000)):
        relative = entry.get(key)
        if not isinstance(relative, str) or Path(relative).is_absolute():
            raise ValueError("Cached source path is not relative")
        path = root / relative
        if path.is_symlink() or not path.resolve().is_relative_to(root) or path.stat().st_size > maximum:
            raise ValueError("Cached source is unsafe or exceeds bound")
        expected = entry["source_sha256" if key == "pdf_path" else "text_file_sha256"]
        if sha256(path) != expected:
            raise ValueError("Cached primary source hash changed")
        files.append(path)
    pages = json.loads(files[1].read_text())
    if (not isinstance(pages, list) or len(pages) > (64 if entry.get("format")=="html" else MAX_PAGES) or any(
            not isinstance(p, dict) or type(p.get("page")) is not int or not isinstance(p.get("text"), str)
            or len(p["text"]) > MAX_PAGE_CHARS for p in pages)):
        raise ValueError("Malformed extracted primary text")
    return pages


def _acquire(paper, directory, deadline, online):
    entry = _load_entry(directory, paper["url"])
    if entry.get("status") == "available":
        try:
            _read_pages(directory, entry, paper)
            return {**entry, **paper}
        except (OSError,ValueError,KeyError,TypeError):
            if not online:
                raise
            entry = {}
    if not online or (entry.get("acquisition_revision") == SOURCE_REVISION and _same_selection(entry, paper)
                      and time.time() < entry.get("retry_at", 0)):
        return entry or {**paper, "status": "unavailable", "error": "Text not cached; offline source preparation"}
    raw, final, headers = _fetch(paper["url"], deadline)
    digest = hashlib.sha256(raw).hexdigest()
    cache = Path(directory) / "novelty_sources"
    if cache.is_symlink():raise ValueError("Source cache directory is a symlink")
    cache.mkdir(parents=True, exist_ok=True)
    is_html = urllib.parse.urlsplit(final).path.startswith("/html/")
    pdf = cache / (digest + (".html" if is_html else ".pdf"))
    if pdf.is_symlink():
        raise ValueError("Cached PDF path is a symlink")
    if pdf.exists() and sha256(pdf) != digest:
        raise ValueError("Existing immutable cached source changed")
    if not pdf.exists():
        temporary = pdf.with_suffix(".pdf.tmp")
        if temporary.is_symlink():
            raise ValueError("Cached temporary path is a symlink")
        temporary.write_bytes(raw)
        temporary.replace(pdf)
    if is_html:
        pages,first = _extract_html(raw, paper.get("context_anchors", []))
    else:
        pages = _extract_pdf(pdf, deadline)
        first = " ".join(p["text"] for p in pages[:2]).lower()
    words = {word for word in re.findall(r"[a-z]{4,}", paper["title"].lower())
             if word not in {"with", "from", "that", "this", "theorem"}}
    first = first.lower()
    if words and len([word for word in words if word in first]) < min(2, len(words)):
        raise ValueError("Extracted paper does not match the provided title identity")
    text_path = cache / (digest + "." + EXTRACTION_REVISION + ".text.json")
    if text_path.is_symlink():
        raise ValueError("Cached extracted text path is a symlink")
    # A new extractor revision gets a new immutable text artifact.
    if text_path.exists() and json.loads(text_path.read_text()) != pages:
        raise ValueError("Existing immutable extracted source changed")
    if not text_path.exists():
        atomic_save_json(pages, text_path)
    entry = {**paper, "status": "available", "final_url": final, "format":"html" if is_html else "pdf", "fetched_at": time.time(),
             "source_sha256": digest, "text_file_sha256": sha256(text_path),
             "extraction_revision": EXTRACTION_REVISION, "acquisition_revision": SOURCE_REVISION,
             "version": headers.get("ETag") or headers.get("Last-Modified") or "SHA256 snapshot " + digest,
             "pdf_path": str(pdf.relative_to(directory)), "text_path": str(text_path.relative_to(directory))}
    atomic_save_json(entry, _entry_path(directory, paper["url"]))
    return entry


def _paper_excerpt(entry, pages, variables, directory):
    terms = (["stopping", "parity", "minimum", "distance", "Theorem", "Definition"] if set(variables) & _CODING
             else [v.replace("_", " ") for v in variables] + ["Theorem", "Lemma", "Proposition"])
    if entry.get("format")=="html":
        eligible=[page for page in pages if page.get("math_readable") and 16<=len(page["text"])<=MAX_EXCERPT_CHARS]
        preferred=entry.get("preferred_anchors",[])
        contexts = entry.get("context_anchors", [])
        required = preferred + contexts
        if required:
            by_anchor = {page.get("anchor"): page for page in eligible}
            missing = [anchor for anchor in required if anchor not in by_anchor]
            if missing:
                raise ValueError("Required complete source statement/context unavailable: " + ", ".join(missing))
            selected = [by_anchor[anchor] for anchor in required]
        else:
            selected=sorted(eligible,key=lambda page:(
                -sum(page["text"].lower().count(term.lower()) for term in terms),page["page"]))[:3]
        if not selected:raise ValueError("No complete bounded HTML statement with readable mathematics")
        return [_statement_source(entry,page,0,page["text"],directory,
                "Complete HTML notation/hypothesis context" if page.get("evidence_kind") == "body_context"
                else "Complete named HTML body statement") for page in selected]
    candidates = []
    pdf_contexts = entry.get("pdf_context_markers", [])
    for page in pages:
        for match in re.finditer(r"(?:^|\n)\s*(Theorem|Proposition|Lemma|Definition|Deﬁnition)\s*(\d+(?:\.\d+)*)[.:]",page["text"]):
            context = page["text"][max(0,match.start()-150):match.start()+2000]
            score = sum(context.lower().count(term.lower()) for term in terms)
            candidates.append((score,-page["page"],-match.start(),page,match))
    if not candidates and not pdf_contexts:
        raise ValueError("No extractable body theorem/proposition/definition located; title or abstract is not theorem evidence")
    preferred = entry.get("preferred_pdf_markers", [])
    if preferred:
        by_marker = {(match[1].replace("Deﬁnition", "Definition") + " " + match[2]): (selected, match)
                     for _, _, _, selected, match in candidates}
        missing = [marker for marker in preferred if marker not in by_marker]
        if missing:
            raise ValueError("Required complete PDF source statements unavailable: " + ", ".join(missing))
        selected_statements = [(marker, *by_marker[marker]) for marker in preferred]
    elif pdf_contexts:
        selected_statements = []  # Registered complete paragraphs, not unrelated page theorems.
    else:
        _, _, _, selected, match = max(candidates, key=lambda item: item[:3])
        selected_statements = [(match[1] + " " + match[2], selected, match)]
    result = []
    for marker, selected, match in selected_statements:
        # Whitespace and PDF glyphs remain exact; even registered paragraph
        # delimiters do not convert PDF text into readable-math certification.
        start = match.start()
        tail = selected["text"][start:]
        explicit_end = entry.get("pdf_end_markers", {}).get(marker)
        pattern = (re.escape(explicit_end) if explicit_end else
                   r"\bProof\s*[:.]|(?:\n\s*(?:Theorem|Proposition|Lemma|Definition|Deﬁnition|Corollary|Remark)\s*\d+(?:\.\d+)*[.:])")
        ending = re.search(pattern, tail[1:])
        if not ending or ending.start() + 1 > MAX_EXCERPT_CHARS:
            raise ValueError("PDF statement extent cannot be bounded completely; use accessible HTML or visual source review")
        text = tail[:ending.start() + 1]
        result.append(_statement_source(entry, selected, start, text, directory, marker))
    for context in pdf_contexts:
        selected = next((page for page in pages if page["page"] == context["page"]), None)
        if selected is None or selected["text"].count(context["start"]) != 1:
            raise ValueError("Required complete PDF context start unavailable or ambiguous")
        start = selected["text"].index(context["start"])
        end = selected["text"].find(context["end"], start + len(context["start"]))
        if end >= 0 and context.get("include_end"):
            end += len(context["end"])
        if end < 0 or end - start > MAX_EXCERPT_CHARS:
            raise ValueError("Required complete PDF context end unavailable or exceeds bound")
        text = selected["text"][start:end]
        result.append(_statement_source(entry, {**selected, "evidence_kind": context.get("evidence_kind", "body_context")},
                                        start, text, directory, context.get("marker", "Complete PDF notation/hypothesis context")))
    return result


def _statement_source(entry,selected,start,text,directory,marker):
    binding = [entry["url"],entry["source_sha256"],selected["page"],start,text]
    source = {"source_id": "primary_" + _digest(binding)[:24], "source_type": "primary_literature", "is_target": False,
        "theorem_id": None, "title": entry["title"], "url": entry["final_url"], "citation": entry.get("citation", ""),
        "locator": "HTML #"+selected["anchor"]+"; complete "+("context" if selected.get("evidence_kind")=="body_context" else "statement") if entry.get("format")=="html" else f"PDF page {selected['page']}; extracted characters {start}–{start+len(text)}",
        "version": entry["version"], "source_path": str((Path(directory)/entry["pdf_path"]).resolve()),
        "source_sha256": entry["source_sha256"], "text_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "cache_path": entry["pdf_path"], "cache_files": [{"path": entry["pdf_path"], "sha256": entry["source_sha256"], "kind": entry.get("format","pdf")},
             {"path": entry["text_path"], "sha256": entry["text_file_sha256"], "kind": "extracted_pages"}],
        "text": text, "page": selected["page"], "excerpt_start": start,
        "evidence_kind": selected.get("evidence_kind", "body_statement"), "statement_marker": marker, "format":entry.get("format","pdf"),
        "topics": entry.get("topics", []), "selection": entry.get("selection", ""),
        "comparison_baselines": entry.get("comparison_baselines", {}).get(selected.get("anchor", marker), []),
        "construction": entry.get("construction"), "comparison_role": entry.get("comparison_role", "unclassified"),
        "extraction_revision": entry.get("extraction_revision"),
        "statement_kind": (re.match(r"\s*(Theorem|Corollary|Proposition|Lemma|Definition|Deﬁnition)\b",text).group(1).replace("Deﬁnition", "Definition").lower()
                           if re.match(r"\s*(Theorem|Corollary|Proposition|Lemma|Definition|Deﬁnition)\b",text) else "unknown"),
        "math_readable": bool(selected.get("math_readable")) if entry.get("format")=="html" else False,
        "extraction_fidelity": "MathML alttext retained" if entry.get("format")=="html" else "PDF extraction may lose mathematical glyphs; verify against original page before a contribution claim",
        "scope": "Actual public research-paper text, untrusted source data; mathematical applicability and hypotheses require comparison. This excerpt does not establish completeness or priority."}
    comparison = entry.get("reviewed_comparison") or {}
    if comparison.get("marker") == marker and comparison.get("source_sha256") == entry["source_sha256"]:
        # Reviewed transcriptions never replace exact extracted source text or
        # turn an unreadable PDF excerpt into a machine-validated quotation.
        image_hash = comparison.get("page_image_sha256")
        if image_hash:
            relative = "novelty_sources/" + entry["source_sha256"] + ".reviewed-page.png"
            image_path = Path(directory) / relative
            if (image_path.is_symlink() or not image_path.resolve().is_relative_to(Path(directory).resolve())
                    or image_path.stat().st_size > MAX_PDF_BYTES or sha256(image_path) != image_hash):
                raise ValueError("Reviewed formula page-image binding failed")
            source["cache_files"].append({"path": relative, "sha256": image_hash, "kind": "reviewed_page_image"})
        source["reviewed_comparison"] = {**comparison,
            "interpretation": "AI-assisted named source comparison for proposal guidance only; not proof assumptions, a verbatim quote, expert endorsement, or originality certification."}
    return source


def _mathlib_review_family(variables):
    """Specific mathematical quantities precede incidental order/degree bridges."""
    variables = set(variables)
    if variables & _CODING:
        return "expander_codes"
    if any("spectral" in name or "eigenvalue" in name or name in {
            "graph_energy", "estrada_index", "algebraic_connectivity", "wilf_bound", "hoffman_bound"}
            for name in variables):
        return "advanced_spectral"  # Existing combined adjacency/Laplacian files.
    if variables & {"chromatic_number", "independence_number", "clique_number"}:
        return "coloring_and_independence"
    if variables & {"diameter", "radius", "girth"}:
        return "metric_topological"
    if "triangle_count" in variables:
        return "extremal_edges_and_triangles"
    return "degree_and_structural_classes"


def pinned_mathlib_sources(theorem, variables):
    """Select actual pinned declarations referenced in the checked target proof."""
    from autonomous_math.conjecturing.model_proposals import _source_declarations, lookup_mathlib_declarations
    receipt = json.loads(Path(theorem["lean_proof"]["receipt_path"]).read_text())
    workspace = receipt.get("workspace") or receipt.get("workspace_path") or receipt.get("workspace_dir")
    if not workspace:
        return [], [{"status": "unavailable", "reason": "Receipt has no pinned workspace location"}]
    family = _mathlib_review_family(variables)
    lookup = lookup_mathlib_declarations({"family": family}, workspace)
    if lookup["status"] == "UNAVAILABLE":
        return [], [{"status": "unavailable", "reason": lookup.get("error", "Pinned Mathlib lookup unavailable")}]
    proof = Path(receipt["source_path"]).read_text()
    target_name = receipt["theorem_name"].split(".")[-1]
    matches = list(re.finditer(r"\btheorem\s+"+re.escape(target_name)+r"(?=\s|[({:])",proof))
    body = proof[matches[-1].start():] if matches else ""
    references = set(re.findall(r"[A-Za-z_][\w'.]*(?:\.[\w']+)+|[A-Za-z_][\w']+", body))
    declarations = []
    for source in lookup["sources"]:
        text = Path(source["source_path"]).read_text()
        for item in _source_declarations(text, list(references)):
            name = item["name"]
            short = name.split(".")[-1]
            used = name in references or any(ref.endswith("." + short) or ref == short for ref in references)
            if not used:
                continue
            lines = text.splitlines(keepends=True)
            line = item["line"]
            header = "".join(lines[line-1:line+14])
            delimiter = re.search(r":=|\bwhere\b",header)
            if not delimiter or delimiter.end()>MAX_EXCERPT_CHARS:
                continue  # Do not supply a declaration clipped in its hypotheses.
            excerpt = header[:delimiter.end()]
            qualifier = name.rsplit(".",1)[0].split(".")[-1]
            exact_qualifier = qualifier in references or any(ref.endswith("."+qualifier) for ref in references)
            rank = 0 if name in references else 1 if exact_qualifier else 2
            declarations.append({"source_id": "mathlib_" + _digest([MATHLIB_PIN, name, source["source_sha256"], excerpt])[:24],
                "source_type": "local_mathlib", "is_target": False, "theorem_id": name, "title": "Pinned Mathlib declaration " + name,
                "url": f"https://github.com/leanprover-community/mathlib4/blob/{MATHLIB_PIN}/{source['mathlib_relative_path']}#L{line}",
                "locator": f"{source['mathlib_relative_path']}:L{line}–L{line+excerpt.count(chr(10))}; {name}",
                "version": MATHLIB_PIN, "source_path": source["source_path"], "source_sha256": source["source_sha256"],
                "text": excerpt, "text_sha256": hashlib.sha256(excerpt.encode()).hexdigest(), "source_context": item["source_context"],
                "declaration_type": item["type"], "declaration_kind": item["kind"],
                "namespace": name.rsplit(".",1)[0] if "." in name else "(root)",
                "reference_match": "literal qualified reference" if rank==0 else "method-name match with source scope; heuristic, not elaborated dependency",
                "_selection_rank": rank,
                "scope": "Literal pinned Mathlib source declaration and implicit-variable context; source inspection is not a new elaboration or priority claim."})
    selected = sorted(declarations, key=lambda item: (item["_selection_rank"],item["declaration_kind"] not in {"theorem","lemma"},item["theorem_id"]))[:3]
    for item in selected:
        item.pop("_selection_rank")
    return selected, []


def targeted_mathlib_sources(record, theorem):
    """Exact registered gap declarations after the existing genuine-pin check."""
    from autonomous_math.conjecturing.model_proposals import _source_declarations, lookup_mathlib_declarations
    topics = {request["topic"] for request in evidence_requests(record, theorem)}
    registry = {
        "degree_empty": {"Mathlib/Combinatorics/SimpleGraph/Finite.lean":
                         ["minDegree_of_subsingleton", "maxDegree_of_subsingleton"]},
        "clique_binary_rank": {"Mathlib/LinearAlgebra/Matrix/Rank.lean": ["rank_submatrix_le"]},
        "independent_edges": {"Mathlib/Combinatorics/SimpleGraph/Finite.lean":
                              ["card_edgeFinset_top_eq_card_choose_two", "edgeFinset_sup", "disjoint_edgeFinset"]},
    }
    requested = {}
    for topic in sorted(topics & registry.keys()):
        for relative, names in registry[topic].items():
            requested.setdefault(relative, set()).update(names)
    if not requested:
        return [], []
    receipt = json.loads(Path(theorem["lean_proof"]["receipt_path"]).read_text())
    workspace = receipt.get("workspace") or receipt.get("workspace_path") or receipt.get("workspace_dir")
    if not workspace:
        return [], [{"status": "unavailable", "reason": "Gap declaration receipt has no pinned workspace location"}]
    verified = lookup_mathlib_declarations({"family": "expander_codes"}, workspace)
    if verified["status"] == "UNAVAILABLE":
        return [], [{"status": "unavailable", "reason": verified.get("error", "Pinned Mathlib gap lookup unavailable")}]
    root = Path(workspace) / ".lake/packages/mathlib"
    sources, unavailable = [], []
    for relative, names in sorted(requested.items()):
        try:
            path = root / relative
            if path.is_symlink() or not path.resolve().is_relative_to(root.resolve()) or path.stat().st_size > 512_000:
                raise ValueError("Registered gap declaration path is unsafe or exceeds bound")
            raw = path.read_bytes()
            text = raw.decode()
            digest = hashlib.sha256(raw).hexdigest()
            declarations = [item for item in _source_declarations(text, sorted(names))
                            if item["name"].rsplit(".", 1)[-1] in names]
            missing = names - {item["name"].rsplit(".", 1)[-1] for item in declarations}
            if missing:
                unavailable.append({"status": "unavailable", "reason": "Pinned declarations not found: " + ", ".join(sorted(missing))})
            for item in declarations:
                line = item["line"]
                header = "".join(text.splitlines(keepends=True)[line - 1:line + 14])
                delimiter = re.search(r":=|\bwhere\b", header)
                if not delimiter or delimiter.end() > MAX_EXCERPT_CHARS:
                    continue
                excerpt = header[:delimiter.end()]
                topic_matches = [topic for topic in sorted(topics & registry.keys())
                                 if item["name"].rsplit(".", 1)[-1] in registry[topic].get(relative, [])]
                sources.append({"source_id": "mathlib_" + _digest([MATHLIB_PIN, item["name"], digest, excerpt])[:24],
                    "source_type": "local_mathlib", "is_target": False, "theorem_id": item["name"],
                    "title": "Pinned Mathlib declaration " + item["name"],
                    "url": f"https://github.com/leanprover-community/mathlib4/blob/{MATHLIB_PIN}/{relative}#L{line}",
                    "locator": f"{relative}:L{line}; {item['name']}", "version": MATHLIB_PIN,
                    "source_path": str(path.resolve()), "source_sha256": digest, "text": excerpt,
                    "text_sha256": hashlib.sha256(excerpt.encode()).hexdigest(), "source_context": item["source_context"],
                    "declaration_type": item["type"], "declaration_kind": item["kind"], "topics": topic_matches,
                    "scope": "Registered exact pinned source signature and variable context for a recorded evidence gap; not an elaboration, theorem-equivalence check or originality certificate."})
        except (OSError, ValueError, KeyError, TypeError) as exc:
            unavailable.append({"status": "unavailable", "reason": str(exc)[:500]})
    return sources[:6], unavailable


def prepare_sources(record, theorem, variables, directory, deadline, online=True, max_fetches=2):
    """Two fetches; reserve five seconds for a final socket read within 20 seconds."""
    deadline = min(deadline, time.monotonic()+15)
    sources, unavailable = pinned_mathlib_sources(theorem, variables)
    extra, failures = targeted_mathlib_sources(record, theorem)
    existing_ids = {source["source_id"] for source in sources}
    sources.extend(source for source in extra if source["source_id"] not in existing_ids)
    unavailable.extend(failures)
    attempted = 0
    for paper in requested_papers(record, variables, theorem):
        entry = _load_entry(directory, paper["url"])
        if entry.get("status") == "available":
            try:
                _read_pages(directory,entry,paper)
            except (OSError,ValueError,KeyError,TypeError):
                entry = {}
        fetch = online and entry.get("status") != "available" and (entry.get("acquisition_revision") != SOURCE_REVISION
            or not _same_selection(entry, paper) or time.time() >= entry.get("retry_at", 0)) and attempted < max_fetches
        attempted += int(fetch)
        try:
            entry = _acquire(paper, directory, deadline, fetch)
            sources.extend(_paper_excerpt(entry, _read_pages(directory, entry), variables, directory))
        except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
            error = str(exc)[:700]
            unavailable.append({"url": paper["url"], "status": "unavailable", "reason": error})
            if fetch:
                atomic_save_json({**paper, "status": "unavailable", "error": error,
                    "acquisition_revision": SOURCE_REVISION, "retry_at": time.time()+FETCH_RETRY_SEC}, _entry_path(directory,paper["url"]))
    coverage = {"local_mathlib": sum(s["source_type"]=="local_mathlib" for s in sources),
                "primary_literature": sum(s["source_type"]=="primary_literature" for s in sources),
                "requested_topics": literature_topics(record, variables, theorem),
                "unregistered_primary_topics": [topic for topic in literature_topics(record, variables, theorem)
                    if not any(topic in paper.get("topics", []) for paper in _PAPERS)],
                "evidence_requests": evidence_requests(record, theorem),
                "unsupplied_evidence_topics": [request["topic"] for request in evidence_requests(record, theorem)
                    if not any(request["topic"] in source.get("topics", []) and
                               source.get("comparison_role") != "different_construction" for source in sources)],
                "unavailable": unavailable, "fetches_attempted": attempted,
                "comparison_gaps": _comparison_gaps(literature_topics(record, variables, theorem)),
                "limitations": ["Curated/allowlisted public source coverage is partial; absence is not evidence of originality.",
                                "Extracted PDF mathematics may be imperfect; exact quotation binds text, not semantic equivalence."]
                               + _spectral_limitations(literature_topics(record, variables, theorem))}
    return {"sources": sources, "coverage": coverage, "revision": SOURCE_REVISION,
            "evidence_key": current_evidence_key(record,theorem,directory)}


def _comparison_gaps(topics):
    if "signless_irregularity" not in topics:
        return []
    return [
        {"title": "On the signless Laplacian spectral radius of irregular graphs", "authors": "Ning, Li and Lu (2013)",
         "url": "https://doi.org/10.1016/j.laa.2012.10.024", "status": "unavailable", "http_status": 403,
         "reason": "Complete connected-irregular theorem text unacquired; abstract is not evidence."},
        {"title": "Signless Laplacian energy and spectral radius of a graph", "authors": "Chen, Liu and Wang",
         "url": "https://papers.ssrn.com/sol3/papers.cfm?abstract_id=5214733", "status": "unavailable", "http_status": 403,
         "reason": "Newer degree/average-2-degree Theorem 2.1 full text inaccessible; not supplied evidence."}]


def _spectral_limitations(topics):
    limitations = []
    if "signless_irregularity" in topics:
        limitations.append("Named newer signless theorem comparison gaps remain incomplete; abstract formulas are not supplied theorem evidence.")
    if "energy_lower_bounds" in topics:
        limitations.append("Stronger energy bounds need second singular value, smallest nonzero absolute eigenvalue, or triangle/quadrangle-free guards. Normalized gap is not a second singular value.")
    return limitations


def prepare_cached_guidance(variables, directory, limit=6, iteration=0):
    """Revalidate bounded complete cached paper groups; never fetch or write."""
    if type(limit) is not int or not 0 <= limit <= 6:
        raise ValueError("Cached literature guidance limit must be between zero and six")
    if type(iteration) is not int or iteration < 0:
        raise ValueError("Cached literature guidance iteration must be nonnegative")
    variables = set(variables)
    topics = literature_topics({}, variables)
    if "parity_code_distance" in variables:
        # The existing proposal iteration gives a small family several complete
        # baselines over successive batches, without increasing its prompt cap.
        priorities = [("griesmer", "singleton", "plotkin"), ("hamming", "stopping", "expander")]
        if "zero_forcing" in topics:
            priorities.append(("zero_forcing",))
        first = [topic for topic in priorities[iteration % len(priorities)] if topic in topics]
        topics = first + [topic for topic in topics if topic not in first]
    payload = {"revision": SOURCE_REVISION, "sources": [], "coverage": {
        "primary_literature": 0, "unavailable": [], "omitted_papers": 0,
        "requested_topics": topics,
        "unregistered_primary_topics": [topic for topic in topics
            if not any(topic in paper.get("topics", []) for paper in _PAPERS)],
        "comparison_gaps": _comparison_gaps(topics),
        "limitations": ["Partial cached primary-paper guidance; relevance and applicability require comparison."]
                       + _spectral_limitations(topics)}}
    # Read the fixed curated corpus so unavailable coverage survives rotation.
    # The number of supplied excerpts remains limited below; no leads are fetched.
    papers = _ranked_papers(topics)
    spectral_priorities = []
    if "signless_irregularity" in topics:
        spectral_priorities.append("Spectral radius minus average degree: a better bound")
    if "energy_lower_bounds" in topics:
        spectral_priorities.extend(["Graph energy estimates via the Chebyshev functional",
                                    "Lectures on Spectral Graph Theory"])
    if "signless_irregularity" in topics:
        spectral_priorities.append("Energies of Hypergraphs")
        spectral_priorities.append("Eigenvalue bounds for the signless Laplacian")
    if "adjacency_edge_envelope" in topics:
        spectral_priorities.extend(["A Bound on the Spectral Radius of Graphs with e Edges", "The Spectral Radius of a Planar Graph"])
    if "signless_clique_cut" in topics:
        spectral_priorities.extend(["A generalization for the clique and independence numbers", "Algebraic connectivity of graphs"])
    if spectral_priorities:
        first = spectral_priorities[iteration % len(spectral_priorities)]
        papers.sort(key=lambda paper: paper["title"] != first)
    for paper in papers:
        try:
            entry = _load_entry(directory, paper["url"])
            pages = _read_pages(directory, entry, paper)
            group = _paper_excerpt({**entry, **paper}, pages, variables, directory)
            keys = {"source_id", "source_type", "title", "url", "citation", "locator", "version",
                    "source_sha256", "text_sha256", "cache_files", "text", "page", "excerpt_start",
                    "evidence_kind", "statement_kind", "math_readable", "topics", "comparison_role", "comparison_baselines",
                    "reviewed_comparison"}
            group = [{key: value for key, value in source.items() if key in keys or
                      (source.get("comparison_role") == "different_construction" and
                       key in {"selection", "construction", "comparison_role"})} for source in group]
            # The statement retains the paper identity. Its complete context
            # records retain exact locators, text, topics and immutable hashes;
            # repeated descriptive metadata must not crowd out full hypotheses.
            if paper.get("comparison_role") == "published_comparison":
                for source in group:
                    if source.get("evidence_kind") == "body_context" and not source.get("comparison_baselines"):
                        for key in ("source_type", "title", "url", "citation", "version", "page", "excerpt_start",
                                    "statement_kind", "comparison_role", "comparison_baselines"):
                            source.pop(key, None)
                        # Both artifact hashes remain on the statement; context
                        # text still binds its source bytes and its own text hash.
                        source["cache_files"] = [item for item in source["cache_files"]
                                                 if item["kind"] != "extracted_pages"]
        except (OSError, ValueError, KeyError, TypeError) as exc:
            payload["coverage"]["unavailable"].append({"url": paper["url"], "reason": str(exc)[:200]})
            continue
        candidate = {**payload, "sources": payload["sources"] + group,
                     "coverage": {**payload["coverage"], "primary_literature": len(payload["sources"]) + len(group)}}
        if len(candidate["sources"]) > limit or len(json.dumps(candidate, sort_keys=True, allow_nan=False).encode()) + 80 > MAX_GUIDANCE_BYTES:
            payload["coverage"]["omitted_papers"] += 1
            continue  # Keep the complete theorem and its field/hypothesis contexts together.
        payload = candidate
    while payload["coverage"]["unavailable"] and len(json.dumps(payload, sort_keys=True, allow_nan=False).encode()) + 80 > MAX_GUIDANCE_BYTES:
        payload["coverage"]["unavailable"].pop()
        payload["coverage"]["omitted_papers"] += 1
    payload["sha256"] = _digest(payload)
    return payload
