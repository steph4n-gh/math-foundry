"""Local theorem matching and evidence-bound originality review.

Registry comparisons and scholarly metadata support review; neither an
unmatched statement nor successful Lean verification establishes novelty.
"""

from autonomous_math.novelty.literature_crosscheck import (
    KnownTheorem,
    KnownTheoremRegistry,
    LiteratureCrossChecker,
    LiteratureMatch,
    NoveltyReport,
    NoveltyStatus,
)

__all__ = [
    "KnownTheorem",
    "KnownTheoremRegistry",
    "LiteratureCrossChecker",
    "LiteratureMatch",
    "NoveltyReport",
    "NoveltyStatus",
]
