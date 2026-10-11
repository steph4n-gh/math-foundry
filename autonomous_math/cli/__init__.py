"""Command Line Interface (CLI) module for autonomous_math pipeline."""

from __future__ import annotations

from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from autonomous_math.cli.demo import run_demo
    from autonomous_math.cli.main import main


def __getattr__(name: str) -> Any:
    if name == "main":
        from autonomous_math.cli.main import main
        return main
    if name == "run_demo":
        from autonomous_math.cli.demo import run_demo
        return run_demo
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")


__all__ = ["main", "run_demo"]
