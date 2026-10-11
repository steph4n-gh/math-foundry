#!/usr/bin/env python3
"""Launch the Autonomous Mathematical Research Web Dashboard.

Provides an interactive visual dashboard for exploring live discovery telemetry,
searchable theorem catalogs, machine-checked Lean 4 proof artifacts, counterexample
certificates, and interactive 2D/3D invariant convex hull manifolds.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import sys

# Ensure repository root is on sys.path
REPO_ROOT = Path(__file__).resolve().parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from autonomous_math.dashboard.server import run_dashboard


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Autonomous Math Discovery Interactive Web Dashboard"
    )
    parser.add_argument(
        "--port",
        "-p",
        type=int,
        default=8050,
        help="Port to serve the dashboard web application on (default: 8050)",
    )
    parser.add_argument(
        "--host",
        type=str,
        default="127.0.0.1",
        help="Host address to bind the dashboard web server (default: 127.0.0.1)",
    )
    parser.add_argument("--output-dir", type=Path, default=REPO_ROOT / "research_outputs")
    args = parser.parse_args()

    run_dashboard(port=args.port, host=args.host, block=True, data_dir=args.output_dir)


if __name__ == "__main__":
    main()
