"""Unit and Integration Tests for Daemon Signal Handling, Indefinite Execution & Checkpointing.

Validates:
- atomic_save_json creates atomic checkpoints without file corruption.
- GracefulDaemonInterrupt catches SIGINT/SIGTERM cleanly and sets stop_requested.
- run_continuous_daemon executes and gracefully checkpoints cumulative discovery atlas.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import signal
import time
import pytest

from run_research import (
    GracefulDaemonInterrupt,
    atomic_save_json,
    run_continuous_daemon,
)


def test_atomic_save_json(tmp_path: Path):
    """Verify that atomic_save_json creates files atomically with correct content."""
    target_file = tmp_path / "nested" / "test_data.json"
    payload = {"status": "ok", "items": [1, 2, 3], "timestamp": 12345.67}

    atomic_save_json(payload, target_file)

    assert target_file.is_file()
    loaded = json.loads(target_file.read_text(encoding="utf-8"))
    assert loaded == payload

    # Verify atomic update
    payload["status"] = "updated"
    atomic_save_json(payload, target_file)
    loaded2 = json.loads(target_file.read_text(encoding="utf-8"))
    assert loaded2["status"] == "updated"

    # Verify no stray temporary files in directory
    files = list(target_file.parent.iterdir())
    assert len(files) == 1
    assert files[0].name == "test_data.json"


def test_graceful_interrupt_handler():
    """Verify GracefulDaemonInterrupt installs, records signals, and uninstalls cleanly."""
    handler = GracefulDaemonInterrupt()
    assert handler.stop_requested is False

    handler.install()
    try:
        # Simulate SIGINT signal delivery
        handler._handler(signal.SIGINT, None)
        assert handler.stop_requested is True
    finally:
        handler.uninstall()


def test_continuous_daemon_graceful_execution(tmp_path: Path):
    """Verify run_continuous_daemon runs, updates atlas, and saves atomic checkpoints."""
    out_dir = tmp_path / "daemon_output"
    atlas = run_continuous_daemon(
        output_dir=out_dir,
        max_iterations=1,
        timeout_sec=90.0,
        limit_per_pair=1,
        limit_per_triad=1,
        max_lean_targets=1,
        proof_backend="none",
    )

    assert atlas["total_iterations"] >= 1
    assert (out_dir / "cumulative_discovery_atlas.json").is_file()
    assert "active_flywheel_lemmas" in atlas or "active_flywheel_lemmas_count" in atlas or "theorems" in atlas

    # Verify content of atlas file
    saved_atlas = json.loads((out_dir / "cumulative_discovery_atlas.json").read_text(encoding="utf-8"))
    assert saved_atlas["total_iterations"] >= 1
    assert len(saved_atlas["theorems"]) > 0


def test_continuous_daemon_stop_requested_early_break(tmp_path: Path, monkeypatch):
    """Verify daemon halts cleanly when interrupt stop is requested."""
    out_dir = tmp_path / "daemon_interrupt_test"

    # Simulate interrupt handler requesting stop immediately
    def mock_install(self):
        self.stop_requested = True

    monkeypatch.setattr(GracefulDaemonInterrupt, "install", mock_install)

    atlas = run_continuous_daemon(
        output_dir=out_dir,
        max_iterations=10,
        timeout_sec=90.0,
        limit_per_pair=1,
        limit_per_triad=1,
        max_lean_targets=1,
        proof_backend="none",
    )

    assert (out_dir / "cumulative_discovery_atlas.json").is_file()
    assert atlas["total_iterations"] == 0
