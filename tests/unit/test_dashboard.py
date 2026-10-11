"""Unit and Integration Tests for Interactive Visual Dashboard.

Validates:
- DashboardDataService telemetry aggregation from cumulative atlas and master catalog.
- Theorem filtering and search across tags, novelty status, and guards.
- Counterexample extraction and canonical graph topology schemas (C5, Petersen, etc.).
- 2D and 3D multi-invariant point cloud and convex hull computation.
- Lean 4 code and proof script retrieval.
- Standalone HTTP server REST API and static UI serving.
"""

from __future__ import annotations

import json
from pathlib import Path
import urllib.request
import numpy as np
import pytest

from autonomous_math.dashboard.data_service import DashboardDataService
from autonomous_math.dashboard.server import run_dashboard, find_free_port
from autonomous_math.cli.main import build_parser, main


def test_dashboard_telemetry_aggregation():
    """Verify live discovery telemetry metrics are correctly calculated."""
    ds = DashboardDataService()
    telemetry = ds.get_telemetry()

    assert "total_conjectures" in telemetry
    assert "total_survived" in telemetry
    assert "total_refuted" in telemetry
    assert "total_rediscoveries" in telemetry
    assert "total_novel" in telemetry
    assert "total_lean_certified" in telemetry
    assert "active_flywheel_lemmas" in telemetry
    assert telemetry["catalog_graphs"] >= telemetry["base_catalog_graphs"]
    assert telemetry["catalog_graphs"] == telemetry["base_catalog_graphs"] + telemetry["replayed_boundary_graphs"]
    assert telemetry["invariants_tracked"] >= 20


def test_dashboard_theorems_query_and_filtering():
    """Verify theorem filtering by status and text search."""
    ds = DashboardDataService()

    all_thms = ds.get_theorems(filter_type="ALL")
    assert len(all_thms) > 0

    lean_thms = ds.get_theorems(filter_type="LEAN_CERTIFIED")
    assert all(t.get("lean_proof") is not None or t.get("status") == "LEAN_CERTIFIED" for t in lean_thms)

    novel_thms = ds.get_theorems(filter_type="CANDIDATE_NOVEL")
    assert all(t.get("novelty_status") == "UNKNOWN_IN_LITERATURE" for t in novel_thms)

    # Search filtering
    searched = ds.get_theorems(query="spectral_radius")
    assert all("spectral_radius" in t.get("statement", "").lower() or "spectral_radius" in t.get("id", "").lower() for searched_t in searched for t in [searched_t])


def test_dashboard_counterexamples():
    """Verify counterexample schemas, invariants, and graph topology dictionaries."""
    ds = DashboardDataService()
    cxs = ds.get_counterexamples()

    assert len(cxs) >= 4  # At least canonical C5, Petersen, K33, Star K14
    cx_ids = [c["id"] for c in cxs]
    assert "cycle_5" in cx_ids
    assert "petersen_graph" in cx_ids

    c5 = next(c for c in cxs if c["id"] == "cycle_5")
    assert c5["order"] == 5
    assert c5["size"] == 5
    assert len(c5["nodes"]) == 5
    assert len(c5["edges"]) == 5

    petersen = next(c for c in cxs if c["id"] == "petersen_graph")
    assert petersen["order"] == 10
    assert petersen["size"] == 15
    assert len(petersen["nodes"]) == 10
    assert len(petersen["edges"]) == 15


def test_dashboard_pointcloud_2d_and_3d():
    """Verify 2D and 3D invariant point clouds and convex hull facets."""
    ds = DashboardDataService()

    # 2D Pointcloud
    pc2 = ds.get_pointcloud(x_inv="max_degree", y_inv="spectral_radius")
    assert pc2["x_axis"] == "max_degree"
    assert pc2["y_axis"] == "spectral_radius"
    assert pc2["total_points"] == 1352
    assert len(pc2["points"]) == 1352
    assert len(pc2["hull_indices"]) >= 3
    assert len(pc2["hull_simplices"]) >= 3

    # 3D Pointcloud
    pc3 = ds.get_pointcloud(x_inv="max_degree", y_inv="spectral_radius", z_inv="chromatic_number")
    assert pc3["z_axis"] == "chromatic_number"
    assert pc3["total_points"] == 1352
    assert "z" in pc3["points"][0]
    assert len(pc3["hull_simplices"]) >= 4


def test_dashboard_pointcloud_decimation_above_2000(monkeypatch, tmp_path):
    """Verify that when instance count > 2000, points are downsampled to <= 2000 while preserving all hull indices."""
    from autonomous_math.sieve.instance_db import InstanceDatabase

    # Create mock matrix with 3,000 points
    n = 3000
    rng = np.random.default_rng(42)
    mock_matrix = {
        "max_degree": rng.uniform(1.0, 10.0, size=n),
        "spectral_radius": rng.uniform(0.5, 9.5, size=n),
    }

    monkeypatch.setattr(InstanceDatabase, "_cached_matrix", mock_matrix)

    ds = DashboardDataService(data_dir=tmp_path)
    pc = ds.get_pointcloud(x_inv="max_degree", y_inv="spectral_radius")

    assert len(pc["points"]) == 2000
    assert pc["total_points"] == 2000
    assert len(pc["hull_indices"]) >= 3

    # Strictly verify that EVERY index in hull_indices is preserved in points
    returned_point_ids = {p["id"] for p in pc["points"]}
    for h_idx in pc["hull_indices"]:
        assert h_idx in returned_point_ids

    # 3D Decimation test
    mock_matrix_3d = {
        "max_degree": rng.uniform(1.0, 10.0, size=n),
        "spectral_radius": rng.uniform(0.5, 9.5, size=n),
        "chromatic_number": rng.uniform(1.0, 5.0, size=n),
    }
    monkeypatch.setattr(InstanceDatabase, "_cached_matrix", mock_matrix_3d)
    pc3 = ds.get_pointcloud(x_inv="max_degree", y_inv="spectral_radius", z_inv="chromatic_number")
    assert len(pc3["points"]) == 2000
    assert pc3["total_points"] == 2000
    assert len(pc3["hull_indices"]) >= 4
    assert "z" in pc3["points"][0]
    returned_3d_ids = {p["id"] for p in pc3["points"]}
    for h_idx in pc3["hull_indices"]:
        assert h_idx in returned_3d_ids


def test_dashboard_lean_code_retrieval():
    """Verify retrieval of verified Lean 4 code."""
    ds = DashboardDataService()
    res = ds.get_lean_code("collatz_sinogowitz_bound")
    assert "theorem_id" in res
    assert "code" in res


def test_dashboard_http_server_endpoints():
    """Launch dashboard HTTP server in background thread and test REST endpoints."""
    port = find_free_port(8950)
    server = run_dashboard(port=port, block=False)

    base_url = f"http://127.0.0.1:{port}"
    try:
        # 1. UI Root
        with urllib.request.urlopen(f"{base_url}/") as resp:
            assert resp.status == 200
            html = resp.read().decode("utf-8")
            assert "<!doctype html>" in html.lower()
            assert "Autonomous Math" in html

        # 2. Telemetry API
        with urllib.request.urlopen(f"{base_url}/api/telemetry") as resp:
            assert resp.status == 200
            data = json.loads(resp.read().decode("utf-8"))
            assert "total_conjectures" in data
            assert data["catalog_graphs"] == data["base_catalog_graphs"] + data["replayed_boundary_graphs"]

        # 3. Theorems API
        with urllib.request.urlopen(f"{base_url}/api/theorems?filter=ALL") as resp:
            assert resp.status == 200
            data = json.loads(resp.read().decode("utf-8"))
            assert "theorems" in data
            assert isinstance(data["theorems"], list)

        # 4. Counterexamples API
        with urllib.request.urlopen(f"{base_url}/api/counterexamples") as resp:
            assert resp.status == 200
            data = json.loads(resp.read().decode("utf-8"))
            assert "counterexamples" in data

        # 5. Pointcloud API
        with urllib.request.urlopen(f"{base_url}/api/pointcloud?x=max_degree&y=spectral_radius") as resp:
            assert resp.status == 200
            data = json.loads(resp.read().decode("utf-8"))
            assert data["total_points"] == 1352

        # 6. Flywheel API
        with urllib.request.urlopen(f"{base_url}/api/flywheel") as resp:
            assert resp.status == 200
            data = json.loads(resp.read().decode("utf-8"))
            assert "lemmas" in data or "total_active_lemmas" in data

        # 7. Mathlib Bridge API
        with urllib.request.urlopen(f"{base_url}/api/mathlib_bridge") as resp:
            assert resp.status == 200
            data = json.loads(resp.read().decode("utf-8"))
            assert "type_alignment" in data
            assert "canonical_aliases" in data
            assert "canonical_lemma_bridges" in data
            assert "spectral_energy_extensions" in data
    finally:
        server.shutdown()


def test_dashboard_mathlib_bridge_info():
    """Verify Mathlib 4 architectural alignment and canonical bridge info."""
    ds = DashboardDataService()
    info = ds.get_mathlib_bridge_info()
    assert "type_alignment" in info
    assert "canonical_aliases" in info
    assert "canonical_lemma_bridges" in info
    assert "spectral_energy_extensions" in info
    assert info["spectral_energy_extensions"]["status"] == "NATIVE_MATHLIB_DEFINITIONS"
    assert "graph_energy" in info["supported_invariants"]
    assert "is_bipartite" in info["supported_properties"]
    assert "clique_number" in info["supported_invariants"]
    assert Path(info["workspace"]).name == "certified_lean"
    assert not info["canonical_aliases"]


def test_dashboard_cli_parser():
    """Verify CLI parser recognizes `dashboard` subcommand and flags."""
    parser = build_parser()
    args = parser.parse_args(["dashboard", "--port", "8888", "--host", "0.0.0.0"])
    assert args.subcommand == "dashboard"
    assert args.port == 8888
    assert args.host == "0.0.0.0"
