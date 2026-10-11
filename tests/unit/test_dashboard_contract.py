"""Data contracts that keep the dashboard's visual evidence faithful."""
import json
from concurrent.futures import ThreadPoolExecutor
from urllib.request import urlopen

import networkx as nx
import numpy as np
import pytest

from autonomous_math.core.ast import Conjecture, ConstantNode, InvariantNode
from autonomous_math.dashboard.data_service import DashboardDataService
from autonomous_math.research_state import atomic_save_json
from autonomous_math.sieve.certificates import CounterexampleCertificate


def test_pointcloud_excludes_undefined_coordinates_without_renumbering(monkeypatch, tmp_path):
    import autonomous_math.sieve.instance_db as instance_db

    class Catalog:
        _cached_matrix = {
            "max_degree": np.array([0, np.nan, 1, 0, np.inf]),
            "spectral_radius": np.array([0, 90, 0, 1, 2]),
        }

    monkeypatch.setattr(instance_db, "InstanceDatabase", Catalog)
    result = DashboardDataService(data_dir=tmp_path).get_pointcloud()
    assert result["excluded_undefined_points"] == 2
    by_id = {point["id"]: point for point in result["points"]}
    assert set(by_id) == {0, 2, 3}
    assert {(p["x"], p["y"]) for p in by_id.values()} == {(0, 0), (1, 0), (0, 1)}
    assert set(result["hull_indices"]) == set(by_id)
    assert all(set(facet) <= set(by_id) for facet in result["hull_simplices"])
    json.dumps(result, allow_nan=False)


def test_empty_refutation_is_preserved_as_an_empty_graph():
    conjecture = Conjecture.create(id="empty_counterexample", lhs=ConstantNode(1), rel="<=", rhs=ConstantNode(0))
    certificate = CounterexampleCertificate.from_counterexample_graph(nx.empty_graph(0), conjecture)
    atlas = {"theorems": {conjecture.id: {
        "id": conjecture.id, "statement": conjecture.to_latex(),
        "conjecture": conjecture.to_dict(), "counterexample": certificate.to_dict(),
    }}}
    rows = DashboardDataService().get_counterexamples(atlas)
    row = next(row for row in rows if row["id"] == conjecture.id)
    assert row["family"] == "Verified refutation"
    assert row["order"] == row["size"] == 0
    assert row["nodes"] == row["edges"] == []


def test_reference_topologies_are_labeled_and_exact():
    rows = DashboardDataService().get_counterexamples({"theorems": {}})
    for row in rows:
        assert row["family"] == "Reference graph"
        assert "not a discovery certificate" in row["description"]
        graph = nx.Graph()
        graph.add_nodes_from(row["nodes"])
        graph.add_edges_from(row["edges"])
        assert graph.number_of_nodes() == row["order"]
        assert graph.number_of_edges() == row["size"]
    petersen = next(row for row in rows if row["id"] == "petersen_graph")
    assert petersen["order"] == 10 and petersen["size"] == 15


def test_dead_runner_is_stale_not_running(tmp_path, monkeypatch):
    import autonomous_math.dashboard.data_service as data_service
    import autonomous_math.sieve.instance_db as instance_db

    class Catalog:
        _cached_gi = []
        _cached_matrix = {}

    def dead_process(_pid, _signal):
        raise ProcessLookupError("process is gone")

    monkeypatch.setattr(instance_db, "InstanceDatabase", Catalog)
    monkeypatch.setattr(data_service.os, "kill", dead_process)
    (tmp_path / "run_status.json").write_text(json.dumps({"state": "running", "pid": 12, "heartbeat": 1}))
    telemetry = DashboardDataService(data_dir=tmp_path).get_telemetry({"theorems": {}})
    assert telemetry["runner"]["state"] == "stale"
    assert telemetry["data_state"] == "missing"
    assert telemetry["timestamp"] is None


def test_cached_refutation_does_not_accept_changed_certificate():
    conjecture = Conjecture.create(id="cache_counterexample", lhs=InvariantNode("order"), rel="<=", rhs=ConstantNode(0))
    certificate = CounterexampleCertificate.from_counterexample_graph(nx.path_graph(3), conjecture)
    atlas = {"theorems": {conjecture.id: {
        "id": conjecture.id, "statement": conjecture.to_latex(),
        "conjecture": conjecture.to_dict(), "counterexample": certificate.to_dict(),
    }}}
    service = DashboardDataService()
    assert len(service.get_counterexamples(atlas)) == 5
    atlas["theorems"][conjecture.id]["counterexample"]["edges"] = []
    with pytest.raises(ValueError, match="Invalid counterexample"):
        service.get_counterexamples(atlas)


def test_parallel_snapshot_requests_return_consistent_verified_graphs(tmp_path, monkeypatch):
    import autonomous_math.sieve.instance_db as instance_db
    from autonomous_math.dashboard.server import run_dashboard

    class Catalog:
        _cached_gi = []
        _cached_matrix = {}

    monkeypatch.setattr(instance_db, "InstanceDatabase", Catalog)
    # A wheel is nonbipartite, so independence evaluation reaches the Z3
    # optimization path instead of the bipartite matching shortcut.
    graph = nx.wheel_graph(6)
    conjecture = Conjecture.create(id="parallel_refutation", lhs=InvariantNode("independence_number"), rel="<=", rhs=ConstantNode(0))
    certificate = CounterexampleCertificate.from_counterexample_graph(graph, conjecture)
    atomic_save_json({"theorems": {conjecture.id: {
        "id": conjecture.id, "statement": conjecture.to_latex(), "status": "REFUTED",
        "conjecture": conjecture.to_dict(), "counterexample": certificate.to_dict(),
    }}}, tmp_path / "cumulative_discovery_atlas.json")
    server = run_dashboard(port=0, block=False, data_dir=tmp_path)
    try:
        def snapshot(_):
            with urlopen(f"http://127.0.0.1:{server.server_port}/api/snapshot", timeout=10) as response:
                return json.loads(response.read())

        with ThreadPoolExecutor(max_workers=6) as pool:
            responses = list(pool.map(snapshot, range(12)))
        for response in responses:
            row = next(row for row in response["counterexamples"] if row["id"] == conjecture.id)
            assert row["nodes"] == list(graph)
            assert {tuple(edge) for edge in row["edges"]} == set(graph.edges())
            assert response["telemetry"]["total_lean_certified"] == 0
    finally:
        server.shutdown()
        server.server_close()
