"""Standalone Web Dashboard Server for Autonomous Mathematical Discovery.

Serves a responsive dark research console with
live discovery telemetry, searchable theorem explorer, Lean 4 code/proof viewer,
counterexample inspector, and interactive 2D/3D invariant convex hull visualizer.
"""

from __future__ import annotations

import http.server
import json
import logging
from pathlib import Path
import socket
import sys
import threading
import time
from typing import Any, Dict, Optional
from urllib.parse import parse_qs, urlparse, unquote
from autonomous_math.research_state import json_safe

from autonomous_math.dashboard.data_service import DashboardDataService, API_LOCK

logger = logging.getLogger("dashboard.server")

STATIC_DIR = Path(__file__).resolve().parent / "static"


class DashboardRequestHandler(http.server.BaseHTTPRequestHandler):
    """HTTP Request Handler providing REST API and static UI delivery."""

    data_service: DashboardDataService

    def do_HEAD(self) -> None:
        self.send_response(200)
        self.end_headers()

    def do_GET(self) -> None:
        if urlparse(self.path).path.startswith("/api/"):
            with API_LOCK:
                self._handle_get()
        else:
            self._handle_get()

    def _handle_get(self) -> None:
        parsed_url = urlparse(self.path)
        path = parsed_url.path
        query_params = parse_qs(parsed_url.query)

        try:
            # REST API Routing
            if path == "/api/snapshot":
                self._send_json(self.data_service.get_snapshot())
            elif path == "/api/telemetry":
                self._send_json(self.data_service.get_telemetry())
            elif path == "/api/theorems":
                filter_type = query_params.get("filter", ["ALL"])[0]
                q = query_params.get("q", [""])[0]
                guard = query_params.get("guard", [None])[0]
                res = self.data_service.get_theorems(filter_type=filter_type, query=q, guard=guard)
                self._send_json({"theorems": res, "count": len(res)})
            elif path == "/api/novelty_reviews":
                self._send_json(self.data_service.get_novelty_reviews())
            elif path.startswith("/api/lean_code/"):
                thm_id = unquote(path[len("/api/lean_code/"):])
                res = self.data_service.get_lean_code(thm_id)
                self._send_json(res)
            elif path.startswith("/api/research_packet/"):
                thm_id = unquote(path[len("/api/research_packet/"):])
                res = self.data_service.get_research_packet(thm_id)
                self._send_json(res, status=200 if res.get("found") else 404)
            elif path == "/api/counterexamples":
                self._send_json({"counterexamples": self.data_service.get_counterexamples()})
            elif path == "/api/pointcloud":
                x_inv = query_params.get("x", ["max_degree"])[0]
                y_inv = query_params.get("y", ["spectral_radius"])[0]
                z_inv = query_params.get("z", [None])[0]
                res = self.data_service.get_pointcloud(x_inv=x_inv, y_inv=y_inv, z_inv=z_inv)
                self._send_json(res)
            elif path == "/api/flywheel":
                self._send_json(self.data_service.get_flywheel_status())
            elif path == "/api/mathlib_bridge":
                self._send_json(self.data_service.get_mathlib_bridge_info())
            elif path in ("/", "/index.html"):
                self._serve_static_index()
            else:
                # Check for static file
                safe_path = (STATIC_DIR / path.lstrip("/")).resolve()
                if safe_path.is_file() and safe_path.is_relative_to(STATIC_DIR.resolve()):
                    self._serve_file(safe_path)
                else:
                    self._serve_static_index()
        except Exception as e:
            logger.error(f"Error serving GET {path}: {e}", exc_info=True)
            self._send_json({"error": str(e)}, status=500)

    def _send_json(self, data: Any, status: int = 200) -> None:
        """Send JSON response with UTF-8 encoding and CORS headers."""
        payload = json.dumps(json_safe(data), indent=2, allow_nan=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(payload)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Cache-Control", "no-cache, no-store, must-revalidate")
        self.end_headers()
        self.wfile.write(payload)

    def _serve_static_index(self) -> None:
        """Serve index.html from static folder."""
        index_file = STATIC_DIR / "index.html"
        if not index_file.is_file():
            self._send_json({"error": "Dashboard UI index.html not found"}, status=404)
            return
        payload = index_file.read_bytes()
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def _serve_file(self, file_path: Path) -> None:
        """Serve static asset with appropriate content type."""
        content_type = "text/plain"
        if file_path.suffix == ".html":
            content_type = "text/html; charset=utf-8"
        elif file_path.suffix == ".css":
            content_type = "text/css; charset=utf-8"
        elif file_path.suffix == ".js":
            content_type = "application/javascript; charset=utf-8"
        elif file_path.suffix == ".json":
            content_type = "application/json; charset=utf-8"
        elif file_path.suffix == ".svg":
            content_type = "image/svg+xml"

        payload = file_path.read_bytes()
        self.send_response(200)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def log_message(self, format: str, *args: Any) -> None:
        """Silence default verbose HTTP server access logs."""
        pass


def find_free_port(start_port: int = 8050) -> int:
    """Find an open TCP port starting from start_port."""
    for port in range(start_port, start_port + 50):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            if s.connect_ex(("127.0.0.1", port)) != 0:
                return port
    return start_port


def run_dashboard(
    port: int = 8050,
    host: str = "127.0.0.1",
    block: bool = True,
    data_dir: Optional[Path] = None,
) -> http.server.ThreadingHTTPServer:
    """Launch the autonomous mathematical discovery web dashboard."""
    actual_port = port
    server_address = (host, actual_port)
    server_type = type("ResearchHTTPServer", (http.server.ThreadingHTTPServer,), {"request_queue_size": 32})
    httpd = server_type(server_address, type("RunRequestHandler", (DashboardRequestHandler,), {"data_service": DashboardDataService(data_dir=data_dir)}))
    actual_port = httpd.server_port

    url = f"http://{host}:{actual_port}"
    print("\n" + "=" * 80)
    print(f"  AUTONOMOUS MATHEMATICAL RESEARCH DASHBOARD ONLINE")
    print(f"  URL: {url}")
    print(f"  Telemetry: {url}/api/telemetry")
    print(f"  Theorems:  {url}/api/theorems")
    print(f"  Press Ctrl+C to stop server.")
    print("=" * 80 + "\n")

    if block:
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("\n[DASHBOARD] Stopping web server...")
            httpd.shutdown()
            httpd.server_close()
            print("[DASHBOARD] Web server stopped cleanly.")
    else:
        t = threading.Thread(target=httpd.serve_forever, daemon=True)
        t.start()

    return httpd


if __name__ == "__main__":
    port_arg = 8050
    if len(sys.argv) > 1:
        try:
            port_arg = int(sys.argv[1])
        except ValueError:
            pass
    run_dashboard(port=port_arg)
