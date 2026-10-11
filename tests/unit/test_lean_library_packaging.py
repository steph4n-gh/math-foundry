"""Generated library bindings must fail closed without invoking Lean or AI."""
import hashlib
import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("package_lean_library", ROOT / "scripts/package_lean_library.py")
package = importlib.util.module_from_spec(spec)
spec.loader.exec_module(package)


@pytest.fixture
def library(tmp_path):
    catalog = json.loads((ROOT / "results/catalog.json").read_text())
    catalog["records"] = [r for r in catalog["records"] if r["id"] in package.FOUNDATIONS]
    for record in catalog["records"]:
        for kind in ("source", "challenge"):
            p = tmp_path / record[kind + "_path"]
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes((ROOT / record[kind + "_path"]).read_bytes())
    (tmp_path / "results/catalog.json").write_text(json.dumps(catalog))
    for path, text in package.expected_files(tmp_path).items():
        p = tmp_path / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    return tmp_path


def test_imports_and_complete_body_remain_verbatim(library):
    manifest = json.loads((library / package.MANIFEST).read_text())
    assert package.check(library) == 8
    for record in manifest["records"]:
        source = (library / record["source_path"]).read_bytes()
        wrapped = (library / record["module_path"]).read_bytes()
        namespace = record["module"].encode()
        before, body = wrapped.split(b"\nnamespace " + namespace + b"\n", 1)
        body = body.removesuffix(b"\nend " + namespace + b"\n")
        prefix = before[before.index(b"import "):]
        assert prefix + body == source


def test_changed_module_cannot_be_hidden_by_rehashing_manifest(library):
    p = library / package.MANIFEST
    manifest = json.loads(p.read_text())
    row = manifest["records"][-1]
    module = library / row["module_path"]
    module.write_text(module.read_text().replace("namespace " + row["module"],
                                              "namespace Unbound"))
    row["module_sha256"] = hashlib.sha256(module.read_bytes()).hexdigest()
    p.write_text(json.dumps(manifest, indent=2) + "\n")
    with pytest.raises(ValueError, match="changed generated"):
        package.check(library)


@pytest.mark.parametrize("path", ["Archive/stale.lean", "Archive/nested/extra.lean", "Unexpected.lean"])
def test_extra_modules_are_not_silently_admitted(library, path):
    p = library / "certified_lean/MathFoundry" / path
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("axiom unsupported : False\n")
    with pytest.raises(ValueError, match="coverage differs"):
        package.check(library)


@pytest.mark.parametrize("ancestor", ["certified_lean", "certified_lean/MathFoundry", "certified_lean/MathFoundry/Archive"])
def test_output_cannot_follow_symlinked_ancestor(tmp_path, ancestor):
    outside = tmp_path / "outside"
    outside.mkdir()
    root = tmp_path / "checkout"
    root.mkdir()
    p = root / ancestor
    p.parent.mkdir(parents=True, exist_ok=True)
    p.symlink_to(outside, target_is_directory=True)
    with pytest.raises(ValueError, match="symlinked output"):
        package.output_path(root, "certified_lean/MathFoundry/Archive/proof.lean")
    assert not list(outside.iterdir())


@pytest.mark.parametrize("command", ["end Escape", "axiom bad : False", "namespace Escape", "set_option maxRecDepth 0", "import Mathlib", "  end Escape", "  axiom bad : False", "  namespace Escape"])
def test_namespace_sensitive_future_sources_fail_closed(command):
    source = "import Mathlib\ntheorem valid : True := by trivial\n" + command + "\n"
    with pytest.raises(ValueError):
        package.wrap_source(source, "valid", "results/proofs/x.lean", "0" * 64)


@pytest.mark.parametrize("name", ["a.b", "a-b", "../escape", "«x»"])
def test_unsanitized_module_name_is_rejected(name):
    with pytest.raises(ValueError, match="sanitized"):
        package.wrap_source("import Mathlib\ntheorem valid : True := by trivial\n", name, "x.lean", "0" * 64)
