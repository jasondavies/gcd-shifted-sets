"""Check the pinned sources and their closure outside Mathlib and Batteries."""

import hashlib
import json
from pathlib import Path
import re


root = Path(__file__).resolve().parents[1] / "vendor" / "jacobsthal"
manifest = json.loads((root / "UPSTREAM.json").read_text())
expected = manifest["files"]
actual = {str(p.relative_to(root)) for p in root.rglob("*.lean") if ".lake" not in p.parts}
if actual != set(expected):
    raise SystemExit(f"Source set mismatch: missing={set(expected) - actual}, extra={actual - set(expected)}")

for filename, digest in expected.items():
    if hashlib.sha256((root / filename).read_bytes()).hexdigest() != digest:
        raise SystemExit(f"Source hash mismatch: {filename}")

visited = set()


def visit(module):
    if module == "Mathlib" or module.startswith(("Mathlib.", "Batteries.")):
        return
    filename = module.replace(".", "/") + ".lean"
    if filename in visited:
        return
    if filename not in expected:
        raise SystemExit(f"Unrecorded dependency: {module}")
    visited.add(filename)
    for dependency in re.findall(r"^import\s+(\S+)", (root / filename).read_text(), re.MULTILINE):
        visit(dependency)


visit(manifest["entrypoint"])
if visited != set(expected):
    raise SystemExit(f"Files outside the dependency closure: {set(expected) - visited}")
print(f"Verified {len(expected)} source hashes and the exact Jacobsthal dependency closure.")
