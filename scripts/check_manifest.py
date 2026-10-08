#!/usr/bin/env python3
"""Check `manifest.json` against the Lean development.

* every `lean_path` exists;
* every name in `target_theorems` is a declaration of the built project;
* `Kuramoto.main_theorem` depends on exactly the axioms listed in the manifest, plus Lean's
  standard `propext`, `Classical.choice`, `Quot.sound` (a `sorry` would appear as `sorryAx`).

Run from the repository root after `lake build`:  python3 scripts/check_manifest.py
"""
import json
import os
import re
import subprocess
import sys
import tempfile

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
MAIN = "Kuramoto.main_theorem"


def short(name: str) -> str:
    return name[len("Kuramoto."):] if name.startswith("Kuramoto.") else name


def main() -> int:
    manifest = json.load(open("manifest.json"))
    ok = True

    names = []
    for ch in manifest["chapters"]:
        if not os.path.exists(ch["lean_path"]):
            print(f"missing file: {ch['lean_path']} (chapter {ch['id']})")
            ok = False
        names += ch["target_theorems"]

    lines = ["import Kuramoto", ""]
    lines += [f"#check @{n}" for n in names]
    lines += [f"#print axioms {MAIN}"]
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write("\n".join(lines) + "\n")
        path = f.name
    try:
        out = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True)
    finally:
        os.unlink(path)
    text = out.stdout + out.stderr

    for line in text.splitlines():
        if "error" in line:
            print(line)
            ok = False

    m = re.search(rf"'{re.escape(MAIN)}' depends on axioms: \[(.*?)\]", text, re.S)
    if not m:
        print(f"could not read the axioms of {MAIN}")
        return 1
    found = {a.strip() for a in m.group(1).split(",")}
    found = {short(a) for a in found}
    expected = {short(a) for a in manifest["axioms"]} | STANDARD
    if found != expected:
        print(f"axioms of {MAIN} differ from the manifest:")
        print("  unexpected:", sorted(found - expected))
        print("  missing:   ", sorted(expected - found))
        ok = False

    print(f"{len(names)} declarations checked; axioms of {MAIN}: {sorted(found - STANDARD)}")
    print("OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
