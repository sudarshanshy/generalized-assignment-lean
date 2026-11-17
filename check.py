#!/usr/bin/env python3
"""Check a project module using the pinned Lean and existing library artifacts."""
from pathlib import Path
import json, os, subprocess, sys
root = Path(__file__).resolve().parent
manifest = json.loads((root / "lake-manifest.json").read_text())
paths = [str(root / ".lake/packages" / p["name"] / ".lake/build/lib/lean") for p in manifest["packages"]]
paths.append(str(root / ".lake/build/lib/lean"))
env = dict(os.environ, LEAN_PATH=":".join(paths))
for file in sys.argv[1:]:
    source = Path(file)
    target = root / ".lake/build/lib/lean" / source.with_suffix(".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(["lean", "-j1", "-o", str(target), str(source)], cwd=root, env=env)
    if result.returncode:
        sys.exit(result.returncode)
