#!/usr/bin/env python3
"""Fetch pinned mathlib artifacts into an isolated download cache."""
from pathlib import Path
import json, os, subprocess, sys
root = Path(__file__).resolve().parent
manifest = json.loads((root / "lake-manifest.json").read_text())
paths = [str(root / ".lake/packages" / p["name"]) for p in manifest["packages"]]
paths.append(str(root))
env = dict(os.environ, LEAN_SRC_PATH=":".join(paths), MATHLIB_CACHE_DIR=str(root / ".lake/download-cache"))
sys.exit(subprocess.run([str(root / ".lake/packages/mathlib/.lake/build/bin/cache"), *sys.argv[1:]], cwd=root, env=env).returncode)
