#!/usr/bin/env python3
"""Regenerate lean/Math0.lean so that it imports every result listed in catalog.json."""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
cat = json.load(open(os.path.join(ROOT, "catalog.json")))
mods = sorted(e["lean_file"][len("lean/"):-len(".lean")].replace("/", ".") for e in cat["results"])
header = """/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Audit
"""
doc = """
/-!
# math0

Root module: imports every verified result. Building it re-runs every audit (`#math0_proves`,
`#math0_refutes`, `#math0_answers`), so `lake build` fails on any `sorry`, non-standard axiom, or
mismatch with the upstream statement.
-/
"""
with open(os.path.join(ROOT, "lean", "Math0.lean"), "w") as f:
    f.write(header + "".join(f"import {m}\n" for m in mods) + doc)
print(f"Math0.lean imports {len(mods)} results")
