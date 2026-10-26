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
# Every statement math0 has frozen, including those that no result settles yet, so that CI
# compiles each of them as soon as it is committed.
frozen = [l.split()[1] for l in open(os.path.join(ROOT, "lean", "Math0", "Statements", "FROZEN.sha256")) if l.strip()]
stmts = sorted("Math0.Statements." + p[:-len(".lean")].replace("/", ".") for p in frozen)
with open(os.path.join(ROOT, "lean", "Math0", "Statements.lean"), "w") as f:
    f.write(header.replace("import Math0.Audit\n", "") + "".join(f"import {m}\n" for m in stmts) + """
/-!
# Frozen statements

Imports every statement listed in `Math0/Statements/FROZEN.sha256`: the conjectures that math0
formalized itself, each fidelity-reviewed and frozen before any proof attempt. Some are not yet
settled by any result.
-/
""")
with open(os.path.join(ROOT, "lean", "Math0.lean"), "w") as f:
    f.write(header + "import Math0.Statements\n" + "".join(f"import {m}\n" for m in mods) + doc)
print(f"Math0.lean imports {len(mods)} results; Math0/Statements.lean imports {len(stmts)} frozen statements")
