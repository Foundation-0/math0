/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Audit
import Math0.ErdosProblems.Erdos1010_erdos_1010_variants_rademacher
import Math0.ErdosProblems.Erdos1048_erdos_1048_variants_diam_ge_two_is_best
import Math0.ErdosProblems.Erdos10_erdos_10_variants_grechuk_example
import Math0.ErdosProblems.Erdos142_erdos_142
import Math0.ErdosProblems.Erdos142_erdos_142_variants_isTheta

/-!
# math0

Root module: imports every verified result. Building it re-runs every audit (`#math0_proves`,
`#math0_refutes`, `#math0_answers`), so `lake build` fails on any `sorry`, non-standard axiom, or
mismatch with the upstream statement.
-/
