/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Audit

/-!
# math0

Root module: imports every verified result. Building this module re-runs every audit
(`#math0_proves`, `#math0_refutes`, `#math0_answers`, `#math0_audit`), so `lake build` fails on
any `sorry`, non-standard axiom, or mismatch with the upstream statement.
-/
