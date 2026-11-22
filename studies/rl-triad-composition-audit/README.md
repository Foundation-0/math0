# Unified Off-Policy RL Geometry & Kernel-Invariance Composition (`TII × Score Centering × RIPO × songe × warp-drive`, `AUDIT-082R`)

- **Audit Status:** `AUDIT-082R VERIFIED` (`N1`, `0` unresolved defects; `56/56` `100.0%` `aletheia v1.4.0 mutate` killed; `aletheia v1.4.0 audit-check --strict-ancestors PASS`; `4/4` isolated `-I` bit-identical R4 determinism; `bypasses_found = 0` across all `TRIAD-BUG-01..03` closures + `4/4` extra probes in `check_072`).
- **Target Artifacts (Strictly Read-Only, `0` External Writes):** Unites Axis 1 Kernel TIM / TII (`REINFORCE Zero` @ `a22153de` & `zero-mismatch-rl` @ `136aca87`), Axis 2 First-Order Drift Cancellation (`arXiv:2609.20807v1` Score Centering + `songe` `AUDIT-073R` Bregman KL), and Axis 3 Second-Order Fisher–Rao Isometry (`arXiv:2607.10169v2` RIPO + `AUDIT-064` `WI-4` Fisher-Schur). No third-party repos or PDFs are vendored here; all five exact compositional theorems (`T1–T5`, `TRIAD-TRAP-01..04`) and the 6-gate fail-closed `certify_unified_rl_step` certifier execute live in standalone pure Python 3 stdlib (`int` / `fractions.Fraction`, **zero floats**).

## Files in This Study

| File | SHA-256 / Role |
|---|---|
| [rl_triad_composition_audit.py](rl_triad_composition_audit.py) | `7efdb921f044c11957c663d403424c181e8f57ccb0b291fc3811ac959a66d4e2` — Pure Python 3 stdlib zero-float `T1–T5` compositional prover + 6-gate `certify_unified_rl_step` (`14` refusal codes; `56/56` R5 killed) |
| [test_rl_triad_composition_r5.py](test_rl_triad_composition_r5.py) | `bbb4d60246efa38b1baa6b1da07511152e933a9a9d36896afa3451fc25c0a777` — Assertion-free isolated R1–R5 test & red-team suite (`19/19` OK) |
| [rl_triad_composition_certificate.json](rl_triad_composition_certificate.json) | `714a799a5d4a65ff8384a7ae0c75eb87bda840cb6b66966da7c91615e5861e67` — Sealed `AUDIT-082R` live-anchored zero-float certificate (`canonical_sha256 = 14020a61d781cf7bf8cee0c424af650e0a569d151b16a575cb34a51b502a5b78`) |
| [RL_TRIAD_COMPOSITION_AUDIT_REPORT.md](RL_TRIAD_COMPOSITION_AUDIT_REPORT.md) | Full forensic synthesis report (`T1–T5`, `TRIAD-TRAP-01..04`, `certify_unified_rl_step`, Law-2 steelman, and Law-4 `N0`/`N1` quarantine) |

## Quickstart (Zero External Dependencies)

From `studies/rl-triad-composition-audit/`:

```bash
# 1. Run exact pure-Q 3-axis RL composition & 6-gate certifier in standalone isolated mode
#    4/4 isolated -I modes (-I -B, -I -O -B, -I -B -W error, -I -O -B -W error)
#    produce bit-identical stdout SHA-256:
#      7d822647b1332ff469697a14889f6e7366a1fe6156b52927d412f40ca03f2068
#    (canonical_sha256 = bb8bebd9f02b63658d7af012bd1b9a46fce1806dfe1f52044529fa98b07d7a68)
python3 -I -B rl_triad_composition_audit.py --standalone --json | sha256sum

# 2. Run the full R5 compositional-trap and 6-gate refusal-site test suite
python3 -I -O -B -W error test_rl_triad_composition_r5.py
```

With [`Foundation-0/aletheia`](https://github.com/Foundation-0/aletheia) v1.4.0 installed or on `PYTHONPATH`:

```bash
python3 -B -W error -m aletheia audit-check . \
  --strict-ancestors --scripts test_rl_triad_composition_r5.py --json
python3 -B -W error -m aletheia mutate rl_triad_composition_audit.py \
  --work-root . --max-mutants 500 --add-cwd --test-cmd "python3 -I -O -B -W error test_rl_triad_composition_r5.py" --json
```
