# Forensic Tomography of the `Frobenius` SAT-Solver Benchmark Gauntlet (`AUDIT-071R`)

- **Audit Status:** `AUDIT-071R VERIFIED` (`N1`, `0` unresolved defects; `49/49` `100.0%` `aletheia v1.4.0 mutate` killed; `aletheia v1.4.0 audit-check --strict-ancestors PASS`; `4/4` isolated `-I` bit-identical R4 determinism).
- **Target Artifact (Strictly Read-Only, `0` External Writes):** Published `Table 2: Full 30-instance, 8-family sequential (1-core) competitive SAT benchmark gauntlet` (`1018x1200` JPEG, SHA-256 `1af95eb5a4e57c65e5dc15d42780451b9be66cef83efe4e32ccd83528f98355d`). No image file or external binary is required to run this study; all arithmetic, scaling laws, clean-room AIG-hybrid vs. pure-DPLL solvers, and disclosure gates execute live in pure Python 3 stdlib (`int` / `fractions.Fraction`, **zero floats**).

## Files in This Study

| File | SHA-256 / Role |
|---|---|
| [frobenius_sat_forensics.py](frobenius_sat_forensics.py) | `22e58dce9f32fcb4e1d426786ea1a84a06116ec7fe8c7b72ae0476aaa6742b14` — Pure-$\mathbb{Q}$ `30 x 5` Table-2 centi-ms & scaling verifier, clean-room AIG-hybrid vs. DPLL oracle, critical 3-SAT blind-spot harness, and Aletheia v1.4.0 disclosure gate |
| [test_frobenius_sat_r5.py](test_frobenius_sat_r5.py) | `24d573cd65415a7e53bb0eec5cfd69c2dcc6ec5520480d9188d5a59c9bc72f78` — 4-group R1–R5 verification, tamper-detection, and `49/49` (`100.0%`) mutation-kill test suite |
| [frobenius_sat_certificate.json](frobenius_sat_certificate.json) | `9eb4f1f3fff05dd263b9626dfefd2edd93a98545e3d71bd1e62cb350e59e7885` — Zero-float canonical JSON certificate (`canonical_sha256 = 5518b2fcab456c6af6032a7d9cfb9d6442c6419b92195adc652949562ff05d51`), byte-identical to `--json` stdout |
| [FROBENIUS_SAT_REPORT.md](FROBENIUS_SAT_REPORT.md) | Full forensic report, exact ratio & scaling tables, clean-room separation vs. NP wall summary, and Law-4 `N0` prior-art quarantine |

## Quickstart (Zero External Dependencies)

From `studies/frobenius-sat-forensics/`:

```bash
# 1. Regenerate the canonical zero-float JSON certificate in isolated mode
#    4/4 isolated -I modes (-I -B, -I -O -B, -I -B -W error, -I -O -B -W error)
#    produce bit-identical stdout SHA-256 matching frobenius_sat_certificate.json verbatim:
#      9eb4f1f3fff05dd263b9626dfefd2edd93a98545e3d71bd1e62cb350e59e7885
#    (canonical_sha256 = 5518b2fcab456c6af6032a7d9cfb9d6442c6419b92195adc652949562ff05d51)
python3 -I -B frobenius_sat_forensics.py --json | sha256sum

# 2. Run the full R5 invariant and refusal-site test suite
python3 -I -O -B -W error test_frobenius_sat_r5.py
```

With [`Foundation-0/aletheia`](https://github.com/Foundation-0/aletheia) v1.4.0 installed or on `PYTHONPATH`:

```bash
python3 -B -W error -m aletheia audit-check . \
  --strict-ancestors --scripts frobenius_sat_forensics.py test_frobenius_sat_r5.py --json
python3 -B -W error -m aletheia mutate frobenius_sat_forensics.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_frobenius_sat_r5.py" --json
```

## Summary of Verified Results (`N1`)

- **Exact Table-2 Arithmetic Audit (`0` Errors):** All `30 x 5` cells, `5/5` solved counts, `5/5` PAR-2 totals (`0` centi-ms diff), `102/102` finite slowdown ratios, and `4/4` PAR-2 ratios (`5,352x`, `5,465x`, `2,921x`, `2,675x`) verify verbatim in exact `Fraction` arithmetic.
- **Steelman vs. Timeout Inflation & Exponential NP Walls:** True mutually-solved finite speedup is **`175.5x–522.6x`**, while **`86.77%–94.75%`** of competitors' headline PAR-2 scores is timeout-penalty inflation. On `Hard-SPN`, `Frobenius` spends **`69.47%`** (`4933/7101`) of total runtime and grows **`62.53x`** (`d=32 -> 64`) — matching CDCL's exponential base (`51.49x–69.31x`, flat constant-factor ratio, hitting `174.16 s > 30 s` at `d = 128`). On `SHA-256`, `64r_k16_unsat` implies **`6,062,534` evals/sec** SIMD bit-sliced evaluation, scaling strictly as $2^k$ (`k = 28` UNSAT `44.28 s > 30 s`).
- **Clean-Room AIG-Hybrid vs. Pure-DPLL Oracle:** Reproduces genuine algebraic separations (Tseitin `0,0,0` vs `15,31,63`; PHP `1,1,1` vs `5,31,241`; multiplier CEC `0`; AIG factoring; 64-way bit-sliced ARX) AND the omitted unstructured critical 3-SAT NP-hard blind spot (`0` XOR3 blocks extracted $\implies$ `100%` DPLL fallback).
