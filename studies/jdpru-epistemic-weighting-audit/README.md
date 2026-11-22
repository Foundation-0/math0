# Prompt-vs-Oracle Epistemic Coverage & Exact Pure-$\mathbb{Q}$ Survey-Weighting Tomography of `github.com/jdpru` (`AUDIT-078R`)

- **Audit Status:** `AUDIT-078R VERIFIED` (`N1`, `0` unresolved defects; `79/79` = `67/67` oracle + `12/12` audit `100.0%` `aletheia v1.4.0 mutate` killed; `aletheia v1.4.0 audit-check --strict-ancestors PASS`; `4/4` isolated `-I` bit-identical R4 determinism; `bypass_count = 0` across `18/18` adversarial red-team probes in `check_069`).
- **Target Artifacts (Strictly Read-Only, `0` External Writes):** `jdpru/cover-your-ais @ aafd6217a61071beca2faa191e692bfc44651991`, `jdpru/CES-Accuracy-Analysis @ 9375b1bbd5a239c23cf7d442c4e7dd4094c9400c`, `jdpru/CS-230-DynaRT @ c024875d595c6529c3e82a43e7e10dafd173fb5b` (plus `4` forks quarantined strictly as `N0`). No third-party repositories are vendored here; all exact pure-$\mathbb{Q}$ weighting theorems, `CYA-GAP-01..06` static scanners, and R5 tests execute live in standalone pure Python 3 stdlib (`int` / `fractions.Fraction`, **zero floats**).

## Files in This Study

| File | SHA-256 / Role |
|---|---|
| [jdpru_epistemic_weighting_oracle.py](jdpru_epistemic_weighting_oracle.py) | `6582399b4b2dfdac491d8019d9e79c58076cd091ec2007e18255de4812737cd2` — Pure Python 3 stdlib zero-float Kish/Bhatia–Davis/Meng/Simpson/2×2-conservation oracle + deterministic `CYA-GAP-01..06` scanners (`67/67` R5 killed) |
| [jdpru_epistemic_audit.py](jdpru_epistemic_audit.py) | `ceae5d6dfcc225822b1cef6779d55dc8a50c5c9e64bea317bce4defc400ed6c5` — Standalone & live-anchored audit runner with symlink-safe `.git/HEAD` SHA verification (`12/12` R5 killed) |
| [test_jdpru_epistemic_r5.py](test_jdpru_epistemic_r5.py) | `34472cf4b53af2344d7e437400ae8088448aad422c7992a45d1e216aa0a471e9` — Assertion-free isolated R1–R5 test & red-team suite (`4/4` suites PASS) |
| [jdpru_epistemic_certificate.json](jdpru_epistemic_certificate.json) | `14696a0ee17849a5eb8fc91e16b215d976f7a0bb0178c7b5f4ceecb80d61c4f3` — Sealed `AUDIT-078R` live-anchored zero-float certificate (`certificate_sha256 = 0a58dfd9e60fbe7f64c6e7b88b30f76d5b6bf9de1f3cbcf490edc196182dc7cb`) |
| [JDPRU_EPISTEMIC_WEIGHTING_REPORT.md](JDPRU_EPISTEMIC_WEIGHTING_REPORT.md) | Full forensic report (`CYA-GAP-01..06`, `PROMPT-BLIND-01..05`, CES pure-$\mathbb{Q}$ theorems, `7/7` README-vs-CSV drifts, and Law-4 `N0`/`N1` quarantine) |

## Quickstart (Zero External Dependencies)

From `studies/jdpru-epistemic-weighting-audit/`:

```bash
# 1. Run exact pure-Q epistemic & survey-weighting oracle in standalone isolated mode
#    4/4 isolated -I modes (-I -B, -I -O -B, -I -B -W error, -I -O -B -W error)
#    produce bit-identical stdout SHA-256:
#      e64823e3fff017db02713d00bcdc186e5cd6b422e3702ea205cd5dec3e43cb22
#    (certificate_sha256 = 8b94cc8ac265027cb80474597cd6017ffdd3b7547d90777fe5a4332b7c96c21d)
python3 -I -B jdpru_epistemic_audit.py --standalone --json | sha256sum

# 2. Run the full R5 invariant, scanner, and red-team test suite
python3 -I -O -B -W error test_jdpru_epistemic_r5.py
```

With [`Foundation-0/aletheia`](https://github.com/Foundation-0/aletheia) v1.4.0 installed or on `PYTHONPATH`:

```bash
python3 -B -W error -m aletheia audit-check . \
  --strict-ancestors --scripts test_jdpru_epistemic_r5.py --json
python3 -B -W error -m aletheia mutate jdpru_epistemic_weighting_oracle.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_jdpru_epistemic_r5.py" --json
python3 -B -W error -m aletheia mutate jdpru_epistemic_audit.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_jdpru_epistemic_r5.py" --json
```
