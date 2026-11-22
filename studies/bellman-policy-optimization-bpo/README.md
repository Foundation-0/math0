# Pure-$\mathbb{Q}$ Trajectory-Bellman & Complementary-Probability Duality Audit of Bellman Policy Optimization (`arXiv:2609.15987`, `AUDIT-083R`)

- **Audit Status:** `AUDIT-083R VERIFIED` (`N1`, `0` unresolved defects; `83/83` = `76/76` oracle + `7/7` audit `100.0%` `aletheia v1.4.0 mutate` killed; `aletheia v1.4.0 audit-check --strict-ancestors PASS`; `4/4` isolated `-I` bit-identical R4 determinism; `bypasses_found = 0` across all `7/7` `BPO-BUG-01..04` closures + `10/10` fresh boundary probes in `check_074`).
- **Target Artifacts (Strictly Read-Only, `0` External Writes):** `arXiv:2609.15987` (*Bellman Policy Optimization*, Zhuoqing Song, Haotian Xu, Xikun Zhang, Lidong Bing, Sep 14, 2026) bridged directly to Score Centering (`AUDIT-080R`), RIPO (`AUDIT-079R`), REINFORCE Zero (`AUDIT-081R`), and the Unified RL Triad (`AUDIT-082R`). No third-party PDFs or LaTeX sources are vendored here; all exact pure-$\mathbb{Q}$ trajectory-Bellman theorems, complementary-probability duality proofs, and trust-region gates execute live in standalone pure Python 3 stdlib (`int` / `fractions.Fraction`, **zero floats**).

## Files in This Study

| File | SHA-256 / Role |
|---|---|
| [bpo_bellman_oracle.py](bpo_bellman_oracle.py) | `be83c6880dd459b3c289482ae33c3f472cfd30081c2c453377c606548d764095` — Pure Python 3 stdlib zero-float BPO Theorem-1, Score-Centering duality, logit-Jacobian cancellation, drift dichotomy, cap-geometry, and trust-region gate oracle (`76/76` R5 killed) |
| [bpo_bellman_audit.py](bpo_bellman_audit.py) | `a2ccf71e8abd4107f01d28b0bc001fbe12e6a192215c50ff6e7b3594a7317cc5` — Standalone & live-anchored audit runner verifying Tables 1–3 and TeX spec completeness (`7/7` R5 killed) |
| [test_bpo_bellman_r5.py](test_bpo_bellman_r5.py) | `5a86d517ab88b570be6da0ad637154a5747905a4f59ee90bebeb719fa4952cbf` — Assertion-free isolated R1–R5 test & red-team suite (`5/5` suites PASS) |
| [bpo_bellman_certificate.json](bpo_bellman_certificate.json) | `4a66617952080266e41e93d9f87d8425ce70f589128af4e7d59bbce415ee4c29` — Sealed `AUDIT-083R` live-anchored zero-float certificate (`certificate_sha256 = 5dec537c601053012bfc83145f49086ac6aef40a0013b322b3dbeb6dd3d0a135`) |
| [BPO_BELLMAN_AUDIT_REPORT.md](BPO_BELLMAN_AUDIT_REPORT.md) | Full forensic report (`BPO-DRIFT-04`, `BPO-SPEC-01`, `BPO-CAP-06`, Top-1 Score Centering duality, Tables 1–3 audit, and Law-4 `N0`/`N1` quarantine) |

## Quickstart (Zero External Dependencies)

From `studies/bellman-policy-optimization-bpo/`:

```bash
# 1. Run exact pure-Q BPO trajectory-Bellman & complementary-ratio oracle in standalone isolated mode
#    4/4 isolated -I modes (-I -B, -I -O -B, -I -B -W error, -I -O -B -W error)
#    produce bit-identical stdout SHA-256:
#      95bde80a95a483b086d48783bbad200e14fa2fdcebfa4b97fef3419fb47b8a31
#    (certificate_sha256 = 57f08881400a2840b6887e0d3ee71e00519c3269350efc5c7a6e79520b2d0306)
python3 -I -B bpo_bellman_audit.py --standalone --json | sha256sum

# 2. Run the full R5 invariant, cap-reachability, and duality test suite
python3 -I -O -B -W error test_bpo_bellman_r5.py
```

With [`Foundation-0/aletheia`](https://github.com/Foundation-0/aletheia) v1.4.0 installed or on `PYTHONPATH`:

```bash
python3 -B -W error -m aletheia audit-check . \
  --strict-ancestors --scripts test_bpo_bellman_r5.py --json
python3 -B -W error -m aletheia mutate bpo_bellman_oracle.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_bpo_bellman_r5.py" --json
python3 -B -W error -m aletheia mutate bpo_bellman_audit.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_bpo_bellman_r5.py" --json
```
