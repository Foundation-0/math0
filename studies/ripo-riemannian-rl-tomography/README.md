# Pure-$\mathbb{Q}$ Differential-Geometric & Statistical Tomography of RIPO (`arXiv:2607.10169v2`, `AUDIT-079R`)

- **Audit Status:** `AUDIT-079R VERIFIED` (`N1`, `0` unresolved defects; `62/62` `100.0%` `aletheia v1.4.0 mutate` killed; `aletheia v1.4.0 audit-check --strict-ancestors PASS`; `4/4` isolated `-I` bit-identical R4 determinism; `bypasses_found = 0` across all red-team + `6/6` extra edge probes in `check_073`).
- **Target Artifacts (Strictly Read-Only, `0` External Writes):** `arXiv:2607.10169v2` (*Beyond Euclidean Clipping: Overcoming Exploration Collapse in LLM RL via Riemannian Isometric Policy Optimization*, Cai et al., Tsinghua & SIA-Lab, ICML 2026; SHA-256 `cb11fb97c9d55532...`) + Zhihu Tab 2 (`2098101007368640039`, SHA-256 `d5a529c9e0c1a432...`) bridged to `AUDIT-064` `WI-4` Fisher-Schur (`Moissanite-Labs/warp-drive#12`, `canonical_sha256 = 9e3f9a74c86c9de0...`). No third-party PDFs are vendored here; all exact pure-$\mathbb{Q}$ theorems, dual-oracle linear algebra (`Bareiss` + `Faddeev–LeVerrier`), Mercator $\ln$ bounds, and hardened trust-region guards execute live in standalone pure Python 3 stdlib (`int` / `fractions.Fraction`, **zero floats**).

## Files in This Study

| File | SHA-256 / Role |
|---|---|
| [ripo_riemannian_audit.py](ripo_riemannian_audit.py) | `dd9c9819cc704c17b75e0d0a24cc002bc6e5433098a883bba9a8ee5fb39c4ad2` — Pure Python 3 stdlib zero-float RIPO audit, boundary/divergence/variance proofs, `AUDIT-064` `WI-4` pullback bridge, and fail-closed symmetric Bernoulli-$\chi^2$ + full-simplex Mercator-KL guard (`62/62` R5 killed) |
| [test_r5_ripo_riemannian.py](test_r5_ripo_riemannian.py) | `922a374367bc80859b4188f73a47205e79e62d1c2fb01ae0b6bb6f816c026310` — Assertion-free isolated R1–R5 verification, unseen-instance, and adversarial-bypass test suite |
| [ripo_riemannian_certificate.json](ripo_riemannian_certificate.json) | `2ecbe3f0d9bec7dea5a7aa6f8d473b5c5dfe15b13318614a93a6a0c1744e6e6a` — Sealed `AUDIT-079R` live-anchored zero-float certificate (`canonical_sha256 = 3e6ab695d0a77e369dda1645aa79af18fa7d85fcccee52787bfd6c9802fbe661`) |
| [REPORT_R9_2_RIPO_RIEMANNIAN_RL.md](REPORT_R9_2_RIPO_RIEMANNIAN_RL.md) | Full forensic report (`RIPO-DOC-01..05`, `RIPO-GEO-01..03`, `RIPO-FS-04`, `RIPO-GUARD-05`, Law-2 steelman, and Law-4 `N0`/`N1` quarantine) |

## Quickstart (Zero External Dependencies)

From `studies/ripo-riemannian-rl-tomography/`:

```bash
# 1. Run exact pure-Q RIPO differential-geometric & guard audit in standalone isolated mode
#    4/4 isolated -I modes (-I -B, -I -O -B, -I -B -W error, -I -O -B -W error)
#    produce bit-identical stdout SHA-256:
#      d9914c85d60448564b9dfee88d27da6c89642ad09bea176e4fe273e719bc5c15
#    (canonical_sha256 = 836353ccb2b347264765930679a81ac420d433ba662dd4b8ff39a63677461eef)
python3 -I -B ripo_riemannian_audit.py --standalone --json | sha256sum

# 2. Run the full R5 invariant, boundary, and mutation-kill test suite
python3 -I -O -B -W error test_r5_ripo_riemannian.py
```

With [`Foundation-0/aletheia`](https://github.com/Foundation-0/aletheia) v1.4.0 installed or on `PYTHONPATH`:

```bash
python3 -B -W error -m aletheia audit-check . \
  --strict-ancestors --scripts test_r5_ripo_riemannian.py --json
python3 -B -W error -m aletheia mutate ripo_riemannian_audit.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_r5_ripo_riemannian.py" --json
```
