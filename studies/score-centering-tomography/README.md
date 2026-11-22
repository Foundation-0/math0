# Pure-$\mathbb{Q}$ Drift–Signal & Top-$K$ Singularity Tomography of Score Centering (`arXiv:2609.20807v1`, `AUDIT-080R`)

- **Audit Status:** `AUDIT-080R VERIFIED` (`N1`, `0` unresolved defects; `81/81` `100.0%` `aletheia v1.4.0 mutate` killed; `aletheia v1.4.0 audit-check --strict-ancestors PASS`; `4/4` isolated `-I` bit-identical R4 determinism; `bypasses_found = 0` across all `SC-BUG-01..03` closures + `7/7` extra probes in `check_071`).
- **Target Artifacts (Strictly Read-Only, `0` External Writes):** `arXiv:2609.20807v1` (*Score Centering Stabilizes Off-Policy Reinforcement Learning*, Marek & Ryabinin), `martin-marek/score-centering @ fdca22b1`, and Zhihu Tab 1 (`2092277762245538186`, SHA-256 `74443b91fa1668f3...`), bridged to `songe` (`AUDIT-073R`) & `Inkling` (`AUDIT-074R`). No third-party repos or PDFs are vendored here; all exact pure-$\mathbb{Q}$ drift/bias/singularity proofs and hardened Top-$K$ / batch-contract oracles execute live in standalone pure Python 3 stdlib (`int` / `fractions.Fraction`, **zero floats**).

## Files in This Study

| File | SHA-256 / Role |
|---|---|
| [score_centering_tomography.py](score_centering_tomography.py) | `d447b25cd88c9d36229f55b2eb261b448dba03db32329dc2bd1be549b6fad72f` — Pure Python 3 stdlib zero-float Score Centering drift/KL/singularity prover + hardened fail-closed `validate_batch_contract` and `evaluate_hardened_topk_score_centering` (`81/81` R5 killed) |
| [test_score_centering_r5.py](test_score_centering_r5.py) | `e692fd3f5bae95299544ac63a4ed21a06f7e96c71759b0a6b5233b8101a2170a` — Assertion-free isolated R1–R5 test & red-team suite (`12/12` OK) |
| [score_centering_certificate.json](score_centering_certificate.json) | `56cc01e643c1f3ca5576ae34484be5ad13687fa480530811defe815ebb738ec2` — Sealed `AUDIT-080R` live-anchored zero-float certificate (`certificate_sha256 = dc9671d3fda0adfd140986d83fbb70c6c86d1ddedc830734765a194558494d36`) |
| [SCORE_CENTERING_AUDIT_REPORT.md](SCORE_CENTERING_AUDIT_REPORT.md) | Full forensic report (`SC-SING-01`, `SC-CODE-01..05`, forward-KL disproof, both-sign witnesses, `songe`/`Inkling` bridges, and Law-4 `N0`/`N1` quarantine) |

## Quickstart (Zero External Dependencies)

From `studies/score-centering-tomography/`:

```bash
# 1. Run exact pure-Q Score Centering tomography & Top-K guard in standalone isolated mode
#    4/4 isolated -I modes (-I -B, -I -O -B, -I -B -W error, -I -O -B -W error)
#    produce bit-identical stdout SHA-256:
#      f52b7105b92679f19028315349142937baf7f6de42755b14fbeaf68b19d23547
#    (certificate_sha256 = 6d5c12aa9032e6f3d405b42f7ba8135960dd952a0c65024b71d6ed8f62f8644e)
python3 -I -B score_centering_tomography.py --json | sha256sum

# 2. Run the full R5 invariant, pigeonhole-dominance, and contract test suite
python3 -I -O -B -W error test_score_centering_r5.py
```

With [`Foundation-0/aletheia`](https://github.com/Foundation-0/aletheia) v1.4.0 installed or on `PYTHONPATH`:

```bash
python3 -B -W error -m aletheia audit-check . \
  --strict-ancestors --scripts score_centering_tomography.py test_score_centering_r5.py --json
python3 -B -W error -m aletheia mutate score_centering_tomography.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_score_centering_r5.py" --json
```
