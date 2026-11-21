# Exact Pure-$\mathbb{Q}$ Polytope, Bipartite Identifiability & Tao Observability Audit of the alphaXiv OpenResearch Intelligence Index (`AUDIT-069R`)

- **Audit Status:** `AUDIT-069R VERIFIED` (`N1`, `0` unresolved defects; `91/91` = `69/69` oracle + `22/22` audit `100.0%` `aletheia v1.4.0 mutate` killed; `aletheia v1.4.0 audit-check --strict-ancestors PASS`; `4/4` isolated `-I` bit-identical R4 determinism).
- **Target Artifacts (Strictly Read-Only, `0` External Writes):** Pinned alphaXiv OpenResearch Intelligence Index HTML/JS/PNG captures (`index.html` `ac66dd30...`, `ResultsTable-Cepl37af.js` `fa223017...`, `RankHeatmap-CVYXZmjT.js` `64d03a35...`, `CostScoreChart-CkzD4pZy.js` `55583ebf...`, `cost-vs-score.png` `51541703...`, `openresearch_sh.html` `9e00c6f0...`) and `alphaXiv/OpenResearch @ 48f42c450ca00ab08fe10358989311193b0f81c6`. No third-party bundles or repos are vendored here; all exact pure-$\mathbb{Q}$ mathematics executes live in standalone pure Python 3 stdlib (`int` / `fractions.Fraction`, **zero floats**).

## Files in This Study

| File | SHA-256 / Role |
|---|---|
| [openresearch_index_oracle.py](openresearch_index_oracle.py) | `3355faad03a7aaca419ba443b041d0290dfe31e875005341b80ce0fadc79aa1a` — Pure Python 3 stdlib zero-float trust kernel (`69/69` R5 mutation killed) |
| [openresearch_index_audit.py](openresearch_index_audit.py) | `5aba6e7ff8118ffe87ab649fd4b5daf150cba4a9039a248921e2281dc2fef992` — Canonical certificate emitter & live-bundle verifier (`--standalone` supported; `22/22` R5 mutation killed) |
| [test_openresearch_index_r5.py](test_openresearch_index_r5.py) | `69f3bc487ad23f90ed2acfedc2147628f89f6e0b2d837cc0f3a214144f98a72e` — R1–R5 invariant & refusal-site test suite (`91/91` `100.0%` combined kill) |
| [openresearch_index_certificate.json](openresearch_index_certificate.json) | `bc9220ef8d15c5607a589a7777acdda9c5cc177c0443b2f31346fccb50428f34` — Sealed `AUDIT-069R` live-anchored zero-float certificate (`canonical_sha256 = e240f393f6a922337a69d2aa5388db6642b6bd75c2c74eae4bce012ec48829b3`) |
| [OPENRESEARCH_INDEX_AUDIT_REPORT.md](OPENRESEARCH_INDEX_AUDIT_REPORT.md) | Full forensic report, Law-2 steelman credit, exact simplex/RREF proofs, `OpenResearch@48f42c45` audit, and Law-4 `N0`/`N1` quarantine |

## Quickstart (Zero External Dependencies)

From `studies/openresearch-index-polytope-identifiability/`:

```bash
# 1. Run exact pure-Q oracle & certificate emitter in standalone isolated mode
#    4/4 isolated -I modes (-I -B, -I -O -B, -I -B -W error, -I -O -B -W error)
#    produce bit-identical stdout SHA-256:
#      f0ad643d1f0a6a4ea35006815e6b540d828493c45af857d1933660cecde657cd
#    (canonical_sha256 = 14313e491099e26e7f2d6d638e64c40bebd6e2071a72a9842bbac41f61862b3d)
python3 -I -B openresearch_index_audit.py --standalone | sha256sum

# 2. Run the full R5 invariant and refusal-site test suite
python3 -I -O -B -W error test_openresearch_index_r5.py
```

With [`Foundation-0/aletheia`](https://github.com/Foundation-0/aletheia) v1.4.0 installed or on `PYTHONPATH`:

```bash
python3 -B -W error -m aletheia audit-check . \
  --strict-ancestors --scripts openresearch_index_oracle.py openresearch_index_audit.py test_openresearch_index_r5.py --json
python3 -B -W error -m aletheia mutate openresearch_index_oracle.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_openresearch_index_r5.py" --json
python3 -B -W error -m aletheia mutate openresearch_index_audit.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_openresearch_index_r5.py" --json
```

## Summary of Verified Results (`N1`)

- **Exact Composite, Missing-Attempt (`74/87`) & Cost Forensics:** Reconstructs `Fable 5.1*` Science exactly as `41/120` (`0.3417`) and proves `$253.52` cost extrapolation gap plus exact MNAR missing-attempt sensitivity bounds across all 8 models.
- **Exact $\Delta_2$ Weight-Simplex Polytope & CI Separability:** Computes exact rational polytope volumes (`2713763/2963763` vs `250000/2963763`; `29.1899%` full-order region; `10/3x` per-task leverage), `9/28` pairwise 95% CI overlaps (`#2–#5` $K_4$ clique), and CI Pareto fragility.
- **Exact Bipartite Model–Harness Non-Identifiability (`dim ker(X) = 3 -> 1`):** Pure-$\mathbb{Q}$ RREF of the `8 x 11` additive incidence matrix proves **`20/28` (`71.43%`)** pairwise model contrasts (every cross-provider pair, including `#1` vs `#2`) and **`3/3` (`100%`)** harness contrasts are algebraically unidentifiable — and proves `+2` cross-harness bridge cells (`(Opus 5.5, OpenCode)` and `(GPT-6 Astra, OpenCode)`) restore **`28/28` (`100%`)** model and **`3/3` (`100%`)** harness identifiability.
- **Tao Observability Gate (`G1–G5`):** Formalizes a fail-closed 5-gate process contract closing the advisory-only `run_command` and opt-in metrics gaps audited in `alphaXiv/OpenResearch@48f42c45`.
