# Extended Nature-Inspired Exact Operators — Pure-$\mathbb{Q}$ Five-Pillar Certifier

> **Standing:** Offline pure-stdlib certifier and R5 test suite (`honest_novelty_tier: N0` — classical prior-art models `NATX-N0-01`..`08` and self-contained exact rational restatement/certifier; no novelty claim above `N0`).
> **Runtime Dependencies:** Python 3 standard library only (`int`, `fractions.Fraction`; zero floats on trust paths or JSON, zero bare `assert`s, zero external writes).

## 1. Shipped Files (Exact In-PR SHA-256)

| File | SHA-256 | Role |
|---|---|---|
| [`nature_extended_oracle.py`](nature_extended_oracle.py) | `ba8c2d03012ed51d0cf99ac98dcfd56bb57d925923144f2d34e774ff0ca69666` | Pure-$\mathbb{Q}$ exact solvers for all 5 pillars + `11` dynamic must-fail controls (`2+2+3+2+2`) + fail-closed `validate_certificate()` (verifies schema, invariants, `canonical_sha256`, and exact oracle recomputation parity) |
| [`nature_extended_certifier.py`](nature_extended_certifier.py) | `e5ff7c1f931f5db4470ca9ed0d35072d6f64234faeb4d6d0ee542f37de58f8cd` | Strict deterministic CLI (`--json`, `--output`, `--check` rejecting duplicate JSON keys, floats, CRLF, invalid UTF-8, oversized ints `>1000` digits, value drift, and byte drift with clean exit `2`) |
| [`test_nature_extended_r5.py`](test_nature_extended_r5.py) | `d94bf2aefc1b8a5af33826a2d8142447ad3755bdd4553d689e7bf616b00d1c1f` | Assertion-free R5 known-answer, control, value-tamper, and CLI error-handling suite (`7/7` groups OK) |
| [`nature_extended_certificate.json`](nature_extended_certificate.json) | `27f9da8604899aa58d1fd1a58044e54da3aaee9340c8b64ea94fe24e7a7735bb` | Canonical offline certificate (inner `canonical_sha256: c96a0dc5e35a66b70d577c688a6ccedc1bfcfab6e97ea0dced40749efb3fe571`) |
| [`NATURE_EXTENDED_REPORT.md`](NATURE_EXTENDED_REPORT.md) | `da76f6338c8d3d40ad30209f79267831673ab5e23d9a0f9c1e00eaee2cebb107` | Full report with DOI-verified `N0` literature table, exact rational tables, and scope boundaries |

## 2. Five Certified Pure-$\mathbb{Q}$ Pillars & `11` Must-Fail Controls (Zero Metaphors)

1. **P1 — Hopfield (1974) / Ninio (1975) Kinetic Proofreading (`NATX-N0-01`..`02`):** Exact $(k+1)\times(k+1)$ Gaussian elimination (`closed_form_residual = 0/1`): `k=2` achieves error ratio `1030301 / 1003003001` (`98.225762×` reduction vs. `k=0`), contrasted against reversible detailed-balance (`1720267 / 17051017 > 1/10`) and coupled-gate (`101 / 1001`) must-fail controls.
2. **P2 — Forrest et al. (1994) Negative Selection on $\{0,1\}^8$ (`NATX-N0-03`):** Exhaustive $256$-string enumeration (`0` Monte Carlo): proves exact `0` false positives across $r \in \{2..8\}$, a non-monotone recombinant+blocking hole jump at $r=4$ (`56 > 8`), over-broad collapse at $r=2$ (`0` detectors), and uncensored-detector `1/2` false-positive failure.
3. **P3 — Turing (1952) Discrete Reaction–Diffusion on $C_6$ (`NATX-N0-04`):** Exact integer ring Laplacian spectrum `[0, 1, 3, 4]` (`max_eigenvector_residual = 0/1`), separating Turing instability (`(1, 10)`) from equal-diffusion, sub-threshold, and spectral-gap (`(1/3, 19/10)`: continuous probe $h(2) = -2/5 < 0$ yet every $C_6$ eigenvalue stays $> 0$) controls.
4. **P4 — Topological $k$-NN Flocking & Kirchhoff $R_{\mathrm{eff}}$ (`NATX-N0-05`..`06`):** Exact tie-free pure-integer geometry ($N=16$): topological $k=6$ retains exact constant $R_{\mathrm{eff}}(0,15) = 725369524 / 1223911449$ and 2-vertex-connectivity under $s \in \{1,2,3,4\}$ uniform dilation while metric $r^2=144$ shatters to `16` singletons and sub-critical $k=1$ stays disconnected (`3` components). *Scope:* certifies uniform-dilation scaling invariance of $k$-NN graphs, not empirical live-flock velocity correlations.
5. **P5 — Turrigiano (1998/2008) Multiplicative Homeostasis $\to$ `siliquant` Absmax / $D_8$ (`NATX-N0-07`..`08`):** Exact `0/1` ratio/cosine drift and `0/8` symmetric absmax / $D_8$ code flips under $g \in \{7/3, 3/11\}$ vs. `8/8` code flips under `Code.centre`-class additive shift $b=3/8$, plus exact inward-tie $D_8$ zero-lane preservation (`d8_absmax_quantize_exact([0,1,0,0,0,0,0,0], 7) == [0,6,0,0,0,0,0,0]`) and unstable-gain ($\eta = 5/2$) divergence control.

## 3. Exact Offline Reproduction (4-Mode Isolated `-I` R4 Parity)

From this directory (`studies/expedition-nature-extended-audit102r/`, 100% offline, Python 3 standard library only):

```bash
# 1. Strict byte-for-byte verification against committed certificate (27f9da86...):
python3 -I -O -B -W error nature_extended_certifier.py --check nature_extended_certificate.json

# 2. 4-mode isolated -I deterministic recomputation parity (all match 27f9da86...):
python3 -I -B nature_extended_certifier.py --json | sha256sum
python3 -I -O -B nature_extended_certifier.py --json | sha256sum
python3 -I -B -W error nature_extended_certifier.py --json | sha256sum
python3 -I -O -B -W error nature_extended_certifier.py --json | sha256sum

# 3. Assertion-free R5 known-answer, control, value-tamper & CLI suite (7/7 groups OK):
python3 -I -O -B -W error test_nature_extended_r5.py
```

**Reproducible Local Checks:** `7/7` R5 groups pass across `-I -B`, `-I -O -B`, `-I -B -W error`, and `PYTHONHASHSEED=42 -B`; `aletheia mutate --max-mutants 0` kills `172/172` (`166` oracle + `6` certifier, `0` survivors, `truncated=False`).
