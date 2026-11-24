# Wave 2 Round 5 — Arm R5-5 (`AUDIT-060`): `alphaXiv` Formal Math, Sumsets, HOPE Hilbert Schur & Recurrence Convergence

- **Audit ID:** `AUDIT-060`
- **Owner:** `spectral-prover` (Arm R5-5, Portal `R5-P05`)
- **Oracle Class:** `exact+anchor` (pure Python 3 stdlib `int`/`Fraction`/`Q[i]`, **ZERO floats in JSON or theorems**, **ZERO external deps**, **ZERO bare `assert`s**; anchored against 6 commit-pinned strictly read-only external clones)
- **Honest Novelty Grade:** **`N1`** *(all upstream theorems — Feige's conjecture / Vlassis–Thomas / Grünbaum, Lin–Li `arXiv:2607.27199`, HOPE `arXiv:2607.21366`, Cauchy Hilbert determinant, Barrington's theorem, `LoopedActor` FPRM, and `QRR` — are strictly quarantined as `N0`; our verified `N1` contributions are the clean-room `aletheia v1.3.0 --lean-audit` 98-file census, `FEIGE-AUDIT-01` declaration-bound axiom verifier hardening, exact catch & Law-2 repair `SUMSET-CW-01` of the Collatz–Wielandt vector in `reproduction/report.md:35` plus exhaustive `462`-set base-12 affine-family classification, the exact Hilbert-space Schur-complement rank-inversion obstruction `SF-01 #27` separating diagonal HOPE from `G ⧄ A` / `G ⧅ V` + `R_H4` exact certification on $H_2..H_8$, and the exact $S_4$/$A_5$ + `LoopedActor`/`QRR` $\mathbb{Q}[i]$ convergence bridge).*

> **Strict Read-Only Ethics Standing:** All external repositories (`alphaxiv/*`, `camail-official/*`) were inspected strictly locally and read-only (`0` writes, PRs, issues, or comments).

---

## 1. Pinned Read-Only Upstream Anchors (`6` Clones Verified Clean)

| Repository | Pinned Commit SHA | Scope in `AUDIT-060` |
|---|---|---|
| `alphaxiv/feige-231f2e0b` | `50b0b2de0940b7f8ebc8c7c9fd628803f4283ba4` | Sole primary-Lean repo of `120` `alphaxiv` repos (`98` `.lean` files, `16,874` lines); `aletheia v1.3.0 --lean-audit`, `b_{n,1}` exact grid & `check_audit.py` audit. |
| `alphaxiv/settling-the-optimal-exponent-relating-sumsets-a` | `756551f6888c63bd33a796b0e7b497564032e2ae` | `arXiv:2607.27199` reproduction: exact 3-state carry automaton, `SUMSET-CW-01` Collatz–Wielandt audit & repair, BigInt depth proof `22 -> 15`, exhaustive `462`-set base-12 classification. |
| `alphaxiv/hilbert-operator-for-progressive-encoding-hope-a` | `23670f903a0f6c7ce7939fc8db26d3db8082d98e` | `arXiv:2607.21366` HOPE: exact $(s,t)$ positive-homogeneity gauge proof (`⟠`), diagonal-HOPE vs. Hilbert Schur (`⧄` / `⧅`, `SF-01 #27`) rank-inversion witness, and finite Hilbert $H_2..H_8$ Bareiss/$R_{H4}$ audit. |
| `alphaxiv/when-does-recurrence-become-an-algorithm-converg` | `7b48186b829192b481ff5792a288bf6f3f4a15ab` | `arXiv:2607.20594`: `aletheia v1.3.0` static audit (`2` bare asserts, `2` unseeded RNGs) + exact $S_4$ vs. $A_5$ derived-series Barrington obstruction. |
| `camail-official/LoopedActor` | `549a4e81ebd2d823112ed1bcf008f837e0f449b5` | Cross-link to Arm R5-3: `models/fprm.py:269-273` exact telescoping convex balance (`== 1`) & `eps`-contraction proof + `180` bare-assert audit. |
| `camail-official/Quotient_Recurrent_Reasoner_QRR` | `3e3c9ebecad534296482316e1c39f1063f0a6a32` | Cross-link to Arm R5-3: `models/integrator.py:217-242` exact $\mathbb{Q}[i]$ $U(1)$ fiber Schur projection (`⧄`), complex $\ell_\infty$ invariance (`⟠`) vs. real $\ell_\infty$ (`CS-11`), & residual singularity proof at $\eta = 1/2$. |

---

## 2. Law-4 Prior-Art Quarantine (`R5-N0-16` – `R5-N0-20`)

| Quarantine ID | Quarantined Baseline (`N0`) | Exact `N1` Delta Delivered Here |
|---|---|---|
| `R5-N0-16` | Feige (2006), Vlassis–Thomas (`arXiv:2607.08415`), Grünbaum (1960), Fu–Han–Wang–Yan–Zhang–Zhou (`arXiv:2607.23980`), Lin–Li (`arXiv:2607.27199`), and `alphaxiv` reproductions | Clean-room `aletheia v1.3.0` 98-file Lean census, `FEIGE-AUDIT-01` declaration-bound axiom hardening, `SUMSET-CW-01` Collatz–Wielandt catch + repair, BigInt depth proof, and exhaustive `462`-set base-12 affine-family classification. |
| `R5-N0-17` | Hilbert (1894), Schur (1911), Cauchy Hilbert determinant, and HOPE (`arXiv:2607.21366`) positive-homogeneity pruning score | Exact pure-$\mathbb{Q}$ $(s,t)$ gauge proof (`⟠`), explicit rank-2 PSD dark-mode counterexample (`SF-01 #27`) proving diagonal HOPE inverts optimal Hilbert Schur pruning (`4/1` vs `0/1`), and exact Bareiss/$R_{H4}$ (`2/1` exact on $H_2$, `>2` on $H_3..H_8$) analysis. |
| `R5-N0-18` | Barrington (1989) $NC^1$ completeness of $A_5$, Bai et al. (2019) DEQ, `arXiv:2607.20594`, `camail-official/{LoopedActor,QRR}` | Pure-stdlib exact commutator-series computation linking $S_4$ (`[24,12,4,1,1]`) vs. $A_5$ (`[60,60]`) to `report.md:56`, exact $\mathbb{Q}$ `fprm.py` telescoping balance, exact $\mathbb{Q}[i]$ `QRR` $U(1)$ Schur projection & `eta=1/2` singularity proof, and static hygiene counts. |
| `R5-N0-19..20` | Lean 4 kernel axioms (`propext`, `Classical.choice`, `Quot.sound`), `aletheia v1.3.0`, and Wave 1–2 `AUDIT-001..055` operators | Live exercise of fixed `ALETHEIA-CLI-01` 5x repeatable `--allow-project-import` on 98 real `.lean` files and direct 8-glyph operator compression (`⧄ ⧅ ⟠ ⦺ ⩩ ⫩`). |

---

## 3. Independently Verified Findings & Exact Operator Compression

### Module 1 — `alphaxiv/feige-231f2e0b@50b0b2de` (Lean 4 `v4.31.0` & Exact Extremizer)
1. **Complete `alphaxiv` Lean Census (`aletheia v1.3.0 --lean-audit`):** GitHub org-wide search confirms `alphaxiv/feige-231f2e0b` holds **all `98/98` `.lean` files (`16,874` lines)** across all `120` `alphaxiv` repositories. Running `aletheia v1.3.0 audit-check` with 5 repeatable `--allow-project-import` flags (`Feige`, `Grunbaum`, `LeanPool`, `VlassisThomas`, `Mathlib`) confirms **`lean_clean = True` (`0` hard escapes, `0` notices)** — zero `sorry`, `admit`, `sorryAx`, custom `axiom`, `native_decide`, `unsafe`, `partial`, `@[extern]`, `@[implemented_by]`, or `debug.skipKernelTC`. Static hygiene catches only `2` minor CSV CRLF files (`reports/unit-slack/data/{runtimes,simulation}.csv`), with `0` bare `assert`s, `0` unseeded RNGs, and `0` leaks.
2. **Exact Zero-Float Replay of $b_{n,1} = (n/(n+1))^n$ (`n = 1..512`):** Recomputes exact `Fraction(n, n+1)**n` for all $n=1\dots 512$, matching `reports/unit-slack/data/summary.json`'s `exact_grid_sha256` **`a6b7756c8ad1cc3e690a2654dd12ffa4a3dc9039951c00ef0bf970aa916a7d84`** bit-for-bit, proving strict monotonicity $b_{n+1,1} < b_{n,1}$, exact alternating Taylor lower bound $S_{21}(-1) < e^{-1} < S_{20}(-1) < b_{512,1}$, and exact Bernoulli extremizer identity $\Pr[\sum_{i=1}^n X_i < n+1] = (n/(n+1))^n$ ($n=1..6$).
3. **`FEIGE-AUDIT-01` (Honest R1/R3 Hardening Note on `reproduction/check_audit.py:17-22`):** While `check_audit.py` cleanly blocks `error:`, `sorryAx`, and non-standard axioms, it parses anonymous `depends on axioms: [...]` / `does not depend on any axioms` lines without binding them to the expected theorem identifiers (`Feige.sharp_unit_slack_feige_complete`, `VlassisThomas.exactCalibration`). Our hardened `verify_feige_axiom_log_strict` binds every required declaration name explicitly and rejects substitution attacks (`'True.intro' does not depend on any axioms`).

### Module 2 — `alphaxiv/settling-the-optimal-exponent-relating-sumsets-a@756551f6` (`arXiv:2607.27199`)
1. **Exact First-Principles 3-State Carry Automaton & $\mathbb{Z}_2$ Equalizer (`⟠`):** Rebuilding the minimal carry-subset DFA over reachable states `[{0}, {-1,0}, {-1}]` reproduces both gadgets with `0` hardcoded constants:
   - `D_paper = {0,1,2,4,5,9}`: $M_{\mathrm{paper}} = \begin{pmatrix} 3 & 6 & 2 \\ 2 & 8 & 2 \\ 2 & 6 & 3 \end{pmatrix}$, charpoly $(\lambda-1)(\lambda^2 - 13\lambda + 16)$, exact sequence **`1, 11, 127, 1475, 17143`** (`0` error vs. direct enumeration of $|(D^k-D^k)\bmod 12^k|$ for $k=1,2,3$ and `report.md:23`), exact rate $(13+\sqrt{105})/24$.
   - `D_imp = {0,1,3,4,5,8}`: $M_{\mathrm{imp}} = \begin{pmatrix} 4 & 4 & 3 \\ 3 & 6 & 3 \\ 3 & 4 & 4 \end{pmatrix}$, charpoly $(\lambda-1)(\lambda^2 - 13\lambda + 18)$, exact recurrence $t_{j+3} = 14 t_{j+2} - 31 t_{j+1} + 18 t_j$ (`0` residual), exact rate $(13+\sqrt{97})/24$.
   - Both matrices commute identically with the $\mathbb{Z}_2$ reflection swap $P$ (`{0} <-> {-1}`), splitting $\mathbb{Q}^3 = \mathbb{Q}_- \oplus \mathbb{Q}_+^2$ (`⟠`).
2. **`SUMSET-CW-01` (Exact Catch & Law-2 Steelman Repair on `reproduction/report.md:35`):** Exhaustive pure-$\mathbb{Q}$ evaluation proves that the literally printed Collatz–Wielandt vector `v = (1, 53/48, 53/48)` **fails** to certify $\rho(M_{\mathrm{imp}}) \le 183/16$ across **all `12/12` permutations and transposes** of $M_{\mathrm{imp}}$ (minimum max-ratio **`563/48 = 11.729... > 183/16 = 11.4375`**; `101/8 = 12.625 > 12` in pair-first order). Repairing the single-vs-pair slot yields **`v_repaired = (1, 53/48, 1)`** on `[{0}, {-1,0}, {-1}]` (equivalently `(1, 48/53, 48/53)` in pair-first order), which rigorously certifies **`max_i (M v)_i / v_i = 606/53 < 183/16`** (normalized rate **`101/106 < 61/64`**), confirming the repo's `183/16`, `61/64`, and exact BigInt depth-threshold reduction **`22(K+2)` $\to$ `15(K+2)`** (`7/22`, verified via $2\cdot 61^{15} < 64^{15} < 2\cdot 61^{14}\cdot 64$ and rational $\sqrt{105}$ brackets). A tighter convergent `(1, 52/47, 1)` certifies **`537/47`** (`179/188`).
3. **Exhaustive Exact Base-12 Classification (`462/462` Normalized 6-Digit Sets):** Across all $\binom{11}{5} = 462$ sets containing `0`, exactly `288` cover $\mathbb{Z}/12\mathbb{Z}$ under $D+D \bmod 12$, `53` directly cover `{0..11}` as integers, and **only `6` sets total** (3 reflection pairs) are strictly contractive — ALL `6` lying in the single exact affine family $M(k) = \begin{pmatrix} k+1 & 10-2k & k \\ k & 12-2k & k \\ k & 10-2k & k+1 \end{pmatrix}$ ($k \in \{1, 2, 3\}$), with **only `2` direct `{0..11}` bases**: **`D_imp = {0,1,3,4,5,8}` ($k=3$, unique optimum)** and **`D_paper = {0,1,2,4,5,9}` ($k=2$)**!

### Module 3 — `alphaxiv/hilbert-operator-for-progressive-encoding-hope-a@23670f90` (`arXiv:2607.21366` — `SF-01 #27`)
1. **Exact Positive-Homogeneity Gauge Invariance (`⟠`) vs. Hilbert Schur-Complement Obstruction (`⧄` / `⧅`):**
   - Verified over exact $\mathbb{Q}$ across 4 multi-channel positive rational rescalings $(s, t) \in \mathbb{Q}_{>0}^6$ that BN $s$-cancellation and post-ReLU $t$-homogeneity leave both channel Gram matrices $G_{ij} = (w_i^\top w_j)\langle\phi_i, \phi_j\rangle$ and Schur pruning losses $(G \mathbin{⧄} A)_{ii}$ identically invariant (`0` residual), while raw $\ell_1$ breaks in `4/4` cases.
   - **Diagonal-HOPE Blindness Witness:** On the exact rank-2 PSD Gram matrix $G = \begin{pmatrix} 9 & 9 & 0 \\ 9 & 9 & 0 \\ 0 & 0 & 4 \end{pmatrix}$ (`⦺(G) = (2, 1, 0)`, dark-mode nullity `dim(G ⧅ V) = 1`), HOPE's diagonal self-capacity ranks orthogonal Channel `2` (`c_2^2 = 4 < 9`) as first to prune (incurring true Hilbert error **`4/1`**), whereas exact Hilbert Schur pushforward (`G ⧄ A`) identifies redundant Channel `0` as **zero-error prunable (`0/1`)**! When $G$ is orthogonal, Schur loss equals HOPE identically (`[9, 5, 4]`).
2. **Exact Finite Hilbert Operators $H_n$ (`n = 2..8`, Bareiss/Cauchy + `AUDIT-002` $R_{\mathrm{opt}}$ vs. `AUDIT-014` $R_{H4}$):**
   - Verified `0`-residual parity between exact Gauss-Jordan $\det(H_n)$ and Cauchy's $\frac{c_n^4}{c_{2n}}$, pure-integer inverse $H_n^{-1}$, strict PD inertia **`⦺(H_n) ⩩ (n, 0, 0)`**, and exact progressive Schur pivot $H_n \mathbin{⧄} \{0,\dots,n-2\} = \frac{((n-1)!)^4}{(2n-2)!(2n-1)!}$ decaying from `1/12` ($n=2$) to **`1/176679360`** ($n=8$, $\lfloor \kappa_F(H_8)^2 \rfloor = 240{,}052{,}201{,}105{,}204{,}236{,}529$).
   - **Higher-Moment Separation:** Moment-Hankel Schur bound $R_{H4}(H_n)$ recovers exact **`2/1`** at $n=2$ (vs. $R_{\mathrm{opt}} = 32/29$) and strictly surpasses `ceil(R_opt) = 2` on **every $H_3 \dots H_8$** (`R_H4(H_3) = 46917762/22912973 > 2`, certifying exact full rank `3` on $H_3$!).

### Module 4 — `alphaxiv/when-does-recurrence-become-an-algorithm-converg@7b48186b` ↔ `camail-official/{LoopedActor, QRR}`
1. **Exact Group-Solvability Obstruction ($S_4$ vs. $A_5$):** Pure-stdlib commutator closure proves $S_4$ has derived series **`[24, 12, 4, 1, 1]`** (solvable, derived length `3`), whereas $A_5$ has derived series **`[60, 60]`** (perfect simple — Barrington's $NC^1$ obstruction explaining `report.md:56`'s OOD collapse on $A_5$).
2. **`LoopedActor` (`models/fprm.py:269-273`):** Proves exact telescoping convex balance $a_2 a_1^{2L} + b_1^{\mathrm{exact}}\sum_{k=0}^{2L-1} a_1^k \equiv 1$ across 4 rational parameterizations, with `fprm.py:273`'s `+ 1e-5` strictly damping total weight `< 1`.
3. **`QRR` (`models/integrator.py:217-242`):** Proves over exact $\mathbb{Q}[i]$ that $F_H = F - i a y$ is an exact rank-1 $U(1)$ fiber Schur projection (`orth_res = 0/1`, `pyth_res = 0/1`), satisfies exact $U(1, \mathbb{Q}[i])$ equivariance and complex $\ell_\infty$ invariance (`⟠`) across 3 Pythagorean triples while real $\ell_\infty$ breaks (`CS-11`), and verifies `integrator.py:235-240`'s residual singularity ($r_{\mathrm{bad}}(1/3) = 2 < r_{\mathrm{bad}}(2/5) = 4 > r_{\mathrm{bad}}(1) = 2$, pole at $\eta = 1/2$).
4. **Live `aletheia v1.3.0` Static Hygiene Census:** `settling-sumsets` (`0` bare asserts, `PASS`), `HOPE` (`0` bare asserts, `PASS`), `when-does-recurrence` (`2` bare asserts at `train_repro.py:463,466`, `2` unseeded RNGs), `LoopedActor` (`180` bare asserts, `13` unseeded RNGs), `QRR` (`60` bare asserts, `15` unseeded RNGs).

---

## 4. Exact Reproduction & Verification Gates

```bash
# 1. 4-mode isolated R4 execution (full clone mode & offline standalone mode)
for flags in "-I -B" "-I -O -B" "-I -B -W error" "-I -O -B -W error"; do
  python3 $flags alphaxiv_math_formal_audit.py --json | sha256sum
  python3 $flags alphaxiv_math_formal_audit.py --standalone --json | sha256sum
  python3 $flags test_r5_alphaxiv_math_formal.py
done

# 2. aletheia v1.3.0 self audit-check + live R5 AST mutation kill (with Foundation-0/aletheia on PYTHONPATH)
python3 -B -W error -m aletheia audit-check . \
  --scripts alphaxiv_math_formal_audit.py test_r5_alphaxiv_math_formal.py --json
python3 -B -W error -m aletheia mutate alphaxiv_math_formal_audit.py \
  --add-cwd --work-root . --test-cmd "python3 -I -O -B -W error test_r5_alphaxiv_math_formal.py" --json
```
