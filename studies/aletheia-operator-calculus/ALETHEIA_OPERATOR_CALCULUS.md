# The Aletheia Operator Calculus (Wave 2 Round 4C — `AUDIT-051`)

- **Arm / Owners:** Glyph Registry & Collision Audit (`session-cartographer`) + Executable Engine & Commutator Discovery (`fractals-probe`, Arm R4C)
- **Artifacts (`symbiosis/round4/operator-calculus/`):**
  - `GLYPH_REGISTRY.md` & `glyph_registry.json` — canonical 8-glyph registry (`0 / 227,540` Lean 4 collisions, `0` expedition collisions, `0` session collisions; all 8 verified Unicode `Sm`)
  - `aletheia_calculus.py` — zero-float pure Python 3 stdlib Unicode/ASCII lexer, precedence parser, typed exact $\mathbb{Q}/\mathbb{Z}$ evaluator, 13-check compressed theorem suite, and 6-probe commutator/composition discovery engine
  - `test_aletheia_calculus_r5.py` — 5-group R1–R5 verification, coordinate/gauge invariance, unseen-instance, and adversarial refusal suite (`100.0%` mutation kill via `aletheia mutate`)
  - `aletheia_calculus_certificate.json` — zero-float canonical JSON certificate (`canonical_sha256 = 3ced28694a7ce21e982128e2d59d4b86df61294ca487659b7ff4416649486377`)
  - `ALETHEIA_OPERATOR_CALCULUS.md` — this report
- **Oracle Class & Honest Law-4 Novelty Tag:** `exact` (zero floats in JSON or any exact theorem; float64 appears ONLY inside Probe `C5`'s negative comparison predicate) | **`N1`** (clean-room zero-float executable operator calculus + exact cross-domain compositional laws, with two sharp candidate `N2` theorems — `C1` Nonlinear Schur–Unmasking Loewner Screening Positivity and `C6` Unconditional Linear Monopole Subadditivity / Rational Metric on $H^1(G, B; \mathbb{Z}_2)$ — kept honestly scoped at `N1` pending external literature review; zero symbolic theater, zero external writes).

---

## 1. Strict Law-4 `N0` Prior-Art Quarantine Table

Every classical theorem used as an ingredient or baseline in this calculus is quarantined as **`N0`**:

| Classical Result | Primary Prior Art | Role in `AUDIT-051` |
|---|---|---|
| Quotient formula for iterated nonsingular Schur complements | Crabtree & Haynsworth (1969) | Baseline for `T1` and smooth branch of Probe `C2` |
| Sylvester law of inertia, Bunch–Kaufman pivoting, Haynsworth inertia additivity, generalized singular Schur inertia | Sylvester (1852); Haynsworth (1968); Carlson–Haynsworth–Markham (1974); Bunch–Kaufman (1977) | Exact $\mathbb{Q}$ engine behind `⦺`, `T2`, and Probe `C2` |
| Matrix concavity / Jensen inequality for Schur complements of SPD matrices | Lieb (1973); Ando (1979) | Theoretical backbone of Probe `C3` (`[⧄_B, ⟠_G]`) |
| Signed graph Laplacians, invertibility of unbalanced graphs, bundle DtN maps | Harary (1953); Zaslavsky (1982); Curtis–Ingerman–Morrow (1998); Kenyon (2011) | Foundation for `⦷` (`L ⦷ χ`) |
| Electrical effective resistance, Rayleigh monotonicity, Kirchhoff/Foster cycle energy | Kirchhoff (1847); Foster (1948); Doyle–Snell (1984) | Foundation for `⧇`, `T3`, and Rayleigh bound in Probe `C4` |
| Woodbury matrix identity | Sherman–Morrison (1950); Woodbury (1950) | Algebraic derivation tool for closed-form Probe `C4` |
| Euler–Maclaurin / Bernoulli regularization of $\zeta(-k)$ | Euler (1749); Mellin (1902); Hardy (1949) | Baseline for `T5` (`⟠` Mellin regulator equalizer) |
| Ramanujan graph spectral bound | Lubotzky–Phillips–Sarnak (1988); Margulis (1988) | Baseline for `T4` (`⦺_-(R_G) ⩩ 0`) |

---

## 2. Canonical 8-Glyph Executable Grammar & LaTeX Bindings

Every glyph is empirically verified `0 / 227,540` across 4 major-lab Lean 4 corpora, `0` across expedition sources, and `0` across `gemini-sessions/` (`glyph_registry.json`), and bound 1-to-1 to both Unicode and ASCII fallback tokens in `aletheia_calculus.py` (with AST parity verified in `test_aletheia_calculus_r5.py`):

| ID | Glyph | Codepoint | ASCII | Prec / Fixity | Portable LaTeX Macro | Exact Typed Semantics (Zero Floats) |
|---|---|---|---|---|---|---|
| `OP-01` | **`⧄`** | `U+29C4` | `\|/\|` | `60` infix L | `\newcommand{\schurpush}{\mathbin{\char"29C4}}` | `M ⧄ B = M_{AA} - M_{AB} M_{BB}^+ M_{BA} ∈ Sym_{|A|}(ℚ)` |
| `OP-02` | **`⧅`** | `U+29C5` | `\|\\\|` | `60` infix L | `\newcommand{\darkshadow}{\mathbin{\char"29C5}}` | `M ⧅ B = (ker M_{BB}, M_{AB}|_{ker}, dim_dark, r_cross)` |
| `OP-03` | **`⦷`** | `U+29B7` | `(||)` | `55` infix L | `\newcommand{\holunmask}{\mathbin{\char"29B7}}` | `L ⦷ χ = (L^χ ⧄ I) - (L ⧄ I) ∈ Sym_{|B|}(ℚ)`, `F ⊆ E(I)` |
| `OP-04` | **`⟠`** | `U+27E0` | `<=>` | `50` infix L | `\newcommand{\obseq}{\mathbin{\char"27E0}}` | `X ⟠ G`: exact Reynolds group average or Mellin regulator-net equalizer |
| `OP-05` | **`⧇`** | `U+29C7` | `[o]` | `70` prefix | `\newcommand{\cohomobs}{\mathop{\char"29C7}}` | `⧇(ω) = ‖ω_harm‖_w^2 / ‖ω‖_w^2 ∈ [0, 1] ∩ ℚ` |
| `OP-06` | **`⦺`** | `U+29BA` | `(+-0)` | `70` prefix | `\newcommand{\kreinsig}{\mathop{\char"29BA}}` | `⦺(A) = (n_+, n_0, n_-) ∈ ℕ^3` (with projections `⦺_+`, `⦺_0`, `⦺_-`) |
| `OP-07` | **`⩩`** | `U+2A69` | `=#=` | `30` non-assoc | `\newcommand{\exacteq}{\mathrel{\char"2A69}}` | `X ⩩ Y`: exact zero-residual identity (strictly forbids `float`) |
| `OP-08` | **`⫩`** | `U+2AE9` | `_|T` | `20` non-assoc | `\newcommand{\rfivegate}{\mathrel{\char"2AE9}}` | `T ⫩ x`: `T(x) ∧ ∀ m ∈ ℳ(x), ¬T(m)` returning `(passed, kill_ratio)` |

---

## 3. One-Line Compressed Expedition Theorems (`13/13` Live Unicode + ASCII Verified)

Every expression below executes directly in `aletheia_calculus.py` in BOTH Unicode and ASCII syntax:

| Check | Source | Live Executable 1-Line Unicode Expression | Exact Outcome |
|---|---|---|---|
| `T1` | `SF-01` | `(M ⧄ D) ⧄ C_after_D ⩩ M ⧄ (D \| C)` | `True` (depth-2 BTZ) |
| `T2a` | `AUDIT-041` | `⦺(Ms) ⩩ ⦺(Ms_BB) + ⦺(Ms ⧄ B)` | `True` (smooth Haynsworth) |
| `T2b` | `AUDIT-041` | `⦺_-(Mx) ⩩ rk(Mx ⧅ B)` | `True` (singular Krein null-coupling) |
| `T3a/b` | `AUDIT-043` | `⧇(e0) ⩩ 15/31` and `⧇(d0f) ⩩ 0` | `True` (Hodge-1 resistance + coboundary) |
| `T4a/b` | `AUDIT-044` | `⦺_-(R_pet) ⩩ 0` and `⦺_-(R_dumb) ⩩ 1` | `True` (Petersen Ram vs `Dumbbell14` Non-Ram) |
| `T5` | `AUDIT-046` | `N1 ⟠ G_mult ⩩ -1/12` | `True` (3-observer multiplicative Mellin net) |
| `T6a/b/c` | `AUDIT-044`/`#268` | `⦺(L_odd ⦷ chi1) ⩩ (1, 2, 1)`, `⦺(L_odd ⦷ (chi1 * chi2)) ⩩ (2, 0, 2)`, `⦺(L_k3 ⦷ chi_k3) ⩩ (1, 0, 2)` | `True` (balanced `(k,·,k)` + odd-cycle `K_3` asymmetry) |
| `T7a/b` | `AUDIT-040R` | `kill(T_ex ⫩ x) ⩩ 1` and `kill(T_vac ⫩ x) ⩩ 0` | `True` (R5 rejects vacuous predicate) |

---

## 4. Six Pairwise Commutator & Composition Discovery Probes (`C1`–`C6`)

### Probe `C1` — `[⧄_D, ⦷_χ]` Nonlinear Schur–Unmasking Loewner Screening Theorem
**Exact Algebraic Law:** Let $G = (B \sqcup C \sqcup D, E, w)$ be any connected positive-weighted graph where collar $C$ separates outer boundary $B$ from deep bulk $D$, and let $\chi \in Z^1(G, B \sqcup C; \mathbb{Z}_2)$ have flip set $F \subseteq E(D)$. Write $\Lambda_{CC}(1) := (L \mathbin{⧄} D)_{CC} \succ 0$, $\Lambda_{CC}(\chi) := (L^\chi \mathbin{⧄} D)_{CC} \succ 0$, $\Delta_{CC}(\chi) := \Lambda_{CC}(\chi) - \Lambda_{CC}(1)$, and untwisted harmonic extension $H := -\Lambda_{CC}(1)^{-1} L_{CB}$. Because $A^{-1} - (A + E)^{-1} = A^{-1} E A^{-1} - A^{-1} E (A + E)^{-1} E A^{-1}$ identically over $\mathbb{Q}$, pushing $\Delta_{CC}(\chi)$ to $B$ yields an **always-PSD nonlinear commutator defect**:
$$H^\top \Delta_{CC}(\chi) H \;-\; (L \mathbin{⦷} \chi) \;\mathbin{⩩}\; \big(\Delta_{CC}(\chi) H\big)^\top \Lambda_{CC}(\chi)^{-1} \big(\Delta_{CC}(\chi) H\big) \;\succeq\; 0, \qquad ⦺_-\!\big([⧄_D, ⦷_\chi]\big) \mathbin{⩩} 0.$$
**Remarkably, this defect is strictly PSD even when $\Delta_{CC}(\chi)$ itself is Krein-indefinite or negative-dominated `(1, 0, 2)`**, forcing BOTH **nested Krein contraction** $⦺_\pm(\Delta_B) \le ⦺_\pm(\Delta_{CC})$ AND **strict monopole screening** $\Phi_B(\chi) \le \Phi_C(\chi)$ across concentric screens:

| Screen Case | `⦺(Δ_CC)` | `⦺(Δ_B)` | `⦺(Defect)` (PSD!) | $\Phi_C(\chi)$ | $\Phi_B(\chi)$ | Screening Drop |
|---|---|---|---|---:|---:|---:|
| `btz_depth2_L3` (`D={0..2}, C={3..5}, B={6..11}`) | `(1, 1, 1)` | `(1, 4, 1)` | **`(2, 4, 0)`** | `8/5` | `44/35` | `12/35` |
| `asymmetric_K3_screened` (all-flipped $K_3$ behind $C$) | **`(1, 0, 2)`** | **`(1, 0, 2)`** | **`(3, 0, 0)`** | `664/73` | `1064/311` | `128832/22703` |
| `concentric_3layer_C2_to_C1` (`D → C_2 → C_1`) | `(1, 1, 1)` | `(1, 1, 1)` | **`(2, 1, 0)`** | `20/9` | `252/143` | `592/1287` |
| `concentric_3layer_C1_to_B` (`C_1 → B`) | `(1, 1, 1)` | `(1, 1, 1)` | **`(2, 1, 0)`** | `252/143` | `468/425` | `40176/60775` |

Three-layer exact monopole screening chain with interface continuity at $C_1$: `20/9 > 252/143 > 468/425`.

### Probe `C2` — Nested Dark-Mode Shadow Composition `(M ⧄ B) ⧅ C` & Singular Schur Associator
1. **Generalized Indefinite+Singular Krein Decomposition (`12/12` seeded trials exact):** For arbitrary symmetric $M$ (even with indefinite $M_{DD}$ and indefinite $M_{AA}$) and shadow-orthogonal subspace $K = \ker(C_{AD}^\top)$:
   $$⦺(M) \;\mathbin{⩩}\; ⦺(M_{DD}) + ⦺\!\big((M \mathbin{⧄} D)\big|_K\big) + \big(r_{\mathrm{cross}},\, -r_{\mathrm{cross}},\, r_{\mathrm{cross}}\big), \qquad r_{\mathrm{cross}} = \operatorname{rk}(M \mathbin{⧅} D).$$
2. **Nonsingular-Fiber Shadow Preservation:** When `dim(M ⧅ B) ⩩ 0` while `B | C` is singular, exact dark-mode nullity and Krein coupling are strictly preserved: `dim((M ⧄ B) ⧅ C) ⩩ dim(M ⧅ (C | B)) = 1` and `rk((M ⧄ B) ⧅ C) ⩩ rk(M ⧅ (C | B)) = 1`.
3. **Singular Schur Associator Breakdown:** For singular $M_{DD}$, the associator `((M ⧄ D) ⧄ C) - (M ⧄ (C | D))` vanishes (`⩩ 0`) when `rk(M ⧅ D) = 0`, and becomes strictly **nonzero** (`rank = 1`, inertia `(1, 1, 0)`) the instant `rk(M ⧅ D) = 1` (dark-mode leakage breaks associativity of generalized Schur elimination).

### Probe `C3` — `[⧄_B, ⟠_G]` Matrix-Jensen / Schur Concavity Commutator Positivity
For SPD $M \succ 0$ and block-preserving cyclic symmetry group $G = \mathbb{Z}_3$ acting on $A \sqcup B$, coarse-graining BEFORE vs. AFTER fiber elimination obeys strict Loewner positivity (`8/8` non-invariant trials, sample inertia `(3, 0, 0)`):
$$⦺_-\!\Big(((M \mathbin{⟠} G) \mathbin{⧄} B) - ((M \mathbin{⧄} B) \mathbin{⟠} G_A)\Big) \;\mathbin{⩩}\; 0,$$
vanishing (`⩩ 0`) identically when $M$ is already $G$-invariant (`M ⟠ G`).

### Probe `C4` — `[⦷_χ, ⧇]` Exact Rank-2 Woodbury Monopole–Dirichlet Obstruction Law
For ANY single flipped interior edge $e^* = (u, v) \in E(I)$ of weight $w > 0$, using $L_{II}^{-1} L_{IB} \mathbf{1}_B = -\mathbf{1}_I$ and the rank-2 Krein flip $L^\chi_{II} - L_{II} = w(s s^\top - b b^\top)$ ($s = e_u + e_v$, $b = e_u - e_v$), exact Woodbury reduction yields the closed rational law:
$$\Phi_B(L \mathbin{⦷} \chi_{e^*}) \;\mathbin{⩩}\; \frac{4 w\, ⧇^{\mathrm{Dir}}(e^*)}{\big(1 + \alpha(e^*)\big)\,⧇^{\mathrm{Dir}}(e^*) + \beta(e^*)^2},$$
where $⧇^{\mathrm{Dir}}(e^*) := 1 - w(G_{uu} + G_{vv} - 2 G_{uv})$ is the grounded Dirichlet cycle obstruction ($G = L_{II}^{-1}$), $\alpha = w(G_{uu} + G_{vv} + 2 G_{uv})$, and $\beta = w(G_{uu} - G_{vv})$. Verified identically (`0` residual) across all 4 regimes with Rayleigh monotonicity `⧇(e*) <= ⧇^Dir(e*)`:

| Graph & Flipped Edge | Direct $\Phi_B$ | Closed Formula | Ungrounded `⧇(e*)` | Dirichlet `⧇^Dir(e*)` | Asymmetry $\beta$ |
|---|---:|---:|---:|---:|---:|
| `odd_btz_mouth_edge` | `11/8` | `11/8` | `1/3` | `11/24` | `1/8` |
| `odd_btz_cut_bridge` | `4/3` | `4/3` | `0/1` | `1/3` | `0/1` |
| `asymmetric_weighted_triangle` | `8628/1607` | `8628/1607` | `35/71` | `719/1187` | `324/1187` |
| `dead_end_dangling_bridge` | `0/1` | `0/1` | `0/1` | `0/1` | `-1/1` |

Note how `odd_btz_cut_bridge` explains the `AUDIT-044` bridge gauge subtlety: the cut-bridge has zero ungrounded cycle energy `⧇(e*) = 0`, yet shorting $B$ closes a relative cycle in $H_1(G, B)$ giving `⧇^Dir(e*) = 1/3` and `Φ_B = 4/3`, whereas a truly dangling bridge (`dead_end_dangling_bridge`) has `⧇^Dir(e*) = 0` and `Φ_B = 0`.

### Probe `C5` — `⫩` Coupled with `⩩` vs. IEEE-754 Float64 `==` Adversarial Kill-Shot
Against 3 `CS-11` adversarial mutants (`131836323/93222358` vs $\sqrt{2}$, exact residual `1/8690408031080164`; $F_{41}/F_{40} = 165580141/102334155$ vs $\phi$, exact residual `1/10472279279564025`; $1 + 10^{-18}$ vs $1$, exact residual `1/1000000000000000000`):
- **`T_exact ⫩ x_valid` (using `⩩`):** **`passed = True`, `kill_ratio = 1/1` (`3/3` killed)**.
- **`T_float ⫩ x_valid` (using IEEE-754 float64 `==`):** **`passed = False`, `kill_ratio = 0/1` (`0/3` killed — all 3 mirages survive!)**.

### Probe `C6` — Unconditional Linear Monopole Subadditivity & Rational Metric on $H^1(G, B; \mathbb{Z}_2)$
**Theorem (5-Line Elementary Proof — Discovered by Computing the `⦷` Homomorphism Defect):**
For **every** connected positive-weighted graph $G = (B \sqcup I, E, w)$ and **every** pair $\chi_1, \chi_2 \in H^1(G, B; \mathbb{Z}_2)$, the boundary monopole unmasking functional $\Phi_B(\chi) := \mathbf{1}_B^\top (L \mathbin{⦷} \chi) \mathbf{1}_B \in \mathbb{Q}_{\ge 0}$ satisfies **linear subadditivity without a square root**:
$$\Phi_B(L \mathbin{⦷} (\chi_1 \chi_2)) \;\le\; \mathcal{E}_{\chi_1 \chi_2}(z) \;\le\; \Phi_B(L \mathbin{⦷} \chi_1) + \Phi_B(L \mathbin{⦷} \chi_2),$$
making $d_{\mathrm{hol}}(\chi_1, \chi_2) := \Phi_B(L \mathbin{⦷} (\chi_1 \chi_2))$ a **true rational metric** on $H^1(G, B; \mathbb{Z}_2)$.

*Proof:* Define $f(x, y) := \operatorname{sgn}(x)\operatorname{sgn}(y)\min(|x|, |y|)$. Then (1) $f$ is continuous and piecewise linear on $\mathbb{R}^2$ with $\|\nabla f\|_2 \equiv 1$ a.e., hence globally Euclidean 1-Lipschitz: $(f(a,c) - f(b,d))^2 \le (a - b)^2 + (c - d)^2$ for all $a,b,c,d \in \mathbb{R}$; (2) $f$ is $\mathbb{Z}_2 \times \mathbb{Z}_2$-equivariant ($f(s_1 x, s_2 y) = s_1 s_2 f(x, y)$) with $f(1, 1) = 1$; (3) for exact rational signed-harmonic minimizers $x^{(1)}, x^{(2)} \in \mathbb{Q}^{|V|}$ ($x^{(i)}|_B = \mathbf{1}_B$), setting $z_v := f(x^{(1)}_v, x^{(2)}_v) \in \mathbb{Q}$ preserves $z|_B = \mathbf{1}_B$ and satisfies $(z_u - \chi_1\chi_2(e) z_v)^2 \le (x^{(1)}_u - \chi_1(e) x^{(1)}_v)^2 + (x^{(2)}_u - \chi_2(e) x^{(2)}_v)^2$ on every edge; (4) multiplying by $w_e > 0$ and summing gives $\Phi_B(\chi_1 \chi_2) \le \mathcal{E}_{\chi_1 \chi_2}(z) \le \Phi_B(\chi_1) + \Phi_B(\chi_2)$. $\blacksquare$

| Case | $\Phi(\chi_1)$ | $\Phi(\chi_2)$ | $\Phi(\chi_1\chi_2)$ | Rational Witness $\mathcal{E}(z)$ | $\Phi(\chi_1) + \Phi(\chi_2)$ | Exact Slack |
|---|---:|---:|---:|---:|---:|---:|
| `btz_odd_L3_L3` | `11/8` | `11/8` | `2/1` | `35/16` | `11/4` | `3/4` |
| `btz_even_L4_L4` | `32/21` | `32/21` | `16/7` | `368/147` | `64/21` | `16/21` |
| `weighted_K4_disjoint` | `201072/46397` | `399780/58019` | `520452/66707` | `27623053428/3366204361` | `2324199156/207069811` | `47270455824720/13813005882377` |
| `weighted_K4_adjacent` | `201072/46397` | `1200/221` | `376032/56213` | `8872888/1221025` | `7701024/788749` | `136302798144/44337947537` |
| `12` random extreme-weight graphs | — | — | All `12/12` | Exact edgewise + energy verified | — | All $\ge 0$ |

---

## 5. R1–R5 Verification Receipts & Falsification Criteria

- **Reproducibility Commands (`symbiosis/round4/operator-calculus/`):**
  ```bash
  # 4-mode isolated R4 bit-identical replay
  for f in "-I -B" "-I -O -B" "-I -B -W error" "-I -O -B -W error"; do
    python3 $f aletheia_calculus.py --json | sha256sum
    python3 $f test_aletheia_calculus_r5.py
  done
  # aletheia v1.2.0 audit-check & 100% mutation kill
  PYTHONPATH=../../../publish/aletheia python3 -B -W error -m aletheia audit-check . \
    --scripts aletheia_calculus.py test_aletheia_calculus_r5.py --json
  PYTHONPATH=../../../publish/aletheia python3 -B -W error -m aletheia mutate aletheia_calculus.py \
    --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_aletheia_calculus_r5.py" --json
  ```
- **Falsification Criteria:** `AUDIT-051` fails if (1) any of the 8 glyphs has a Unicode/Lean/expedition collision or fails Unicode-vs-ASCII AST/eval parity; (2) any of the 13 compressed theorems or 6 commutator probes (`C1..C6`) fails independent SymPy verification on either reported or unseen weighted graphs/indefinite matrices; (3) any single float appears in `aletheia_calculus_certificate.json`; (4) any operator breaks vertex-relabeling or interior-coboundary gauge invariance; or (5) any mutant survives `aletheia mutate` (`< 100%`) or any isolated `-I` R4 / `audit-check` gate fails.
