# Wave 2 Round 9 — Arm R9-2 (`AUDIT-079`): Pure-$\mathbb{Q}$ Differential-Geometric & Statistical Tomography of RIPO (`arXiv:2607.10169v2`, ICML 2026)

- **Arm / Owner:** Arm R9-2 (`spectral-prover`), strictly read-only on all external sources (`0` external writes).
- **Pinned Read-Only Anchors:**
  - `arXiv:2607.10169v2` (*Beyond Euclidean Clipping: Overcoming Exploration Collapse in LLM RL via Riemannian Isometric Policy Optimization*, Zhicheng Cai, Xinyuan Guo, Hanlin Wu, Wei-Ying Ma, Ya-Qin Zhang, Hao Zhou; Tsinghua AIR & SIA-Lab, ICML 2026; revised 8 Oct 2026) — staged PDF `symbiosis/round9/repos/ripo/arxiv_2607.10169.pdf`, SHA-256 `cb11fb97c9d555329f41e3ff6a821fd10294f69a29431dc05c204e60b9b63960` (**no public code repository URL** appears anywhere in the PDF metadata, body, or arXiv abstract page).
  - Zhihu Tab 2 (`https://zhuanlan.zhihu.com/p/2098101007368640039`, *`<RL 算法> 黎曼等距策略优化 RIPO`* by `Aiolus`, extracted via sanctioned read-only `/browser`) — staged transcript `symbiosis/round9/repos/zhihu/zhihu_2098101007368640039_ripo.md`, SHA-256 `d5a529c9e0c1a43294dce6e3b793affd476d4df9f243f37926c0accf08c23792`.
  - Verified Expedition Bridge Target: `AUDIT-064` `WI-4` (`symbiosis/round6/arm4-weight-iteration/warp_weight_iteration_certificate.json`, file SHA-256 `c4d3ab6f32e1d07f1cc5984b2fd90231b316e54b6791d540db16003fb63dcfcd`, `canonical_sha256: 9e3f9a74c86c9de0717a2814d480413989be6fed2a8b56a186fc61913cf78450`).
- **Oracle Class & Honest Law-4 Novelty Tag:** `exact+anchor` (100% pure Python 3 stdlib `int`/`Fraction`/`math.isqrt`, **ZERO floats** in code or JSON, **ZERO bare `assert`s**, **ZERO external deps**) | **`N1`** (exact pure-$\mathbb{Q}$ tomography of `arXiv:2607.10169v2` + Zhihu Tab 2 catching 5 concrete quantitative/structural defects, exact boundary/divergence/variance proofs `RIPO-GEO-01..03`, exact `AUDIT-064` `WI-4` Fisher-Schur pullback bridge `RIPO-FS-04`, and a fail-closed symmetric Bernoulli-$\chi^2$ + full-simplex trust-region guard `RIPO-GUARD-05`; all classical information-geometry & RL foundations strictly quarantined as `N0`).
- **Artifacts (`symbiosis/round9/arm2-ripo-riemannian-rl/`):**
  - [ripo_riemannian_audit.py](ripo_riemannian_audit.py) — self-contained pure-$\mathbb{Q}$ audit, theorem verifier, dual-oracle linear algebra (`Bareiss` + `Faddeev–LeVerrier`), and fail-closed trust-region guard (live read-only and `--standalone` modes)
  - [test_r5_ripo_riemannian.py](test_r5_ripo_riemannian.py) — 5-group R1–R5 verification, unseen-instance, adversarial-bypass, and `100.0%` mutation-kill test suite
  - [ripo_riemannian_certificate.json](ripo_riemannian_certificate.json) — canonical zero-float JSON certificate (`canonical_sha256: 3e6ab695d0a77e369dda1645aa79af18fa7d85fcccee52787bfd6c9802fbe661`)
  - [REPORT_R9_2_RIPO_RIEMANNIAN_RL.md](REPORT_R9_2_RIPO_RIEMANNIAN_RL.md) — this report

---

## 1. Law-2 Steelman Credit & Strict Law-4 `N0` Prior-Art Quarantine

### 1.1 Law-2 Steelman Credit to `arXiv:2607.10169v2` (*RIPO*) & Zhihu Tab 2
RIPO's core practical insight is genuine and empirically impactful: fixed-ratio PPO-Clip (`|r - 1| <= eps`) severely under-updates low-probability exploration tokens (where `0.5 * pi_old * eps^2 -> 0`) relative to high-probability exploitation tokens, and heuristics like DAPO's constant `eps_high = 0.28` still amplify dominant tokens (`0.8 -> 1.0`). Scaling the ratio threshold inversely with `sqrt(pi_old)` (`Eqn. 11`, `|r - 1| <= sqrt(delta / pi_old)`) directly targets that asymmetry with negligible compute overhead, yielding strong empirical gains across all 4 models in Table 1 (`Qwen3-1.7B/4B/8B-Base`, `Llama3.2-3B-Instruct`), PPO on GSM8K (Table 4), Pass@128 scaling on AIME-25/HMMT-25 (Table 5), and coding/search tasks (Table 6). Zhihu Tab 2 (`Aiolus`) accurately transcribed all 7 rows of Table 1 (`Qwen3-8B-Base`) verbatim from the paper.

### 1.2 Law-4 `N0` Quarantine Table (Aligned with `ROUND9_PORTALS.md` `R9-N0-05..10`)

| Quarantine ID | Established Classical / Published Prior Art (`N0`) | Role in `AUDIT-079` |
|---|---|---|
| `R9-N0-05` | Fisher (1922) variance-stabilizing $\sqrt{p}$ map, Csiszár (1967) $f$-divergences (Pearson/Neyman $\chi^2$, Hellinger $H^2$, KL), Amari (1998) Fisher–Rao metric & Natural Gradient, Kakade (2001) Natural Policy Gradient | Classical reference metric & global $f$-divergence inequalities (`2 H^2 <= D_KL <= chi^2`) used to audit RIPO |
| `R9-N0-06` | TRPO (Schulman et al. 2015), PPO-Clip (Schulman et al. 2017), Dual-Clip PPO (Ye et al. 2020), GRPO (Shao et al. 2024), DAPO/DCPO/GSPO/GMPO | Published RL baselines & clipping variants audited |
| `R9-N0-07` | Cai et al. (`arXiv:2607.10169v2`, ICML 2026) and `Aiolus` Zhihu Tab 2 (`2098101007368640039`) | Primary read-only audit targets (pinned by SHA-256) |
| `R9-N0-09` | Verified expedition artifact `AUDIT-064` `WI-4` (`warp-drive#12`, `F_p = diag(9/4, 49/2, 0)`, Krein inertia `(2, 1, 0)`, Schur kernel `0/1`) | Reused exact verified bridge target (`RIPO-FS-04`) |
| `R9-N0-10` | Bareiss (1968) fraction-free determinant, Faddeev–LeVerrier (1940) characteristic polynomial, Descartes' rule of signs, Mercator $\ln$ series | Classical pure-$\mathbb{Q}$ exact computational primitives |

---

## 2. Pillar 1 — Exact Pure-$\mathbb{Q}$ Audit of Worked Examples & Empirical Tables (`arXiv:2607.10169v2` & Zhihu Tab 2)

Auditing every equation, worked example (`Sec. 4.1`, p. 4), and Tables 1–3 (`pp. 6–8`) in exact `Fraction` arithmetic uncovered **5 concrete quantitative/structural discrepancies**:

| Defect ID | Exact Location (`arXiv:2607.10169v2` / Zhihu Tab 2) | Published Claim | Exact Pure-$\mathbb{Q}$ Audit Result |
|---|---|---|---|
| **`RIPO-DOC-01`** | `Sec. 4.1`, Eqns. (9)–(11) & worked example (`p. 4`); Zhihu Tab 2 `L22–25` | $\delta = 0.02$: high-prob $\pi_{\mathrm{old}} = 0.8$ caps at **`0.92`**; low-prob $\pi_{\mathrm{old}} = 0.01$ caps at `0.024`; both have constant distance `0.01` ("isometric"). | **(a) Factor-of-2 slip:** Eqn. (11) drops $\sqrt{2}$ so boundary $d_{\mathrm{geom}} = \delta/2 = \mathbf{1/100}$ (not $\delta = 1/50$). **(b) Truncation defect:** exact $\pi_{\max}(4/5) = 4/5 + \sqrt{2/125} \in [1243515313/1342177280, 4974061253/5368709120] \approx 0.92649 > 0.926$, which rounds to **`0.93`**, NOT `0.92` (at `0.92`, actual $d_{\mathrm{geom}} = \mathbf{9/1000} \ne 1/100$). **(c) Hidden negative lower clip:** at $\pi_{\mathrm{old}} = 1/100 < \delta = 1/50$, $1 - \epsilon = 1 - \sqrt{2} \in [-222379213/536870912, -1779033703/4294967296] < 0$! **(d) `15×` Non-Isometry:** between the paper's OWN two worked points (`4/5` vs `1/100`), true minimum full-simplex $\frac{1}{2}\chi^2$ differs by exact **`99/20` (`4.95×`)**, exact $4 H^2$ differs by **`> 11×`**, and exact TRPO KL $D_{\mathrm{KL}}(P \| Q)$ differs by **`> 15×`**! |
| **`RIPO-DOC-02`** | `Table 1` (`p. 6`) `Qwen3-8B-Base` & Zhihu Tab 2 `L35–41` | `RIPO` `38.5 (+35.1%)` vs `GRPO` `28.5`; `DCPO` `34.5` (`Qwen3-8B-Base`) and `27.8` (`Qwen3-4B-Base`). | All 7 Zhihu rows match Table 1 verbatim. Exact 7-benchmark rational means on `Qwen3-8B-Base`: `Base = 807/70`, `GRPO = 1997/70`, `DAPO = 2143/70`, `GSPO = 1124/35`, `GMPO = 2469/70`, `DCPO = 2421/70`, `RIPO = 1346/35`. **(a) Double-rounding inflation on headline `+35.1%`:** rounded `(77/2 - 57/2)/(57/2) = 20/57` (`35.09% -> +35.1%`) vs exact `(1346/35 - 1997/70)/(1997/70) = 695/1997` (`34.80% -> +34.8%`), exact gap **`325/113829` (`+0.2855` pp)**. **(b) `DCPO` rounding errors:** on `8B`, `2421/70 = 34.5857...` rounds to **`34.6`**, not `34.5` (error `3/35 > 1/20`); on `4B`, `979/35 = 27.9714...` rounds to **`28.0`**, not `27.8` (error `6/35`). **(c) Abstract claim verified:** on `Qwen3-1.7B-Base` AIME24, `(18.3 - 11.3)/11.3 = 70/113 > 3/5` (`61.95% > 60%`). |
| **`RIPO-DOC-03`** | `Table 2` (`p. 8`) vs `Sec. 5.4` prose (`p. 7`) | Prose claims *"when $\delta_{\mathrm{high}}$ is set substantially larger than $\delta_{\mathrm{low}}$, performance degrades markedly ... much easier to increase than to decrease."* | **Complete row-label inversion:** `0/3` collapsed columns (`28.8`, `27.5`, `27.9`) satisfy $\delta_{\mathrm{high}} > \delta_{\mathrm{low}}$; ALL **`3/3`** collapsed columns print $\delta_{\mathrm{low}} > \delta_{\mathrm{high}}$ (`(0.05, 0.02)`, `(0.08, 0.02)`, `(0.08, 0.04)`). |
| **`RIPO-DOC-04`** | `Table 3` (`p. 8`), row `SMT25` | `GRPO = 21.9`, `RIPO = 34.2 (+14.2)` | **Copy-paste arithmetic error:** exact difference is `34.2 - 21.9 = 123/10` (`+12.3`), NOT `+14.2` (`71/5`); error `19/10` (`+1.9`, copied from `BRUMO25` directly above). |
| **`RIPO-DOC-05`** | `Sec. 5.1` (`p. 5`) vs `Eqns. (11), (15)` | Default $\delta = 0.05$ (`1/20`), plus *"dual clipping to the importance ratio ... with the lower and upper bounds set to $0.5$ and $10$, respectively."* | Ad-hoc `[1/2, 10]` clamping silently breaks RIPO's claimed Riemannian isometry for ALL $\pi_{\mathrm{old}} < 4\delta = \mathbf{1/5}$ (`0.20`) on the lower bound and ALL $\pi_{\mathrm{old}} < \delta/81 = \mathbf{1/1620}$ on the upper bound (`RIPO-GEO-01`). |

---

## 3. Pillar 2 — Exact Pure-$\mathbb{Q}$ Boundary & Divergence Breakdown Theorems (`RIPO-GEO-01` & `RIPO-GEO-02`)

### 3.1 Theorem `RIPO-GEO-01` (Lower-Clip Dead Zone, Upper Simplex Overflow & Dual-Clip Collapse)
Under RIPO `Eqn. (11)` ($\epsilon(\pi_{\mathrm{old}}) = \sqrt{\delta / \pi_{\mathrm{old}}}$, clip interval $[1 - \epsilon, 1 + \epsilon]$) at the paper's default $\delta = 1/20$ (`0.05`):
1. **Lower-Clip Dead Zone ($\pi_{\mathrm{old}} < \delta = 1/20$):**
   $$1 - \sqrt{\frac{\delta}{\pi_{\mathrm{old}}}} < 0 \iff \pi_{\mathrm{old}} < \delta.$$
   Because any valid policy satisfies $r = \pi_\theta / \pi_{\mathrm{old}} \ge 0 > 1 - \epsilon$, **every negative advantage $\hat{A} < 0$ is identically unclipped all the way to $\pi_\theta \to 0^+$ ($D_{\mathrm{KL}}(\pi_{\mathrm{old}} \| \pi_\theta) = +\infty$)**. Exact rational witnesses at $\delta = 1/20$:
   - $\pi_{\mathrm{old}} = 1/80 \implies \epsilon = 2/1 \implies [L, U] = [\mathbf{-1/1}, 3/1]$; at $r = 1/100, \hat{A} = -1$, surrogate $= \mathbf{-1/100}$ (100% unclipped!).
   - $\pi_{\mathrm{old}} = 1/500 \implies \epsilon = 5/1 \implies [L, U] = [\mathbf{-4/1}, 6/1]$.
2. **Upper-Clip Simplex Overflow ($\pi_{\mathrm{old}} \ge p^*(\delta)$):**
   $$\pi_{\mathrm{old}}(1 + \epsilon) = \pi_{\mathrm{old}} + \sqrt{\delta \pi_{\mathrm{old}}} \ge 1 \iff \delta \pi_{\mathrm{old}} \ge (1 - \pi_{\mathrm{old}})^2.$$
   At $\delta = 1/20$, $20p^2 - 41p + 20 = (5p - 4)(4p - 5) = 0$ yields the exact rational boundary root **$p^* = 4/5$ (`0.80`)**, where $q_{\max} = 4/5 + 1/5 = 1$ ($D_{\mathrm{KL}}(P \| Q) = +\infty$!), and for all $\pi_{\mathrm{old}} > 4/5$ the upper clip lies strictly outside the probability simplex! Thus the strictly non-vacuous two-sided window is only $[1/20, 4/5]$ (width **`3/4`**), excluding BOTH the exploration tail $(0, 1/20)$ and exploitation tail $(4/5, 1)$.
3. **Sec. 5.1 Dual-Clip `[1/2, 10]` Isometry Collapse:** Clamping $1 - \epsilon \ge 1/2$ activates for all $\pi_{\mathrm{old}} < 4\delta = \mathbf{1/5}$ (reverting lower updates to Euclidean $d_{\mathrm{geom}} = \pi_{\mathrm{old}}/8 \to 0$); clamping $1 + \epsilon \le 10$ activates for all $\pi_{\mathrm{old}} < \delta/81 = \mathbf{1/1620}$.

### 3.2 Theorem `RIPO-GEO-02` (Local $\chi^2$ vs. Exact Fisher–Rao Hellinger & KL Breakdown when $\pi_{\mathrm{old}} \ll \delta$)
RIPO's trust-region ball $d_{\mathrm{geom}} = \frac{1}{2}\frac{(q - p)^2}{p} = \frac{\delta}{2}$ is a **single-coordinate local Pearson $\chi^2$ approximation**, NOT a Fisher–Rao isometry:
1. **Simplex-Conservation Cauchy–Schwarz Lower Bound:** For ANY categorical distribution $P$ and update $Q$ with $\Delta_a = Q_a - P_a$,
   $$\chi^2(Q \| P) = \frac{\Delta_a^2}{P_a} + \sum_{b \ne a} \frac{\Delta_b^2}{P_b} \ge \frac{\Delta_a^2}{P_a} + \frac{\Delta_a^2}{1 - P_a} = \frac{\Delta_a^2}{P_a(1 - P_a)},$$
   proving RIPO systematically underestimates minimum full-simplex $\frac{1}{2}\chi^2$ by at least $\frac{1}{1 - P_a}$ (exact `5×` at $P_a = 4/5$, exact `99/20` non-isometry between `4/5` and `1/100`).
2. **Rare-Token Collapse of Exact Hellinger & KL ($\pi_{\mathrm{old}} \ll \delta$):** On the exact rational-square ladder at Table-2 $\delta = 1/25$ (`0.04`) with $k = m^2 - 1$, $p = \delta/k^2$, $q = p m^2 = p + \sqrt{\delta p}$, RIPO claims constant $d_{\mathrm{geom}} = \mathbf{1/50}$, YET exact single-coordinate $2(\sqrt{q} - \sqrt{p})^2 = \frac{2\delta}{(m+1)^2}$, full-simplex $4 H^2(P, Q)$, and Mercator-bracketed TRPO $D_{\mathrm{KL}}(P \| Q)$ ALL decay strictly to $0$:

| $m$ | $k = \epsilon$ | $p_{\mathrm{old}}$ | $q_{\mathrm{RIPO}}$ | Claimed $d_{\mathrm{geom}}$ | Exact $2(\sqrt{q}-\sqrt{p})^2$ | $4 H^2(P, Q)$ Bracket | $\lfloor d_{\mathrm{geom}} / D_{\mathrm{KL}}^{\mathrm{hi}}(P \| Q) \rfloor$ |
|---:|---:|---:|---:|---:|---:|---:|---:|
| `2` | `3` | `1/225` | `4/225` | `1/50` | `2/225` | `[1205111/134217728, 4820445/536870912]` | `2×` |
| `3` | `8` | `1/1600` | `9/1600` | `1/50` | `1/200` | `[1345543/268435456, 2691087/536870912]` | `5×` |
| `5` | `24` | `1/14400` | `1/576` | `1/50` | `1/450` | `[18653/8388608, 1193793/536870912]` | `13×` |
| `10` | `99` | `1/245025` | `4/9801` | `1/50` | `2/3025` | `[709999/1073741824, 710001/1073741824]` | **`51×` (`> 50×`)** |

---

## 4. Pillar 3 — Exact Variance / Second-Moment Decomposition (`RIPO-GEO-03`)

In `Sec. 4.2` (`Eqn. 14`, p. 5; Zhihu Tab 2 `L27`), RIPO claims the raw second moment $v(x') = \pi_{\mathrm{old}}(1 + \sqrt{\delta/\pi_{\mathrm{old}}})^2 \approx \mathcal{O}(\delta)$ is *"density-independent and constant-order."* The exact algebraic identity is:
$$v(x') = (\sqrt{\pi_{\mathrm{old}}} + \sqrt{\delta})^2 = \underbrace{\pi_{\mathrm{old}}}_{\Theta(1)\text{ near }1} + \underbrace{2\sqrt{\delta \pi_{\mathrm{old}}}}_{\text{asymmetric cross term}} + \underbrace{\delta}_{v_{\mathrm{centered}}(x') = \pi_{\mathrm{old}}(r-1)^2}.$$
- **Actual homoscedasticity holds ONLY for the *centered* ratio variance contribution** $v_{\mathrm{centered}}(x') = \pi_{\mathrm{old}}(r - 1)^2 = \delta$ (exact `1/20`), NOT the raw second moment $v(x')$, which scales as $\Theta(1)$ near $\pi_{\mathrm{old}} = 1$ and exhibits upper-vs-lower raw second-moment asymmetry $v_+(x') - v_-(x') = 4\sqrt{\delta\pi_{\mathrm{old}}}$.
- **Exact rational witnesses at $\delta = 1/20$:**
  - Rare ($\pi_{\mathrm{old}} = 1/500, \sqrt{\delta p} = 1/100$): $v_+ = \mathbf{9/125}$ (`36/25 × delta`), $v_- = 4/125$, $v_{\mathrm{centered}} = \mathbf{1/20}$, asymmetry `1/25`.
  - Mid ($\pi_{\mathrm{old}} = 1/5, \sqrt{\delta p} = 1/10$): $v_+ = \mathbf{9/20}$ (`9× delta`), $v_- = 1/20$, $v_{\mathrm{centered}} = \mathbf{1/20}$, asymmetry `2/5`.
  - High ($\pi_{\mathrm{old}} = 4/5, \sqrt{\delta p} = 1/5$): $v_+ = \mathbf{5/4}$ (**`25× delta`** and **`625/36 ≈ 17.36×`** larger than `1/500`!), $v_- = 9/20$, $v_{\mathrm{centered}} = \mathbf{1/20}$, asymmetry `4/5`.
- **Eqn. (13) squared-mean counterexample:** At $\pi_{\mathrm{old}} = 1/1, r = 1, A = 1$, true $\operatorname{Var}[rA] = \mathbf{0/1}$ while raw $\mathbb{E}[r^2 A^2] = \mathbf{1/1}$ (`100%` squared-mean error).

---

## 5. Pillar 4 — Exact Pullback Bridge to `AUDIT-064` `WI-4` Fisher-Schur (`RIPO-FS-04`)

Pulling back RIPO's probability-simplex Fisher–Rao metric $G_{\mathrm{simplex}}(p) = \operatorname{diag}(1/p)$ along the exact softmax Jacobian $J_p = \operatorname{diag}(p) - pp^\top$ (`1^T J_p = 0`, $J_p^\top \operatorname{diag}(1/p) J_p = J_p$) and unembedding $U$ yields **EXACTLY `AUDIT-064` `WI-4`'s residual-space Fisher-KL curvature** $F_p = (J_p U)^\top \operatorname{diag}(1/p) (J_p U) = U^\top(\operatorname{diag}(p) - pp^\top)U$. On the exact `AUDIT-064` `WI-4` witness ($p = (1/2, 1/4, 1/4)$, $U = [[2,0,1],[-1,7,1],[-1,-7,1]]$):
- Exact diagonal $F_p = \operatorname{diag}(\mathbf{9/4}, \mathbf{49/2}, \mathbf{0/1})$ (matches `AUDIT-064` `canonical_sha256: 9e3f9a74...` bit-for-bit!).
- Dual-oracle **Bareiss + Faddeev–LeVerrier** verification: `det = 0/1`, Krein inertia **`⦺(F_p) = (2, 1, 0)`**, exact Schur kernel **`F_p ⧄ {0, 1} = 0/1`**.
- **Coordinate-vs-Coupled Inversion Witness:** All 3 `WI-4` residual steps preserve $\sum dp_i = 0$ and achieve identical task gain `1/1`:
  - `raw` ($\delta h = (1, 0, 0)^\top$, $dp = (3/4, -3/8, -3/8)^\top$): full $\frac{1}{2}\chi^2 = \mathbf{9/8}$, token-0 RIPO $d_{\mathrm{geom}} = \mathbf{9/16}$ (half of full).
  - `pre` ($\delta h = (1/5, 2/5, 0)^\top$, $dp = (3/20, 5/8, -31/40)^\top$): token-0 RIPO $d_{\mathrm{geom}}$ **SHRINKS `25×`** (`9/16 -> 9/400`, ratio **`1/25`**, only **`9/802`** of full cost!) while true coupled Fisher–Rao cost **EXPLODES `401/225` (`+78.22%`)** to **`401/200`**!
  - `schur` ($\delta h = (0, 0, 1)^\top \in \ker(F_p)$, $dp = (0, 0, 0)^\top$): exact **`0/1`** on BOTH token-0 and full coupled Fisher–Rao!

---

## 6. Pillar 5 — Fail-Closed Pure-$\mathbb{Q}$ Symmetric Bernoulli-$\chi^2$ & Full-Simplex Guard (`RIPO-GUARD-05`)

To close BOTH RIPO's lower-clip dead zone ($\pi_{\mathrm{old}} < \delta$) AND upper simplex overflow ($\pi_{\mathrm{old}} + \sqrt{\delta\pi_{\mathrm{old}}} \ge 1$) without reverting to Euclidean `[0.5, 10]` clamping, [ripo_riemannian_audit.py](ripo_riemannian_audit.py) implements:
1. **`evaluate_ripo_trust_region_hardened(..., mode="symmetric_chi2_guard")`:** Enforces the exact polynomial trust region
   $$\mathcal{B}_{\mathrm{sym}}(p, \delta) = \big\{ q \in (0, 1) \;:\; (q - p)^2 \le \delta p(1 - p) \;\wedge\; (q - p)^2 \le \delta q(1 - q) \big\},$$
   which (a) guarantees strict interior bounds $0 < q_{\mathrm{lo}} < p < q_{\mathrm{hi}} < 1$ for ALL $p, \delta \in (0, 1)$ (closing BOTH dead zones!), (b) preserves RIPO's $O(\sqrt{\delta/p})$ rare-token upper exploration scale, (c) rejects boundary collapses fail-closed (`ERR_PROBABILITY_COLLAPSE_ZERO`, `ERR_PROBABILITY_SATURATION_ONE`), and (d) globally certifies the exact $f$-divergence sandwich $2 H^2(P, Q) \le \min(D_{\mathrm{KL}}(P\|Q), D_{\mathrm{KL}}(Q\|P)) \le \max(D_{\mathrm{KL}}(P\|Q), D_{\mathrm{KL}}(Q\|P)) \le \delta$ without local Taylor breakdown.
   - Witness (`p = 1/80, q = 1/8000, delta = 1/20, A = -1`): `ripo_raw` leaves $r = 1/100$ unclipped (`DIAGNOSTIC_DEAD_ZONE_UNCLIPPED`, lower bound `-1/1`); `symmetric_chi2_guard` intercepts with `CLIP_LOWER_GUARD` (`ratio_clipped = 484326205/2818572288 > 0`, `lower_dead_zone_prevented = true`).
   - Witness (`p = 9/10, q = 99/100, delta = 1/20, A = 1`): `symmetric_chi2_guard` intercepts with `CLIP_UPPER_GUARD` (`q_safe_hi = 10700794037/11274289152 < 1`, `upper_overflow_prevented = true`).
2. **`verify_simplex_step_hardened(p_old, p_new, delta, kl_budget)`:** Enforces strict simplex conservation, rejects zero support (`ERR_SUPPORT_COLLAPSE`), and verifies full-simplex Pearson $\chi^2 \le \delta$, Neyman $\chi^2 \le \delta$, Cauchy–Schwarz lower bound, and exact Mercator-bracketed $D_{\mathrm{KL}}(P \| Q) \le \text{kl\_budget}$.

---

## 7. Exact Verification Receipts & Falsification Criteria

- **Repro Commands (`symbiosis/round9/arm2-ripo-riemannian-rl/`):**
  ```bash
  for f in "-I -B" "-I -O -B" "-I -B -W error" "-I -O -B -W error"; do
    python3 $f ripo_riemannian_audit.py --json | sha256sum
    python3 $f ripo_riemannian_audit.py --standalone --json | sha256sum
    python3 $f test_r5_ripo_riemannian.py
  done
  PYTHONPATH=../../../publish/aletheia python3 -B -W error -m aletheia audit-check . \
    --strict-ancestors --scripts ripo_riemannian_audit.py test_r5_ripo_riemannian.py --json
  PYTHONPATH=../../../publish/aletheia python3 -B -W error -m aletheia mutate ripo_riemannian_audit.py \
    --add-cwd --work-root . --test-cmd "python3 -I -O -B -W error test_r5_ripo_riemannian.py" --json
  ```
- **Falsification Criteria:** Fails if any SHA-256 of `arxiv_2607.10169.pdf`, `zhihu_2098101007368640039_ripo.md`, or `AUDIT-064` `warp_weight_iteration_certificate.json` mismatches; if any rational fraction in Pillars 1–5 fails independent SymPy/stdlib verification; if any float, bare `assert`, CRLF line ending, broken relative link, or local absolute-path leak appears; if any of the `4/4` isolated `-I` R4 hashes diverge; or if any mutant survives `aletheia v1.4.0 mutate` (`< 100.0%`).
