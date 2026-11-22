# AUDIT-083 — Exact Pure-Rational Tomography of Bellman Policy Optimization (`arXiv:2609.15987`)

- **Audit ID:** `AUDIT-083R` (Wave 2 Round 9, Arm R9-6; all 4 red-team defect classes `BPO-BUG-01..04` closed)
- **Target Paper:** *Bellman Policy Optimization* (`arXiv:2609.15987`, Zhuoqing Song, Haotian Xu, Xikun Zhang, Lidong Bing, Sep 14, 2026 — primary source behind Zhihu `2084586770000261374`)
- **Epistemic Tier:** `N1` (Verified pure-$\mathbb{Q}$ executable oracles, verbatim LaTeX source & PDF/text SHA-256 anchors, `83/83` `100.0%` R5 mutation kill across both Python modules; classical PMD / Bellman / DPO / binary-KL prior art quarantined cleanly as `N0`)
- **Governance Standard:** `Foundation-0/aletheia v1.4.0` (Laws 1–5: zero floats on trust paths or JSON certificates, zero bare `assert`s, `4/4` isolated `-I` R4 parity, `100.0%` R5 mutation kill, `audit-check --strict-ancestors PASS`)
- **External Write Count:** `0` (strictly read-only inspection of staged arXiv preprint artifacts)
- **Live Certificate SHA-256:** `5dec537c601053012bfc83145f49086ac6aef40a0013b322b3dbeb6dd3d0a135` (`bpo_bellman_certificate.json`)
- **Standalone Certificate SHA-256:** `57f08881400a2840b6887e0d3ee71e00519c3269350efc5c7a6e79520b2d0306` (`--standalone`)

---

## 1. Pinned Read-Only Preprint Artifacts (SHA-256)

| Staged Artifact (`symbiosis/round9/repos/bpo/`) | SHA-256 |
|---|---|
| `2609.15987.pdf` | `92c83c177a22d2a708d246c71468fdddbdda28a6f6fdd04ffd8590060f6dc31a` |
| `2609.15987.txt` (`pdftotext -layout`) | `6ea4059c62f3c27438857e361095ce4928b5edb50226e6f22a8f53f553d4015a` |
| `latex_src/main.tex` (`1,320` lines, exact source) | `a12f6d1ceab55b74334cbeeae1130e5e99c0ecfed4203344cc84d0f0aaa9c483` |
| `2609.15987.src.tar.gz` | `32a82df1094761791d14d03da527cd89fa847451d472afd65bc4a32cc1eff319` |

*(No public GitHub implementation repository URL is linked in `main.tex`; only the three Hugging Face AIME dataset URLs appear at `main.tex:1240`.)*

---

## 2. Law-2 Steelman Credit (Verified Strengths)

1. **Exactness of Theorem 1 on Reachable States (`main.tex:900-965, 1078-1204`):** The trajectory-level martingale proof eliminating intermediate state values $V^\mu(s_t)$ via Bellman telescoping $\sum_{t=1}^{|y|} A^\mu(s_t, y_t) = R(x, y) - V^\mu(x)$ and $\log Z_\mu(s_t) = D_{\mathrm{KL}}(\mu(\cdot|s_t) \,\|\, \pi^+(\cdot|s_t))$ is mathematically airtight under $\pi \in \Pi_\mu$.
2. **Elimination of Rare-Token Importance-Ratio Explosion (`main.tex:815`):** On rare exploration tokens ($\mu, \pi \ll 1$, e.g., $10\times$ jump $\mu = 1/1000, \pi = 1/100$), GRPO importance sampling explodes to $r = 10/1$ (clipped immediately at $1.28$), whereas BPO's smoothed weight stays $\omega = 1099/1090 \approx 1.008257$ (linear in $\pi - \mu$, mirroring RIPO `AUDIT-079` and DPPO).
3. **Arithmetic Consistency of Tables 1–3 (`main.tex:1054-1058, 1275-1279, 1308-1311`):** Every one of the `14` benchmark rows across `Qwen3-30B-A3B-Base` (Table 1) and `Qwen3-4B-Base` (Tables 2–3) satisfies exact 1-decimal rounding of $(A_{24} + A_{25} + A_{26})/3$ with maximum discrepancy `1/30` (`0.0333` pp), and all four headline gains (`+11.0, +7.0, +3.1, +4.1` pp, `main.tex:599`) match Table 1 exactly.
4. **Explicit MoE Router-Replay Control (`main.tex:1034`):** All `Qwen3-30B-A3B-Base` runs enable Rollout-Router Replay (R3) to control MoE trainer-inference routing mismatch, independently confirming `AUDIT-081` (Axis-1 TIM orthogonality).

---

## 3. Five Exact Pure-$\mathbb{Q}$ Mathematical Findings & Cross-Arm Unification

### 3.1 Pillar 1 — Exact Theorem 1 Proof, $\Pi_\mu$ Necessity, & Step-1 Linearization Fixed-Point Destruction (`BPO-THM1` / `BPO-LIN-01`)

Using exact base-2 exponential form (`eta_scale = 4`, common denominator $D = 2$) on the finite-horizon `T=2`, binary-vocabulary RLVR tree ($R(00)=1$, $R(01)=R(10)=R(11)=0$, uniform $\mu = (1/2, 1/2)$):

- **Exact Bellman & PMD Values:** $V^\mu(x) = 1/4$, $V^\mu(s_0) = 1/2$, $V^\mu(s_1) = 0/1$; $\pi^+_{\mathrm{root}} = (4/5, 1/5)$ ($Z_\mu = 5/4$), $\pi^+_{s_0} = (16/17, 1/17)$ ($Z_\mu = 17/8$), $\pi^+_{s_1} = (1/2, 1/2)$ ($Z_\mu = 1/1$).
- **Exact Partition-KL & Martingale Verification:** At every reachable state, $Z_\mu(s)^D = \exp(D_{\mathrm{KL}}(\mu \| \pi^+))^D$ (`25/16` at root, `289/64` at $s_0$, `1/1` at $s_1$) and $\prod_a \exp(d_\pi(s,a))^{D \mu_a} = 1/1$ identically for EVERY feasible $\pi$.
- **Exact Sufficiency, Necessity, & Domain Caveats (`verify_pmd_bellman_theorem1_exact`):**
  1. At $\pi = \pi^+$: $\exp(\delta(x,y;\pi^+,\mu))^2 = 1/1$ on all four trajectories (`00, 01, 10, 11`).
  2. Perturbing reachable state $s_0$ to $(1/2, 1/2)$ breaks trajectory residuals (`00 -> 16/1`, `01 -> 1/16`), proving necessity.
  3. On unreachable branch $\mu_{\mathrm{root}} = (1, 0)$: perturbing unreachable $s_1$ to $(9/10, 1/10)$ keeps all reachable residuals at `1/1`, verifying Theorem 1's domain restriction to $\mathcal{S}_x^\mu$ (`main.tex:906, 1196`).
  4. **Strict Necessity of $\pi \in \Pi_\mu$ (`main.tex:878, 1185`):** If $\mu_{\mathrm{root}} = (1, 0)$ and $\tilde{\pi}_{\mathrm{root}} = (1/2, 1/2) \notin \Pi_\mu$, then $\log(\tilde{\pi}/\mu) + D_{\mathrm{KL}}(\mu \| \tilde{\pi}) = \log(1/2) + \log(2) = 0$ identically — **without absolute continuity $\Pi_\mu$, infinitely many off-support policies achieve zero objective $\mathcal{L}(\tilde{\pi}) = 0$!** Our oracle enforces exact support equivalence (`ABSOLUTE_CONTINUITY_VIOLATION` / `SUPPORT_VIOLATION`).
- **Step-1 Linearization Destroys the PMD Fixed Point (`BPO-LIN-01`, `main.tex:981-989`):**
  - At $\pi = \pi^+$, the exact critic-free gradient (`Eq. 15` line 1, `main.tex:987`) is identically **`0/1`** because $\delta(x, y; \pi^+, \mu) = 0$.
  - After Step 1 replaces $\delta(x, y; \pi, \mu)/\eta$ with $R(x, y) - V^\mu(x)$ (`Eq. 15` line 2, `main.tex:988`), the step size $\eta$ vanishes and the linearized root logit gradient at $\pi = \pi^+$ is $-\mu_{\mathrm{root},0}\mu_{\mathrm{root},1}(V^\mu(s_0) - V^\mu(s_1)) = \mathbf{-1/8 \neq 0}$ (completely independent of $\pi$ and $\eta$!). Thus Step 1 **destroys Theorem 1's PMD fixed-point equivalence** and turns BPO Eq. (16) into unregularized Score Centering.

### 3.2 Pillar 2 — Exact Algebraic Identity Between BPO & Score Centering (`arXiv:2609.20807`, `AUDIT-080`) + Logit-Jacobian Cancellation

1. **Exact Full-Vocab Identity (`BPO-DUAL-01`, `main.tex:998`):**
   $$\nabla_\theta \Bigl(\log \pi_\theta(y_t^i \mid s_t^i) + D_{\mathrm{KL}}\bigl(\mu(\cdot \mid s_t^i) \,\|\, \pi_\theta(\cdot \mid s_t^i)\bigr)\Bigr) \;=\; \nabla_\theta \log \pi_\theta(y_t^i \mid s_t^i) - \mathbb{E}_{v \sim \mu}\bigl[\nabla_\theta \log \pi_\theta(v \mid s_t^i)\bigr].$$
   Before binary-KL approximation, **BPO Eq. (16) (`main.tex:998`) is literally identical to full-vocabulary Score Centering (`arXiv:2609.20807`)!**
   *(Terminology catch `BPO-KL-NAME`: `main.tex:968` and `main.tex:1002` both call $D_{\mathrm{KL}}(\mu \,\|\, \pi)$ "the full reverse KL divergence", mirroring Zhihu Tab 1's direction flip caught in `AUDIT-080` — relative to the optimized policy $\pi$, $D_{\mathrm{KL}}(\mu \,\|\, \pi)$ is the **forward / inclusive / M-projection KL**, whereas PMD's original Eq. (9) penalty $D_{\mathrm{KL}}(\pi \,\|\, \mu)$ is the reverse KL!)*
2. **Exact $K = 1$ Top-$K$ Duality (`BPO-DUAL-02`, `main.tex:1007, 1223`):**
   Setting Score Centering's Top-$K$ head set (`AUDIT-080`) to the singleton $\mathcal{H} = \{y_t\}$ gives tail mass ratio $\rho_{\{y_t\}} = \frac{1 - \mu(y_t)}{1 - \pi(y_t)}$, reconstructed surrogate $\hat{q}_{\{y_t\}}(y_t) = \mu(y_t)$ and $\hat{q}_{\{y_t\}}(v) = \rho_{\{y_t\}} \pi(v)$ ($v \neq y_t$), and exact logit gradient identity:
   $$\tilde{g}^{\mathrm{BPO}}_{\epsilon=0}(z; y_t) \;\equiv\; \frac{1 - \mu(y_t)}{1 - \pi(y_t)} \nabla_z \log \pi(y_t) \;\equiv\; e_{y_t} - \hat{q}_{\{y_t\}} \;\equiv\; \tilde{g}^{\mathrm{SC}}_{\mathcal{H}=\{y_t\}}(z; y_t).$$
3. **Exact Logit-Jacobian Cancellation vs. Autodiff Singularity (`BPO-CANCEL-03`):**
   - In exact logit space, the $(1 - \pi(y_t))$ denominator cancels *identically* against $\frac{\partial \log \pi(y_t)}{\partial z_{y_t}} = 1 - \pi(y_t)$, yielding exact $\ell_1$ logit-gradient norm $\|\tilde{g}^{\mathrm{BPO}}_{\epsilon=0}\|_1 = \mathbf{2(1 - \mu(y_t))} \le 2$ — **globally bounded for ALL $\pi \in (0, 1)$, independent of $\pi$!**
   - The explosion cited in `main.tex:1013` is purely an **autodiff factorization artifact** from computing `stopgrad((1-mu)/(1-pi))` separately before multiplying by $\nabla \log \pi(y)$.
   - Applying additive smoothing $\omega = \frac{1 + \epsilon - \mu}{1 + \epsilon - \pi} \in [\frac{\epsilon}{1+\epsilon}, \frac{1+\epsilon}{\epsilon}]$ removes the `0/0` NaN, but **damps the logit gradient on overconfident tokens by $\frac{1 - \pi}{1 + \epsilon - \pi} \to 0$** — e.g., at $\pi = 99/100, \mu = 1/2, \epsilon = 1/10$, exact unsmoothed $\rho_{\{y\}} = 50/1$ has exact canceled $\ell_1$ norm `1/1`, while smoothed BPO ($\omega = 60/11$, capped to `3/1`) damps the gradient on an overconfident negative-advantage token by **`1/11`** (`90.9%` loss of corrective signal!).
4. **Hyperparameter Omission (`BPO-SPEC-01`) & Exact Cap-Active Triangle Area (`BPO-CAP-06`):**
   - `main.tex` defines BPO's mask $M_t^i$ using $\epsilon_{\mathrm{low}}, \epsilon_{\mathrm{high}}$ (`main.tex:820-828`) yet **never specifies BPO's numeric $\epsilon_{\mathrm{low}}, \epsilon_{\mathrm{high}}$ values anywhere in the 1,320-line manuscript** (`bpo_clip_numeric_specified_in_tex = False`).
   - If paired with DAPO `[0.8, 1.28]` (`main.tex:1248`), then for EVERY $\hat{A}^i > 0$ token $M_t^i = 0$ whenever $\omega > 1.28$, so **`min(w, C)` NEVER fires for any positive advantage** (`cap_dead_for_positive_adv = True`) and ONLY fires on negative-advantage tokens inside the high-$\pi$/low-$\mu$ triangle $\pi > \frac{(C-1)(1+\epsilon) + \mu}{C}$ of exact unit-square area $\mathrm{Area}(\omega > C) = \frac{(1 + \epsilon - C\epsilon)^2}{2C}$:

| Ablation $(\epsilon, C)$ | Global $\omega$ Envelope | Exact Cap-Active Area | $\pi_{\min}$ (at $\mu=0$) | $\mu_{\max}$ (cap dead above) |
|---|---|---|---|---|
| $(\epsilon=0.05, C=3)$ | `[1/21, 21/1]` | `27/200` (`13.500%`) | `7/10` | `9/10` |
| $(\epsilon=0.10, C=2)$ | `[1/11, 11/1]` | `81/400` (`20.250%`) | `11/20` | `9/10` |
| $(\epsilon=0.10, C=3)$ *(default)* | `[1/11, 11/1]` | **`8/75` (`10.667%`)** | **`11/15`** | **`4/5`** |
| $(\epsilon=0.10, C=4)$ | `[1/11, 11/1]` | `49/800` (`6.125%`) | `33/40` | `7/10` |
| $(\epsilon=0.20, C=3)$ | `[1/6, 6/1]` | `3/50` (`6.000%`) | `4/5` | `3/5` |
| $(\epsilon=0.30, C=3)$ | `[3/13, 13/3]` | `2/75` (`2.667%`) | `13/15` | `2/5` |

This exact geometry explains *why* Table 3 (`main.tex:1308-1310`) exhibits only a `0.5` pp spread across $C \in \{2, 3, 4\}$.

### 3.3 Pillar 3 — Exact $|\mathcal{V}|=2$ vs. $|\mathcal{V}| \ge 3$ Off-Policy Drift-Cancellation Dichotomy (`BPO-DRIFT-04`)

| Vocabulary & Policy Witness | Full Score Centering $\|d\|_1$ | Unsmoothed BPO ($\epsilon=0$) $\|d\|_1$ | Smoothed BPO ($\epsilon=1/10$) $\|d\|_1$ |
|---|---|---|---|
| $|\mathcal{V}|=2$: $\pi=(1/4, 3/4), \mu=(1/2, 1/2)$ | **`0/1`** | **`0/1`** (binary KL = full KL) | **`12/119`** (`0.1008`, broken by $\epsilon$) |
| $|\mathcal{V}|=3$: $\pi=(1/4, 1/2, 1/4), \mu=(1/2, 1/4, 1/4)$ | **`0/1`** | **`5/24`** (`d = (+3/32, -5/48, +1/96)`) | **`203/816`** (`+19.4%` larger drift!) |

Because BPO changes the singleton partition $\mathcal{H} = \{y_t\}$ on every sampled token $y_t$, binary KL **breaks exact off-policy drift cancellation on every LLM vocabulary $|\mathcal{V}| \ge 3$**, and additive smoothing $\epsilon > 0$ further increases the trinary drift norm (`5/24 -> 203/816`).

### 3.4 Pillar 4 — 4-Axis Cross-Arm RLVR Synthesis (`AUDIT-079/080/081/082/083`)

- **Axis 1 (Kernel / MoE TIM — `AUDIT-081` REINFORCE Zero):** BPO (`main.tex:1034`) explicitly requires Rollout-Router Replay (R3) on `Qwen3-30B-A3B-Base`, confirming BPO cannot eliminate MoE routing TIM alone.
- **Axis 2 (First-Order Drift Cancellation — `AUDIT-080` Score Centering):** BPO Eq. (16) IS full Score Centering; BPO Eq. (17) IS Top-1 Score Centering ($\mathcal{H}=\{y_t\}$), trading zero-drift on $|\mathcal{V}| \ge 3$ for zero full-vocab logit overhead.
- **Axis 3 (Second-Order Geometry — `AUDIT-079` RIPO & `AUDIT-082` Triad):** Like RIPO's $|\sqrt{\pi} - \sqrt{\mu}|$ and DPPO's $|\pi - \mu|$, BPO's smoothed weight $\omega \approx 1 + (\pi - \mu)/(1 + \epsilon)$ tames rare-token IS blowup (`10/1 -> 1099/1090`), but flips the singularity from $\mu \to 0$ (IS) to $\pi \to 1$ (complementary ratio).
- **Fail-Closed Certifier (`evaluate_bpo_trust_region_gate`):** Enforces all nine safety invariants simultaneously (`BPO_TRUST_REGION_CLIPPED`, `BPO_SINGULAR_AUTODIFF`, `BPO_OVERCONFIDENT_DAMPING`, `BPO_CAP_GLOBALLY_UNREACHABLE`, `BPO_LOWER_MASK_GLOBALLY_DEAD`, `BPO_UPPER_MASK_GLOBALLY_DEAD`, `BPO_CAP_MASK_DEAD_CONFLICT`, `BPO_MULTITOKEN_DRIFT_ACTIVE` / `BPO_SMOOTHED_BINARY_DRIFT_ACTIVE`, `BPO_MOE_TIM_UNMITIGATED`), closing `BPO-BUG-01..03`.

### 3.5 Pillar 5 — Empirical Tables & Peak-Checkpoint Caveat (`main.tex:1042, 1054-1058, 1246`)

All `14/14` rows in Tables 1–3 verify exact 1-dp arithmetic (`max_abs_diff = 1/30`). However, `main.tex:1246` selects the **peak mean Avg@32 checkpoint** across evaluation checkpoints for Table 1 (`50.5%` peak vs `49.4%` final at step 400 vs `45.5%` DPPO final at step 400, `main.tex:1042`); peak-selection variance on 30-problem AIME benchmarks should be quarantined as an empirical `N0` caveat alongside the omitted $\epsilon_{\mathrm{low}}, \epsilon_{\mathrm{high}}$ specification (`BPO-SPEC-01`).

---

## 4. Law-4 Epistemic Quarantine (`N0` vs. `N1`)

- **`N1` (Mechanically Verified in `AUDIT-083R`):** Exact rational Theorem 1 tree verification, $\Pi_\mu$ necessity proof, Step-1 linearization fixed-point destruction (`-1/8 != 0`), exact BPO ↔ Score-Centering full-vocab & Top-1 algebraic identities, exact logit-Jacobian cancellation (`||g||_1 = 2(1-mu)`), exact cap-active triangle areas, exact $|\mathcal{V}|=2$ vs $|\mathcal{V}| \ge 3$ drift dichotomy, full-document multi-line `BPO-SPEC-01` scan & verbatim LaTeX/SHA-256 bindings, `14/14` table arithmetic audit, `4/4` isolated `-I` R4 parity, and `83/83` (`100.0%`) R5 mutation kill (`76/76` oracle + `7/7` audit).
- **`N0` (Prior Art & Unreproduced GPU Claims Quarantined):**
  1. Policy Mirror Descent (Lan 2023, Xiao 2022, Geist et al. 2019), Bellman equations (Sutton & Barto 1998), DPO/token-level log-ratio reparameterization (Rafailov et al. 2023/2024), and Binary KL (DPPO, Qi et al. 2026) are prior art (`N0`).
  2. `Qwen3-30B-A3B-Base` and `Qwen3-4B-Base` GPU training runs (`50.5%` / `25.8%` AIME Avg@32) are not re-executed here (no official code repo is linked in `arXiv:2609.15987`) and remain reported empirical claims (`N0`, with internal arithmetic verified `N1`).

---

## 5. Reproduction & Falsification Criteria

### Exact Reproduction Commands (Run from `symbiosis/round9/arm6-bellman-bpo/`)

```bash
# 1. Live read-only audit against staged arXiv:2609.15987 artifacts
python3 -I -B -W error bpo_bellman_audit.py --output bpo_bellman_certificate.json

# 2. Standalone pure-Q verification (zero external files required)
python3 -I -B -W error bpo_bellman_audit.py --standalone --json

# 3. Full R5 & adversarial red-team test suite (-I -O -B -W error)
python3 -I -O -B -W error test_bpo_bellman_r5.py

# 4. Aletheia v1.4.0 mutation kill verification (requires PYTHONPATH=<aletheia-repo>)
python3 -B -W error -m aletheia mutate bpo_bellman_oracle.py \
  --test-cmd "python3 -I -O -B -W error test_bpo_bellman_r5.py" --add-cwd
python3 -B -W error -m aletheia mutate bpo_bellman_audit.py \
  --test-cmd "python3 -I -O -B -W error test_bpo_bellman_r5.py" --add-cwd
```

### Falsification Criteria

`AUDIT-083` is falsified if any of the following is demonstrated:
1. Any non-determinism across isolated `python3 -I -B -W error` runs (live or `--standalone`).
2. Any float accepted by any public oracle function or serialized anywhere in `bpo_bellman_certificate.json`.
3. Any counterexample to the exact pure-$\mathbb{Q}$ identities (`BPO-DUAL-01/02`, `BPO-CANCEL-03`, `BPO-DRIFT-04`, `BPO-LIN-01`, `BPO-CAP-06`) or any bypass of `verify_pmd_bellman_theorem1_exact` or `evaluate_bpo_trust_region_gate`.
4. Any surviving mutant under `aletheia v1.4.0 mutate --add-cwd` in `bpo_bellman_oracle.py` or `bpo_bellman_audit.py`.
5. Any numeric assignment of BPO's $\epsilon_{\mathrm{low}}$ or $\epsilon_{\mathrm{high}}$ located in `latex_src/main.tex` (`a12f6d1c...`).
