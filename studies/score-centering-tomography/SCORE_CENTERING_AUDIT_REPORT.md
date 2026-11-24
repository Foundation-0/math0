# AUDIT-080: Exact Pure-Q Tomography of Score Centering (`arXiv:2609.20807v1`, `martin-marek/score-centering@fdca22b1`, Zhihu `2092277762245538186`)

> **Audit ID:** `AUDIT-080` (Wave 2 — Round 9, Arm R9-3)  
> **Scope (Strictly Read-Only, `0` external writes):**
> - `arXiv:2609.20807v1` (*Score Centering Stabilizes Off-policy Reinforcement Learning*, Martin Marek & Max Ryabinin, Together AI, 17 Sep 2026)
> - Official JAX reference repository `martin-marek/score-centering @ fdca22b19793babdf08e33e5ba51537e82cbed2f` (pinned from PDF Footnote 1)
> - Sanctioned live read-only Zhihu essay `2092277762245538186` by `Aiolus` (`zhihu_2092277762245538186_score_centering.md`, `9,437 B`, `sha256: 74443b91fa1668f3...`)
> **Artifacts:** [score_centering_tomography.py](score_centering_tomography.py) · [test_score_centering_r5.py](test_score_centering_r5.py) · [score_centering_certificate.json](score_centering_certificate.json)  
> **Novelty Classification (Law 4):** **`N1`** (engineering synthesis, verbatim defect discovery, exact pure-$\mathbb{Q}$ counterexample witnesses, and fail-closed Top-$K$ gate — zero `N2` claim; all foundational RL/KL/control-variate results quarantined under `N0` below).

---

## 1. Law-2 Steelman Credit (What Works and Why It Matters)

Before auditing defects, we explicitly credit the verified strengths of all three primary sources:

1. **Marek & Ryabinin (`arXiv:2609.20807v1`, Together AI):**
   - Cleanly identify that off-policy policy-gradient instability stems from the **drift term** $\mathbb{E}_\mu[A]\,\mathbb{E}_\mu[\nabla_\theta \log \pi_\theta]$ interacting with a *moving* sampler $\mu \to \pi_\theta$ (explaining why supervised fine-tuning with a *fixed* $\mu$ does not collapse under severe off-policy mismatch).
   - Derive an algebraically minimal, low-memory **Top-$K$ centering operator** (Eq. 6–8) whose backward pass touches only the $K$ gathered head log-probabilities while canceling drift identically under the tail-scaled reconstruction $\hat{\mu}$.
   - Demonstrate empirically across `1.7B`–`30B` MoE/dense models under FP8/INT8/INT4 train–inference mismatch (`TIM`) and asynchronous staleness that `TIS + SC` stabilizes training without storing full-vocabulary sampler logprobs.
   - Ship a remarkably clean, compact, readable JAX implementation (`martin-marek/score-centering@fdca22b1`, `losses.py` `173` lines) unifying `TIS`, `MIS`, `PPO`, `DAPO`, `GSPO`, `TOPR`, and `DPPO` through a single `ISCorrection` + `log_mass` abstraction, paired with an exact drift-cancellation test (`tests/test_loss.py`).
2. **`Aiolus` (Zhihu `2092277762245538186`):**
   - Provides a sharp bilingual walkthrough of the covariance-signal vs. drift decomposition, writes the exact two-term bias identity (`L106–108`) separating **distribution mismatch** $\operatorname{Cov}_\pi(A^\pi, z) - \operatorname{Cov}_\mu(A^\pi, z)$ from **advantage mismatch** $\operatorname{Cov}_\mu(A^\pi - A^\mu, z)$, and surfaces the key community counterpoint (`REINFORCE Zero`, NVIDIA, `alphaXiv:2611.reinforce-zero-kernel-alignment-asynchronous-rl`).

---

## 2. Pinned Read-Only Source Inventory & Cryptographic Anchors

Every file below was inspected strictly read-only (`0` mutations, `0` `__pycache__`, `git status --short` empty) and verified at runtime by `audit_live_repos()` in [score_centering_tomography.py](score_centering_tomography.py):

| Staged Relative Path (`../repos/`) | Bytes | Exact SHA-256 | Role |
|---|---:|---|---|
| `score-centering/arxiv_2609.20807.pdf` | `1,354,897` | `73173515a8f1244e7c20b5ffc2a47270b1e0fe31c099b075d35460af58b64019` | Primary paper PDF (`v1`) |
| `score-centering/arxiv_2609.20807.txt` | `56,454` | `a53342f3774e1effd43e386e06ae76766c0002262616d2cfa8a5726c90b87cd2` | Plain-text extraction (`1,570` lines) |
| `score-centering/arxiv_2609.20807_layout.txt` | `76,219` | `01d1959f6f0e929e60bd571f8bb9c5b16abc5b918b44846303672fbaa761ae16` | Layout-preserving extraction (`1,048` lines) |
| `zhihu/zhihu_2092277762245538186_score_centering.md` | `9,437` | `74443b91fa1668f3aa15e170de2520a02f356f64be549a60de2bcc84484f6d3d` | Sanctioned Zhihu Tab 1 transcript (`126` lines) |
| `score-centering/repo/losses.py` | `9,013` | `c9094e9663d1770badcfc0327c41aa201e408dd0b868d6656444c4f497b04820` | Official JAX loss & IS/SC engine (`fdca22b1`) |
| `score-centering/repo/tests/test_loss.py` | `2,087` | `199fa0e2d684a6727940c7bfad9c6afee75e0446b7a0132911c9383c798aa91d` | Official drift-cancellation test (`fdca22b1`) |
| `score-centering/repo/README.md` | `8,821` | `94422aa05a3dd0e43b74427fd8c9c80612f76256ee509d43b15207ec1b190c9c` | Official JAX/PyTorch snippets (`fdca22b1`) |

---

## 3. Pillar 1 — Exact Pure-$\mathbb{Q}$ Foundations & Two Verbatim Slips in Zhihu Tab 1

### 3.1 Drift–Signal Invariance (`arXiv:2609.20807` Eq. 3 & 5)
On tabular softmax logits $\ell \in \mathbb{R}^V$ with score $s_v = \nabla_\ell \log \pi(v) = e_v - \pi \in \mathbb{Q}^V$, [score_centering_tomography.py](score_centering_tomography.py) verifies identically in exact $\mathbb{Q}$ (`trainer_p = (1/2, 1/4, 1/4)`, `sampler_q = (1/4, 1/2, 1/4)`, `A = (4, 0, 0)`):
- On-policy zero mean: $\mathbb{E}_\pi[s] = (0, 0, 0)$.
- Off-policy decomposition: $g_{\mathrm{off}} = (1/2, -1/4, -1/4) = \underbrace{(-1/4, 1/4, 0)}_{\text{drift }\mathbb{E}_\mu[A]\mathbb{E}_\mu[s]} + \underbrace{(3/4, -1/2, -1/4)}_{\text{signal }\operatorname{Cov}_\mu(A, s)}$.
- Centered score $\tilde{s} = s - \mathbb{E}_\mu[s]$ gives $\mathbb{E}_\mu[\tilde{s}] = (0, 0, 0)$ and $\operatorname{Cov}_\mu(A, \tilde{s}) = \operatorname{Cov}_\mu(A, s) = g_{\mathrm{SC}} = (3/4, -1/2, -1/4)$.

### 3.2 `SC-ZHIHU-01` [MATH SLIP] — Wrong KL Direction (`zhihu_2092277762245538186_score_centering.md:42`)
- **Verbatim claim (`zhihu:42`):** claims $\mathbb{E}_\mu[\nabla \log \pi(a|s)]$ is *"the gradient of the **reverse KL** between $\mu$ and $\pi$"* (`注：因为这一项本质是\mu,\pi两者reverse KL的梯度`).
- **Exact pure-$\mathbb{Q}$ disproof:**
  $$\nabla_\ell D_{\mathrm{KL}}(\mu \| \pi) = \nabla_\ell \Big(-\sum_v \mu_v \log \pi_v\Big) = -\sum_v \mu_v s_v = \pi - \mu \implies +\mathbb{E}_\mu[s] = -\nabla_\ell D_{\mathrm{KL}}(\mu \| \pi).$$
  Thus $+\mathbb{E}_\mu[\nabla \log \pi]$ is the negative gradient of the **forward / M-projection KL** (cross-entropy / SFT distillation toward teacher $\mu$, matching `arXiv:2609.20807` Sec. 4 L406), **not** reverse KL $D_{\mathrm{KL}}(\pi \| \mu)$.
- **Dyadic pure-$\mathbb{Q}$ non-collinearity witness:** With $\pi = (1/2, 1/4, 1/4)$ and $\mu = (1/4, 1/2, 1/4)$, the likelihood ratios are exact powers of 2: $\pi_v / \mu_v = (2, 1/2, 1)$, so $\log_2(\pi_v / \mu_v) = (+1, -1, 0) \in \mathbb{Z}^3$. Therefore:
  - $\mathbb{E}_\mu[s] = -\nabla_\ell D_{\mathrm{KL}}(\mu \| \pi) = (-1/4, 1/4, 0)$.
  - $\nabla_\ell D_{\mathrm{KL}}(\pi \| \mu) / \ln 2 = \sum_v \pi_v \log_2(\pi_v / \mu_v) s_v = (3/8, -5/16, -1/16)$.
  - The $2 \times 2$ determinant on coordinates `(0, 2)` is $(-1/4)(-1/16) - (0)(3/8) = \mathbf{1/64 \neq 0}$, proving $\mathbb{E}_\mu[s]$ is **not even collinear** with $\nabla_\ell D_{\mathrm{KL}}(\pi \| \mu)$ (neither $+\nabla$, nor $-\nabla$, nor any scalar multiple!).

### 3.3 `SC-ZHIHU-02` [MATH SLIP] — Sign Flip in $\Delta = \text{bias}_{\mathrm{SC}} - \text{bias}_{\mathrm{off}}$ & Both-Sign Witnesses (`zhihu:106-112`)
- **Verbatim claim (`zhihu:112`):** writes `|Cov_pi(A^pi, z) - Cov_mu(A^mu, z)| - |Cov_pi(A^pi, z) - Cov_mu(A^mu, z) + E_mu[A] E_mu[z]|`.
- **Exact identity:** Writing $\delta_{\mathrm{cov}} = \operatorname{Cov}_\pi(A^\pi, z) - \operatorname{Cov}_\mu(A^\mu, z)$ and $d = \mathbb{E}_\mu[A^\mu]\,\mathbb{E}_\mu[z]$:
  $$e_{\mathrm{SC}} = g_{\mathrm{true}} - g_{\mathrm{SC}} = \delta_{\mathrm{cov}}, \qquad e_{\mathrm{off}} = g_{\mathrm{true}} - g_{\mathrm{off}} = g_{\mathrm{true}} - (g_{\mathrm{SC}} + d) = \delta_{\mathrm{cov}} \mathbf{-} d.$$
  `zhihu:112` has the **wrong sign** (`+ d` instead of `- d`).
- **Exact pure-$\mathbb{Q}$ witnesses on binary softmax $\pi = (3/4, 1/4)$, $\mu = (1/2, 1/2)$:**

| Case | $A^\pi = A^\mu$ | $e_{\mathrm{SC}} = \delta_{\mathrm{cov}}$ | $e_{\mathrm{off}} = \delta_{\mathrm{cov}} - d$ | Exact $\Delta_{L_1}$ | Exact $\Delta_{L_2^2}$ | Exact $\Delta_{L_\infty}$ | Buggy `zhihu:112` $\Delta_{L_1}$ |
|---|---|---|---|---:|---:|---:|---:|
| **$\Delta < 0$ (SC strictly better)** | `(1, 1)` | `(0, 0)` | `(1/4, -1/4)` | **`-1/2`** | **`-1/8`** | **`-1/4`** | `-1/2` |
| **$\Delta > 0$ (SC strictly worse!)** | `(3, -1)` | `(-1/4, 1/4)` | **`(0, 0)`** | **`+1/2`** | **`+1/8`** | **`+1/4`** | **`-1/2` (WRONG SIGN!)** |

When drift $d = (-1/4, 1/4)$ happens to cancel $\delta_{\mathrm{cov}} = (-1/4, 1/4)$, vanilla off-policy REINFORCE achieves **zero** single-step bias while Score Centering incurs bias `1/2`, and `zhihu:112`'s `+ d` slip flips the predicted sign from `+1/2` to `-1/2`.

---

## 4. Pillar 2 — Exact Top-$K$ Conservation Subtlety, Singularity (`SC-SING-01`), & `TIS`/`MIS` Tail-Scale Dichotomy

### 4.1 Head Residual Sum vs. Full-Vocab Conservation & Residual Tail-Shape Bias
On $V = 4$, head $\mathcal{H} = \{0, 1\}$, tail $\mathcal{T} = \{2, 3\}$ ($|\mathcal{T}| = 2$), $\pi = (1/2, 1/4, 1/8, 1/8)$ ($P_H = 3/4$), $\mu = (1/4, 1/4, 3/8, 1/8)$ ($Q_H = 1/2$), $\rho = (1 - Q_H)/(1 - P_H) = 2$:
1. **Head residual sum is NOT identically zero:** $\sum_{v \in \mathcal{H}} (\mu_v - \rho \pi_v) = (-3/4) + (-1/4) = \mathbf{-1 = 1 - \rho = (Q_H - P_H)/(1 - P_H)}$ (zero iff $Q_H = P_H$).
2. **Full-vocab logit-gradient conservation IS identically zero (for $P_H < 1$):** $\nabla_\ell \sum_{v \in \mathcal{H}} (\mu_v - \rho \pi_v) \log \pi_v = \hat{\mu} - \pi = (-1/4, 0, 1/8, 1/8)$, whose entries sum to **`0/1`**, giving exact zero drift $\mathbb{E}_{\hat{\mu}}[\tilde{s}_{\mathrm{top}\text{-}k}] = (0, 0, 0, 0)$.
3. **True-$\mu$ tail-shape residual bias:** $\mathbb{E}_\mu[\tilde{s}_{\mathrm{top}\text{-}k}] = \sum_{v \in \mathcal{T}} (\mu_v - \rho \pi_v) s_v = \mathbf{(0, 0, 1/8, -1/8)}$ (`L1 = 1/4`), vanishing only when $\mu|_{\mathcal{T}} \propto \pi|_{\mathcal{T}}$ or $|\mathcal{T}| = 1$.

### 4.2 `SC-SING-01` [HIGH] — Boundary Singularity (`0/0`, `+\infty`) and `eps = 1e-6` Blowup
- **Unprotected Sec. 4.1 (`arXiv` L503) & `zhihu:88`:** `(1 - sum(q_H)) / (1 - sum(p_H))` yields `0/0 = NaN` when $P_H = Q_H = 1$ and `(1 - Q_H) / 0 = +inf` when $P_H = 1, Q_H < 1$.
- **`eps = 1e-6` floor (`arXiv` App. A.3 L1067–1070, `losses.py:147`, `README.md:51-53,88-90`):** Under a peaked trainer (`1 - P_H = 1/10_000_000`) paired with heavy quantized-sampler TIM tail (`1 - Q_H = 1/10`; note paper Sec. A.4 L1091 logs `4.2%` worst-batch tail mass at INT8/INT4 `30B`):
  - Exact $\rho = 10^6$; floored $\rho_\varepsilon = (1/10) / 10^{-6} = \mathbf{100{,}000}$!
  - Head residuals explode to $\approx -50{,}000$ (`L1 = 999990999/10000`, ~$10^5\times$ amplification).
  - Reconstructed simplex mass breaks conservation: $\sum_v \hat{\mu}_{\varepsilon, v} = 9/10 + 10^5 \cdot 10^{-7} = \mathbf{91/100 \neq 1}$ (dropping `9/100` of tail mass uncanceled).

### 4.3 Exact `TIS+SC` vs. `MIS+SC` vs. Vanilla `SC` Tail-Scale Dichotomy ($\alpha(\rho) = \rho f(1/\rho)$)

| $\rho$ | Vanilla `SC` ($\alpha = \rho$) | `TIS + SC` ($\alpha = \min(1, 2\rho)$) | `MIS + SC` ($\alpha = \mathbf{1}[1/5 \le \rho \le 2]$) | Regime |
|---:|---:|---:|---:|---|
| `1/10` | `1/10` | `1/5` | **`0/1`** | Below `MIS` cliff ($\rho < 1/5$) |
| `1/5` | `1/5` | `2/5` | **`1/1`** | `MIS` lower closed boundary |
| `1/2` | `1/2` | `1/1` | `1/1` | `TIS` saturation knee |
| `1/1` | `1/1` | `1/1` | `1/1` | Matched tail mass |
| `2/1` | `2/1` | `1/1` | **`1/1`** | `MIS` upper closed boundary |
| `5/1` | `5/1` | `1/1` | **`0/1`** | Above `MIS` cliff ($\rho > 2$) |
| `100000/1` | **`100000/1` (UNBOUNDED!)** | **`1/1` (BOUNDED!)** | **`0/1` (CLIFF!)** | Peaked trainer + TIM tail |

This exact dichotomy explains mathematically why `TIS + SC` automatically tames the `SC-SING-01` tail-ratio blowup ($\alpha(\rho) \in [0, 1]$ unconditionally!) whereas vanilla `SC` blows up linearly in $\rho$ and `MIS + SC` suffers discontinuous `1 -> 0` cliffs.

---

## 5. Pillar 3 — Five Verbatim Live Findings in `martin-marek/score-centering @ fdca22b1` (`SC-CODE-01..05`)

| ID | Severity | Exact Location | Defect Mechanism | Exact Pure-$\mathbb{Q}$ Witness Receipt |
|---|---|---|---|---|
| **`SC-CODE-01`** | **HIGH** | `losses.py:139-153` | Independent `if score_center and full:` (`L139`) followed by `if "center_ids" in b: ... if score_center:` (`L143, 149`, missing `elif`) subtracts the centering term **TWICE** (`s - 2 s_bar`) whenever a batch carries both full vocab logprobs and `center_ids` (e.g., to log `kl_head`). | Single-centered drift = `(0, 0, 0)`; double-centered drift = **`(1/4, -1/4, 0) = -E_q[s]`** (exact sign flip!). |
| **`SC-CODE-02`** | **HIGH** | `losses.py:116-121, 162-169`; `README.md:132-133` | Guard `L121` only rejects `stat == "tv"` (`DPPO`), permitting sequence-level IS (`GSPO` `level=seq_mean low=0.9997 high=1.0004 outside=drop sign=ppo`, `TOPR` `level=seq_sum high=1.0 outside=clamp sign=neg`) composed with token-level `SC` (`token_c = None`). Because $w_{\mathrm{seq}}(y)$ depends on the entire trajectory, $\mathbb{E}_q[A\,w_{\mathrm{seq}}(y) \sum_t \tilde{s}_t] = A\,\operatorname{Cov}_q(w_{\mathrm{seq}}, \sum_t \tilde{s}_t) \neq 0$ even under constant advantage! | 2-token binary trajectory ($p=(3/4, 1/4), q=(1/2, 1/2)$): upstream `TOPR` (`README.md:133`, `sign=neg`) gives `(0, 0)` at `A=+1` and **`(-3/16, +3/16)` (`L1 = 3/8`) at `A=-1`**; upstream `GSPO` (`README.md:132`, `sign=ppo`) gives **`(-1/8, +1/8)` (`L1 = 1/4`) at `A=+1`** and **`(-3/8, +3/8)` (`L1 = 3/4`) at `A=-1`**! |
| **`SC-CODE-03`** | **MED** | `losses.py:65-75, 146-152` | Dual zero-tail defect: **(a)** raw `q_tail = 1.0 - q_head.sum(-1)` is unclamped in `kl_head` (`L148`), so slight overshoot $Q_H = 1 + 10^{-6}$ multiplies `q_tail < 0` by `log(1e-9) < -20`, adding spurious positive KL **`> 1/50000`**; **(b)** when `q_tail == 0` (`rho == 0`) and `c.high == math.inf` (unclipped or lower-only IS), `log_mass(0.0, -inf, ..., c)` evaluates `(0 >= -inf) & (0 <= inf) = True` and hallucinates **`alpha = 1`** instead of `0`, leaving missing-support IS drift uncanceled! | $V=4, \mathcal{H}=\{0,1\}, p=(1/4)^4, q=(1/2, 1/2, 0, 0)$: buggy `losses.py` (`alpha=1`) leaves uncanceled drift **`(1/8, 1/8, -1/8, -1/8)`**; hardened gate (`alpha=0`) reduces drift to **`(0, 0, 0, 0)`**! |
| **`SC-CODE-04`** | **MED** | `losses.py:147`, `README.md:51-53,88-90` | `eps = 1e-6` tail denominator floor permits `10^5x` residual amplification and `9/100` simplex mass loss under sharp trainer + TIM tail. | See Pillar 2 (`rho_eps = 100000/1`, `sum q_hat = 91/100`). |
| **`SC-CODE-05`** | **LOW / TEST** | `tests/test_loss.py:28-30` | Unit test ONLY tests `k = V - 1 = 2` on `V = 3` (`\|T\| = 1`), where $\rho p_{V-1} \equiv q_{V-1}$ makes $\hat{q} \equiv q$ tautologically exact (`0%` coverage of `k < V - 1` tail-shape bias, `P_H -> 1`, double-centering, `seq_c + SC`, and `Q_H = 1` missing-support IS). | On `V=3, k=2`: `rho * p_tail == q_tail == 1/4` identically; on `V=4, k=2`: non-zero tail-shape bias `(0, 0, 1/8, -1/8)`. |

---

## 6. Pillar 4 — Hardened Fail-Closed Gate & Cross-Round Bridges (`AUDIT-073R`, `AUDIT-074R`)

### 6.1 Hardened Pure-$\mathbb{Q}$ Contract & Top-$K$ Gate
[score_centering_tomography.py](score_centering_tomography.py) implements two fail-closed pure-$\mathbb{Q}$ primitives:
1. `validate_batch_contract(batch_spec)`: strictly validates exact schema keys (rejecting unknown/missing keys, non-bool flags, whitespace/case-mangled strings), unconditionally enforces `batch_mode` consistency across `"none"`/`"full_vocab"`/`"topk_head"` (rejecting contradictory flags and simultaneous `has_full_vocab & has_topk_head` even when `score_center=False`), unconditionally enforces `is_stat == "ratio"` when `is_level in ("none", "seq_sum")`, and refuses `sc-double-centering-forbidden` (closes `SC-CODE-01`), `seq_mean`/`seq_sum` IS with `score_center=True` (closes `SC-CODE-02`), and `is_stat="tv"` with `score_center=True`.
2. `evaluate_hardened_topk_score_centering(...)`: strictly validates simplex positivity, exact-integer `topk_ids` (no booleans, no duplicates, `1 <= len < V`, in-range `0..V-1`), exact `q_head` bounds (`0 <= q_v <= 1`, `0 < sum <= 1`), the exact top-$K$ **pigeonhole dominance inequality** `(V - K) * min(q_head) >= q_tail` (blocking non-top-$K$ and zero-mass heads), impossible zero-probability `sampled_token` checks (`q_head[pos] > 0` for head tokens; `q_tail > 0` for tail tokens), enforces **`q_tail == 0 => alpha = 0`** (`ZERO_TAIL_SUPPORT_GUARDED`, closing `SC-CODE-03`), and triggers exact rational shrinkage **`rho_eff = min(rho_max, (q_tail + tail_floor) / (p_tail + tail_floor))`** with status **`DAMPED_FALLBACK_REQUIRED`** whenever `p_tail < tail_floor` or `rho > rho_max` (capping the `10^5x` blowup cleanly to `10/1` while preserving exact full-vocab logit-gradient conservation `sum == 0`!).
3. `audit_live_repos(repos_dir)`: strictly verifies all `7/7` pinned SHA-256 digests and `13/13` verbatim line anchors read-only, while hardening `.git/HEAD` symbolic ref resolution against `..` traversal, non-`refs/` paths, and `.git/` symlink escapes (`repo-git-ref-invalid`, `repo-git-ref-escape`).

### 6.2 Bridge to `AUDIT-073R` (`sous-labs/songe`, `SNG-01`) — Signed Forward-KL Anti-Distillation
Because $+\mathbb{E}_\mu[s] = -\nabla_\ell D_{\mathrm{KL}}(\mu \| \pi)$, the off-policy drift term $\mathbb{E}_\mu[A]\,\mathbb{E}_\mu[s] = -\mathbb{E}_\mu[A]\,\nabla_\ell D_{\mathrm{KL}}(\mu \| \pi)$ acts as a **signed forward-KL distillation force**:
- When $\mathbb{E}_\mu[A] > 0$, drift pulls $\pi \to \mu$ (standard forward-KL distillation).
- When $\mathbb{E}_\mu[A] < 0$ (e.g., `losses.py:21` `zero_minus` reward mode `(0, -1)` at `1/4` pass rate giving $\mathbb{E}_\mu[A] = -3/4$), drift equals **`+(3/4) \nabla_\ell D_{\mathrm{KL}}(\mu \| \pi) = (3/16, -3/16, 0)`**, actively performing **anti-distillation** that pushes $\pi$ *away* from $\mu$ — the exact geometric counterpart of `songe`'s `SNG-01` reversed teacher-KL gradient!

### 6.3 Bridge to `AUDIT-074R` (`Inkling-2-Mini-loom`, `LOOM-IR-03`) — Silent `top_k=64` Truncation Trap
In `AUDIT-074R`, AMD Loom's `@g_head_select` silently clamps `top_k = 0` to `k = 64` out of `V = 200,058` (`32/100029` of vocabulary) and renormalizes strictly over those `64` tokens (`TV = 35/64`). Feeding such a truncated sampler into Score Centering (`k = 128`) hands the trainer **`Q_H = 1, q_tail = 0`** while concealing `35/64` of true pre-truncation tail mass: on our exact 4-token coarse-graining witness (`q_true = (15/64, 14/64, 20/64, 15/64)` vs. `q_loom = (15/29, 14/29, 0, 0)` under uniform $p$), Score Centering's centering target diverges from the true full-vocab drift by **`L1 = 35/32`** AND hits `SC-CODE-03` under unclipped IS!

---

## 7. Law-4 `N0` Prior-Art Quarantine & Honest `N1` Attribution

Aligned verbatim with `../cartography/ROUND9_PORTALS.md` (`R9-N0-01`–`R9-N0-10`):

- **`N0` (Quarantined Prior Art — NOT claimed as new):**
  - `R9-N0-05`: Classical KL / $f$-divergences (Csiszár 1967), M-projection vs. I-projection (Amari 1998).
  - `R9-N0-06`: REINFORCE (Williams 1992), score-function control variates / baselines (Greensmith–Bartlett–Baxter 2004; Ranganath et al. 2014), truncated IS `TIS` (Ionides 2008), PPO (Schulman et al. 2017), GRPO (Shao et al. 2024).
  - `R9-N0-07`: Published Zhihu essay by `Aiolus` (`2092277762245538186`) and Marek & Ryabinin (`arXiv:2609.20807v1`, `martin-marek/score-centering@fdca22b1`).
  - `R9-N0-09`: Prior expedition verified artifacts (`AUDIT-073R` `songe` `SNG-01`, `AUDIT-074R` `Inkling` `LOOM-IR-03`).
  - `R9-N0-10`: Read-only SHA-256 digests and verbatim line anchors of external sources.
- **`N1` (Honest Engineering & Verification Contribution of `AUDIT-080`):**
  1. Pure-$\mathbb{Q}$ exact tomography & non-collinearity / sign-flip counterexamples (`SC-ZHIHU-01`, `SC-ZHIHU-02`, both $\Delta < 0$ and $\Delta > 0$).
  2. Exact separation of head-residual sum (`1 - rho`) from full-vocab logit conservation (`0`), residual tail-shape bias (`L1 = 1/4`), `eps=1e-6` `10^5x` blowup + `91/100` simplex defect (`SC-SING-01`), and `TIS`/`MIS`/`SC` tail-scale dichotomy.
  3. Five verbatim live findings in `martin-marek/score-centering@fdca22b1` (`SC-CODE-01..05`) with exact rational witnesses.
  4. Hardened fail-closed pure-$\mathbb{Q}$ contract validator & regularized Top-$K$ gate (`validate_batch_contract`, `evaluate_hardened_topk_score_centering`) + cross-round bridges to `AUDIT-073R` & `AUDIT-074R`.

---

## 8. Reproducibility & Verification Receipts (Aletheia v1.4.0)

- **Live-anchored certificate:** [score_centering_certificate.json](score_centering_certificate.json) (`sha256: dc9671d3fda0adfd140986d83fbb70c6c86d1ddedc830734765a194558494d36`, `7/7` source files & `13/13` verbatim anchors verified, `0` floats).
- **Standalone pure-$\mathbb{Q}$ certificate:** `sha256: 6d5c12aa9032e6f3d405b42f7ba8135960dd952a0c65024b71d6ed8f62f8644e`.
- **Aletheia v1.4.0 Audit Gate:** `aletheia audit-check . --strict-ancestors --scripts score_centering_tomography.py test_score_centering_r5.py` `PASS` (`0` defects, `8/8` ancestor dirs clean, `0` bare `assert`s, `0` floats, `0` local absolute-path or file-URI leaks, `0` CRLF, `0` `__pycache__`).
- **R4 Determinism:** `4/4` isolated `python3 -I -O -B -W error` runs bit-identical (live `--json`, standalone `--json`, human summary, `test_score_centering_r5.py`).
- **R5 Mutation Gate:** `aletheia v1.4.0 mutate score_centering_tomography.py --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_score_centering_r5.py"` **`81/81` (`100.0%`) KILLED, `0` survivors**.
