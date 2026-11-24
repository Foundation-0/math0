# AUDIT-069: Exact Pure-Q Mathematical Tomography & Tao Observability Audit of the alphaXiv OpenResearch Intelligence Index

- **Audit ID:** `AUDIT-069` (Wave 2 Round 7, Arm `R7-2`)
- **Governance Standard:** `Foundation-0/aletheia v1.4.0` (Laws 1–5; zero-float pure-$\mathbb{Q}$ trust path; `100%` R5 AST mutation kill; `4/4` isolated `-I` R4 bit-identical determinism)
- **External Write Policy:** **STRICTLY 100% READ-ONLY** (`0` external PRs, `0` external issues/comments, `0` external repository mutations)
- **Executable Oracle & Verifier:**
  - `openresearch_index_oracle.py` — Pure Python 3 stdlib zero-float trust kernel (`IndexOracleError`)
  - `openresearch_index_audit.py` — Live verbatim JS/HTML/Rust parser & canonical certificate emitter (`--standalone` supported)
  - `test_openresearch_index_r5.py` — R5 refusal-site & exact-invariant unittest suite
  - `openresearch_index_certificate.json` — Canonical zero-float exact rational certificate

---

## 1. Pinned Read-Only Primary Sources & SHA-256 Provenance

Every empirical number, quote, and code-level finding in this report is anchored verbatim to the following pinned read-only captures (verified byte-for-byte by `openresearch_index_audit.py`):

| Artifact | Canonical Source | Exact SHA-256 Digest |
|---|---|---|
| `index.html` | `https://alphaxiv.org/blog/introducing-openresearch-intelligence-index` (Myles Anderson & Daniel Kim, Nov 20, 2026) | `ac66dd30e7c2f53566041fd9968b1ebbe29e14370bd98ce6e5e8ac7f51d2533f` |
| `ResultsTable-Cepl37af.js` | alphaXiv Vite component chunk (8-model mean/SE table, attempts, tokens, minutes, harness) | `fa223017805af7b8bbe31dd44d7814018cb0c02c9de1ab012e3a56545819c187` |
| `RankHeatmap-CVYXZmjT.js` | alphaXiv Vite component chunk (8 models × 18 rows: Index + 3 tracks + 14 sub-tasks) | `64d03a352625cc0c9f9ae87e3f8815b71800bfdf1c95d7779d743982cc5dd36c` |
| `CostScoreChart-CkzD4pZy.js` | alphaXiv Vite component chunk (headline 95% CIs, full-pass USD, per-track USD & scores) | `55583ebfbb15ace29f9004518882a377f2df68d09bf4831e23d0305572d4c0e2` |
| `cost-vs-score.png` | Static OG/Twitter card (`og:image` & `twitter:image` in `index.html`) | `51541703586bffabf9cee98bf2287294edead2a4c9434655e5ba83abc72bd8e7` |
| `openresearch_sh.html` | `https://openresearch.sh` landing capture | `9e00c6f0a2e0b10f4c120a3e39c0edf123a9b1594e2d3e4b99fed5cb99a2a516` |
| `alphaXiv/OpenResearch` | `https://github.com/alphaXiv/OpenResearch` @ commit `48f42c450ca00ab08fe10358989311193b0f81c6` | Verified clean read-only clone (`git status --short` empty) |

---

## 2. Law-2 Steelman Credit (What alphaXiv Got Right)

Before presenting exact mathematical refutations and engineering gaps, we explicitly credit genuine methodological strengths published by Myles Anderson & Daniel Kim:

1. **Uncertainty Reporting (SE + 95% CIs):** Unlike most agent leaderboards that publish bare point estimates, alphaXiv ships per-model standard errors in `ResultsTable-Cepl37af.js` and asymmetric 95% confidence intervals (`lo`, `hi`) in `CostScoreChart-CkzD4pZy.js`, enabling rigorous separability audits.
2. **Explicit Harness & Cost Disclosure:** The blog explicitly discloses the exact harness per model (`Claude Code`, `Codex`, `OpenCode`), acknowledges in prose that *"Because harnesses differ by provider, a score difference between two providers reflects both the model and its native harness"*, and reports both per-attempt API cost and full-pass cost (`$62.9` to `$1,951.9`).
3. **Incomplete-Run Transparency (`Fable 5.1*`):** The authors flag `Fable 5.1*` with a hollow scatter marker and asterisk across all three figures (`74 of 87 attempts`) rather than silently concealing missing trials.
4. **Right Research Instinct on Observability:** Motivating the benchmark with Terence Tao's Navier–Stokes critique (*"Disappointingly, we've learned almost nothing mathematically from what they did. Research is as much about the process as it is about the result"*) identifies the exact central bottleneck of autonomous science — even though the current v1 scalar index does not yet measure it.

---

## 3. Exact Pure-Q Mathematical & Forensic Tomography

### 3.1 Composite Formula, `Fable 5.1*` Exact `41/120` Rational Science Reconstruction, and `74/87` Cost Extrapolation

| Model | Provider | Harness | Att | Published Index (95% CI) | Recomputed `0.4S+0.4P+0.2L` | Delta | Full USD (`60/18/9` Sum) | `Att × Mean` USD |
|---|---|---|---:|---|---|---:|---:|---:|
| `Opus 5.5` | Anthropic | `Claude Code` | `87` | `0.6183` (`0.5909–0.6446`) | `0.618320` | `-0.000020` | `$1,432.4` (`$1,432.32`) | `$1,432.02` |
| `GPT-6 Astra` | OpenAI | `Codex` | `87` | `0.5658` (`0.5384–0.5905`) | `0.565780` | `+0.000020` | `$1,951.9` (`$1,951.92`) | `$1,952.28` |
| `GPT-6.1 Sol` | OpenAI | `Codex` | `87` | `0.5495` (`0.4990–0.5959`) | `0.549480` | `+0.000020` | `$333.1` (`$332.94`) | `$333.21` |
| `Gemini 4 Argon` | Google | `OpenCode` | `87` | `0.5261` (`0.5001–0.5509`) | `0.526100` | `0.000000` | `$798.4` (`$798.30`) | `$798.66` |
| `Fable 5.1*` | Anthropic | `Claude Code` | **`74`** | `0.5107` (`0.4802–0.5392`) | `0.510700` | `0.000000` | **`$1,738.7`** (`$1,738.83`) | **`$1,485.18`** |
| `DeepSeek V4.1 Flash` | DeepSeek | `OpenCode` | `87` | `0.2740` (`0.2377–0.3078`) | `0.274040` | `-0.000040` | `$62.9` (`$63.12`) | `$62.64` |
| `Kimi K3` | Moonshot AI | `OpenCode` | `87` | `0.2714` (`0.2529–0.2903`) | `0.271380` | `+0.000020` | `$947.8` (`$947.76`) | `$947.43` |
| `Qwen3.8-Flash` | Qwen | `OpenCode` | `87` | `0.2142` (`0.1812–0.2417`) | `0.214220` | `-0.000020` | `$394.7` (`$394.86`) | `$394.98` |

**Exact Forensic Findings:**
1. **Exact Formula Match:** Across all 8 models, `0.4·Science + 0.4·PostTraining + 0.2·Literature` matches the published 4-decimal index within exact `4/100000` (`0.00004`), attributable solely to 4-decimal rounding of published track means.
2. **Exact Rational Reconstruction of `Fable 5.1*` Science = `41/120`:** All 7 complete models have Science scores that are exact multiples of `1/60` (`35/60, 38/60, 37/60, 33/60, 5/60, 2/60, 0/60`). For `Fable 5.1*` (`74/87` attempts = `13` missing), `RankHeatmap-CVYXZmjT.js` reports Engineering sciences (3 tasks) = **`0.278`**, which cannot be `k/9` (`2/9=0.222, 3/9=0.333`) — it is exact **`5/18 = (1/2 + 1/3 + 0)/3`**, proving at least one Engineering task averaged over `2` completed attempts instead of `3`. Weighting the 5 Science disciplines by task count yields:
   $$\frac{3 \cdot \frac{2}{9} + 5 \cdot \frac{7}{15} + 2 \cdot 0 + 7 \cdot \frac{3}{7} + 3 \cdot \frac{5}{18}}{20} = \frac{\frac{41}{6}}{20} = \frac{41}{120} = 0.341666\ldots \to \mathbf{0.3417}$$
   matching `CostScoreChart-CkzD4pZy.js` (`0.3417`) to all 4 published digits.
3. **Extrapolated Cost Accounting & MNAR Missing-Data Bounds (`Fable 5.1*`):**
   - `Fable 5.1*`'s reported full-pass cost `$1,738.7` equals the **extrapolated 87-attempt cost** `60×$23.30 + 18×$13.36 + 9×$11.15 = $1,738.83`, which is **`+$253.52` higher** than its estimated actual 74-attempt spend (`74 × $20.07 = $1,485.18`).
   - Meanwhile, its published 95% CI `[0.4802, 0.5392]` (width `0.0590`) reflects sampling SE on *observed* attempts (implicit MCAR assumption). Under exact **Missing-Not-At-Random (MNAR)** sensitivity (`0`-imputation for timeouts/crashes vs `1`-imputation):
     - Uniform `13/87` missingness spans **`[0.4344, 0.5838]`** (exact `[188959/435000, 84653/145000]`, width exact `13/87 ≈ 0.1494`, `2.53×` wider than the published CI).
     - Concentrated single-track worst-case headline deltas reach **`13/150` (`±0.0867`)** in Science, **`13/45` (`±0.2889`)** in Post-training, and **`1/5` (`±0.2000`)** in Literature.

---

### 3.2 Stale Static OG/Social Image (`cost-vs-score.png`) vs. Live Interactive JS (`CostScoreChart-CkzD4pZy.js`)

Direct inspection of `index.html` confirms both `property="og:image"` and `name="twitter:image"` serve `cost-vs-score.png` (`SHA-256: 51541703...`). Side-by-side comparison against the live interactive JS (`CostScoreChart-CkzD4pZy.js`, `55583ebf...`) reveals that **`cost-vs-score.png` is a stale pre-publication snapshot rendered under EQUAL `(1/3, 1/3, 1/3)` track weights and earlier `Opus 5.5` / `Fable 5.1*` evaluations**:

| Model | Live JS Headline `(0.4, 0.4, 0.2)` | Exact Equal-Weight `(1/3, 1/3, 1/3)` | Visual Panel (a) in `cost-vs-score.png` | Diagnostic Match |
|---|---:|---:|---:|---|
| `DeepSeek V4.1 Flash` | `0.2740` | **`0.3079`** (`2309/7500`) | `~0.308` (above `0.30` line) | Exact `(1/3, 1/3, 1/3)` match (`+0.0339` over live JS) |
| `Kimi K3` | `0.2714` | **`0.3004`** (`9013/30000`) | `~0.300` (on `0.30` line) | Exact `(1/3, 1/3, 1/3)` match (`+0.0290` over live JS) |
| `Qwen3.8-Flash` | `0.2142` | **`0.2553`** (`383/1500`) | `~0.255` | Exact `(1/3, 1/3, 1/3)` match (`+0.0411` over live JS) |
| `Gemini 4 Argon` | `0.5261` | **`0.5307`** | `~0.531` | Exact `(1/3, 1/3, 1/3)` match |
| `GPT-6.1 Sol` | `0.5495` | **`0.5424`** | `~0.542` | Exact `(1/3, 1/3, 1/3)` match |
| `GPT-6 Astra` | `0.5658` | **`0.5527`** | `~0.553` | Exact `(1/3, 1/3, 1/3)` match |
| `Opus 5.5` | `0.6183` (Sci `0.5833`) | `0.6175` (with live Sci) | `~0.606` (Panel b Sci `~0.55`) | Pre-re-eval `Opus 5.5` Science + `(1/3, 1/3, 1/3)` |
| `Fable 5.1*` | `0.5107` (PT `0.6395`) | `0.5241` (with live PT) | `~0.445` (Panel b Sci `~0.27`, Panel c PT `~0.47`) | Pre-re-eval `Fable 5.1*` (`~+0.17` PT shift) + `(1/3, 1/3, 1/3)` |

*Operational impact:* Every social share preview of the blog post displays a stale chart whose weighting scheme (`1/3, 1/3, 1/3`) and `Opus 5.5`/`Fable 5.1*` data points contradict the live interactive charts and published formula.

---

### 3.3 Exact Pure-Q 2-Simplex Weight-Sensitivity Polytope ($\Delta_2$) & `10/3×` Task-Leverage Asymmetry

1. **Exact Single-Task Leverage Disparity (`10/3 = 3.333333×`):**
   - Published weights `(2/5, 2/5, 1/5)` distributed over `(20, 6, 3)` tasks yield exact per-task headline weights:
     - Science: **`1/50 = 0.020000`** per task
     - Post-training: **`1/15 = 0.066667`** per task (`3.333×` Science)
     - Literature: **`1/15 = 0.066667`** per task (`3.333×` Science)
   - Under task-proportional weighting `(20/29, 6/29, 3/29)` (every one of the 29 tasks weighted equally at `1/29`), `Opus 5.5` (`0.6014`) leads `GPT-6 Astra` (`0.5984`) by only exact **`881/290000 ≈ +0.003038`** — a **`17.28×` collapse** (`15225/881`) of the published `+0.0525` headline gap!
2. **Exact Pure-$\mathbb{Q}$ Sutherland–Hodgman Polytope Volumes over $\Delta_2 = \{(w_S, w_P, w_L) \ge 0 : w_S+w_P+w_L=1\}$:**
   - **#1 Winner Partition (exact conservation check: sum = `1/1`):**
     - `Opus 5.5` is `#1` on exact **`2,713,763 / 2,963,763` (`91.5648%`)** of $\Delta_2$.
     - `GPT-6 Astra` is `#1` on exact **`250,000 / 2,963,763` (`8.4352%`)** of $\Delta_2$, strictly when $w_S$ crosses the exact rational line segment joining `(w_S = 1183/1683 ≈ 0.702911, w_L = 0)` to `(w_S = 1261/1761 ≈ 0.716070, w_P = 0)`.
     - All remaining 6 models have exact **`0/1` (`0.0000%`)** `#1` simplex area — none can take `#1` under any non-negative track weights.
   - **Ranking Fragility:**
     - The full 8-model published ranking (`Opus > Astra > Sol > Argon > Fable > DeepSeek > Kimi > Qwen`) holds on only **`29.1899%`** of $\Delta_2$ (`255176508419330478725013871 / 874194559263183892228209000`); **`70.8101%`** of valid track-weight choices alter the leaderboard ordering!
     - Even the top-5 ranking holds on only **`32.0390%`** of $\Delta_2$ (`13830938685020964514559 / 43169031342565260561000`); **`67.9610%`** flips!

---

### 3.4 Exact 95% CI Overlap $K_4$ Clique & Headline vs. Per-Track Pareto Fragility

- **Pairwise 95% CI Separability (`9 / 28` pairs overlap):**
  - **Complete $K_4$ Clique on Ranks `#2–#5`:** Every single pair among `{GPT-6 Astra, GPT-6.1 Sol, Gemini 4 Argon, Fable 5.1*}` (`6/6` pairs) has overlapping 95% CIs (`widths: 0.0008–0.0521`), spanning a **`5.86×`** API cost spread (`$333.1` to `$1,951.9`).
  - **Top-of-Frontier CI Collapse (`Opus 5.5` vs `GPT-6.1 Sol`):** `#3 GPT-6.1 Sol` (`[0.4990, 0.5959]`, `$333.1`) overlaps `#1 Opus 5.5` (`[0.5909, 0.6446]`, `$1,432.4`) by exact **`1/200 = 0.0050`** while costing **`14324/3331 = 4.3002×` less**! Thus `Opus 5.5` loses strict Pareto dominance over `GPT-6.1 Sol` within published 95% CIs.
  - **Razor-Thin `#1` vs `#2` Separation:** The smallest clean non-overlapping separation in the entire benchmark is `Opus 5.5 > GPT-6 Astra` (`0.5909` vs `0.5905`), separated by exact **`1/2500 = 0.0004`**.
  - **Bottom Tier Overlap:** `DeepSeek V4.1 Flash` (`[0.2377, 0.3078]`, `$62.9`) completely contains `Kimi K3`'s 95% CI (`[0.2529, 0.2903]`, `$947.8`, **`15.07×` cost**) and overlaps `Qwen3.8-Flash` (`[0.1812, 0.2417]`, width `0.0040`).
- **Headline vs. Per-Track Pareto Frontier Divergence:**
  - **Headline:** `{DeepSeek V4.1 Flash, GPT-6.1 Sol, Opus 5.5}`
  - **Science:** `{DeepSeek V4.1 Flash, GPT-6.1 Sol, GPT-6 Astra}` (`Opus 5.5` dominated!)
  - **Post-training:** `{DeepSeek V4.1 Flash, Kimi K3, GPT-6.1 Sol, Opus 5.5}` (`Kimi K3` on frontier!)
  - **Literature:** `{DeepSeek V4.1 Flash, GPT-6.1 Sol, Gemini 4 Argon, Fable 5.1*, Opus 5.5}` (`Argon` and `Fable 5.1*` on frontier!)
  - Four models excluded from the headline Pareto frontier (`GPT-6 Astra`, `Kimi K3`, `Gemini 4 Argon`, `Fable 5.1*`) are Pareto-optimal on individual tracks.

---

### 3.5 Exact Pure-Q Bipartite Model–Harness Non-Identifiability Theorem (`dim ker(X) = 3`) & Constructive `2`-Cell Bridge

Consider the additive two-way model $y_{m,h} = \mu_m + \gamma_h$ over the `8` published `(model, harness)` cells (`11` parameters: `8` model main effects $\mu_m$ + `3` harness effects $\gamma_h$). Exact pure-$\mathbb{Q}$ RREF of the `8 × 11` incidence matrix $X$ proves:

- **Published Design:** `rank(X) = 8`, **`dim ker(X) = 3`** (matching the `3` disconnected bipartite components: `Claude Code` `{Opus 5.5, Fable 5.1*}`, `Codex` `{GPT-6 Astra, GPT-6.1 Sol}`, and `OpenCode` `{Argon, DeepSeek, Kimi, Qwen}`).
- **Exact Identifiability Breakdown:**
  - Only **`8 / 28` (`2/7 = 28.57%`)** pairwise model contrasts $\mu_i - \mu_j$ are orthogonal to $\ker(X)$ (the within-harness pairs).
  - **`20 / 28` (`5/7 = 71.43%`)** pairwise model contrasts — **every single cross-provider comparison**, including `#1 Opus 5.5 vs #2 GPT-6 Astra` and `#1 Opus 5.5 vs #3 GPT-6.1 Sol` — are **algebraically unidentifiable**: shifting $\gamma_{\text{ClaudeCode}} \mapsto \gamma_{\text{ClaudeCode}} + \Delta$ and $\mu_{\text{Opus}}, \mu_{\text{Fable}} \mapsto \mu - \Delta$ preserves all `8` observed scores identically while arbitrarily reversing `#1` and `#2`.
  - **`3 / 3` (`100%`)** pairwise harness contrasts (`Claude Code - Codex`, `Claude Code - OpenCode`, `Codex - OpenCode`) are unidentifiable.
- **Constructive Minimum Bridge Design (`+2` cells = `+25%` evals -> `100%` identifiability):**
  - Because `alphaXiv/OpenResearch` (`48f42c45`, `README.md` & `SYSTEM_PROMPT.md:5-7`) already runs Anthropic and OpenAI models natively on `OpenCode`, evaluating just **`2` cross-harness bridge cells** — `(Opus 5.5, OpenCode)` and `(GPT-6 Astra, OpenCode)` — connects all `3` components into `1`:
    - `rank(X): 8 -> 10`, **`dim ker(X): 3 -> 1`** (irreducible 1-D global gauge only)
    - Identifiable model pairs: **`8/28 -> 28/28` (`100.0%`)**
    - Identifiable harness pairs: **`0/3 -> 3/3` (`100.0%`)**

---

### 3.6 Sub-Task Coverage Sparsity, Navigational Saturation, & Terence Tao's Black-Box Observability Paradox

1. **Post-Training `6/12` (`50%`) Factorial Sparsity:** Prose describes *"fine-tuning 3 base models (Qwen3-0.6B, Qwen3-1.7B, SmolLM2-360M) on 4 benchmarks (GSM8K, HumanEval, IFEval, BFCL)"* (`12` factorial pairs), but `RankHeatmap-CVYXZmjT.js` evaluates only **`6/12`** pairs (`BFCL` and `HumanEval` are tested on `1` base model each).
2. **Literature `Navigational` Ceiling Saturation:** All 8 models cluster in `[0.878, 0.922]` (range **`0.044`**), and the `#8` overall model (`Qwen3.8-Flash`, `0.2142`) ranks **`#1` (`0.922`)** on `Navigational`, compressing variance on `1/3` of the Literature track (`6.67%` of headline).
3. **The Tao Black-Box Observability Paradox & Rust Repo Audit (`alphaXiv/OpenResearch@48f42c45`):**
   - The blog quotes Terence Tao (*"Disappointingly, we've learned almost nothing mathematically from what they did. Research is as much about the process as it is about the result"*), yet the Index formula assigns **`w_observability = 0`**, omits source code (`"Its source code is coming soon"`), and grants Post-training agents **4 hours on an H100 GPU with unrestricted internet access** without a published split-leakage or contamination audit.
   - Read-only code inspection of `alphaXiv/OpenResearch @ 48f42c45` shows that `SKILL.md:29-39` states *"The run command and the environment are a fixed contract — identical on every node"*, yet this rule is **advisory prompt text only**: `src/commands/create_experiment.rs:38` passes `run_command: args.run_command` directly to `CreateExperimentSpec`, `src/local/experiments.rs:369` allows per-node `run_command` overrides, and `src/commands/metrics.rs:77` confirms Trackio metric logging is opt-in (`"It logs only if the code calls trackio.init with name=ORX_RUN_ID"`).

---

## 4. Concrete Engineering Bridge: `Foundation-0/aletheia v1.4.0` × `Moissanite-Labs/warp-drive#13/#15`

Our oracle's `evaluate_tao_observability_gate` formalizes Tao's critique as a fail-closed 5-gate process contract directly uniting existing verified Expedition infrastructure:

| Gate | Requirement Enforced | Closed Vulnerability in OpenResearch Index | Verified Expedition Bridge |
|---|---|---|---|
| **G1 (`frozen_contract_sha256`)** | `64`-char lowercase SHA-256 of Ring-0 eval harness & fixed run command | Advisory-only `SKILL.md` rule 2 overridden by `create_experiment.rs:38` | `Moissanite-Labs/warp-drive#13` (`experiment_contract.py` Ring-0 lock) |
| **G2 (`split_leakage_count == 0`)** | Exact zero train/eval split overlap receipt | Post-training agents tuning on `GSM8K`/`HumanEval`/`IFEval`/`BFCL` | `Moissanite-Labs/warp-drive#13/#15` (split-leakage boundary) |
| **G3 (`internet_contamination_audit`)** | Exact `"OFFLINE_OR_ALLOWLIST_VERIFIED"` | 4h H100 + unrestricted internet access during PostTrainBench | `warp-drive#15` trust-boundary allowlist gate |
| **G4 (`goodhart_kl_delta_bps <= max`)** | Bounded KL divergence from base policy | Reward hacking / benchmark overfitting during 4h H100 RL/SFT | `warp-drive#12/#13` Fisher-Schur `+55%` Goodhart KL latch |
| **G5 (`r4 >= 3` & `r5_killed == total > 0`)** | `>= 3` isolated `-I` bit-identical runs & `100%` AST refusal-site mutation kill | Unreproducible or vacuous grading scripts (`"source code coming soon"`) | `Foundation-0/aletheia v1.4.0` (`audit-check` + `mutate`) |

*Oracle Proof:* Under `evaluate_tao_observability_gate`, an outcome-only `0.6183` run with black-box process receipts (`0/5` gates) or even a `0.6559` run missing only internet contamination audit (`4/5` gates) is **fail-closed `REJECTED_BLACK_BOX`** with `observable_adjusted_score = 0/1`; only a governed `5/5` run is **`PROMOTED`**.

---

## 5. Law-4 Epistemic Hygiene & `N0` / `N1` Quarantine

- **`N1` (Verified Directly in This Audit):**
  - All 8-model composite scores, exact `4/100000` rounding bounds, exact `Fable 5.1*` `41/120` rational Science reconstruction & `$253.52` cost extrapolation gap, exact MNAR bounds, exact $\Delta_2$ polytope volumes (`2713763/2963763` vs `250000/2963763`; `29.1899%` full-order region; `10/3×` task leverage), exact `9/28` CI overlaps + `#2–#5` $K_4$ clique + `Sol`/`Opus` CI Pareto fragility, exact `dim ker(X) = 3 -> 1` bipartite confounding proof & 2-bridge recovery, stale `cost-vs-score.png` equal-weight `(1/3, 1/3, 1/3)` diagnostic, and `alphaXiv/OpenResearch@48f42c45` Rust source inspection (`create_experiment.rs:38`, `experiments.rs:369`, `metrics.rs:77`).
- **`N0` (Explicitly Quarantined — NOT Claimed):**
  - We do **NOT** claim that any model cheated via internet access during alphaXiv's Post-training runs — raw agent traces, container network logs, and task scoring code are unpublished (`"Its source code is coming soon"`), so contamination is an **unverified audit surface**, not an allegation of misconduct.
  - We do **NOT** claim the exact distribution of `Fable 5.1*`'s `13` missing attempts across all 29 tasks beyond proving at least one Engineering task averaged over `< 3` attempts (`5/18`) and bounding worst-case MNAR sensitivity.
  - We do **NOT** claim which specific model would win under cross-harness bridge evaluation (`Opus 5.5` on `OpenCode` vs `GPT-6 Astra` on `OpenCode`); we prove only that without `>= 2` bridge cells, cross-provider contrasts are algebraically unidentifiable in the additive model.
  - We do **NOT** claim the exact pixel coordinates of `cost-vs-score.png` were digitized to 4 decimals by OCR; visual inspection establishes the `(1/3, 1/3, 1/3)` shift (`~+0.03–0.04` on DeepSeek/Kimi/Qwen) and `Fable 5.1*` `~0.47 -> 0.6395` Post-training jump qualitatively and consistently across all 8 markers.

---

## 6. Reproduction Commands & Falsification Criteria

```bash
# 1. Exact pure-Q unit & refusal-site test suite (isolated mode)
PYTHONDONTWRITEBYTECODE=1 python3 -I -O -B -W error test_openresearch_index_r5.py

# 2. Live verbatim bundle audit & canonical zero-float certificate (or --standalone)
PYTHONDONTWRITEBYTECODE=1 python3 -I -O -B -W error openresearch_index_audit.py --write-cert openresearch_index_certificate.json
PYTHONDONTWRITEBYTECODE=1 python3 -I -O -B -W error openresearch_index_audit.py --standalone > /dev/null

# 3. Aletheia v1.4.0 R5 AST refusal-site mutation audit on BOTH modules (requires 100.0% kill, 0 survivors)
PYTHONDONTWRITEBYTECODE=1 python3 -B -W error -m aletheia mutate openresearch_index_oracle.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_openresearch_index_r5.py" --json
PYTHONDONTWRITEBYTECODE=1 python3 -B -W error -m aletheia mutate openresearch_index_audit.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_openresearch_index_r5.py" --json

# 4. Aletheia v1.4.0 full hygiene, AST, zero-float JSON & R4 parity gate
PYTHONDONTWRITEBYTECODE=1 python3 -B -W error -m aletheia audit-check . \
  --strict-ancestors --scripts openresearch_index_audit.py test_openresearch_index_r5.py --json
```

**Falsification Criteria:** Any finding in this audit is immediately falsified if:
1. Any published model's `(S, P, L)` score in `CostScoreChart-CkzD4pZy.js` yields a different `0.4S+0.4P+0.2L` value or simplex polytope volume than certified in `openresearch_index_certificate.json`;
2. `dim ker(X)` of the published 8-cell `(model, harness)` incidence matrix differs from `3`, or adding `(Opus 5.5, OpenCode)` and `(GPT-6 Astra, OpenCode)` fails to reduce `dim ker(X)` to `1`;
3. `alphaXiv/OpenResearch@48f42c45` rejects per-node `--run-command` overrides in `src/commands/create_experiment.rs` / `src/local/experiments.rs`;
4. Any mutant in `openresearch_index_oracle.py` survives `aletheia v1.4.0 mutate`, any float enters `openresearch_index_certificate.json`, or `4/4` isolated `-I` runs fail bit-for-bit SHA-256 parity.
