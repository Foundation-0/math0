# Track S94: Wave-6 Fourth-Order Cross-Cluster Convergence (`Portals 98–100` $\times$ Expedition `S31`–`S86`)

- **Track ID:** `TRACK-S94-NEURON-BASIS-BONSAI-SLEEP-CONVERGENCE`
- **Schema Version:** `aletheia.track_s94.wave6_neuron_bonsai_sleep.certificate.v1`
- **Oracle Class / Novelty Tier (Law 4 Honesty):** `exact` / **`N1`** — Pure-$\mathbb{Z}/\mathbb{Q}$ exact algebraic synthesis (`0` floats, `0` bare `assert`s, `0` RNG, `0` dataset copies into `expedition/`) + **`18/18` universally quantified (`∀`) pure-`Init` Lean `4.36.0` theorems**, unifying `12` read-only Wave-6 primary snapshots (`Portals 98–100`) with `10` frozen upstream expedition certificates (`S31`, `S50`, `S59`, `S70`, `S73`, `S76`, `S78`, `S79`, `S80`, `S86`). All classical results (`N0`) are explicitly attributed; **`0` `N2` claims**.
- **Canonical Certificate (`s94_wave6_convergence_certificate.json`, `0o600`):**
  - `payload_sha256`: `ac7ef28717eb2d7940f908013416faf6495ada82a4c115a67b8ca710640edfab`
  - `certificate_sha256`: `b21f0fba7aef4739cd1a246644bc32a997352d43685246e148c357e1e2055f60`
  - File SHA-256 (`15,197` B, LF-terminated canonical JSON): `1ad705c23646b65df0dc9ac928d3a4070deef61f5d17f8e8f249b4f75f51335b`
- **Lean `4.36.0` Companion (`Wave6ConvergenceOperators.lean`):**
  - SHA-256: `ac3c812972562a68a5d14b635e265d7d79d66ceac14bd3a0d0ef1898b648a940`
  - **`18/18` universally quantified (`∀`) pure-`Init` theorems** (`4` with `[]` zero axioms, `14` with `[propext]` only; `0` `Quot.sound`, `0` `Classical.choice`, `0` `sorryAx`, `0` warnings; `lake build` clean `RC=0`).

---

## 0. `OWN_TERMS_FIRST` & Law-2 Transformational Steelman

Before uniting Wave-6's three flagship frontiers — **Privileged Neuron Interpretability & Weight Mirroring (`Portal 98`)**, **Ternary `Bonsai 2.5 27B` & `Magnitude` 3-Tier Streaming (`Portal 99`)**, and **The Sleep Trilogy + Forecasting RL + `Harvey Tenet` (`Portal 100`)** — with our ten frozen expedition certificates, **Law 2b** states the strongest skeptical critique first:

> **Steelman Skeptical Critique:** *These three clusters operate in distinct regimes with sharp incompatibilities: (i) `Bonsai 2.5 27B` explicitly uses blockwise Hadamard rotations (`g128`, `1.76 bpw`) to achieve `99.4%` of FP16 tool-calling accuracy, so claiming Hadamard rotations always destroy privileged neurons is false; (ii) `Magnitude` runs `50+ GB` models smoothly on consumer machines by exploiting `~5%` ultra-sparse MoE activation, so a dense-model NVMe streaming wall does not invalidate sparse MoE engines; and (iii) Zero-$\Delta W$ KV-Refinement Sleep (`2611`) has zero weight forgetting ONLY because it forgets everything across sessions once the KV cache resets, whereas real long-term skill acquisition (e.g., `Thinking Machines` Forecasting RL and `Harvey Tenet`) requires weight updates.*

**Response in Exact Operators & Explicit Law-5 Domain Boundaries:**
- **Pillar 1** proves the exact `[H_k, D] != 0` importance-smearing law **paired with its isotropic converse (`Thm 3`)**: smearing triggers *precisely* when diagonal neuron importance $D$ is skewed AND scaling is placed *inside* rather than *outside* the orthogonal transform (`siliquant#97` `71/8 = 8.875×`), whereas uniform/isotropic weights ($D = c I_k$) commute identically (`[H_k, c I_k] = 0`, `1×`), explaining why `Bonsai 2.5` succeeds with blockwise Hadamard ternary weights while importance-weighted `hHBG128` blows up KL by `2.89–4.81×`.
- **Pillar 2** proves the exact `8 GiB` dense-27B residency cliff (`b_crit = 325/171 = 1.9006 bpw`, `Thm 7`) **paired with the sparse-MoE active-fraction law (`Thm 11`)**: `Bonsai 2.5` (`1.76 bpw`, `5.93 GB`) sits strictly below the dense residency cliff (`60.13 tok/s`, `1.00×` slowdown), while `Magnitude` succeeds on `53.8 GB` models precisely when ultra-sparse MoE activation (`1/20 = 5%`, `2.69 GB` active/token) keeps the hot working set inside the `6.5 GB` GPU cache (`132.57 tok/s` at 100% hit, `59.54 tok/s` at 80% hit vs. `0.30 tok/s` dense FP16).
- **Pillar 3** proves an exact **2-axis consolidation phase diagram**: Axis 1 (**Zero-$\Delta W$ KV-Refinement Sleep**, `2.10×`/`2.39×` token efficiency, `0` wake latency, `0` weight forgetting, `0` cross-session persistence, bounded by `S76` $\rho < 1$ & `S79` last-loop KV sharing) vs. Axis 2 (**Weight-Modifying Consolidation**, cross-session persistence bounded by `S78` `Forgetting/Learning = 1`, `Thinking Machines` Brier/reference-bias theorem `Thms 13–15`, and `S80` / `Harvey Tenet` anti-Goodhart hold-out ratchet), unified under a 5-gate Borromean fixed point (`Thm 18`).

---

## 1. Pillar 1 — Privileged Neuron Basis (`Portal 98`) $\times$ `siliquant` `A_16` / `[H_8, D] != 0` / `S31` `DPI`

Anchored verbatim to `anthropic_neuron_basis_theory.txt`, `anthropic_neuron_basis_apps.txt`, `stdlogits_neuron_lens_README.md`, `stdlogits_neuron_reflection_README.md`, `S31`, `S59`, `S70`, and `siliquant#97`:

### 1.1 Exact $O(k)$ Importance Smearing Under `[H_k, D] != 0` (`Thms 1–3`)
For a $k$-coordinate privileged-basis diagonal importance matrix $D_k(\alpha) = \operatorname{diag}(\alpha, 1, \dots, 1)$ (modeling sparse concept-bearing MLP neurons: Anthropic Part 1 finds `< 1%` Type-3 polysemantic neurons; `neuron-reflection` finds `100 / 442,368` = `0.0226%` greedy neurons match `88–123%` of top-1% loading), conjugating by symmetric orthogonal Sylvester Hadamard $H_k = \frac{1}{\sqrt{k}} H_k^{\text{int}}$ flattens every diagonal entry of $M = H_k D_k(\alpha) H_k$ to $\bar{d} = (\alpha + k - 1)/k$ (`Thm 1`), injects $\pm (\alpha - 1)/k$ off-diagonal cross-talk across all $k(k-1)$ pairs, and produces `2(k - 1)` nonzero commutator entries in $[H_k^{\text{int}}, D_k]$. For unit lattice error $E = e_1^T$, the mis-ordered weight error $\Delta W = E D^{-1} H_k$ has unweighted MSE `1` yet true privileged-basis importance error $(\alpha^2 + k - 1)/k$ (`Thm 2`):

| Order $k$ ($\alpha = k$) | Nonzero $[H_k^{\text{int}}, D]$ | Smeared Diagonal $\bar{d}$ | Off-Diag $|\cdot|$ | Unweighted MSE | True Importance MSE $\|\Delta W D\|_F^2$ |
| :---: | :---: | :---: | :---: | :---: | :---: |
| `2` | `2 / 4` | `3/2` | `1/2` | `1` | **`5/2` (`2.5000×`)** |
| `4` | `6 / 16` | `7/4` | `3/4` | `1` | **`19/4` (`4.7500×`)** |
| **`8` (`siliquant#97`)** | **`14 / 64`** | **`15/8`** | **`7/8`** | **`1`** | **`71/8` (`8.8750×`)** |
| `16` | `30 / 256` | `31/16` | `15/16` | `1` | **`271/16` (`16.9375×`)** |
| `8` (Isotropic $\alpha = 1$, Law-5) | **`0 / 64`** | `1` | `0` | `1` | **`1` (`1.0000×`)** |
| Axis-Aligned / Permuted (`S59`/`S70`) | **`0 / 64`** | `max = 8` preserved | `0` | `1` | **`1` (`1.0000×`)** |

### 1.2 Exact `neuron-reflection` Householder Dial $H(k) = I - k d d^T$ & `S31` `DPI` Detection (`Thms 4–6`)
For exact unit contrast axis $d = (3/5, 4/5, 0, 0) \in \mathbb{Q}^4$ ($\|d\|_2^2 = 1$):
- **`k = 2` Mirror:** Exact involution $H(2)^2 = I_4$ (`Thm 5`, guaranteeing exact `Editor.restore`) and exact orthogonal isometry $H(2)^\top H(2) = I_4$ (`Thm 4`).
- **`k = 1` Directional Fusion:** Exact idempotent projection $H(1)^2 = H(1)$ with $H(1) d = 0$ (`Thm 6`).
- **Zero-Frobenius Blindness vs. Rank-1 `S31` `DPI` Spike:** Mirroring row 0 of our exact $4 \times 4$ witness $W_0$ (`||W_0||_F^2 = 100`) yields **`||W'||_F^2 = 100` (`Delta ||W||_F^2 = 0` exact!)** — rendering aggregate Frobenius norms 100% blind to zero-training refusal collapses (`5/6 -> 1/12` writes mirrored, `5/6 -> 1/24` both sides on `Qwen3-8B`!). Yet the differential matrix $\Delta W = W' - W_0$ has **`||Delta W||_F^2 = 100`**, exact **`rank = 1`**, `100%` spectral concentration (`sigma_1^2 / ||Delta W||_F^2 = 1`), and peak-to-mean row concentration `N/m` = **`442368 / 100 = 110592/25 = 4,423.68×`** on `Qwen3-8B`'s `100`-neuron sparse edit (cf. `S31` `75,968×` two-row concentration)!
- **Exact RelP `R`/`S`-Lens Adjoint Identity:** On exact $4 \times 4$ rational Jacobian $J_L$, $(J_L^\top u) \cdot v = u \cdot (J_L v) = 41/4$ exact (`stdlogits_neuron_lens_README.md:74`).

---

## 2. Pillar 2 — Ternary `Bonsai 2.5 27B` $\times$ `Magnitude` 3-Tier Streaming $\times$ `8 GiB` Consumer-Silicon Roofline (`Portal 99`)

Anchored verbatim to `bonsai25_gguf_README.md`, `prismml_bonsai25_27b.txt`, `magnitude_README.md`, `S73`, `S78`, and `S86`:
- **`Bonsai 2.5 27B` Exact Primary Anchors (`Qwen3.8-27B`, `27.36B = 684/25 B` total):** FP16 `53.8 GB` (`269/5 GB`) $\to$ `PTQ1_0` **`5.93 GB` (`593/100 GB`, `1.76 bpw = 44/25 bpw`)**, exact compression **`5380/593 = 9.0725×`**, retaining **`772/777 = 99.36%`** of FP16 agentic tool calling (`77.2` vs `77.7`), **`542/605 = 89.59%`** of FP16 agentic coding (`54.2` vs `60.5`), and **`2053/2108 = 97.39%`** of FP16 general capability (`82.12` vs `84.32`).
- **Exact `8 GiB` 3-Tier Hardware Model (`S86` `8,192 MiB` budget):** Usable GPU weight budget $C_{\text{gpu}} = 13/2 = 6.5\text{ GB}$ (reserving `1.5 GB` for KV/desktop, matching `bonsai25_gguf_README.md:196-197`), RAM $C_{\text{ram}} = 31\text{ GB}$, NVMe $954\text{ GB}$; bandwidths $B_{\text{gpu}} = 1783/5 = 356.6\text{ GB/s}$ (GDDR6), $B_{\text{ram}} = 50\text{ GB/s}$ (`7.1320×` penalty), $B_{\text{ssd}} = 6\text{ GB/s}$ (`59.4333×` penalty).
- **Exact Dense-27B Residency Phase Cliff (`Thm 7`):**
  $$b_{\text{crit}}(N = 27.36\text{B},\, C_{\text{gpu}} = 6.5\text{ GB}) = \frac{8 \cdot C_{\text{gpu}}}{N} = \frac{325}{171} = \mathbf{1.9006\text{ bpw}}$$
  `Bonsai 2.5`'s `1.76 bpw < 1.9006 bpw` sits strictly below the cliff, while every $\ge 2.0\text{ bpw}$ dense 27B quant spills (`Thms 8–10`):

| Model / Regime (`27.36B` Base) | Weight Size | $(f_{\text{gpu}}, f_{\text{ram}}, f_{\text{ssd}})$ | Spill Slowdown | Exact Roofline Decode |
|---|---:|:---:|---:|---:|
| **`Bonsai 2.5 PTQ1_0` (`1.76 bpw`, Dense)** | `5.93 GB` | **`(1, 0, 0)`** | **`1.0000×`** | **`35660/593 = 60.1349 tok/s`** |
| `A_16 QuadSnake` (`3.0 bpw`, Dense) | `10.26 GB` | `(325/513, 188/513, 0)` | `69409/21375 = 3.2472×` | `2228750/208227 = 10.7035 tok/s` |
| `4.5 bpw` (Dense) | `15.39 GB` | `(650/1539, 889/1539, 0)` | `582529/128250 = 4.5421×` | `8915000/1747587 = 5.1013 tok/s` |
| `FP16` (`16.0 bpw`, Dense) | `53.80 GB` | `(65/538, 155/269, 163/538)` | `1794533/80700 = 22.2371×` | `534900/1794533 = 0.2981 tok/s` |
| **`Magnitude` Sparse MoE (`5%` Active, `h=1.0`)** | `2.69 GB` active | `100%` hot GPU cache | **`1.0000×`** | **`35660/269 = 132.5651 tok/s`** |
| **`Magnitude` Sparse MoE (`5%` Active, `h=0.8`)** | `2.69 GB` active | `80%` GPU / `20%` RAM | **`2783/1250 = 2.2264×`** | **`44575000/748627 = 59.5423 tok/s`** |

---

## 3. Pillar 3 — The Sleep Trilogy $\times$ Forecasting RL & `Harvey Tenet` $\times$ `S50`/`S76`/`S78`/`S79`/`S80` (`Portal 100`)

### 3.1 Exact 2-Axis Consolidation Phase Diagram (`Thms 13–18`)
- **Axis 1 — Zero-$\Delta W$ KV-Refinement Sleep (`2504.13171` + `2605.26099` + `2611` KV-Refinement):**
  - `2611` achieves **`21/10 = 2.10×`** (`N=2`) and **`239/100 = 2.39×`** (`N=4`) prefix-token efficiency at **`0`** wake-latency overhead, **`0`** KV-cache growth, and **`0`** permanent weight forgetting (`cross_session_persistence: false`).
  - `2504.13171` achieves `5×` test-time compute reduction and `5/2 = 2.5×` multi-query cost amortization.
  - Coupled to `S76` loop contraction ($\rho = 1/4 \implies e_2 = 1/16, e_4 = 1/256$ vs. divergence $5/4 \implies 625/256$, `Thm 16`), `S79` last-loop KV sharing (`128/35`, `512/131`, `2048/515` for $L \in \{2048, 8192, 32768\}$, `Thm 17`), and `S50` within-session rank-1 state transport ($\|\Delta S\|_F^2 = 212/5$, margin flip `-133/25`).
- **Axis 2 — Weight-Modifying Consolidation (`Thinking Machines` RL + `Harvey Tenet` + `S78`/`S80`):**
  - Persistent across sessions (`cross_session_persistence: true`), governed by `S78` unit forgetting conservation (`Forgetting/Learning = 1`, `229/5` kB) and `S80` unguarded `songe` FWER (`39/400` per night $\implies$ `0.8715` over 20 nights vs. `aletheia` ratchet `5` clean / `0` Goodhart accepts).
  - **Exact Brier Strict Proper-Scoring & Single-Draw Overconfidence Paradox (`Thms 13, 15`):** For $q = 3/5$, calibrated $p_1 = 3/5$ vs. overconfident $p_2 = 4/5$: on $Y=1$ (occurring `60%` of the time!), $p_2$ wins single-draw error (`1/25 < 4/25`), yet in expectation $p_1$ strictly dominates (`6/25 < 7/25`, excess penalty `(p_2 - q)^2 = 1/25`).
  - **Exact Reference-Mixture Calibration Bias (`Thm 14`, `Thinking Machines` $\lambda$-mixture):** For $q = 3/5, r = 4/5$: $\lambda = 1/2 \implies p^* = 7/10$ (`bias = 1/10`, excess error `1/100`); pure reference $\lambda = 0 \implies p^* = 4/5$ (`bias = 1/5`, excess error `1/25`, `4×` worse); pure outcome $\lambda = 1 \implies p^* = 3/5$ (`bias = 0`).
- **Borromean 5-Gate Consolidation Fixed Point (`Thm 18`):** All `5/5` single-gate ablations (`rho = 5/4`, `forgetting_budgeted = False`, `lambda = 0`, `goodhart_drift = 0.8715`, `residency_ok = False`) are strictly rejected (`all_five_ablations_rejected: true`).

---

## 4. Lean `4.36.0` Formalization (`18/18` Universal `∀` Theorems)

All `18/18` theorems in `Wave6ConvergenceOperators.lean` are universally quantified (`∀`), pure-`Init` (`0` external imports, `0` warnings, `0` `Quot.sound`, `0` `Classical.choice`, `0` `sorryAx`):

| # | Theorem (`S94Wave6Convergence.*`) | Pillar | Kernel Axioms |
| :---: | :--- | :---: | :--- |
| 1 | `hadamard_smearing_diagonal_flat_universal` | 1 | `[propext]` |
| 2 | `hadamard_importance_blowup_linear_in_k_universal` | 1 | `[propext]` |
| 3 | `hadamard_uniform_isotropic_commutes_universal` | 1 | `[propext]` |
| 4 | `householder_reflection_isometry_universal` | 1 | `[propext]` |
| 5 | `householder_reflection_involution_universal` | 1 | `[propext]` |
| 6 | `householder_projection_idempotent_and_dpi_universal` | 1 | `[propext]` |
| 7 | `residency_phase_cliff_universal` | 2 | `[propext]` |
| 8 | `tier_spill_strict_slowdown_universal` | 2 | `[propext]` |
| 9 | `nvme_spill_dominates_ram_spill_universal` | 2 | **`[]` (zero axioms)** |
| 10 | `three_tier_monotonic_time_universal` | 2 | `[propext]` |
| 11 | `sparse_moe_active_bandwidth_gain_universal` | 2 | **`[]` (zero axioms)** |
| 12 | `joint_bpw_compression_headroom_universal` | 2 | `[propext]` |
| 13 | `brier_strict_proper_scoring_universal` | 3 | `[propext]` |
| 14 | `reference_mixture_bias_variance_universal` | 3 | `[propext]` |
| 15 | `single_draw_overconfidence_paradox_universal` | 3 | `[propext]` |
| 16 | `sleep_loop_contraction_vs_divergence_universal` | 3 | **`[]` (zero axioms)** |
| 17 | `last_loop_kv_sharing_strict_gain_universal` | 3 | `[propext]` |
| 18 | `five_gate_consolidation_borromean_universal` | 3 | **`[]` (zero axioms)** |

---

## 5. Cryptographic Provenance Manifest (`12` Wave-6 Snapshots + `10` Upstream Certs)

All `12` read-only Wave-6 primary snapshots (`Portals 98–100`, stored outside `expedition/`) and all `10` frozen upstream expedition certificates (`S31`–`S86`) are pinned by exact byte length and SHA-256 in `s94_wave6_convergence_certificate.json` and verified live via `--verify-pins --expedition-root .. --wave6-root <wave6-dir>`:

- **12 Wave-6 Snapshots (`P98–P100`):** `anthropic_neuron_basis_theory.txt` (`ae5697d3...`), `anthropic_neuron_basis_apps.txt` (`405f3622...`), `stdlogits_neuron_lens_README.md` (`4027688a...`), `stdlogits_neuron_reflection_README.md` (`c88103c6...`), `prismml_bonsai25_27b.txt` (`edf79d57...`), `bonsai25_gguf_README.md` (`85d142d0...`), `magnitude_README.md` (`c3357b7d...`), `arxiv_2504_13171.txt` (`d1ca566b...`), `arxiv_2605_26099.txt` (`12608e2b...`), `alphaxiv_2611_sleep_report.txt` (`905caa37...`), `thinkingmachines_forecasting.txt` (`82346e5b...`), `harvey_tenet.txt` (`97871ce2...`).
- **10 Frozen Upstream Certificates:** `S31` (`f4f7f8ab...`), `S50` (`1316eede...`), `S59` (`914a8451...`), `S70` (`5cdce98d...`), `S73` (`33dfb415...`), `S76` (`d30805fc...`), `S78` (`3b8341ef...`), `S79` (`9c30539e...`), `S80` (`95681a29...`), `S86` (`675bf68c...`).

---

## 6. Prior-Art Attribution (`N0`) & Reproducibility Commands

- **`N0` Classical Foundations:** Sylvester–Hadamard matrices (1867), Householder reflections (1958), Brier proper scoring rule (1950), Williams–Waterman–Patterson Roofline model (2009), Banach Contraction Principle (1922), and primary Wave-6 sources (Anthropic 2026, `stdlogits`, PrismML, Magnitude, Lin et al. 2025, Lee et al. 2026, Thinking Machines / Mantic, Harvey Research).
- **`N1` Verified Contribution:** Pure-$\mathbb{Z}/\mathbb{Q}$ cross-cluster synthesis and `18`-theorem pure-`Init` Lean `4.36.0` formalization unifying `Portals 98–100` with `10` frozen expedition tracks under explicit Law-5 boundaries (`n2_claims = 0`).

```bash
python3 -I -B verify_s94_wave6_convergence.py --standalone --json | cmp - s94_wave6_convergence_certificate.json
python3 -I -B verify_s94_wave6_convergence.py --check s94_wave6_convergence_certificate.json --json
python3 -I -B verify_s94_wave6_convergence.py --verify-lean Wave6ConvergenceOperators.lean --json
python3 -I -B verify_s94_wave6_convergence.py --verify-pins --expedition-root .. --json
python3 -I -B test_s94_wave6_convergence_r5.py -v
```
