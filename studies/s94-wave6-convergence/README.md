# Wave-6 Fourth-Order Cross-Cluster Convergence (`Portals 98–100` $\times$ `S31–S86`)

- **Track ID:** `TRACK-S94-NEURON-BASIS-BONSAI-SLEEP-CONVERGENCE` (`aletheia.track_s94.wave6_neuron_bonsai_sleep.certificate.v1`)
- **Arithmetic & Proof Discipline:** Pure-$\mathbb{Z}/\mathbb{Q}$ Python 3 standard library only (`int`, `fractions.Fraction`; zero production floats, zero bare `assert`s, zero RNG, zero external dependencies, zero Wave-6 snapshot copies or model weights shipped) paired with **`18/18` universally quantified (`∀`) pure-`Init` `Lean 4.36.0` theorems** (`0` external imports, `0` warnings, `4` `[]` zero-axiom + `14` `[propext]` only, `0` `Quot.sound`, `0` `Classical.choice`, `0` `sorryAx`).
- **Canonical Certificate:** [`s94_wave6_convergence_certificate.json`](s94_wave6_convergence_certificate.json) (`15,197` bytes; file SHA-256 `1ad705c23646b65df0dc9ac928d3a4070deef61f5d17f8e8f249b4f75f51335b`; `payload_sha256 = ac7ef28717eb2d7940f908013416faf6495ada82a4c115a67b8ca710640edfab`, `certificate_sha256 = b21f0fba7aef4739cd1a246644bc32a997352d43685246e148c357e1e2055f60`).
- **Cryptographic Provenance Pins (`12/12` Wave-6 Snapshots + `10/10` Upstream Certs):** Cryptographically anchors `12` read-only primary Wave-6 snapshots (`Portals 98–100`, stored strictly outside the repository) and `10` frozen upstream expedition certificates (`S31`, `S50`, `S59`, `S70`, `S73`, `S76`, `S78`, `S79`, `S80`, `S86`) by exact byte length and SHA-256 (enumerated in [`REPORT.md`](REPORT.md) §5). Optional `--verify-pins --expedition-root <dir> --wave6-root <dir>` re-hashes all `22/22` pinned files on disk when available; `--check`, `--standalone`, `--verify-lean`, and `test_s94_wave6_convergence_r5.py` execute 100% self-contained with zero external files.

---

## Prior Art & Honest Novelty Separation (`N0` vs. `N1`, Zero `N2` Claims)

- **`N0` Established Prior Art:** Classical mathematical foundations—Sylvester–Hadamard matrices (1867), Householder reflections (1958), Brier proper scoring rule (1950), Williams–Waterman–Patterson Roofline model (2009), and the Banach Contraction Principle (1922)—together with all primary Wave-6 works (Anthropic 2026, `stdlogits`, PrismML `Bonsai 2.5`, `Magnitude`, Lin et al. 2025, Lee et al. 2026, Thinking Machines / Mantic, Harvey Research) and all `10` upstream expedition certificates (`S31–S86`) are explicitly credited as `N0` foundations.
- **`N1` Contributions of This Study (Max Novelty Tier = `N1`, `0` `N2` Claims):**
  1. **Pillar 1 — Privileged Neuron Basis $\times$ `[H_k, D] != 0` Smearing & Householder `DPI` (`Thms 1–6`):** Exact Sylvester–Hadamard importance-smearing law (`5/2`, `19/4`, `71/8 = 8.8750×`, `271/16`) paired with its Law-5 isotropic converse (`[H_k, c I_k] = 0`, explaining why blockwise Hadamard `Bonsai 2.5` succeeds while importance-weighted `hHBG128` blows up KL); exact Householder mirror isometry/involution ($H(2)^\top H(2) = I, H(2)^2 = I \implies \Delta \|W\|_F^2 = 0$) vs. rank-1 `S31` `DPI` concentration (`4,423.68×` on `100 / 442,368` neurons) and RelP `R`/`S`-lens adjoint identity (`41/4`).
  2. **Pillar 2 — `8 GiB` Consumer-Silicon 3-Tier Roofline & Sparse-MoE Boundary (`Thms 7–12`):** Exact dense-27B residency cliff $b_{\text{crit}} = 325/171 = 1.9006\text{ bpw}$ (`Bonsai 2.5` `1.76 bpw`, `5.93 GB`, `9.0725×` compression, `60.1349 tok/s`, `1.0000×` slowdown vs. `3.0 bpw` `10.7035`, `4.5 bpw` `5.1013`, `FP16` `0.2981 tok/s`) contrasted with `Magnitude`'s `5%`-active sparse-MoE regime (`2.69 GB` active/token: `132.5651 tok/s` at 100% GPU hit, `59.5423 tok/s` / `2.2264×` at 80% hit).
  3. **Pillar 3 — 2-Axis Consolidation Phase Diagram & Borromean 5-Gate Fixed Point (`Thms 13–18`):** Separates Axis 1 (**Zero-$\Delta W$ KV-Refinement Sleep**: `2.10×`/`2.39×` token efficiency, `0` wake latency, `0` weight forgetting, `0` cross-session persistence, coupled to `S76` $\rho = 1/4$ contraction & `S79` last-loop KV sharing) from Axis 2 (**Weight-Modifying Consolidation**: cross-session persistence governed by `S78` unit forgetting conservation, `S80` 20-night FWER `0.8715` vs. `0` Goodhart accepts, exact Brier strict proper-scoring, single-draw overconfidence paradox, and $\lambda$-reference mixture calibration bias), certifying all `5/5` single-gate ablations strictly fail.

---

## Live `Lean 4.36.0` Formalization (`18/18` Universal `∀` Pure-`Init` Theorems)

All `18/18` theorems in [`Wave6ConvergenceOperators.lean`](Wave6ConvergenceOperators.lean) are universally quantified (`∀`) under namespace `S94Wave6Convergence` and compile directly under `Lean 4.36.0` (`Init` only, zero external imports, zero warnings, `4` literal `[]` zero-axiom + `14` `[propext]` only, `0` `Quot.sound`, `0` `Classical.choice`, `0` `sorryAx`):

| # | Theorem (`S94Wave6Convergence.*`) | Pillar | Scope (`∀`) | Kernel Axioms |
| :-: | :--- | :-: | :--- | :--- |
| 1 | `hadamard_smearing_diagonal_flat_universal` | 1 | Hadamard diagonal spike flattening ($\alpha > 1, k \ge 2$) | `[propext]` |
| 2 | `hadamard_importance_blowup_linear_in_k_universal` | 1 | Exact $O(k)$ importance-weighted MSE blowup under `[H_k, D] != 0` | `[propext]` |
| 3 | `hadamard_uniform_isotropic_commutes_universal` | 1 | Law-5 isotropic converse (`[H_2, c I_2] = 0`, zero off-diagonal leak) | `[propext]` |
| 4 | `householder_reflection_isometry_universal` | 1 | Exact Householder $k=2$ reflection isometry ($\Delta \|W\|_F^2 = 0$) | `[propext]` |
| 5 | `householder_reflection_involution_universal` | 1 | Exact Householder $k=2$ involution ($H(2)^2 = I$) | `[propext]` |
| 6 | `householder_projection_idempotent_and_dpi_universal` | 1 | Householder $k=1$ projection orthogonality & `S31` `DPI` spike | `[propext]` |
| 7 | `residency_phase_cliff_universal` | 2 | Exact dense GPU residency phase cliff separation | `[propext]` |
| 8 | `tier_spill_strict_slowdown_universal` | 2 | Any positive system-RAM spill strictly slows decode | `[propext]` |
| 9 | `nvme_spill_dominates_ram_spill_universal` | 2 | NVMe SSD spill strictly dominates RAM spill penalty | `[]` |
| 10 | `three_tier_monotonic_time_universal` | 2 | Universal 3-tier GPU+RAM+SSD harmonic roofline bound | `[propext]` |
| 11 | `sparse_moe_active_bandwidth_gain_universal` | 2 | Sparse-MoE active fraction strictly reduces memory traffic | `[]` |
| 12 | `joint_bpw_compression_headroom_universal` | 2 | Joint bit-width compression strictly frees bit budget | `[propext]` |
| 13 | `brier_strict_proper_scoring_universal` | 3 | Exact integer Brier strict proper-scoring decomposition | `[propext]` |
| 14 | `reference_mixture_bias_variance_universal` | 3 | Reference-mixture calibration bias ($\lambda < D, q \ne r$) | `[propext]` |
| 15 | `single_draw_overconfidence_paradox_universal` | 3 | Single-draw overconfidence wins on $Y=1$ yet loses in expectation | `[propext]` |
| 16 | `sleep_loop_contraction_vs_divergence_universal` | 3 | Offline sleep loop contraction ($\rho < 1$) vs. divergence ($\rho > 1$) | `[]` |
| 17 | `last_loop_kv_sharing_strict_gain_universal` | 3 | Last-loop KV sharing strictly compresses KV cache ($R \ge 2, W < L$) | `[propext]` |
| 18 | `five_gate_consolidation_borromean_universal` | 3 | Borromean 5-gate joint consolidation necessity (`g1..g5`) | `[]` |

---

## Files in This Study (`9` Files, Zero External Weights or Snapshot Copies)

| File | SHA-256 | Role |
| :--- | :--- | :--- |
| [`README.md`](README.md) | *(this file)* | Public overview, `N0`/`N1` boundary, `18`-theorem index, pin notes, and quickstart commands |
| [`REPORT.md`](REPORT.md) | `1d9475826c568eab3f1c0700e36175b1b1b6c15fab8ad75c9b2e46dcc327f533` | Full Wave-6 convergence tables across Pillars 1–3, `22`-file cryptographic provenance manifest, and `N0`/`N1` attribution |
| [`Wave6ConvergenceOperators.lean`](Wave6ConvergenceOperators.lean) | `ac3c812972562a68a5d14b635e265d7d79d66ceac14bd3a0d0ef1898b648a940` | `18/18` universally quantified (`∀`) pure-`Init` `Lean 4.36.0` theorems (`0` imports, `0` warnings) |
| [`lakefile.toml`](lakefile.toml) | `be46ec128b84e7ec1f9cf646c3e1bd988d64a7dfa2db81efe4a3f26829c33169` | Lean 4 `lake` package configuration |
| [`lean-toolchain`](lean-toolchain) | `582a63f8f9c5128067b688778c1051cf1464c3ca9d57b9325025c051c29b774a` | Pinned `leanprover/lean4:v4.36.0` toolchain |
| [`s94_wave6_convergence_oracle.py`](s94_wave6_convergence_oracle.py) | `a6d9640d5c84cafa1f50eb78c77a8dd9a431c123a19401986f5348c6788aed0f` | Pure-$\mathbb{Z}/\mathbb{Q}$ reference oracle and canonical certificate builder (`0` floats, `0` bare asserts) |
| [`verify_s94_wave6_convergence.py`](verify_s94_wave6_convergence.py) | `20c60fb784e6aa4b2d4aeb06957e6ed4e668219cdf609446997ab4db5d79ae95` | Zone-B hardened standalone verifier, independent secondary auditor (`SEC`/`FR0`/`FR1`), static + live `Lean 4` checker, and optional `--verify-pins` auditor |
| [`s94_wave6_convergence_certificate.json`](s94_wave6_convergence_certificate.json) | `1ad705c23646b65df0dc9ac928d3a4070deef61f5d17f8e8f249b4f75f51335b` | Committed canonical zero-float JSON certificate (`15,197` bytes) |
| [`test_s94_wave6_convergence_r5.py`](test_s94_wave6_convergence_r5.py) | `1e296bfc604def91029c956db1ac49c70cba7e8d0fc87dc8680d3254a0662cb5` | Assertion-free verification, re-signed semantic tamper, filesystem, R10+ Lean gate, and live/Lean-less test suite (`7/7 OK`, `0` skips) |

---

## Quickstart & Exact Reproduction

From `studies/s94-wave6-convergence/`:

```bash
# 1. Verify the committed zero-float canonical JSON certificate (full pure-Z/Q replay; works without lean)
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 -I -B verify_s94_wave6_convergence.py \
    --check s94_wave6_convergence_certificate.json --json

# 2. Verify canonical standalone regeneration bit-for-bit
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 -I -B verify_s94_wave6_convergence.py --standalone --json \
  | cmp - s94_wave6_convergence_certificate.json

# 3. Verify all 18 pure-Init Lean 4.36.0 theorems via static anti-bypass + live kernel check
#    (requires lean 4.36.0 on PATH)
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  python3 -I -B verify_s94_wave6_convergence.py \
    --verify-lean Wave6ConvergenceOperators.lean --json

# 4. Run full test suite across all three isolated Python modes (7/7 OK, 0 skips even without lean)
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -I -B test_s94_wave6_convergence_r5.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -I -O -B test_s94_wave6_convergence_r5.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -I -B -W error test_s94_wave6_convergence_r5.py
```
