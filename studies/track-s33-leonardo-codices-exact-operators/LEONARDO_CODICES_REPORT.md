# Track S33 — Portal 30: Leonardo da Vinci Live 2023–2026 Exact-Operator Quintet

- **Track ID:** `TRACK-S33-LEONARDO-CODICES-EXACT-OPERATORS`
- **Schema:** `aletheia.leonardo_codices.certificate.v1`
- **Novelty Classification:** `N1` (exact pure-$\mathbb{Z}/\mathbb{Q}$ operator synthesis and deterministic algebraic certification of five Leonardo da Vinci codex problems connected to 2023–2026 published literature; no unverified physical claims and zero floating-point arithmetic)
- **Arithmetic & Dependencies:** Pure Python 3 standard library (`int`, `fractions.Fraction`); `0` AST float literals, `0` `float()` calls, `0` bare `assert` statements, `0` `.isdigit()`/`.isnumeric()`/`.isdecimal()` calls, `0` mathematical/Monte-Carlo RNG calls (`secrets.token_hex(8)` used solely for collision-free atomic temp file naming under concurrent writers), `0` external dependencies across all three Python modules (`leonardo_codices_oracle.py`, `leonardo_codices_audit.py`, `test_leonardo_codices_r5.py`).

## Certified Digests & Artifact Manifest

| Digest | SHA-256 |
| --- | --- |
| `payload_sha256` | `a9a4cebcfd62510052e53393d4ef76254a11823ed4dec42a7660f849daac7f7b` |
| `certificate_sha256` | `b8a4047dc262fefa0b56bcbe4529218587494f893e9ad284de31bb26ceda79f5` |
| `canonical_sha256` (no trailing LF) | `bc3baee291cad981f33c1ad9099a3d693382bec4b5beac830d17ebb6f70675d0` |
| `file_sha256` (`leonardo_codices_certificate.json`) | `9eec31665b5e4b96e7b486fde40f21813f161924d64c04e7155cf459db587438` |

| Frozen Code / Certificate Artifact | Lines | Bytes | SHA-256 |
| --- | --- | --- | --- |
| `leonardo_codices_oracle.py` | `1772` | `77941` | `ba42c87a2c7a1ed59c295be9872536b0ff269e0a8962cd3714d97073ef5e7f72` |
| `leonardo_codices_audit.py` | `545` | `25668` | `f982f23801e44672f671050cc28d8b389e74979325e26d9e49d4c7188af5b9e2` |
| `test_leonardo_codices_r5.py` | `957` | `57098` | `541cdf74eb9e27b9e7be30b4925c653b3660fc60065fc3c44385633b79444097` |
| `leonardo_codices_certificate.json` | `1` | `15075` | `9eec31665b5e4b96e7b486fde40f21813f161924d64c04e7155cf459db587438` |

---

## Pillar 1 — *Codex Arundel* f. 143v: Exact Pitcher Snapshot Uniqueness & Unified Discrete Acceleration Obstruction

**Literature anchor:** Gharib, Roh & Noca, *"Leonardo da Vinci's Visualization of Gravity as a Form of Acceleration"*, *Leonardo* (MIT Press, 2023).

1. **Continuous Ballistic Bivariate $\mathbb{Q}[\tau, s]$ Snapshot Uniqueness Theorem:** For a horizontal pitcher trajectory $X_p(t) = \sum_{k=0}^{d} c_k t^k$ releasing particles at time $\tau$ that fall freely for elapsed duration $s = T - \tau > 0$ (snapshot time $T = \tau + s$), the particle's position relative to the pitcher at snapshot time $T$ is
   $$\Delta x(\tau, s) = X_p(\tau) + \dot{X}_p(\tau)\, s - X_p(\tau + s), \qquad \Delta y(s) = -\frac{1}{2} g s^2,$$
   so the instantaneous particle-stream slope relative to the pitcher satisfies
   $$\frac{\Delta y}{\Delta x} = \frac{-\frac{1}{2} g}{\Delta x(\tau, s) / s^2}.$$
   In $\mathbb{Q}[\tau, s]$, the exact quotient $\Delta x(\tau, s) / s^2$ is independent of $(\tau, s)$ **if and only if** $c_2 \neq 0$ and $c_k = 0$ for all $k \ge 3$ ($X_p''' \equiv 0$, constant horizontal acceleration $a_h = 2 c_2$), in which case $\Delta x(\tau, s) / s^2 \equiv -c_2$ and $\Delta y / \Delta x = g / (2 c_2) = g / a_h$. The hypotenuse forms a $45^\circ$ isosceles right triangle (*Equatione di Moti*) **if and only if** $a_h = g$.
   - **45-degree witness:** $c = (3, 7, 5)$, $g = 10 \implies a_h = 10$, $\Delta x(\tau, s) / s^2 \equiv -5$ (zero non-constant terms), exact slope $\Delta y / \Delta x = (-5)/(-5) = \mathbf{1}$.
   - **General straight-slope witness:** $c = (0, 2, 2)$, $g = 10 \implies a_h = 4$, $\Delta x(\tau, s) / s^2 \equiv -2$, exact slope $\mathbf{5/2}$ (`is_45_degree_equatione_di_moti = false`).
   - **Must-fail negative controls:**
     - Cubic jerk $c = (0, 0, 5, 1)$ gives $\Delta x(\tau, s) / s^2 = -5 - 3\tau - s$ (nonzero bivariate residual terms `tau^1*s^0: -3`, `tau^0*s^1: -1`, breaking straightness).
     - Quartic $c = (1, 0, 5, 0, 1/2)$ gives $\Delta x(\tau, s) / s^2 = -5 - 3\tau^2 - 2\tau s - \frac{1}{2} s^2$ (nonzero terms `tau^2*s^0: -3`, `tau^1*s^1: -2`, `tau^0*s^2: -1/2`).
2. **Continuous vs Apples-to-Apples Uniform Discrete Velocity Comparison ($N \in \{3, 4, 5, 6\}$):** All snapshot points $\Delta x(k, N) = X(k) + v(k)(N - k) - X(N)$, $\Delta y(k, N) = -(N - k)^2$ are computed directly from exact $(X, v)$ formulas:
   - **Continuous ballistic velocity ($v(k) = \dot{X}(k) = 2k$):** Galileo $X(k) = k^2$ gives exact collinearity determinants **`[0, 0, 0, 0]`** across $N = 3, 4, 5, 6$.
   - **Uniform backward difference ($v_{\text{bwd}}(k) = X(k) - X(k-1)$):** Galileo $X(k) = k^2$ ($v_{\text{bwd}} = 2k - 1$) yields constant $O(1)$ discretization determinants **`[2, 2, 2, 2]`** (consecutive ratios **`[1, 1, 1]`**), whereas Leonardo $X(k) = 2^k - 1$ ($v_{\text{bwd}} = 2^{k-1}$) breaks collinearity strictly at $N = 3$ with exponentially diverging determinants **`[4, 8, 16, 32]`** ($2^{N-1}$, consecutive ratios **`[2, 2, 2]`**).
   - **Uniform forward difference ($v_{\text{fwd}}(k) = X(k+1) - X(k)$):** Galileo $X(k) = k^2$ ($v_{\text{fwd}} = 2k + 1$) yields constant **`[-2, -2, -2, -2]`** (ratios **`[1, 1, 1]`**), whereas Leonardo $X(k) = 2^k - 1$ ($v_{\text{fwd}} = 2^k$) yields exponentially diverging **`[-2, -4, -8, -16]`** ($-2^{N-2}$, ratios **`[2, 2, 2]`**).
3. **Exact 4-Interval Rational Diagnostics** ($[0, 1, 4, 9, 16]$ vs $[0, 1, 3, 7, 15]$):
   - Centered $R^2 = \mathbf{8000/8091}$ ($\approx 0.988753$).
   - Origin-anchored $R^2 = \mathbf{12482/12567}$ ($\approx 0.993236$).
   - Endpoint-normalized RMS$^2 = \mathbf{337/115200}$ ($\approx 0.002925$, RMS $\approx 5.41\%$).

---

## Pillar 2 — *Codex Leicester* Rising Bubble Paradox: Exact Rayleigh–Lamb Resonances & 4D Hurwitz–Hermite Hopf Bifurcation

**Literature anchors:** `arXiv:2609.26283` (Aug 2026, exact rational capillary–bubble Rayleigh–Lamb resonances) and Herrada & Eggers, *"Leonardo's paradox resolved: Path instability of an air bubble rising in water"*, *PNAS* (2023).

1. **Exact Pure-$\mathbb{Q}$ Rayleigh–Lamb Spectrum:**
   $$\omega_l^2(\tau) = \frac{\sigma\, l(l-1)(l+1)(l+2)}{(l+1)\tau + l}, \qquad l \in \{2, \dots, 12\}.$$
   - **Vacuum limit ($\tau = 0, \sigma = 1$):** $\omega_2^2 = 12, \omega_3^2 = 40, \omega_4^2 = 90, \omega_5^2 = 168, \omega_6^2 = 280, \mathbf{\omega_7^2 = 432}, \dots, \omega_{12}^2 = 2002$. The **unique** integer harmonic resonance $\omega_l / \omega_2 = k \in \mathbb{Z}_{>0}$ in $l \in [3, 12]$ occurs at **$l = 7, k = 6$** ($\omega_7^2 / \omega_2^2 = 432/12 = 36 = 6^2$); modes $l \in \{3, 4, 5, 6\}$ are non-resonant in vacuum.
   - **Zero-surface-tension control ($\sigma = 0$):** All squared frequencies across $l = 2 \dots 12$ vanish identically.
2. **All 6 Exact Positive Rational Resonances $\tau_{l,k} > 0$ ($3 \le l \le 10$):** Solved directly and back-substituted identically in $\mathbb{Q}$:

| Mode $l$ | Harmonic $k$ | Exact Density Ratio $\tau_{l,k}$ | Exact $\omega_l^2(\tau_{l,k}) = k^2 \omega_2^2(\tau_{l,k})$ |
| --- | --- | --- | --- |
| `5` | `4` | `10/9` | `72` |
| `6` | `5` | `2/7` | `210` |
| `8` | `8` | `46/27` | `216` |
| `9` | `9` | `23/60` | `4320/7` |
| `10` | `10` | `2/77` | `1155` |
| `10` | `11` | `10/7` | `462` |

3. **Exact 4D Coupled Sway–Tilt–Wake Hopf Operator:** For the reduced-order 4D coupled sway–tilt–wake linearization $A(\mu)$ (an exact pure-$\mathbb{Q}$ algebraic Hopf model of path instability, not a 3D Navier–Stokes DNS), $\det(\lambda I - A(\mu)) = \lambda^4 + 4\lambda^3 + 9\lambda^2 + 10\lambda + (6 + \mu)$ is recovered directly via exact Bareiss determinants at $z \in \{0, \pm 1, \pm 2\}$ and certified by both Bareiss Hurwitz minors $(\Delta_1, \Delta_2, \Delta_3)$ and exact $4 \times 4$ symmetric Hermite–Sylvester congruence inertia:

| Regime | $\mu$ | Characteristic Polynomial | $(\Delta_1, \Delta_2, \Delta_3)$ | Hermite Diagonal | Inertia $(n_+, n_-, n_0)$ |
| --- | --- | --- | --- | --- | --- |
| Subcritical straight rise | `10` | `[1, 4, 9, 10, 16]` | `(4, 26, 4)` | `[4, 26, 1, 32/13]` | `(4, 0, 0)` |
| Critical Hopf threshold | `41/4` | `[1, 4, 9, 10, 65/4]` | `(4, 26, 0)` | `[4, 26, 0, 0]` | `(2, 0, 2)` ($\omega_H^2 = 5/2$) |
| Supercritical oscillatory | `11` | `[1, 4, 9, 10, 17]` | `(4, 26, -12)` | `[4, 26, -3, -102/13]` | `(2, 2, 0)` |

---

## Pillar 3 — *Codex Atlanticus* f. 69r & f. 899v: Reciprocal Arch Bridge Farkas Duality & Da Vinci Dome Obstructions

**Literature anchor:** `arXiv:2401.00881` (Jan 2024, Da Vinci domes / collinear reciprocal grids) and *Codex Atlanticus* f. 69r / f. 899v.

1. **Collinear-Rod Descartes Angular-Defect Obstruction:** Across vertex degrees $2 \dots 6$, any flat or saddle crossing of straight continuous rods yields angular defect $\delta_v \le 0$ (`0` half-turns for degrees `2, 3, 4, 6`; `-1/3` half-turns for degree-5 saddle), proving positive Gaussian curvature cannot arise from purely collinear flat-rod joints without out-of-plane eccentricity, curvature, or topological disclinations.
2. **Euler Torus vs Sphere Obstruction:**
   - All **11/11** periodic uniform planar tilings satisfy $\chi = V - E + F = 0$.
   - All **6** spherical polyhedral cages (tetrahedron, octahedron, cube, icosahedron, dodecahedron, truncated-icosahedron dome) satisfy $\chi = 2$ (total Descartes defect $720^\circ$). Specifically, for fullerene-type trivalent spherical domes tiled exclusively by pentagons and hexagons (dodecahedron and truncated-icosahedron dome), Euler's formula forces **exactly `12` pentagonal faces** (whereas the tetrahedron is trivalent with `4` triangles and `0` pentagons, the cube has `6` squares and `0` pentagons, and the octahedron/icosahedron have vertices of degrees `4` and `5`).
3. **Exact 3-Beam / 4-Contact Unilateral-Compression Reciprocal Arch Bridge:** With `(3, 4, 5)` Pythagorean crown notches, solving the exact 8-equation equilibrium system yields unique strictly positive normal forces $f_n = [3, 3, 7/5, 7/5]$ and tangential forces $f_t = [1, 1, -1/5, -1/5]$, giving contact ratios $|f_t|/f_n = [1/3, 1/3, 1/7, 1/7]$ and sharp Coulomb stability threshold **$\mu_{\min} = \mathbf{1/3}$**:
   - **Primal equilibrium certified:** $\mu = 1/3$ (threshold) and $\mu = 1/2$ (safe interior) with zero 9-DOF residual and non-negative cone weights.
   - **Exact Farkas dual virtual-velocity collapse ($\mu < 1/3$):**
     - $\mu = 1/4$: $v = [-2, 0, -2, 0, -1, 0, 2, 0, 2]$ gives $A^T v = [0, 2, 0, 2, 0, 0, 0, 0] \ge 0$ and $v^T g = -2 < 0$.
     - $\mu = 0$: $v = [-2, -1, -2, 0, -2, 0, 2, -1, 2]$ gives $A^T v = \mathbf{0}$ and $v^T g = -8 < 0$.
   - **Catastrophic central-beam removal negative control:** Deleting the interlocking crown beam yields exact 6-DOF virtual collapse velocity $v = [1, -1/2, -1, -1, -1/2, 1]$ with $A^T v = [0, 0, 0, 0]$ and $v^T g = -2 < 0$ even at $\mu = 100$.

---

## Pillar 4 — *MS M / Trattato* Branching Law vs Sopp–Valbuena *PNAS* 2023 vs Murray vs Pythagorean Trees

**Literature anchors:** Sopp & Valbuena, *"Vascular optimality explains tree branching beyond Leonardo's rule"*, *PNAS* (2023); `arXiv:2411.08024` (Nov 2024, Pythagorean trees).

1. **Generalized Variational Branching Exponent** $\alpha^*(p, q, m) = (p + q)/m$:
   - Leonardo cross-sectional area conservation $(2, 2, 2) \mapsto \mathbf{2}$.
   - Laminar Poiseuille Murray's law $(4, 2, 2) \mapsto \mathbf{3}$.
   - Turbulent branching $(5, 2, 3) \mapsto \mathbf{7/3}$.
2. **Exact Pure-$\mathbb{Z}$ Symmetric-Split Poiseuille Dominance:** Computed directly from $J(r, Q) = Q^2 r^{-4} + 2 r^2$ at symmetric split $n = 2, Q_c = 1/2$: $C_{\text{Murray}}^3 = \mathbf{54} < \mathbf{64} = C_{\text{Leonardo}}^3$ (exact cubic gap **`10`**).
3. **Exact Pythagorean Trees (`arXiv:2411.08024`):** Primitives `(3, 4, 5)`, `(5, 12, 13)`, and `(8, 15, 17)` conserve both cross-sectional area (`25, 169, 289`) and constant-aspect-ratio $\kappa = 5/2$ lateral surface area (`125/2, 845/2, 1445/2`); 3-level recursive splitting preserves area `[1, 1, 1, 1]` across all four depths.
4. **Exact 4-Level / 15-Edge / 7-Internal-Node Kirchhoff–Schur Complement Laplacian Pushforward:** Eliminating all 7 internal nodes via exact Gaussian elimination over $\mathbb{Q}$ (`L_II u_I = -L_IB u_B`):
   - Naive $\alpha = 2$ uniform-pipe scaling (`G = [1, 1/4, 1/16, 1/64]`): $R_{\text{eff}} = \mathbf{15}$, $G_{\text{eff}} = 1/15$.
   - Sopp–Valbuena conduit widening (`G = [1, 1/2, 1/4, 1/8]`): $R_{\text{eff}} = \mathbf{4}$, $G_{\text{eff}} = 1/4$.
   - Exact vascular conductance gain ratio: **`15/4 = 3.75×`**, matching independent series–parallel reduction identically.

---

## Pillar 5 — *De Ludo Geometrico* Squarable Lunes, *MS B* Aerial Screw (`arXiv:2506.10223`), & `CS-13` Myth Audit (`arXiv:1311.0816`)

**Literature anchors:** *De Ludo Geometrico* / *Codex Atlanticus* lune quadratures; `arXiv:2506.10223` (Aug 2025, Johns Hopkins aerial screw aeroacoustics); `arXiv:1311.0816` (historical attribution audit).

1. **All 5 Classical Squarable Lunes from First-Principles Chebyshev $U_k(\cos\theta)$:**

| Ratio $m:n$ | Reduced Polynomial in $y = \cos^2\theta$ (ascending) | Degree in $y$ | Exact Ferrari Cubic Resolvent Root | Constructible |
| --- | --- | --- | --- | --- |
| `2:1` | `[-1, 2]` | `1` | `n/a_deg_le_2` | `true` |
| `3:1` | `[-1, -4, 8]` | `2` | `n/a_deg_le_2` | `true` |
| `3:2` | `[1, -14, 16]` | `2` | `n/a_deg_le_2` | `true` |
| `5:1` | `[-1, -6, 44, -96, 64]` | `4` | `1/8` | `true` |
| `5:3` | `[-1, -16, 224, -576, 384]` | `4` | `1/8` | `true` |

2. **Exact Zero-$\pi$ Area Dissections (Derived Directly from Side Lengths & Radii in $\mathbb{Q} \oplus \mathbb{Q}\pi$):**
   - Hippocrates `2:1` lune (right isosceles triangle legs `L = 2`): `(algebraic_area = 1, pi_coeff = 0)`.
   - Leonardo *Codex Atlanticus* 4-lune rosette (inscribed square side `s = 2`): `(algebraic_area = 4, pi_coeff = 0)`.
3. **Exact Galois Ruler-and-Compass Obstructions:**
   - **`4:1` lune:** $4x^3 - 2x - 1$ has degree $3 \neq 2^k$, zero rational roots across all 6 Rational Root Theorem candidates (`±1, ±1/2, ±1/4`), and is irreducible mod $5$ via exact Rabin irreducibility test.
   - **`7:1` lune:** $y^6 - 10y^5 + 37y^4 - 62y^3 + 46y^2 - 12y - 6$ (in $y = 4\cos^2\theta$) has degree $6 \neq 2^k$ and is irreducible mod $17$ via exact Rabin irreducibility test.
4. ***MS B* Aerial Screw Iso-Lift Dimensional Scaling (`arXiv:2506.10223`):** Distinguishing **power-squared reduction** ($1 - P^2/P_0^2$) cleanly from **mechanical power reduction** ($1 - P/P_0 = 1 - \sqrt{P^2/P_0^2}$):
   - **Pure $3\times$ blade-area scaling ($\lambda = 3, c_L = c_D = 1$):** $\omega^2/\omega_0^2 = 1/3$ (simplified tonal acoustic proxy drop $2/3 \approx 66.67\%$), exact **power-squared ratio** $P^2/P_0^2 = 1/3$ (power-squared reduction $2/3 \approx 66.67\%$), and exact rational bracket $(57/100)^2 < 1/3 < (58/100)^2$ certifying **mechanical power reduction** $1 - 1/\sqrt{3} \approx \mathbf{42.265\%}$ (in the $42\%$–$43\%$ band).
   - **Johns Hopkins 2025 mechanism witness ($\lambda = 7/2, c_L = 1, c_D = 27/25$):** exact **power-squared ratio** $P^2/P_0^2 = \mathbf{1458/4375}$ (power-squared reduction $2917/4375 \approx 66.674\%$), strictly bracketed in $((57/100)^2, (58/100)^2)$ so **mechanical power reduction** is $1 - \sqrt{1458/4375} \approx \mathbf{42.272\%}$ (matching the JHU `arXiv:2506.10223` reported $\approx 42.2\%$ mechanical power reduction). The simplified tonal acoustic proxy yields $\omega^2/\omega_0^2 = 2/7$ (drop $5/7 \approx 71.43\%$), contrasted honestly with JHU's full aeroacoustic simulation figure of $\approx 72.3\%$.
5. **Honest `CS-13` Myth Audit (`arXiv:1311.0816`):**
   - The widely misattributed "Leonardo da Vinci proof of the Pythagorean theorem" is explicitly **not** attributed to Leonardo's authentic codices (`attributed_to_leonardo_in_authentic_codices = false`); its documented origin is **Johann Tobias Mayer (1772)**.
   - Golden-ratio numerology is explicitly excluded (`golden_ratio_numerology_excluded = true`).

---

## Zone-B Architecture & Verification Summary

- **Auditor Architecture & Honest Scope (`leonardo_codices_audit.py`):** `leonardo_codices_audit.py` shares exact parsers and deterministic certificate replay (`build_standalone_certificate`, `validate_certificate_payload`) with `leonardo_codices_oracle.py`; therefore `--check` performs **full pure-$\mathbb{Q}$ deterministic replay and secondary algebraic cross-checking** (not zero-shared-code verification). Under both `full_replay=True` and `full_replay=False`, `validate_certificate_payload` enforces `_validate_payload_structure` (exact top-level keys, metadata, pillar dicts, and iterative bool-vs-int schema separation). `secondary_algebraic_audit` enforces `require_int` (rejecting `bool`) on all audited integer fields across all 5 pillars plus strict distinctness of all 6 `(l, k)` positive resonance pairs.
- **Thread-Safe & TOCTOU-Hardened File I/O:** Per-component `dir_fd` (`openat` with `O_RDONLY | O_DIRECTORY | O_NOFOLLOW` plus `lstat` symlink classification on `ELOOP`/`ENOTDIR`), bounded `max_bytes <= 64 MiB` chunked regular-file reads, `type(payload) is bytes` pre-check before directory traversal, locked monotonic counter + `secrets.token_hex(8)` + bounded 32-attempt `EEXIST` retry loop (`TEMP_RETRY_EXHAUSTED`), `O_CREAT | O_EXCL | O_NOFOLLOW | O_NONBLOCK` temp writes, real `os.fsync(tmp_fd)`, pre-replace `os.fstat(tmp_fd).st_nlink == 1` guard, atomic `os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd)`, directory `os.fsync(dfd)`, target hardlink (`st_nlink > 1`) protection, deleted-CWD `CWD_UNAVAILABLE` handling, lone UTF-16 surrogate rejection, and strict zero-abbreviation CLI parsing.
- **Verification Gates Passed (Post-Final-Edit, Strictly Sequential):**
  - **3-Mode Isolated Parity (`-I -B`, `-I -O -B`, `-I -B -W error`) + `-I -O -B -W error` & `PYTHONHASHSEED=42 -B`:** Bit-identical `9eec31665b5e4b96e7b486fde40f21813f161924d64c04e7155cf459db587438` ×5, `--check` `valid=true` & `secondary_audit_passed=true` ×5, `test_leonardo_codices_r5.py` `OK` ×5.
  - **Live `aletheia v2.0.0 mutate --max-mutants 0`:** `85/85` (`100.0%`, `survived=0`) on `leonardo_codices_audit.py` + `93/93` (`100.0%`, `survived=0`) on `leonardo_codices_oracle.py` = **`178/178` (`100.0%`)**.
  - **Exhaustive `SWAP + SUBCOND_DEL` AST `BoolOp` Sweep (`timeout=30`):** `55/55` (`100.0%`) on `leonardo_codices_audit.py` + `58/58` (`100.0%`) on `leonardo_codices_oracle.py` = **`113/113` (`100.0%`)**.
  - **Live Zone-B Adversarial Fuzzer:** `23/23` CLI + `18/18` in-memory (`full_replay=True`) = **`41/41` (`100.0%`)**, PLUS **`18/18` (`100.0%`)** in-memory under `full_replay=False` (`0` bypasses, `0` crashes).
  - **Live Concurrency & Kernel Race Stress:** `>= 500` live concurrent `renameat2(RENAME_EXCHANGE)` swaps asserted across `550` read+write iterations, `>= 420` concurrent `os.link`/`os.unlink` hardlink race iterations, plus `16`-thread distinct-target (`640` writes) + `16`-thread same-target (`640` writes) = `1,280` multi-threaded concurrent atomic writes (`0` errors, `0` clobbers, `0` leftover temp files).
  - **Aletheia Static & Safety Gate:** `aletheia v2.0.0 audit-check . --strict-ancestors --safety-scan --scripts leonardo_codices_audit.py test_leonardo_codices_r5.py` -> `PASS` (`5` files, `2/2` isolated-parity scripts, `0` findings, `0` `__pycache__`).
