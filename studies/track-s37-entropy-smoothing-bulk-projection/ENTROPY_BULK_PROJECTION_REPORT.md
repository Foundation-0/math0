# Exact-$\mathbb{Z}/\mathbb{Q}$ Entropy as Dual-Scale Smoothing, Worthington/Unruh/Gravity Bifurcation & Off-Brane Continuum Projection

- **Study ID:** `track-s37-entropy-smoothing-bulk-projection`
- **Schema:** `aletheia.entropy_bulk_projection.certificate.v1`
- **Scope:** Unifies discrete dual-scale smoothing (discrete `JKO` Rényi-2/Dirichlet flow, Arnold Cat Map filament complexity peak, Jaynes MaxEnt missing-vector balancing, incompressible Worthington axial focusing, Unruh analogue sonic horizon, and gravitational negative-heat-capacity/Jeans bifurcation) with off-brane continuum projection (exact off-brane Plummer core identity, Schur pushforward `⧄` / dark-mode shadow `⧅`, Shtanov–Sahni timelike bounce, DMPR Pell-rational negative tidal charge shadows, and GW170817/CMB observational phase gates).
- **Arithmetic & Dependencies:** Pure Python 3 standard library over exact $\mathbb{Z}/\mathbb{Q}$ (`int` and `fractions.Fraction`); `0` third-party libraries, `0` AST float literals, `0` `float()` calls, `0` JSON floats, `0` bare `assert` statements, `0` `.isdigit()`, `0` mathematical RNG (`secrets.token_hex(8)` is used strictly for atomic temp-file collision avoidance in `entropy_bulk_projection_audit.py`; `test_entropy_bulk_projection_r5.py` exercises deliberate runtime float rejection via `int(3) / int(2)` and JSON token `"1.5"`).
- **Certificate Digests:**
  - `entropy_bulk_projection_certificate.json` file SHA-256 (`0o600`): `5207acf2f586d4d964336d540fda7f76384c2472840dee2150d7d5ac20ce4b35`
  - `payload_sha256`: `0a42243b26da3e6a20f1f0319f8f25061179af376aae047b9e1334534563e25f`
  - `certificate_sha256`: `1ec65107773e70b820d4c7258b6090a1b8a7b92ade016d79f44d793a6cc20f65`

---

## 1. Epistemic Scope (`N0` Literature Context vs. `N1` Certified Operators)

- **Overall Certificate Novelty Tier:** **`N1`** (exact-$\mathbb{Z}/\mathbb{Q}$ computer-certified cross-domain synthesis combining discrete `JKO` / Arnold Cat Map / MaxEnt operators, incompressible Worthington-to-Unruh-to-Jeans bifurcation separation, off-brane Plummer core & Schur `⧄`/`⧅` dark-gravity projection certificates, and Pell-parametrized DMPR negative tidal-charge shadow bounds with observational falsification gates).
- **Explicit Unmeasured-Scope Flags (Certified `false` in Payload):**
  - `measured_live_cosmological_nbody_fits = false` (Plummer core & Schur `⧄` dark-gravity identities are exact mathematical operators, NOT empirical galaxy-rotation-curve or cosmological $N$-body fits).
  - `measured_eht_shadow_tidal_charge_detection = false` (DMPR Pell-rational shadow monotonicity certifies exact general-relativistic metric predictions, NOT an EHT observational detection of $q < 0$).
  - `measured_laboratory_worthington_piv_velocimetry = false` (Worthington axial focusing and Unruh surface gravity are exact analytical continuum identities, NOT experimental fluid PIV measurements).
- **`N0` (Classical Results & Literature Context — Explicitly Quarantined):**
  - Jordan–Kinderlehrer–Otto (`JKO`, 1998) Wasserstein gradient flow; Arnold's Cat Map on $\mathbb{T}^2$; Aaronson–Carroll–Ouellette (`arXiv:1405.6903`) coffee-and-cream complexity arc; Jaynes MaxEnt; Rayleigh–Plesset & Worthington jet mechanics; Unruh (1981) analogue acoustic metric; Jeans instability & virial theorem; classical Plummer (1911) sphere; Shiromizu–Maeda–Sasaki (SMS) Gauss–Codazzi brane projection; Shtanov–Sahni timelike-bulk bounce (`arXiv:2602.06691`); Dadhich–Maartens–Papadopoulos–Rezania (DMPR) tidal-charge metric (`arXiv:2607.13992` *DARK-HIDE*); Pardo et al. (2018) GW170817 spacetime dimension bound $D = 4.02^{+0.07}_{-0.10}$ and Planck 2018 CMB $\Omega_{\mathrm{DM}} h^2 \approx 0.1200, \Omega_b h^2 \approx 0.02237$ at $z = 1100$.
- **`N1` (Exact-$\mathbb{Z}/\mathbb{Q}$ Certified Contributions in This Study):**
  1. Simultaneous exact certification of discrete `JKO` Rényi-2 / Dirichlet monotonicity on $Q_3$ (with exact $(2/3)^2 = 4/9$ spectral-gap contraction) and $C_8$ (with explicit non-vacuous $\le 3/4$ spectral-gap contraction across all `8/8` steps, since $\lambda_2(C_8)^2 = \frac{3 + 2\sqrt{2}}{8} < \frac{3}{4} \iff 8 < 9$), an exact $\mathbb{Z}_{16}^2$ Arnold Cat Map witness where coarse variance & Dirichlet energy collapse to **exact `0`** while microscopic perimeter hits its **theoretical maximum `256`** and macro-complexity follows a strict non-monotonic peak (`2 -> 6 -> 7 -> 1` levels; `8 -> 28 -> 32 -> 0` active edges) before returning via exact $\det M = 1$ Poincaré recurrence at $t = 12$, plus exact Shannon/Rényi-2 Jaynes MaxEnt coincidence setting all `6/6` missing orthogonal modes in $\ker(A)$ to exact zero bias.
  2. Exact pure-$\mathbb{Q}$ certification of the Worthington axisymmetric stagnation field $(u_r, u_z) = (-\alpha r, 2\alpha z)$ ($\nabla\cdot\mathbf{u} \equiv 0$, $k^4$ axial kinetic-energy amplification along streamlines $\psi = \alpha r^2 z$, Euler–Bernoulli stagnation pressure peak, Rayleigh–Plesset `1/8` scaling coefficient), exact Unruh sonic horizon surface gravity $\kappa = \frac{1}{2}\partial_r(c_w^2 - v_r^2)|_{r_H} = c_w^2 / r_H = 9/2$ matching Killing $\tilde{\kappa} = 1/r_H = 1/2$, and exact gravitational negative heat capacity ($C_V^{\mathrm{grav}} = -C_V^{\mathrm{gas}} = -15$) + Jeans sign-flip bifurcation ($\omega^2 \in \{-32, -20, 0, 28, 64\}$).
  3. Exact pure-$\mathbb{Q}$ Off-Brane Plummer Core proof (zero NFW $1/r$ cusp, finite central core $\rho_{\mathrm{eff}}(0) = \frac{3M}{4\pi y_0^3}$, exact Pythagorean triplets `(3,4,5), (5,12,13), (8,15,17)` giving $M_{\mathrm{enc}}/M \in \{27/125, 125/2197, 512/4913\}$, exact circular-velocity peak $r_{\max}^2 = 2y_0^2$ with $v_{c,\max}^4/(GM)^2 = 4/(27 y_0^2)$, evaluating to `4/27` at $y_0 = 1$), unified with exact Bareiss-certified Schur pushforward `⧄` & dark-mode shadow `⧅` across `2×2`, `4×4`, and `6×6` coupled $(O, H)$ M-matrix Laplacians (`0` visible source $m_O = 0$ inducing strictly positive $J_{\mathrm{dark}} > 0$, exact $\det M = \det M_{HH}\det S_O$, exact full-system match, and exact energy decomposition $E_{\mathrm{full}} = E_O + m_H^\top M_{HH}^{-1} m_H$).
  4. Exact pure-$\mathbb{Q}$ Shtanov–Sahni regular bounce certification ($H^2(\rho_c) = 0$, $\dot{H}(\rho_c) = +\frac{3}{2}(1+w) > 0$) vs singular RS-II ($\dot{H} < 0$), exact DMPR Pell-equation parametrization $b^2 - 8 a^2 = 1$ with envelope-theorem monotonicity $\frac{d(b_{\mathrm{crit}}^2)}{d\hat{q}} = -\frac{1}{f(r_{\mathrm{ph}})^2} < 0$, exact `5`-point shadow chain $16 < 27 < \frac{574992}{14161} < \frac{128}{3} < \frac{2000}{9}$, exact algebraic bracket for $\hat{q} = -1$ ($b_{\mathrm{crit}}^2(-1) = \frac{71 + \sqrt{4913}}{4} \in (\frac{141}{4}, \frac{71}{2}) = (35.25, 35.50)$, refining earlier rough approximations), and exact $\mathbb{Z}/\mathbb{Q}$ arithmetic inequality checks over published GW170817/CMB $z=1100$ literature benchmarks (explicitly separated below from heuristic cosmological model inference).

---

## 2. Four Certified Pure-$\mathbb{Z}/\mathbb{Q}$ Pillars

### Pillar 1 — Entropy as Dual-Scale Smoothing (`JKO`, Arnold Cat Map & Jaynes MaxEnt)
1. **Discrete `JKO` / Doubly-Stochastic Diffusion ($Q_3$ & $C_8$, `8` steps from Dirac spike $e_0$):**
   - **$Q_3$ ($d=3$, $P = I - \frac{1}{6}L$, $\lambda_2 = 2/3$):** Collision energy $\|p_t\|_2^2$ decreases strictly from `1` $\to$ `1/3` $\to$ `3603611/28697814` (`> 1/8` uniform floor; exact Rényi-2 entropy increases strictly); Dirichlet roughness $p_t^\top L p_t$ decreases strictly from `3` $\to$ `3641/3188646` with exact contraction factor $\le (2/3)^2 = 4/9$ at every step.
   - **$C_8$ ($d=2$, $P = I - \frac{1}{4}L$, $\lambda_2^2 = \frac{3 + 2\sqrt{2}}{8} < \frac{3}{4}$):** Collision energy decreases strictly from `1` $\to$ `3/8` $\to$ `4860289/33554432` (`> 1/8`); Dirichlet roughness decreases strictly from `2` $\to$ `195153/16777216`, with explicit non-vacuous contraction bound $\le 3/4$ verified at all `8/8` steps.
2. **Exact Integer Arnold Cat Map $M = \begin{pmatrix}2 & 1 \\ 1 & 1\end{pmatrix}$ ($\det M = 1$, $\operatorname{tr} M = 3$, $\Delta = 5$) on $\mathbb{Z}_{16}^2$ (`8×8` initial block, `64` pixels, `4×4` coarse macro-grid):**

| Step `t` | Micro Perimeter $\Pi(S_t)$ | Coarse Collision Energy | Coarse Block Variance | Coarse Dirichlet Energy | Active Macro Edges | Distinct Macro Levels |
|---:|---:|---:|---:|---:|---:|---:|
| `0` | `32` | `1/4` | `48` | `2048` | `8` | `2` |
| `1` | `74` | `33/256` | `17` | `1088` | `28` | `6` |
| `2` | `166` | `19/256` | `3` | `288` | **`32`** (peak) | **`7`** (peak) |
| `3` | **`256`** (`4 × 64` max) | **`1/16`** (exact uniform) | **`0`** | **`0`** | **`0`** | **`1`** |

   - At every step $t = 1..12$, $M^{-1} = \begin{pmatrix}1 & -1 \\ -1 & 2\end{pmatrix}$ recovers $S_{t-1}$ with zero information loss, and $S_{12} = S_0$ identically (exact finite-torus Poincaré recurrence).
3. **Jaynes MaxEnt Orthogonal-Complement Balancing ($\mathbb{R}^8$, `2` linear constraints $\mathbf{1}^\top p = 1$ and $c^\top p = 1/4$ for $c = (+1^4, -1^4)$):**
   - Unique optimal distribution $p^* = (\tfrac{5}{32}, \tfrac{5}{32}, \tfrac{5}{32}, \tfrac{5}{32}, \tfrac{3}{32}, \tfrac{3}{32}, \tfrac{3}{32}, \tfrac{3}{32})$ (`||p*||_2^2 = 17/128`, Gibbs stratum ratio $p_+/p_- = 5/3$), coinciding identically between Shannon exponential-family MaxEnt and Rényi-2 orthogonal projection.
   - Explicit `6`-vector basis of $\ker(A)$ certified full rank `6` via Bareiss Gram determinant $\det(V^\top V) = 16 > 0$; **`6/6` missing orthogonal vectors satisfy $v_j^\top p^* = 0$ identically**.
   - Valid feasible perturbation $\delta \in \ker(A)$ (`||\delta||_2^2 = 1/1024`) obeys exact Pythagorean optimality $\|p^* + \delta\|_2^2 = 137/1024 = 17/128 + 1/1024 > 17/128$.

### Pillar 2 — Incompressible Worthington Axial Focusing, Unruh Sonic Horizon & Gravity Bifurcation
- **Incompressible Axisymmetric Worthington Flow $(u_r, u_z) = (-\alpha r, 2\alpha z)$ ($\alpha = 3/2, \beta = 2\alpha = 3$):**
  - Exact divergence identity $\frac{1}{r}\partial_r(r u_r) + \partial_z u_z = -2\alpha + \beta = 0$; exact stagnation point $\mathbf{u}(0, 0) = (0, 0)$; exact control-cylinder volume flux conservation ($\Phi_{\mathrm{in}}/(2\pi) = \Phi_{\mathrm{out}}/(2\pi) = 72$ at $R = 4, H = 3$); exact Euler–Bernoulli stagnation pressure peak $p(r,z) = p_0 - \frac{1}{2}\rho\alpha^2(r^2 + 4z^2)$; exact streamline $\psi = \alpha r^2 z$ focusing where radial compression $r \to r/k$ amplifies axial kinetic energy by exact **$k^4$** (`16×` at $k=2$, `81×` at $k=3$); exact Rayleigh–Plesset self-similar cavity collapse coefficient `1/8`.
- **Unruh (1981) Analogue Sonic Horizon ($v_r(r) = -c_w r_H / r$, $c_w = 3, r_H = 2$):**
  - $f_{\mathrm{ac}}(r) = c_w^2 - v_r(r)^2$ flips strictly from `-27 < 0` (supersonic interior $r=1$) through `0` at $r_H = 2$ to `+27/4 > 0` (subsonic exterior $r=4$).
  - Exact Unruh surface gravity $\kappa = \frac{1}{2}f_{\mathrm{ac}}'(r_H) = c_w |v_r'(r_H)| = c_w^2 / r_H = \mathbf{9/2}$, normalizing to $\tilde{\kappa} = \kappa / c_w^2 = \mathbf{1/2} = 1/r_H$ (matching the dimensionless Killing horizon operator).
- **Gravitational Negative Heat Capacity & Jeans Bifurcation:**
  - Virial equilibrium ($2K + U = 0$ with $K = 15, U = -30, E = -15$) gives $C_V^{\mathrm{grav}} = -15 < 0$ vs ideal gas $C_V^{\mathrm{gas}} = +15 > 0$ (exact sign inversion).
  - Jeans dispersion $\omega^2(k) = k^2 c_s^2 - \Omega_J^2$ ($c_s = 2, \Omega_J^2 = 36 \implies k_J = 3$) flips across $k \in \{1, 2, 3, 4, 5\}$ as **`-32, -20, 0, +28, +64`** (long-wavelength gravitational clumping vs short-wavelength acoustic smoothing).

### Pillar 3 — Off-Brane Plummer Core Theorem & Schur `⧄` / `⧅` Dark-Gravity Source
- **Exact Off-Brane Plummer Core Theorem ($\Phi(r) = -GM / \sqrt{r^2 + y_0^2}$, $R = \sqrt{r^2 + y_0^2}$):**
  - Enclosed 3D mass $M_{\mathrm{enc}}(r) = M r^3 / R^3$ has exact derivative $\frac{d M_{\mathrm{enc}}}{dr} = \frac{3 M r^2 y_0^2}{R^5}$, yielding exact Plummer cored halo density $4\pi\rho_{\mathrm{eff}}(r) = \frac{3 M y_0^2}{R^5}$ with finite central density $4\pi\rho_{\mathrm{eff}}(0) = \frac{3 M}{y_0^3}$ (zero NFW $1/r$ cusp, zero central slope), conserved total mass $\lim_{r\to\infty} M_{\mathrm{enc}}(r) = M$ (`1 - (M_enc/M)^2 < 3e-6` at $r = 1000 y_0$), and exact circular-velocity peak $r_{\max}^2 = 2 y_0^2$ ($v_{c,\max}^4 / (GM)^2 = 4 / (27 y_0^2)$).
  - Exact Pythagorean rational witnesses: `(3,4,5)` $\to M_{\mathrm{enc}}/M = \mathbf{27/125}$, `4πρ_eff/M = 48/3125`; `(5,12,13)` $\to \mathbf{125/2197}$, `432/371293`; `(8,15,17)` $\to \mathbf{512/4913}$, `675/1419857`.
- **Exact Coupled $(O, H)$ Schur Pushforward `⧄` & Dark-Mode Shadow `⧅` ($m_O = 0$, $m_H > 0$):**

| Coupled Graph | $\det(M) = \det(M_{HH})\det(S_O)$ | Induced $J_{\mathrm{dark}} = -M_{OH}M_{HH}^{-1}m_H$ | Observable Potential $\phi_O$ (`0` residual vs full) | Energy Split $E_{\mathrm{full}} = E_O + \Delta E_H$ |
|---|---|---|---|---|
| `2×2` (`1+1`) | `5 = 2 · (5/2)` | `[2]` (`> 0`) | `[4/5]` (`> 0`) | `48/5 = 8/5 + 8` |
| `4×4` (`2+2`) | `192 = 15 · (64/5)` | `[17/15, 23/15]` (`> 0`) | `[11/24, 13/24]` (`> 0`) | `149/12 = 27/20 + 166/15` |
| `6×6` (`3+3`) | `4200 = 72 · (175/3)` | `[5/6, 4/3, 11/6]` (`> 0`) | `[11/30, 1/2, 19/30]` (`> 0`) | `302/15 = 32/15 + 18` |

  - All `3/3` full operators $M$, hidden blocks $M_{HH}$, and Schur complements $S_O = M \mathbin{⧄} O$ pass exact Bareiss Sylvester positive-definiteness (`100%` leading minors `> 0`).

### Pillar 4 — Shtanov–Sahni Bounce, DMPR Pell Shadows & GW170817/CMB Observational Gates
- **Shtanov–Sahni Timelike Bounce (`2602.06691`) vs Singular RS-II:**
  - $H_{\mathrm{SS}}^2(x) = x(1 - x)$ hits exact regular turnaround $H_{\mathrm{SS}}^2(1) = 0$ with $\partial_x H_{\mathrm{SS}}^2|_{1} = -1 < 0$, peak $H_{\mathrm{SS}}^2(1/2) = 1/4$, and strictly positive bounce acceleration $\dot{H}(1) = +2$ (radiation $w=1/3$) and $+3/2$ (dust $w=0$); RS-II $H_{\mathrm{RS}}^2(x) = x(1+x)$ has $H_{\mathrm{RS}}^2(1) = 2 > 0$, $\partial_x H_{\mathrm{RS}}^2|_{1} = 3 > 0$, and $\dot{H}_{\mathrm{RS}}(1) = -6 < 0$ (singular collapse).
- **DMPR Braneworld Metric $f(r) = 1 - \frac{2M}{r} + \frac{q}{r^2}$ & Exact Pell Equation $b^2 - 8 a^2 = 1$ (`2607.13992` *DARK-HIDE*):**
  - Setting $\hat{q} = q/M^2 = 1 - a^2$ yields rational horizon $r_h/M = 1 + a$ and rational photon sphere $r_{\mathrm{ph}}/M = (3 + b)/2$ iff **$b^2 - 8 a^2 = 1$**, identically parametrized over $\mathbb{Q}$ by $a(t) = \frac{2t}{t^2 - 8}, b(t) = \frac{t^2 + 8}{t^2 - 8}$.
  - Envelope theorem proves unconditional strict shadow enlargement for negative tidal charge: $\frac{d(b_{\mathrm{crit}}^2)}{d\hat{q}} = -\frac{1}{f(r_{\mathrm{ph}})^2} < 0$.
  - Certified strict shadow chain:
    $$b_{\mathrm{crit}}^2(+1) = 16 \;<\; b_{\mathrm{crit}}^2(0) = 27 \;<\; b_{\mathrm{crit}}^2\!\left(-\tfrac{495}{289}\right) = \tfrac{574992}{14161} \;<\; b_{\mathrm{crit}}^2(-2) = \tfrac{128}{3} \;<\; b_{\mathrm{crit}}^2(-35) = \tfrac{2000}{9}.$$
  - For the benchmark $\hat{q} = -1$, exact algebraic simplification yields $b_{\mathrm{crit}}^2(-1) = \frac{71 + 17\sqrt{17}}{4} = \frac{71 + \sqrt{4913}}{4}$, strictly enclosed via $70^2 = 4900 < 4913 < 5041 = 71^2$ in **`(141/4, 71/2) = (35.25, 35.50)`** (`~35.2732 M^2`, strictly above Schwarzschild `27 M^2`).
- **GW170817 & CMB $z = 1100$ Phase-Constraint Gates (Exact $\mathbb{Z}/\mathbb{Q}$ Arithmetic Checks vs. Heuristic Cosmological Inference):**
  - *Exact $\mathbb{Z}/\mathbb{Q}$ arithmetic checks over published literature benchmarks:* $\frac{98}{25} < 4 < \frac{409}{100}$ (`[3.92, 4.09]`), exact margin $5 - \frac{409}{100} = \frac{91}{100} > 0$, exact screening amplitude ratio squared $R_c / d_L = 10/40 = 1/4$, exact Planck 2018 benchmark ratio $\Omega_{\mathrm{DM}} / \Omega_b = \frac{12000}{2237} \in (5, 6)$ (`5.3643`), and exact epoch inequality $z_{\mathrm{CMB}} = 1100 > z_{\mathrm{stars}} = 30$.
  - *Heuristic cosmological model inference (external to $\mathbb{Z}/\mathbb{Q}$ arithmetic):* Interpreting Pardo et al. (2018)'s GW170817 interval as excluding naive flat infinite $D = 5$ bulk leakage (thus motivating warped, compactified, or horizon-localized bulk geometries) and interpreting $z_{\mathrm{CMB}} \gg z_{\mathrm{stars}}$ with $\Omega_{\mathrm{DM}} / \Omega_b \approx 5.36$ as disfavoring post-stellar-only black-hole dark matter both depend on external astrophysical modeling assumptions and published observational error bars, not purely on exact arithmetic.

---

## 3. Audit Architecture, Honest Scope & Strict I/O Security Boundary

- **`entropy_bulk_projection_audit.py --check <cert.json>`** enforces fail-closed strict I/O (concrete `pathlib.Path`, NUL/surrogate refusal, deleted-CWD `CWD_UNAVAILABLE`, atomic `dir_fd` `O_RDONLY|O_DIRECTORY|O_NOFOLLOW` PWD & ancestor traversal with root-owned macOS Darwin `/tmp` / `/var` / `/etc` $\to$ `/private/*` prefix normalization and zero `os.path.islink`, leaf `O_NOFOLLOW|O_NONBLOCK` + `S_ISREG` + `64 KiB` streaming capped reads with `max_bytes <= 64 MiB`, CRLF/trailing-LF/UTF-8/canonical-ASCII-JSON checks, iterative depth/bit-capped JSON validation with symmetric `MAX_INT_BITS = 3321` $\leftrightarrow$ `MAX_INT_DIGITS = 1000` round-trip bounds across all parsers and formatters), then executes:
  1. **Full deterministic pure-$\mathbb{Z}/\mathbb{Q}$ replay** (`validate_certificate_payload(cert, full_replay=True)` enforcing strict `bool` on `full_replay`, 64-char lowercase ASCII hex validation before `hmac.compare_digest`, exact digest & canonical byte match, plus structural/exact-int schema check even under `full_replay=False`);
  2. **Field-complete division-free secondary algebraic invariant cross-check** (`secondary_audit_payload`) running iterative JSON-tree validation at entry (rejecting all float and subclass injections on direct API calls) and fail-closed verifying exact nested key sets, epistemic-scope and hygiene flags, exact-`int` (non-`bool`) types, list cardinalities, exact rational values, and division-free cross-multiplied algebraic identities (`det_m == det_m_hh * det_s_o`, `full_energy == obs_schur_energy + dark_shadow_energy_deficit`, `p_pert == p_star + delta`, `kappa * rh == cw * cw`, `knorm * rh == 1`, `b^2 - 8 a^2 == 1`, `f_ph * r_ph^2 == r_ph^2 - 2 r_ph + q`, `b2 * f_ph == r_ph^2`, `db2_dq * f_ph^2 == -1`, `rat * ob == odm`) across all four pillars under both `full_replay=True` and `full_replay=False`.
- **Honest Scope Note:** `entropy_bulk_projection_audit.py` imports canonicalization, parsing, and replay primitives from `entropy_bulk_projection_oracle.py`; `--check` is therefore a **full pure-$\mathbb{Z}/\mathbb{Q}$ deterministic replay + field-complete division-free secondary algebraic invariant cross-check**, while independent zero-shared-code re-derivation is reserved for external clean-room auditors.
- **Atomic Write Hardening (`--write`):** Validates `type(data) is bytes` before opening any directory/temp descriptor; refuses hardlinked targets (`st_nlink > 1`, permitting `st_nlink <= 1` under concurrent same-target unlinks); generates thread-locked monotonic + CSPRNG (`secrets.token_hex(8)`) `0o600` temp files via `O_WRONLY|O_CREAT|O_EXCL|O_NOFOLLOW|O_NONBLOCK` with 32-attempt `EEXIST` retry (`TEMP_RETRY_EXHAUSTED`); calls `os.fsync(tmp_fd)`; enforces pre-replace `os.fstat(tmp_fd).st_nlink == 1` (`HARDLINK_FORBIDDEN` with temp cleanup on any failure); atomically replaces via `os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd)`; and calls `os.fsync(dfd)`. Under standard POSIX semantics, a malicious same-UID process with write access to the parent directory remains outside any user-space process boundary.

---

## 4. Verification Receipts (Strictly Sequential)

| Gate | Scope & Command Class | Result |
|---|---|---|
| **Standard 3-Mode Isolated + Hashseed Parity** | `-I -B`, `-I -O -B`, `-I -B -W error`, plus `-I -O -B -W error` & `PYTHONHASHSEED=42 -B` | **PASS**: standalone `5207acf2...` (mode `0o600`), `--check --json` `e483c6f1...`, test suite `11/11 OK`, zero-arg `OK` (bit-identical across all runs) |
| **Exhaustive Leaf, Zero-Denom, Subclass & Float Sweep** | All `359` payload leaves across `verify_certificate_dict(full_replay=False)`, direct `secondary_audit_payload`, & live CLI `--check` | **PASS**: `1,422/1,422` FR0 + `1,422/1,422` direct secondary + `359/359` floats + `250/250` subclasses + `12/12` live CLI zero-denom (`0` accepted, `0` raw exceptions, `0` `rc=1` tracebacks) |
| **Live AST Mutation Testing (`mutate`)** | `--max-mutants 0 --work-root . --add-cwd --timeout 60` on both `oracle.py` & `audit.py` | **PASS `154/154` (`100.0%`, `survived=0`, `truncated=False`)**: `oracle.py` `72/72` + `audit.py` `82/82` |
| **Whole-File AST `BoolOp` (`OP_SWAP + SUBCOND_DEL`)** | All `36` `ast.BoolOp` nodes across `oracle.py` & `audit.py` | **PASS `109/109` (`100.0%`, `surv=[]`)**: `oracle.py` `64/64` (`21` nodes) + `audit.py` `45/45` (`15` nodes) |
| **4-Surface Adversarial Fuzzer** | CLI + `verify_certificate_dict(full_replay=True)` + `verify_certificate_dict(full_replay=False)` + `oracle.validate_certificate_payload(full_replay=False)` | **PASS `77/77` (`100.0%`) on ALL `4` surfaces**: `23/23` CLI + `18/18` FR1 + `18/18` FR0 + `18/18` FR0+Oracle (`bypasses=0, crashes=0`) |
| **Live Concurrency, Kernel Races & `procfs`** | `16T` distinct + `16T` same + `80T` burst + live `renameat2(RENAME_EXCHANGE)` + `os.link`/`os.unlink` + `/proc/kallsyms` | **PASS**: `16T` distinct (`0o600`), `16T` same (`0o600`), `80T` burst (`0` errs/`0` temps); `>= 500` `renameat2` swaps (`0` leaks/`0` clobbers/`0` temps); `>= 420` hardlink flips (`0` clobbers/`0` temps); `/proc/kallsyms` -> `FILE_TOO_LARGE` |
| **Static AST & Audit-Check Verification** | `audit-check . --strict-ancestors --safety-scan --scripts entropy_bulk_projection_audit.py test_entropy_bulk_projection_r5.py` | **PASS** (`5` files, `2/2` isolated parity scripts, `0` findings, `0` AST floats/`float()`/bare `assert`s/`.isdigit()`, `0` JSON floats, `PYC=0`, `CRLF=0`, `0` leaks) |

---

## 5. Frozen File Manifest (Non-Report Files)

| File | Lines | Bytes | Mode | SHA-256 |
|---|---:|---:|---|---|
| `entropy_bulk_projection_oracle.py` | `1417` | `65918` | `0o644` | `2875c6805b643779758e771f3500e5aec03e21a42f59e7a21617c1c98af745f0` |
| `entropy_bulk_projection_audit.py` | `1115` | `49266` | `0o644` | `1f3682a20dc5214be8cb33831e3a47991d7e5b75ae45107c7008a25712fb089e` |
| `test_entropy_bulk_projection_r5.py` | `1012` | `63503` | `0o644` | `878dbe7b6f5891b6358b407fc98de4628be2716865e65033f49f70ddfbddef13` |
| `entropy_bulk_projection_certificate.json` | `1` | `10419` | `0o600` | `5207acf2f586d4d964336d540fda7f76384c2472840dee2150d7d5ac20ce4b35` |
