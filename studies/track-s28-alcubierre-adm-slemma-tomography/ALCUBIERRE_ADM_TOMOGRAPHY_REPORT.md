# Track S28 (Portal 24): Exact-$\mathbb{Q}$ Alcubierre ADM, S-Lemma (`⦺`), Hawking–Ellis, Horizon & Physical-Shell Tomography

**Track ID:** `TRACK-S28-ALCUBIERRE-ADM-SLEMMA-TOMOGRAPHY`  
**Schema:** `aletheia.alcubierre_adm_tomography.certificate.v1`  
**Oracle Class:** `exact` (100% pure Python 3 standard library; exact $\mathbb{Z}/\mathbb{Q}$ `Fraction` arithmetic; `0` AST floats, `0` bare `assert`s, `0` RNG)  
**Novelty Classification (Law 4):** **`N0`/`N1` Honest Framing** — exact-$\mathbb{Q}$ formal certification and unification of classical and 2024–2026 warp-drive results (`N0`), combined with genuinely novel zero-float exact-$\mathbb{Q}$ S-lemma / Krein-inertia certification, explicit rational boundary/blind-spot witnesses, and an exact algebraic Beltrami–Natário helicity bridge (`N1`).

---

## 1. Executive Summary & Honest Law-4 / `CS-13` Literature Grounding

Track S28 delivers a self-contained, zero-float, pure-$\mathbb{Q}$ 4D General Relativity tomography suite for ADM warp-drive spacetimes and physical subluminal shells, grounded against classical foundations (Alcubierre 1994; Pfenning & Ford 1997; Van Den Broeck 1999; Natário 2002; Finazzi, Liberati & Barceló 2009 `arXiv:0904.0141`) and the 2021–2026 warp-metric literature (`arXiv:2105.03079`, `arXiv:2205.15950`, `arXiv:2207.06458`, `arXiv:2405.02709`, `arXiv:2512.18008v1`, `arXiv:2602.16495v1`, `arXiv:2602.18023v6`, `arXiv:2609.36211v1`, `arXiv:2610.17629`).

- **`N0` (Exact-$\mathbb{Q}$ Certification of Known Theorems & Bounds):**
  - Arbitrary-lapse 3+1 ADM divergence–enstrophy Hamiltonian identity and vorticity/lapse-gradient momentum identity; Gullstrand–Painlevé Schwarzschild vacuum flux $\oint \mathbf{J}_{\mathrm{ADM}}\cdot d\mathbf{S} = 16\pi M$ (`arXiv:2105.03079`, `arXiv:2205.15950`, `arXiv:2512.18008v1`).
  - Alcubierre exact longitudinal equation of state $w_x = p_x / \rho_E \equiv +3$ and mandatory two-annulus equatorial Hawking–Ellis Type-IV obstruction expanding as $v \to 0^+$ (`arXiv:2602.16495v1`).
  - Natário zero-expansion Stokes-flow thin-wall minimizer $f^*(x) = \frac{3}{2}x^2 - x^3$ achieving the sharp constant $1/4$ and finite-aspect concentric-sphere resistance (`arXiv:2609.36211v1`).
  - Superluminal ($v > 1$) Killing horizon geometry, antisymmetric front white-hole / rear black-hole surface gravities derived directly from comoving 4D Christoffel symbols $\Gamma^t_{00}$ ($\kappa_{\mathrm{front}} = +v f'(r_H) < 0$ white-hole blueshift, $\kappa_{\mathrm{rear}} = -v f'(r_H) > 0$ black-hole Hawking), Pfenning–Ford $v^2$ wall-energy scaling, and subluminal ($v < 1$) horizon absence (`arXiv:0904.0141`, `arXiv:2207.06458`).
  - Conformally flat Lichnerowicz Hamiltonian constraint, Van Den Broeck compact collar zero weighted curvature integral vs. Schwarzschild ADM-mass tail, and positive-energy subluminal spherical shells (`arXiv:2405.02709`, `arXiv:2610.17629`).
- **`N1` (New Exact-$\mathbb{Q}$ Certification Engines, Boundary Witnesses & Cross-Track Bridges):**
  1. **Zero-Float Exact-$\mathbb{Q}$ S-Lemma / Sylvester–Krein Inertia (`⦺`) Engine:** Upgrades the numerical SDP / floating-point eigenvalue machinery of `arXiv:2602.18023v6` to exact rational Bunch–Kaufman congruence inertia `krein_inertia_exact(M) -> (n_+, n_0, n_-)` over `Fraction`, producing unconditional all-observer certificates for NEC, WEC, SEC, and DEC via exact multipliers $(\lambda_{\mathrm{NEC}}, \lambda_{\mathrm{WEC}}, \lambda_{\mathrm{SEC}}, \mu_{\mathrm{DEC}})$ alongside exact Pythagorean-quadruple causal violation witnesses.
  2. **Irrotational Non-Unit-Lapse Type-IV Boundary Witness:** Explicit rational 4D jet ($N = 3/2, \partial_x N = 5, S = I_3, \boldsymbol{\omega} = 0$) proving $G_{\hat{0}\hat{0}} = 4/3 > 0$, $G_{\hat{0}\hat{1}} = -40/9$, $G_{\hat{1}\hat{1}} = -4/3$, $\Delta_{(0,1)} = -6400/81 < 0$ (Hawking–Ellis Type IV with explicit null NEC violation witness $k = (1,1,0,0), G(k,k) = -80/9 < 0$), cleanly demarcating the unit-lapse hypothesis of Rodal's irrotational Type-I theorem (`arXiv:2512.18008v1`).
  3. **Exact Eulerian Blind-Spot Witness:** Explicit unit-lapse irrotational Type-I 4D jet with $G_{\hat{0}\hat{0}} = +3 > 0$, $G_{\hat{0}\hat{i}} = 0$, $G_{\hat{1}\hat{1}} = -9$, passing Eulerian WEC while violating NEC/WEC along null $(1,1,0,0)$ ($-6$), Pythagorean quadruple $(7,6,3,2)$ ($-255$), and boosted timelike $(5,4,0,0)$ ($\eta = -9$, $-69$).
  4. **Exact Beltrami–Natário Helicity Bridge:** Pythagorean force-free Beltrami shift mode $\mathbf{k}=(3,4,0), \lambda=5$ unifying Natário zero-expansion warp drives directly with Chandrasekhar–Kendall helicity eigenmodes: $\nabla\cdot\boldsymbol{\beta}=0$, $\nabla\times\boldsymbol{\beta}=5\boldsymbol{\beta}$, $16\pi\mathbf{j}_E=-25\boldsymbol{\beta}$, and pointwise $16\pi\rho_E = -\frac{\lambda}{2}(\boldsymbol{\beta}\cdot\boldsymbol{\omega}) = -25/2$.
  5. **Dual Law-2 Steelman Physical Shells + Sharp DEC Threshold Witness:** Both a smooth 4D conformally flat Lichnerowicz shell jet and an Israel Minkowski-interior / Schwarzschild-exterior thin shell ($s = 4/5 \implies R/M = 50/9 > 9/4 > 25/12$) boosted by Pythagorean velocity $v = 3/5$ ($\gamma = 5/4$) are certified WEC+NEC+SEC+DEC `PASS` for all observers via S-lemma `⦺`, paired with a sharp sub-threshold negative control ($s = 1/6 \implies R/M = 72/35 < 25/12$) whose spacelike energy-flux DEC failure is witnessed by timelike observer $u = (6,0,5,0)$ ($\eta = -11 < 0$, $J^2 = 1225/144 > 0$).

---

## 2. Certified Five-Pillar Exact-$\mathbb{Q}$ Results

All results below are computed from first principles by `alcubierre_adm_oracle.py` via its exact 4D Christoffel $\to$ Ricci $\to$ Einstein jet engine (`einstein_tensor_from_jet`, `adm_conformal_einstein_jet`), exact sparse multivariate polynomial ring `MPoly` over $\mathbb{Q}$, and exact Bunch–Kaufman congruence engine `krein_inertia_exact`.

### Pillar 1 — Arbitrary-Lapse 4D ADM Identities, GP Boundary, Sign-Flip Duality & Type-IV Trigger
- **General 4D ADM Identities (non-constant $N$, time/space-varying $\boldsymbol{\beta}$):**
  - Hamiltonian constraint $16\pi N^2 \rho_E \equiv \nabla\cdot\mathbf{J}_{\mathrm{ADM}}(\boldsymbol{\beta}) - \frac{1}{2}|\boldsymbol{\omega}|^2$: exact residual `0`.
  - Momentum constraint $16\pi j_i \equiv -\frac{1}{N}(\nabla\times\boldsymbol{\omega})_i - \frac{2}{N^2}(\partial_j N)(S_{ij} - \delta_{ij}\operatorname{tr}S)$ (with $16\pi j_i = -2G_{\hat{0}\hat{i}}$): exact residual `[0, 0, 0]`.
- **Gullstrand–Painlevé Schwarzschild Boundary ($M = 2$, $r \in \{1, 4, 9, 16\}$):**
  - $\beta_r = \sqrt{2M/r} \in \{2, 1, 2/3, 1/2\} \subset \mathbb{Q}$; full 4D vacuum $G_{\mu\nu} \equiv 0$, $\rho_E \equiv 0$, $\boldsymbol{\omega} \equiv 0$, and radius-independent ADM flux $\oint_{S_r^2} \mathbf{J}_{\mathrm{ADM}}\cdot d\mathbf{S} / \pi = 32 = 16M$ at all four radii.
- **Unit-Lapse Sign-Flip Duality:**
  - Pointwise $-G^0{}_0 \equiv 8\pi(\rho_E - \boldsymbol{\beta}\cdot\mathbf{j}_E)$: exact residual `0`.
  - Exact 3D polynomial integration over compact bubble $\beta_x = (1-x^2)(1-y^2)(1-z^2)$, $\beta_y = x\beta_x$, $\beta_z = 0$ on $[-1, 1]^3$:
    - $\int \nabla\cdot\mathbf{J}_{\mathrm{ADM}} = 0$ (nontrivial pointwise cancellation),
    - $\int |\boldsymbol{\omega}|^2 = \frac{65536}{7875} > 0$,
    - $\int 16\pi\rho_E = -\frac{32768}{7875} < 0$,
    - $\int (-2G^0{}_0) = +\frac{32768}{7875} = -\int 16\pi\rho_E > 0$.
- **Irrotational Non-Unit-Lapse Type-IV Trigger:**
  - $N = 3/2$, $\partial_x N = 5$, $S = I_3$, $\boldsymbol{\omega} = 0$: $G_{\hat{0}\hat{0}} = 4/3 > 0$, $G_{\hat{0}\hat{1}} = -40/9$, $G_{\hat{1}\hat{1}} = -4/3$, $\Delta_{(0,1)} = -6400/81 < 0$ (Type IV); null witness $k = (1,1,0,0)$ yields $G(k,k) = -80/9 < 0$.
  - Unit-lapse control ($\nabla N = 0$ on identical shift jet): $G_{\hat{0}\hat{i}} \equiv [0, 0, 0]$ (Type I).

### Pillar 2 — Exact Alcubierre $w_x \equiv +3$ EOS & Mandatory Two-Annulus Type-IV Obstruction
- **Off-Equatorial Full-4D Verification:** At generic off-equatorial jet ($v = 7/5$, nonzero $f_x, f_y, f_z, f_{xy}, f_{xz}, f_{yz}$), $G_{\hat{0}\hat{0}} \equiv -\frac{1}{4}v^2(f_y^2 + f_z^2)$ and $G_{\hat{1}\hat{1}} \equiv 3 G_{\hat{0}\hat{0}}$ ($w_x \equiv +3$) hold identically.
- **Smooth $C^3$ Septic Hermite Wall ($h(u) = 1 - 35u^4 + 84u^5 - 70u^6 + 20u^7$, $R=4, \Delta=2, v=2$):**
  - Inner shoulder $u = 1/10$ ($\rho = 21/5$): $\Delta_{(0,1)} = -\frac{11989959449182909119}{6250000000000000000} < 0$ (**Type IV**).
  - Core inflection $u = 1/2$ ($\rho = 5$): $G_{\hat{0}\hat{0}} = -1225/1024$, $G_{\hat{1}\hat{1}} = -3675/1024$, $G_{\hat{0}\hat{1}} = -7/32$, $\Delta_{(0,1)} = +1488081/65536 > 0$ (**Type I**, still NEC/WEC violated).
  - Outer shoulder $u = 9/10$ ($\rho = 29/5$): $\Delta_{(0,1)} = -\frac{9482732321762826569079}{5256250000000000000000} < 0$ (**Type IV**).
- **Subluminal Type-IV Expansion Sweep ($19$ interior stations $u = k/20$):** As $v$ decreases across $(2, 1, 1/2, 1/5, 1/10)$, Type-IV coverage rises strictly monotonically: `14/19 -> 16/19 -> 17/19 -> 18/19 -> 19/19 (1)`.

### Pillar 3 — Zero-Float Exact-$\mathbb{Q}$ S-Lemma / Krein Inertia (`⦺`) & Eulerian Blind Spot
- **Exact Congruence Inertia Benchmarks:** $\operatorname{in}(\eta) = (3, 0, 1)$, zero-diagonal hyperbolic $2\times 2$ block $= (1, 0, 1)$, rank-deficient $3\times 3$ hyperbolic block $= (1, 1, 1)$.
- **Observer-Robust Satisfaction on Non-Diagonal Boosted Perfect Fluid:** Rest-frame $\operatorname{diag}(5, 1, 1, 1)$ boosted by exact Pythagorean velocity $v = 3/5$ ($\gamma = 5/4$) has nonzero off-diagonal momentum flux $T_{01} \ne 0$, yet multipliers $(\lambda_{\mathrm{NEC}}, \lambda_{\mathrm{WEC}}, \lambda_{\mathrm{SEC}}, \mu_{\mathrm{DEC}}) = (2, 2, 2, 10)$ certify inertia `(4, 0, 0)` across all four energy conditions (**NEC+WEC+SEC+DEC `PASS` for ALL observers**).
- **Exact Pythagorean-Quadruple Violation Witness on Alcubierre Core:** Null vector $k = (3, 2, 2, 1)$ ($\eta(k,k) = 0$) certifies $G_{\mathrm{core}}(k,k) = -13489/512 < 0$.
- **Eulerian Blind-Spot Irrotational Type-I Witness:** Unit-lapse irrotational jet yields $G_{\hat{0}\hat{0}} = +3 > 0$ and $G_{\hat{0}\hat{i}} = 0$ (passing Eulerian WEC), yet $G_{\hat{1}\hat{1}} = -9$, violated by null $(1,1,0,0)$ ($-6$), Pythagorean quadruple $(7,6,3,2)$ ($-255$), and timelike $(5,4,0,0)$ ($\eta = -9$, $-69$).

### Pillar 4 — Natário Stokes-Flow $1/4$ Minimum, Beltrami Helicity Bridge & Killing Horizons
- **Sharp Thin-Wall Stokes Minimizer:** $f^*(x) = \frac{3}{2}x^2 - x^3$ achieves exact constant $c^* = 1/4$ vs. smooth $C^2$ quintic competitor $f_5(x) = \frac{1}{2}(10x^3 - 15x^4 + 6x^5)$ achieving $c_5 = 5/14 > 1/4$, with exact Euler–Lagrange cross-term $\int_0^1 (f^*)'' (f_5'' - (f^*)'')\,dx = 0$ and exact SOS gap $J(f_5) = J(f^*) + \|f_5'' - (f^*)''\|_{L^2}^2$.
- **Exact Finite-Aspect Concentric-Sphere Stokes Resistance ($|E_{\mathrm{Stokes}}|/(v^2 R)$):**
  - $\Delta/R = 1/10 \to 2014683/6616$ (scaled $\varepsilon^3 E = 2014683/6616000 > 1/4$),
  - $\Delta/R = 1/5 \to 41859/908$ ($\varepsilon^3 E = 41859/113500 > 1/4$),
  - $\Delta/R = 1/2 \to 1899/376$ ($\varepsilon^3 E = 1899/3008 > 1/4$),
  - $\Delta/R = 1 \to 93/68$ ($\varepsilon^3 E = 93/68 > 1/4$).
- **Exact Beltrami Helicity Bridge:** Pythagorean mode $\mathbf{k} = (3, 4, 0)$, $\lambda = 5$, phase $(3/5, 4/5)$ satisfies $\nabla\cdot\boldsymbol{\beta} = 0$, $\nabla\times\boldsymbol{\beta} = 5\boldsymbol{\beta}$, $16\pi\mathbf{j}_E = -25\boldsymbol{\beta}$, helicity density $\boldsymbol{\beta}\cdot\boldsymbol{\omega} = 5$, Coulomb norm $|\boldsymbol{\beta}|^2/\lambda = 1/5$, and exact pointwise $16\pi\rho_E = -25/2 = -\frac{\lambda}{2}(\boldsymbol{\beta}\cdot\boldsymbol{\omega})$.
- **Superluminal Killing Horizons vs. Subluminal Horizon Absence:**
  - Superluminal $v = 2$ (comoving frame $ds^2 = -dt^2 + (dx' + v(1-f)\,dt)^2 + dy^2 + dz^2$, Killing vector $\xi = \partial_t$, $\xi^\nu\nabla_\nu\xi^\mu = \Gamma^\mu_{00} = \kappa\,\xi^\mu$ computed via `christoffel_from_metric_jet`): exact horizon midpoint $u_H = 1/2$, $r_H = 5$, $f(r_H) = 1/2 = 1 - 1/v$, comoving $g'_{tt}(r_H) = 0$; **front wall** ($x' = +5$, $\partial_{x'} f = -35/32 < 0$) is a **white-hole / blueshift horizon** with $\Gamma^0_{00} = \kappa_{\mathrm{front}} = +v f'(r_H) = -35/16 < 0$ (exponential RSET pileup, matching Finazzi–Liberati–Barceló `arXiv:0904.0141v2` Sec. II.A Eqs. (6),(13)), and **rear wall** ($x' = -5$, $\partial_{x'} f = +35/32 > 0$) is a **black-hole / Hawking horizon** with $\Gamma^0_{00} = \kappa_{\mathrm{rear}} = -v f'(r_H) = +35/16 > 0$ ($\Gamma^{1,2,3}_{00} = 0$ at both walls); Pfenning–Ford wall scaling exponent $v^2$.
  - Subluminal $v = 3/5$: strictly horizon-free ($\max g'_{tt} = -16/25 < 0$).

### Pillar 5 — Law-2 Steelman: Conformally Flat Lichnerowicz & Physical Subluminal Shells
- **General 4D Lichnerowicz Hamiltonian Constraint:** $16\pi\rho_E \equiv -8\psi^{-5}\Delta\psi + K^2 - K_{ij}K^{ij}$ holds with exact residual `0` on a generic time- and space-varying $(\psi, N, \boldsymbol{\beta})$ jet.
- **Van Den Broeck Compact Collar vs. Schwarzschild ADM Tail:** Compact pocket $\psi = 1 + (1-x^2)^2(1-y^2)^2(1-z^2)^2$ on $[-1, 1]^3$ gives $\int \psi^5 R^{(3)} = -8\int\Delta\psi = 0$, contrasting with the isotropic Schwarzschild tail $\psi = 1 + M/(2r)$ ($M = 2$) yielding $16\pi M_{\mathrm{ADM}} = 32\pi$.
- **Boosted ($v = 3/5, \gamma = 5/4$) Smooth 4D Conformally Flat Shell Jet:** Computed directly from `adm_conformal_einstein_jet` at $r=10, \psi=21/20, \psi'=-1/200, \psi''=-1/100, N=19/20, N'=1/200, N''=1/2000$ ($\rho_{\mathrm{rest}} = 140800/4084101$, $p_r = -60800/85766121$, $p_t = -25462400/1629556299$); boosted flux $G_{01} \ne 0$, yet S-lemma multipliers $(\lambda_{\mathrm{NEC}}, \lambda_{\mathrm{WEC}}, \lambda_{\mathrm{SEC}}, \mu_{\mathrm{DEC}}) = (\frac{70400}{4084101}, \frac{70400}{4084101}, \frac{48800}{77597919}, \frac{9912320000}{16679880978201})$ yield inertia `(4, 0, 0)` across all four conditions (**WEC+NEC+SEC+DEC `PASS` for ALL observers**).
- **Boosted ($v = 3/5$) Israel Thin Shell ($s = \sqrt{1-2M/R} = 4/5 \implies R/M = 50/9 > 9/4 > 25/12$):** $8\pi R\sigma = 2/5$, $8\pi R p_\theta = 1/40$, S-lemma multipliers $(1/5, 1/5, 1/5, 1/10)$ yield `(4, 0, 0)` across all four conditions (**WEC+NEC+SEC+DEC `PASS` for ALL observers**).
- **Sharp Negative Control ($s = 1/6 \implies R/M = 72/35 < 25/12$):** $8\pi R\sigma = 5/3 < 8\pi R p_\theta = 25/12$; timelike observer $u = (6, 0, 5, 0)$ ($\eta(u, u) = -11 < 0$) witnesses spacelike energy flux $J^2 = 1225/144 > 0$ (**DEC violation certified**; note $u = (5, 0, 4, 0)$ sits exactly on the null-flux boundary $J^2 = 0$ and is cleanly rejected as a strict violation witness).

---

## 3. Zone-B Hardening Architecture & Independent Verification Scope

- **`--check` Verification Model:** `alcubierre_adm_audit.py --check <cert.json>` performs **full pure-$\mathbb{Q}$ deterministic replay** (`validate_certificate_payload(..., full_replay=True)`, re-computing all five pillars and comparing canonical SHA-256 digests in constant time) **plus** an independent **secondary algebraic cross-check** (`secondary_algebraic_audit`) that re-parses rational strings and re-verifies every algebraic invariant, discriminant identity, sign condition, and threshold across all five pillars. (Because `--check` invokes the shared oracle replay engine, it is accurately characterized as full pure-$\mathbb{Q}$ replay + secondary algebraic cross-check, not zero-shared-code verification.)
- **Race-Free File I/O & CLI Hardening:**
  - Per-component `dir_fd` traversal via `os.open(..., O_RDONLY | O_DIRECTORY | O_NOFOLLOW, dir_fd=dfd)` eliminating directory-swap TOCTOU races (`ELOOP`/`ENOTDIR` $\to$ `SYMLINK_FORBIDDEN`).
  - Leaf reads open via `O_RDONLY | O_NOFOLLOW | O_NONBLOCK` inside the resolved parent `dir_fd`, verify `S_ISREG(fstat(fd))`, and stream in `65,536`-byte chunks strictly capped at `MAX_JSON_BYTES = 1,048,576` (safely halting pseudo-files like `/proc/kallsyms` with `FILE_TOO_LARGE`).
  - Leaf writes refuse symlinks, non-regular files, and hardlinks (`st_nlink > 1` $\to$ `HARDLINK_FORBIDDEN`), create a unique sibling temp file via `O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_NONBLOCK` inside the same `dir_fd`, write completely, and atomically swap via `os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd)` with fail-closed cleanup on error.
  - Explicit fail-closed guards for deleted CWD (`CWD_UNAVAILABLE`, `rc=2`), lone UTF-16 surrogates across `argv`, `Path`, `PWD`, and JSON (`INVALID_UTF8_SURROGATE`, `rc=2`), ASCII-only rational digits in `parse_exact_rational` (rejecting Unicode superscript/circled/Arabic-Indic/fullwidth digits with `INVALID_RATIONAL`), strict exact-`Fraction` / shape / dimension / symmetry validation across all exported linear-algebra, S-lemma, witness, and `MPoly` helpers (preventing silent `int / int -> float` precision loss), and strict manual CLI parsing rejecting flag-like and equals-syntax path injections (`--write --json`, `--check --json`, `--write=--json`, `--check=--json` $\to$ `rc=2`, `0` files created).

---

## 4. Verification Receipts & Frozen Artifact Manifest

All verification runs executed strictly sequentially (`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1`) against the frozen artifacts below:

| Gate | Command / Scope | Observed Result |
|---|---|---|
| **Unit & Adversarial Suite** | `python3 -I -B test_alcubierre_adm_r5.py -v` | **`14/14 OK`** |
| **3-Mode Isolated Parity** | `-I -B`, `-I -O -B`, `-I -B -W error` (plus `-I -O -B -W error` & `PYTHONHASHSEED=42 -B`) | **Bit-identical**: standalone `6d5579f5...`, `--check --json` `2b4bcfde...`, `14/14 OK` |
| **Default-CLI `aletheia v2.0.0 mutate`** | `--max-mutants 0 --work-root . --add-cwd` (no `--guards`) | **`54/54` (`oracle`) + `78/78` (`audit`) = `132/132` (`100.0%`, `survived=0`, `truncated=False`, `PASS`)** |
| **Exhaustive AST `BoolOp` (`SWAP+SUBCOND_DEL`)** | All `BoolOp` AST nodes (`timeout=30`) | **`54/54` (`18` SWAP + `36` DEL, `oracle`) + `6/6` (`2` SWAP + `4` DEL, `audit`) = `60/60` (`100.0%`, `surv=[]`)** |
| **Zone-B Adversarial Fuzzer** | `23` CLI vectors + `18` in-memory vectors | **`41/41 PASS`** (`bypasses=0, crashes=0`) |
| **Live `renameat2(RENAME_EXCHANGE)` Race** | `700` concurrent reads + `700` concurrent writes | **`12,552` swaps**, `read(ok=319, rej=381, leaks=0)`, `write(ok=90, rej=610, clobbers=0)`, `leftovers=0` |
| **Live `os.link`/`os.unlink` Hardlink Race** | `600` concurrent writes vs. live linker thread | **`680` link ops**, `ok=114, rej=486`, `clobbered=False`, `leftovers=0` |
| **Pseudo-file & Deleted-CWD Probes** | `/proc/kallsyms` + live deleted-CWD subprocess | `/proc/kallsyms` $\to$ `FILE_TOO_LARGE`; deleted CWD $\to$ `rc=2 CWD_UNAVAILABLE` |
| **AST Float / Bare-Assert Scan** | All 3 `.py` files (`alcubierre_adm_oracle.py`, `alcubierre_adm_audit.py`, `test_alcubierre_adm_r5.py`) | **`0` float literals, `0` `float()` calls, `0` bare `assert`s** |
| **`aletheia v2.0.0 audit-check`** | `--strict-ancestors --safety-scan --scripts alcubierre_adm_audit.py test_alcubierre_adm_r5.py` | **`PASS`** (`0` CRLF, `0` pycache, `0` leaks, `0` bare asserts, `2/2` isolated-parity scripts, `0` findings) |

### Frozen 4-File Code & Certificate Manifest

| File | Lines | Bytes | SHA-256 |
|---|---:|---:|---|
| `alcubierre_adm_oracle.py` | 1,622 | 74,048 | `b195ae8f87b270ca1529789ffd7c2e65255d5ccea1971b8c98e9cad856c56e99` |
| `alcubierre_adm_audit.py` | 498 | 22,436 | `aa76ff4843b3283b871ac02ab09289f1500ccbee03bd5135f447a01f8f4d5417` |
| `test_alcubierre_adm_r5.py` | 955 | 59,474 | `b969d344a607d08e0a4e8c53acabe5948c810e3f33a4a6f2ad89e891b12ad630` |
| `alcubierre_adm_certificate.json` | 1 | 7,831 | `6d5579f52d176f39d6f160a405873843ff616ca7d1d76c95f1a3d340237bbc9f` |

- **Certificate `payload_sha256`:** `4f05e6c96b0ebd7afa1927d67068e0f32d4e8d2e8ed5f7aabba8684767778532`
- **Certificate `certificate_sha256`:** `be9f1ab60fd7b242420331ff452961a2f00f0a0a9deccc6e5aab6f3d9a5bcacb`
- **Canonical `--check --json` Output SHA-256:** `2b4bcfdef7833d232d01ee5ce247fdef103af22bfe4ea3271e72c3c2f639caf6`
