# Planetary Fluid Dynamics & Plate Tectonics as Neural Network Linear Regions

**Study ID:** `track-s43-viscoplastic-tectonics-relu-regions`  
**Certificate Schema:** `aletheia.tectonics_relu_regions.certificate.v1`  
**Novelty & Scope Ledger:** `novelty_tier = N1` (unified exact-$\mathbb{Z}/\mathbb{Q}$ operator and explicit obstruction certification bridging viscoplastic plate tectonics and ReLU linear regions); `individual_domains_novelty = N0` (Duvaut–Lions 1972; Solomatov 1995; Moresi–Solomatov 1998; Tackley 2000; Bercovici 1993/2003; Montúfar et al. 2014; Zhang–Naitzat–Lim 2018); `oracle_class = exact`; `measured_live_mantle_convection_gcm = false`; `measured_live_deep_network_training_runs = false`; `zero_trust_path_floats = true`; `zero_bare_asserts = true`; `zero_mathematical_rng = true`.

---

## 1. Executive Summary

This study strips the analogy between planetary plate tectonics and neural network linear regions down to **four pure-$\mathbb{Z}/\mathbb{Q}$ algebraic pillars** (zero floating-point arithmetic, zero bare `assert` statements, zero mathematical RNG, zero third-party dependencies):

1. **Pillar 1 — Variational Bingham Viscoplasticity $\equiv$ Two-Sided ReLU Proximal Soft-Thresholding & 1D Poiseuille Plug-vs-Shear Partition:** Proves on a `41`-point exact rational stress grid that the Duvaut–Lions convex nonsmooth minimizer equals the two-sided ReLU soft-thresholding operator identically (with exact KKT subdifferential closure and strict variational dominance $\Delta\mathcal{J} \ge \eta_0 \delta^2 > 0$), and certifies the exact `1D` Bingham Poiseuille channel ($G=4, H=2, \tau_Y=4, \eta_0=1 \implies Y=1/2, y_p=1, u_{\mathrm{plug}}=2, Q_{\mathrm{half}}=10/3, Q_{\mathrm{full}}=20/3$) as a 2-neuron ReLU partition satisfying exact viscoplastic dissipation balance $D_{\mathrm{visc,half}} + D_{\mathrm{yield,half}} = 16/3 + 8 = 40/3 = G Q_{\mathrm{half}}$.
2. **Pillar 2 — Exact 3-Phase Dimensionless Yield-Number Diagram ($Y = \tau_Y / (G H)$) $\leftrightarrow$ Neural Linear-Region Regimes & 2D Shallow ReLU Regions:** Sweeps `8` exact rational yield numbers $Y \in \{0, 1/8, 1/4, 1/2, 3/4, 1, 5/4, 2\}$, certifying the sharp phase transition between **Newtonian / Magma Ocean** ($Y=0$), **Mobile Lid / Plate Tectonics** ($0 < Y < 1$), and **Stagnant Lid** ($Y \ge 1$, exact flux collapse $Q=0$); pairs this with a 2D `3`-neuron shallow ReLU network partitioning $\mathbb{Q}^2$ into `7` exact linear regions (`[0,0,1]` impossible) with piecewise-constant Jacobians and `9` continuous codimension-1 walls carrying exact rank-1 Jacobian jumps $\Delta J = c_k w_k^\top$.
3. **Pillar 3 — Exact R-T-F Triple-Junction 1-Cocycle $\leftrightarrow$ Tropical ReLU Codim-2 Balancing & 2D Jacobian-Determinant Flux Taxonomy:** Certifies the exact $\mathbb{Q}^3$ R-T-F triple junction at $p=(0,0,1)$ with $\omega_A=(0,1,0), \omega_B=(0,0,0), \omega_C=(-1,1,0)$ ($\omega_{AB}+\omega_{BC}+\omega_{CA}=0$, $v_{AB}+v_{BC}+v_{CA}=0$, splitting walls into Divergent Ridge $+1$, Convergent Subduction Trench $-2$, and Transform Fault shear $-1$); pairs this with the `3`-region tropical ReLU hinge $f(x,y)=\max(2x, 2y, -x-2y)$ satisfying exact gradient-jump cocycle $\Delta g_{AB}+\Delta g_{BC}+\Delta g_{CA}=0$ and nontrivial weighted tropical balancing $2(1,1) + 1(-4,1) + 1(2,-3) = (0,0)$, plus exact 2D ReLU Jacobian-determinant contrast ($\det J_+ \in \{3, 1/2, 0, 1\}$).
4. **Pillar 4 — Three Explicit Exact Obstructions on the Discrete $S^2$ Cube Cellular Hodge Complex (Zero Metaphor):** Constructs $(C^0 \xrightarrow{d_0} C^1 \xrightarrow{d_1} C^2)$ on the oriented discrete $S^2$ cube ($V=8, E=12, F=6, \chi=2, \operatorname{rank}(d_0)=7, \operatorname{rank}(d_1)=5, (\beta_0,\beta_1,\beta_2)=(1,0,1), d_1 d_0 \equiv 0_{6\times 8}$) to certify exactly where the two domains strictly diverge:
   - **Obstruction A (Toroidal-Zero $\equiv$ Conservative Gradient-Flow Curl-Zero):** Poloidal field $u_{\mathrm{pol}}=d_0\phi$ has identically zero curl ($d_1 u_{\mathrm{pol}}=0_6$); orthogonal toroidal field $u_{\mathrm{tor}}=d_1^\top\psi$ has identically zero outward discrete divergence ($\operatorname{div}(u_{\mathrm{tor}})=-d_0^\top u_{\mathrm{tor}}=0_8$); combined witness $u_{\mathrm{eq}}=u_{\mathrm{pol}}+u_{\mathrm{tor}}$ satisfies exact Hodge orthogonality ($\langle u_{\mathrm{pol}},u_{\mathrm{tor}}\rangle=0$), Pythagorean norm $\|u_{\mathrm{eq}}\|_2^2 = 4+4=8$, and exact equipartition $E_{\mathrm{tor}}/E_{\mathrm{pol}}=1$.
   - **Obstruction B (Compact-Manifold Gauss–Stokes Conservation vs. Unconstrained ReLU):** Using the standard DEC codifferential outward discrete divergence $\operatorname{div}(u) = \delta_1 u = -d_0^\top u$ (so a unit flux along oriented edge $e_i=(a \to b)$ with $d_0[e_i][a]=-1, d_0[e_i][b]=+1$ contributes $+1$ net outflow at tail $a$ and $-1$ net inflow at head $b$, verified `12/12`), all `12/12` basis edge fluxes on $S^2$ satisfy $\mathbf{1}_8^\top(-d_0^\top e_i) = 0$; the asymmetric witness $u_{\mathrm{asym}}=(-3,1,-2,0,-1,2,-4,0,3,-2,-1,1)$ yields $\operatorname{div}(u_{\mathrm{asym}})=(-1,3,1,-2,-9,4,5,-1)$ with net outflow / ridge creation `+13` = net inflow / trench subduction `-13` (global net `0`), whereas unconstrained 2D ReLU $F_{\mathrm{dead}}(x_1,x_2)=(\operatorname{ReLU}(x_1),\operatorname{ReLU}(x_2))$ on $[-1,1]^2$ collapses area by ratio `1/4` with global displacement divergence `-4 < 0`.
   - **Obstruction C (Static Feedforward Inference Freeze vs. Stateful `GDN-2` Rank-1 Advection):** A static ReLU wall ($x_1=1$) is frozen across inference turns ($\Delta x_{\mathrm{wall}}=0$, query $q=(3/2,0)$ stays `+1/2`), whereas a 1-step exact `GDN-2` rank-1 delta-rule memory update ($\alpha=1/2, \beta=1, k=(1,0), v=(1/4,0) \implies S_1=\operatorname{diag}(1/4,1/2)$, $\operatorname{rank}(\Delta)=1, S_1 k = v$) advects the effective wall $x_1=1 \to 4$ ($\Delta x_{\mathrm{wall}}=+3$) and flips $q=(3/2,0)$ from `+1/2` (`ReLU=1/2`) to `-5/8` (`ReLU=0`) under zero weight updates ($\Delta W = 0$).

---

## 2. Exact Mathematical Tables (Pure $\mathbb{Z}/\mathbb{Q}$)

### 2.1 Pillar 1 — Variational Proximal Identity (`41`-Point Grid, $\eta_0 = 3/2, \tau_Y = 2$)

| $\tau$ | $e^*(\tau)$ | KKT Subgradient $s \in [-1,1]$ | $\mathcal{J}(e^*)$ | $\mathcal{J}(e^* + 1/10) - \mathcal{J}(e^*)$ | $\mathcal{J}(e^* - 1/10) - \mathcal{J}(e^*)$ | Regime |
|---:|---:|---:|---:|---:|---:|:---|
| `-5` | `-1` | `-1` | `-3/2` | `3/200` | `3/200` | Negative shear (`12` grid pts) |
| `-2` | `0` | `-1` | `0` | `83/200` | `3/200` | Rigid plug boundary (`17` plug pts) |
| `0` | `0` | `0` | `0` | `43/200` | `43/200` | Rigid plug interior |
| `2` | `0` | `1` | `0` | `3/200` | `83/200` | Rigid plug boundary |
| `5` | `1` | `1` | `-3/2` | `3/200` | `3/200` | Positive shear (`12` grid pts) |

All `41/41` grid points $\tau_k = k/4$ ($k=-20,\dots,20$) satisfy exact KKT optimality $2\eta_0 e^* + \tau_Y s - \tau = 0$ with $|s| \le 1$ and strict variational dominance $\mathcal{J}(e^* \pm \delta) - \mathcal{J}(e^*) \ge \eta_0 \delta^2 > 0$ at $\delta \in \{1/10, 1\}$.

### 2.2 Pillar 2 — 3-Phase Dimensionless Yield-Number Sweep ($G=4, H=2, \eta_0=1$)

| $Y = \tau_Y/(GH)$ | $\rho_p = y_p/H$ | $u_{\mathrm{plug}}$ | $Q_{\mathrm{half}}$ | $Q_{\mathrm{full}}$ | $D_{\mathrm{visc,half}}$ | $D_{\mathrm{yield,half}}$ | Plastic Share | Active Walls | Tectonic Regime $\leftrightarrow$ Neural Regime |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---|
| `0` | `0` | `8` | `32/3` | `64/3` | `128/3` | `0` | `0` | `0` | `newtonian_magma_ocean` $\leftrightarrow$ `splintered_unregularized_limit` |
| `1/8` | `1/8` | `49/8` | `833/96` | `833/48` | `343/12` | `49/8` | `3/17` | `2` | `mobile_lid_plate_tectonics` $\leftrightarrow$ `modular_feature_learning` |
| `1/4` | `1/4` | `9/2` | `27/4` | `27/2` | `18` | `9` | `1/3` | `2` | `mobile_lid_plate_tectonics` $\leftrightarrow$ `modular_feature_learning` |
| `1/2` | `1/2` | `2` | `10/3` | `20/3` | `16/3` | `8` | `3/5` | `2` | `mobile_lid_plate_tectonics` $\leftrightarrow$ `modular_feature_learning` |
| `3/4` | `3/4` | `1/2` | `11/12` | `11/6` | `2/3` | `3` | `9/11` | `2` | `mobile_lid_plate_tectonics` $\leftrightarrow$ `modular_feature_learning` |
| `1` | `1` | `0` | `0` | `0` | `0` | `0` | `0` | `0` | `stagnant_lid` $\leftrightarrow$ `dead_relu_frozen_ntk` |
| `5/4` | `1` | `0` | `0` | `0` | `0` | `0` | `0` | `0` | `stagnant_lid` $\leftrightarrow$ `dead_relu_frozen_ntk` |
| `2` | `1` | `0` | `0` | `0` | `0` | `0` | `0` | `0` | `stagnant_lid` $\leftrightarrow$ `dead_relu_frozen_ntk` |

In the companion 2D `3`-neuron shallow ReLU network ($f(x) = I_2 x + \sum_{k=1}^3 c_k \operatorname{ReLU}(w_k \cdot x + b_k)$), all `7` nonempty activation patterns (`[0,0,1]` impossible) have certified piecewise-constant Jacobians ($\det J \in \{1, 3, -3, 4, 4, 13, 8\}$), and all `9` codimension-1 walls are continuous with exact rank-1 Jacobian jump $\Delta J = c_k w_k^\top$ ($\det \Delta J = 0, \Delta J \neq 0$).

### 2.3 Pillar 3 — R-T-F Triple Junction, Tropical ReLU Balancing & 2D Jacobian Contrast

- **R-T-F Triple Junction ($p=(0,0,1)$, $\omega_A=(0,1,0), \omega_B=(0,0,0), \omega_C=(-1,1,0)$):**
  - Exact 1-cocycle closure: $\omega_{AB}+\omega_{BC}+\omega_{CA} = (0,1,0)+(1,-1,0)+(-1,0,0) = (0,0,0)$ and $v_{AB}+v_{BC}+v_{CA} = (1,0,0)+(-1,-1,0)+(0,1,0) = (0,0,0)$.
  - Using uniform boundary tangent $t = n \times p$:
    - **AB (`divergent_ridge`):** $n=(1,0,0), t=(0,-1,0)$, opening $+1 > 0$, shear $0$.
    - **BC (`convergent_subduction_trench`):** $n=(1,1,0), t=(1,-1,0)$, opening $-2 < 0$, shear $0$.
    - **CA (`transform_fault`):** $n=(1,0,0), t=(0,-1,0)$, opening $0$, shear $-1 \neq 0$.
- **Tropical 3-Region ReLU Hinge ($l_A=2x, l_B=2y, l_C=-x-2y$):**
  - Gradient jumps: $\Delta g_{AB}=(2,-2), \Delta g_{BC}=(1,4), \Delta g_{CA}=(-3,-2) \implies \sum \Delta g = (0,0)$.
  - Tropical weights & primitive rays: $m_{AB}=2, r_{AB}=(1,1)$; $m_{BC}=1, r_{BC}=(-4,1)$; $m_{CA}=1, r_{CA}=(2,-3) \implies m_{AB}r_{AB}+m_{BC}r_{BC}+m_{CA}r_{CA}=(0,0)$ while unweighted $\sum r = (-1,-1) \neq (0,0)$.
- **2D ReLU Wall $F(x)=x+c\operatorname{ReLU}(x_1)$ ($\det J_- = 1$):**
  - `ridge_expanding` ($c=(2,0)$): $\det J_+ = 3$, rank `2`.
  - `trench_contractive` ($c=(-1/2,0)$): $\det J_+ = 1/2$, rank `2`.
  - `trench_dead_slab_collapse` ($c=(-1,0)$): $\det J_+ = 0$, rank `1`, explicit collision $F(1,5) = F(7,5) = (0,5)$.
  - `transform_volume_preserving_shear` ($c=(0,2)$): $\det J_+ = 1$, rank `2`, pure shear.

### 2.4 Pillar 4 — Discrete $S^2$ Cube Hodge Complex & Explicit Obstructions

- **Cellular Complex:** $V=8, E=12, F=6, \chi=2$; $d_1 d_0 \equiv 0_{6\times 8}$; $\mathbf{1}_6^\top d_1 \equiv 0_{12}$; $\operatorname{rank}(d_0)=7, \operatorname{rank}(d_1)=5 \implies (\beta_0, \beta_1, \beta_2)=(1,0,1)$.
- **Obstruction A:** $E_{\mathrm{pol}} = \|d_0\phi\|_2^2 = 4$ ($d_1 u_{\mathrm{pol}} = 0_6$), $E_{\mathrm{tor}} = \|d_1^\top\psi\|_2^2 = 4$ ($\operatorname{div}(u_{\mathrm{tor}}) = -d_0^\top u_{\mathrm{tor}} = 0_8$), $\langle u_{\mathrm{pol}}, u_{\mathrm{tor}}\rangle = 0$, $\|u_{\mathrm{pol}}+u_{\mathrm{tor}}\|_2^2 = 8$, $E_{\mathrm{tor}}/E_{\mathrm{pol}} = 1$.
- **Obstruction B:** Under outward discrete divergence $\operatorname{div}(u) = -d_0^\top u$ (DEC codifferential $\delta_1 = -d_0^\top$, verified `12/12` to assign $+1$ outflow at edge tail and $-1$ inflow at edge head), `12/12` standard basis edge fluxes satisfy $\mathbf{1}_8^\top(-d_0^\top e_i) = 0$; asymmetric witness $u_{\mathrm{asym}}=(-3,1,-2,0,-1,2,-4,0,3,-2,-1,1)$ yields $\operatorname{div}(u_{\mathrm{asym}})=(-1,3,1,-2,-9,4,5,-1)$ with net outflow / ridge creation `+13` and net inflow / trench subduction `-13` (global net `0`), whereas unconstrained 2D ReLU $F_{\mathrm{dead}}$ collapses area to `1/4` with global displacement divergence `-4 < 0`.
- **Obstruction C:** Static wall $x_1=1$ stays frozen ($\Delta x_{\mathrm{wall}}=0$, pre-activation `+1/2` -> `+1/2`); 1-step `GDN-2` update ($\alpha=1/2, \beta=1, k=(1,0), v=(1/4,0)$) gives rank-1 $\Delta$, exact key overwrite $S_1 k = v$, wall advection $1 \to 4$ ($\Delta x_{\mathrm{wall}}=+3$), and query flip `+1/2 -> -5/8` (`ReLU`: `1/2 -> 0`) with $\Delta W = 0$.

---

## 3. Strict I/O Security & Verification Architecture

- **Symmetric Integer & JSON Bounds:** `MAX_INT_BITS = 3321` (`|n| <= 2^{3321} - 1`) is the binding fail-closed enforcement cap across both parsing (`parse_exact_int_ascii`) and serialization (`_require_bounded_int` / `validate_json_tree_iterative`), paired with the pre-parse ASCII decimal-length guard `MAX_INT_DIGITS = 1000` ($10^{1000}-1$ has `1,000` digits / `3,322` bits and is rejected cleanly with `INT_TOO_LARGE`, preventing any raw Python `ValueError` on `>4,300`-digit integers), `MAX_JSON_DEPTH = 32`, `MAX_JSON_BYTES = 1_048_576`, zero floats, zero `NaN`/`Infinity`, zero duplicate keys, and zero lone UTF-16 surrogates.
- **Race-Free Atomic `dir_fd` I/O (`tectonics_relu_regions_audit.py`):** Concrete `pathlib.Path` enforcement, NUL/surrogate refusal, deleted-CWD `CWD_UNAVAILABLE` wrapping, root-owned macOS Darwin `/tmp`, `/var`, `/etc` $\to$ `/private/*` prefix normalization, step-by-step `openat(O_RDONLY | O_DIRECTORY | O_NOFOLLOW)` traversal + logical `$PWD` symlink walk (zero `os.path.islink`), `65,536`-B streaming capped reads (`<= 64 MiB`), and atomic `0o600` writes with `threading.Lock()` + monotonic counter + `secrets.token_hex(8)` + 32-attempt `EEXIST` retry, `os.fsync(tmp_fd)`, pre-replace `os.fstat(tmp_fd).st_nlink == 1`, target `st_nlink <= 1` (`HARDLINK_FORBIDDEN`), `os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd)`, and `os.fsync(dfd)`.
- **Field-Complete Secondary Audit (`secondary_audit_payload`), Division-Free Cross-Multiplication & Bijective Bool Separation:** Bijective bool/non-bool leaf separation (`_BOOL_LEAF_KEYS`, `42` disjoint keys -> `NON_BOOL_IN_BOOL_FIELD`, `BOOL_IN_NON_BOOL_FIELD`, `BOOL_IN_LIST`) is enforced directly inside `validate_certificate_payload(..., full_replay=False)`, and field-complete strict-keyset `secondary_audit_payload` is enforced under both `full_replay=True` and `full_replay=False` across every algebraic witness in all 4 pillars using division-free cross-multiplication on untrusted parsed rationals (`yn * g * h == ty`, `yp * g == ty`, `up * 2 * eta == ...`, `qh * 6 * eta == ...`) so zero-denominator tampers (`g_grad="0"`, `h_half="0"`, `eta0="0"`) fail closed with typed `TectonicsReluError` (`0` raw `ZeroDivisionError`). Exported helper `discrete_outward_div_s2(d0, flux)` enforces strict `list` containers (`12×8` `int` matrix and `12`-element `int` vector; rejecting `bool`, `float`, `str`, subclasses, and wrong lengths with typed `TectonicsReluError`).
- **Strict Manual CLI Parser:** Zero flag abbreviations (`--st`/`--wr`/`--ch`/`--js` -> `UNKNOWN_FLAG`, `rc=2`), rejecting space- and equals-syntax flag-like/empty paths (`--write --json`, `--write=--json`, `--write ""` -> `rc=2`, `0` files created).

---

## 4. Verification Receipts & Frozen Manifest

All checks executed sequentially with `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1`:

- **Certificate Digests (`tectonics_relu_regions_certificate.json`, mode `0o600`):**
  - `file_sha256`: `3f9b7424def5c2dd0af5c397aeca64d3ced326f950a5e62dc24296bb235b5018` (`9,929` B)
  - `payload_sha256`: `0577e876dcea1937693a217bfe1aef6031869f9325832412ad70d3bd41562704`
  - `certificate_sha256`: `a0bca10efa3ca48c2c01c25c5b071cea05383ac660424d873b153cab7fbd21d2`
- **3-Mode Isolated Parity + Extended Modes (`-I -B`, `-I -O -B`, `-I -B -W error`, plus `-I -O -B -W error` & `PYTHONHASHSEED=42 -B` without `-I`):**
  - zero-arg: bit-identical `49375297346e30bd2a74658f53128d75a73a656439547990bd2c3e61b7976263` ×5.
  - `--standalone --json`: bit-identical `3f9b7424def5c2dd0af5c397aeca64d3ced326f950a5e62dc24296bb235b5018` (`== disk 0o600`) ×5.
  - `--check tectonics_relu_regions_certificate.json --json`: bit-identical `b3d2139edac7856bef6819b0a3d34a49a636c775aec5405bb168b60d1e34f27a` (`valid = true`) ×5.
  - `test_tectonics_relu_regions_r5.py`: **`10/10 OK` ×5** (`0` warnings, `0` AST floats, `0` bare asserts).
- **Exhaustive Zero-Denominator & Leaf Tamper Sweep:** **`1,606`** mutations across all **`504`** payload leaves (incl. `"0"` & `"1/0"`) on both `verify_certificate_dict(full_replay=False)` & `secondary_audit_payload` (**`3,212/3,212`**: `bypasses = 0`, `raw_excs = 0`, `0` `ZeroDivisionError`).
- **Live AST Mutation Testing (`mutate --max-mutants 0 --work-root . --add-cwd --timeout 60`):**
  - `tectonics_relu_regions_oracle.py`: **`63/63` (`100.0%`, `survived = 0`, `truncated = False`)**.
  - `tectonics_relu_regions_audit.py`: **`82/82` (`100.0%`, `survived = 0`, `truncated = False`)**.
  - Combined: **`145/145` (`100.0%`, `0` survivors)**.
- **Exhaustive `SWAP + SUBCOND_DEL` AST `BoolOp`:**
  - `tectonics_relu_regions_oracle.py`: **`69/69`** (`23` nodes, `survived = 0`, `timeouts = 0`).
  - `tectonics_relu_regions_audit.py`: **`42/42`** (`14` nodes, `survived = 0`, `timeouts = 0`).
  - Combined: **`111/111` (`100.0%`, `0` survivors)**.
- **Live 4-Surface Adversarial Fuzzer:** **`23/23` CLI + `18/18` `validate(full_replay=True)` + `18/18` `validate(full_replay=False)` + `18/18` `verify_dict(full_replay=False)` = `77/77` (`100.0%`, `bypasses = 0`, `crashes = 0`)**.
- **Live Concurrency & Kernel Race Stress:** `16T×10` distinct + `80T` barrier burst (`0o600`, `0` errs, `0` tmps), `renameat2(RENAME_EXCHANGE)` (`164,453` swaps, `0` leaks, `0` clobbers, `victim` intact, `0` tmps), `os.link`/`os.unlink` hardlink race (`230,350` flips, `0` unexpected errs, `0` tmps).
- **Static Hygiene (`audit-check . --strict-ancestors --safety-scan --scripts tectonics_relu_regions_audit.py test_tectonics_relu_regions_r5.py`):** **`PASS`** (`5` files, `2/2` scripts clean across all 3 isolated modes, `0` findings, `PYC = 0`).

### Frozen 5-File Manifest

| File | Lines | Bytes | Mode | SHA-256 |
|:---|---:|---:|:---:|:---|
| `tectonics_relu_regions_oracle.py` | 1,352 | 56,969 | `0644` | `a5100cf954fbb883f37110776d4e7597268f8d17d0b3796172ad8c6b3868a31b` |
| `tectonics_relu_regions_audit.py` | 930 | 44,344 | `0644` | `69125e943bb2ee5f03645636612e83926ba976e48b3ba32eab68c7ca31e86389` |
| `test_tectonics_relu_regions_r5.py` | 1,057 | 60,596 | `0644` | `a272c52786b54db01a00bc83abf1309e25b14f572522a75c974827778fb23fbd` |
| `tectonics_relu_regions_certificate.json` | 1 | 9,929 | `0600` | `3f9b7424def5c2dd0af5c397aeca64d3ced326f950a5e62dc24296bb235b5018` |
| `TECTONICS_RELU_REGIONS_REPORT.md` | *(this report)* | — | `0644` | *(verified by manifest receipt)* |
