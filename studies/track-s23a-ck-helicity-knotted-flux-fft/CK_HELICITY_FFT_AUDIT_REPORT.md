# Track S23a: Chandrasekhar–Kendall Force-Free States, Magnetic Helicity Conservation, Knotted Flux Tubes & Helical-Basis FFT/NTT Spectral Convolutions

- **Track:** `S23a` (`track-s23a-ck-helicity-knotted-flux-fft`)
- **Oracle Class:** `exact` (pure Python 3 standard library; `int`, `fractions.Fraction`, and Gaussian rationals $\mathbb{Q}[i]$ only; `0` floats on trust paths; `0` bare `assert`s; `0` external dependencies; `0` RNG; Zone-B hardened CLI and in-memory API)
- **Novelty Classification:** `N1` (new zero-float pure-$\mathbb{Z}/\mathbb{Q}/\mathbb{Q}[i]$ executable certificate engine combining combinatorial knotted flux-tube helicity & Borromean obstruction, cylindrical CK power-series & Pythagorean-quadruple $6\times 6$ helical projectors, 3D polynomial Chandrasekhar–Fermi virial integration, Waleffe helical triad conservation, and exact 3D $\mathbb{Q}[i]$-FFT + dual-prime NTT/CRT spectral convolution parity atop `N0` classical MHD/topology foundations)
- **Scope Honesty:** Certifies exact algebraic and combinatorial identities over $\mathbb{Z}$, $\mathbb{Q}$, and $\mathbb{Q}[i]$ on finite formal power-series truncations, finite Pythagorean wavevector shells, polynomial fields on $[-1, 1]^3$, and discrete periodic lattices ($\mathbb{Z}_4^3$, $\mathbb{Z}_8^3$); does **not** claim infinite-dimensional continuum PDE existence/regularity or compute non-Abelian Chern–Simons homotopy invariants inside this certificate (see explicit Law-5 Borromean disclosure below).

---

## 1. Theorem 1 — Knotted Flux-Tube Abelian $U(1)$ Helicity, Framing & Law-5 Borromean Obstruction

Using Moffatt's topological helicity decomposition $H = \sum_{i \ne j} \Phi_i \Phi_j \operatorname{Lk}_{ij} + \sum_i \Phi_i^2 (\operatorname{Tw}_i + \operatorname{Wr}_i)$ from exact signed crossing diagrams ($\operatorname{Lk}_{ij} = \frac{1}{2}\sum_{c \in (i,j)} \varepsilon(c) \in \mathbb{Z}$, $\operatorname{Wr}_i = \sum_{c \in (i,i)} \varepsilon(c) \in \mathbb{Z}$), with explicit Călugăreanu–White–Fuller Reidemeister I compensation ($\operatorname{Wr}_i \mapsto \operatorname{Wr}_i + k$, $\operatorname{Tw}_i \mapsto \operatorname{Tw}_i - k$):

| Topology Witness | Components / Crossings | Fluxes $\Phi$ | Pairwise $\operatorname{Lk}$ | Self-Linking $\operatorname{Tw}+\operatorname{Wr}$ | $H_{\mathrm{mutual}}$ | $H_{\mathrm{total}}$ | RI Framing Invariant |
|---|---:|---|---|---|---|---|---|
| **Unknot** (`RI +2/-2`) | `1 / 0` | `[3/2]` | `[[0]]` | `['0']` | `0` | `0` | `true` |
| **Positive Hopf Link** | `2 / 2` | `[3/2, 5/3]` | `[[0, 1], [1, 0]]` | `['0', '0']` | `5` | `5` | `true` |
| **Negative Hopf Link** | `2 / 2` | `[3/2, 5/3]` | `[[0, -1], [-1, 0]]` | `['0', '0']` | `-5` | `-5` | `true` |
| **`T(2,3)` Trefoil Cable** | `2 / 18` | `[1, 2]` | `[[0, 6], [6, 0]]` | `['6', '6']` | `24` | `54` | `true` |
| **`T(2,5)` Cinquefoil Cable** | `2 / 30` | `[1/2, 3/2]` | `[[0, 10], [10, 0]]` | `['10', '10']` | `15` | `40` | `true` |
| **`T(3,4)` Torus Cable** | `2 / 40` | `[1, 1/3]` | `[[0, 12], [12, 0]]` | `['12', '12']` | `8` | `64/3` | `true` |
| **Whitehead Link** | `2 / 5` | `[2, 3]` | `[[0, 0], [0, 0]]` | `['0', '0']` | `0` | `0` | `true` |
| **Borromean Rings (Law-5)** | `3 / 6` | `[2, 3, 5]` | `0` (all pairs) | `['0', '0', '0']` | `0` | `0` | `true` |

- **Exact Torus-Surface Framing Identity:** For every positive $(p,q)$ torus braid $(\sigma_1 \cdots \sigma_{p-1})^q$, $\operatorname{Wr} = (p-1)q$, $\operatorname{Tw}_{\mathrm{torus}} = q$, and parallel-cable linking $\operatorname{Lk}(C_1, C_2) = pq = \operatorname{Wr} + \operatorname{Tw}_{\mathrm{torus}}$ (`6`, `10`, `12`).
- **Exact Chiral Anti-Symmetry:** $H_{\mathrm{mutual}}(\text{Hopf}_+) = +5 = -H_{\mathrm{mutual}}(\text{Hopf}_-)$.
- **Explicit Law-5 Obstruction (Borromean Rings):** This certificate directly computes and proves from the 6-crossing Borromean diagram that all 3 pairwise Gauss linking numbers vanish ($\operatorname{Lk}_{01} = \operatorname{Lk}_{12} = \operatorname{Lk}_{20} = 0$), forcing Abelian $U(1)$ mutual helicity $H_{\mathrm{mutual}} = 0$ identically for all fluxes. Milnor's triple linking invariant $|\bar{\mu}(1,2,3)| = 1$ (Milnor 1954, `N0`) is cited classically as the higher non-Abelian Brunnian invariant that separates the Borromean rings from the 3-unlink (complementing non-Abelian $SU(2)_k$ Chern–Simons / Jones-polynomial link invariants).
- **Negative `must_fail` Control:** An odd inter-component crossing sum (`[(0, 1, +1)]`) fails closed with `ODD_CROSSING_SUM`.

---

## 2. Theorem 2 — Chandrasekhar–Kendall Force-Free Eigenstates, Woltjer–Arnold Bound & Chandrasekhar–Fermi Virial Obstruction

### 2A. Exact Cylindrical Chandrasekhar–Kendall Formal Power-Series Identity
On exact radial Bessel series $f(r) = \sum_{j=0}^{D} c_j r^{m+2j}$ with $c_0 = 1$, $c_j = -\frac{\gamma^2}{4 j (m+j)} c_{j-1}$, $\gamma^2 = \lambda^2 - k_z^2$, and $\mathbf{B} = \lambda \nabla \times (\psi \hat{\mathbf{z}}) + \nabla \times \nabla \times (\psi \hat{\mathbf{z}})$ ($\psi = f(r) e^{i(m\theta + k_z z)}$):

| Mode | $(\lambda, k_z, m)$ | $\gamma^2 = \lambda^2 - k_z^2$ | Terms $D$ | Verified Radial Order | $\nabla \cdot \mathbf{B} \equiv 0$ | $\nabla \times \mathbf{B} \equiv \lambda \mathbf{B}$ |
|---|---|---:|---:|---:|---|---|
| Axisymmetric spheromak | `(5, 3, 0)` | `16` | `8` | `r^0 .. r^13` | `true` | `true` |
| Helical kink | `(13/2, 5/2, 1)` | `36` | `8` | `r^0 .. r^14` | `true` | `true` |
| Negative-helicity quadrupole | `(-10, 6, 2)` | `64` | `7` | `r^0 .. r^13` | `true` | `true` |
| **`must_fail` broken dispersion** | `(5, 3, 0)`, $\gamma^2 = 17$ | `17 != 16` | `6` | `r^0 .. r^9` | `true` | **`false` (detected)** |

### 2B. Exact $\mathbb{T}^3$ Pythagorean-Norm Helical Projectors & Woltjer–Arnold Bound ($2E \ge \lambda_1 |H|$)
Across all **7** integer-norm Pythagorean wavevectors $\mathbf{k} \in \{(1,0,0), (0,1,0), (0,0,1), (1,2,2), (2,3,6), (1,4,8), (4,4,7)\}$ ($\|\mathbf{k}\| \in \{1, 1, 1, 3, 7, 9, 9\}$), the exact $\mathbb{Q}[i]^{3\times 3}$ projectors $P_0 = \hat{\mathbf{k}}\hat{\mathbf{k}}^\top$ and $P_\pm = \frac{1}{2}((I_3 - P_0) \pm i K_\times)$ certify:
- $P_0 + P_+ + P_- = I_3$, idempotence ($P_a^2 = P_a$), mutual orthogonality ($P_a P_b = 0$), Hermiticity ($P_a^\dagger = P_a$),
- Exact curl eigenrelation $i\mathbf{k} \times (P_\pm \mathbf{e}_j) = \pm \|\mathbf{k}\| (P_\pm \mathbf{e}_j)$,
- Exact $6\times 6$ real-symmetric embedding $M = \begin{pmatrix} A & -B \\ B & A \end{pmatrix}$ with $M^\top = M$ and $\operatorname{Tr}(M_\pm) = 2$.
- **Woltjer–Arnold Inequality ($2E \ge \lambda_1 |H|$) with Dual-Formula Helicity Parity** (direct Coulomb gauge $\sum \langle \hat{\mathbf{A}}, \hat{\mathbf{B}} \rangle \equiv \sum (\|\hat{\mathbf{B}}_+\|^2 - \|\hat{\mathbf{B}}_-\|^2)/\|\mathbf{k}\|$):
  - **Saturated Minimal Beltrami CK State** (`6` full modes on $\|\mathbf{k}\| = 1$, pure $+$-helicity): $E = 15/2$, $H = 15$, $\lambda_1 = 1$, slack $2E - \lambda_1 |H| = 0$ (`woltjer_arnold_saturated: true`).
  - **Mixed-Shell / Mixed-Helicity State** (`8` full modes across $\|\mathbf{k}\| \in \{1, 3, 7, 9\}$): $E = 1625/18$, $H = -317/27$, $\lambda_1 = 1$, strict rational slack $2E - \lambda_1 |H| = 4558/27 > 0$.

### 2C. Exact Chandrasekhar–Fermi (1953) Virial Obstruction
- Constructed an exact degree-3 polynomial vector potential $\mathbf{A} \in \mathbb{Q}[x,y,z]^3$ ($\mathbf{B} = \nabla \times \mathbf{A} \implies \nabla\cdot\mathbf{B} \equiv 0$) and certified over exact $\mathbb{Q}[x,y,z]$ that the pointwise Maxwell stress divergence identity $\partial_j (x_i T_{ij}) + \frac{1}{2}|\mathbf{B}|^2 - \mathbf{x}\cdot((\nabla\times\mathbf{B})\times\mathbf{B}) \equiv 0$ vanishes identically.
- Exact integration over $[-1, 1]^3$ confirms the Gauss virial identity identically in $\mathbb{Q}$: $\mathcal{M} = 149/9$, $\int_V \mathbf{x}\cdot(\mathbf{J}\times\mathbf{B}) = -428/9$, $\oint_{\partial V} (\mathbf{x}\cdot\mathbf{T})\cdot d\mathbf{S} = -577/9$, with $(-577/9) + (149/9) - (-428/9) = 0$.
- Scalar virial budget $2T + 3(\gamma - 1)U + \mathcal{M} + \Omega - \Sigma_S = 0$ certifies that a purely self-confined force-free magnetic field in $\mathbb{R}^3$ ($T = U = \Omega = \Sigma_S = 0$, $\mathcal{M} = 149/9 > 0$) has non-zero residual **`149/9`** (**obstructed**), whereas gravity-confined ($\Omega = -239/9$) and wall/coil-confined ($\Sigma_S = 149/9$) equilibria balance identically to `0`.

---

## 3. Theorem 3 — Exact Helical Triad Conservation & Zero-Float 3D FFT / Dual-Prime NTT+CRT Spectral Convolutions

### 3A. Exact Waleffe (1992) Triad-by-Triad Ideal Helicity Conservation ($\frac{dH_{\mathrm{triad}}}{dt} \equiv 0$)

| Pythagorean Triad ($\mathbf{k}+\mathbf{p}+\mathbf{q}=\mathbf{0}$) | Integer Norms | Non-Solenoidal $\mathbf{u}$? | Per-Leg Ideal $\frac{dH}{dt}$ | Ideal Sum | Resistive $\eta$ | Resistive $\frac{dH}{dt}$ (Direct == Helical) |
|---|---|---|---|---:|---:|---:|
| `(1,2,2) + (-1,2,-2) + (0,-4,0)` | `(3, 3, 4)` | `false` (solenoidal) | `[-40/3, 178/9, -58/9]` | **`0`** | `0` | `0` |
| `(6,2,3) + (-2,2,-1) + (-4,-4,-2)` | `(7, 3, 6)` | **`true` (compressible)** | `[-14746/21, 1178/3, 6500/21]` | **`0`** | `0` | `0` |
| `(3,0,0) + (0,4,0) + (-3,-4,0)` (`must_fail` $\eta > 0$) | `(3, 4, 5)` | `true` | `[0, -81, 81]` | **`0`** | `1/10` | **`-177/5` (breaks conservation)** |

### 3B. Exact 3D Radix-2 $\mathbb{Q}[i]$-FFT ($4^3$) & Dual-Prime NTT/CRT ($4^3$, $8^3$) Parity
- **Exact $4\times 4\times 4$ $\mathbb{Q}[i]$-FFT** ($\omega_4 = e^{2\pi i / 4} = i \in \mathbb{Q}[i]$): exact roundtrip (`IFFT3(FFT3(B)) == B`), exact Parseval ($64 \times 2688 = 172032$), and **`0` mismatches** across all `192` vector entries between $\mathrm{FFT}_3(\mathbf{u} \times \mathbf{B})$ and $\frac{1}{64}(\hat{\mathbf{u}} \circledast_\times \hat{\mathbf{B}})$.
- **Exact Dual-Prime NTT + Signed CRT** ($p_1 = 998244353$, $p_2 = 167772161$, primitive root $g = 3$, combined modulus $M = 167477612308856833$): bit-for-bit exact agreement across all **`192/192`** entries of $4^3$ 3D circular cross-product convolution against the direct $O(N^6)$ integer reference (`max_abs = 310`), plus exact $8^3$ (`512`-node) roundtrip, modular Parseval over $\mathbb{F}_{p_1}$, and direct spot-checks at `(0,0,0)` and `(3,5,7)`.

---

## 4. Law-4 Novelty Accounting (`N0` vs `N1`) & Verification Receipts

### `N0` Classical Foundations
- Gauss linking integral (1833), Călugăreanu–White–Fuller ribbon theorem (1959–1971), Moffatt topological magnetic helicity (1969), Berger–Field relative helicity (1984), Milnor triple linking invariant (1954).
- Chandrasekhar–Fermi virial theorem (1953), Chandrasekhar–Kendall force-free eigenstates (1957), Woltjer (1958) / Arnold (1974) helicity lower bound, Waleffe (1992) helical triad decomposition.
- Cooley–Tukey radix-2 FFT butterfly (1965), Pollard's finite-field Number-Theoretic Transform (1971), and classical Chinese Remainder Theorem (CRT).

### `N1` New Contributions in Track S23a
- Unified zero-float pure-$\mathbb{Z}/\mathbb{Q}/\mathbb{Q}[i]$ executable certificate engine (`ck_helicity_fft_oracle.py`) paired with a Zone-B hardened CLI performing full pure-$\mathbb{Q}$ deterministic replay and secondary algebraic cross-checking (`ck_helicity_fft_audit.py`), reserving zero-shared-code verification strictly for independent external auditors.
- Exact symbolic polynomial verification and $[-1, 1]^3$ Gauss integration of the Chandrasekhar–Fermi Maxwell stress divergence identity, exact Pythagorean-norm $(7, 3, 6)$ compressible-velocity triad conservation witness, and bit-exact 3D $\mathbb{Q}[i]$-FFT / dual-prime NTT+CRT cross-product spectral convolution parity.

### Verification & Hardening Receipts (`100.0% PASS`)
- **Isolated Interpreter Parity (`-I -B`, `-I -O -B`, `-I -B -W error`, plus `PYTHONHASHSEED=42 -I -B` and `-I -O -B -W error`):**
  - `--standalone --json` bit-identical **`b55631b1be71e8e46c5f6d153015c83b65bdf73bde7788933053e84b64aa6d31`** (`payload_sha256: 58ac1991e9e2a24b35cd3805bba1c42e1dad9518798fb36b469205708ddfcccb`, `certificate_sha256: 0ba996aaea3dfad160172eaae722e76fa385e77b1461b1ffe81c0053fd165df1`).
  - `--check ck_helicity_fft_certificate.json --json` bit-identical **`1eab8fb2726123a312b0f84c040aeebc3c23aaa08f04a928c1e7bbb276aaa57d`** (`valid: true`); `test_ck_helicity_fft_r5.py` **`13/13 OK`** (`0` warnings, `0` bare `assert`s).
- **Live `aletheia v2.0.0 mutate --max-mutants 0 --work-root . --add-cwd`:**
  - `ck_helicity_fft_oracle.py`: **`78/78` (`100.0%`, `survived=0`, `truncated=False`) KILLED**.
  - `ck_helicity_fft_audit.py`: **`43/43` (`100.0%`, `survived=0`, `truncated=False`) KILLED**.
  - **Combined:** **`121/121` (`100.0%`) KILLED**.
- **Exhaustive AST `BoolOp` (`and` $\leftrightarrow$ `or`, `timeout=30`) Sweep:**
  - `ck_helicity_fft_oracle.py`: **`24/24`** + `ck_helicity_fft_audit.py`: **`14/14`** = **`38/38` (`100.0%`, `survived=[]`) KILLED**.
- **Zone-B Adversarial Fuzzing:**
  - **`23/23` CLI + `18/18` In-Memory = `41/41` (`100.0%`, `bypasses=0`, `crashes=0`, `status: PASS`)**.
- **Zone-B I/O, TOCTOU & CLI Hardening:**
  - Atomic per-component `dir_fd` (`openat` with `O_RDONLY | O_DIRECTORY | O_NOFOLLOW`) directory traversal + leaf `O_NOFOLLOW | O_NONBLOCK` + `os.fstat(fd)` `S_ISREG` + capped streaming reads (`MAX_JSON_BYTES = 1,048,576`, safe on `/proc/kallsyms`).
  - Atomic write via `O_CREAT | O_EXCL | O_NOFOLLOW` temp file inside the pinned `dir_fd` + `os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd)` after verifying existing target is regular and `st_nlink == 1` (`HARDLINK_FORBIDDEN`, preserving original hardlinked bytes; live-tested across `>= 600` concurrent `renameat2(RENAME_EXCHANGE)` read+write swaps with `0` leaks and `0` clobbers).
  - Deleted-CWD fail-closed handling (`CWD_UNAVAILABLE`, `rc=2`), lone UTF-16 surrogate rejection on `Path`, `PWD`, and `argv` (`INVALID_UTF8_SURROGATE`, `rc=2`), exact `Path` type, `/dev/null` & FIFO zero-hang refusal, `chmod 000` clean `FILE_READ_ERROR`, strict zero-abbreviation CLI rejecting both space-separated (`--write --json`, `--check --json`) and `=`-syntax (`--write=--json`, `--check=--json`, `--write=`, `--check=`, `--wr=--json`) flag-like/empty paths (`rc=2`, `0` files created), `0` trust-path floats, and `aletheia v2.0.0 audit-check --strict-ancestors --safety-scan --scripts ck_helicity_fft_audit.py test_ck_helicity_fft_r5.py PASS` (`5` files, `2/2` parity scripts).
