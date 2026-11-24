# Track S36 (Portal 33) — Girih $\mathbb{Q}(\phi)$ & $E_8$ Elser–Sloane, Book of Kells Plait & Kirchhoff Matrix-Tree, and Victor Vasarely *Vega* Metric & *Plastic Alphabet*

- **Track ID:** `TRACK-S36-GIRIH-KELLS-VASARELY-OPERATORS`
- **Schema:** `aletheia.girih_kells_vasarely.certificate.v1`
- **Oracle Class:** `exact` (pure Python 3 standard library over exact $\mathbb{Z}$, $\mathbb{Q}$, and $\mathbb{Q}(\phi) = \mathbb{Q}[\phi]/(\phi^2 - \phi - 1)$; `0` external dependencies, `0` AST `float` literals or `float()` calls, `0` bare `assert`s, `0` `.isdigit()`, `0` mathematical RNG)
- **Novelty Classification (Law-4 Honesty):** **`N1`** unified cross-domain exact-operator certification suite built directly atop **`N0`** classical theorems (Lu & Steinhardt *Science* 2007; Elser & Sloane *J. Phys. A* 1987; Cromwell 1993 / Kirchhoff 1847 / Tait checkerboard knot determinant; Beltrami 1868 orthographic metric & Burnside's Lemma / Vasarely 1955 *Unité Plastique*). Zero historical or physical conflation is claimed across the three domains.

---

## 1. Pillar 1 — Girih Quasicrystalline Tiles Over $\mathbb{Q}(\phi)$ & Elser–Sloane $E_8 \to H_4$ Bridge (`N0` Classical Base)

Representing every tenth root of unity $e^{i k \cdot 36^\circ}$ ($k = 0,\dots,9$) exactly in $\frac{1}{2}\mathbb{Z}[\phi] \times (\mathbb{Z}[\phi]\cdot \sin 36^\circ)$ with $\sin^2 36^\circ = \frac{3 - \phi}{4}$, `certify_pillar1_girih_qphi_e8()` verifies unit step norm $\|e^{i k \cdot 36^\circ}\|^2 = 1$ for all $k \in \{0,\dots,9\}$, traces every unit-edge Girih polygon to exact closure, and computes each exact area over $\sin 36^\circ$ directly by the shoelace formula:

| Girih Tile | Edges | Interior Angles (deg) | Exact Area / $\sin 36^\circ$ in $\frac{1}{2}\mathbb{Z}[\phi]$ |
|---|---:|---|---|
| Rhombus | `4` | `72, 108, 72, 108` | $\phi$ (`0 + 1*phi`) |
| Pentagon | `5` | `108` × 5 | $\frac{1}{2} + \frac{3}{2}\phi$ (`1/2 + 3/2*phi`) |
| Bowtie | `6` | `72, 72, 216, 72, 72, 216` | $-1 + 2\phi = \sqrt{5}$ (`-1 + 2*phi`) |
| Elongated Hexagon | `6` | `72, 144, 144, 72, 144, 144` | $2 + \phi$ (`2 + 1*phi`) |
| Decagon | `10` | `144` × 10 | $5 + 5\phi = 5\phi^2$ (`5 + 5*phi`) |

### Certified Girih Identities, Inflation & Elser–Sloane $E_8 \to H_4$ Bridge
- **Additive dissections:** `Elongated Hexagon + Bowtie == 2 * Pentagon` ($1 + 3\phi$) and `Decagon == 2 * Elongated Hexagon + 2 * Pentagon` ($5 + 5\phi$).
- **Penrose ratios & $\phi^2$ inflation:** Exact `P3` thick/thin rhombus area ratio $= \phi$, exact `P2` kite/dart area ratio $= \phi$, and inflation matrix $M = \begin{pmatrix}2 & 1 \\ 1 & 1\end{pmatrix}$ with exact Bareiss $\det(M) = 1$, $\operatorname{tr}(M) = 3$, and characteristic polynomial $(\phi^2)^2 - 3\phi^2 + 1 = 0$.
- **Elser–Sloane (1987) $E_8 \to H_4/\mathbb{R}^4$ icosian cut-and-project bridge:** Generating all `120` unit icosians $2I$ ($\|u\|_\parallel^2 = 1$) and `120` scaled icosians $\phi \cdot 2I$ ($\|\phi u\|_\parallel^2 = \phi^2$, exact radius ratio $\phi$) gives `240` vectors in $\frac{1}{2}\mathbb{Z}[\phi]^4$. Under the exact integer icosian $E_8$ inner product $\langle u, v \rangle_{E_8} = 2 \cdot \operatorname{Re}(u\bar{v})$, where $\operatorname{Re}(a + b\phi) = a$ denotes the $\phi^0$ coordinate projection:
  - Every one of the `240` vectors has exact squared norm `2`;
  - The root inner-product histogram from any root is exact `{-2: 1, -1: 56, 0: 126, 1: 56, 2: 1}`;
  - Generic Weyl-chamber decomposition yields exactly `8` simple roots whose `8x8` Gram matrix has exact fraction-free Bareiss determinant **`det(G_8) = 1`** (uniquely identifying the even unimodular $E_8$ lattice and bridging $E_8$ directly to Girih $\mathbb{Q}(\phi)$).
  - **Naming clarification (exact quadratic form):** the *field trace* of $a + b\phi$ over $\mathbb{Q}$ is $\operatorname{Tr}_{\mathbb{Q}(\phi)/\mathbb{Q}}(a + b\phi) = 2a + b$ (its conjugate is $\phi' = 1 - \phi$, so $\phi + \phi' = 1$), **not** $2a$. The functional used by this oracle is the $2a$ **coordinate form** $2 \cdot \operatorname{Re}$, i.e. twice the $\phi^0$ projection of the Hermitian product $u\bar{v}$ — the standard icosian inner product. It is precisely this $2a$ coordinate form that returns *integer* inner products, all `240` exact squared norms `2`, the exact histogram `{-2: 1, -1: 56, 0: 126, 1: 56, 2: 1}`, and the unimodular Gram determinant $\det(G_8) = 1$ (the exact $E_8$ root system). The frozen certificate field label `qphi_e8_bridge` (which words the same map as `trace form tau(a+b*phi)=2a`) is pinned byte-for-byte in the payload; this note is the authoritative naming correction.

---

## 2. Pillar 2 — Book of Kells Knot/Plait Strands, Breakline Surgery & Kirchhoff Matrix-Tree (`N0` Classical Base)

### 2.1 Exact $m \times n$ Plait Strand-Count Theorem & Breakline Surgery
Using explicit directed half-edge permutation-cycle tracing on the $[0, 2m] \times [0, 2n]$ diagonal billiard lattice (`trace_celtic_plait_strands`), `certify_pillar2_kells_plait_kirchhoff()` verifies live across **all `144/144` pairs $(m, n) \in \{1,\dots,12\}^2$** that `strand_count(m, n) == gcd(m, n)` (`0` mismatches; `91` coprime single-strand knots; witness counts `2x3 -> 1`, `3x4 -> 1`, `4x6 -> 2`, `6x6 -> 6`).

Live breakline surgery (`"V"` vertical / `"H"` horizontal wall at an interior crossing) verifies the exact topological dichotomy:
- **Distinct-component crossing (`c -> c - 1`):** On `(2, 2)` (`2` strands) at `(1, 2)`, BOTH `"V"` and `"H"` merge `2 -> 1`; on `(4, 6)` at `(1, 2)`, `"V"` merges `2 -> 1`; on `(6, 6)` at `(1, 2)`, `"V"` merges `6 -> 5`.
- **Single-component self-crossing:** On `(2, 3)` (`1` strand) at `(1, 2)`, the orientation-preserving smoothing `"H"` splits `1 -> 2` (`c -> c + 1`), while the orientation-reversing smoothing `"V"` preserves `1 -> 1` (reversing one loop orientation).

### 2.2 Dual Tait Checker-Graph Kirchhoff Matrix-Tree Determinant
For any alternating planar link diagram, Kirchhoff's Matrix-Tree Theorem computes the spanning-tree count $\tau(G) = \det(L_0) = |V_K(-1)|$ (linking directly to the Jones polynomial determinant identity). Exact fraction-free Bareiss determinants certify:
- **Classic alternating knots:** Trefoil $3_1$: `3`; Figure-eight $4_1$: `5`; Cinquefoil $5_1$ `(2,5)`: `5`.
- **Alternating Celtic plaits (White $P_m \square P_n$ vs. planar-dual Black Tait graph — exact planar-duality parity $\tau(G_W) == \tau(G_B)$):**

| Celtic Plait | Crossings | White Vertices | Black Vertices | $\tau(G_W) = \det L_0(G_W)$ | $\tau(G_B) = \det L_0(G_B)$ |
|---|---:|---:|---:|---:|---:|
| `2x2` (Solomon link) | `4` | `4` | `2` | `4` | `4` |
| `2x3` ($7_4$ single knot) | `7` | `6` | `3` | `15` | `15` |
| `3x3` (`3`-strand link) | `12` | `9` | `5` | `192` | `192` |
| `3x4` (single Celtic knot) | `17` | `12` | `7` | `2415` | `2415` |

---

## 3. Pillar 3 — Victor Vasarely *Vega* Orthographic Beltrami Metric & *Plastic Alphabet* (`N0` Classical Base)

### 3.1 Exact Orthographic Beltrami First Fundamental Form
Projecting the upper unit hemisphere $z = \sqrt{1 - \rho^2}$ ($\rho^2 = x^2 + y^2 < 1$) orthographically onto the disk induces the exact first fundamental form $g_{ij} = \delta_{ij} + \frac{x_i x_j}{1 - \rho^2}$ with Gaussian curvature $K = +1$. Exact Bareiss determinants confirm $\det(g) = K^2(\rho) = \frac{1}{1 - \rho^2}$ with strictly monotonic radial bulging across all `5` exact Pythagorean rational points (including off-axis `(3/13, 4/13)` exercising nonzero $g_{12} = 1/12$):

| $(x, y)$ | $\rho$ | $\rho^2$ | Exact $K^2(\rho) = \det(g)$ | Truncated 4-dp | Hyperbolic Disk $\det(g_{\mathrm{hyp}})$ ($K = -1$) |
|---|---|---|---|---|---|
| `(0, 0)` | `0` | `0` | `1` | `1.0000` | `16` |
| `(3/13, 4/13)` | `5/13` | `25/169` | `169/144` | `1.1736` | `13051691536/429981696` (reduced `815730721/26873856`) |
| `(3/5, 0)` | `3/5` | `9/25` | `25/16` | `1.5625` | `6250000/65536` (reduced `390625/4096`) |
| `(4/5, 0)` | `4/5` | `16/25` | `25/9` | `2.7777` | `6250000/6561` |
| `(12/13, 0)` | `12/13` | `144/169` | `169/25` | `6.7600` | `13051691536/390625` |

*(Exact reduced rational `poincare_det_g_hyp` values are stored verbatim in the certificate.)*

### 3.2 *Plastic Alphabet* (*Unité Plastique*) $D_4$ Dihedral Burnside Orbit Grammar
Under explicit $D_4$ (order `8`) permutation action:
- **Single-tile form orbits:** `11` oriented form states (`3` $D_4$-invariant: circle, square, rhombus; `2` $D_2$-invariant: tilted ellipse, upright rectangle; `1` $C_2$-invariant: right-isosceles triangle) yield `sum(Fix(g)) / 8 = 48 / 8 = 6` distinct shape orbits, giving `6 * c * (c - 1)` distinct two-color `(bg != fg)` tiles (`c=2 -> 12`, `c=6 -> 180`, `c=12 -> 792`).
- **`2x2` quad-block orbits:** Exact Burnside count $(k^4 + 2k^3 + 3k^2 + 2k)/8$ matches brute-force canonical orbit enumeration identically for `k=2 -> 6`, `k=3 -> 21`, and `k=6 -> 231`.

---

## 4. Pillar 4 — Cross-Domain Exact-Operator Unification & Honest Law-5 Obstructions (`N1`)

All three domains are linked strictly by shared exact algebraic operators (NOT historical or physical analogy):
1. **Fraction-free Bareiss determinant:** Simultaneously certifies unimodular $E_8$ icosian Gram `det = 1`, Girih inflation `det = 1`, Kells dual Tait Kirchhoff spanning trees (`3, 5, 5, 4, 15, 192, 2415`), and Vasarely metric distortion `det(g) = 1/(1 - rho^2)` (`1 .. 169/25`).
2. **Exact $\mathbb{Q}(\phi)$ cut-and-project:** the Elser–Sloane icosian construction lifts the `240` $E_8$ roots into Girih $\frac{1}{2}\mathbb{Z}[\phi]^4$ exactly; the $2 \cdot \operatorname{Re}$ coordinate form ($2a$ projection — the field trace itself is $2a + b$, see the Pillar 1 naming clarification) reproduces the exact integer $E_8$ root system with unimodular $\det(G_8) = 1$.
3. **Explicit Law-5 obstructions:**
   - **Aperiodic vs. periodic:** Girih tilings require non-crystallographic $\mathbb{Z}[\phi]$ (5-fold symmetry is forbidden on 2D lattices), whereas Kells rectangular plaits live on periodic planar $\mathbb{Z}^2$ grids.
   - **Positive vs. negative curvature:** Vasarely *Vega* orthographic distortion arises from positive Gaussian curvature $K = +1$ on $S^2$, whereas hyperbolic Poincaré-disk shells (Escher *Circle Limit*) live on $K = -1$ with $\det(g_{\mathrm{hyp}}) = 16/(1-\rho^2)^4$.

---

## 5. Zone-B Verification Summary — Hardening, Honest POSIX Threat Boundary & Gate Receipts

The certificate carries exactly **four mathematical pillars** — `pillar1_girih_qphi_e8`, `pillar2_kells_plait_kirchhoff`, `pillar3_vasarely_vega_alphabet`, `pillar4_cross_domain_unification`. Zone-B hardening is the *separate* audit/CLI verification layer summarized in this section; it is deliberately **not** counted as a fifth mathematical pillar, and it contributes no mathematical claims to the payload.

### Atomic `dir_fd` I/O & Honest POSIX Threat Scope
- `girih_kells_vasarely_audit.py` pins every path traversal via per-component `openat(O_RDONLY | O_DIRECTORY | O_NOFOLLOW)` (`_step_dir_fd_chain`), normalizes verified root-owned macOS `/var`/`/tmp`/`/etc` system aliases to `/private/*` strictly on `sys.platform == "darwin"` (`_normalize_darwin_system_prefix`), checks logical `PWD` via `dir_fd` chain (zero `os.path.islink`), rejects deleted CWD, reads regular files via `O_RDONLY | O_NOFOLLOW | O_NONBLOCK` + `fstat` `S_ISREG` + streaming `65536`-byte loop capped by `max_bytes <= 64 MiB`, and writes atomically via `threading.Lock()` + monotonic sequence + `os.getpid()` + `secrets.token_hex(8)` + `32`-attempt `EEXIST` retry + `O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_NONBLOCK` (`0o600`) + `os.fsync(tmp_fd)` + pre-replace `os.fstat(tmp_fd).st_nlink == 1` + `os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd)` + `os.fsync(dfd)`. Target pre-write check accepts `st_nlink <= 1` so concurrent same-target unlinks are not misclassified.
- **Honest POSIX same-UID threat boundary:** Atomic `dir_fd` + `O_NOFOLLOW` + `0o600` temp mode + pre-replace `st_nlink == 1` closes symlink/ancestor/hardlink/TOCTOU/cross-user attacks and concurrent same-process races (`16T`, `80T`, `renameat2` leaf swaps, `os.link`/`os.unlink` flips). Under POSIX semantics, an adversarial process running under the **exact same UID** with write permission to the parent directory still holds discretionary kernel authority to replace or hardlink sibling entries *between* syscalls (`lstat` -> `replace`); protecting against a compromised same-UID actor requires kernel-level UID/namespace/directory-permission isolation outside user-space Python.

### Artifact Manifest (5 Files)

| File | Lines | Bytes | Mode | SHA-256 |
|---|---:|---:|---|---|
| `girih_kells_vasarely_oracle.py` | `1,494` | `76,110` | `0o644` | `fa0d32b47f922902fd09cc6b73913fec53ce3167448aa503a9a81ee62486492f` |
| `girih_kells_vasarely_audit.py` | `515` | `21,956` | `0o644` | `d685a8696e818f7127859a093d5a1704fba1c9d6605aac14a177f39199eaf559` |
| `test_girih_kells_vasarely_r5.py` | `979` | `57,055` | `0o644` | `1f016f493c01089d1d92793187e50d45fa4f4b05933dfc73ab3dffb53da98a64` |
| `girih_kells_vasarely_certificate.json` | `1` | `5,777` | `0o600` | `ed398ef31a53fe51ebccdccd5bffd3290a4787e139e32ae9a4722f383d37e7ed` |
| `GIRIH_KELLS_VASARELY_REPORT.md` | *(self)* | *(self)* | `0o644` | *(self; digest recorded in external verification receipt)* |

### Verified Gate Receipts (Post-Final-Edit)
- **Certificate digests:**
  - `payload_sha256`: `3c5aaa1c91f54f7ee796c554ad126562dae08718ecca97e812913ec0495e6b62`
  - `certificate_sha256`: `8e7453dc892b20e5dde8d75288126db2d3683bb08f12fd321f0e231ca7a53270`
  - On-disk `girih_kells_vasarely_certificate.json` (`0o600`, `5,777` B): `ed398ef31a53fe51ebccdccd5bffd3290a4787e139e32ae9a4722f383d37e7ed`
- **Isolated-Mode Parity (`-I -B`, `-I -O -B`, `-I -B -W error`, `-I -O -B -W error`, plus `PYTHONHASHSEED=42 -B` without `-I`):**
  - `--standalone --json`: `ed398ef31a53fe51ebccdccd5bffd3290a4787e139e32ae9a4722f383d37e7ed` ×5
  - `--check --json`: `43406dffab479f5f96f1c5394c63ddb7993f0678ab3a7d4159c2982b5d1fbc7d` ×5
  - `test_girih_kells_vasarely_r5.py`: `8/8 OK` ×5
- **Live `aletheia v2.0.0 mutate --max-mutants 0 --work-root . --add-cwd`:** `49/49` (`audit`) + `102/102` (`oracle`) = **`151/151` (`100.0%`, `survived=0`, `truncated=False`)**.
- **Exhaustive `SWAP + SUBCOND_DEL` AST `BoolOp`:** `39/39` (`audit`, `11` BoolOps) + `47/47` (`oracle`, `15` BoolOps) = **`86/86` (`100.0%`, `survived=[]`)**.
- **Zone-B 4-Surface Adversarial Fuzzer:** **`77/77` (`100.0%`, `bypasses=0, crashes=0`)** (`23/23` CLI + `18/18` `full_replay=True` + `18/18` `full_replay=False` + `18/18` direct `secondary_audit_payload`).
- **Live Concurrency & Kernel Races:** `16T` distinct + `16T` same-target + `80T` barrier burst (`0` errs, `0o600`, `0` leftover tmps); `renameat2(RENAME_EXCHANGE)` (`325,354` swaps, `0` escapes, `decoy_ok=True`, `0` raw exceptions, `0` tmps); hardlink race (`42,114` flips, `347` clean rejections, `0` raw exceptions, `0` tmps).
- **Hygiene:** `aletheia v2.0.0 audit-check . --strict-ancestors --safety-scan --scripts girih_kells_vasarely_audit.py test_girih_kells_vasarely_r5.py` **`PASS`** (`0` bare asserts, `0` floats/`float()`, `0` `.isdigit()`, `0` CRLF, `0` leaks, `0` `.pyc`, `0` safety/ancestor findings, `0` `/dev/null` writes).
