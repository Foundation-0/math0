# Track S35 — Geometric & Algorithmic Lineage Certificate (`Portal-32`)

**Track ID:** `TRACK-S35-GEOMETRIC-ALGORITHMIC-LINEAGE`  
**Schema Version:** `aletheia.track_s35.geometric_lineage.v1`  
**Methodology:** The Aletheia Method v2.0.0 (`OWN_TERMS_FIRST`, Law 1b, Law 2b, Law 4 `CS-13`, Law 5 Pure-$\mathbb{Z}/\mathbb{Q}$ Exact Operators)  
**Novelty Classification:** **`N1` (Verified Zero-Float Implementation & Replay-Certified Audit Suite)** over **`N0` (Classical / Published Mathematical Prior Art)** across all six historical pillars  
**Trust-Path Arithmetic:** Pure Python 3 standard library (`int`, `fractions.Fraction`, exact quadratic extension $\mathbb{Q}[\sqrt{3}]$); **`0`** IEEE-754 floats, **`0`** `float()` calls, **`0`** bare `assert`s, **`0`** `.isdigit()` calls, **`0`** external dependencies, **`0`** mathematical RNG calls.

---

## 1. `OWN_TERMS_FIRST` — Formal Mathematical Scope

Every claim in this track is defined strictly by an exact integer, rational ($\mathbb{Q}$), or quadratic-field ($\mathbb{Q}[\sqrt{3}]$) invariant independently reproducible from `geometric_lineage_oracle.py` without appealing to art-historical metaphor:

1. **Discrete Gauss–Bonnet & Star-Polyhedral Genus (Pillar 1 — Paolo Uccello, c. 1430):**
   - For an $M \times N$ quad-mesh torus $T_{M,N}$ ($V = MN$, $E = 2MN$, $F = MN$, $\chi = V - E + F = 0$), the Descartes angular defect $\delta_v = 2\pi - \sum_{f \ni v} \theta_{v,f}$ satisfies $\sum_{v \in V} \delta_v / (2\pi) = \chi = 0$, with positive curvature on the outer rim exactly cancelling negative curvature on the inner rim (`+4\pi` vs `-4\pi`, independent of $(M, N)$).
   - For the Kepler–Poinsot small stellated dodecahedron $\{5/2, 5\}$ ($12$ pentagrammic faces, $30$ edges of incidence $2$, $12$ vertices of degree $5$), $\chi = 12 - 30 + 12 = -6$, yielding orientable topological genus $g = (2 - \chi)/2 = 4$, contrasted against the convex Platonic dodecahedron $\{5, 3\}$ ($V = 20, E = 30, F = 12, \chi = 2, g = 0$).
2. **Exact Cayley–Menger Metric Determinant & Projective Cross-Ratio (Pillar 2 — Piero della Francesca, c. 1474–1482):**
   - For four points with squared pairwise distances $d_{ij}^2 \in \mathbb{Q}$, the $5 \times 5$ bordered Cayley–Menger determinant computed via exact fraction-free Bareiss elimination satisfies $288 V^2 = \det \mathrm{CM}(d_{ij}^2)$, vanishing identically on coplanar configurations ($\det = 0$) and turning strictly negative ($\det < 0$) on non-Euclidean/impossible distance metrics.
   - Under central perspective projection $P: (X, Y, Z) \mapsto (f X / Z, f Y / Z)$ ($Z > 0$, $f \in \mathbb{Q}_{>0}$), any four collinear 3D points $(A, B, C, D)$ project to four collinear 2D points $(A', B', C', D')$ with identically conserved projective cross-ratio $[A', B'; C', D'] - [A, B; C, D] = 0$, even when the ordinary affine ratio $(B - A)/(C - A)$ is strictly distorted.
3. **Exact Linear Algebra, $\mathbb{Q}[\sqrt{3}]$ Isometric Net SAT, & Minimal-Polynomial Root Bracketing (Pillar 3 — Albrecht Dürer, 1514 & 1525):**
   - The *Melencolia I* $4 \times 4$ magic matrix $D$ has all $16$ canonical sums equal to $34$, $\operatorname{tr}(D) = 34$, exact $\det(D) = 0$, non-vanishing top-left $3 \times 3$ minor $\det(D_{1:3,1:3}) = 136 \ne 0 \implies \operatorname{rank}(D) = 3$, and exact right nullspace generator $v = (1, -3, 3, -1)^\top$ ($D v = 0$).
   - The truncated triangular trapezohedron (cube $[0, 4]^3$ clipped by $x + y + z = 1$ and $x + y + z = 11$; $V = 12, E = 18, F = 8, \chi = 2$) unfolds along a $7$-edge spanning tree ($11$ cut edges) into an exact isometric $2$D net in $\mathbb{Q}[\sqrt{3}]^2$ whose $\binom{8}{2} = 28$ face pairs are certified strictly interior-disjoint via exact Separating Axis Theorem (SAT) over $\mathbb{Q}[\sqrt{3}]$.
   - Dürer's 1525 fixed-compass pentagon construction yields $u_{\mathrm{D\ddot{u}rer}} = 4 \cos \theta_{\mathrm{D\ddot{u}rer}}$, the unique negative real root of $P(u) = u^4 - 12 u^3 + 56 u^2 - 48 u - 176$. Since $P'(u) = 4u^3 - 36u^2 + 112u - 48 < 0$ for all $u \le 0$, $P(-13/10) = 102601/10000 > 0$, and $P(-5/4) = -671/256 < 0$, we prove $u_{\mathrm{D\ddot{u}rer}} \in (-13/10, -5/4)$ strictly below $4\cos 108^\circ = 1 - \sqrt{5} > -5/4$ (equivalently $(9/4)^2 = 81/16 > 5$), with exact polynomial division remainder $P(u) \equiv -8u - 16 \pmod{u^2 - 2u - 4}$.
4. **Integer Dissection Defect & Guillotine Obstruction (Pillar 4 — Piet Mondrian / `OEIS A276523`):**
   - For $n \in \{3, \dots, 10\}$, exact non-congruent integer-rectangle tilings of $[0, n]^2$ certify upper bounds $M(n) \le [2, 4, 4, 5, 5, 6, 6, 8]$; live exhaustive pure-$\mathbb{Z}$ bitmask branch-and-bound certifies impossibility below $M(3) = 2$, $M(4) = 4$, and $M(5) = 4$; explicit witnesses at $n \in \{7, 8, 10\}$ separate guillotine-cuttable optimal tilings from non-guillotine pinwheel optima.
5. **Discrete Integer Structure Tensor & Exact $\mathbb{Q}[\sqrt{3}]$ Moiré Aliasing (Pillar 5 — Bridget Riley):**
   - On periodic discrete intensity grids, the exact integer structure tensor $J = \sum (\nabla I)(\nabla I)^\top$ satisfies $J_{xy} = 0$ identically on rectilinear stripes and checkerboard controls, whereas cross-mortar $3 \times 3$ Sobel filtering on a staggered Café-Wall grating ($J_{xy} = -1024$, $\tan 2\theta = -1$) and central-difference filtering on a pinched shear grating ($J_{xy} = -512$, $\tan 2\theta = -2$) yield strictly non-zero off-diagonal shear and strictly elevated coherence numerator $(J_{xx} - J_{yy})^2 + 4 J_{xy}^2 > (J_{xx} - J_{yy})^2$.
   - Over $\mathbb{Z}/12\mathbb{Z}$ in exact $\mathbb{Q}[\sqrt{3}]$, multiplying two near-Nyquist cosine gratings $f_1 = 5, f_2 = 4$ (Nyquist $N/2 = 6$) obeys $2 c_5(n) c_4(n) = c_1(n) + c_3(n)$ identically, with exact low-frequency beat $|f_1 - f_2| = 1$ and exact sub-Nyquist fold-back $12 - (5 + 4) = 3$, and exact zero projection on all other modes $k \in \{0, 2, 4, 5, 6\}$.
6. **Exact Burnside Orbit Enumeration & $\Theta(n^2)$ Algorithmic Specification Compression (Pillar 6 — Sol LeWitt, 1974):**
   - Live exhaustive traversal over all $2^{12} = 4{,}096$ edge-subgraphs of the $3$-cube $Q_3$ certifies exactly $2{,}366$ connected $3$D-spanning proper subgraphs, decomposing into $122$ orbits under the proper rotation group $O$ ($|O| = 24$, Burnside fix sum $2{,}928 = 122 \times 24$) and $77$ orbits under the full octahedral group $O_h$ ($|O_h| = 48$, Burnside fix sum $3{,}696 = 77 \times 48$), yielding $45$ chiral enantiomorphic pairs and $32$ achiral forms ($2 \cdot 45 + 32 = 122$, $45 + 32 = 77$).
   - *Wall Drawing #118* expands an $O(1)$ specification ($64$ fixed rule bits) into $\binom{n}{2} = \Theta(n^2)$ segments ($1{,}225$ segments at $n = 50$, exact doubling ratio $\binom{100}{2}/\binom{50}{2} = 198/49$), and *Wall Drawing #260* enumerates all $2^4 - 1 = 15$ non-empty subsets of four line directions.

---

## 2. Law-2b Transformational Steelman & Anti-Numerology Boundary (`CS-13`)

A naive narrative linking Renaissance painting, De Stijl, Op Art, and Conceptual Art invites two well-known failure modes: (i) **retroactive mathematical projection** (attributing modern theorems to historical artisans who worked via workshop rules) and (ii) **aesthetic numerology** (claiming golden-section $\phi$ proportions in Piero, Dürer, or Mondrian without exact invariance).

Under **Law 2b** and **`CS-13`**, Track S35 explicitly strips aesthetic romanticism and restricts every claim to falsifiable mathematical structure:

- **What holds strictly:** Each artwork/treatise instantiates or directly motivates a concrete, machine-checkable discrete/algebraic operator: piecewise-flat curvature cancellation on quad tori (`P1`), projective cross-ratio invariance vs. affine foreshortening (`P2`), exact rank-deficiency, non-overlapping polyhedral unfolding, and algebraic non-exactness of a fixed-compass pentagon (`P3`), combinatorial integer dissection optimization (`P4`), spatial-gradient orientation coupling and discrete Nyquist folding (`P5`), and finite group action orbit counting plus constant-program quadratic output expansion (`P6`).
- **What is explicitly rejected:**
  - **No golden-ratio mystique:** In `P3`, Dürer's 1525 fixed-compass pentagon is proved *not* to achieve the exact golden-ratio angle $108^\circ$ ($\cos 108^\circ = (1 - \sqrt{5})/4$), and `P4` treats Mondrian's name purely as the established combinatorial label for the integer dissection sequence `OEIS A276523` (not as a claim that Mondrian solved `A276523` on canvas).
  - **No over-claiming perceptual neuroscience:** In `P5`, the Café-Wall illusion's biological retina/V1 mechanism is *not* claimed to be solved by a $3 \times 3$ Sobel filter; rather, `P5` establishes the exact mathematical distinction between $1$-pixel central differences (which yield $J_{xy} = 0$ on $1$-pixel mortar) and finite-aperture $3 \times 3$ cross-mortar filters (which extract non-zero oriented shear $J_{xy} = -1024$).
  - **Honest complexity-theory boundary:** `P6`'s $O(1)$-program $\to \Theta(n^2)$-output expansion connects directly to MDL/Kolmogorov complexity formalism without conflating LeWitt's wall-drawing instructions with Turing-universal minimum description length.

---

## 3. Law-4 Prior-Art & Novelty Ledger (`N0` / `N1`)

| Component | Classification | Established Prior Art & Attribution |
|---|---|---|
| `P1` Mazzocchio torus & $\{5/2, 5\}$ genus | **`N0`** | Paolo Uccello (c. 1430); R. Descartes (1630) angular defect; J. Kepler (1619) & L. Poinsot (1809) star polyhedra; Gauss–Bonnet theorem. |
| `P2` Cayley–Menger volume & cross-ratio | **`N0`** | Piero della Francesca (*De prospectiva pingendi*, *Libellus*, c. 1474–1482); Pappus / Desargues projective cross-ratio; A. Cayley (1841); K. Menger (1928). |
| `P3` Magic square, unfolding net, 1525 pentagon | **`N0`** | A. Dürer (*Melencolia I*, 1514; *Underweysung der Messung*, 1525); M. Ghomi (2014) & E. Demaine et al. (2026) Dürer unfolding conjecture; standard algebraic analysis of Dürer's approximate pentagon ($\approx 108.366^\circ$ base / $107.7^\circ$ upper angles). |
| `P4` Mondrian art problem (`OEIS A276523`) | **`N0`** | C. O'Kuhn (2016) / `OEIS A276523`; M. Dębski, J. Grytczuk, M. Śleszyńska-Nowak et al. asymptotic bounds and non-guillotine dissections. |
| `P5` Café-Wall structure tensor & Moiré | **`N0`** | Bridget Riley Op Art (1960s); R. L. Gregory & P. Heard (1979) Café Wall illusion; J. Bigün & G. H. Granlund (1987) structure tensor; discrete cosine aliasing. |
| `P6` *Incomplete Open Cubes* & Wall Drawings | **`N0`** | Sol LeWitt (1974) *Incomplete Open Cubes* (and R. K. Guy / Burnside $O$ vs $O_h$ census: $122$ / $77$); W. Burnside (1897); A. N. Kolmogorov (1965) / MDL. |
| Unified zero-float $\mathbb{Z}/\mathbb{Q}/\mathbb{Q}[\sqrt{3}]$ oracle + Zone-B fail-closed certificate auditor | **`N1`** | Original reproducible implementation in `geometric_lineage_oracle.py`, `geometric_lineage_audit.py`, and `test_geometric_lineage_r5.py` with `100.0%` mutation kill rate (`185/185`), `100.0%` AST `BoolOp` kill rate (`63/63`), and `77/77` 4-surface Zone-B adversarial fuzz pass. |

---

## 4. Exact Certified Quantitative Results

All values below are extracted verbatim from `geometric_lineage_certificate.json` (`payload_sha256: c89c673cb99696bd007ae9fd8a8afda219913157105d7bd487e707efca777885`, `certificate_sha256: 4cf29d1fd377042afa9d578849e53a1f89a65186b7c66abd74a0b5b35a95474c`).

### 4.1 Pillar 1 — Uccello: Mazzocchio Quad Tori & Small Stellated Dodecahedron

| Mesh / Polyhedron | $V$ | $E$ | $F$ | $\chi$ | Genus $g$ | Outer / Inner Defect ($\div \pi$) | $\sum \delta_v / (2\pi)$ |
|---|---:|---:|---:|---:|---:|---|---|
| Mazzocchio $4 \times 4$ (also 3D planar-quad embedded) | `16` | `32` | `16` | `0` | `1` | `+1/2` / `-1/2` (totals `+4` / `-4`) | `0` |
| Mazzocchio $4 \times 8$ | `32` | `64` | `32` | `0` | `1` | `+1/4` / `-1/4` (totals `+4` / `-4`) | `0` |
| Mazzocchio $8 \times 12$ | `96` | `192` | `96` | `0` | `1` | `+1/12` / `-1/12` (totals `+4` / `-4`) | `0` |
| Mazzocchio $16 \times 12$ | `192` | `384` | `192` | `0` | `1` | `+1/24` / `-1/24` (totals `+4` / `-4`) | `0` |
| Small Stellated Dodecahedron $\{5/2, 5\}$ | `12` | `30` | `12` | `-6` | `4` | Every edge incidence `2`, every vertex degree `5` | — |
| Platonic Dodecahedron $\{5, 3\}$ (contrast) | `20` | `30` | `12` | `2` | `0` | Convex sphere baseline | — |

### 4.2 Pillar 2 — Piero della Francesca: Bareiss Cayley–Menger & Projective Cross-Ratio

| Test Case | Exact Bareiss $\det \mathrm{CM}$ | Exact $V^2 = \det / 288$ | Status |
|---|---:|---:|---|
| Unit regular tetrahedron ($d_{ij}^2 = 1$) | `4` | `1/72` | Verified |
| Orthogonal $(3, 4, 5)$ tetrahedron | `28800` | `100` | Verified ($V = 10$) |
| General rational tetrahedron | `5000` | `625/36` | Exact match with triple product |
| Coplanar 4-point negative control | `0` | `0` | Degenerate ($\det = 0$) |
| Metric-inequality violation control | `-19400` | `< 0` | Non-Euclidean ($\det < 0$) |

| Perspective Line Case | 3D Affine Ratio | 2D Projected Affine Ratio | 3D Cross-Ratio | 2D Cross-Ratio | Residual |
|---|---:|---:|---:|---:|---:|
| `oblique_foreshortened_line_1` | `3` | `2` (broken) | `9/7` | `9/7` | `0` |
| `steep_depth_line_2` | `4` | `2` (broken) | `6/5` | `6/5` | `0` |

### 4.3 Pillar 3 — Albrecht Dürer: *Melencolia I*, $\mathbb{Q}[\sqrt{3}]$ Net, & 1525 Pentagon Error

- **Magic Square $D$ (1514):** All `16` sums `= 34`, `trace = 34`, `year_encoding = [15, 14]`, `det = 0`, top-left $3 \times 3$ minor `= 136`, exact `rank = 3`, right nullspace basis `v = [1, -3, 3, -1]` with `D * v = [0, 0, 0, 0]`.
- **Truncated Triangular Trapezohedron Net:** $V = 12, E = 18, F = 8, \chi = 2$; `7` hinge edges form a valid spanning tree (`11` cut edges); all `8` faces exact isometric in $\mathbb{Q}[\sqrt{3}]^2$; all `28/28` face pairs certified interior-disjoint via exact SAT over $\mathbb{Q}[\sqrt{3}]$.
- **1525 Fixed-Compass Pentagon Exact Error Proof:**
  - Minimal polynomial of $u_{\mathrm{D\ddot{u}rer}} = 4\cos \theta_{\mathrm{D\ddot{u}rer}}$: $P(u) = u^4 - 12u^3 + 56u^2 - 48u - 176$ (`[1, -12, 56, -48, -176]`).
  - Derivative $P'(u) = 4u^3 - 36u^2 + 112u - 48 < 0$ strictly on $(-\infty, 0]$.
  - Exact evaluations: $P(-13/10) = 102601/10000 > 0$, $P(-5/4) = -671/256 < 0 \implies u_{\mathrm{D\ddot{u}rer}} \in (-13/10, -5/4)$.
  - Strict separation from regular $108^\circ$: $4\cos 108^\circ = 1 - \sqrt{5} > -5/4 \iff 9/4 > \sqrt{5} \iff 81/16 > 5$ (exact!).
  - Exact polynomial division: $P(u) = (u^2 - 2u - 4)(u^2 - 10u + 40) + (-8u - 16)$.

### 4.4 Pillar 4 — Piet Mondrian (`OEIS A276523`)

| $n$ | Optimal Defect $M(n)$ | Witness Tile Count | Guillotine? | Exhaustive B&B Lower Bound |
|---:|---:|---:|:---:|---|
| `3` | `2` | `3` | Yes | `M(3) >= 2` proved (`<= 1` impossible, `28` B&B nodes) |
| `4` | `4` | `4` | Yes | `M(4) >= 4` proved (`<= 3` impossible, `700` B&B nodes) |
| `5` | `4` | `3` | Yes | `M(5) >= 4` proved (`<= 3` impossible, `2,308` B&B nodes) |
| `6` | `5` | `5` | Yes | Exact upper-bound witness matching `A276523` |
| `7` | `5` | `5` (guillotine) / `8` (non-guillotine) | Both (`5`) | Guillotine & non-guillotine optima both certified |
| `8` | `6` | `6` (guillotine) / `7` (non-guillotine) | Both (`6`) | Guillotine & non-guillotine optima both certified |
| `9` | `6` | `3` | Yes | Exact upper-bound witness matching `A276523` |
| `10` | `8` | `6` | **No** (pinwheel) | Non-guillotine pinwheel optimum certified |

### 4.5 Pillar 5 — Bridget Riley: Discrete Structure Tensor & $\mathbb{Q}[\sqrt{3}]$ Moiré

| Pattern Case | Operator | $J_{xx}$ | $J_{xy}$ | $J_{yy}$ | $\tan(2\theta)$ | $(J_{xx}-J_{yy})^2$ | $(J_{xx}-J_{yy})^2 + 4J_{xy}^2$ | Shear Tilt? |
|---|---|---:|---:|---:|---:|---:|---:|:---:|
| `rectilinear_stripes_central` | `central_diff` | `1024` | `0` | `0` | `0` | `1048576` | `1048576` | No |
| `rectilinear_checker_sobel` | `sobel_3x3` | `4096` | `0` | `4096` | `0` | `0` | `0` | No |
| `riley_cafewall_sobel` | `sobel_3x3` | `3072` | `-1024` | `1024` | `-1` | `4194304` | `8388608` | **Yes** |
| `riley_pinched_shear_central` | `central_diff` | `1024` | `-512` | `512` | `-2` | `262144` | `1310720` | **Yes** |

- **Exact $\mathbb{Z}/12\mathbb{Z}$ Moiré ($\mathbb{Q}[\sqrt{3}]$):** $f_1 = 5, f_2 = 4$, Nyquist $= 6$, exact mode projections `{0: "0", 1: "1", 2: "0", 3: "1", 4: "0", 5: "0", 6: "0"}` — proving exact beat $|5 - 4| = 1$ and exact sub-Nyquist fold-back $12 - (5 + 4) = 3$.

### 4.6 Pillar 6 — Sol LeWitt: *Incomplete Open Cubes* & Wall Drawings

- **Live $2^{12} = 4{,}096$ $Q_3$ Subgraph Search:** `2,366` connected 3D-spanning proper subgraphs.
  - Under proper rotations $O$ (`|O| = 24`): **`122` orbits**, Burnside fix sum **`2,928`** (`2928 / 24 = 122`), edge distribution `{3:3, 4:5, 5:14, 6:24, 7:32, 8:25, 9:13, 10:5, 11:1}`.
  - Under full isometries $O_h$ (`|O_h| = 48`): **`77` orbits**, Burnside fix sum **`3,696`** (`3696 / 48 = 77`), edge distribution `{3:2, 4:3, 5:9, 6:14, 7:19, 8:16, 9:9, 10:4, 11:1}`.
  - Chirality decomposition: **`45` chiral enantiomorphic pairs** + **`32` achiral forms** (`2 * 45 + 32 = 122`, `45 + 32 = 77`).
- ***Wall Drawing #118* ($\Theta(n^2)$ Compression over fixed `64`-bit rule):**
  - $n = 10 \to 45$ segments (`45/64 = 0.7031`), $n = 25 \to 300$ (`75/16 = 4.6875`), $n = 50 \to 1{,}225$ (`1225/64 = 19.1406`), $n = 100 \to 4{,}950$ (`2475/32 = 77.3438`); exact doubling ratio $\binom{100}{2}/\binom{50}{2} = 198/49$.
- ***Wall Drawing #260*:** `2^4 - 1 = 15` non-empty subsets of four line directions.

---

## 5. Zone-B Security Architecture & Honest Threat Boundary

`geometric_lineage_audit.py` implements Zone-B fail-closed hardening:

- **Atomic `dir_fd` Traversal & Reader (`read_regular_bytes_capped`):**
  - Rejects non-concrete `Path` subclasses, NUL bytes, lone UTF-16 surrogates, root/`.`/`..` leaves, symlinks (leaf and any intermediate ancestor via `O_DIRECTORY | O_NOFOLLOW` `dir_fd` chain), FIFOs/devices (`O_NONBLOCK` + `fstat` `S_ISREG`), and deleted/symlinked `PWD`/`CWD` (`CWD_UNAVAILABLE` / `SYMLINK_ANCESTOR_FORBIDDEN`, zero `os.path.islink`).
  - Streams in `65,536`-byte chunks enforcing exact-int `max_bytes <= 64 MiB` (`1 << 100` raises typed `INT_OUT_OF_RANGE`).
- **Atomic Writer (`write_regular_bytes_safe`):**
  - Creates temporary files in the opened parent `dir_fd` with mode `0o600`, `O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_NONBLOCK`, `threading.Lock()` + `secrets.token_hex(8)` + bounded `64`-attempt `EEXIST` retry, `os.fsync(tmp_fd)`, pre-replace `os.fstat(tmp_fd).st_nlink == 1`, target `st_nlink <= 1` check, `os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd)`, and parent directory `os.fsync(dfd)`.
- **Honest Same-UID POSIX Threat Boundary:**
  - Under POSIX, there is no atomic kernel primitive combining `renameat` with a simultaneous check on target or source `st_nlink`. A concurrent **same-UID** attacker with write access to the target directory can create a hardlink in the narrow window between `lstat`/`fstat` and `os.replace`. Even in that same-UID race, `os.replace` atomically swaps the directory entry to the freshly written temp inode rather than mutating an existing hardlinked inode in place, preventing in-place clobber of linked sentinels. Full immunity against a malicious same-UID writer requires OS-level directory isolation (`0700` owned directory or distinct UIDs).
- **Strict JSON, Rational & CLI Trust Boundary:**
  - Strict ASCII-only integer/rational parsers reject `"-0"`, `"007"`, Unicode digits, non-canonical fractions, duplicate JSON keys (including `\u0061` escapes), float literals, `NaN`/`Infinity`, integers exceeding `1,000` digits (including `10**4300` in both `parse_strict_json_text` and `canonical_json_bytes`), and cyclic/deep containers (`depth > 64`).
  - `format_decimal` suppresses signed negative zero (`"-0.000000"` normalized to `"0.000000"`).
  - CLI rejects flag-like path arguments in both space (`--write --json`, `--check --json`) and equals (`--write=--json`, `--check=--json`) forms without creating stray files.
- **Honest Verification Boundary (`--check`):**
  - `verify_certificate_dict(..., full_replay=True)` validates canonical ASCII+LF framing, constant-time `hmac.compare_digest` over both `payload_sha256` and `certificate_sha256`, schema-safe exact-int/bool/rational `secondary_audit_payload` (enforcing iterative JSON-tree validation, exact `frozenset` keysets across all `51` dicts, exact list lengths across all `55` lists, and bijective leaf verification across all `475` leaves even when `full_replay=False` or called directly), AND deterministic full oracle replay via `geometric_lineage_oracle.build_payload()`. It is **deterministic replay + bijective secondary algebraic cross-check**, not a zero-shared-code independent oracle.

---

## 6. Verification Receipts & Frozen Artifact Manifest

All verification gates were executed strictly sequentially (`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1`) after the final code edit:

| Gate | Scope | Exact Result |
|---|---|---|
| **Unit & Adversarial Regression Suite** | `test_geometric_lineage_r5.py` (8 test methods, incl. exhaustive `51`-dict / `55`-list / `475`-leaf / container-to-scalar sweep) | **`8/8` PASS** (`~1.16s`, `0` bare asserts, `0` AST floats, `0` `float()` calls, `0` `.isdigit()`, `0` device-path writes) |
| **Deterministic Multi-Mode Parity** | `-I -B`, `-I -O -B`, `-I -B -W error`, `-I -O -B -W error`, `PYTHONHASHSEED=42 -B` (without `-I`) | **`5/5` bit-identical** (`6a260e45323163a341546502a785c345bf64183f377a2b726ad8776c818ef0b7`), `--check` OK ×5, regression suite OK ×5 |
| **Refusal-Site Mutation Suite (Exhaustive)** | `geometric_lineage_oracle.py` | **`39/39` (`100.0%`, `survived=0`, `truncated=False`)** |
| **Refusal-Site Mutation Suite (Exhaustive)** | `geometric_lineage_audit.py` | **`146/146` (`100.0%`, `survived=0`, `truncated=False`)** |
| **Exhaustive `SWAP + SUBCOND_DEL` AST `BoolOp`** | `geometric_lineage_oracle.py` + `geometric_lineage_audit.py` | **`30/30` + `33/33` = `63/63` (`100.0%`, `0` survivors)** |
| **4-Surface Zone-B Adversarial Fuzzing** | CLI (`23`) + `full_replay=True` (`18`) + `full_replay=False` (`18`) + direct `secondary_audit_payload` (`18`) | **`77/77` (`100.0%`, `bypasses=0`, `crashes=0`)** |
| **Concurrency & Kernel Races** | `16T` distinct + `16T` same + `80T` burst + `600` `renameat2(RENAME_EXCHANGE)` + `600` `os.link`/`os.unlink` hardlink race | **`0` errors, `0` leaks, `0` clobbers, `0` leftover `.tmp` files** |
| **Static Hygiene & Path-Safety Gate** | Strict ancestor permissions, safety scan, zero-float / zero-assert / zero-CRLF / zero-leak verification | **`PASS`** (`0` host-path leaks, `0` private-repo refs, `0` CRLF, `0` `.pyc`) |

### Frozen Code & Certificate Manifest

| File | Lines | Bytes | Mode | SHA-256 |
|---|---:|---:|---:|---|
| `geometric_lineage_oracle.py` | `1329` | `55758` | `0o644` | `68c7bfd5f06d08644d477230ac22f3d525d5b59fe18d2acc285bb461e998c39c` |
| `geometric_lineage_audit.py` | `950` | `45264` | `0o644` | `16df1b40825ed7cdda18454cc9caf4dfe8117255f932465fcab34bd242465f68` |
| `test_geometric_lineage_r5.py` | `929` | `51629` | `0o644` | `019c66cdbe26a5c70540ba6a4d3f845fce60bde0e639896485d1d0a0fd685ad5` |
| `geometric_lineage_certificate.json` | `1` | `8370` | `0o600` | `6a260e45323163a341546502a785c345bf64183f377a2b726ad8776c818ef0b7` |
| `GEOMETRIC_LINEAGE_REPORT.md` | (this report) | — | `0o644` | See directory manifest on freeze |
