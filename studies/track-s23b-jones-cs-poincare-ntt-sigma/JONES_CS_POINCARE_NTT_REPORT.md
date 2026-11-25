# Exact $SU(2)_k$ Chern–Simons Levels, Jones Polynomials, Poincaré-Disk $SL(2,\mathbb{Z})$ Modularity & Exact NTT+CRT Divisor-$\sigma_k$ Convolutions

**Study:** `track-s23b-jones-cs-poincare-ntt-sigma` | **Oracle Class:** `exact` (pure Python 3 stdlib $\mathbb{Z}/\mathbb{Q}/\mathbb{Q}[\zeta]$, zero floats, zero bare `assert`s, zero RNG) | **Novelty:** `N0`/`N1` (classical theorems of Jones 1985, Kauffman 1987, Witten 1989, Kac–Peterson 1984, Verlinde 1988, Rosso–Jones 1993, Ramanujan 1916, and Cooley–Tukey 1965 / Pollard 1971 unified into a single self-verifying, zero-float, cyclotomic + NTT+CRT standard-library certificate engine with explicit Borromean Abelian-vs-non-Abelian separation)

---

## 1. Executive Summary (Own Terms First)

This study strips topological quantum field theory, hyperbolic modular tilings, and multiplicative divisor convolutions down to their exact algebraic operators over $\mathbb{Z}$, $\mathbb{Q}$, cyclotomic fields $\mathbb{Q}(\zeta_N) = \mathbb{Q}[x]/(\Phi_N(x))$, and multi-prime finite-field Number-Theoretic Transforms (NTT + CRT), certifying three interconnected theorems without a single floating-point operation:

1. **Theorem 1 — Exact PD-Code Kauffman Bracket, Jones Polynomials, Chern–Simons Level-$k$ Evaluations & Borromean Obstruction:** From oriented planar diagram (PD) codes alone, we compute the exact Kauffman bracket state sum $\langle D \rangle(A) \in \mathbb{Z}[A, A^{-1}]$ and writhe-normalized Jones polynomial $V_L(t) = (-A^3)^{-w(D)} \langle D \rangle(A)\big|_{A = t^{-1/4}} \in \mathbb{Z}[t^{\pm 1/2}]$, verify Reidemeister I, II, and III invariance explicitly, match the Rosso–Jones closed form for $T(2,3), T(2,5), T(3,4)$, prove chirality of $3_1$ and amphichirality of $4_1$, and prove the **Borromean Abelian-vs-non-Abelian separation obstruction**: `L6a4` has identically zero pairwise linking matrix ($\operatorname{Lk}_{12}=\operatorname{Lk}_{23}=\operatorname{Lk}_{13}=0$, hence zero Abelian $U(1)$ mutual helicity) and collapses to the 3-unlink value `1` at Abelian Chern–Simons level $k=1$, yet strictly separates from the 3-unlink via its full Jones polynomial and non-Abelian Chern–Simons evaluations at $k \in \{2, 3, 4\}$ inside $\mathbb{Z}[x]/(\Phi_{2(k+2)}(x))$.
2. **Theorem 2 — Exact Cyclotomic $SU(2)_k$ Kac–Peterson Modular Representation & Cayley Poincaré-Disk Isomorphism:** For $k \in \{1, 2, 3, 4\}$, we construct the exact modular matrices $S, T$ inside $\mathbb{Q}(\zeta_N)$ ($N \in \{24, 16, 40, 24\}$, $\varphi(N) \le 16$) via exact Gauss sums, certifying $S^\top = S$, $S^* = S$, $S^2 = I$, $S^\dagger S = I$, $(ST)^3 = I$, and all $8 + 27 + 64 + 125 = 224$ exact integer Verlinde fusion coefficients $N_{ab}^c \in \{0, 1\}$. Over exact $\mathbb{Q}[i]$ and $\mathbb{Q}(\zeta_{12})$, we certify the Cayley isomorphism $\mathcal{C}(\tau) = \frac{\tau - i}{\tau + i}: \mathbb{H} \to \mathbb{D}$, exact $SL(2,\mathbb{Z}) \to PSU(1,1)$ conjugation ($S_{\mathbb{D}}: w \mapsto -w$, $T_{\mathbb{D}}: w \mapsto \frac{(1+i/2)w - i/2}{(i/2)w + (1-i/2)}$), exact pseudo-hyperbolic distance-squared invariance, and exact elliptic fixed points $\tau = i \mapsto w = 0$ and $\tau = e^{i\pi/3} \mapsto -i(2-\sqrt{3})$ (connecting directly to Poincaré-disk Circle Limit hyperbolic tilings).
3. **Theorem 3 — Divisor-$\sigma_k$ Hecke Multiplicativity & Exact Radix-2 NTT + Multi-Prime CRT Zero-Float Convolutions:** We certify all `4,800` Hecke multiplicativity identities for $1 \le m, n \le 40$, $k \in \{1, 3, 5\}$, and implement an iterative radix-2 Cooley–Tukey NTT over $p_1 = 998244353$, $p_2 = 469762049$, and $p_3 = 1004535809$ with exact signed Garner/CRT reconstruction — matching naive $O(N^2)$ integer convolution bit-for-bit on Ramanujan's $E_2 \leftrightarrow E_4$ identity ($N = 128$, 2-prime CRT), $E_4^2 = E_8$ ($N = 128$, 2-prime CRT), and $\Delta = (E_4^3 - E_6^2)/1728$ + Ramanujan $\tau(n)$ multiplicativity (`106` coprime pairs) and prime-power Hecke recurrence (`9` prime-power checks) up to $N = 64$ (3-prime CRT).

---

## 2. Theorem 1 — Exact Jones Polynomials, Borromean Separation & $SU(2)_k$ Chern–Simons Evaluations

### Table 1 — Exact PD-Code Jones Polynomials $V_L(t) \in \mathbb{Z}[t^{\pm 1/2}]$

| Knot / Link | Braid / PD Source | Crossings | Linking / Symmetry Witness | Exact Jones Polynomial $V_L(t)$ |
|---|---|---:|---|---|
| Unknot $0_1$ | `free_loops=1` (also R1 $\sigma_1^{\pm 1}$) | 0 (1) | R1 invariant (`1`) | $1$ |
| 2-Unlink | `free_loops=2` (also R2 $\sigma_1\sigma_1^{-1}$) | 0 (2) | R2 invariant | $-t^{-1/2} - t^{1/2}$ |
| 3-Unlink | `free_loops=3` | 0 | Baseline for `L6a4` | $t^{-1} + 2 + t$ |
| Positive Hopf Link | $\sigma_1^2$ (2 strands) | 2 | $\operatorname{Lk}_{12} = +1$ | $-t^{1/2} - t^{5/2}$ |
| Right-Handed Trefoil $T(2,3)$ | KnotAtlas PD & $\sigma_1^3$ | 3 | Matches Rosso–Jones; R2 & R3 invariant | $t + t^3 - t^4$ |
| Left-Handed Trefoil $\overline{3_1}$ | Mirror PD | 3 | Chiral: $V_{\overline{3_1}}(t) = V_{3_1}(t^{-1}) \ne V_{3_1}(t)$ | $t^{-1} + t^{-3} - t^{-4}$ |
| Cinquefoil $T(2,5)$ | $\sigma_1^5$ (2 strands) | 5 | Matches Rosso–Jones | $t^2 + t^4 - t^5 + t^6 - t^7$ |
| Torus Knot $T(3,4)$ ($8_{19}$) | $(\sigma_1\sigma_2)^4$ (3 strands) | 8 | Matches Rosso–Jones | $t^3 + t^5 - t^8$ |
| Figure-Eight $4_1$ | KnotAtlas PD & $(\sigma_1\sigma_2^{-1})^2$ | 4 | Amphichiral: $V_{4_1}(t) \equiv V_{4_1}(t^{-1})$ | $t^{-2} - t^{-1} + 1 - t + t^2$ |
| **Borromean Rings `L6a4`** | $(\sigma_1\sigma_2^{-1})^3$ (3 strands) | 6 | **$\operatorname{Lk}_{12}=\operatorname{Lk}_{23}=\operatorname{Lk}_{13}=0$** yet $V_{\text{Borr}} \ne V_{\text{3-unlink}}$ | $-t^{-3} + 3t^{-2} - 2t^{-1} + 4 - 2t + 3t^2 - t^3$ |

### Table 2 — Exact Chern–Simons Evaluations at $t^{1/2} = \zeta_{2(k+2)} \in \mathbb{Z}[x]/(\Phi_{2(k+2)}(x))$

| Level $k$ | Ring $\mathbb{Z}[x]/(\Phi_m)$ | $V_{3_1}(\zeta)$ & $|V_{3_1}|^2$ | $V_{4_1}(\zeta)$ & $|V_{4_1}|^2$ | $V_{\text{Borromean}}(\zeta)$ & $|V_{\text{Borr}}|^2$ | Physical Regime |
|---:|---|---|---|---|---|
| $k = 1$ | $\mathbb{Z}[x]/(\Phi_6)$, $\deg 2$ | $1$, $|V|^2 = 1$ | $1$, $|V|^2 = 1$ | $1$, $|V|^2 = 1$ (**equals $V_{\text{3-unlink}}$!**) | Abelian semion collapse |
| $k = 2$ | $\mathbb{Z}[x]/(\Phi_8)$, $\deg 4$ ($t=i$) | $-1$, $|V|^2 = 1$ | $-1$, $|V|^2 = 1$ | $-2$, $|V|^2 = 4$ (vs $V_{\text{3-unlink}}=+2$) | Ising ($c = 3/2$) |
| $k = 3$ | $\mathbb{Z}[x]/(\Phi_{10})$, $\deg 4$ | $-x + x^2 + x^3$, $|V|^2 = 3 - x^2 + x^3$ | $-2x^2 + 2x^3 = 1 - \sqrt{5}$, $|V|^2 = 6 - 2\sqrt{5}$ | $2 - 4x^2 + 4x^3 = 4 - 2\sqrt{5}$ | Fibonacci ($c = 9/5$, golden ratio) |
| $k = 4$ | $\mathbb{Z}[x]/(\Phi_{12})$, $\deg 4$ | $-1 + 2x^2 = i\sqrt{3}$, $|V|^2 = 3$ | $-1$, $|V|^2 = 1$ | $1$, $|V|^2 = 1$ (vs $V_{\text{3-unlink}} = 3$) | $SU(2)_4$ ($c = 2$) |

**Abelian-vs-Non-Abelian Borromean Obstruction:** Every pairwise Gauss linking number of `L6a4` vanishes identically ($\operatorname{Lk} = 0_{3\times 3}$), so any Abelian $U(1)$ mutual-helicity invariant (and even Abelian $SU(2)_1$ Chern–Simons, where $V_{\text{Borromean}}(e^{2\pi i/3}) = 1 = V_{\text{3-unlink}}(e^{2\pi i/3})$) cannot distinguish the Borromean rings from three unlinked circles. Non-Abelian $SU(2)_k$ at all certified levels $k \in \{2, 3, 4\}$ (and the full Jones polynomial) separate them cleanly via exact cyclotomic algebra.

---

## 3. Theorem 2 — Exact Cyclotomic $SU(2)_k$ Modularity & Cayley Poincaré-Disk Isomorphism

### Table 3 — Exact $SU(2)_k$ Kac–Peterson Modular Data in $\mathbb{Q}(\zeta_N)$

| Level $k$ | Central Charge $c = \frac{3k}{k+2}$ | Exact Field $\mathbb{Q}(\zeta_N)$ ($\varphi(N)$) | Conformal Weights $h_a = \frac{a(a+2)}{4(k+2)}$ | $S^2=I$, $S^\dagger S=I$, $(ST)^3=I$ | Verlinde Triples ($N_{ab}^c \in \{0,1\}$) |
|---:|---|---|---|---|---:|
| $k = 1$ | $1$ | $\mathbb{Q}(\zeta_{24})$ ($\deg 8$) | $0, 1/4$ | **EXACT** | `8/8` (`4` nonzero) |
| $k = 2$ | $3/2$ | $\mathbb{Q}(\zeta_{16})$ ($\deg 8$) | $0, 3/16, 1/2$ | **EXACT** | `27/27` (`10` nonzero) |
| $k = 3$ | $9/5$ | $\mathbb{Q}(\zeta_{40})$ ($\deg 16$) | $0, 3/20, 2/5, 3/4$ | **EXACT** | `64/64` (`20` nonzero; $\tau \otimes \tau = 1 \oplus \tau$) |
| $k = 4$ | $2$ | $\mathbb{Q}(\zeta_{24})$ ($\deg 8$) | $0, 1/8, 1/3, 5/8, 1$ | **EXACT** | `125/125` (`35` nonzero) |

### Exact Cayley Isomorphism $\mathcal{C}: \mathbb{H} \to \mathbb{D}$ Over $\mathbb{Q}[i]$ & $\mathbb{Q}(\zeta_{12})$

Under $\mathcal{C}(\tau) = \frac{\tau - i}{\tau + i}$ with matrix $C = \begin{pmatrix} 1 & -i \\ 1 & i \end{pmatrix}$ and inverse $C^{-1} = \frac{1}{2}\begin{pmatrix} 1 & 1 \\ i & -i \end{pmatrix}$:
- $S_{\mathbb{D}} = C S C^{-1} = \begin{pmatrix} -i & 0 \\ 0 & i \end{pmatrix} \in SU(1,1)$, acting as $w \mapsto -w$ (exact $180^\circ$ rotation around the Poincaré-disk center).
- $T_{\mathbb{D}} = C T C^{-1} = \begin{pmatrix} 1 + i/2 & -i/2 \\ i/2 & 1 - i/2 \end{pmatrix} \in SU(1,1)$, acting as $w \mapsto \frac{(1 + i/2)w - i/2}{(i/2)w + (1 - i/2)} = \frac{(2i-1)w + 1}{-w + (1+2i)}$ with exact inverse $T_{\mathbb{D}}^{-1} = C T^{-1} C^{-1} = \begin{pmatrix} 1 - i/2 & i/2 \\ -i/2 & 1 + i/2 \end{pmatrix}$, acting as $w \mapsto \frac{(1 - i/2)w + i/2}{(-i/2)w + (1 + i/2)} = \frac{(1+2i)w - 1}{w + (2i-1)} = \frac{(-1-2i)w + 1}{-w + (1-2i)}$ (exact conjugation confirms $T_{\mathbb{D}}(0) = \frac{1-2i}{5} = \mathcal{C}(1+i)$, $T_{\mathbb{D}}^{-1}(0) = \frac{1+2i}{5} = \mathcal{C}(-1+i)$, $T_{\mathbb{D}}(1) = T_{\mathbb{D}}^{-1}(1) = 1$, and $T_{\mathbb{D}}(T_{\mathbb{D}}^{-1}(w)) \equiv w$).
- Both satisfy $M^\dagger J M = J$ ($J = \operatorname{diag}(1, -1)$), $\det(M) = 1$, $S_{\mathbb{D}}^2 = -I$, $(S_{\mathbb{D}} T_{\mathbb{D}})^3 = -I$, exact interior preservation $1 - |w|^2 > 0$, and exact pseudo-hyperbolic distance-squared invariance $\frac{|w_1 - w_2|^2}{|1 - \bar{w}_1 w_2|^2}$ across all $\mathbb{Q}[i]$ test points.
- Elliptic fixed points map exactly to $\mathcal{C}(i) = 0$ (fixed by $S_{\mathbb{D}}$) and $\mathcal{C}(e^{i\pi/3}) = -i(2 - \sqrt{3}) \in \mathbb{Q}(\zeta_{12})$ with exact $|w|^2 = 7 - 4\sqrt{3} < 1$ and $(T_{\mathbb{D}} S_{\mathbb{D}})(w) = w$ (bridging directly into Poincaré-disk Circle Limit hyperbolic tilings).

---

## 4. Theorem 3 — Exact Hecke Multiplicativity & Zero-Float Radix-2 NTT + CRT Convolutions

- **Hecke Multiplicativity:** Certified identically across all `4,800` pairs ($1 \le m, n \le 40$, $k \in \{1, 3, 5\}$): $\sigma_k(m)\sigma_k(n) = \sum_{d \mid \gcd(m,n)} d^k \sigma_k(mn/d^2)$.
- **NTT Primes:** $p_1 = 998244353 = 119\cdot 2^{23} + 1$, $p_2 = 469762049 = 7\cdot 2^{26} + 1$, $p_3 = 1004535809 = 479\cdot 2^{21} + 1$ (all primitive root $g = 3$), with fail-closed dynamic-range check $2 \|a\|_1 \|b\|_\infty < \prod p_i$ guaranteeing exact signed reconstruction in $(-M/2, M/2)$.
- **Three Certified Zero-Float NTT+CRT Modular Identities (bit-identical to naive $O(N^2)$):**
  1. **Ramanujan $E_2 \leftrightarrow E_4$ ($N = 128$, 2-prime CRT `(p1, p2)`):** $5\sigma_3(n) + (1 - 6n)\sigma_1(n) = 12 \sum_{j=1}^{n-1} \sigma_1(j)\sigma_1(n-j)$ exact for all $1 \le n \le 128$ (`conv[128] = 982345`).
  2. **$E_4^2 = E_8$ ($N = 128$, 2-prime CRT `(p1, p2)` on $\sigma_3 * \sigma_3$):** $480\sigma_3(n) + 57600(\sigma_3 * \sigma_3)[n] = 480\sigma_7(n)$ exact for all $1 \le n \le 128$ (`[q^128] E_8 = 272343662505554400`).
  3. **Modular Discriminant $\Delta = (E_4^3 - E_6^2)/1728$ ($N = 64$, 3-prime CRT `(p1, p2, p3)`):** Exact divisibility by `1728` for all $0 \le n \le 64$, exact $\tau(1..12) = [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944]$, $\tau(64) = 2699296768$, exact multiplicativity $\tau(mn) = \tau(m)\tau(n)$ across all `106` coprime pairs with $mn \le 64$, and exact prime-power Hecke recurrence $\tau(p^{r+1}) = \tau(p)\tau(p^r) - p^{11}\tau(p^{r-1})$ across all `9` prime powers $p^{r+1} \le 64$ ($p \in \{2, 3, 5, 7\}$).

---

## 5. Honest Scope Boundary & Attribution

- **Classical Attribution (`N0`/`N1`):** All mathematical theorems certified here are classical (V. F. R. Jones 1985; L. H. Kauffman 1987; E. Witten 1989; V. G. Kac & D. H. Peterson 1984; E. Verlinde 1988; M. Rosso & V. F. R. Jones 1993; S. Ramanujan 1916; J. W. Cooley & J. W. Tukey 1965; J. M. Pollard 1971). The engineering contribution (`N1`) is their unification into a single zero-float, zero-dependency, fail-closed pure-$\mathbb{Z}/\mathbb{Q}/\mathbb{Q}[\zeta]$ self-verifying certificate suite.
- **Finite-Range Scope:** Hecke multiplicativity ($1 \le m, n \le 40$), $E_2 \leftrightarrow E_4$ and $E_4^2 = E_8$ ($N \le 128$), $\Delta/\tau$ ($N \le 64$), and $SU(2)_k$ ($k \in \{1, 2, 3, 4\}$) are machine-certified on the explicit stated finite domains; general all-$n$/all-$k$ analytic proofs belong to the cited classical literature.

---

## 6. Verification Receipts

- **Frozen Canonical Certificate (`jones_cs_poincare_ntt_certificate.json`):**
  - `file_sha256`: `04f1d454a96a4090dedf2c8a47c377c5e78d3724423761d8d359667bc87b0bd1`
  - `payload_sha256`: `b486548bb1b1ceac75d8ae3a1ad6951f6f0cf9b2748daae82d385d831617c6e0`
  - `certificate_sha256`: `cb336e8c122e4ae91520cd7f906ea5360fccf42171e46a77ac39370f3936e72f`
- **5-Mode Isolated `-I` Parity (`-I -B`, `-I -O -B`, `-I -B -W error`, `-I -O -B -W error`, `PYTHONHASHSEED=42 -B`):**
  - `jones_cs_poincare_ntt_audit.py --standalone --json` x5: bit-identical `04f1d454a96a4090dedf2c8a47c377c5e78d3724423761d8d359667bc87b0bd1`.
  - `jones_cs_poincare_ntt_audit.py --check jones_cs_poincare_ntt_certificate.json` (default full pure-$\mathbb{Q}$ deterministic replay across all 3 theorems) x5: bit-identical `088e281496fe04d276f2db2e385d4960f7694053575b8298cd7627a433d2d43f` (`valid: true`, `full_replay: true`, `all_theorems_passed: true`).
  - `test_jones_cs_poincare_ntt_r5.py` x5: `10/10 OK` (zero bare `assert`s; independent Laurent Skein cross-checks on `kauffman_jones_from_pd` outputs, exact $\mathbb{Q}[i]$ $T_{\mathbb{D}} \circ T_{\mathbb{D}}^{-1} \equiv \mathrm{id}$ checks, signed NTT+CRT vs naive $O(N^2)$ checks, atomic per-component `dir_fd` (`openat`) `O_DIRECTORY | O_NOFOLLOW` traversal + verified root-owned macOS Darwin prefix normalization (`/var`, `/tmp`, `/etc` $\to$ `/private/*`) + leaf `O_NOFOLLOW | O_NONBLOCK` reads + atomic `O_CREAT | O_EXCL` temp + `os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd)` writes + `/proc/kallsyms` streaming cap + hardlink `HARDLINK_FORBIDDEN` & live `420`-write concurrent `os.link` race + scratch `os.mkfifo` `NON_REGULAR_FILE` + deleted/unreadable CWD `CWD_UNAVAILABLE` (`rc=2`) + space- and equals-syntax CLI guard (`--check --json`, `--write --json`, `--check=--json`, `--write=--json`, `--check=`, `--write=`, `allow_abbrev=False`, `rc=2`) + `sys.argv[1:]` `require_str`).
- **Live Concurrent `renameat2(RENAME_EXCHANGE)` & Hardlink Inode-Immutability Verification:**
  - `renameat2(RENAME_EXCHANGE)`: `1,000` concurrent `load_safe_bytes` (`533 ok`, `467 SYMLINK_FORBIDDEN`, `leaks=0`) + `1,000` concurrent `safe_write_bytes` (`492 ok`, `508 SYMLINK_FORBIDDEN`, `clobbers=0`, `leftover=0`) against `49,986` live kernel swaps (`unexpected=0`).
  - Concurrent `os.link`/`os.unlink` hardlink race: `1,000` writes (`208 ok`, `792 HARDLINK_FORBIDDEN`) against `341` live hardlinks (`clobbers=0`, `leftover=0`).
- **Live Mutation & AST `BoolOp` Testing:**
  - Live mutation testing (`--max-mutants 0`, `-I -O -B -W error`): `jones_cs_poincare_ntt_oracle.py` **`115/115`** + `jones_cs_poincare_ntt_audit.py` **`7/7`** = **`122/122` (`100.0%`, `survived=0`, `truncated=False`) KILLED**.
  - Exhaustive AST `BoolOp` (`and` $\leftrightarrow$ `or`) sweep: `jones_cs_poincare_ntt_oracle.py` **`16/16`** + `jones_cs_poincare_ntt_audit.py` **`4/4`** = **`20/20` (`100.0%`, `surv=[]`) KILLED**, plus **`6/6` (`100.0%`)** `SUBCOND_DEL` on `_normalize_darwin_system_prefix`.
- **Adversarial Input Boundary Fuzzing:**
  - CLI surface (`jones_cs_poincare_ntt_audit.py --check`, default full pure-$\mathbb{Q}$ replay): **`25/25` `REJECTED_CLEAN`** (`baseline_ok=true`, `bypasses=0`, `crashes=0`, `PASS`).
  - In-memory validator surface (`validate_certificate_payload`, both `full_replay=True` and `full_replay=False`): **`19/19` + `19/19` `REJECTED_CLEAN`** (`bypasses=0`, `crashes=0`, `PASS`).
  - Combined: **`63/63` (`100.0%`) `REJECTED_CLEAN`**.
- **Static & Hygiene Gate (`--strict-ancestors --safety-scan`):**
  - `PASS` (`5` files scanned, `3` `.py`, `1` `.json`, `2/2` parity scripts, `0` bare asserts, `0` AST float literals / `float()` calls on oracle & audit CLI, `0` CRLF, `0` `__pycache__`, `0` path leaks, `0` private-repo leaks, `0` ancestor permission findings, `0` safety findings).
