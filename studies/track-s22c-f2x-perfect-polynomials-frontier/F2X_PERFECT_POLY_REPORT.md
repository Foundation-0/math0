# Track S22c Report: Exact Pure-Z Bit-Packed F2[x] Perfect Polynomials & Odd Perfect Polynomial Obstruction Frontier

**Track ID:** `TRACK-S22C-F2X-PERFECT-POLY`  
**Portal:** Portal 14, Leg 3 (completing the Perfect-Number Trilogy alongside `Track S22a` modular $E_2/E_4$ and `Track S22b` odd perfect cyclotomic/spoofs)  
**Oracle Class:** `exact` (100% pure Python 3 stdlib exact integer bit-packed $\mathbb{F}_2[x]$ arithmetic and `fractions.Fraction`; zero IEEE-754 floats, zero `float()` calls, zero bare `assert` statements, zero `.isdigit()` calls, zero mathematical RNG, zero third-party dependencies)  
**Honest Law-4 Novelty:** `N1` (clean-room unified pure-$\mathbb{Z}/\mathbb{Q}$ machine-verified oracle, exhaustive degree censuses, characteristic-2 algebraic obstruction suite, and Zone-B hardened certificate pipeline; all classical theorems by Canaday 1941, Beard–O'Connell–West 1977, and Gallardo–Rahavandrainy 2007–2025 strictly quarantined as `N0`)  
**Certificate SHA-256 (`0o600`, `5,622` B):** `5969b8ca5ca45db4c502eec153040c21b932a75d9dcb344821bbf25e6d8ea7dc`  
**Payload SHA-256:** `d57c9f578e6da612ecaae670d7dd25936d185defc49d18aec4601080fd7307d0`  
**Envelope `certificate_sha256`:** `8e7b6dc8240a176ef381d5307b04abdb179004a8bd36c59d24dcc6795b5b2813`

---

## 1. Executive Summary

Over the polynomial ring $\mathbb{F}_2[x]$, Canaday (1941) defined a nonzero polynomial $A \in \mathbb{F}_2[x]$ to be **perfect** when the sum of all its monic divisors equals itself:
$$\sigma(A) = \sum_{D \mid A} D = A \quad \Longleftrightarrow \quad \sum_{\substack{D \mid A \\ D \neq A}} D = 0 \pmod{2}.$$
(Under this nonzero definition, the trivial constant polynomial $A = 1$ is vacuously odd and satisfies $\sigma(1) = 1$; throughout this report, the odd perfect polynomial frontier concerns **nonconstant** odd perfect polynomials, i.e., $\deg(A) \ge 1$, equivalently $\deg(A) \ge 2$ since no degree-$1$ polynomial in $\mathbb{F}_2[x]$ is coprime to $x(x+1)$.) Because $2 \equiv 0$ in characteristic $2$, the integer condition $\sigma(N) = 2N$ (proper divisor sum $= N$) translates directly to $\sigma(A) = A$ (proper divisor sum $= 0$, since $A \oplus A = 0$). Using exact carry-less bit-packed integer representations ($A = \sum_k c_k x^k \leftrightarrow \sum_k c_k 2^k \in \mathbb{Z}_{\ge 0}$) and a zero-division smallest-irreducible-factor (`spf`) / cofactor (`cof`) sieve, `f2x_perfect_poly_oracle.py` and `f2x_perfect_poly_audit.py` establish four exact mathematical pillars (`P1..P4`) under a Zone-B hardened verification boundary (`P5`):

1. **P1 — Bit-Packed $\mathbb{F}_2[x]$ Ring, Rabin Irreducibility & $\sigma$ Laws:** Exact Necklace/Möbius irreducible counts for $\deg 1..12$ (`[2, 1, 2, 3, 6, 9, 18, 30, 56, 99, 186, 335]`), `510/510` independent Rabin vs sieve agreement through $\deg \le 8$, `6/6` coprime multiplicativity + direct divisor-enumeration + Frobenius squaring + $x \mapsto x+1$ involution checks, `36/36` geometric sum identities $(P+1)\sigma(P^e) = P^{e+1}+1$, and explicit Canaday anchor $A = x(x+1) = 6$.
2. **P2 — Complete Splitting Characterization ($x^a(x+1)^b$):** Exhaustive enumeration of all `288` non-constant pairs $(a, b) \in [0..16]^2 \setminus \{(0,0)\}$ proves that $x^a(x+1)^b$ is perfect if and only if $a = b = 2^n - 1$ (`[[1,1], [3,3], [7,7], [15,15]]`), backed by exact Mersenne-power duality $\sigma(x^{2^n-1}) = (x+1)^{2^n-1}$ and $\sigma((x+1)^{2^n-1}) = x^{2^n-1}$ verified through $n = 6$ ($\deg = 126$) plus `5` negative controls.
3. **P3 — Complete $\deg 1..14$ Census & All `11` Canaday Sporadic Perfect Polynomials:** Exhaustive census of all `32,766` monic polynomials of $\deg 1..14$ finds exactly **`9`** perfect polynomials (`3` splitting + `6` sporadic; exact rational density **`3/10922`**, decimal `0.000275`, pure-integer `-0.00` normalization witness `0.000000`). All **`11`** sporadic even perfect polynomials of Canaday (1941) ($\deg 5..20$) are machine-certified with full prime reconstruction, `6` independent direct divisor-enumeration cross-checks ($\deg \le 11$), and exact $x \mapsto x+1$ involution structure (`5` conjugate twin pairs + unique deg-16 self-symmetric fixed point `67184`).
4. **P4 — Nonconstant Odd Perfect Polynomial Obstruction Frontier ($\deg 2..24$):** Direct exhaustive verification across all **`32,767`** nonconstant odd monic polynomials of $\deg 2..16$ (`16,384` at $\deg 16$) finds **`0`** solutions. Two characteristic-2 algebraic obstructions are machine-verified across all `69` odd irreducibles of $\deg 2..8$:
   - **Theorem 4A (Even-Exponent / Square Necessity):** For all `276` pairs $(P, e) \in \{\text{odd irreds } \deg 2..8\} \times \{1, 3, 5, 7\}$, $x(x+1) \mid \sigma(P^e)$ identically, proving every nonconstant odd perfect polynomial in $\mathbb{F}_2[x]$ must be a pure square $A = B^2$ (sharp contrast with integer odd perfect numbers $N = p^\alpha m^2$).
   - **Theorem 4B (Unconditional $\omega(A) \ge 3$ via Char-2 Derivative Identity):** $\gcd(P, \sigma(P^e)) = 1$ rules out $\omega(A) = 1$, and differentiating $(P+1)\sigma(P^{2a}) = P^{2a+1}+1$ yields $P'\sigma(P^{2a}) \oplus (P+1)\sigma(P^{2a})' = P^{2a}P'$, forcing $\sigma(P^{2a})' \ne 0$ (hence $\sigma(P^{2a})$ is never a square in $\mathbb{F}_2[x]$, verified across `276` witnesses), ruling out $\omega(A) = 2$ unconditionally.
   - **Square-Lifted Exhaustive Frontier ($\deg 2..24$):** Testing all **`2,047`** nonconstant odd squares $A = B^2$ with **`2 <= deg(B) <= 12`** ($4 \le \deg(A) \le 24$) yields **`0`** solutions, certifying unconditionally that **zero nonconstant odd perfect polynomials exist in $\mathbb{F}_2[x]$ of degree $1 \le \deg(A) \le 24$** (excluding trivial constant $A = 1$ where $\sigma(1) = 1$; covering all **`8,388,607`** ($2^{23} - 1$) nonconstant odd monic polynomials of degree `2..24`).

---

## 2. Pillar-by-Pillar Exact Results

### 2.1 Pillar 1: Bit-Packed $\mathbb{F}_2[x]$ Ring & Divisor-Sum Engine

| Property | Exact Certified Count / Value |
| --- | --- |
| Irreducible counts $\deg 1..12$ | `[2, 1, 2, 3, 6, 9, 18, 30, 56, 99, 186, 335]` |
| Rabin vs SPF sieve cross-check ($\deg 1..8$) | `510 / 510` exact agreement |
| Coprime multiplicativity + direct divisor-sum + Frobenius + shift involution | `6 / 6` exact witnesses |
| Geometric sum identity $(P+1)\sigma(P^e) = P^{e+1}+1$ | `36 / 36` exact witnesses (`6` irreducibles $\times$ `6` exponents) |
| Canaday anchor $A = x(x+1)$ (`mask = 6`) | $\sigma(x) = 3$, $\sigma(x+1) = 2$, $\sigma(6) = 6$, $\sigma(6) \oplus 6 = 0$ |

### 2.2 Pillar 2: Splitting Perfect Polynomials $x^a(x+1)^b$

Exhaustive grid over $(a, b) \in [0..16]^2 \setminus \{(0,0)\}$ (`288` non-constant polynomials):
- **Exact perfect splitting pairs:** `[[1, 1], [3, 3], [7, 7], [15, 15]]` (precisely $a = b = 2^n - 1$).
- **Mersenne-power duality ($\sigma(x^{2^n-1}) = (x+1)^{2^n-1}$ and $\sigma((x+1)^{2^n-1}) = x^{2^n-1}$):**

| $n$ | Exponent $e = 2^n - 1$ | Degree $2e$ | Duality Exact |
| ---: | ---: | ---: | :---: |
| 1 | 1 | 2 | `True` |
| 2 | 3 | 6 | `True` |
| 3 | 7 | 14 | `True` |
| 4 | 15 | 30 | `True` |
| 5 | 31 | 62 | `True` |
| 6 | 63 | 126 | `True` |

- **Negative controls (`is_perfect = False`):** `(2,1)`, `(1,2)`, `(2,2)`, `(3,1)`, `(4,4)`.

### 2.3 Pillar 3: Exhaustive $\deg 1..14$ Census & All `11` Canaday Sporadic Polynomials

- **Exhaustive $\deg 1..14$ census:** `32,766` monic polynomials $\to$ **`9`** perfect (`3` splitting: masks `6, 120, 32640`; `6` sporadic: masks `36, 54, 2470, 2640, 3144, 3780`).
- **Exact rational density:** `9 / 32766 = 3/10922` (`0.000275`; `-0.00` formatter witness `format_decimal_rounded(-1/10_000_000, 6) == "0.000000"`).
- **All `11` Canaday (1941) sporadic even perfect polynomials (`5` conjugate twin pairs under $x \mapsto x+1$, `1` unique deg-16 self-symmetric fixed point):**

| Mask | Deg | $\omega(A)$ | Shift $A(x+1)$ | Symmetry | Exact Canonical Factorization in $\mathbb{F}_2[x]$ |
| ---: | ---: | ---: | ---: | --- | --- |
| `36` | 5 | 3 | `54` | Twin Pair 1 | `x^2*(x+1)*(x^2+x+1)` |
| `54` | 5 | 3 | `36` | Twin Pair 1 | `x*(x+1)^2*(x^2+x+1)` |
| `2470` | 11 | 4 | `3780` | Twin Pair 2 | `x*(x+1)^2*(x^2+x+1)^2*(x^4+x+1)` |
| `3780` | 11 | 4 | `2470` | Twin Pair 2 | `x^2*(x+1)*(x^2+x+1)^2*(x^4+x+1)` |
| `2640` | 11 | 3 | `3144` | Twin Pair 3 | `x^4*(x+1)^3*(x^4+x^3+x^2+x+1)` |
| `3144` | 11 | 3 | `2640` | Twin Pair 3 | `x^3*(x+1)^4*(x^4+x^3+1)` |
| `41280` | 15 | 4 | `52632` | Twin Pair 4 | `x^6*(x+1)^3*(x^3+x+1)*(x^3+x^2+1)` |
| `52632` | 15 | 4 | `41280` | Twin Pair 4 | `x^3*(x+1)^6*(x^3+x+1)*(x^3+x^2+1)` |
| `67184` | 16 | 4 | `67184` | **Self-Symmetric** | `x^4*(x+1)^4*(x^4+x^3+1)*(x^4+x^3+x^2+x+1)` |
| `1098176` | 20 | 5 | `1157904` | Twin Pair 5 | `x^6*(x+1)^4*(x^3+x+1)*(x^3+x^2+1)*(x^4+x^3+1)` |
| `1157904` | 20 | 5 | `1098176` | Twin Pair 5 | `x^4*(x+1)^6*(x^3+x+1)*(x^3+x^2+1)*(x^4+x^3+x^2+x+1)` |

### 2.4 Pillar 4: Nonconstant Odd Perfect Polynomial Obstruction Frontier

A polynomial $A \in \mathbb{F}_2[x]$ is **odd** when $\gcd(A, x(x+1)) = 1$, i.e., $A(0) = 1$ and $A(1) = 1$. The constant polynomial $A = 1$ is trivially odd and satisfies $\sigma(1) = 1$, so all non-existence statements below apply strictly to **nonconstant** odd polynomials ($\deg(A) \ge 1$, equivalently $\deg(A) \ge 2$ because both degree-$1$ polynomials $x$ and $x+1$ are even).

1. **Direct Exhaustive Non-Existence ($\deg 2..16$):** Every nonconstant odd monic polynomial of degree `2..16` (`32,767` total; `16,384` at $\deg = 16$) was evaluated directly via exact multiplicative $\sigma$; **`0`** nonconstant odd perfect polynomials exist.
2. **Theorem 4A (Even-Exponent / Square Necessity):** For any odd irreducible $P$ ($P(0) = P(1) = 1$) and any odd exponent $e$, $\sigma(P^e) = 1 + P + \dots + P^e$ has $e+1 \equiv 0 \pmod{2}$ terms, so $\sigma(P^e)(0) = 0$ and $\sigma(P^e)(1) = 0$, hence $x(x+1) \mid \sigma(P^e)$. Since $\sigma$ is multiplicative, any nonconstant odd perfect polynomial $A$ cannot contain any odd prime-power exponent, so **$A = B^2$ must be a pure square** (with $\deg(B) \ge 2$). Verified explicitly across all `69` odd irreducibles of $\deg 2..8$ $\times$ $e \in \{1, 3, 5, 7\}$ (`276/276` witnesses).
3. **Theorem 4B (Unconditional $\omega(A) \ge 3$ for Nonconstant Odd Perfect $A$):**
   - $\omega(A) \ne 1$ because $\gcd(P, \sigma(P^e)) = \gcd(P, 1) = 1$.
   - $\omega(A) \ne 2$: if $A = P^{2a}Q^{2b}$ were a nonconstant odd perfect polynomial, then $\sigma(P^{2a})\sigma(Q^{2b}) = P^{2a}Q^{2b}$ with $\gcd(P, \sigma(P^{2a})) = 1$ forces $Q^{2b} \mid \sigma(P^{2a})$ and $\sigma(P^{2a}) = Q^{2b}$ (a square!). Differentiating $(P+1)\sigma(P^{2a}) = P^{2a+1}+1$ in characteristic $2$ gives:
     $$P'\sigma(P^{2a}) \oplus (P+1)\sigma(P^{2a})' = P^{2a}P'.$$
     If $\sigma(P^{2a})$ were a square, then $\sigma(P^{2a})' = 0$, forcing $P'(\sigma(P^{2a}) \oplus P^{2a}) = 0$. Every irreducible over $\mathbb{F}_2$ is separable ($P' \ne 0$), and $\sigma(P^{2a}) \ne P^{2a}$ since $1 + P + \dots + P^{2a-1} \ne 0$, a contradiction. Therefore $\sigma(P^{2a})' \ne 0$, so $\sigma(P^{2a})$ is **never a square** in $\mathbb{F}_2[x]$, ruling out $\omega(A) = 2$ unconditionally (`276/276` witnesses verified).
4. **Square-Lifted Exhaustive Non-Existence ($\deg 2..24$):** By Theorem 4A, checking all `2,047` nonconstant odd roots $B$ with **`2 <= deg(B) <= 12`** covers every nonconstant odd perfect candidate of degree $1 \le \deg(A) \le 24$ — spanning all **`8,388,607`** ($2^{23} - 1$) nonconstant odd monic polynomials of degree `2..24` (excluding trivial constant $A = 1$). Exact $\sigma(B^2)$ evaluation yields **`0`** solutions.

---

## 3. Pillar 5: Zone-B Hardened Verification & Honest Boundaries

### 3.1 Hardening Controls Implemented

- **Exact `4,096`-Bit Enforcement Cap & `4,300`-Digit Immunity:** `MAX_EXACT_INT_BITS = MAX_JSON_INT_BITS = 4,096` is the exact enforcement cap across `format_fraction`, `format_decimal_rounded`, `canonical_json_bytes`, `_validate_json_tree`, and `parse_exact_rational`, while `MAX_JSON_INT_DIGITS = 1,234` (`len(str((1<<4096)-1)) == 1234`) serves as a **necessary (not sufficient)** decimal-length pre-parse cap that prevents Python's `4,300`-digit `int -> str` `ValueError` before exact bit-length checking (so `1,234`-digit integers above $2^{4096}-1$, such as $10^{1234} - 1$ which has `4,100` bits, fail closed on the `4,096`-bit cap with `INT_BIT_LIMIT`).
- **Public Helper Validation:** All public oracle functions (`factor_with_sieve`, `sigma_from_factors`, `format_factorization_f2`, `compute_sigma_direct_by_divisors`, polynomial primitives) validate exact concrete types and ranges fail-closed via `F2xPerfectError`.
- **Atomic `dir_fd` Filesystem Hardening:**
  - Concrete `pathlib.Path` check (`_EXACT_PATH_TYPES`), NUL-byte and lone UTF-16 surrogate rejection, deleted-CWD `OSError -> CWD_UNAVAILABLE (rc=2)`.
  - Atomic relative-path `dir_fd` walk over `PWD` (`_check_pwd_no_symlinks`) + per-component `os.open(..., O_RDONLY | O_DIRECTORY | O_NOFOLLOW)`.
  - Streaming `65,536`-byte `read_regular_bytes_capped` (`O_RDONLY | O_NOFOLLOW | O_NONBLOCK`, `fstat` `S_ISREG`, strict cap `<= 64 MiB`, closing `/proc/kallsyms` `st_size==0` traps).
  - Atomic `write_regular_bytes_safe`: `type(payload) is bytes` before touching filesystem $\to$ target `lstat` (`SYMLINK_FORBIDDEN`, `NOT_A_REGULAR_FILE`, `HARDLINK_FORBIDDEN` on `st_nlink > 1`) $\to$ `threading.Lock()` + `secrets.token_hex(8)` + `EEXIST` retry loop with `O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_NONBLOCK` (`0o600`) $\to$ `os.fsync(tmp_fd)` $\to$ pre-replace `os.fstat(tmp_fd).st_nlink == 1` $\to$ `os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd)` $\to$ `os.fsync(dfd)`.
- **Strict JSON / CLI / Division-Free Field-Complete Secondary Audit:** UTF-8 BOM/CRLF/NUL/surrogate/duplicate-key/float/non-finite/depth-64/byte-cap (`MAX_JSON_BYTES = 1 MiB`) enforcement in `parse_strict_json_text`; `_validate_json_tree` inside `canonical_json_bytes`, `verify_certificate_dict`, and directly inside `secondary_audit_payload`; strict 64-char lowercase ASCII hex check before `hmac.compare_digest`; strict exact-`str` argv validation rejecting empty, space-syntax (`--write --json`), and equals-syntax (`--write=--json`, `--check=--json`) flag-like arguments (`rc=2`, `0` files created); strict-keyset `secondary_audit_payload` enforcing exact nested key-sets on every object (`payload`, `p1..p4`, `canaday_anchor_x_xp1`, `duality_witnesses_n_1_to_6[*]`, `negative_controls[*]`, `census_deg_1_to_14[*]`, `canaday_11_sporadic[*]`), division-free cross-multiplication (`dens_q * p3["total_monic_polys_deg_1_to_14"] == p3["perfect_count_deg_1_to_14"]`, eliminating any `ZeroDivisionError` when `total_monic_polys_deg_1_to_14 = 0`), exact canonical `prior_art_quarantine_n0`, exact negative-control `(a, b)` non-perfection, and exact factorization / $\sigma(A) = A$ / `is_splitting` / `omega` / `factorization` invariants under BOTH `full_replay=True` and `full_replay=False`.

### 3.2 Honest Same-UID POSIX Atomicity Boundary & `--check` Scope

- **Same-UID POSIX Atomicity Boundary:** The `dir_fd` + `O_NOFOLLOW` + `0o600` `O_CREAT|O_EXCL` temp + `os.fsync(tmp_fd)` + pre-replace `fstat(tmp_fd).st_nlink == 1` + target `st_nlink <= 1` + `os.replace(..., dir_fd)` + `os.fsync(dfd)` protocol closes symlink-following, FIFO/device open blocks, hardlink target clobber, partial writes, and concurrent temp-name races across honest concurrent threads/processes and live `renameat2(RENAME_EXCHANGE)` / hardlink attack loops. Under standard POSIX semantics, however, a hostile process executing under the **same UID** with write permission on the parent directory retains kernel authority to unlink or rename directory entries between syscalls; full isolation against a malicious same-UID adversary requires OS-level privilege separation (distinct UIDs or mount namespaces).
- **Deterministic-Replay `--check` & `secondary_audit_payload` Scope:** `f2x_perfect_poly_audit.py --check <path>` verifies a deterministic standalone certificate against canonical LF-only UTF-8 bytes, strict JSON/tree validation, SHA-256 integrity, `secondary_audit_payload`, AND full pure-$\mathbb{Z}/\mathbb{Q}$ replay (`build_certificate()`). Callers invoking `verify_certificate_dict(cert, full_replay=False)` skip the full degree-14/16/24 sieve census while still running strict nested-keyset, SHA-256, exact-`int`, and exact algebraic factorization/divisor-sum cross-checks in `secondary_audit_payload` (note: `secondary_audit_payload` imports polynomial/sieve primitives from `f2x_perfect_poly_oracle.py`, so it is an intra-package algebraic cross-check rather than a zero-shared-code independent verifier).

---

## 4. Honest Law-4 Prior-Art Quarantine (`N0` vs `N1`)

| Classification | Attribution & Scope |
| :---: | --- |
| **`N0` (Prior Art)** | E. F. Canaday (1941), *The sum of the divisors of a polynomial*, Duke Math. J. 8(4), 721–737 — definition of perfect polynomials over $\mathbb{F}_2[x]$ and the `11` sporadic even perfect polynomials. |
| **`N0` (Prior Art)** | J. T. B. Beard Jr., J. R. O'Connell Jr., K. I. West (1977), *Perfect polynomials over $GF(q)$*, Atti Accad. Naz. Lincei — complete characterization of splitting perfect polynomials. |
| **`N0` (Prior Art)** | L. H. Gallardo & O. Rahavandrainy (2007–2025) — square necessity, number-of-irreducible-factors obstructions, and non-existence bounds for nonconstant odd perfect polynomials over $\mathbb{F}_2[x]$. |
| **`N1` (This Track)** | Clean-room unified pure-$\mathbb{Z}/\mathbb{Q}$ zero-float bit-packed $\mathbb{F}_2[x]$ oracle, exhaustive $\deg 1..14$ all-polynomial & $\deg 2..16$ direct / $\deg 2..24$ square-lifted nonconstant odd censuses, machine-checked characteristic-2 derivative obstruction certificates, and Zone-B hardened verification suite. |

---

## 5. Post-Final-Edit Verification Receipts & Frozen Manifest

All checks executed strictly sequentially (`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1`) after the final code edit:

- **3-Mode Isolated Parity + Extended Modes (`-I -B`, `-I -O -B`, `-I -B -W error`, plus `-I -O -B -W error` & `PYTHONHASHSEED=42 -B` without `-I`):**
  - `--standalone --json`: bit-identical `5969b8ca5ca45db4c502eec153040c21b932a75d9dcb344821bbf25e6d8ea7dc` across all `5/5` modes (matching disk `0o600` certificate byte-for-byte).
  - `--check f2x_perfect_poly_certificate.json`: bit-identical `cdf885a23dfc9f92b5f5dd738cbcaa52a4cfa0e19d214ccad828bc96ca70e0d7` across all `5/5` modes.
  - `test_f2x_perfect_poly_r5.py`: **`4/4 OK`** across all `5/5` modes (including `33` re-signed semantic, zero-denominator, & strict nested-keyset tamper kills across both `full_replay=False` and `secondary_audit_payload`, `16T` distinct + `16T` same-target + `80T` barrier burst + `520`-iter `renameat2(RENAME_EXCHANGE)` + `420`-iter hardlink race: `0` leaks, `0` clobbers, `0` `.tmp` leftovers).
- **Exhaustive Zero-Denominator & Leaf Tamper Sweep:** **`657`** mutations across all **`223`** payload leaves (incl. `0`, `"0"`, `"1/0"`) on both `verify_certificate_dict(full_replay=False)` & `secondary_audit_payload` (**`1,314/1,314`**: `bypasses=0, raw_excs=0`, `0` `ZeroDivisionError`).
- **Live `aletheia v2.0.0 mutate --max-mutants 0 --work-root . --add-cwd --guards require_ok`:**
  - `f2x_perfect_poly_oracle.py`: **`31/31` (`100.0%`, `survived=0`, `truncated=False`)**.
  - `f2x_perfect_poly_audit.py`: **`89/89` (`100.0%`, `survived=0`, `truncated=False`)**.
  - **Combined:** **`120/120` (`100.0%`)**.
- **Exhaustive AST `BoolOp` (`OP_SWAP + SUBCOND_DEL`):**
  - `f2x_perfect_poly_oracle.py`: `OP_SWAP=2/2`, `SUBCOND_DEL=4/4` = **`6/6` (`100.0%`, `surv=[]`)**.
  - `f2x_perfect_poly_audit.py`: `OP_SWAP=10/10`, `SUBCOND_DEL=20/20` = **`30/30` (`100.0%`, `surv=[]`)**.
  - **Combined:** **`36/36` (`100.0%`, `surv=[]`)**.
- **Live 4-Surface Zone-B Fuzzer:**
  - `CLI`: **`23/23`** (`bypasses=0, crashes=0, PASS`).
  - `verify_certificate_dict(..., full_replay=True)`: **`18/18`** (`bypasses=0, crashes=0, PASS`).
  - `verify_certificate_dict(..., full_replay=False)`: **`18/18`** (`bypasses=0, crashes=0, PASS`).
  - `secondary_audit_payload(...)`: **`18/18`** (`bypasses=0, crashes=0, PASS`).
  - **Combined:** **`77/77` (`100.0%`)**.
- **AST & Hygiene Audit:** `0` bare `assert`s, `0` AST float literals, `0` `float()` calls, `0` `.isdigit()`, `0` mathematical RNG, real `os.fsync` at `f2x_perfect_poly_audit.py` lines `356, 366`, `0` absolute home-directory path leaks, `0` private-org leaks, `0` `.pyc`/`__pycache__`; `aletheia v2.0.0 audit-check . --strict-ancestors --safety-scan --scripts f2x_perfect_poly_audit.py test_f2x_perfect_poly_r5.py` **`PASS`** (`5` files, `2/2` scripts clean across all 3 isolated modes, `0` findings).

### Frozen Code & Certificate Manifest

| File | Lines | Bytes | Mode | SHA-256 |
| --- | ---: | ---: | :---: | --- |
| `f2x_perfect_poly_oracle.py` | 920 | 32,721 | `0644` | `1d4df80841fe8cd365ab084e6e633b78781788e975ef4932d04437fc2ffb6ff6` |
| `f2x_perfect_poly_audit.py` | 894 | 39,240 | `0644` | `8cd479e78511cd03aee606c318c8082c54ccb959ac0afc1e9941ce9e296de27e` |
| `test_f2x_perfect_poly_r5.py` | 950 | 56,799 | `0644` | `eb719cf291b6266b0a5b7d93c50e402d4a44a39ddf50ae7327e7783c2ad62962` |
| `f2x_perfect_poly_certificate.json` | 1 | 5,622 | `0600` | `5969b8ca5ca45db4c502eec153040c21b932a75d9dcb344821bbf25e6d8ea7dc` |
| `F2X_PERFECT_POLY_REPORT.md` | — | — | `0644` | *(this report; verified via `aletheia v2.0.0 audit-check --strict-ancestors --safety-scan`)* |
