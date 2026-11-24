# Track S40 (Portal 38) — Exact Pure-$\mathbb{Z}/\mathbb{Q}/\mathbb{F}_2[x]$ Operator Bridge: Mozart $n$-th Order Patterns $\to$ Perfect Numbers & $\mathbb{F}_2[x]$ Perfect Polynomials

- **Track / Portal ID:** `TRACK-S40-MOZART-PERFECT-BRIDGE` / `Portal-38`
- **Schema Version:** `aletheia.track_s40.mozart_perfect_bridge.v1`
- **Methodology:** The Aletheia Method v2.0.0 (`OWN_TERMS_FIRST`, Law 1b, Law 2b, Law 4 `CS-13`, Law 5 Beyond-Language Exact Operators)
- **Novelty Classification:** **`N1`** (clean-room unified pure-$\mathbb{Z}/\mathbb{Q}/\mathbb{F}_2[x]$ exact-operator certificate engine and Zone-B fail-closed auditor bridging Mozart finite-difference/Ducci operators to perfect-number and $\mathbb{F}_2[x]$ perfect-polynomial proofs; all classical theorems and cited prior work strictly quarantined as **`N0`**)
- **Trust-Path Arithmetic:** 100% pure Python 3 stdlib (`int`, `fractions.Fraction`, `math`); **`0`** IEEE-754 floats in production code and certificate (`test_mozart_perfect_bridge_r5.py` has `0` AST float literals and `0` `float()` calls, using `json.loads("1.5")` and `json.loads("4.0")` solely as negative runtime test fixtures); **`0`** bare `assert`s; **`0`** `.isdigit()` calls; **`0`** mathematical RNG calls (`secrets.token_hex(8)` used strictly for atomic temp filename uniqueness).
- **Canonical Certificate Digests (`mozart_perfect_bridge_certificate.json`, `0o600`):**
  - File / `--standalone --json` SHA-256: `3c6b226b43804befdd102a4f02800421087ed851009967bc20b2e72479ce336e`
  - `payload_sha256`: `540afeaa6eb549d61e7a85d7f7d025a83e497d67e1e6238d277f2eb6baea913a`
  - `certificate_sha256`: `b87590fe14b30c90d8536ee45153db9f6a2a3ad7cc06569b94fa6ff031aa1b10`

---

## 1. `OWN_TERMS_FIRST` & Law-2b / Law-5 Scope Boundary

Every bridge in Track S40 strips surface musical/historical labels (Stage A) and retains only coordinate-, transposition-, and radix-invariant exact ring and difference operators (Stage B):

1. **Pillar 1 — Frobenius–Ducci $2^n$ Nilpotence $\equiv$ Canaday (1941) Splitting Perfect Polynomials $\xrightarrow{x=2}$ Euclid–Euler:**
   - The single characteristic-2 Frobenius identity $(x + 1)^{2^n} = x^{2^n} + 1$ in $\mathbb{F}_2[x]$ simultaneously:
     - (a) annihilates every $2^n$-length binary cyclic phrase under $\Delta = S + I$ ($\Delta^{2^n} \equiv 0 \pmod{x^{2^n} + 1}$), matching Mozart's $2^n$-length Ducci collapses (`K.551` 4-note & 8-note, `K.545` Alberti `L=4`, `K.550` 8-note);
     - (b) divides cleanly by $(x + 1)$ to give the exact duality swap $\sigma(x^{2^n-1}) = (x+1)^{2^n-1}$ and $\sigma((x+1)^{2^n-1}) = x^{2^n-1}$, certifying Canaday's splitting perfect polynomials $A_n(x) = x^{2^n-1}(x+1)^{2^n-1}$ with $\sigma(A_n) = A_n$ across $n = 1..6$ (degrees `2, 6, 14, 30, 62, 126`, plus direct all-divisor XOR checks for `n = 1..3`);
     - (c) specializes in characteristic $0$ at $x = 2$ to Euclid–Euler even perfect numbers $N = 2^{p-1}(2^p - 1)$ (`p = 2, 3, 5, 7, 13, 17, 19`, exact $\sigma(N) = 2N$), while exposing the exact composite-exponent split at $m = 4$: $x^4 + 1 = (x+1)^4$ remains purely primary in $\mathbb{F}_2[x]$ ($A_2$ perfect), whereas $2^4 - 1 = 15 = 3 \cdot 5$ breaks primality in $\mathbb{Z}$ ($N = 120$ abundant: $\sigma(120) = 360 = 240 + 120$).
2. **Pillar 2 — Cyclotomic Period Obstruction vs. $\mathbb{F}_2[x]$ Odd Perfect Square Theorem & Honest $\mathbb{Z}$ Carry-Propagation Obstruction:**
   - Exact cyclotomic factorization $S^L - 1 = \prod_{d \mid L} \Phi_d(S)$ over $\mathbb{Z}[S]$ shows why odd cyclotomic factors ($\Phi_3$ for `K.550` 3-note sigh `L=3`, $\Phi_5$ for `L=5`, $\Phi_3 \Phi_6$ for `K.331` `6/8` bar `L=6`) are coprime to $\Delta = S + 1$ in $\mathbb{F}_2[S]$ and block Ducci nilpotence into cycles of exact period `3, 15, 6`.
   - The identical cyclotomic divisor identity $\sigma(p^a) = \prod_{d \mid (a+1),\, d > 1} \Phi_d(p)$ is certified across `24/24` $\mathbb{Z}$ prime powers and `15/15` $\mathbb{F}_2[x]$ prime powers.
   - Over $\mathbb{F}_2[x]$, for EVERY one of the `21` odd irreducibles $P$ of degree `2..6` and odd exponents $a \in \{1, 3, 5\}$ (`63/63` cases, plus `6/6` non-square odd composite products), $x(x+1) \mid (P+1) \mid \sigma(P^a)$, proving **every odd perfect polynomial in $\mathbb{F}_2[x]$ must be a perfect square $A = B^2$**.
   - **Honest Law-4 / Law-5 Carry-Propagation Obstruction:** In $\mathbb{Z}$, carry propagation ($1 + 1 = 2 \ne 0$) breaks this characteristic-2 collapse: every Euler prime $q \equiv 1 \pmod 4$ (`q = 5, 13, 17, 29, 37, 41`) satisfies $v_2(\sigma(q^1)) = v_2(\sigma(q^5)) = 1$ (emitting the single factor of $2$ matching $\sigma(N) = 2N$, contrasted with `q = 3, 7, 11, 19` where $v_2(q+1) \ge 2$). Therefore the $\mathbb{F}_2[x]$ square theorem **does not prove** the integer Odd Perfect Number conjecture, which remains **genuinely open** (`integer_opn_conjecture_remains_open: true`).
3. **Pillar 3 — Nyquist-4 $\sigma(n)$ Difference Spectrum $\to$ Euler Pentagonal Annihilator & Ramanujan $E_2 \leftrightarrow E_4$ Perfect-Number Convolution:**
   - Exact pure-$\mathbb{Q}$ spectral prism compares both raw energy ratios $R_n = E_n / E_{n-1}$ (unweighted total-energy convention) and per-sample mean-square ratios $R_n^{\mathrm{ms}} = \frac{E_n/(L-n)}{E_{n-1}/(L-n+1)}$ (length-normalized convention) across $n^2$, `K.550`, `K.545` Alberti, and $\sigma(1..32)$, certifying strict Nyquist ordering $R_2(n^2) < 1 < R_2(\text{K.550}) < 2 < 3 < R_2(\text{K.545 Alberti}) < R_2(\sigma) < 4$, with $\sigma(1..32)$ clearing raw $R_2..R_5 > 17/5$ (`3.4`) and mean-square $R_2^{\mathrm{ms}}..R_5^{\mathrm{ms}} = [3.687131, 3.685513, 3.636022, 3.616118] > 18/5$ (`3.6`).
   - Euler's pentagonal recurrence annihilates $\sigma(n)$ on `100/100` (`n = 1..100`) with exact constant second difference $\Delta^2 p_k^+ \equiv \Delta^2 p_k^- \equiv 3$ ($\Delta^3 \equiv 0$) and period-4 sign sequence `[+1, +1, -1, -1]` annihilated identically by the Alberti shift factor $(S^2 + I) \mid (S^4 - I)$.
   - Ramanujan's general $E_2 \leftrightarrow E_4$ convolution $12 \sum_{k=1}^{n-1} \sigma(k)\sigma(n-k) = 5\sigma_3(n) + (1 - 6n)\sigma(n)$ holds on `64/64` (`n = 1..64`), and substituting $\sigma(n) = 2n$ yields the exact perfect-number specialization $12\sum_{k=1}^{n-1}\sigma(k)\sigma(n-k) = 5\sigma_3(n) + 2n(1 - 6n)$ selecting **exactly `{6, 28}`** in `1..64` and verified at `n = 496` (`6 -> 840`, `28 -> 116,208`, `496 -> 694,330,560`).
4. **Pillar 4 — Adversarial Law-5 Anti-Numerology Control (Stage A vs. Stage B):**
   - Demonstrates quantitatively that Stage-A surface features (fixed-origin C-pitch-class histogram under transposition $p \mapsto p + c$; base-10 "ends in `6` or `8`" artifact under radix change $b \in \{2, 8, 10, 12, 16\}$; and Mozart sonata golden-ratio bar-count splits `K.282/283/332/576 I` with nonzero integer golden defects `-99, -1871, -2801, +1124` and `> 2%` deviation from $\phi^{-1}$) fail gauge/radix/exactness tests, whereas Pillars 1–3 are `100%` transposition-, coordinate-, and radix-invariant.

---

## 2. Law-4 `N0` Prior-Art Quarantine & Novelty Accounting

| Mathematical Result / Reference | Classification | Attribution |
|---|---|---|
| Even perfect numbers $N = 2^{p-1}(2^p - 1)$ | **`N0`** | Euclid (*Elements* IX.36); L. Euler |
| Splitting perfect polynomials $x^{2^n-1}(x+1)^{2^n-1}$ over $\mathbb{F}_2[x]$ | **`N0`** | E. F. Canaday (*Duke Math. J.*, 1941) |
| Odd perfect polynomials over $\mathbb{F}_2[x]$ must be squares | **`N0`** | L. H. Gallardo & O. Rahavandrainy |
| Ducci $2^k$-nilpotence & cyclotomic cycle obstructions | **`N0`** | E. Ducci (1930s); C. Ciamberlini & A. Marengoni (1937) |
| Pentagonal recurrence for $\sigma(n)$ | **`N0`** | L. Euler (1747) |
| $E_2 \leftrightarrow E_4$ divisor-sum convolution | **`N0`** | S. Ramanujan (*Trans. Cambridge Philos. Soc.*, 1916) |
| Refutation of Mozart golden-section bar-count claims | **`N0`** | J. F. Putz (*Mathematics Magazine*, 1995) |
| Unified zero-float pure-$\mathbb{Z}/\mathbb{Q}/\mathbb{F}_2[x]$ bridge oracle, dual raw/mean-square prism certification, carry-obstruction witness, & Zone-B fail-closed auditor | **`N1`** | Original reproducible implementation in `mozart_perfect_bridge_oracle.py`, `mozart_perfect_bridge_audit.py`, and `test_mozart_perfect_bridge_r5.py` |

---

## 3. Exact Certified Quantitative Results

All numbers below are extracted verbatim from `mozart_perfect_bridge_certificate.json`.

### 3.1 Pillar 1 — Frobenius–Ducci, Canaday Splitting (`n = 1..6`), & Euclid–Euler (`p = 2..19`)

- **Mozart $2^n$ Nilpotence:** `K551_4note_CDFE` (`L=4`, `4` steps, $\Delta^4 \bmod (x^4+1) = 0$), `K545_Alberti_4` (`L=4`, `4` steps), `K551_8note` (`L=8`, `7` steps), `K550_8note` (`L=8`, `8` steps).
- **Canaday $A_n(x) = x^{2^n-1}(x+1)^{2^n-1}$:** `n = 1..6` $\to$ exact degrees `[2, 6, 14, 30, 62, 126]`, all `6/6` satisfy $(x+1)^{2^n} = x^{2^n}+1$, $\sigma(x^{2^n-1})=(x+1)^{2^n-1}$, $\sigma((x+1)^{2^n-1})=x^{2^n-1}$, and $\sigma(A_n)=A_n$ (plus direct all-divisor XOR sum for `n = 1, 2, 3`).
- **Euclid–Euler Specialization ($x = 2$):** `p = 2, 3, 5, 7, 13, 17, 19` $\to$ $M_p = 3, 7, 31, 127, 8191, 131071, 524287$ (all prime) $\to$ $N = 6, 28, 496, 8128, 33550336, 8589869056, 137438691328$ (all $\sigma(N) = 2N$).
- **Composite $m = 4$ Contrast:** $\mathbb{F}_2[x]$ has $x^4+1=(x+1)^4$ primary ($A_2$ perfect), whereas $\mathbb{Z}$ has $2^4-1=15=3\cdot 5$ composite and $N=120$ abundant ($\sigma(120)=360 \ne 240$, excess `+120`).

### 3.2 Pillar 2 — Cyclotomic Factorization, $\mathbb{F}_2[x]$ Square Theorem, & $\mathbb{Z}$ Carry Obstruction

- **Non-$2^k$ Mozart Obstructions:** `K550_3note_sigh` (`L=3`, divisors `[1, 3]`, period `3`), `F2_impulse_L5` (`L=5`, divisors `[1, 5]`, period `15`), `K331_6_8_bar` (`L=6`, divisors `[1, 2, 3, 6]`, period `6`); all odd $\Phi_d$ coprime to $\Delta = S+1$ in $\mathbb{F}_2[S]$.
- **Cyclotomic $\sigma(p^a)$ Factorization:** `24/24` exact in $\mathbb{Z}$ (`p in {2,3,5,7}`, `a in 1..6`); `15/15` exact in $\mathbb{F}_2[x]$.
- **$\mathbb{F}_2[x]$ Odd Perfect Square Theorem:** All `21` odd irreducibles of degree `2..6` × `a in {1, 3, 5}` (`63/63` cases) satisfy $x(x+1) \mid (P+1) \mid \sigma(P^a)$; `6/6` explicit non-square odd composite products blocked.
- **$\mathbb{Z}$ Carry-Propagation Obstruction:** All `6/6` Euler primes $q \in \{5, 13, 17, 29, 37, 41\}$ ($q \equiv 1 \pmod 4$) give $v_2(\sigma(q^1)) = v_2(\sigma(q^5)) = 1$, contrasted with all `4/4` $q \equiv 3 \pmod 4$ controls (`3, 7, 11, 19`) giving $v_2(q+1) \in \{2, 3, 2, 2\} \ge 2$. Integer OPN remains open.

### 3.3 Pillar 3 — Nyquist-4 $\sigma(n)$ Prism, Euler Pentagonal Annihilator, & Ramanujan Convolution

| Sequence | $L$ | $E_1$ | $E_2$ | Raw $R_2 = E_2/E_1$ | Raw $R_2..R_5$ (dec6) | Mean-Square $R_2^{\mathrm{ms}}..R_5^{\mathrm{ms}}$ (dec6) |
|---|---:|---:|---:|---:|---|---|
| `quadratic_n2_1_to_32` | `32` | `43679` | `120` | `120/43679` | `0.002747, 0, 0, 0` | `0.002839, 0, 0, 0` |
| `K550_phrase_20` | `20` | `87` | `161` | `161/87` | `1.850575, 2.739130, 3.081633, 3.300957` | `1.953384, 2.900256, 3.274235, 3.521020` |
| `K545_Alberti_16` | `16` | `415` | `1432` | `1432/415` | `3.450602, 3.664804, 3.731707, 3.696078` | `3.697074, 3.946713, 4.042683, 4.032086` |
| `sigma_1_to_32` | `32` | `10016` | `35739` | `35739/10016` | `3.568191, 3.562663, 3.510642, 3.486971` | **`3.687131, 3.685513, 3.636022, 3.616118`** |

- **Euler Pentagonal Annihilator:** `100/100` exact zero residuals (`n = 1..100`), $\Delta^2 p_k^+ \equiv \Delta^2 p_k^- \equiv 3$, $\Delta^3 \equiv 0$, Alberti period-4 sign kernel $(S^2+I)([+1,+1,-1,-1]^4) = 0$ and $(S^4-I) = 0$.
- **Ramanujan $E_2 \leftrightarrow E_4$ Convolution:** General identity $12\sum \sigma(k)\sigma(n-k) = 5\sigma_3(n) + (1-6n)\sigma(n)$ holds `64/64` (`n = 1..64`); perfect-number specialization $2n(1-6n)$ holds on `1..64` iff $n \in \{6, 28\}$; exact perfect-number witnesses: `6 -> 840`, `28 -> 116,208`, `496 -> 694,330,560`.

### 3.4 Pillar 4 — Adversarial Law-5 Anti-Numerology Control

- **Transposition Control (`K.545` Alberti, shifts `0, 1, 5, 7, 12`):** Stage-B energies & ratios `5/5` identical; Stage-A C-pitch-class count breaks (`4 -> 0, 8, 0`) on non-octave transpositions.
- **Radix Control (`6, 28, 496` across bases `2, 8, 10, 12, 16`):** Stage-B $\sigma(N)=2N$ holds `5/5`; Stage-A base-10 ending-in-`6/8` artifact breaks in bases `2` (`[0,0,0]`), `8` (`[6,4,0]`), `12` (`[6,4,4]`), and `16` (`[6,12,0]`).
- **Golden-Section Refutation:** Proven rational bracket $\phi^{-1} \in [618033/1000000, 618034/1000000]$; `K.282_I`, `K.283_I`, `K.332_I`, `K.576_I` all fail exact zero defect (`-99, -1871, -2801, +1124`) and deviate by `> 2%`.

---

## 4. Zone-B Security Architecture & Honest Threat Boundary

- **Binding `3,321`-Bit Integer/Rational Cap & `4,300`-Digit Immunity:** `MAX_INT_BITS = 3_321` and `MAX_RATIONAL_BITS = 3_321` are the binding fail-closed enforcement caps, paired with a necessary (not sufficient) pre-parse decimal-length cap `MAX_INT_DIGITS = 1_000` (`len(str((1 << 3321) - 1)) == 1000`, far below Python's `4,300`-digit `int -> str` threshold even under `format_decimal(..., 12)`). Integers with `1,000` digits exceeding $2^{3321} - 1$ (such as $10^{1000} - 1$, which has `3,322` bits) pass the digit-length check and fail closed cleanly at the binding `3,321`-bit cap with `INT_BIT_LIMIT`, guaranteeing zero uncaught `ValueError` and full round-trip acceptance for every integer in $[-(2^{3321}-1),\, 2^{3321}-1]$ across `parse_strict_json_text` (with explicit `max_bytes` UTF-8 byte cap), `canonical_json_bytes`, `format_rational`, `format_decimal`, and `parse_exact_rational`. `is_prime_exact` enforces an explicit upper bound `MAX_PRIME_CHECK = 10_000_000` (`INT_OUT_OF_RANGE`) to prevent trial-division CPU exhaustion.
- **Durable `0o600` Atomic `dir_fd` I/O:** `read_regular_bytes_capped` traverses ancestors atomically via `dir_fd` `O_RDONLY | O_DIRECTORY | O_NOFOLLOW` (plus atomic `dir_fd` `_check_pwd_no_symlinks` and deleted-CWD `CWD_UNAVAILABLE`), opens leaf with `O_NOFOLLOW | O_NONBLOCK`, enforces `fstat S_ISREG`, and streams in `65,536`-byte chunks (`max_bytes <= 64 MiB`). `write_regular_bytes_safe` validates `type(payload) is bytes`, checks target `dir_fd` `lstat` (`SYMLINK_FORBIDDEN`, `NOT_A_REGULAR_FILE`, `HARDLINK_FORBIDDEN` for `st_nlink > 1`), creates an exclusive `0o600` temp file using `_TEMP_NAME_LOCK` + monotonic counter + `secrets.token_hex(8)` (`O_CREAT | O_EXCL | O_NOFOLLOW | O_NONBLOCK`, bounded `64`-retry `EEXIST`), calls `os.fsync(fd)`, verifies pre-replace `os.fstat(fd).st_nlink == 1`, executes `os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd)`, and calls `os.fsync(dfd)`.
- **Honest Same-UID POSIX Threat Boundary:** POSIX has no atomic kernel primitive combining `renameat` with simultaneous link-count enforcement; a concurrent same-UID attacker with write access to the target directory can create a hardlink in the narrow window between `lstat`/`fstat` and `os.replace`. Even in that race, `os.replace` swaps the directory entry to the new temp inode rather than mutating an existing linked inode in place, preventing in-place clobber of linked sentinels. Full defense against a malicious same-UID process requires OS-level directory isolation (`0700` owned directory or distinct UIDs).
- **Honest Verification Boundary (`--check` & Field-Complete Strict-Keyset Secondary Audit):** `verify_certificate_dict(..., full_replay=True)` performs canonical ASCII+LF framing checks, constant-time `hmac.compare_digest` over both `payload_sha256` and `certificate_sha256`, and field-complete strict nested-keyset, type-tree (`_validate_json_tree`), shift-bound, primality-bound, non-negative energy, and algebraic `secondary_audit_payload` enforcement across all `513` payload leaves (pinning exact case IDs, exponents before shifts, Mersenne/Euler/control primes before trial division, spectral prism lengths/energies/ratios/`dec6`, Ramanujan $5\sigma_3(n) + (1-6n)\sigma_1(n)$, Stage-A/B transposition/radix values, and golden-ratio `> 2%` $\phi^{-1}$ brackets even under `full_replay=False` and direct `secondary_audit_payload`), plus deterministic full oracle replay via `mozart_perfect_bridge_oracle.build_payload()`. Because `audit` imports `oracle`, `--check` is deterministic replay plus intra-package secondary algebraic cross-check rather than a zero-shared-code independent oracle.

---

## 5. Post-Last-Edit Sequential Verification Receipts & Frozen Manifest

All gates ran strictly sequentially (`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1`) after the final code edit:

| Gate | Scope | Exact Result |
|---|---|---|
| **Unit & Adversarial Suite** | `test_mozart_perfect_bridge_r5.py` (`7` test methods, incl. `67` re-signed `full_replay=False` + direct `secondary_audit_payload` tamper kills & live CLI DoS checks) | **`7/7` PASS** (`0` bare asserts, `0` AST floats/`float()`, `0` `.isdigit()`) |
| **3-Mode Isolated Parity + `PYTHONHASHSEED=42`** | `-I -B`, `-I -O -B`, `-I -B -W error` (plus `-I -O -B -W error` and `PYTHONHASHSEED=42 -B` without `-I`) | **100% bit-identical** (`3c6b226b43804befdd102a4f02800421087ed851009967bc20b2e72479ce336e`), `--check --json` `c9aed388...`, unit suite OK across all modes |
| **Exhaustive Re-Signed Leaf & DoS Sweep** | All `513` payload leaves (`3,756` checks across `FR=False` + `secondary_audit_payload`, incl. `-1`, `0`, `1<<40`, `10**18+3`, `10**18+9`, `1/0`, `SubStr`, + `10` live CLI `--check` DoS certs) | **`0` accepted, `0` raw crashes, `0` timeouts, `0` `rc=1` tracebacks** |
| **Live `aletheia v2.0.0 mutate` (`--max-mutants 0`)** | `mozart_perfect_bridge_oracle.py` + `mozart_perfect_bridge_audit.py` (`--guards require_ok`) | **`43/43` + `76/76` = `119/119` (`100.0%`, `survived=0`, `truncated=False`)** |
| **Whole-File `OP_SWAP + SUBCOND_DEL` AST `BoolOp`** | `mozart_perfect_bridge_oracle.py` + `mozart_perfect_bridge_audit.py` | **`6/6` + `24/24` = `30/30` (`100.0%`, `surv=[]`)** |
| **Live 4-Surface Zone-B Fuzzer** | CLI (`23`) + `verify(full_replay=True)` (`18`) + `verify(full_replay=False)` (`18`) + `secondary_audit_payload` (`18`) | **`77/77` (`100.0%`, `bypasses=0`, `crashes=0`)** |
| **Concurrency & Kernel Races** | `16T` distinct (`0o600`) + `16T` same + `80T` burst + `550` `renameat2(RENAME_EXCHANGE)` + `550` hardlink race | **`0` errors, `0` leaks, `0` clobbers, `0` leftover `.tmp`** |
| **`aletheia v2.0.0 audit-check`** | `--strict-ancestors --safety-scan --scripts mozart_perfect_bridge_audit.py test_mozart_perfect_bridge_r5.py` | **`PASS`** (`5` files, `2/2` scripts, `0` findings, `0` host-path/private-repo leaks, `0` `.pyc`) |

### Frozen Code & Certificate Manifest

| File | Lines | Bytes | SHA-256 |
|---|---:|---:|---|
| `mozart_perfect_bridge_oracle.py` | `1073` | `41220` | `bb80021fd1f750612f0d1ee8c2054c2255d6585b6f492c2ce684e5445ac45b62` |
| `mozart_perfect_bridge_audit.py` | `1225` | `52536` | `4f65fdf266c0fa9b694dc3f1865a9d88e7bcbd6876b2887a6364fc1cf7fcd917` |
| `test_mozart_perfect_bridge_r5.py` | `813` | `49211` | `87e025ef6bef556dbdbcac9307db41052e268b0b2748d8e8a84fd847d0ac3d25` |
| `mozart_perfect_bridge_certificate.json` | `1` | `11634` | `3c6b226b43804befdd102a4f02800421087ed851009967bc20b2e72479ce336e` |
| `MOZART_PERFECT_BRIDGE_REPORT.md` | (this report) | — | See directory manifest on freeze |
