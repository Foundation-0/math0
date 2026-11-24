# Track S22a: Exact Quasi-Modular $E_2 \leftrightarrow E_4$ (`E_8` Theta Series) Convolution Operator, Lucas–Lehmer Certificates & Aliquot Dynamics

- **Track ID:** `TRACK-S22A-PERFECT-QUASI-MODULAR-BRIDGE`
- **Oracle Class:** `exact` (100% pure Python 3 stdlib `int` + `fractions.Fraction`; zero AST floats, zero `float()` calls, zero bare `assert`s, zero mathematical RNG — CSPRNG `secrets.token_hex` used exclusively for atomic temp filenames; zero external dependencies)
- **Honest Law-4 Novelty Classification:** **`N1`** (clean-room zero-float exact $\mathbb{Z}/\mathbb{Q}$ verifier uniting Ramanujan's quasi-modular differential algebra with the perfect-defect $E_8$-shell operator, Leech $\Theta_{\Lambda_{24}}$ theta series, Euclid–Euler / Lucas–Lehmer certificates, complete elementary LTE algebraic prime-power driver classification, and Zone-B hardened certification; all classical theorems strictly quarantined as **`N0`** below)
- **Canonical Certificate Digests (`perfect_quasi_modular_certificate.json`, `0o600`, LF-only):**
  - File / zero-arg / `--standalone --json` SHA-256: `cb4b8e17feea332a3928f43df500b55ebb68d0d49869683cc730a8ffe9ad7166` (`4,887` B)
  - `payload_sha256`: `231f37b886e7cdedfd421f722e6ca2d15143cff99f859299d3dd358579380b49`
  - `certificate_sha256`: `dbc0c5c597505bb238b993df2dd054b561bc4f80f2ea4ff7131caa177193ebbd`
  - `--check` stdout SHA-256: `86053a13bb3ffd01b64e7244e5256a6a167d6d2a2dd1484c3a98020c9d0272d7`

---

## 1. Strict Law-4 `N0` Prior-Art Quarantine

Every classical theorem and upstream result verified here is explicitly quarantined as **`N0`**:

| Classical Result | Primary Prior Art (`N0`) | Role in Track S22a |
|---|---|---|
| Even perfect number characterization $N = 2^{p-1}(2^p - 1)$ | Euclid (*Elements* IX.36, ~300 BCE); Euler (1747) | Theorem 2 exact bijection & divisor-sum checks |
| Lucas–Lehmer primality test & $\mathbb{Z}[\sqrt{3}]$ trace recurrence | Lucas (1878); Lehmer (1930) | Theorem 2 pure-$\mathbb{Z}$ certificates up to $M_{127}$ |
| Euler divisor law $q \equiv 1 \pmod{2p}$, $q \equiv \pm 1 \pmod 8$ & $M_{67}$ factorization | Euler (1750); F. N. Cole (1903) | Theorem 2 composite Mersenne counterexamples |
| Quasi-modular Eisenstein ODEs ($E_2, E_4, E_6, \Delta$) & $5\sigma_3 + (1-6n)\sigma_1 = 12\sum \sigma_1(k)\sigma_1(n-k)$ | Ramanujan (1916); Serre (1973); Kaneko–Zagier (1995) | Theorem 1 $q$-series algebra & perfect-defect bridge |
| $E_8$ theta series $\Theta_{E_8} = E_4$ & Leech theta series $\Theta_{\Lambda_{24}} = E_4^3 - 720\Delta$ | Conway–Sloane (1988); Hecke (1937) | Theorem 1 $E_8$ & Leech $\Lambda_{24}$ shell-count bridge |
| Amicable pairs, Poulet 5-cycle (`12496`) & 28-cycle (`14316`), Lehmer-Five (`276`), aliquot drivers, Lifting-the-Exponent (LTE) | Paganini (1866); Poulet (1918); Guy–Selfridge (1975); Catalan–Dickson conjecture | Theorem 3 cycle certificates, LTE driver classification, & `276` trajectory |

---

## 2. Theorem 1 — Exact Quasi-Modular $E_2 \leftrightarrow E_4$ (`E_8` Shell) Convolution & Leech Bridge

Over the exact truncated polynomial ring $\mathbb{Z}[q]/(q^{37})$ (`deg = 36`), with $E_2(q) = 1 - 24\sum \sigma_1(n)q^n$, $E_4(q) = 1 + 240\sum \sigma_3(n)q^n = \Theta_{E_8}(q)$, $E_6(q) = 1 - 504\sum \sigma_5(n)q^n$, $E_8(q) = 1 + 480\sum \sigma_7(n)q^n$, and $\theta = q\frac{d}{dq}$:

1. **All Three Ramanujan Quasi-Modular ODEs & $E_4^2 = E_8$ Verified Coefficient-by-Coefficient (`n = 0..36`, zero residual):**
   $$12\theta E_2 = E_2^2 - E_4, \qquad 3\theta E_4 = E_2 E_4 - E_6, \qquad 2\theta E_6 = E_2 E_6 - E_4^2, \qquad E_4^2 = E_8.$$
2. **Exact Perfect-Defect $E_8$-Shell Operator Characterization (`n = 1..36`):**
   Equating $[q^n]$ in $12\theta E_2 = E_2^2 - E_4$ yields $5\sigma_3(n) + (1 - 6n)\sigma_1(n) = 12\sum_{k=1}^{n-1}\sigma_1(k)\sigma_1(n-k)$. Writing the perfect defect $\delta_{\mathrm{perf}}(n) := \sigma_1(n) - 2n$:
   $$5\sigma_3(n) - 2n(6n-1) - 12\sum_{k=1}^{n-1}\sigma_1(k)\sigma_1(n-k) = (6n - 1)\,\delta_{\mathrm{perf}}(n).$$
   Because $6n - 1 \ge 5 > 0$ for every $n \ge 1$, the left-hand side vanishes **if and only if** $n$ is perfect, directly tying perfect numbers to the $E_8$ shell count $r_{E_8}(n) = 240\sigma_3(n)$:

   | $n$ | Class | $\sigma_1(n)$ | $\delta_{\mathrm{perf}}(n)$ | $\sigma_3(n)$ | $r_{E_8}(n) = 240\sigma_3(n)$ | $\sum_{k=1}^{n-1}\sigma_1(k)\sigma_1(n-k)$ | Exact Operator Residual $(6n-1)\delta_{\mathrm{perf}}(n)$ |
   |---:|---|---:|---:|---:|---:|---:|---:|
   | `1` | Deficient | `1` | `-1` | `1` | `240` | `0` | `-5` |
   | **`6`** | **Perfect** | `12` | **`0`** | `252` | **`60,480`** | `70` | **`0`** |
   | `10` | Deficient | `18` | `-2` | `1,134` | `272,160` | `384` | `-118` |
   | `12` | Abundant | `28` | `+4` | `2,044` | `490,560` | `686` | `+284` |
   | **`28`** | **Perfect** | `56` | **`0`** | `25,112` | **`6,026,880`** | `9,684` | **`0`** |

   - **Quasi-Modular Anomaly Negative Control:** Dropping the quasi-modular term $(1-6n)\sigma_1(n)$ (treating $E_2$ as if modular) fails immediately with exact missing anomaly `5` at $n=1$ and `420` at $n=6$.
3. **Exact Discriminant $\Delta(q)$ & Leech Lattice Theta Series $\Theta_{\Lambda_{24}}(q)$ Bridge:**
   - $(E_4^3 - E_6^2)$ is exactly divisible by `1728` at every degree $0 \le n \le 36$, and $\Delta = (E_4^3 - E_6^2)/1728$ matches the Euler product $q\prod_{m=1}^{36}(1-q^m)^{24}$ identically ($\tau(1..6) = [1, -24, 252, -1472, 4830, -6048]$, plus exact Hecke multiplicativity at $n \in \{6, 10, 15\}$ and prime-square recurrences $\tau(p^2) = \tau(p)^2 - p^{11}$ at $p \in \{2, 3, 5\}$).
   - $\Theta_{\Lambda_{24}}(q) = E_4^3 - 720\Delta = (7 E_4^3 + 5 E_6^2)/12$ holds identically for $n = 0..36$, giving exact shell counts **`[1, 0, 196560, 16773120, 398034000]`** (zero roots at $[q^1]$, exact Leech kissing number `196,560` at $[q^2]$).

---

## 3. Theorem 2 — Euclid–Euler Bijection & Pure-$\mathbb{Z}$ Lucas–Lehmer Certificates

1. **First 12 Mersenne Primes & Even Perfect Numbers Certified (`p ∈ {2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127}`):**
   - Pure-$\mathbb{Z}$ Lucas–Lehmer recurrence $s_0 = 4$, $s_{k+1} = (s_k^2 - 2) \bmod M_p$ certifies $s_{p-2} \equiv 0 \pmod{M_p}$ up to Lucas's 39-digit $M_{127} = 2^{127} - 1$ (77-digit even perfect number `14474011154664524427946373126085988481573677491474835889066354349131199152128`), with exact Euclid–Euler coprimality & divisor identity $\sigma_1(2^{p-1})\sigma_1(M_p) = 2 N_p$.
   - Independent exact factorization verifies $\sigma_1(N_p) = 2N_p$ directly for $p \in \{2, 3, 5, 7, 13\}$; an exhaustive integer sieve over $1 \le n \le 10{,}000$ returns strictly `[6, 28, 496, 8128]` (zero odd perfect numbers $\le 10{,}000$).
   - Exact $\mathbb{Z}[\sqrt{3}]$ algebraic trace invariant $s_k \equiv \omega^{2^k} + \bar{\omega}^{2^k} \pmod{M_p}$ ($\omega = 2 + \sqrt{3}$) verified step-by-step for $p \in \{3, 5, 7, 11, 13\}$ (with step-0 sign-flip negative control $s_0 = -4 \equiv 27 \pmod{31}$ reconverging at $k=1$ to verify intermediate step checking).
2. **Five Composite Prime-Exponent Mersenne Counterexamples (Exact Factorizations + Divisibility + Euler Congruences + Pinned Nonzero LL Residues):**
   - $M_{11} = 2047 = 23 \times 89$ (`LL = 1736`)
   - $M_{23} = 8{,}388{,}607 = 47 \times 178{,}481$ (`LL = 6107895`)
   - $M_{29} = 536{,}870{,}911 = 233 \times 1{,}103 \times 2{,}089$ (`LL = 458738443`)
   - $M_{37} = 137{,}438{,}953{,}471 = 223 \times 616{,}318{,}177$ (`LL = 117093979072`)
   - $M_{67} = 2^{67}-1 = 193{,}707{,}721 \times 761{,}838{,}257{,}287$ (Cole 1903; `LL = 44350645312365507266`)
   - `verify_mersenne_factor_euler(p, q)` enforces odd prime $p$, prime $q$, exact divisibility $2^p \equiv 1 \pmod q$ (`pow(2, p, q) == 1`, rejecting non-divisors such as $q = 199$ for $p = 11$ and composite divisors such as $q = 2047$), $2p \mid (q-1)$, and $q \equiv \pm 1 \pmod 8$.

---

## 4. Theorem 3 — Exact Aliquot Dynamics, Prime-Power Driver Classification (LTE Proof) & Open Lehmer-5 `276`

1. **Exact Cycle & Control Certificates (`s(n) = \sigma_1(n) - n`):**
   - **Order-1 fixed points:** `6`, `28`, `496`, `8128`.
   - **Order-2 amicable pairs (`5/5`):** `(220, 284)`, `(1184, 1210)`, `(2620, 2924)`, `(5020, 5564)`, `(6232, 6368)`.
   - **Poulet order-5 sociable cycle:** `12496` (`min=12496`, `max=15472`, 5 distinct vertices, exact closure).
   - **Poulet order-28 sociable cycle:** `14316` (`min=14316`, `max=629072`, 28 distinct vertices, exact closure).
   - **Terminating & aspiring controls:** `12 -> 16 -> 15 -> 9 -> 4 -> 3 -> 1 -> 0` and `95 -> 25 -> 6 -> 6`.
2. **Exact Elementary Classification of Prime-Power Guy–Selfridge Drivers (`d = 2^a v`, `v = 1` or `p^e` odd — Exact LTE Proof):**
   Requiring (i) $v \mid (2^{a+1} - 1)$ and (ii) $2^{a-1} \mid \sigma_1(v)$:
   - **$v = 1$:** $2^{a-1} \mid 1 \implies a = 1 \implies \mathbf{d = 2}$ (downdriver).
   - **$v = p^e$ with even $e \ge 2$:** $\sigma_1(p^e) = 1 + p + \dots + p^e$ is a sum of $e + 1$ odd terms, hence odd, forcing $2^{a-1} \mid \sigma_1(p^e) \implies a = 1$ and $p^e \mid (2^2 - 1) = 3$, impossible since $p^e \ge 9 > 3$.
   - **$v = p^e$ with odd $e \ge 3$ (Exact Lifting-the-Exponent Proof):** Because $p$ is odd and $e + 1$ is even, Lifting the Exponent gives the exact identity
     $$v_2(\sigma_1(p^e)) = v_2\!\left(\frac{p^{e+1} - 1}{p - 1}\right) = v_2(p + 1) + v_2(e + 1) - 1,$$
     so $2^{a-1} \le 2^{v_2(\sigma_1(p^e))} \le \frac{(p + 1)(e + 1)}{2}$ and therefore $2^{a+1} = 4\cdot 2^{a-1} \le 2(p + 1)(e + 1)$. Condition (i) yields the **unconditional exact LTE bound**:
     $$p^e \le 2^{a+1} - 1 < 2(p + 1)(e + 1).$$
     This eliminates every odd prime $p \ge 3$ and odd $e \ge 3$ completely:
     - **Unique finite bound exception $(p, e) = (3, 3)$** ($3^3 = 27 < 32 = 2\cdot 4\cdot 4$): here $v_2(\sigma_1(27)) = v_2(40) = 3 = v_2(4) + v_2(4) - 1$, forcing $a \le 4$, and $27 \nmid (2^{a+1} - 1)$ for every $a \in \{1, 2, 3, 4\}$ (`3, 7, 15, 31`).
     - **$p = 3$, odd $e \ge 5$:** at $e = 5$, $3^5 - 2(3+1)(5+1) = 243 - 48 = 195 > 0$; each step $e \to e + 2$ adds $8\cdot 3^e \ge 1944$ to $3^e$ versus only $16$ to $8(e + 1)$, so $3^e > 2(3+1)(e+1)$ for all odd $e \ge 5$.
     - **$p \ge 5$, $e = 3$:** $p^3 - 2(p + 1)(3 + 1) = p^3 - 8p - 8 = (p - 5)(p^2 + 5p + 17) + 77 \ge 77 > 0$ for all $p \ge 5$.
     - **$p \ge 5$, odd $e \ge 5$:** starting from $p^3 > 8(p+1)$, each step $e \to e + 2$ multiplies the LHS by $p^2 \ge 25$ while multiplying the RHS by $(e + 3)/(e + 1) \le 3/2$, preserving $p^e > 2(p + 1)(e + 1)$ inductively for all odd $e \ge 3$.
   - **$v = p$ odd prime:** $p = k\cdot 2^{a-1} - 1 \le 4\cdot 2^{a-1} - 1 \implies k \in \{1, 2, 3, 4\}$. Exact linear combinations prove:
     - $k = 1$: $(2^{a+1}-1) - 4(2^{a-1}-1) = 3 \implies p \mid 3 \implies p=3, a=3 \implies \mathbf{d = 24}$ (unique non-perfect prime-power driver),
     - $k = 2$: $(2^{a+1}-1) - 2(2^a-1) = 1 \implies p \mid 1$ (impossible for all $a \ge 1$),
     - $k = 3$: $3(2^{a+1}-1) - 4(3\cdot 2^{a-1}-1) = 1 \implies p \mid 1$ (impossible for all $a \ge 1$),
     - $k = 4$: $p = 2^{a+1}-1$ Mersenne prime $\implies d = 2^a(2^{a+1}-1)$ (**all even perfect numbers**).
   - Cross-checked exhaustively for all $1 \le a \le 24$ (finding strictly `{2, 24}` plus the 7 even perfect numbers with $p \le 25$), alongside the three composite 3-perfect drivers `120 = 2^3·15`, `672 = 2^5·21`, `523776 = 2^9·1023` and non-driver guide `12 = 2^2·3` (rejected since $3 \nmid 7$).
3. **Open Lehmer-5 `276` Exact 26-Term Driver Trajectory (`a_0 = 276` .. `a_25 = 465,780`):**
   - `k = 0..4`: `276 -> 396 -> 696` (hits abundant driver **`24 = 2^3·3`** at `k=2`) `-> 1104 -> 1872`.
   - `k = 5..7`: `3770 -> 3790 -> 3050` (downdriver **`2`** pulls the orbit down).
   - `k = 8..25` (**18 consecutive steps**): `2716 -> 2772 -> 5964 -> ... -> 465780` locks onto the **even-perfect driver `28 = 2^2·7`** with exact $v_2(a_k) = 2$ at every step, obeying the exact persistence law $s(28m) = 28(2\sigma_1(m) - m)$ (odd cofactor $2\sigma_1(m)-m$) across `k = 8..18`.
   - Exact first-step abundancies for all five open Lehmer-Five seeds: `276` (`56/23`), `552` (`60/23`), `564` (`112/47`), `660` (`168/55`), `966` (`384/161`) — all strictly $> 2$. *(Honest boundary: boundedness of the `276` aliquot sequence remains an open problem; this oracle certifies only the exact finite prefix $a_0 \dots a_{25}$ and driver mechanism.)*

---

## 5. Zone-B Security Hardening & Honest Threat Model

### Hardening Controls Implemented
- **Atomic `dir_fd` Traversal & Bounded Streaming Reads:** Component-by-component `dir_fd` `O_RDONLY | O_DIRECTORY | O_NOFOLLOW` traversal (`_open_parent_dir_fd` & `_check_pwd_no_symlinks`), leaf `O_RDONLY | O_NOFOLLOW | O_NONBLOCK` + `fstat S_ISREG` + `65,536`-byte streaming `read_regular_bytes_capped` (`1 <= max_bytes <= 64 MiB`), and deleted-CWD `CWD_UNAVAILABLE` wrapping.
- **Hardlink-Safe Durable Atomic Writer (`write_regular_bytes_safe`):** Enforces `type(data) is bytes` before opening descriptors, checks target `os.lstat(leaf, dir_fd=dfd)` (`SYMLINK_FORBIDDEN`, `NOT_A_REGULAR_FILE`, `st_nlink > 1 -> HARDLINK_FORBIDDEN`), creates temp siblings under `threading.Lock()` + monotonic sequence + `secrets.token_hex(8)` with 16-attempt `EEXIST` retry (`TEMP_EXHAUSTED`) at mode `0o600`, executes `os.fsync(tmp_fd)`, checks pre-replace `os.fstat(tmp_fd)` (`S_ISREG` and `st_nlink == 1`), atomically replaces via `os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd)`, and calls `os.fsync(dfd)`.
- **Strict CLI Argv, Bounded Arithmetic & Full-Cardinality Secondary Audit:**
  - `perfect_quasi_modular_audit.py` accepts ONLY exact canonical forms `[]`, `--standalone --json`, `--write [PATH]`, and `--check PATH`, rejecting dash-prefixed or empty paths (`--check --json`), stray/duplicate `--json` flags, and unknown arguments.
  - `is_prime_exact(n)` enforces `0 <= n <= 10**14` (matching `factorize_exact` and `verify_mersenne_factor_euler`), preventing unbounded $O(\sqrt{n})$ trial-division CPU DoS (`is_prime_exact(10**18 + 3)` fails closed instantly with `INT_OUT_OF_RANGE`).
  - `secondary_audit_payload(payload)` invokes `_validate_json_tree_iterative(payload)` upfront (blocking all Python subclasses `_StrSub`/`_IntSub`/`_ListSub`/`_DictSub` and runtime floats on direct API calls), uses short-circuiting `type(comp_list) is list and len(comp_list) == ...` (eliminating eager `len(...)` `TypeError` on scalar tampers across API and live CLI `--check`), and pins every composite Mersenne `ll_nonzero_residue_str` against exact `lucas_lehmer_certificate(exp_p)["final_residue_str"]`.
- **Exact Biconditional Integer Cap & Strict JSON:** `MAX_INT_BITS = 4_000` (`(1 << 4000) - 1` has `1,205` decimal digits `<< 4,300`) is paired with `MAX_INT_DIGITS = 1_205` and strict RFC 8259 ASCII-only `_parse_bounded_int` (rejecting Unicode digits, leading zeros, `-0`), guaranteeing round-trip symmetry between `canonical_json_bytes` and `parse_strict_json_text` with zero risk of hitting Python's 4,300-digit `int`-to-`str` `ValueError`.
- **Honest Scope Boundaries:**
  - *Same-UID POSIX Writer Boundary:* `0o600` temp permissions, `O_EXCL | O_NOFOLLOW`, pre-replace `fstat(tmp_fd).st_nlink == 1`, target `st_nlink <= 1`, and `dir_fd` `os.replace` eliminate unprivileged/cross-user tampering and hardlink clobbering; a co-privileged same-UID local attacker racing the kernel window between `fstat(tmp_fd)` and `os.replace` remains an inherent POSIX kernel boundary unless isolated by OS privilege/mount controls.
  - *Verification Scope:* `--check` / `verify_certificate_dict(..., full_replay=True)` performs deterministic pure-$\mathbb{Z}/\mathbb{Q}$ replay against the bundled oracle plus full-cardinality `secondary_audit_payload` verification (also enforced under `full_replay=False`); it is a self-contained deterministic verifier, not a zero-shared-code independent audit.
  - *Static Hygiene:* All `3/3` `.py` files contain `0` bare `assert`s, `0` AST `float` literals, `0` `float()` calls, and `0` `.isdigit()` calls (`test_perfect_quasi_modular_r5.py` constructs runtime floats via `3 / 2` or JSON `"1.5"`/`"NaN"` strings solely as fail-closed negative controls).

---

## 6. Post-Last-Edit Sequential Verification Receipts & Frozen 5-File Manifest

All checks executed sequentially with `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1`:

- **3-Mode Isolated Parity + Extended Modes (`-I -B`, `-I -O -B`, `-I -B -W error`, plus `-I -O -B -W error` & `PYTHONHASHSEED=42 -B` without `-I`):**
  - Zero-arg & `--standalone --json`: bit-identical `cb4b8e17feea332a3928f43df500b55ebb68d0d49869683cc730a8ffe9ad7166` ×5 (`== disk 0o600`).
  - `--check perfect_quasi_modular_certificate.json`: bit-identical `86053a13bb3ffd01b64e7244e5256a6a167d6d2a2dd1484c3a98020c9d0272d7` ×5 (`valid: true`).
  - `test_perfect_quasi_modular_r5.py`: **`5/5 OK`** ×5 (`16T` distinct + `16T` same-target + `80T` barrier burst + live `os.fsync` temp-hardlink probe + `520`-iter `renameat2(RENAME_EXCHANGE)` + `420`-iter `os.link`/`os.unlink` hardlink race: `0` errors, `0` leaks, `0` clobbers, `0` temp leaks).
- **Exhaustive Leaf + Scalar + Zero-Denominator + Subclass/Float Tamper Sweep:** **`1,291`** mutations across all **`196`** leaves, **`14`** lists, and **`20`** dicts (incl. scalar `0`/`None`/`"12345"`, `"0"`/`"1/0"`, forged LL residues, subclasses, and floats) on both `verify_certificate_dict(full_replay=False)` & direct `secondary_audit_payload` + live CLI `--check` (**`bypasses=0`, `raw_excs=0`**, `0` tracebacks).
- **Live `aletheia v2.0.0 mutate --max-mutants 0 --work-root . --add-cwd --guards require_ok`:** **`2/2` (`audit.py`) + `83/83` (`oracle.py`) = `85/85` (`100.0%`, `survived=0`, `truncated=False`) KILLED**.
- **Whole-File Exhaustive `SWAP + SUBCOND_DEL` AST `BoolOp`:** **`9/9` (`audit.py`, `3` nodes) + `60/60` (`oracle.py`, `20` nodes) = `69/69` (`100.0%`, `survived=[]`) KILLED**.
- **Live 4-Surface Zone-B Fuzzer:** **`23/23` CLI + `18/18` `verify_certificate_dict(full_replay=True)` + `18/18` `verify_certificate_dict(full_replay=False)` + `18/18` `secondary_audit_payload` = `77/77` (`100.0%`, `bypasses=0`, `crashes=0`) `PASS`**.
- **Hygiene:** `aletheia v2.0.0 audit-check . --strict-ancestors --safety-scan --scripts perfect_quasi_modular_audit.py test_perfect_quasi_modular_r5.py` **`PASS`** (`5` files, `2/2` scripts clean across all 3 isolated modes, `0` CRLF, `0` `__pycache__`/`.pyc`, `0` personal-path or private-repo leaks, `0` bare `assert`s, `0` unseeded RNG warnings, `0` safety/ancestor findings).
- **Falsification Criteria:** Fails if any Ramanujan ODE, perfect-defect identity, $\Delta$/Leech coefficient, Lucas–Lehmer certificate, composite Mersenne factorization, Poulet cycle, LTE Guy–Selfridge driver identity, or `276` trajectory step deviates from exact integer arithmetic; if any float enters the JSON certificate; or if any isolated-mode parity, `aletheia mutate`, AST `BoolOp`, Zone-B fuzz, race, or `audit-check` gate fails.

### Frozen 5-File Manifest

| File | Lines | Bytes | Mode | SHA-256 |
|---|---:|---:|:---:|---|
| `perfect_quasi_modular_oracle.py` | 1,557 | 60,426 | `0644` | `6118f2f5c887a99c85b2bb15144ea909265873bfd6046f71074827fe4f9d411c` |
| `perfect_quasi_modular_audit.py` | 105 | 4,216 | `0644` | `3cc2548830fa2ab1104f4a9ac7c8009e920e89979dade604c326cb215bd2f845` |
| `test_perfect_quasi_modular_r5.py` | 886 | 51,951 | `0644` | `996a914f6112e4cf405559caab4463bd3eba5268c8019b1d5fa206efa4ddbf58` |
| `perfect_quasi_modular_certificate.json` | 1 | 4,887 | `0600` | `cb4b8e17feea332a3928f43df500b55ebb68d0d49869683cc730a8ffe9ad7166` |
| `PERFECT_QUASI_MODULAR_REPORT.md` | — | — | `0644` | *(self; verified by 5-file `audit-check`)* |
