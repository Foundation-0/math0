# Track S22b — Odd Perfect Numbers, Cyclotomic Factor Chains, Odd Spoof Algebra, Abundancy Outlaws & Solitary-10 Obstructions (R3)

- **Track ID:** `TRACK-S22B-ODD-PERFECT-CYCLOTOMIC-SPOOFS`
- **Oracle Class:** Pure Python 3 stdlib exact $\mathbb{Z}/\mathbb{Q}$ (`fractions.Fraction`), zero IEEE-754 floats, zero bare `assert`s, zero RNG, Zone-B hardened CLI & verifier (full pure-$\mathbb{Q}$ replay on `--check`)
- **Novelty Rating (Law-4 Honest Accounting):** **`N0` classical number-theoretic re-derivation + `N1` self-contained machine-certified pure-$\mathbb{Z}/\mathbb{Q}$ cyclotomic branch-and-bound proof trees and Zone-B-hardened verification artifact**
- **Certificate Digests (R3, bit-identical to R2):**
  - `payload_sha256`: `f6e98999b0df7c8e14dd3acdfa4c5ecd4666b2d228fc01f78b5e02579ce20a45`
  - `certificate_sha256`: `e2b9937611a97879d825b3f89c9d943dc594e48763d06b85cfdeb0ad2c8d2972`

---

## 1. Executive Summary & Law-4 Scope Boundaries

Every theorem and refutation tree in this track is derived and checked from first principles over exact integers $\mathbb{Z}$ and exact rationals $\mathbb{Q}$ (`fractions.Fraction`) with no external libraries, no floating-point arithmetic, and no probabilistic primality heuristics (deterministic 12-base Miller–Rabin is provably exact for all $n < 3.317 \times 10^{24}$).

### Strict Separation of Certified Results vs. Open Problems

| Subject | Status in Track S22b (R2) | Classical Prior Art (Credited) |
| :--- | :--- | :--- |
| Touchard congruence ($N \equiv 1 \pmod{12}$ or $9 \pmod{36}$) | **CERTIFIED** (exhaustive over $\mathbb{Z}/36\mathbb{Z}$) | Euler; Touchard (1953) |
| Cyclotomic identity $\sigma(q^a) = \prod_{d \mid (a+1), d>1} \Phi_d(q)$ | **CERTIFIED** (`40/40` pairs, `0` mismatches) | Classical cyclotomic algebra |
| Unconditional OPN bound $\omega(N) \ge 5$ | **CERTIFIED** (`1+1+19+907 = 928` nodes, `0` loop fall-offs, `max_table_prime=4999`) | Sylvester (1888); Dickson (1913) |
| $3 \nmid N$ OPN bound $\omega(N) \ge 8$ | **CERTIFIED** (`1+46 = 47` nodes, `0` loop fall-offs, `max_table_prime=4999`) | Sylvester (1888) |
| Odd spoofs across all 3 failure axes (`primality`, `positivity`, `distinctness`) | **CERTIFIED** (`3` exact spoofs & defects) | Descartes (1638); Voight (2003); Andersen–Byrnes–Nielsen |
| Greening solitary numbers $1 \le n \le 30$ (`18` numbers) & `5` friendly clubs | **CERTIFIED** (exact $\gcd(n,\sigma_1(n))=1$ & $I(n)$) | Greening (1956) |
| `11` unconditional abundancy outlaws (`8` Type A + `3` non-trivial Type B) | **CERTIFIED** (exact rational overshoot) | Stanton–Holdener (2007) |
| Existence of an odd perfect number | **OPEN** (not claimed; modern literature $N > 10^{1500}$, $\omega(N) \ge 10$ by Ochem–Rao 2012 / Nielsen 2015 cited only as context) | Open conjecture |
| Abundancy ratio `5/3` | **OPEN** (Weiner 2000 equivalence to OPN with $5 \parallel N$; certified $\omega(n) \ge 4$ in `77` nodes, `0` loop fall-offs) | Weiner (2000) |
| Abundancy ratio `7/5` | **OPEN** (conjectured outlaw; certified odd square, $2,3,7 \nmid n$, $\operatorname{ord}_7(5)=6$, $\omega(n) \ge 5$ in `27+2583` nodes, `0` loop fall-offs) | Stanton–Holdener (2007) |
| Solitary status of `10` ($I(10) = 9/5$) | **OPEN** (smallest undecided integer; certified odd square, $5^2 \mid m$, $3 \nmid m$, $9 \mid \sigma(m)$, $\omega(m) \ge 7$ in `1+8+20217` nodes with `max_table_prime=24989`, **`0` loop fall-offs**, and $\{n \le 50{,}000 : I(n) = 9/5\} = \{10\}$) | Ward (2008) |

---

## 2. Theorem 1 — Euler Form, Touchard Congruence, Cyclotomic Factorization & OPN Branch-and-Bound Obstructions

### 2.1 Touchard Congruence Over $\mathbb{Z}/36\mathbb{Z}$

Any odd perfect number has Euler form $N = p^\alpha m^2$ with odd prime $p \equiv \alpha \equiv 1 \pmod 4$, $\gcd(p, m) = 1$. Exhaustive enumeration over all odd residues $(p \bmod 36, m \bmod 36, \alpha \bmod 12)$ with $p \equiv 1 \pmod 4$, $3 \nmid p$, $\alpha \in \{1, 5, 9\}$ certifies:
- When $3 \mid m$ (hence $3 \mid N$): $N \bmod 36 \in \{9\}$ identically.
- When $3 \nmid m$ (hence $3 \nmid N$): if $p \equiv 2 \pmod 3$ ($p \bmod 36 \in \{5, 17, 29\}$), then $3 \mid (p + 1) \mid \sigma(p^\alpha) \mid 2N$, contradicting $3 \nmid N$. Hence $p \equiv 1 \pmod{12}$ and $N \bmod 36 \in \{1, 13, 25\}$, i.e. $N \equiv 1 \pmod{12}$.

### 2.2 Exact Cyclotomic Factor-Chain Identity

For every $(q, a) \in \{3, 5, 7, 11, 13\} \times \{1, \dots, 8\}$ (`40/40` pairs, `0` mismatches), the oracle certifies over $\mathbb{Z}$ via exact Möbius inversion of $\Phi_d(q)$:
$$\sigma(q^a) = \sum_{j=0}^{a} q^j = \prod_{\substack{d \mid (a+1) \\ d > 1}} \Phi_d(q).$$
Fixing any prime power $q^a \parallel N$ in the search forces every odd prime divisor of $\sigma(q^a)$ (after stripping prime divisors of the target numerator) to divide $N$.

### 2.3 Exact Rational Ceilings for $3 \nmid N$

For an odd integer $N$ with $3 \nmid N$ and $\omega(N) = k$, $I(N) < \prod_{i=1}^{k} \frac{p_i}{p_i - 1}$ where $p_1 < \dots < p_k$ are the first $k$ primes $\ge 5$:

| $\omega(N)$ | Primes $\ge 5$ | Exact Upper Bound $\prod \frac{p}{p-1}$ | Margin $2 - \prod \frac{p}{p-1}$ | Strictly Below $2$? |
| :---: | :--- | :---: | :---: | :---: |
| `5` | `5, 7, 11, 13, 17` | `17017/9216` | `+1415/9216` | **Yes** |
| `6` | `5, 7, 11, 13, 17, 19` | `323323/165888` | `+8453/165888` | **Yes** |
| `7` | `5, 7, 11, 13, 17, 19, 23` | `676039/331776` | `-12487/331776` | **No** (crosses $2$; refuted by cyclotomic B&B) |

### 2.4 Sound Fail-Closed Cyclotomic Branch-and-Bound Refutations & Positive-Control Calibration

Using `solve_abundancy_exact` (pure-$\mathbb{Z}$ exact cross-multiplied lower/upper abundancy bounds, Euler prime assignment, Touchard $p \equiv 1 \pmod{12}$ restriction when $3 \nmid N$ and $3 \nmid \text{num}$, exact cyclotomic prime propagation, fail-closed `PRIME_TABLE_EXHAUSTED` guard on any unclosed prime-loop tail, and fail-closed `UNFACTORED_COFACTOR` guard if any unfactored composite cofactor fits within $\omega$):

| Case | Target | $\omega$ | Constraints | `max_table_prime` | Nodes Explored | Result |
| :--- | :---: | :---: | :--- | :---: | :---: | :--- |
| Unconditional OPN | `2` | `1` | `need_euler=True` | `4999` | `1` | **REFUTED** (`I_hi_undershoot: 1`) |
| Unconditional OPN | `2` | `2` | `need_euler=True` | `4999` | `1` | **REFUTED** (`I_hi_undershoot: 1`) |
| Unconditional OPN | `2` | `3` | `need_euler=True` | `4999` | `19` | **REFUTED** |
| Unconditional OPN | `2` | `4` | `need_euler=True` | `4999` | `907` | **REFUTED** ($\implies \omega(N) \ge 5$) |
| $3 \nmid N$ OPN | `2` | `6` | `need_euler=True, forbid={3}` | `4999` | `1` | **REFUTED** (`I_hi_undershoot: 1`) |
| $3 \nmid N$ OPN | `2` | `7` | `need_euler=True, forbid={3}` | `4999` | `46` | **REFUTED** ($\implies 3 \nmid N \Rightarrow \omega(N) \ge 8$) |

**Fail-Closed Completeness Closure:**
- Every `for q` prime-search loop in `solve_abundancy_exact` enforces `require_ok(broke, "PRIME_TABLE_EXHAUSTED", ...)`, guaranteeing the engine can never fall off `primes_table` and return a false `refuted: True`.
- Every cyclotomic cofactor branch where `len(used) + len(new_ps) + 1 <= omega` enforces `require_ok(cof == 1, "UNFACTORED_COFACTOR", ...)`.
- Negative tests lock `n = 3^2 \cdot 5003^2 = 225{,}270{,}081` (`omega=2, need_euler=False`) and `n = 5 \cdot 5003^2 = 125{,}150{,}045` (`omega=2, need_euler=True`) under default `prime_limit=5000` -> both raise `PRIME_TABLE_EXHAUSTED` (and `prime_limit=6000` recovers `225,270,081`).

**Positive-Control Calibration (`8/8` Exact Recoveries):** To verify the refutation engine never over-prunes valid solutions, the identical `solve_abundancy_exact` routine recovers all `8` planted odd solutions across $\omega \in \{1, 2, 3, 4\}$, Euler and odd-square modes, and $3 \nmid N$:

| Planted $n$ | Exact $I(n)$ | $\omega$ | Mode | Nodes Explored | Recovered |
| :---: | :---: | :---: | :--- | :---: | :---: |
| `9` | `13/9` | `1` | Odd square | `4` | `True` |
| `45` | `26/15` | `2` | Euler | `9` | `True` |
| `117` | `14/9` | `2` | Euler | `16` | `True` |
| `225` | `403/225` | `2` | Odd square | `7` | `True` |
| `325` | `434/325` | `2` | Euler, $3 \nmid n$ | `10` | `True` |
| `5733` | `38/21` | `3` | Euler | `122` | `True` |
| `28125` | `5642/3125` | `2` | Euler | `10` | `True` |
| `693693` | `722/363` | `4` | Euler | `843` | `True` |

---

## 3. Theorem 2 — Exact Odd Spoof Algebra Across All Three Failure Axes

Relaxing the prime-factorization axioms of $\sigma$ to formal multiplicative evaluation $\tilde{\sigma}(\prod_i b_i^{e_i}) = \prod_i \sum_{j=0}^{e_i} b_i^j$ yields exact odd spoof perfect solutions $\tilde{\sigma}(N) = 2N$ spanning all three structural failure axes (`primality`, `positivity`, `distinctness`):

| Spoof | Formal Factorization | Value $N$ | $\tilde{\sigma}(N) = 2N$ | Failure Axes | True $|N|$ Factorization | True $I(|N|) - 2$ | True $|N|$ Class |
| :--- | :--- | :---: | :---: | :--- | :--- | :---: | :--- |
| **Descartes (1638)** | $3^2 \cdot 7^2 \cdot 11^2 \cdot 13^2 \cdot 22021^1$ | `198,585,576,189` | `397,171,152,378` | `primality` ($22021 = 19^2 \cdot 61$) | $3^2 \cdot 7^2 \cdot 11^2 \cdot 13^2 \cdot 19^2 \cdot 61$ | `+1600/11011` | **Abundant** |
| **Voight (2003)** | $3^4 \cdot 7^2 \cdot 11^2 \cdot 19^2 \cdot (-127)^1$ | `-22,017,975,903` | `-44,035,951,806` | `positivity` ($-127 < 0$) | $3^4 \cdot 7^2 \cdot 11^2 \cdot 19^2 \cdot 127$ | `+2/63` | **Abundant** |
| **Andersen–Byrnes–Nielsen (Repeated/Signed)** | $3^2 \cdot 7^2 \cdot 7^2 \cdot (-19)^2 \cdot 13^1$ | `+101,411,037` | `202,822,074` | `positivity`, `distinctness` ($-19 < 0$, $7$ repeated) | $3^2 \cdot 7^4 \cdot 13 \cdot 19^2$ | `-31484/371469` | **Deficient** |

Genuine odd integers underlying spoofs sit on **either** side of $I = 2$: Descartes and Voight yield abundant $|N|$, whereas the positive repeated/signed spoof $101{,}411{,}037$ yields a genuinely **deficient** true integer ($\sigma_1(101{,}411{,}037) - 2 \cdot 101{,}411{,}037 = -8{,}595{,}132$).

---

## 4. Theorem 3 — Greening Solitary Numbers, Friendly Clubs, Outlaws, Open Frontier & Solitary-10

### 4.1 Greening (1956) Solitary Numbers ($1 \le n \le 30$) & Friendly Clubs

- **Greening Criterion ($\gcd(n, \sigma_1(n)) = 1 \implies n$ solitary):** Exactly **`18`** integers in $1 \le n \le 30$:
  `[1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 21, 23, 25, 27, 29]`.
- **Certified Friendly Clubs (`5/5` exact):**
  - $I = 2$: `(6, 28, 496, 8128)`
  - $I = 12/5$: `(30, 140, 2480, 6200, 40640)`
  - $I = 7/3$: `(12, 234)`
  - $I = 5/2$: `(24, 91963648)`
  - $I = 93/40$: `(80, 200)`

### 4.2 Unconditional Abundancy Outlaws (`11` Certified)

1. **Type A — Stanton–Holdener Denominator Overshoot (`8` ratios):** If $\gcd(a, b) = 1$ and $I(b) > a/b$, then any solution $I(n) = a/b$ satisfies $b \mid n \implies I(n) \ge I(b) > a/b$, contradiction.
   Certified ratios: `5/4` ($I(4)=7/4$), `7/6` ($I(6)=2$), `11/6` ($I(6)=2$), `9/8` ($I(8)=15/8$), `11/8`, `13/8`, `11/9` ($I(9)=13/9$), `17/10` ($I(10)=9/5$).
2. **Type B — Non-Trivial Odd-Parity Square-Closure Overshoot (`3` ratios with $I(b) < a/b$):** When $b$ is odd, $\gcd(a, b) = 1$, $I(b) < a/b < I(2b)$, and parity forces every prime $p \mid b$ to appear with even exponent in $n$ (either $a$ odd forcing odd square $n$, or $v_2(a) = 1$ with every prime $p \mid b$ satisfying $p \equiv 3 \pmod 4$ so no $p \mid b$ can have odd exponent since $4 \mid (p+1) \mid \sigma(p^{2k+1})$), $n$ is forced to be divisible by the **exact square-closure** $b_{\mathrm{sq}} = \prod_{p^{e_p} \parallel b} p^{2\lceil e_p / 2 \rceil}$ (which equals $b^2$ if and only if $b$ is squarefree; e.g. for non-squarefree $b = 147 = 3 \cdot 7^2$, $b_{\mathrm{sq}} = 3^2 \cdot 7^2 = 441$ and $I(441) = 247/147$ is an exact friend, so `certify_type_b_odd_square_outlaw(247, 147)` cleanly rejects with `OUTLAW_B_SQ_NO_OVERSHOOT` while `(241, 147)` certifies via $I(441) = 247/147 > 241/147$). Whenever $I(b_{\mathrm{sq}}) > a/b$, $a/b$ is unconditionally an outlaw:
   - **`49/33`:** $I(33)=16/11 < 49/33 < 24/11=I(66)$, odd $49 \implies b_{\mathrm{sq}}(33) = 33^2 \mid n \implies I(n) \ge I(33^2) = 1729/1089 > 49/33$ (overshoot `112/1089`).
   - **`50/33`:** $I(33)=16/11 < 50/33 < 24/11=I(66)$, $v_2(50)=1$ and $3, 11 \equiv 3 \pmod 4 \implies b_{\mathrm{sq}}(33) = 33^2 \mid n \implies I(n) \ge 1729/1089 > 50/33$ (overshoot `79/1089`).
   - **`73/51`:** $I(51)=24/17 < 73/51 < 36/17=I(102)$, odd $73 \implies b_{\mathrm{sq}}(51) = 51^2 \mid n \implies I(n) \ge I(51^2) = 3991/2601 > 73/51$ (overshoot `268/2601`).

### 4.3 Open Frontier Obstructions (`5/3` and `7/5` — Honest Law-4 Classification)

- **`5/3` (`OPEN_EQUIVALENT_TO_OPN_WITH_5_EXACTLY_DIVIDING_N`):**
  By Weiner (2000), $I(n) = 5/3 \iff I(5n) = 2$ with $5 \parallel 5n$. Any solution $n$ is an odd square with $3^2 \mid n$ and $2, 5, 7 \nmid n$ ($I(6)=2, I(225)=403/225, I(441)=247/147 > 5/3$). Elementary product upper bound eliminates $\omega(n) \le 2$ ($\frac{3}{2}\cdot\frac{11}{10} = \frac{33}{20} < \frac{5}{3}$); our exact solver refutes $\omega(n) = 3$ in **`77` nodes** (`0` fall-offs), certifying $\omega(n) \ge 4$.
- **`7/5` (`OPEN_CONJECTURED_OUTLAW`):**
  Any solution $n$ is an odd square with $5^2 \mid n$ and $2, 3, 7 \nmid n$ ($I(10)=9/5, I(15)=8/5, I(1225)=1767/1225 > 7/5$; $\operatorname{ord}_7(5) = 6$ is even, so $7 \nmid \sigma(5^{2a})$). Elementary product upper bound eliminates $\omega(n) \le 2$ ($\frac{5}{4}\cdot\frac{11}{10} = \frac{11}{8} < \frac{7}{5}$); our exact solver refutes $\omega(n) \in \{3, 4\}$ in **`27 + 2583` nodes** (`0` fall-offs), certifying $\omega(n) \ge 5$.

### 4.4 Solitary-`10` Obstructions ($I(10) = 9/5$)

`10` is the smallest positive integer whose solitary status remains open. For any hypothetical friend $m \ne 10$ with $I(m) = 9/5$, Track S22b certifies from first principles:
1. **Parity (`friend_must_be_odd_square = True`, `friend_is_even_square = False`):** If $2 \mid m$, then $10 \mid m \implies I(m) > I(10) = 9/5$ for all $m > 10$. Thus $m$ is odd, hence $\sigma(m) = \frac{9}{5}m$ is odd, forcing $m$ to be an **odd square** with $5^2 \mid m$.
2. **$3 \nmid m$ (`three_cannot_divide_friend = True`):** If $3 \mid m$, then $3^2 5^2 \mid m$. Both $3^4 5^2$ ($I = 3751/2025 > 9/5$) and $3^2 5^4$ ($I = 10153/5625 > 9/5$) overshoot, forcing $3^2 \parallel m$; then $13 = \sigma(3^2) \mid \sigma(m) = \frac{9}{5}m \implies 13^2 \mid m$, which overshoots via $I(3^2 5^2 13^2) = 1891/975 > 9/5$.
3. **$9 \mid \sigma(m)$ and Mod-3 Constraint:** Since $3 \nmid m$ and $5 \sigma(m) = 9m$, we have $v_3(\sigma(m)) = 2$ exactly. For any prime $p \equiv 2 \pmod 3$, $\sigma(p^{2a}) \equiv 1 \pmod 3$ (certified across $a \in \{1..6\}$), so every factor of $3$ in $\sigma(m)$ comes from primes $p \equiv 1 \pmod 3$.
4. **Ward-Style $\omega(m) \ge 7$ Unconditional Refutation (`0` Loop Fall-Offs):** Elementary product bound eliminates $\omega(m) \le 4$ ($\frac{5}{4}\cdot\frac{7}{6}\cdot\frac{11}{10}\cdot\frac{13}{12} = \frac{1001}{576} < \frac{9}{5}$); `solve_abundancy_exact(Fraction(9,5), k, need_euler=False, forbid_primes={3}, force_primes=(5,), require_v3_sigma=2)` refutes $k = 4$ (`1` node, `max_table_prime=4999`), $k = 5$ (`8` nodes, `max_table_prime=4999`), and $k = 6$ (**`20,217` nodes, `prime_limit=25000`, `max_table_prime=24989`** — closing the `{5,7,11,13,29}` branch up through its exact upper bound `q < 20,736` with **`next_prime_upper_bound: 25` and `0` fall-offs**), certifying **$\omega(m) \ge 7$**.
5. **Exhaustive Exact Integer Sieve (`1 .. 50,000`):** Exact divisor-sum sieve certifies $\{1 \le n \le 50{,}000 : 5\sigma_1(n) = 9n\} = \{10\}$.

---

## 5. Verification, Mutation & Zone-B Security Receipts (R3)

All verification gates ran sequentially under `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1` with zero `__pycache__`, zero temp leaks, and zero network/GitHub writes. Note that `--check` performs a **full pure-$\mathbb{Q}$ replay** against `odd_perfect_cyclotomic_oracle.compute_s22b_payload()` followed by constant-time `hmac.compare_digest` over canonical LF-only JSON bytes (independent zero-shared-code re-derivation is performed by external verifiers).

- **5-Mode Isolated `-I` Parity (`-I -B`, `-I -O -B`, `-I -B -W error`, `-I -O -B -W error`, `PYTHONHASHSEED=42 -I -B`):**
  - `odd_perfect_cyclotomic_audit.py --standalone --json` and zero-arg stdout match committed `odd_perfect_cyclotomic_certificate.json` bit-for-bit across all `5/5` modes (`6a30f9b113108dec0db2e11f70530a38237602e7daeae79b29b8d2e116f4a089`, bit-identical to R2).
  - `odd_perfect_cyclotomic_audit.py --check odd_perfect_cyclotomic_certificate.json` returns `valid: true` across all `5/5` modes.
  - `test_odd_perfect_cyclotomic_r5.py` passes `3/3 OK` across all `5/5` modes (`0` warnings).
- **Live `aletheia v2.0.0 mutate --max-mutants 0 --work-root . --add-cwd --guards require_ok`:**
  - `odd_perfect_cyclotomic_audit.py`: **`34/34` (`100.0%`, `survived=0`, `truncated=False`) KILLED**.
  - `odd_perfect_cyclotomic_oracle.py`: **`54/54` (`100.0%`, `survived=0`, `truncated=False`) KILLED**.
  - **Combined:** **`88/88` (`100.0%`) KILLED**.
- **Exhaustive AST `BoolOp` (`And <-> Or`, `timeout=30s`) Sweep:**
  - `odd_perfect_cyclotomic_audit.py`: **`8/8` (`100.0%`, `survived=0`) KILLED**.
  - `odd_perfect_cyclotomic_oracle.py`: **`31/31` (`100.0%`, `survived=0`) KILLED**.
  - **Combined:** **`39/39` (`100.0%`) KILLED**.
- **Live Zone-B Adversarial Fuzzer:**
  - CLI surface (`--target-cli odd_perfect_cyclotomic_audit.py`): **`23/23 PASS`** (`bypasses=0, crashes=0`).
  - In-memory surface (`verify_certificate_dict`): **`18/18 PASS`** (`bypasses=0, crashes=0`).
  - **Combined:** **`41/41` (`100.0%`) PASS**.
- **Live Concurrent TOCTOU & Hardlink Race Stress (`500` Iterations):**
  - Concurrent `renameat2(RENAME_EXCHANGE)` swapping both leaf (`regular <-> symlink`) and intermediate ancestor (`dir <-> symlink`) plus concurrent `os.link()` / `os.unlink()` hardlink racing across `500` reads & `500` writes: **`leaks=0, clobbers=0, hl_clobbers=0`**.
- **Zone-B & CLI Hardening Coverage (R2/R3):**
  - Concrete `pathlib.Path` + NUL-byte + lone UTF-16 surrogate (`INVALID_UTF8_SURROGATE`) path refusal; deleted-CWD `OSError` wrapping (`CWD_UNAVAILABLE`, `rc=2`).
  - Atomic per-component `dir_fd` `openat` (`O_RDONLY | O_DIRECTORY | O_NOFOLLOW`) traversal (closing `renameat2` intermediate-symlink TOCTOU) + relative-`PWD` symlink walk.
  - Leaf read via `O_RDONLY | O_NOFOLLOW | O_NONBLOCK` + `fstat` `S_ISREG` + streaming capped `os.read(MAX_JSON_BYTES + 1)` (rejecting `/proc/kallsyms` `st_size==0` with `FILE_TOO_LARGE` and `chmod 000` with `FILE_READ_ERROR`).
  - Leaf write via `dir_fd` `lstat` (`SYMLINK_FORBIDDEN` / `NOT_A_REGULAR_FILE` / `HARDLINK_FORBIDDEN`) + `O_CREAT | O_EXCL | O_NOFOLLOW | O_NONBLOCK` temp file in the same `dfd` + atomic `os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd)` (zero `O_TRUNC` truncation, zero concurrent hardlink clobber, zero partial writes).
  - Strict exact-`str` `argv`, flag-like path refusal (`--write --json`, `--check --json`, `--check --help`, `--write -`, `--write ""`, `--check ""` -> `INVALID_PATH_ARG`, `rc=2`; `--write=--json`, `--check=--json` -> `INVALID_CLI_ARGS`, `rc=2`; never creates `./--json`).
- **Static & Hygiene Checks:** `aletheia v2.0.0 audit-check . --strict-ancestors --safety-scan --scripts odd_perfect_cyclotomic_audit.py test_odd_perfect_cyclotomic_r5.py` **`PASS`** (`5` files, `2/2` R4, `0` bare `assert`s, `0` AST float literals, `0` path leaks, `0` CRLF, `0` `__pycache__`, `0` safety findings).

---

## 6. Frozen Artifact Manifest (R3)

| File | Lines | Bytes | SHA-256 |
| :--- | :---: | :---: | :--- |
| `odd_perfect_cyclotomic_oracle.py` | `888` | `34,043` | `c0fee1a24fc7220a9bbe58fa1700437ef1cbae230dec7b72c89bec7f9332a307` |
| `odd_perfect_cyclotomic_audit.py` | `410` | `17,056` | `cf796bd090b1d1c53897d6a9ece9db42fc7e76599602be82e46625b8d3640cb9` |
| `test_odd_perfect_cyclotomic_r5.py` | `479` | `34,159` | `5bb5e72aa750cc08af1bf21ba583176cda15f302fc59444d18e505b629daee85` |
| `odd_perfect_cyclotomic_certificate.json` | `1` | `11,293` | `6a30f9b113108dec0db2e11f70530a38237602e7daeae79b29b8d2e116f4a089` |
| `ODD_PERFECT_CYCLOTOMIC_REPORT.md` | *(this report)* | *(see delivery manifest)* | *(omitted to prevent self-hash cycle)* |
