# Track S25: Catalan–Dickson Aliquot Transfer Operator & Unified Five-Pillar Exact $\mathbb{Z}/\mathbb{Q}$ Synthesis (Portals 17–21)

- **Track ID:** `Track S25`
- **Oracle Class:** `exact` (100% pure Python 3 stdlib `int`, `fractions.Fraction`, `math`, `hashlib`; zero IEEE-754 floats in oracle, audit, or JSON certificate; zero bare `assert`s; zero RNG; zero third-party dependencies)
- **Honest Law-4 Novelty Classification:** **`N1`** (clean-room unified pure-$\mathbb{Z}/\mathbb{Q}$ exact verification engine across Portals 17–21, exact 5-state $(v_2, v_3, v_5)$ even-basin finite-state aliquot Markov transfer operator $T_{\{2,3,5\}}$ and invariant-measure drift inversion witness, exact 6-driver converse counterexample witness $u=25$ sharpening the `iff` vs. sufficiency law, and Uniform Zone-B atomic `dir_fd` / `os.replace` certification; all classical theorems and open conjectures strictly quarantined as **`N0`** below)
- **Canonical Certificate Digests (`aliquot_transfer_certificate.json`):**
  - File / zero-arg / `--standalone --json` SHA-256: `6cff81f9043f2db337615e3c48b1ef16e3cdaf5cfa41f50be7e51a817e27f8f4`
  - `payload_sha256`: `1245aedd06e59d2eaaaa69c684f0439f5e08c37ed89918224305ce2876a4e6f4`
  - `certificate_sha256`: `594b8a48cb317d05047e9f172c80f0726548556765612b17a49ef4e3b673aee0`

---

## 1. Strict Law-4 `N0` Prior-Art Quarantine & Epistemic Boundaries

Every classical theorem and open conjecture verified or modeled here is explicitly quarantined as **`N0`**:

| Classical Result / Conjecture | Primary Prior Art (`N0`) | Exact Role in `Track S25` |
|---|---|---|
| Catalan–Dickson Conjecture (1888) vs. Guy–Selfridge Heuristic (1975); Bosma–Kane (2012) geometric mean; Lehmer Five `{276, 552, 564, 660, 966}`; Poulet cycles (`12496`, `14316`) | Catalan (1888); Dickson (1913); Poulet (1918); Guy–Selfridge (1975); Bosma–Kane (2012) | Pillar 1 exact parity-lock, driver algebra, finite-state Markov model `T_{2,3,5}`, untouchables, & `1..1,000` atlas |
| Sylvester–Servais–Norton abundance lower bounds & Zsigmondy primitive-divisor theorem | Sylvester (1888); Servais (1888); Zsigmondy (1892); Norton (1961) | Pillar 2 exact pure-$\mathbb{Q}$ $k_{\mathrm{Sylv}}(q)$ through $q=101$, sharp odd-abundant witnesses, & odd-prime Zsigmondy |
| Descartes' 1638 odd spoof `198585576189`, Pomerance $\alpha=1$ divisor reduction, & Euler-product reciprocal convergence | Descartes (1638); Pomerance (1975/2018); Laatsch (1986); Weiner (2000) | Pillar 3 exact Euler factor `9/20 -> 3*pi^2/16`, exhaustive odd $m \le 10{,}000$, & even-$2^a$ pseudorandomness falsification |
| Ore harmonic divisor numbers, Ore's Conjecture (1948), & Kanold finite-slice bounds | Ore (1948); Kanold (1957); Garcia (1954) | Pillar 4 exact $H(n)I(n)=\tau(n)$, 2-adic LTE valuation law, Kanold–Sylvester ceilings, $h=3$ proof, & sieve $\le 100{,}000$ |
| Cyclotomic factor chains $\Phi_\ell(p)$, Kirchhoff valuation conservation, & Descartes spoof web | Euler (1747); Sylvester (1888); Descartes (1638) | Pillar 5 Descartes spoof Kirchhoff balance (`4` seed nodes `{3,7,11,13}` + `2` external leak primes `{19,61}`), universal 2-step $\Phi_\ell$ funnel, & $\Phi_3$ cascade |

> **Honest Scope Statement:** Pillar 1's finite-state $(v_2, v_3, v_5)$ Markov transfer operator $T_{\{2,3,5\}}$ is an **`N1` exact finite-state statistical model** over $2 \le n \le 10{,}000$ even — it does **NOT** prove or disprove the open Catalan–Dickson Conjecture (`N0`). Likewise, Pillars 2–5 certify exact finite algebraic obstructions and bounded exhaustive domains — they do **NOT** prove or disprove the existence of odd perfect numbers or odd Ore numbers (`N0`).

---

## 2. Pillar 1 — Catalan–Dickson vs. Guy–Selfridge & Aliquot Transfer Operator (Portal 17)

1. **Exact Parity-Lock & Zero-Density Square-Escape Theorem (`1 <= n <= 10,000`, `0` exceptions):**
   $$s(n) \equiv n \pmod 2 \iff \sigma_1(n) \equiv 0 \pmod 2 \iff n \notin \{m^2, 2m^2\}.$$
   Verified exhaustively across all `10,000` integers (`parity_vs_sigma_exceptions = 0`, `parity_vs_escape_exceptions = 0`), with exactly `170` parity-flipping escape portals (`100` squares $m^2$ + `70` double-squares $2m^2$, exact density `17/1000`).
2. **Exact Even-Perfect Driver Monotonicity & Sharpened `6`-Driver Persistence Law:**
   - For $D \in \{6, 28, 496\}$ and coprime odd $u \in \{5, 7, 11, 13, 17, 19, 25, 35\}$ (`22/22` coprime pairs): $s(Du) = D(2\sigma_1(u) - u) > Du$ strictly.
   - Across all `99` odd $5 \le u \le 300$ with $\gcd(u, 6) = 1$: $v_2(s(6u)) = 1$ unconditionally (`0` exceptions), and the exact `iff` criterion is $v_3(s(6u)) = 1 \iff (2\sigma_1(u) - u) \not\equiv 0 \pmod 3$ (`70/99` persist). Sufficiency $3 \mid \sigma_1(u) \implies v_3(s(6u)) = 1$ holds unconditionally (`62/62`), while the converse fails at **`8` exact counterexamples**, minimally **`u = 25`** ($\sigma_1(25) = 31 \not\equiv 0 \pmod 3$, yet $s(150) = 222 = 2\cdot 3\cdot 37$ preserves $v_3 = 1$).
3. **Exact Pure-$\mathbb{Q}$ 5-State $(v_2, v_3, v_5)$ Even-Basin Markov Transfer Operator $T_{\{2,3,5\}}$ (`n in 2..10,000` even):**
   - Partitioning even $n \le 10{,}000$ into `5` canonical driver classes (`D2_PLAIN`, `D6_CORE`, `D10_30_MIX`, `D4_HIGH2_NO3`, `D12_24_HIGH2_3`) and solving $\pi^* T = \pi^*$, $\sum \pi^*_i = 1$ via exact `Fraction` Gauss–Jordan yields zero residual identically:
     - **Archimedes Pure-$\mathbb{Q}$ Basin Bounds ($223/71 < \pi < 22/7$):** Even asymptotic mean $\frac{5\pi^2}{24} - 1 > \frac{127661}{120984} > 1$; odd asymptotic mean $\frac{\pi^2}{8} - 1 < \frac{23}{98} < 1$.
     - **Uniform Even Empirical Mass Ratio:** `2640757/2500500` ($\approx 1.05609 > 1$).
     - **Exact Mass-Weighted Stationary Drift $\mathbb{E}_{\pi^*}[\text{mass-ratio}] = \sum_i \pi^*_i \frac{\sum_{n \in i} s(n)}{\sum_{n \in i} n}$:** `28487305372749924592746968370533862970981 / 29410233730096405346336003744168969062500` ($\approx 0.96861880 < 1$; for reference, weighting $\pi^*$ against unweighted within-state means $\frac{1}{|i|}\sum_{n \in i}\frac{s(n)}{n}$ similarly yields $\approx 0.96805446 < 1$), driven by $\pi^*$ shifting mass out of high-ratio `D12_24_HIGH2_3` (`16.66% -> 9.35%`, mass-weighted ratio `7349453/4168332`) into contracting `D2_PLAIN` (`26.68% -> 33.43%`, mass-weighted ratio `966683/1668334`).
4. **Exact Untouchable Proofs Over All $\mathbb{N}$ & Certified $1 \le n \le 1{,}000$ Aliquot Atlas:**
   - Every composite $n$ satisfies $s(n) \ge 1 + n/p_{\min} \ge 1 + \sqrt{n} \implies n \le (s(n) - 1)^2$. Checking $1 \le n \le (k-1)^2$ proves unconditionally over all $\mathbb{N}$ that **`2`** (bound `1`), **`5`** (bound `16`), and **`52`** (bound `2,601`) are untouchable (`0` preimages). The oracle verifies explicit preimages for all `499` odd integers $k \in [3, 1001] \setminus \{5\}$ ($s(4)=3, s(8)=7$, and `497` Goldbach semiprimes $s(pq) = 1+p+q = k$), recording the certified count `goldbach_odd_preimage_witnesses_le_1001 = 499` in the certificate.
   - **Complete `1..1,000` Partition (`1,000` total):** `965` terminating (incl. **`138`**, stored in `trajectory_138`: peaking at `179,931,895,322` at step `117` and hitting `1` at step `177`, `0` at step `178`; other terminating trajectories such as `{702, 978, 990}` are counted inside `atlas_1_to_1000_counts["terminates"] = 965` without storing their individual intermediate peaks in the frozen certificate), `19` reaching perfect cycles (`6, 28, 496`), `3` reaching amicable `(220, 284)`, `12` merging into the open Lehmer-Five families (`276:[276,306,396,696]`, `552:[552,888]`, `564:[564,780]`, `660:[660,828,996]`, `966:[966]`), and `1` ultra-high-peak seed (`840`, cleanly flagged exceeding `10^22`). Independent closure verified for Poulet 5-cycle (`12496`, max `15472`) and 28-cycle (`14316`, max `629072`), plus certified 20-step summary records (`a20`, `distinct_driver_tags`, and `driver_tag_tail5`) for all 5 Lehmer-Five seeds (`276 -> a_20=54684`, visiting `4` distinct tags `["D24_DRV","D28_PERF","D2_DOWN","EVEN_OTHER"]` over 20 steps with `a_20` and all 5 tail steps `driver_tag_tail5` locked on `D28_PERF`; whereas `966 -> a_20=82278` remains locked on `D6_PERF` across all 20 steps).

---

## 3. Pillar 2 — Sylvester–Servais–Norton Abundance Wall & Odd-Prime Zsigmondy (Portal 18)

1. **Exact Pure-$\mathbb{Q}$ Sylvester Wall $k_{\mathrm{Sylv}}(q) = \min\{k : \prod_{j=1}^k \frac{p_j}{p_j-1} > 2, \, p_1=q\}$ (`9/9` certified with full exact `"num/den"` product and exact margin above `2` in certificate):**
   - $q=3 \to k=3$ ($p_{\max}=7$, exact `35/16`, margin `3/16`)
   - $q=5 \to k=7$ ($p_{\max}=23$, exact `676039/331776`, margin `12487/331776`)
   - $q=7 \to k=15$ ($p_{\max}=61$, exact `5855632691117327/2889476997120000`)
   - $q=11 \to k=27$ ($p_{\max}=127$); $q=13 \to k=41$ ($p_{\max}=199$, margin $< 1/35461$); $q=17 \to k=62$ ($p_{\max}=337$); $q=19 \to k=85$ ($p_{\max}=479$); $q=47 \to k=380$ ($p_{\max}=2707$, margin $< 1/26262$); $q=101 \to k=1331$ ($p_{\max}=11197$, `13016`-bit exact numerator, knife-edge margin `< 1/103137`).
2. **Sharp Odd-Abundant Witnesses Attaining $k_{\mathrm{Sylv}}(q)$:**
   - $q=3$: $945 = 3^3\cdot 5\cdot 7$, $I(945) = 128/63$ (margin `+2/63`).
   - $q=5$: $930{,}483{,}178{,}625 = 5^3\cdot 7^2\cdot 11^2\cdot 13^2\cdot 17\cdot 19\cdot 23$, $I(N) = 216297216/107632525$ (margin `+1032166/107632525`).
3. **Sylvester–Zsigmondy Structural Obstruction:** Exact rational deficit $\frac{p}{p-1} - I(p^{2b}) = \frac{1}{p^{2b}(p-1)}$ certified across `15` pairs ($p \in \{3,5,7,11,13\}, b \in \{1,2,3\}$), paired with **`45/45`** odd-prime Zsigmondy primitive-divisor pairs verified across odd $p \in \{3..29\}$ and odd $d \in \{3,5,7,9,11\}$ (`0` exceptions, every primitive divisor $r \equiv 1 \pmod d$; `zsigmondy_odd_pairs_checked = 45`, with `6` representative witness samples stored in `zsigmondy_samples`).

---

## 4. Pillar 3 — Convergent Reciprocals, Pomerance $\alpha=1$ & Pseudorandomness Ceiling (Portal 19)

1. **Exact Rational Euler Product (`6/6` local primes + closed-form tail identity):**
   $(1 + 3p^{-2} + 5p^{-4} + \dots) = \frac{1+p^{-2}}{(1-p^{-2})^2} = \frac{1-p^{-4}}{(1-p^{-2})^3}$; at $p=2$, local factor is `20/9`, giving exact $p=2$ removal factor **`9/20`** and exact Bernoulli/Euler constant $\sum_{m \ge 1, \text{ odd}} \frac{\tau(m^2)}{m^2} = \frac{9}{20}\cdot\frac{(1/6)^3}{1/90}\pi^2 = \frac{9}{20}\cdot\frac{5}{12}\pi^2 = \mathbf{\frac{3}{16}\pi^2}$.
2. **Exhaustive Odd $1 \le m \le 10{,}000$ (`5,000` odd integers):** **EXACTLY `2` solutions** to $\Delta(m^2) = 2m^2 - \sigma_1(m^2) > 0, \Delta(m^2) \mid m^2$: trivial `m = 1` ($\Delta=1, p=1$) and **Descartes' 1638 odd spoof `m = 3003 = 3·7·11·13`** ($m^2 = 9{,}018{,}009$, $\sigma_1(m^2) = 18{,}035{,}199$, $\Delta = 819$, $p = 22021 = 19^2\cdot 61$ composite).
3. **Exact Even-Number Pseudorandomness Falsification Witness:** For all $1 \le a \le 30$, $2(2^a) - \sigma_1(2^a) = 1 \mid 2^a$ identically (hit rate `1`), demonstrating constructively why pseudorandomness heuristics cannot by themselves constitute a proof of nonexistence for odd perfect numbers.

---

## 5. Pillar 4 — Harmonic Duality ($H(n)\cdot I(n) \equiv \tau(n)$) & Ore's Conjecture (Portal 20)

1. **Exact Duality & 2-Adic LTE Valuation Law:** $H(n)I(n) = \tau(n)$ verified across $1 \le n \le 1{,}000$ (`0` exceptions); exact 2-adic valuation law $v_2(\sigma_1(n)) = v_2(\tau(n)) + \sum_{p \equiv 3 \pmod 4,\, a\text{ odd}}(v_2(p+1) - 1)$ (noting $v_2(p+1)-1 = 0$ identically for $p \equiv 1 \pmod 4$) verified exhaustively across ALL **`10,000`** odd $1 \le n \le 20{,}000$ (`0` exceptions), plus prime-power non-Ore checks (`54/54`, $\gcd(p^a, \sigma_1(p^a)) = 1$ and $\sigma_1(p^a) > a+1$).
2. **Kanold–Sylvester Pure-$\mathbb{Q}$ Finite Ceilings & Exact $h=3$ Nonexistence Proof:**
   - Ceilings on $\omega(n)$ for odd Ore $h$: $h=3 \implies \omega \le 2$ (`128/35 >= 3`); $h=5 \implies \omega \le 3$ (`512/77`); $h \in \{7, 9, 11\} \implies \omega \le 4$ (`12288/1001`); $h \in \{13, 15\} \implies \omega \le 5$ (`393216/17017`).
   - Exact pure-$\mathbb{Q}$ proof of **ZERO odd Ore solutions for $h=3$:** $\omega=2$ is forced (prime powers are non-Ore and Kanold–Sylvester gives $\omega \le 2$ since $128/35 > 3$); for $3 \mid n$, if $n = 3q$ ($q$ prime $> 3$, squarefree) then $H(3q) = \frac{3q}{q+1} < 3$ (and $v_2$-LTE already forbids odd exponent on $3 \equiv 3 \pmod 4$), while for all other $3 \mid n$ ($\omega=2$ non-squarefree, or $\omega \ge 3$) we have $\tau(n) \ge 6 > 45/8 > 3I(n) \implies H(n) > 3$; for $p \ge 5$ with $\max(a,b) \ge 2$, $H(n) > 144/35 > 3$; for $p \ge 5$ squarefree ($p,q \equiv 1 \pmod 4$ by LTE $\implies p \ge 5, q \ge 13$), $I(pq) \le 84/65 < 4/3 \implies H(pq) \ge 65/21 > 3$.
3. **Exhaustive Certified Sieve $1 \le n \le 100{,}000$:** Exactly **`18`** Ore numbers (`1, 6, 28, 140, 270, 496, 672, 1638, 2970, 6200, 8128, 8190, 18600, 18620, 27846, 30240, 32760, 55860`), with **`1`** as the unique odd Ore number $\le 100{,}000$.

---

## 6. Pillar 5 — Cyclotomic Webs, Kirchhoff Conservation & $\Phi_\ell$-Attractor Cascade (Portal 21)

1. **Descartes' Spoof Kirchhoff Balance Matrix (`4` seed nodes `{3, 7, 11, 13}` + `2` external leak primes `{19, 61}` forming fake Euler node `L = 22,021`):** Seed powers `{3^2, 7^2, 11^2, 13^2}` emit $\Phi_3(3)=13$, $\Phi_3(7)=3\cdot 19$, $\Phi_3(11)=7\cdot 19$, $\Phi_3(13)=3\cdot 61$, leaving exact deficit `{3:0, 7:1, 11:2, 13:1}` and external leak $L = 19^2\cdot 61 = 22{,}021$. Fake Euler outflow $(L+1)/2 = 11{,}011 = 7^1\cdot 11^2\cdot 13^1$ matches the deficit identically solely by truncating $\Phi_3(19) = 3\cdot 127$ and $\Phi_3(61) = 3\cdot 13\cdot 97$.
2. **Universal 2-Step $\Phi_\ell$-Attractor Funnel (`l in {3, 5, 7}`, all `669` primes $p \le 5{,}000$):**
   - `l=3`: `d0=1, d1=330, d2=338` (`338/338` fully factored); `138` $\Phi_3$-smooth primes $< 5{,}000$ (`[67, 79, 137, 149, 163, ...]`).
   - `l=5`: `d0=1, d1=163, d2=505` (`505/505` fully factored).
   - `l=7`: `d0=1, d1=110, d2=558` (`79` fully factored for $p \le 500$, plus exact $\Phi_7(p) \equiv 1 \pmod 7$ & $v_7(\Phi_7(p))=1$ verification across all `669` primes paired with the exact $\operatorname{ord}_r(p) = \ell \implies r \equiv 1 \pmod \ell$ proof).
3. **Exact Forward $\Phi_3$-Cascade of `{3}` Through Depth `5`:** `[[3], [13], [61], [97], [3169], [3348577]]`.

---

## 7. Uniform Zone-B Hardening, Verification Gates & Falsification Criteria

- **Certificate Verification Semantics:** `aliquot_transfer_audit.py --check <path>` performs atomic `dir_fd` `openat` regular-file reading (`O_RDONLY | O_DIRECTORY | O_NOFOLLOW` handling both `ELOOP` and `ENOTDIR`, leaf `O_NOFOLLOW | O_NONBLOCK`, `fstat` `S_ISREG`, streaming capped `os.read`), strict zero-float / zero-BOM / zero-CRLF / zero-surrogate / ASCII-digit-only / bounded-depth / bounded-int JSON parsing, strict 64-char lowercase ASCII hex validation BEFORE `hmac.compare_digest`, **full pure-$\mathbb{Q}$ deterministic replay + secondary algebraic cross-check** (reserving zero-shared-code verification to independent external verifiers). Writes use `dir_fd` `lstat` (`SYMLINK_FORBIDDEN`, `NOT_A_REGULAR_FILE`, `HARDLINK_FORBIDDEN`) followed by fresh `O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_NONBLOCK` temp creation in the same `dfd` and atomic `os.replace(..., src_dir_fd=dfd, dst_dir_fd=dfd)`. Under the standard POSIX same-directory-write threat model, atomic `dir_fd` traversal and `O_CREAT | O_EXCL` + `os.replace` prevent path-traversal TOCTOU escapes and in-place hardlink clobbering across concurrent renames/links while assuming the destination directory itself is not owned by a hostile co-writer capable of unlinking or swapping entries independently.
- **3-Mode Isolated Parity (`-I -B`, `-I -O -B`, `-I -B -W error`) + `-I -O -B -W error` & `PYTHONHASHSEED=42 -B`:**
  - Zero-arg & `--standalone --json`: bit-identical `6cff81f9043f2db337615e3c48b1ef16e3cdaf5cfa41f50be7e51a817e27f8f4` ×5 (exact match to on-disk `aliquot_transfer_certificate.json`).
  - `--check aliquot_transfer_certificate.json`: bit-identical `0ddb4f920f4206fc396f2f3777e60529b002838e71f37cf0faa4a58475333243` ×5 (`valid: true`).
  - `test_aliquot_transfer_r5.py`: **`4/4 OK`** ×5 (`0` warnings, `0` bare `assert`s), including `v_p_exact` primality guards (`NOT_PRIME`), ASCII-digit-only `_parse_bounded_int` refusal (`INVALID_JSON_INT` on Arabic-Indic/superscript/empty tokens), live `520`-iter concurrent `renameat2(RENAME_EXCHANGE)` (`0` leaks, `0` clobbers) + `420`-iter concurrent `os.link` hardlink race (`0` clobbers, `0` leftover temps), deleted-CWD `CWD_UNAVAILABLE` (`rc=2`), lone UTF-16 surrogates (`rc=2`), and strict flag-like / equals-syntax CLI path refusal (`--write --json`, `--write=--json`, `--check=--json` -> `rc=2`, `0` files created).
- **Live Default-CLI `aletheia v2.0.0 mutate --max-mutants 0 --work-root . --add-cwd`:** **`47/47` (`audit`) + `24/24` (`oracle`) = `71/71` (`100.0%`, `survived=0`, `truncated=False`) KILLED**.
- **Exhaustive `SWAP + SUBCOND_DEL` AST `BoolOp` Sweep (`timeout=30`):** **`24/24` (`audit`, `8/8` SWAP + `16/16` SUBCOND_DEL) + `48/48` (`oracle`, `16/16` SWAP + `32/32` SUBCOND_DEL) = `72/72` (`100.0%`, `survived=[]`) KILLED**.
- **Live Zone-B Adversarial Fuzzer:** **`23/23` CLI + `18/18` In-Memory = `41/41` (`100.0%`, `bypasses=0`, `crashes=0`) `PASS`**.
- **Static & Hygiene Gate:** `aletheia v2.0.0 audit-check . --strict-ancestors --safety-scan --scripts aliquot_transfer_audit.py test_aliquot_transfer_r5.py` **`PASS`** (`5` files, `2/2` isolated-parity scripts, `0` findings, `PYC=0`, `0` personal-path/private-org leaks, `0` bare `assert`s, `0` floats in oracle/audit/cert).
- **Falsification Criteria:** Fails if any parity-lock, driver, Markov stationary residual, untouchable, `1..1,000` atlas, Sylvester wall, Zsigmondy, Euler-product, Pomerance $m \le 10{,}000$, 2-adic LTE, Kanold–Sylvester, Ore $\le 100{,}000$, Descartes Kirchhoff, or $\Phi_\ell$-funnel invariant deviates from exact $\mathbb{Z}/\mathbb{Q}$ arithmetic; if any float enters the oracle, audit, or JSON certificate; or if any isolated-parity, race-stress, default-CLI `aletheia mutate`, `SWAP+SUBCOND_DEL` `BoolOp`, Zone-B fuzzer, or `audit-check` gate fails.
