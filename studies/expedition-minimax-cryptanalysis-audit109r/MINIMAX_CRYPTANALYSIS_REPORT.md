# Clean-Room Cryptanalysis Audit of `MiniMax-AI/Research` (`57842cef`)

- **Pinned Upstream Reference (Not Vendored Here):** `MiniMax-AI/Research` @ `57842cef92e84eaf8e2535b12f48ba5586080ddd` (`Cryptography/{BentSum,ARADI,COLM,SBC-VOLE,Blender,TII-McEliece,HAWK}`, plus upstream Issues `#1` & `#2`).
- **Novelty Classification:** **`N0`** (all underlying cryptanalytic constructions, theorems, and algebraic identities belong to `MiniMax-AI/Research` and cited prior art: Tokareva 2014/2016; Shaporenko 2022; Feng et al. `arXiv:2610.32239`; NSA ARADI ePrint 2024/1240; Bellini et al. LATINCRYPT 2025; COLM CAESAR / J. Cryptol. 2024; Huth & Joux SBC-VOLE Asiacrypt 2025; Bradbury Blender NIST SHA-3; Goppa / Patterson 1975 / MacWilliams–Sloane 1977; Cassels / Conway–Sloane; Lenstra–Lenstra–Lovász 1982; Ducas et al. HAWK ASIACRYPT 2022; Straznickas & Weis ePrint 2026/1593; no full-text prior-art record is shipped here).
- **Runtime & Exactness:** Pure Python 3 standard library only (`int`, `fractions.Fraction`; zero floats on certified paths or JSON, zero bare `assert` statements, zero shared code with upstream).
- **Scope Architecture:** Three computational verification pillars plus a fail-closed canonical JSON certification and `--verify FILE` validator. Declared upstream file manifests, counts, and paper-text booleans are isolated in `declared_upstream_inputs` strictly outside `all_gates_passed`, and every claim is tagged with its evidence scope (`exact`, `sampled`, `definitional`, or `anchor`).
- **Dual-Mode Provenance Boundary (`--standalone` vs. `--live`):**
  - `--standalone` (used to generate the committed `minimax_cryptanalysis_certificate.json`, `live_portal_inspected = false`, `diag_source = "standalone_pinned_fixture"`) recomputes all three pure-$\mathbb{Z}/\mathbb{F}_2/\mathbb{F}_{2^m}/\mathbb{Q}$ computational pillars offline from scratch while recording the declared pinned upstream metadata in `declared_upstream_inputs`. It does **not** read upstream files from disk.
  - `--live --research-dir <path>` (`live_portal_inspected = true`, `diag_source = "live_portal_read"`) inspects a local read-only checkout, enforces `.git/HEAD == 57842cef...` (refusing trees without `.git/HEAD` unless `--upstream-commit` is passed explicitly), enforces pinned SHA-256 digests on all 5 Lean files, `snf_audit_vectors.json`, and `verified_tii_94_summary.json` (failing closed with `PIN_HASH_MISMATCH`), runs the upgraded Lean 4 lexical token scanner, validates all 94 TII challenge rows, and checks `Blender/paper/main.tex`.

---

## 1. Pillar 1: `BentSum` (`arXiv:2610.32239`) — Pure-$\mathbb{Z}$ Walsh–Hadamard & ANF Verification

**Claim Scope:** `exact` (all 19 computational checks in Pillar 1).

1. **Counterexample Hypotheses & Scope Note:**
   - Tokareva's conjecture states that every Boolean function $f : \mathbb{F}_2^n \to \mathbb{F}_2$ (even $n \ge 4$) of algebraic degree $\le n/2$ can be expressed as a sum of two bent functions ($f = g + h$).
   - By the codimension-$k$ weight-congruence theorem (Feng et al. `arXiv:2610.32239`, not re-proved in Python), if $f$ is supported in a codimension-$k$ affine coset ($k < n/2$) and $f = g + h$ for two bent functions $g, h$, then $2^{k+1} \mid \mathrm{wt}(f)$.
   - Consequently, a counterexample satisfying $\deg(f) \le n/2$ with $2^{k+1} \nmid \mathrm{wt}(f)$ is proved **not** to be a sum of any two bent functions (any search for bent pairs summing to it will find none). Python verifies the finite $n \in \{6, 8, 10\}$ hypotheses, truth tables, Walsh spectra, ANF degrees, coset containment, periods, and Maiorana–McFarland positive controls:
     - **$q_3$ on $\mathbb{F}_2^6$** ($z_0 z_1 + z_2 z_3 + z_4 z_5$): $\mathrm{wt}(q_3) = 28$, $\deg(q_3) = 2$, $W_{q_3}(\omega)^2 = 64$ for all `64` $\omega$ (bent).
     - **`cylQ3(4)` on $\mathbb{F}_2^8$** ($x_0 x_1 q_3(x_2,\dots,x_7)$): satisfies the Tokareva hypothesis ($\deg = 4 = n/2$, even $n=8$), support strictly inside codimension-$2$ coset $\{x_0 = x_1 = 1\}$ ($k=2 < 4$), $\mathrm{wt} = 28 \equiv 4 \pmod 8$ ($8 \nmid 28$), unique constant derivative $(a, c) = (0, 0)$ over all `256` directions, and $g_8 + \mathrm{cylQ3}(4)$ is explicitly verified not bent.
     - **Positive Bent-Sum Control ($n=8$):** Maiorana–McFarland pair $g_8(u,v) = u \cdot v$ and $h_8 = g_8 + u_0 u_1 u_2$ (both verified bent via exact FWHT) satisfies $\widehat{\varphi}(\omega) \in \{0, \pm 16\}$, Parseval support count $N = 8$ on `zeroOn({0,1})`, and $\mathrm{wt}(u_0 u_1 u_2) = 32$ ($8 \mid 32$).
     - **`liftCylQ3(4)` on $\mathbb{F}_2^{10}$** ($x_1 + \mathrm{cylQ3}(4)(x_2,\dots,x_9)$): satisfies the balanced derivative hypothesis ($\mathrm{wt} = 512$, $\deg = 4 = n/2 - 1$), and exhaustive 1,024-vector scan confirms period set is strictly $\{0, e_0\}$ (`[0, 1]`).
     - **Positive Bent-Derivative Control ($n=10$):** $g_{10}(a, b, z) = a b + a u_0 u_1 u_2 + u \cdot v$ verified bent ($W^2 = 1024$ for all `1024` $\omega$) with exact directional derivative $D_{e_0} g_{10} = x_1 + u_0 u_1 u_2$.
2. **Lean 4 Lexical Token Scanner (`minimax_cryptanalysis_audit.py:scan_lean4_lexical`):**
   - Runs strictly in `--live` mode (and unit tests) as a **lexical token scan** — **not** Lean kernel elaboration (Lean itself is not executed in this study).
   - Strips `--` line comments, nested `/- ... -/` block comments, standard `"..."` strings, char literals `'c'` (preserving Lean identifier primes), and Lean 4 raw string literals `r"..."` and `r#"..."#` (where `\` is not an escape character).
   - Scans stripped text for `12` soundness-bypass patterns: `sorry`, `sorryAx`, `axiom`, `native_decide`, `decide +native` (including `-flag` combinations, multiline forms, and `decide (config := { ... native := true ... })`), `unsafe`, `implemented_by`, `admit`, `extern` (including `@[extern ...]` / `opaque` with `extern`), `ofReduceBool` (including `Lean.ofReduceBool`), `ofReduceNat`, and `set_option debug.skipKernelTC`.
   - Declared upstream 5-file SHA-256 manifest is recorded in `declared_upstream_inputs` (outside `all_gates_passed`).

---

## 2. Pillar 2: Clean-Room Verification of ARADI, COLM, SBC-VOLE & Blender-256

1. **`ARADI` (NSA ePrint 2024/1240; `12 exact` checks + `1 sampled` check):**
   - `exact`: All 4 word maps $L_0=(11,8,14), L_1=(10,9,11), L_2=(9,4,14), L_3=(8,9,7)$ are $\mathbb{F}_2$-involutions ($L_j^2 = I_{32}$) with canceling-mask dimensions `[0, 0, 0, 8]`; $L_3$ is uniquely symmetric and orthogonal ($L_3^\top L_3 = I_{32}$) with `8` disjoint 4-column islands; super-S-box ANF degrees collapse to `[3, 3]`; LATINCRYPT 2025 single-column blind-column histogram is `{"8": 16, "13": 16}` (max `24/32` covered); analytical 5-round zero-sum derivation on the 48-point cube prefix yields `198` equations (`99` row $x$ + `99` row $z$, island nullities `[16, 12, 10, 12, 18, 0, 16, 15]`); mitigation $L_3' = (7, 3, 11)$ is involutive with `0` canceling masks.
   - `sampled`: Empirical 5-round zero-violation check records `0 / 396` violations across **`2` seeded round-key trials** (`seed = 0x20261122a8ad1001`, `198` equations per trial; a 4-round negative control triggers nonzero violations).
2. **`COLM` ($\mathbb{F}_{2^{128}} = \mathbb{F}_2[x]/(x^{128}+x^7+x^2+x+1)$; `5 exact` checks):**
   - `exact`: Exact Rabin irreducibility proof confirms $x^{128}+x^7+x^2+x+1$ is irreducible over $\mathbb{F}_2$ ($x^{2^{128}} \equiv x$ and $\gcd(x^{2^{64}}+x, f) = 1$); exact inverse $3 \cdot 3^{-1} = 1$; transplant condition $\deg(x^{m-1}/3) \le m - 2$ first holds at `m = 129`, giving transplant set `{1, 3, 4, 5, 6, 7, 129, 130}`; $\mathrm{COLM}_\tau$ obstruction holds for all $\tau \in \{1,\dots,127\}$ ($\deg(x^\tau / 3) = 127$).
   - `definitional` (outside `checks` / `all_gates_passed`): Fade relation $\sum_{k \in \{1,2,3,8,129\}} x^{k-1} = 0$ (the defining polynomial) and polynomial-basis ranks `[128, 128]`.
   - `anchor` (outside `checks` / `all_gates_passed`): J. Cryptol. 2024 Theorem 2 arithmetic at published parameters `(q=2, s=1, a=6, m=390)` yields $\sigma = 795$ and `4428155 / 2^128 < 2^-105`.
3. **`SBC-VOLE` ($\mathbb{F}_{2^{257}} = \mathbb{F}_2[x]/(x^{257}+x^{12}+1)$; `1 exact` check + `3 sampled` checks):**
   - `exact`: Frobenius test $x^{2^{257}} \equiv x$ proves irreducibility (257 is prime).
   - `sampled` (`seed = 0x202611220109abcd`, **`1` trial**): On this specific seeded SplitMix64 instance ($n=130$, 256 secret bits, 257 $\mathbb{F}_2$ equations from one transcript), the linear system has `gf2_linear_rank = 255` and `free_nullity = 1`, recovering all 256 secret bits identically. The exact `(rank=255, free_nullity=1)` split is **seed-specific** (other seeds frequently yield full rank 256, nullity 0).
4. **`Blender-256` (`2 sampled` checks + `4 exact` standard-IV checks; conditional upstream issue rulings in `declared_upstream_inputs`):**
   - `sampled` (`start_state = standard_blender256_iv_only`, `seed = 0x20261122b1e4de25`, **`24`-step stream, `1` trial**): Starting from the **standard Blender-256 IV** (not arbitrary start states; a zero/random start state breaks the invariant), the 6-bit chain parity vector traverses an 8-cycle of distinct vectors obeying `p_4 = p_0 ^ 1` and `p_5 = p_1 ^ 1`.
   - `exact` (from standard Blender-256 IV): Clean-room 12-step DFS entry obeys `p_4 = p_0 ^ 1, p_5 = p_1 ^ 1` and never sets $W_0, W_2, W_4, W_6 \in \{0, \mathtt{0xFFFFFFFF}\}$; from-IV 2-adic SNF over $(\mathbb{Z}/2^{32}\mathbb{Z})^8$ closes from `[0, 0, 1, 1, 2, 2, 3, 3]` (unshifted) to `[0, 0, 1, 1, 1, 1, 1, 1]` (multi-shifted).
   - `definitional` (outside `checks`): `wt(0)=0` and `wt(0xFFFFFFFF)=32` are both even; Proposition 6 two-step length arithmetic `((13+3)//4 + 2)*4 = 24` bytes; modular superposition over $\mathbb{Z}/2^{32}\mathbb{Z}$ is an additive identity.
   - **Conditional Upstream Issue Rulings (recorded in `declared_upstream_inputs`, outside `all_gates_passed`):**
     - *Issue `#1`:* Given upstream `Blender/paper/main.tex` at pinned commit `57842cef` stating `"global minimum"` for the two-step silent-carry healing family, Proposition 6 arithmetic establishes a 24-byte minimum only within that two-step family, not globally.
     - *Issue `#2`:* Given upstream `Blender/paper/main.tex` at pinned commit `57842cef` §3.3 stating `"steer W_0, W_2, W_4, W_6 in {x, ~x}"`, that prose conflicts with the Theorem 2 standard-IV invariant `p_4 = p_0 ^ 1`, whereas clean-room 12-step entry stays on shifted phase constants obeying Theorem 2.

---

## 3. Pillar 3: Background Algebraic Identities Verified in This Audit

**Scope Disclaimer:** Both identities below are **classical background algebraic identities verified in this audit** (`exact`). No code in this study reads, imports, or modifies objects in `math0` code-table scripts, `siliquant`, or `mcproof`. In particular, the Goppa identity operates on **binary** (`GF(2)`) subfield subcodes over $\mathbb{F}_{2^5}$, whereas this repository's code-table work targets $\mathbb{F}_3$ to $\mathbb{F}_9$.

1. **Binary Goppa Shortening & Minimum-Weight Identity (`TII-McEliece`; `8 exact` checks):**
   - `exact`: Clean-room binary Goppa code $\Gamma(L, g)$ over $\mathbb{F}_{2^5}$ ($n=24, m=5, t=3, k=9$, $g(X) = X^3 + X^2 + a X + 1$, root-free on $\mathbb{F}_{2^5}$) has `13` minimum weight-$7$ codewords, all satisfying Theorem 1 ($\sigma'_S(X) = g(X)^2$ and $e_2(z_S) = g_{t-1}^2$).
   - `exact` (full-code shortening equality): Shortening $\Gamma(L, g)$ to $n'=21$ yields a `64`-codeword (`dim=6`, `6` weight-7 words) subcode that is explicitly verified **set-equal** to $\Gamma(L[:21], g)$ constructed directly on the shorter support $L[:21]$.
   - `definitional` / `anchor` (outside `checks`): Odd-pair parity $\binom{7}{2} \equiv 3 \pmod 2$ (`definitional`); quadratic feature count $F(d) = 1 + d + \binom{d}{2}$ evaluated on published TII-125 (`98347/15052 = 6.533816`) and TII-250 (`197803/30016 = 6.589919`) parameters (`anchor`); campaign summary `94` solved (`89` Route A, `5` Route B, `55` first-bloods) sits in `declared_upstream_inputs`.
2. **Rank-8 Parity-Sublattice Gram-Determinant Law & Blind Exact LLL (`HAWK`; `11 exact` checks):**
   - `exact`: Planted inverse verification ($U_{\text{rec}} B_{\text{raw}} = B_{\text{good}}$, $|\det U_{\text{rec}}| = 1$, $\det G_{\text{red}} = \det G_{\text{raw}} > 0$, max diagonal `31,954 -> 41`) **plus blind exact pure-$\mathbb{Q}$ LLL reduction** directly on $B_{\text{raw}}$ (without receiving $B_{\text{good}}$), recovering unimodular $U_{\text{LLL}}$ ($|\det U_{\text{LLL}}| = 1$, $U_{\text{LLL}} B_{\text{raw}} = B_{\text{LLL}}$, exact Gram determinant invariance) and `max_diag = 41`.
   - `exact`: Parity-congruence sublattice $H$ explicitly verified to satisfy BOTH $H \mathbb{Z}^8 = 2 \mathbb{Z}^8 + \mathbb{Z} u_{\text{parity}}$ (every row mod 2 in $\{0, u_{\text{parity}} \bmod 2\}$ with $|\det H| = 128 = 2^{n-1}$, rejecting non-parity index-128 matrices such as $\mathrm{diag}(2,\dots,2,1)$) AND the standard Gram-determinant scaling identity $\det(H G H^\top) = 2^{14} \det(G)$.
   - `anchor` (outside `checks`): Published HAWK BKZ block-size differences `92-58=34`, `205-156=49`, `432-351=81` and HAWK-256 Hermite ratio `4222/10000 < 1`.

---

## 4. Exact Offline Reproduction

Run from `studies/expedition-minimax-cryptanalysis-audit109r/` (100% offline, Python 3 standard library only):

```bash
# 1. Offline standalone certificate generation (bit-identical across -I -B, -I -O -B, -I -B -W error, PYTHONHASHSEED=42 -B)
python3 -I -B minimax_cryptanalysis_audit.py --standalone --json | sha256sum
python3 -I -O -B minimax_cryptanalysis_audit.py --standalone --json | sha256sum
python3 -I -B -W error minimax_cryptanalysis_audit.py --standalone --json | sha256sum
PYTHONHASHSEED=42 python3 -B minimax_cryptanalysis_audit.py --standalone --json | sha256sum

# 2. Strict fail-closed verification of the committed certificate (re-derives all 3 pillars & checks canonical bytes)
python3 -I -O -B -W error minimax_cryptanalysis_audit.py --verify minimax_cryptanalysis_certificate.json

# 3. Assertion-free R5 adversarial, wrong-value, Lean 4 raw-string, and --verify forgery suite (4/4 groups OK)
python3 -I -O -B -W error test_minimax_cryptanalysis_r5.py

# 4. File integrity check
sha256sum -c SHA256SUMS

# 5. Optional live read-only audit against a local MiniMax-AI/Research checkout (@ 57842cef)
python3 -I -B -W error minimax_cryptanalysis_audit.py --live --research-dir <path/to/MiniMax-AI-Research>
```
