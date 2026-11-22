# Track S14 (`AUDIT-109`): Clean-Room Cryptanalysis Audit of `MiniMax-AI/Research` & Exact Law-5 Operator Bridge to `mcproof`, `math0` & `siliquant`

- **Audit ID:** `AUDIT-109` / `AUDIT-109R` (Zone-B hardened closing `MM109-BUG-01..04`: canonical string-key JSON roundtrip, Lean string/char-literal comment stripping, per-challenge TII-94 + `.git/HEAD` live verification, and non-zero SHA / strict JSON-type enforcement).
- **Pinned Upstream Portal (Strictly Read-Only, `0` External Writes):** `MiniMax-AI/Research` @ `57842cef92e84eaf8e2535b12f48ba5586080ddd` (`Cryptography/{BentSum,ARADI,COLM,SBC-VOLE,Blender,TII-McEliece,HAWK}`, plus open Issues `#1` & `#2` by `@ziyang-theory`; `0` open/closed PRs at snapshot).
- **Dual-Mode Provenance Boundary (`--standalone` vs. `--live`):** Offline `--standalone` mode recomputes all three pure-$\mathbb{Z}/\mathbb{F}_2/\mathbb{F}_{2^m}/\mathbb{Q}$ mathematical pillars live from scratch while replaying the pinned `MiniMax-AI/Research @ 57842cef` file-hash / Lean-purity / SNF / TII-94 manifest (`diag_source = "standalone_pinned_fixture"`, `live_portal_inspected = false`; it does NOT hash local upstream `.lean` files from disk). Live on-disk hashing and scanning of `BentSum/lean/`, `snf_audit_vectors.json`, `Blender/paper/main.tex`, all `94` rows of `verified_tii_94_summary.json`, and `.git/HEAD` execute strictly in `--live --research-dir <path>` mode (`diag_source = "live_portal_read"`, `live_portal_inspected = true`).
- **Governance Standard:** Aletheia v2.0.0 (pure Python 3 stdlib `int`/`Fraction`, `0` floats, `0` bare `assert`s, `0` shared code with upstream, strict Law 4 `N0`/`N1` attribution, strict Law 5 zero-metaphor exact operators).
- **Novelty Classification (Law 4 Honest Default):**
  - **`N0` (Prior Art & Upstream Cryptanalysis):** All underlying cryptanalytic results and formalizations belong strictly to `MiniMax-AI/Research` and cited literature (Tokareva 2014/2016; Shaporenko 2022; Feng et al. `arXiv:2610.32239`; NSA ARADI ePrint 2024/1240; Bellini et al. LATINCRYPT 2025; COLM CAESAR / J. Cryptol. 2024; Huth & Joux SBC-VOLE Asiacrypt 2025; Bradbury Blender NIST SHA-3; Patterson 1975 / MacWilliams–Sloane 1977 Goppa locator identity; Ducas et al. HAWK ASIACRYPT 2022; Straznickas & Weis ePrint 2026/1593; `@ziyang-theory` Issues `#1` & `#2`).
  - **`N1` (Independent Clean-Room Audit & Cross-Repo Operator Bridge):** Independent zero-shared-code pure-$\mathbb{Z}/\mathbb{F}_2/\mathbb{F}_{2^m}/\mathbb{Q}$ re-verification of all 7 portal mechanisms, exact formal rulings on open `Blender-256` Issues `#1` & `#2` (showing why §3.3 prose contradicts Theorem 2 while the shifted-subspace algorithm itself is sound), and concrete Law-5 mathematical operator bridges to `Proven-Commons/mcproof`, `Foundation-0/math0`, and `Moissanite-Labs/siliquant`.

---

## 1. Pillar 1: `BentSum` (`arXiv:2610.32239`) Lean 4 Purity & Pure-$\mathbb{Z}$ Walsh–Hadamard Audit

1. **Aletheia v2.0.0 Lean 4 Static Purity Audit (`Cryptography/BentSum/lean/`):**
   - `aletheia v2.0.0 audit-check Cryptography/BentSum/lean --lean-audit --allow-project-import Mathlib BentSum` -> **`PASS`** (`5` `.lean` files scanned, **`0` findings**, `0` notices): zero `sorry`, zero `sorryAx`, zero `axiom`, zero `native_decide`, zero `unsafe`, zero `implemented_by`, zero `admit`.
   - Pinned SHA-256 file manifest:
     - `BentSum.lean`: `6bcd5557d4cc90b94e2dde3781b667261376d454363f2ee53c533540e73127de`
     - `BentSum/Basic.lean`: `db88b32349a4815f9050892e4d89e698b7e2b9743221e257d1dd53f134707961`
     - `BentSum/Congruence.lean`: `8ff756e7dd01ace03e83de619906ab6427779fd55a579958c8d1044eaaf3693b`
     - `BentSum/Counterexample.lean`: `d03e1786d2e894266aece0a82841fecef31c445c043c9af668dd01bb3682c5ea`
     - `BentSum/Derivative.lean`: `53e614fa14c3ac2436b6f611a4f1fbba731031ef7c767b0f7e95ca0ebc0af72b`
2. **Independent Zero-Shared-Code Pure-$\mathbb{Z}$ Walsh–Hadamard & ANF Verification:**
   - **$q_3$ on $\mathbb{F}_2^6$** ($z_0 z_1 + z_2 z_3 + z_4 z_5$): $\mathrm{wt}(q_3) = 28$, $\deg(q_3) = 2$, $W_{q_3}(\omega)^2 = 64$ for all `64` $\omega$ (**bent**).
   - **Tokareva Bent-Sum Counterexample `cylQ3(4)` on $\mathbb{F}_2^8$** ($x_0 x_1 q_3(x_2,\dots,x_7)$): $\mathrm{wt} = 28$, exact ANF $\deg = 4 = n/2$, support strictly inside codimension-$2$ coset $\{x_0 = x_1 = 1\}$, $\mathrm{wt} \bmod 8 = 4 \neq 0$ (contradicting the bent-sum weight congruence $2^{k+1} = 8 \mid \mathrm{wt}$), and exhaustive 256-direction check confirms unique constant derivative $(a, c) = (0, 0)$.
   - **Positive Bent-Sum Congruence Control ($n=8$):** Explicit Maiorana–McFarland pair $g(u,v) = u \cdot v$ and $h = g + u_0 u_1 u_2$ (both verified bent via exact FWHT) has signed-indicator Walsh spectrum $\widehat{\varphi}(\omega) \in \{0, \pm 16\}$, Parseval support count $N = 8$ (even) on `zeroOn({0,1})`, and $\mathrm{wt}(u_0 u_1 u_2) = 32 = 8 \cdot 4$ ($8 \mid 32$).
   - **Tokareva Derivative Counterexample `liftCylQ3(4)` on $\mathbb{F}_2^{10}$** ($x_1 + \mathrm{cylQ3}(4)(x_2,\dots,x_9)$): balanced ($\mathrm{wt} = 512$), exact ANF $\deg = 4 = n/2 - 1$, exhaustive 1,024-vector period check confirms period set is strictly $\{0, e_0\}$ (`[0, 1]`).
   - **Positive Bent-Derivative Control ($n=10$):** $g_{10}(a, b, z) = a b + a u_0 u_1 u_2 + u \cdot v$ verified bent ($W^2 = 1024$ for all `1024` $\omega$) with exact directional derivative $D_{e_0} g_{10} = x_1 + u_0 u_1 u_2$.

---

## 2. Pillar 2: Clean-Room Verification of Fast Algebraic Operators & Live Peer Errata

1. **`ARADI` (NSA ePrint 2024/1240):**
   - Independently verified all 4 word maps $L_0=(11,8,14), L_1=(10,9,11), L_2=(9,4,14), L_3=(8,9,7)$ are $\mathbb{F}_2$-involutions ($L_j^2 = I_{32}$), with canceling-mask subspace dimensions `[0, 0, 0, 8]` — **`L_3` is uniquely symmetric and orthogonal ($L_3^\top L_3 = I_{32}$)** and decomposes by BFS into `8` disjoint 4-column islands.
   - Super-S-box ANF degrees collapse to `[3, 3]` (no degree-4 `wxyz` term).
   - LATINCRYPT 2025 blind-column audit across all `32` single-column input diffs at $r_0 = 0$: blind-column histogram `{"8": 16, "13": 16}` (maximum `24 / 32` covered columns).
   - Analytical 5-round zero-sum certificate on the 48-point cube prefix derives **`198` universal equations** (`99` row $x$ + `99` row $z$, per-island nullities `[16, 12, 10, 12, 18, 0, 16, 15]`) with **`0` empirical violations** across 2 seeded independent 640-bit round-key trials (`396` checks).
   - Mitigation $L_3' = (7, 3, 11)$ verified involutive with `0` canceling masks.
2. **`COLM` (2-Query Splice Forgery over $\mathbb{F}_{2^{128}} = \mathbb{F}_2[x]/(x^{128}+x^7+x^2+x+1)$):**
   - Exact $3 \cdot 3^{-1} = 1$; fade relation $\sum_{k \in \{1,2,3,8,129\}} x^{k-1} = 0$ with $\mathrm{rank}\{x^0,\dots,x^{127}\} = 128$ and $\mathrm{rank}\{x^0,\dots,x^{128}\} = 128$ (minimum fade length $\ell = 130$).
   - Transplant condition $\deg(x^{m-1}/3) \le m - 2$ first holds at **`m = 129`**, yielding exact transplant index set **`{1, 3, 4, 5, 6, 7, 129, 130}`**.
   - $\mathrm{COLM}_\tau$ obstruction verified for all $\tau \in \{1,\dots,127\}$ ($\deg(x^\tau/3) = 127 > \tau - 1$).
   - Exact pure-$\mathbb{Q}$ J. Cryptol. 2024 Theorem 2 bound at $(q=2, s=1, a=6, m=390 \implies \sigma=795)$: `4428155 / 2^128 < 2^-105`, contradicted by probability-`1` splice forgery.
3. **`SBC-VOLE` (Single-Signature Linear Key Recovery over $\mathbb{F}_{2^{257}} = \mathbb{F}_2[x]/(x^{257}+x^{12}+1)$):**
   - Frobenius test $x^{2^{257}} \equiv x$ confirms irreducibility (`257` prime).
   - Clean-room end-to-end attack at full cryptographic dimension ($n = 130$, `256` secret bits, `257` public $\mathbb{F}_2$ equations from a single transcript `(\Delta, B, F_x, F_y, u, v)`): achieves $\mathbb{F}_2$-rank `255` (`free_nullity = 1`) on our seeded SplitMix64 instance and recovers all `256` secret bits identically via the public NSBC check.
4. **`Blender-256` Open Issues `#1` & `#2` (`@ziyang-theory`) & 2-Adic SNF Subgroup Steering:**
   - **Theorem 2 Parity Obstruction:** Starting from standard IV, $p(W^{\mathrm{IV}}) = (1, 0, 1, 0, 0, 1) \in \mathbb{F}_2^6$ traverses an 8-cycle of distinct non-zero vectors satisfying permanent invariants **`p_4 = p_0 ^ 1`** and **`p_5 = p_1 ^ 1`** under arbitrary message fragments.
   - **Ruling on Issue `#1` (`CONFIRMED — SCOPE OVERCLAIM`):** `Blender/paper/main.tex` Proposition 6 (`L758–L764`) and Contributions (`L139`) claim `24` bytes (`ceil(13/4) = 4` prefix words + `2` active words) as the *"global minimum"*, whereas the proof rules out $\ell \le 23$ strictly **within the two-step silent-carry healing family**.
   - **Ruling on Issue `#2` (`CONFIRMED — PROSE CONFLICT, ALGORITHM SOUND`):** §3.3 (`L644`) states *"steer $W_0, W_2, W_4, W_6 \in \{x, \neg x\}$ to enter $\mathcal{C}_x$"*, which is impossible from standard IV because $\mathrm{wt}(0)=0$ and $\mathrm{wt}(\mathtt{0xFFFFFFFF})=32$ are both even, forcing $p_0 = p_4 = 0$ in contradiction to Theorem 2 (`p_4 = p_0 ^ 1`). Live clean-room 12-step entry (`W'_0 in {x, ~x}`) confirms the **actual algorithm** never puts $W_0, W_2, W_4, W_6 \in \{x, \neg x\}$ — it locks onto the non-zero shifted phase constants $D^{(\phi)}$ preserving `p_4 = p_0 ^ 1`!
   - **2-Adic SNF Subgroup Closure over $(\mathbb{Z}/2^{32}\mathbb{Z})^8$:** Verified BOTH directly from the standard Blender-256 IV (`snf_from_iv_*`) AND against shipped `snf_audit_vectors.json` (`sha256: 6dbb69fa...`, `100/100` `GF(2)` XOR failures vs `100/100` exact modular superpositions): unshifted clean walks yield `[0, 0, 1, 1, 2, 2, 3, 3]` (index $2^{12}$), while multi-shifted clean walks close the rank defect to `[0, 0, 1, 1, 1, 1, 1, 1]` (maximal parity subgroup $H_{\mathrm{par}}$ of index $2^6 = 2^{m-2}$).

---

## 3. Pillar 3: Law-5 Exact-Operator Bridge to `mcproof`, `math0` & `siliquant`

1. **`TII-McEliece` Primal-Shortened Goppa Operator -> `Foundation-0/math0` (`PR #3/#4` `gfq` Codes):**
   - Clean-room $\mathbb{F}_{2^5}$ binary Goppa code $(n=24, m=5, t=3, k=9)$ with $g(X) = X^3 + X^2 + a X + 1$ yields `13` minimum weight-$7$ codewords ALL satisfying Theorem 1 ($\sigma'_S(X) = g(X)^2$, $e_2(z_S) = g_{t-1}^2$) and Theorem 2(3) ($\binom{7}{2} \equiv 3 \pmod 2$). Primal shortening to $n'=21$ preserves $g(X)$ identically (`6` codewords) while quadratically compressing the odd-weight relation feature count $F(d) = 1 + d + \binom{d}{2}$.
   - Exact pure-$\mathbb{Q}$ compression ratios: **`TII-125`** $(507, 9, 7 \to n'=237)$: `98347 / 15052 = 6.533816×`; **`TII-250`** $(1010, 10, 12 \to n'=467)$: `395606 / 60032 = 197803 / 30016 = 6.589919×` (`6.59×`). Campaign manifest (`c7bc0c0c...`): `94` solved (`89` Route A, `5` Route B, `55` first-bloods).
   - **Concrete `math0` Bridge:** Primal column-window shortening preserves alternant/Goppa locator invariants while shrinking degree-2 relation systems quadratically in $k' = n' - r$, directly supporting shortened-subcode weight/distance pruning in `math0`'s `gfq` linear-code verifier (`PR #3/#4`).
2. **`HAWK` Parity Sublattice & Exact Unimodular Gram Operator -> `math0` & `Moissanite-Labs/siliquant` (`lattice/`):**
   - Exact rank-$8$ clean-room verification via fraction-free Bareiss integer determinant:
     - Parity-congruence sublattice $\Lambda' = 2\Lambda_\tau + \mathbb{Z} w_0$ transform $H \in \mathbb{Z}^{8 \times 8}$ satisfies $|\det(H)| = 128 = 2^{n-1}$ and $\det(H G H^\top) = 2^{14} \det(G) = 2^{2(n-1)} \det(G)$, multiplying covolume by $2^{n-1}$ at fixed $\lambda_1$ (halving the asymptotic Hermite ratio and isolating $\pm V_\tau$ with spectral gap $\lambda_2/\lambda_1 = 2$; BKZ block-size drops `34 / 49 / 81` for `HAWK-256/512/1024`; `HAWK-256` Hermite ratio `4222/10000 < 1` forces required root Hermite factor `< 1`).
     - Exact triangular backward-substitution unimodular transform recovery ($U B_{\mathrm{raw}} = B_{\mathrm{good}}$, $|\det U| = 1$, $G_{\mathrm{red}} = U G_{\mathrm{raw}} U^\top$) preserves $\det(G)$ identically while compressing max Gram diagonal from `31,954` to `41` (`31954/41`, `779.37×`).
   - **Concrete `siliquant` & `math0` Bridge:** (a) Congruence-sublattice closure ($\Lambda' = 2\Lambda + \mathbb{Z} w_0$) provides an exact integer covolume/spectral-gap refinement operator for parity-constrained lattice codebooks (`D_n`/`E_8`); (b) Cholesky embedding + integer triangular unimodular recovery eliminates condition-number squaring ($\kappa(G) = \kappa(B)^2$) in Hessian-weighted lattice quantization (`siliquant` `experiments/lattice-vs-scalar-rounding-2026-11-15/`); (c) `BentSum/lean/` (`5` files, `0` banned constructs) serves as a clean Mathlib benchmark for `Proven-Commons/mcproof` and `math0` Hadamard/`CW(n,k)` support congruences.

---

## 4. Reproduction Commands

```bash
# 1. Offline standalone verification (recomputes all 3 mathematical pillars + replays pinned portal manifest)
python3 -I -B -W error symbiosis/stream/track-s14-minimax-cryptanalysis/minimax_cryptanalysis_audit.py --standalone --json

# 2. Live read-only audit against a local MiniMax-AI/Research checkout (@ 57842cef)
python3 -I -B -W error symbiosis/stream/track-s14-minimax-cryptanalysis/minimax_cryptanalysis_audit.py --live --research-dir <path/to/MiniMax-AI-Research> --output symbiosis/stream/track-s14-minimax-cryptanalysis/minimax_cryptanalysis_certificate.json

# 3. Assertion-free R5 adversarial & mutation-killing test suite
python3 -I -O -B -W error symbiosis/stream/track-s14-minimax-cryptanalysis/test_minimax_cryptanalysis_r5.py
```
