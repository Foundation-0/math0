# Cross-Field Operator Propagation from `anthropics/formal-math/vp-vnp` (`M1`–`M6`)

- **Scope & Origin:** Strictly typed cross-field propagation of the six algebraic, combinatorial, and formal-verification mechanisms (`M1`–`M6`) extracted from `anthropics/formal-math/vp-vnp` across four executable pure-$\mathbb{Z}/\mathbb{Q}/\mathbb{F}_2$ pillars paired with `13` live kernel-checked `Lean 4.36.0` theorems.
- **Arithmetic & Verification Discipline:** Pure-$\mathbb{Z}/\mathbb{Q}/\mathbb{F}_2$ (`fractions.Fraction` / `decimal.Decimal`, `0` production floats, `0` bare `assert`s, `0` external Python dependencies); pure-`Init` `Lean 4.36.0` (`0` external imports, `0` compiler warnings, `13/13` non-vacuous theorems).
- **Canonical Certificate:** `s82_vpvnp_propagation_certificate.json` (`1,721` B, `0o600`, file SHA-256 `10c1203cd9c9f80d4082f4cdbbd09f60624aa1d4fd6b49c70ec5d622f0d2f76b`, `payload_sha256` `ecf05db1bb683b19a4047850154f3fc2a6b87ae404536d52634e030cbc213502`).

---

## 1. Executive Summary & Strictly Typed Propagation Matrix (`M1`–`M6`)

Every transposition below enforces strict type fidelity: wherever lifting an operator across fields, floating-point precisions, or graph weights breaks an invariant, the exact algebraic obstruction is proved and witnessed explicitly rather than smoothed over by analogy.

| ID | Source Mechanism (`vp-vnp`) | Propagated Target & Exact Verified Artifact | Verified Explicit Non-Commutativity / Scope Obstruction |
| :-: | :--- | :--- | :--- |
| `M1` | Meixner crossing-wires (`Prop B.2`) & `CAT(0)` CN curvature (`Thm C.1`, `Rem D.3`) | `[8,4,4]` / `[16,11,4]` linear-code rank-metric witness (`det G = -1/4`) & 4-party `(Q, K, V, O)` crossing ranks `[1, 4, 4]` | Negative Gram curvature (`u^T (2G) u = -2 < 0`) blocks isometric Euclidean/$L_2$ embedding; Zorn spectral points bound asymptotic rates rather than finite-$N$ latency |
| `M2` | Flat-vs-contracting dichotomy (`Thm D.2`) & Strassen rerouting (`Thm A.6`, `App. G`) | Exact Strassen `⟨2,2,2⟩` ($f_{3,1}$) rank-`7` vs. naive `8` bilinear rerouting (`16/16` basis pairs, `343 < 512`, `7^10 < 2^29`) | `Thm D.2` is non-constructive (LEM + compactness); whether $\mathbb{R}/\mathbb{C}$ is flat or contracting remains open; asymptotic contraction does not automatically lower concrete small-$N$ rank |
| `M3` | `Lem F.2` tight rank-1 shear factorization in $U_n(\mathbb{F}_2)$ (`<= 4` / `<= 16` mult.) | Constructive 1D nearest-neighbor `CNOT` compiler (`184` verified circuits across `n = 4, 5, 6, 8`, `CNOT(0->7)` len `92`) | **Real-Shear Obstruction:** lifting $x_j = I + E_{j,j+1}$ to $\mathbb{Z}/\mathbb{Q}/\mathbb{R}$ breaks $\mathbb{F}_2$ carry-free involution and orthogonality ($\operatorname{tr}(S_8^\top S_8) = 9 \ne 8$, minimal polynomial $\lambda^2 - 3\lambda + 1 = 0$, $\kappa_2 = \phi^2 \in [2.61800, 2.61805] > 1$ vs. `WHT` $\kappa_2 = 1$) |
| `M4` | `Lem N.2` Laurent cutoff ($N = 2^L \Delta$) & `Prop N.4` scale shift ($\sigma_r: \varepsilon \mapsto \varepsilon^r$) | Pure-$\mathbb{Q}$ `CircularEP` DEQ pole control (`e* = 0 -> -7/3`, `N = 8`; `e* = 1/100 -> -1/100 * beta^{-1}`) & $\sigma_3$ isolation (`r=1 -> -1`, `r=3 -> 0`, `9/4`) | **BF16 Subnormal Floor:** exact in $\mathbb{Q}((\beta))$, yet 4 rounds of $\sigma_3$ at $\beta = 2^{-2}$ hit $2^{-162} < 2^{-126}$ (flushing below BF16 normal range), and $N = 2^L\Delta$ scales exponentially in depth $L$ |
| `M5` | `Prop E.10` unweighted balanced-cut identity ($9s(k-s) \ge 2k^2$) | Weighted-Cheeger lift on `128`-expert `Inkling 2 Mini` Zipf MoE (`1/4 > 2/9` unweighted vs. `Zipf-1` `0.110768`, `Zipf-2` `0.004694`) | **Heavy-Tail Collapse:** placing hot experts on one shard drops cross-shard traffic `2.0062x` (`Zipf-1`) and `47.3399x` (`Zipf-2`) below the unweighted `2/9` floor; `Prop E.10` requires uniform $K_k$ weights |
| `M6` | Isolated `Statement.lean`/`Challenge.lean` + dual-kernel `Lean + nanoda` + Table 3 parity | Standalone executable `aletheia` v2.3 Formal Trust Gates (`T-13`..`T-15`): `1/1` positive bundle passed, `6/6` adversarial controls killed | Dual-kernel & static anti-bypass checking eliminate kernel bugs and axiom smuggling, not natural-language specification drift or unformalized remarks (`Remark N.6`); semantic statement fidelity remains irreducible |

---

## 2. Pillar-by-Pillar Quantitative & Formal Results

### 2.1 Pillar 1 (`M1` + `M2`) — Strassen `⟨2,2,2⟩` Rerouting, Code-Subspace `CAT(0)` Curvature & 4-Party `(Q, K, V, O)` Crossing Wires

Implemented in `oracle_m1_m2_cat0_rerouting_and_codes()` (`s82_vpvnp_propagation_oracle.py`):

1. **Strassen `⟨2,2,2⟩` Exact Bilinear Rerouting:** All `16/16` elementary basis pairs $(E_{ab}, E_{cd})$ plus dense integer witness $A = \begin{pmatrix}3 & -7\\ 11 & 5\end{pmatrix}$, $B = \begin{pmatrix}-2 & 13\\ 17 & -19\end{pmatrix}$ ($AB = \begin{pmatrix}-125 & 172\\ 63 & 48\end{pmatrix}$) match naive $2\times 2$ multiplication identically using `7` scalar products instead of `8`, yielding exact contraction $7^3 = 343 < 512 = 8^3$ and $7^{10} = 282{,}475{,}249 < 536{,}870{,}912 = 2^{29}$ ($\omega < 2.9$). Certified over universal `Int` in `strassen_2x2_exact_rerouting` and `strassen_exponent_strictly_subcubic`.
2. **Linear-Code Rank Metric & Non-Euclidean `CAT(0)` Embedding:**
   - Extended Hamming `[8, 4, 4]` ($E_8$ Construction-A core): enumerating all `15` nonzero codewords verifies exact minimum Hamming weight `4`.
   - Extended Hamming `[16, 11, 4]` (`A_16` Construction-A core): $\mathbb{F}_2$ Gaussian elimination on its $5 \times 16$ parity-check matrix verifies exact rank `5` and code dimension `16 - 5 = 11`.
   - Embedding the 5-point `Mat_2(F_2)` rank-metric witness $\{0, E_{00}, E_{01}, E_{11}, E_{00}+E_{11}\}$ inside the linear-code operator space gives exact rational Gram determinant $\det G = -1/4 < 0$ and negative quadratic witness $u^\top (2G) u = -2 < 0$ at $u = (2, -1, 2, -2)^\top$ (certified in `linear_code_rank_metric_non_euclidean`).
3. **4-Party `(Q, K, V, O)` Meixner Crossing-Wires Attention Toy (`Prop B.2`):** Constructing the integral determinant polynomial $\Psi(X) = \det M \in \mathbb{Z}[X]$ over $|\Sigma_1| = |\Sigma_2| = 2$ ($\Theta = 16$) produces exact `QO|KV` flattening ranks `1` at $X^0$, `4` at $X^{16}$, and `4` at the crossing-wire point $X = 1$.

### 2.2 Pillar 2 (`M3`) — Constructive `Lem F.2` 1D Nearest-Neighbor `CNOT` Compiler & Real-Shear Obstruction

Implemented in `synthesize_cnot1d_rank1()` and `oracle_m3_cnot1d_compiler_and_real_shear_obstruction()`:

- **Verified 1D Nearest-Neighbor `CNOT` Synthesis over $U_n(\mathbb{F}_2)$:** For any cut $1 \le k < n$ and nonzero binary vectors $\xi \in \mathbb{F}_2^k, \omega \in \mathbb{F}_2^{n-k}$, `synthesize_cnot1d_rank1` compiles $I + \operatorname{upper\_right}(\xi\omega^\top)$ exclusively into elementary nearest-neighbor 1D `CNOT` gates $x_j = I + E_{j,j+1}$ ($0 \le j < n-1$):
  - **Exhaustive coverage:** `23/23` targets for $n = 4$ and `72/72` targets for $n = 5$.
  - **Structured long-range coverage:** `25/25` targets for $n = 6$ ($k=3$) and `64/64` targets for $n = 8$ ($k=4$), totaling **`184/184`** exact matrix-verified circuits.
  - **Observed tight generator multiplicity:** peak `4` per gate on endpoint-1 targets ($\xi_{k-1} = \omega_0 = 1$) and peak `16` in general; maximal-distance 8-qubit `CNOT(0 -> 7)` compiles to `92` nearest-neighbor 1D `CNOT` gates.
  - Certified in Lean for `U_4(F_2)` (`lem_F2_cnot1d_long_range_E03`, `cnot1d_involution`).
- **Exact Real-Shear Obstruction:** Lifting the elementary shear $S_8 = I_8 + E_{0,1}$ from $\mathbb{F}_2$ to $\mathbb{Z}/\mathbb{Q}/\mathbb{R}$ preserves $\det(S_8) = 1$, yet breaks both involution ($S_8^2 = I_8 + 2 E_{0,1} \ne I_8$) and orthogonality:
  - Exact Gram trace $\operatorname{tr}(S_8^\top S_8) = 6 + (1 + 2) = 9 \ne 8$.
  - The $2\times 2$ nontrivial Gram block $M = \begin{pmatrix}1 & 1\\ 1 & 2\end{pmatrix}$ satisfies the exact minimal polynomial $M^2 - 3M + I = 0$ ($\lambda^2 - 3\lambda + 1 = 0$, certified in `real_shear_minimal_poly_and_non_orthogonality`).
  - Integer `isqrt(5 * 10^8) = 22360` brackets $\kappa_2(S_8) = \phi^2 = \frac{3+\sqrt{5}}{2} \in [2.61800, 2.61805] > 13/5 = 2.6 > 1$ (certified in `real_shear_kappa_exceeds_26_tenths`), contrasting sharply with orthogonal Walsh–Hadamard (`WHT_8` / `BlockH4`, $\kappa_2 = 1$) used for MSE-preserving quantization.

### 2.3 Pillar 3 (`M4`) — Pure-$\mathbb{Q}$ Laurent Pole Control (`CircularEP` / `Prop N.4`) & BF16 Underflow Boundary

Implemented in `oracle_m4_laurent_circularep_and_rocket_isolation()`:

- **`CircularEP` Implicit DEQ Gradient $-\frac{1}{\beta}(E(x^\beta) - E_0)$:**
  - When free-phase relaxation converges exactly ($e^* = 0$), multiplying $-\beta^{-1}$ into $E_{\mathrm{diff}} = \frac{7}{3}\beta + \frac{5}{2}\beta^2 + \frac{11}{4}\beta^9$ cancels the $\beta^{-1}$ pole completely, yielding exact $[\beta^0] = -7/3$ (certified in `circularep_zero_residual_cancels_pole`).
  - Applying `Lem N.2`'s exact cutoff $N = 2^L\Delta = 8$ ($L = 3, \Delta = 1$) strips $\frac{11}{4}\beta^9$ while preserving all $[\beta^{\le 0}]$ coefficients identically (certified universally in `m4_laurent_cutoff_valuation_bound`).
  - Introducing a nonzero free-phase residual $e^* = 1/100$ immediately contaminates the gradient with an exact $-1/100 \cdot \beta^{-1}$ pole.
- **`Prop N.4` Scale-Shift Isolation ($\sigma_r: \beta \mapsto \beta^r$):** Composing an outer $\beta^{-2}$ pole ($P = 2$) with inner perturbation error gives minimum exponent `-1` (pole leak) at $r = 1 \le P$, whereas $r = 3 > P$ isolates all perturbation terms to $\beta^{\ge 1}$ (`min_exp = 0`) and recovers exact $[\beta^0] = 9/4$ (certified in `prop_N4_sigma_r_isolates_pole`).
- **Honest Finite-Precision Boundary (BF16):** Four composed rounds of $\sigma_3$ at $\beta = 2^{-2}$ yield exponent $-2 \cdot 3^4 = -162 < -126$ (the IEEE BF16 minimum normal exponent), demonstrating that exact algebraic isolation over $\mathbb{Q}((\beta))$ does not commute with unrescaled low-precision floating point.

### 2.4 Pillar 4 (`M5` + `M6`) — Weighted-Cheeger MoE Cut Collapse & Executable `aletheia` v2.3 Trust Gates (`T-13`..`T-15`)

Implemented in `evaluate_gate_t13`, `evaluate_gate_t14`, `evaluate_gate_t15`, `evaluate_aletheia_v23_trust_bundle`, and `oracle_m5_m6_weighted_moe_cheeger_and_trust_gates()`:

- **Weighted-Cheeger Lift on `128`-Expert `Inkling 2 Mini` Toy MoE (`M5`):**

| Routing Distribution ($k = 128$, `64/64` Hot/Cold Shard) | Cross-Shard Fraction $W(S)W(S^c)/W_{\mathrm{tot}}^2$ | Ratio Below `Prop E.10` Floor (`2/9`) | Weighted Conductance $\Phi_w(S)$ |
| :--- | :---: | :---: | :---: |
| Unweighted uniform ($w_i = 1$) | `1/4` (`0.250000`) | Above floor (`> 2/9 = 0.222222`) | `0.500000` |
| `Zipf-1` ($w_i = 1/i$) | `0.110768` | **`2.0062x`** below `2/9` | `0.873139` |
| `Zipf-2` ($w_i = 1/i^2$) | `0.004694` | **`47.3399x`** below `2/9` | `0.995284` |

  Both the unweighted floor `9 * s * (k - s) >= 2 * k^2` (`prop_E10_unweighted_balanced_cut`) and a finite heavy-tail counterexample beating `2/9` by `> 22x` (`weighted_moe_zipf_cut_beats_unweighted_floor`) are kernel-checked in `VpVnpPropagationCerts.lean`.

- **Executable `aletheia` v2.3 Formal Trust Gates (`T-13`..`T-15`, `M6`):**
  - `T-13` (Statement/Challenge isolation): forbids non-allowlisted imports in `Statement.lean`, non-`Statement` imports in `Challenge.lean`, and any module importing `Challenge.lean`.
  - `T-14` (Dual-kernel + pinned-SHA contract): requires 40-char lowercase hex SHAs on `comparator`, `nanoda`, and `mathlib`, `enable_nanoda = True`, strictly standard axioms (`propext`, `Quot.sound`, `Classical.choice`), and zero `sorry` outside `Challenge.lean`.
  - `T-15` (1:1 paper-to-Lean parity + gap honesty): verifies every `formalized = True` entry resolves to a declared Lean symbol and every `formalized = False` remark carries a non-empty `gap_reason`.
  - **Verification:** `1/1` `vp-vnp`-style positive bundle passes (`passed = True`), and `6/6` adversarial negative controls (`T13_STATEMENT_EXTERNAL_IMPORT`, `T13_CHALLENGE_IMPORTED_BY`, `T14_NANODA_DISABLED`, `T14_SORRY_OUTSIDE_CHALLENGE`, `T15_MISSING_LEAN_DECL`, and `Remark N.6` false formalization overclaim) are rejected fail-closed (`aletheia_v23_trust_gate_fail_closed`).

---

## 3. Live `Lean 4.36.0` Theorem Ledger (`VpVnpPropagationCerts.lean`)

Compiled live under `Lean 4.36.0` (`0` external imports, `0` warnings, `0` stderr, `static_clean = True`, pinned SHA-256 `5c774b97...`, exact-set `#print axioms` verification):

| # | Theorem (`S82VpVnpPropagationCerts.*`) | Pillar | Live Kernel Axioms |
| :-: | :--- | :---: | :--- |
| 1 | `strassen_2x2_exact_rerouting` | P1 (`M2`) | `[propext, Quot.sound]` |
| 2 | `strassen_exponent_strictly_subcubic` | P1 (`M2`) | `[]` (zero axioms) |
| 3 | `linear_code_rank_metric_non_euclidean` | P1 (`M1`) | `[propext]` |
| 4 | `lem_F2_cnot1d_long_range_E03` | P2 (`M3`) | `[propext, Classical.choice, Quot.sound]` |
| 5 | `cnot1d_involution` | P2 (`M3`) | `[propext, Classical.choice, Quot.sound]` |
| 6 | `real_shear_minimal_poly_and_non_orthogonality` | P2 (`M3`) | `[propext, Classical.choice, Quot.sound]` |
| 7 | `real_shear_kappa_exceeds_26_tenths` | P2 (`M3`) | `[]` (zero axioms) |
| 8 | `circularep_zero_residual_cancels_pole` | P3 (`M4`) | `[propext, Quot.sound]` |
| 9 | `m4_laurent_cutoff_valuation_bound` | P3 (`M4`) | `[propext, Quot.sound]` |
| 10 | `prop_N4_sigma_r_isolates_pole` | P3 (`M4`) | `[propext, Quot.sound]` |
| 11 | `prop_E10_unweighted_balanced_cut` | P4 (`M5`) | `[propext, Quot.sound]` |
| 12 | `weighted_moe_zipf_cut_beats_unweighted_floor` | P4 (`M5`) | `[]` (zero axioms) |
| 13 | `aletheia_v23_trust_gate_fail_closed` | P4 (`M6`) | `[]` (zero axioms) |

---

## 4. Verification Receipts & Frozen Package Inventory

All gates executed clean post-last-edit (`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1`, CPU-only):

- **CLI & Live Lean:** `--write`, `--check`, `--standalone` all match `payload_sha256 = ecf05db1bb683b19a4047850154f3fc2a6b87ae404536d52634e030cbc213502` (`pillars_passed = 4`); `--verify-lean` passes live `Lean 4.36.0` (`13/13` theorems, `0` warnings, pinned SHA-256 `5c774b97...`, zero-TOCTOU private temp execution, R10+ static anti-bypass clean blocking `import`, `notation`/`infix`/`prefix`/`postfix`, `declare_syntax_cat`/`syntax`/`elab`/`macro`, guillemet-unwrapped `debug.*`, comment/whitespace-separated bang-strings, raw strings, unterminated literals/guillemets, `initialize`, `run_cmd`/`run_meta`, `dbg_trace`/`throwError`, `native := !false` with `0` FP on `native := false`, and exact-set multi-line `#print axioms`).
- **Isolated Interpreter Parity + `umask 077` + Simulated CI `chmod 644` + Live `$PWD` Symlink Rejection:** `test_s82_r5.py` **`12/12 OK ×7`** (`-I -B`, `-I -O -B`, `-I -B -W error`, `PYTHONHASHSEED=42`, `umask 077`, CI `chmod 644` `--check`/`-I -B`/`-I -O -B`); live `cd -L sym_d && --check` / `--verify-lean` fail closed (`rc = 1`).
- **4-Surface Adversarial Fuzzer (`CLI` 25 + `FR1` 19 + `FR0` 19 + `SEC` 19):** **`82 / 82 PASS`** (`bypasses = 0`, `crashes = 0`), with strict `type(full_replay) is bool` and full 39/39 pillar-leaf semantic verification.
- **Mutation Coverage (`aletheia-fast-mutate --workers 4 --timeout 180 --max-mutants 0`):** **`109 / 109 (100.0%)`** (`s82_vpvnp_propagation_oracle.py` `9/9`, `verify_s82_vpvnp_propagation.py` `100/100`, `survived = 0`, `truncated = False`).
- **Null-Controlled Whole-File DFS AST `BoolOp` (`OP_SWAP + SUBCOND_DEL`):** **`136 / 136 (100.0%)`** (`s82_vpvnp_propagation_oracle.py` `25/25`, `verify_s82_vpvnp_propagation.py` `111/111`, `null_controls = 2/2`, `survived = 0`, **`timeouts = 0`**).
- **Dual `aletheia audit-check --lean-audit --strict-ancestors --safety-scan --scripts verify_s82_vpvnp_propagation.py test_s82_r5.py`:** Verified `PASS ×2` post-report freeze (`6` files, `2/2` R4, `1/1` Lean `0` findings/`0` notices, `0` leaks/asserts/CRLF/safety).

### Frozen 6-File Package Inventory (`5` Sibling SHA-256s + `REPORT.md`)

| File | Lines | Bytes | Mode | SHA-256 |
| :--- | ---: | ---: | :---: | :--- |
| `VpVnpPropagationCerts.lean` | `269` | `14436` | `0o644` | `5c774b978e9eaf918edfd63b4d85d01ce0740b45469c7c48b934f85c380f1dd8` |
| `s82_vpvnp_propagation_certificate.json` | `1` | `1721` | `0o600` | `10c1203cd9c9f80d4082f4cdbbd09f60624aa1d4fd6b49c70ec5d622f0d2f76b` |
| `s82_vpvnp_propagation_oracle.py` | `840` | `32947` | `0o644` | `40141a50a99b68c91929ad9085c17802d3572fb2ea081af4b60c588d33aecef1` |
| `test_s82_r5.py` | `910` | `49160` | `0o644` | `48b5ffd96bec55112195e8aa8f2e0c6e05775f48b1cf9da37f1e3d153b4638e9` |
| `verify_s82_vpvnp_propagation.py` | `929` | `36542` | `0o644` | `f5fa4fecc18a240520728f1b7ea513e556c852aefde762570c02e0853851545a` |
| `REPORT.md` | *(this file)* | *(external SHA)* | `0o644` | *(pinned externally to avoid circular self-hash)* |
