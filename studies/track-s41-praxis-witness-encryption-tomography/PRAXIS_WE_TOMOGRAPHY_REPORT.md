# Track S41 (Portals 43 + 45): Praxis Witness Encryption & `P = NP` Rank-Gap / Pólya Obstructions — Exact Tomography Report

## 1. Attribution & Scope (`N0` Prior Anchors vs. `N1` Executable Synthesis)

- **Track ID:** `TRACK-S41-PRAXIS-WITNESS-ENCRYPTION-TOMOGRAPHY`
- **Certificate Schema:** `aletheia.praxis_we_tomography.certificate.v1`
- **Oracle Class / Novelty:** `exact` / **`N1`** (zero floating-point literals, zero `float()`, zero bare `assert`, zero `.isdigit()`/`.isnumeric()`/`.isdecimal()`, zero `islink`/`is_symlink`, zero mathematical RNG; `secrets.token_hex(8)` is used solely for collision-free atomic temp filenames).
- **Grounded Prior Literature (`N0` — external theorems & parameterizations, explicitly attributed):**
  1. **Tse, Vanjani & Vesely (Nov 2026), *Praxis: Practical Witness Encryption for NP*:** BQS / QAP coset sumcheck (`Lemma 4.7`, `Eq. (4)`), rank-gap threat model (`Example 2.1`, `Fig. 4`, `Lemma 4.3`, `p. 19`), Frobenius conjugate lifting (`Example 5.2`, `Eq. (5)–(7)`, `Lemma 5.4`, `Fig. 6–10`), BN254 `Table 4` instantiation, `Proposition 5.7` element counts, `Section 5.4 (P1)–(P5)` admissibility, `Definition B.1` / `Lemma B.2` generic-group bound `E(u)`, `Lemma B.5` Moore determinant, `Appendix C` / `Proposition C.1`, and `Table 6` Lean-vs-Paper scope ledger.
  2. **Hair & Sahai (2026):** Witness encryption from bounded-factor MinRank (`Appendix C` basic construction `R=3` vs. `R=4` and `Proposition C.1`).
  3. **Pólya (1913), *Aufgabe 424*:** Non-existence of a $\pm 1$ entrywise sign pattern reducing the $3 \times 3$ permanent to the determinant over $\mathbb{Z}$ (Portal 45).
  4. **Lasserre (2001) / Schoenebeck (2008):** Sum-of-Squares (SOS) semidefinite pseudodistribution hierarchy — explicitly linked here to the exact rank-2 PSD mixture passing all quadratic tests on UNSAT `Example 2.1`.
  5. **Pocklington (1914) / Capelli / Sorenson–Webster (2015):** Deterministic primality certification via factored $F \mid (q-1)$ with $F^2 > q$, binomial irreducibility of $T^n - c_0$ over $\mathbb{F}_q$, and deterministic 12-base Miller–Rabin for $n < 3.317 \times 10^{24}$.
- **Novelty Contribution (`N1` — unified executable verification):**
  1. Pure-$\mathbb{Z}/\mathbb{Q}/\mathbb{F}_q/\mathbb{F}_{q^n}$ executable small-prime-field Praxis `Enc`/`Dec` engine (`q = 257`, `n = 4`, chunked `Fig. 9–10`) with honest key/message unmasking and fail-closed non-witness rejection.
  2. Unified exact rank-1/2/3/4 cheat classifier connecting Praxis rank-2 mixtures to Lasserre/SOS PSD moment matrices (`15/15` exact rational principal minors $\ge 0$) and Pólya's `0/512` vs. `512/512` $\mathbb{F}_2$ sign-cancellation collapse.
  3. Pure-$\mathbb{Z}/\mathbb{Q}$ deterministic audit of BN254's exact `Table 4` prime order $q$, `Proposition 5.7`, `Lemma B.2` rational $E(u)$ bounds, and `Appendix C` Hair–Sahai thresholds without floating-point rounding.
  4. Executable `Aletheia CS-19` sealed-witness bridge over the $\mathbb{F}_{257}$ Praxis oracle paired with a Zone-B hardened atomic `dir_fd` CLI and strict-keyset secondary auditor.

---

## 2. Four Exact Mathematical Pillars

### Pillar 1: Executable Small-Prime-Field Praxis Core Protocol (`q = 257`, `Fig. 6–10`)

Instantiates `Example 2.1` True BQS ($w_1 w_3 = 1$, $w_2(w_1 + w_3) = 0$, $w_j^2 = w_0 w_j$ with honest witness $w = (1, 1, 0, 1)$) inside the subgroup $H \subset \mathbb{F}_{257}^\times$ of order $16$ with extension $\mathbb{F}_{257}[T]/(T^4 - 3)$:

| Parameter / Check | Exact Value / Verdict |
|---|---|
| Field & Binomial Extension | $q = 257$, $n = 4$, $c_0 = 3$, $\omega = 3^{64} \bmod 257 = 241$; Capelli $3^{128} \equiv -1 \pmod{257}$ (`true`) |
| Packing / Chunking | $K_1 = 2$, $K_2 = 1$, $\nu = 2$, $D = 9$, $(J, \Delta) = (2, 5)$, $(J', \Delta') = (2, 2)$, $3n/2 = 6$ copies, $n(n+1)/2 = 10$ pairs |
| `Lemma 4.7` / `Eq. (4)` QAP Coset Sumcheck | `qap_rw_allowed_nu_ndiv_k = true`, `eq4_key_remainder_zero = true`, `eq4_oth_remainder_zero = true` |
| Negative Control ($w = (1,1,1,1)$) | `neg_control_non_passing_rejected = true` |
| `Example 5.2` / `Eq. (5)` / `Eq. (7)` | `example52_v_formula_exact = true`, `eq5_tie_divisions_exact = true`, `eq7_mask_identity_exact = true` |
| `Lemma 5.4` & Honest Key / Message Recovery | $\kappa_{\text{expected}} = \kappa_{\text{recovered}} = 65$, $c_w = 10$, $t = 2$, $r_w = c_w + t = 12$; `decryption_recovered_exact_message = true` |
| Ciphertext Commitment Digest | `0bf45d6cb0e43ea3173cee4ae42ad3630032925064a0a933da8c530c1201fde2` |

### Pillar 2: Rank-1/2/3/4 Cheat Classification, SOS PSD Witness & Pólya (1913) Obstruction

| Regime | Exact Construction & Certified Result |
|---|---|
| `Example 2.1` Witness Counts | True BQS: `1` witness `(1,1,0,1)`; UNSAT BQS ($w_1 w_3 = 1,\ w_2(w_1+w_3)=1$): `0` Boolean witnesses; Rank-1 honest moment matrix passes (`rank1_witness_passes = true`) |
| **Rank-2 Shared SOS/Praxis Cheat** | $W^{(2)} = \frac{1}{2}(u_1 u_1^\top + u_2 u_2^\top)$ with $u_1=(1,1,0,1), u_2=(1,1,1,1)$: exact $\mathbb{Q}$-rank `2`, passes all UNSAT quadratic tests over $\mathbb{Q}$, **all `15/15` principal minors $\ge 0$** (`size_1 = [1, 1, 1/2, 1]`, `size_2 = [0, 1/4, 0, 1/4, 0, 1/4]`, `size_3 = [0,0,0,0]`, `size_4 = [0]`, proving exact Lasserre degree-2 SOS PSD feasibility). Killed over $\mathbb{F}_{101}$ (`Fig. 4`: $\phi_1(u_1)=61, \phi_1(u_2)=94, \det = 68 \neq 0$) and killed by Praxis quadratic ties (`praxis_quad_ties_broken_by_repeat = true`) |
| **Rank-3 Tensor (`p. 19`) & Moore Det (`Lemma B.5`)** | Symmetric linear-tie tensor $W_c$ has exact $\mathbb{F}_{257}$-rank `3`, passes all linear ties (`all_linear_ties_hold = true`), fails Praxis quadratic ties (`quad_ties_broken_by_linear_tensor = true`), and alternating 3-unknown quadratic sum leaks nonzero row-0/diagonal (`quad_alt_sum_leaks_row0_or_diag = true`). `Lemma B.5` $3 \times 3$ Moore determinant over $\mathbb{F}_{257^4}$: independent forms yield `[0, 0, 96, 0] != 0`; linearly dependent control yields `[0, 0, 0, 0]` |
| **Rank-4 Alternating-Sum Cheat (`1 vs. 4` Tightness)** | Signed alternating sum over $\{0,1\}^4$ on 4 decoupled unknowns (`dim 5`) over $\mathbb{F}_{257}$: exact stacked rank `4`, `booleanity_passed = true`, `row0_zero = true`, `diag_zero = true`, `nonzero_stack = true`, and **all `3/3` Praxis ties hold** (`praxis_ties_all_3_hold = true`), confirming tightness of the rank-1 vs. rank-4 gap |
| **Pólya (1913) Exhaustive Obstruction** | Exhaustive enumeration of all $2^9 = 512$ binary $3 \times 3$ matrices & sign patterns: `512/512` satisfy $\operatorname{perm}(M) \equiv \det(M) \pmod{2}$ ($\mathbb{F}_2$ collapse), while **`0/512`** $\pm 1$ sign-flip patterns match all `6` permutations over $\mathbb{Z}$ (`max_permutation_matches_out_of_6 = 5`) |

### Pillar 3: Exact Pure-$\mathbb{Z}/\mathbb{Q}$ BN254 `Table 4` Admissibility, `Lemma B.2` & `Appendix C`

- **BN254 Prime Order $q$ & Deterministic Pocklington Primality:**
  - $t = 4965661367192848881$, $q = 36t^4 + 36t^3 + 18t^2 + 6t + 1 = 21888242871839275222246405745257275088548364400416034343698204186575808495617$.
  - Factored small prime-power divisor $F = 2^{28}\cdot 3^2\cdot 13\cdot 29\cdot 983\cdot 11003\cdot 237073\cdot 405928799\cdot 1670836401704629 \mid (q-1)$ has `161` bits ($F^2 > q$, `321 > 254` bits); each factor is deterministically verified prime via Sorenson–Webster 12-base Miller–Rabin, and base $a=5$ certifies `pocklington_prime_verified = true`.
- **`Table 4` Core & `(P1)–(P5)` Admissibility:**
  - $N = 391693$, $n_c = 1694$, $F_{\max} = 2047$, $\nu = 2048$, $|H| = 2^{22} = 4194304$, $D = 3861007$, $(J,\Delta) = (11, 351001)$ ($J\Delta = D + 4$), $(J',\Delta') = (11, 315392)$ ($J'\Delta' = \nu n_c$), $n = 4608$, $c_0 = 5$, $d_R = 64$, $k = 71$, $\ell = 6121$, $K_1 = 192$, $K_2 = 12$, $g = 1736375024658487$, $\theta = (2^{20}-1)/2^{221}$.
  - Divisibility: $q \equiv 1 \pmod{2d_R}$, $n \mid (q-1)$, $|H| \mid (q-1)$ all `true`.
  - Capelli irreducibility of $T^{4608} - 5$ over $\mathbb{F}_q$: $5^{(q-1)/2} \equiv -1 \pmod q$ and $5^{(q-1)/3} \not\equiv 1 \pmod q$ (`true`).
  - `g_bounds_exact = true` ($g^8 \ge 2^{405} > (g-1)^8$, $g^{-4} \le 2^{-202} < \theta < g^{-3} < g^{-2}$), `search_range_2B_plus_1_lt_q = true`, `p1_chunk_bounds_hold = true`, `p2_group_coverage_holds = true`, `p4_lifting_24beta4_lt_q3 = true` ($\beta = 243200 \cdot 10^{51}$ satisfies $2^{187.31} < \beta < 2^{187.32}$ and $24\beta^4 < q^3$), `p4_lifting_beta_2_188_lt_q3 = true`.
- **`Proposition 5.7` Counts & `Definition B.1` / `Lemma B.2` Rational $E(u)$:**
  - $n_1 = 151468429$, $n_2 = 28413964$, $2n_2 = 56827928$, $L_1 = 151468430$, $L_2 = 56827929$, $L_T = 2$, $L = 208296361$, $d_f = 11592627$, $\varepsilon_f = (d_f + 61)/(q - D) = 5796344 / 10944121435919637611123202872628637544274182200208017171849102093287902317305$.
  - Exact rational `E(2) < 2^{-122}` (`b2_e2_lt_2_neg122 = true`) and `E(2^{101}) - E(2) <= 1 - 2^{-100}` (`b2_e_diff_le_1_minus_2_neg100 = true`) with exact truncated margin `(1 - 2^{-100}) - (E(2^{101}) - E(2)) = 0.00000081...`.
- **`Appendix C` Hair–Sahai Basic Construction & `Proposition C.1`:**
  - $R = 3$ fails `Eq. (10)` ($m_3^4 < 100 \cdot 2^{199}$, `hs_r3_fails_eq10 = true`).
  - $R = 4$: $K = 219348150$, $m = 85917354266100$ satisfies $m^3 < m^4 < 100\cdot 2^{199} < m^5$ (`hs_r4_m4_fails_m5_passes_eq10 = true`).
  - `Proposition C.1` lower bound: $k_{\text{lb}} = 39888960295450910$, certified via exact integer power $k_{\text{lb}}^{100} > 2^{5514}$ (`hs_prop_c1_gt_2_55_14 = true`, i.e. $> 2^{55.14}$).

### Pillar 4: Honest Scope Ledger (`Table 6`) & Executable `Aletheia CS-19` Bridge

- **Exact Reduction-Loss & Curve-Margin Accounting:**
  - Reduction time `108` bits vs. MSIS Matzov estimate `207/2` (`103.5`) bits $\implies$ exact reduction loss `9/2` (`4.5`) bits (`reduction_loss_factor_sq = 512`, i.e., $(2^{9/2})^2 = 2^9$).
  - BN254 ETNFS estimate `103` bits vs. GGM target `100` bits (`etnfs_margin_above_ggm_bits = 3`), heavy-cheat lattice security `173` bits, paper-reported ciphertext size `"7.88"` GiB.
- **`Table 6` Lean-vs-Paper Delta Ledger (`4/4` rows certified):**
  - `T6-01`: Fixed Table 4 parameters & 256-bit messages/seeds in Lean vs. general `(P1)–(P5)` & 100-bit messages/seeds in paper.
  - `T6-02`: Opaque sign-class `name([kappa]_T)` key derivation in Lean vs. direct `[kappa]_T` in paper.
  - `T6-03`: Exhaustive short-multiple search & logged `H_key` oracle-call count in Lean vs. polynomial-time Lenstra/HNF `LIFT` (`Lemma B.9`) & unlogged monitor with explicit runtime $t_R$ in paper.
  - `T6-04`: Groth16 honest setup trapdoor & definition faithfulness remain outside the Lean kernel (`Table 5`).
- **Executable `Aletheia CS-19` Sealed-Witness Bridge ($\mathbb{F}_{257}$, $\tau = 25$):**
  - Commitment ciphertext SHA-256: `949ca5f6aec7ed7d249499b779b957f7e3f868c288cf559f9676c26031c24ade`.
  - Valid witness `(1, 1, 0, 1)` recovers exact `valid_witness_kappa = 21` and unmasks `"CS19-SEALED-KEY!"` (`valid_witness_unmasked_exact = true`).
  - Forged non-witness `(1, 1, 1, 1)` fails closed with `NON_WITNESS_REJECTED` (`invalid_witness_rejected = true`).

---

## 3. Honest Security & Verification Boundaries

1. **Small-Field Execution vs. Full BN254 Audit:** Pillars 1 & 4 execute full chunked `Fig. 9–10` `Enc`/`Dec` over $\mathbb{F}_{257}$ (`n=4`) in exponent space; Pillar 3 audits every `Table 4`, `Proposition 5.7`, `Lemma B.2`, and `Appendix C` equation exactly over $\mathbb{Z}/\mathbb{Q}$ without materializing the `7.88 GiB` BN254 group ciphertext.
2. **`secondary_audit_payload` vs. `full_replay=True`:** `verify_certificate_dict(..., full_replay=False)` runs `validate_certificate_payload(..., full_replay=False)` plus the field-complete strict-keyset `secondary_audit_payload`, which enforces top-level keys/metadata, strict non-short-circuit integer/string types, constant-time `hmac.compare_digest` ciphertext/commitment digest pins, exact `P1`/`P2`/`P3`/`P4` certified values, exact `Table 6` delta rows, and exact `N0` literature anchors (catching all `50` tested re-signed payload tampers under both `verify_certificate_dict(..., full_replay=False)` and standalone `secondary_audit_payload`). Because `secondary_audit_payload` imports exact parsing/evaluation primitives from `praxis_we_tomography_oracle.py`, it is an intra-package algebraic cross-check rather than a zero-shared-code independent verifier; `full_replay=True` performs full deterministic recomputation with constant-time SHA-256 comparison (`hmac.compare_digest`).
3. **POSIX Same-UID Threat Boundary:** File I/O uses per-component atomic `dir_fd` traversal (`O_RDONLY|O_DIRECTORY|O_NOFOLLOW`), logical `PWD` symlink verification via `dir_fd`, `65,536`-byte streaming capped reads (`max_bytes <= 64 MiB`, `O_NONBLOCK` FIFO refusal), and durable `0o600` atomic writes (`threading.Lock()` + monotonic counter + `secrets.token_hex(8)` + `32`-retry `EEXIST` + `os.fsync(tmp_fd)` + pre-replace `fstat(tmp_fd).st_nlink == 1` + target `st_nlink <= 1` refusal + `os.replace(..., dir_fd)` + `os.fsync(dfd)`). Within a shared writable directory, an adversarial process running under the same UID (or with `CAP_DAC_OVERRIDE`/`ptrace`) remains outside the unprivileged POSIX isolation boundary.

---

## 4. Frozen File Manifest & Post-Last-Edit Verification Receipts

### 4.1 Frozen Code & Certificate Manifest (`4` Core Artifacts + This Report = `5` Files)

| File | Lines | Bytes | Mode | SHA-256 |
|---|---:|---:|---|---|
| `praxis_we_tomography_oracle.py` | 1901 | 78388 | `0o644` | `e0a0b3d657d1c7d83ab183cd5cb15013f8feaf963bbd7be29d0bf04760bf88a3` |
| `praxis_we_tomography_audit.py` | 862 | 38965 | `0o644` | `7f691fda6fb174405b305927e527c5692566b493630810bf4b7f21f774fb7822` |
| `test_praxis_we_tomography_r5.py` | 1053 | 61810 | `0o644` | `11983fed602076dd3ec913f5d98d66ef5e3c959af92562d7d385d56765d06a82` |
| `praxis_we_tomography_certificate.json` | 1 | 6435 | `0o600` | `006e0eb496188cf7c603e70ecb388838ab1112ece30481717856dd0cc9f67902` |

- **Certificate Digests:**
  - `payload_sha256`: `48d928e05cead33863e88c3fb3bc644ee6006c01c4957c6c8c2c9be56efd57f6`
  - `certificate_sha256`: `71ac5d6d4416850cd62a4afbb78be5b06fa9493b93eb84ca4ce491be22f90b31`
  - `canonical_sha256`: `30f04920f43d549e59a96e4fb7d70cda1d2fd829cbf39be9231f391cbd529f7a`
  - `file_sha256` (canonical JSON + trailing LF): `006e0eb496188cf7c603e70ecb388838ab1112ece30481717856dd0cc9f67902`

### 4.2 Post-Last-Edit Sequential Verification Receipts (`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1`)

- **3-Mode R4 Parity (`-I -B`, `-I -O -B`, `-I -B -W error`) plus `-I -O -B -W error` and `PYTHONHASHSEED=42 -B`:**
  - Zero-arg CLI: `OK aletheia.praxis_we_tomography.certificate.v1 ...` identical across all 5 runs (`6328cdc0...`).
  - `--standalone --json`: SHA-256 `006e0eb496188cf7c603e70ecb388838ab1112ece30481717856dd0cc9f67902` (exact match to disk `0o600` certificate) across all 5 runs.
  - `--check praxis_we_tomography_certificate.json --json`: `valid=true`, `secondary_audit_passed=true` (`0f9d2e80...`) across all 5 runs.
  - `test_praxis_we_tomography_r5.py`: **`13/13 OK` ×5** (includes `50` re-signed tamper kills verified under both `verify_certificate_dict(..., full_replay=False)` and standalone `secondary_audit_payload`, `16T` distinct + `16T` same-target + `80T` barrier burst `0o600` writes, `>= 550` `renameat2(RENAME_EXCHANGE)` swaps, `>= 440` `os.link`/`os.unlink` hardlink races, FIFO non-blocking refusal, deleted-CWD refusal, `PWD` symlink refusal, `0` leaked temp files).
- **Live `aletheia v2.0.0 mutate --max-mutants 0 --work-root . --add-cwd`:**
  - `praxis_we_tomography_audit.py`: **`57/57` (`100.0%`, `survived=0`, `truncated=False`)**.
  - `praxis_we_tomography_oracle.py`: **`105/105` (`100.0%`, `survived=0`, `truncated=False`)**.
  - Combined: **`162/162` (`100.0%`)**.
- **Exhaustive `OP_SWAP + SUBCOND_DEL` AST `BoolOp`:**
  - `praxis_we_tomography_audit.py`: **`21/21` (`100.0%`, `surv=[]`)**.
  - `praxis_we_tomography_oracle.py`: **`116/116` (`100.0%`, `surv=[]`)**.
  - Combined: **`137/137` (`100.0%`)**.
- **Live 4-Surface Zone-B Adversarial Fuzzer:**
  - CLI (`fuzz_cli_checker`): **`23/23 PASS`** (`bypasses=0, crashes=0, baseline_ok=True`).
  - `verify_certificate_dict(..., full_replay=True)`: **`18/18 PASS`** (`bypasses=0, crashes=0, baseline_ok=True`).
  - `verify_certificate_dict(..., full_replay=False)`: **`18/18 PASS`** (`bypasses=0, crashes=0, baseline_ok=True`).
  - `validate_certificate_payload(..., full_replay=False)`: **`18/18 PASS`** (`bypasses=0, crashes=0, baseline_ok=True`).
  - Combined: **`77/77 PASS` (`100.0%`)**.
- **AST Hygiene & `aletheia v2.0.0 audit-check`:**
  - `0` AST float literals, `0` `float()` calls, `0` bare `assert`s, `0` `.isdigit()`/`.isnumeric()`/`.isdecimal()`, `0` `islink`/`is_symlink`, `0` CRLF, `0` host-path/private-repo leaks, `0` `.pyc`/`__pycache__` files, `FILE_COUNT = 5`.
  - `aletheia v2.0.0 audit-check . --strict-ancestors --safety-scan --scripts praxis_we_tomography_audit.py test_praxis_we_tomography_r5.py`: **`PASS`** (`5` files, `2/2` script parity checks passed, `0` findings).
