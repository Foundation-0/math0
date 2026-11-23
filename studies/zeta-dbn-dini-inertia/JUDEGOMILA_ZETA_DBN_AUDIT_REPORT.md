# AUDIT-049: Read-Only Aletheia Tomography & Cross-Domain Operator Synthesis of `judegomila/{zeta-explorer,dbn-lambda-01787854-candidate-audit}`

- **Audit ID:** `AUDIT-049` (Wave 2 Round 4B, Arm `R4B-1`)
- **Oracle Class:** `exact+anchor`
- **Honest Novelty Classification:** **`N1`** (strict read-only external tomography, zero-float reference hardening closing `J-01`/`J-02`, live `aletheia v1.2.0` CLI defect discovery, and exact $\mathbb{Q}/\mathbb{Q}[i]$ cross-domain operator correspondence; all upstream mathematical theorems strictly quarantined as `N0`)
- **Read-Only Posture:** `100%` read-only on all external repositories (`0` writes, `0` PRs, `0` issues, `0` external comments; `git status --porcelain` verified empty on both pinned clones)
- **Pinned Read-Only Sources (External, Not Vendored in `math0`):**
  - `judegomila/dbn-lambda-01787854-candidate-audit` @ `a74738deb6d5e0f76887cb36901da08b68dca705`
  - `judegomila/zeta-explorer` @ `694eb35f9144ad223d6f8a6afa7398a116146b1b`
- **Standalone vs. External Audit Boundary:** Running `judegomila_zeta_dbn_tomography.py`, `hardened_dini_and_r5_mutator.py`, and `test_judegomila_r5.py` in standalone `math0` recomputes **100% of the pure-$\mathbb{Q}/\mathbb{Q}[i]$ mathematics live** (Part 3A Polymath 15 exact rational identities, Part 3B `-O` negative-truncation proof, Part 4 Sylvester–Schur inertia / $\mathbb{Q}[i]$ singular Schur 4-axiom Moore–Penrose / degree-4 backward-heat PDE polynomial-coefficient & 3-point residual witness, and all 12 R5 hardened-Dini test groups). Parts 1, 2, 3B–3E external clone SHA256SUMS, 326-file Lean 4 census, 10/10 `dbn-audit` subprocess replays, and `aletheia/cli.py:94` CLI bug reproduction require the unvendored read-only clones and external `aletheia` checkout; in standalone mode, those sections emit `"external_repos_verified_in_this_run": false` (and `--require-live-repos` fails closed with `FileNotFoundError`).

---

## 1. Law-2 Steelman: What `judegomila` Built Exceptionally Well

Before reporting any hardening gaps, an honest Law-2 steelman must recognize that `dbn-lambda-01787854-candidate-audit` and `zeta-explorer` independently implement several of the highest-rigor computational-proof disciplines in our own Aletheia framework:

1. **Cryptographic Artifact Sealing (`100%` Integrity):**
   - `dbn-audit/SHA256SUMS`: **`443 / 443`** files verified bit-identical (`0` mismatches).
   - `zeta-explorer/research-checkpoints/rh-arithmetic-theta-2026-11-20/geometric-compression/SHA256SUMS`: **`27 / 27`** files verified bit-identical (`0` mismatches).
2. **Clean Lean 4 Trust-Boundary Discipline Across `326` `.lean` Files (`aletheia v1.2.0 --lean-audit`):**
   - **`dbn-audit` (`25` `.lean` files: `21` in `lean/aristotle/` + `4` top-level):** **`0` `sorry`, `0` `axiom`, `0` `native_decide`, `0` `unsafe`/`implemented_by`/`partial`/`debug.skipKernelTC`, `0` notices.**
   - **`zeta-explorer` (`301` `.lean` files):** **`0` `native_decide`, `0` `unsafe`, `0` `implemented_by`, `0` `partial`, `0` `debug.skipKernelTC`.** All `105` Lean files in `formalization/lean-aristotle/` (all `20` Aristotle projects, including `frozen-rung/Inertia.lean` and `flow_blindness/RequestProject/Main.lean`) have **`0` hard trust escapes and `0` notices**. All `75` hard findings (`51` `LEAN4_SORRY`, `24` `LEAN4_AXIOM`) are cleanly isolated in explicitly marked exploratory/draft directories (`formalization/lean/`, `formalization/lean-mathlib-probe/`, `lean/LambdaAttack/`, `research-checkpoints/`).
   - Moreover, `flow_blindness/RequestProject/Main.lean:31-34` explicitly upgrades the earlier `axiom H : ℝ → ℂ → ℂ` of `MathlibBridge.lean:126` into a universally quantified variable `H` so every theorem holds with zero axioms.
   - The sole notice in `formalization/lean/qrh-lambda/QrhLambda/Hyps.lean:59` (`LEAN4_EXISTS_IMPLICATION_NOTICE`) was inspected verbatim and confirmed **100% benign** — it is an existential inside the *antecedent* `(∃ s ∈ Set.Icc t₀ t₁, ¬ TailBelow s (β s)) → ...`, not a vacuous `∃ x, P x → Q` conclusion.
3. **Independent Convergent Invention of Aletheia R4 & R5:**
   - `verify.sh` sanitizes `PYTHONOPTIMIZE`, `PYTHONPATH`, `PYTHONHOME`, and `verify_assembly_1787854.py:14-16` explicitly refuses `sys.flags.optimize` (`exit 2`).
   - `verifiers/verify_prop410_arb_logs.py` enforces strict banner/parameter/order/ball/endpoint/source/proof-note bindings, and its companion `verifiers/verify_prop410_arb_mutation.py` achieves an astonishing **`25 / 25` (`100.0%`, `0` survivors)** AST mutation kill rate under live `aletheia v1.2.0 mutate`!
   - `verify_assembly_1787854.py` explicitly labels external mathematical imports with `[CITED THEOREM INPUT]` and `[CITED CLASSICAL INPUT]`, separating machine-checked certificates from cited theorems (Platt–Trudgian Theorem 1, Polymath 15 Theorem 1.2).
4. **Sound FLINT/Arb C Interval Hygiene (Audited Verbatim Across 4 C Sources):**
   - `verify_prop410_arb.c` refuses `wp < 256`, uses `arb_union` across parameter boxes, extracts exact directed endpoints (`arb_get_ubound_arf` / `arb_get_lbound_arf`), and checks `arb_is_negative` on exact scaled rational differences.
   - `TloopSinglemat_closed_cert.c` checks `arb_is_int`/`arb_is_positive`, marches dyadically with `ARF_RND_FLOOR`, evaluates whole prisms `t_box = arb_union(t, t_next)`, enforces strict winding `< 1/4`, and implements the `2*(num-1)` fix.
   - `verify_triangle_y_dini_arb.c` proves `arb_contains(ybox, yexact_lo) && arb_contains(ybox, yexact_hi)` directly in Arb before auditing all four Euler-prime legs, using `ARF_RND_CEIL` ratio reporting after strict `arb_lt(numerator, denominator)`.
   - `lemma_sweep_p235711.c` uses conservative `ARF_RND_FLOOR` storage.
5. **Independent Exact-Rational Polymath 15 Theorem 1.2 Re-Verification + `10 / 10` Stdlib Replays:**
   - Every exact rational weld identity checks cleanly in pure `Fraction` arithmetic (zero floats):
     - $t_0 + y_0^2 / 2 = \frac{129}{800} + \frac{87677}{5000000} = \frac{893927}{5000000} = 0.1787854$
     - $T_{\mathrm{PT}} - X/2 = 3000175332800 - \frac{6000000185827}{2} = \frac{350479773}{2} > 0$
     - $y_0^2 - (1809/10000)^2 = \frac{234599}{10^8} > 0$
     - $y_{\mathrm{box,lo}}^2 < y_0^2$ and $1 - 2 t_0 = \frac{271}{400} < y_{\mathrm{box,hi}}^2$
     - Finite window count $N_{\mathrm{mid}} - N_0 + 1 = 3840000 - 690988 + 1 = 3149013$
     - Proposition 4.10 exact margin $T_{\min} - E_{\max} = \frac{557871094787662151}{10^{24}} > \frac{557}{10^9}$
     - Dini exact worst slack $1 - 0.99999860767275095 = \frac{27846544981}{20000000000000000} \approx 1.39232724905 \times 10^{-6} > 0$
   - All **`10 / 10`** stdlib-only verifiers in `dbn-audit/verifiers/` pass live read-only replay (`exit 0`, exact sentinel matched). *(Note honestly: `8` additional verifiers in `dbn-audit` require external `mpmath`, and C recompilation requires `libflint`/`libarb`, neither of which is installed in the clean stdlib audit environment; those 8 scripts were inspected statically rather than executed.)*

---

## 2. Law-3 Adversarial Tomography: Concrete Zero-False-Positive Findings (`J-01`–`J-05` + `ALETHEIA-CLI-01`)

None of the hygiene findings below invalidate the published candidate bound $\Lambda \le 0.1787854$. Every finding is a concrete, reproducible verification-hardening gap or cross-domain structural discovery:

| ID | Target | Exact Finding | Live Evidence | Reference Closure |
|---|---|---|---|---|
| **`J-01`** | `dbn-audit/verifiers/verify_triangle_y_dini_logs.py` & `verify_triangle_y_dini_arb.c` | **Unmutated referee-added log parser for the thinnest load-bearing gate (`slack = 27846544981/20000000000000000`):** Unlike `verify_prop410_arb_logs.py` (`25/25 = 100%` killed under `aletheia mutate`), `verify_triangle_y_dini_logs.py` has no mutation suite (**`5/20 = 25%`** self-run kill rate, **`15` survivors**). Specifically: (a) `bits` in `audit_log(path, bits)` is unused and `verify_triangle_y_dini_arb.c` omits `PREC` from its banner, so aliasing the 180-bit and 256-bit logs passes silently; (b) `RATIO_RE.search(row)` accepts trailing junk or duplicate `ratio_ub=`; (c) `text.count(leg) == 1` does not bind `(P, N_lo..N_hi, patterns=3^k)` to its exact `PASS P=` line in order; (d) total line count (`6`) and witness-box containment `[y_lo, y_hi] ⊆ ybox` are unchecked. | `aletheia mutate` live: `5/20` (`25%`) on `verify_triangle_y_dini_logs.py` vs `25/25` (`100%`) on `verify_prop410_arb_logs.py`. | `hardened_dini_and_r5_mutator.py` + `test_judegomila_r5.py`: **`37/37` (`100%`, `0` survivors)** under `aletheia mutate`; passes live on both sealed logs! |
| **`J-02`** | `dbn-audit/verifiers/verify_tail_1787854_{160,256}.py:131,137`, `verify_prop410_arb_mutation.py:250`, and `zeta-explorer/.../geometric-compression/*.py` | **Bare `assert`s on numerical trust paths (`5` in `dbn-audit/verifiers/`, `32` in `geometric-compression/`):** While `verify_assembly_1787854.py` guards `sys.flags.optimize`, invoking `verify_tail_1787854_{160,256}.py` directly under `python3 -O` strips `assert v >= 0` in `floor_trunc`/`ceil_trunc`, causing negative `Fraction(-1, 100)` with `digits=2` to format silently as **`"-1.99"`** (a `199×` silent magnitude corruption via Python's floor `divmod(-1, 100) == (-1, 99)`!). In `geometric-compression/check_frame_geometry.py`, all core `eq`/`nonnegative`/`positive` checks are bare `assert`s, making all 10 checks pass as silent no-ops under `python3 -O`. | AST census (`5` + `32` exact sites) + live algebraic proof `divmod(-1, 100) -> "-1.99"`. | `safe_floor_trunc` & `safe_ceil_trunc` in `hardened_dini_and_r5_mutator.py` (`-O`-immune explicit `HardenedAuditError`). |
| **`J-03`** | `dbn-audit/verifiers/verify_native_binding.py:147,216,219` | **Global RNG hygiene (minor advisory):** Uses module-global `random.seed(1_787_854)` + `random.uniform(...)`. Confirmed **deterministic and seeded** (not unseeded!), so not a soundness bug — recommended hygiene upgrade is an isolated `rng = random.Random(1_787_854)`. | AST call scan `[(147,'random.seed'), (216,'random.uniform'), (219,'random.uniform')]`. | Isolated `random.Random(...)` instance. |
| **`J-04`** | `dbn-audit/OPEN_REVIEW_QUESTIONS.md` & `EXTERNAL_REFEREE_REPORT_2026-07-28.md` | **Documented external analytic trust boundary (confirmed verbatim):** Even with `443/443` seal + full FLINT/Arb replays, `dbn-audit` transparently leaves 3 prose-only analytic steps outside machine proof (`B_t ≠ 0` on `ℝ`, `t > 0 → t = 0` dominated-convergence limit of Lemma 8.4/Thm 1.3, and the Dini upper-derivative derivation) plus the cited Platt–Trudgian height `3_000_175_332_800` and Polymath 15 Thm 1.2. | Confirmed verbatim in `verify_assembly_1787854.py:203-210,268-271` and docs. | Explicit `[CITED THEOREM INPUT]` annotation discipline (extracted back into Aletheia!). |
| **`ALETHEIA-CLI-01`** | Our own `publish/aletheia/aletheia/cli.py:94` (`v1.2.0`) | **Live `argparse` overwrite bug discovered while auditing `zeta-explorer`:** `p_aud.add_argument("--allow-project-import", nargs="*", default=[])` uses default `action="store"`. Passing repeated flags `--allow-project-import Mathlib --allow-project-import RequestProject` silently overwrites `["Mathlib"]` with `["RequestProject"]`, causing `Mathlib` imports to still fail `LEAN4_NON_INIT_IMPORT`! | Live in-memory `build_parser().parse_args(...)` repro in `judegomila_zeta_dbn_tomography.py` Part 2 (`repeated_flag_parsed == ["RequestProject"]` vs `grouped_flag_parsed == ["Mathlib", "RequestProject"]`). | `aletheia v1.2.1` 1-line fix: `action="extend", nargs="+"` at `aletheia/cli.py:94`. |

---

## 3. Complete `aletheia v1.2.0` Lean 4 Census (`326` `.lean` Files)

| Repository & Directory Bucket | `.lean` Files | Hard Findings | Notices | Breakdown |
|---|---:|---:|---:|---|
| `dbn-audit/lean/aristotle/` | 21 | **0** | 0 | Clean |
| `dbn-audit/` (top-level) | 4 | **0** | 0 | Clean |
| **`dbn-audit` Subtotal** | **25** | **0** | **0** | **Zero trust escapes** |
| `zeta-explorer/formalization/lean-aristotle/` (`20` projects) | 105 | **0** | 0 | Clean (`Inertia.lean`, `flow_blindness/Main.lean`, etc.) |
| `zeta-explorer/formalization/lean/qrh-lambda/` | 79 | **0** | 1 | `Hyps.lean:59` benign antecedent existential notice |
| `zeta-explorer/formalization/lean/` (other) | 61 | 4 | 0 | `4` `sorry` in `DeBruijnNewman/Basic.lean` |
| `zeta-explorer/formalization/lean-mathlib-probe/` | 13 | 2 | 0 | `1` `sorry` (`EntireLP.lean:353`), `1` `axiom H` (`MathlibBridge.lean:126`) |
| `zeta-explorer/lean/LambdaAttack/` | 8 | 25 | 1 | `2` `sorry`, `23` `axiom`, `1` vacuous `: True := trivial` (`EmpiricalSweep.lean:139`) |
| `zeta-explorer/research-checkpoints/` | 32 | 44 | 0 | `44` `sorry` in documented draft statement skeletons (`rh-push-2026-11-16/fleet-lanes`) |
| `zeta-explorer/` (other) | 3 | **0** | 0 | Clean |
| **`zeta-explorer` Subtotal** | **301** | **75** | **2** | **`51` `LEAN4_SORRY`, `24` `LEAN4_AXIOM`; `0` `native_decide`/`unsafe`/`partial`/`skipKernelTC`** |
| **Combined Total** | **326** | **75** | **2** | Zero false positives |

---

## 4. Beyond-Language Cross-Domain Operator Isomorphisms (`zeta-explorer` $\longleftrightarrow$ Expedition `SF-01`–`SF-04`)

Every structural correspondence below is backed by an **independent, pure-$\mathbb{Q}$ / pure-$\mathbb{Q}[i]$ (zero-float, zero-SymPy) executable proof** in `judegomila_zeta_dbn_tomography.py` (Part 4):

1. **`frozen-rung/Inertia.lean` $\longleftrightarrow$ `SF-01` Sylvester–Schur Inertia & Compression Monotonicity (`AUDIT-027`/`041`/`043`/`044`):**
   - `FrozenRung.negIndex_fromBlocks_schur` proves $\mathrm{ind}_-(Q) = \mathrm{ind}_-(C) + \mathrm{ind}_-(A - B C^{-1} B^{\mathsf{H}})$ and compression monotonicity $\mathrm{ind}_-(P^{\mathsf{H}} Q P) \le \mathrm{ind}_-(Q)$ in zero-sorry Lean 4.
   - Our pure-$\mathbb{Q}$ first-nonzero-pivot 1x1/2x2 hyperbolic symmetric congruence engine (`exact_symmetric_inertia_q`) verifies the exact identity on both a passive `C > 0` $5\times 5$ block form (`Q:(3,0,2) = C:(2,0,0) + Q_eff:(1,0,2)`) and an active zero-diagonal hyperbolic block `C = [[0,2],[2,0]]` (`Q:(3,0,2) = C:(1,0,1) + Q_eff:(2,0,1)`), plus compression monotonicity `ind_-(P^T Q P) = 2 <= 2`.
2. **`geometric-compression/check_frame_geometry.py` $\longleftrightarrow$ `AUDIT-002` `R_opt` Blindness & `AUDIT-027`/`039`/`041` Singular Schur Pseudoinverse:**
   - **Indefinite Trace-Ratio Control (`check_indefinite_trace_control`):** On `diag(-1, 1, ..., 1)` ($n = 100$), $\mathrm{tr} = 98$, $\mathrm{tr}(M^2) = 100$, so normalized ratio $R = n\,\mathrm{tr}(M^2)/\mathrm{tr}(M)^2 = \frac{2500}{2401} < \frac{21}{20}$ despite having eigenvalue $-1 < 0$ — the exact same structural blindness behind our `CS-11` / `R_opt` falsification (`AUDIT-002`, `AUDIT-045`).
   - **Singular Schur Complement (`check_pseudoinverse`):** Using pure Gaussian rationals $\mathbb{Q}[i]$ (`(Fraction, Fraction)` pairs, zero SymPy), we verify all 4 Moore–Penrose axioms for rank-1 $D = C_e^{\mathsf{H}} C_e = \begin{pmatrix}2&2\\2&2\end{pmatrix}$ ($D^+ = \frac{1}{8}\begin{pmatrix}1&1\\1&1\end{pmatrix}$), range compatibility $D D^+ B = B$, exact orthogonal projector $\Pi = C_e D^+ C_e^{\mathsf{H}}$, Schur–geometric residual equality $E - B^{\mathsf{H}} D^+ B = C_o^{\mathsf{H}}(I - \Pi)C_o$, exact minimum squared distance $y^{\mathsf{H}}(E - B^{\mathsf{H}} D^+ B)y = \|C_o y - C_e x_{\min}\|^2 = 3$ for $y = (2, 1+i)^{\mathsf{T}}$, and exact normal-equation orthogonality $C_e^{\mathsf{H}}(C_o y - C_e x_{\min}) = 0$.
3. **`flow_blindness/RequestProject/Main.lean` + `engine/ROADMAP.md` (`10` Adversarial Controls) $\longleftrightarrow$ `SF-04` / Aletheia Law 3:**
   - `FlowBlindness.softClass_noGo` proves that any class of profiles invariant under backward heat flow ($\Phi \mapsto e^{-\varepsilon u^2}\Phi$) and containing the genuine profile cannot prove RH, given $0 \le \Lambda$ (Rodgers–Tao).
   - We verify an exact degree-4 rational backward-heat polynomial witness $H_t(z) = z^4 - 12(t - \Lambda) z^2 + 12(t - \Lambda)^2$ by checking both exact monomial-coefficient cancellation in $\partial_t H_t + \partial_z^2 H_t$ (`coeff_z2 = -12 + 12 = 0`, `coeff_tau = 24 - 24 = 0`, `pde_polynomial_coeffs_zero: true`) and 3 rational sample-point residuals (`pde_3point_residuals_all_zero: true`), with $\mathrm{IsDBNConstant}(H, \Lambda)$ holding for both $\Lambda = 0$ (RH witness) and $\Lambda = 1/5$ (positive-$\Lambda$ Davenport–Heilbronn control), demonstrating concretely why backward-invariant predicates collapse at $t = -1$.
   - We verify all `10` graph controls in `research-checkpoints/rh-push-2026-11-16/engine/ROADMAP.md:13` (`ctl-DH`, `ctl-HEAT`, `ctl-TW+`, `ctl-TW-`, `ctl-EA`, `ctl-NR`, `ctl-B`, `ctl-U`, `ctl-THW`, `ctl-PA`) — an independent convergent parallel to Aletheia Law-3 / R5 negative controls!
4. **`klein-annulus-coupling-2026-11-14/README.md` $\longleftrightarrow$ `SF-01` + `AUDIT-042`/`043` Annular/Horizon Blindness:**
   - Its core head-null obstruction $E - B^* D^{-1} B \succeq 0$ and $E_{KK} - E_{KR} A_R^{-1} E_{RK} \succeq 0$ is structurally isomorphic to our `SF-01` fiber-elimination Schur pushforward across boundary/horizon cuts.

---

## 5. Reverse Extractions for `Foundation-0/aletheia` v1.2.1+

1. **Fix `aletheia/cli.py:94` (`ALETHEIA-CLI-01`):** Change `--allow-project-import` from `nargs="*"` to `action="extend", nargs="+"` so repeated `--allow-project-import` flags accumulate instead of silently overwriting earlier prefixes.
2. **Adopt `[CITED THEOREM INPUT]` Tagging:** Borrow `dbn-audit/verifiers/verify_assembly_1787854.py`'s explicit distinction between machine-verified gates and prose/cited theorem premises into `aletheia`'s audit-receipt schema.
3. **Adopt Strict Arb-Ball & Multi-Control Templates:** Add a reusable stdlib Arb-ball `[mid +/- rad]` parser + non-aliasing multi-precision check (`hardened_dini_and_r5_mutator.py`) and an adversarial control-matrix table template (inspired by `zeta-explorer`'s 10 `ctl-*` controls).
4. **Refine `LEAN4_EXISTS_IMPLICATION_NOTICE`:** Distinguish antecedent existentials `(∃ x, P x) → Q` (benign, as in `QrhLambda/Hyps.lean:59`) from unparenthesized vacuous-risk `∃ x, P x → Q` to keep `aletheia` notice signal razor-sharp.

---

## 6. Law-4 Prior-Art Quarantine (`N0` vs. `N1`)

| Classification | Scope |
|---|---|
| **`N0` (Upstream / Classical Prior Art — NOT claimed as new)** | Polymath 15 Theorem 1.2 (Rodgers–Tao, Polymath 15, 2019); Platt–Trudgian RH height verification $T_{\mathrm{PT}} = 3{,}000{,}175{,}332{,}800$ (2021); Rodgers–Tao $\Lambda \ge 0$ (2020); `judegomila`'s candidate $\Lambda \le 0.1787854$ proof pipeline, FLINT/Arb certificates, `verify_prop410_arb_mutation.py`, Aristotle Lean 4 formalizations (`Inertia.lean`, `flow_blindness`), `check_frame_geometry.py`, and 10-control RH obstruction map; Sylvester's law of inertia & Moore–Penrose pseudoinverse Schur complement identities. |
| **`N1` (Our Verified Engineering & Cross-Domain Audit Contributions)** | Complete `326`-file `aletheia v1.2.0 --lean-audit` census across both pinned repos (`0` FPs); live `aletheia mutate` head-to-head benchmark (`25/25` Prop410 vs `5/20` unmutated Dini vs `37/37` hardened Dini); hardened zero-float `-O`-immune reference Dini verifier & truncation formatters closing `J-01`/`J-02` (`100.0%` R5 killed); discovery & reproduction of `aletheia/cli.py:94` `--allow-project-import` overwrite bug; pure-$\mathbb{Q}/\mathbb{Q}[i]$ zero-SymPy cross-domain operator isomorphism probes bridging `zeta-explorer` to `SF-01`/`SF-04`/`AUDIT-002`/`027`/`041`/`043`. |

---

## 7. Verification Artifacts, Reproducibility & Falsification Criteria

- **Artifacts in `studies/zeta-dbn-dini-inertia/` (Standalone 4-Mode Isolated `-I` Digests):**
  - `judegomila_zeta_dbn_tomography.py` (4/4 isolated `-I` standalone stdout SHA-256: `d073a29161d54a402c2cd081498c59a11def20d45efa3f6500148aad9c20bbdf`; `AUDIT_049_CANONICAL_SHA256`: `66aee283a7183f6898a816c69227cb2f11e5177b75f7e76401c7dc74a580ff49`; `0` floats in JSON; `0` bare asserts; fails closed with `FileNotFoundError` under `--require-live-repos` when external clones are absent)
  - `hardened_dini_and_r5_mutator.py` (4/4 isolated `-I` standalone stdout SHA-256: `e907524d267a0b04e69ea9f2e516e8d65acdda9bae276c9c8a63523498c39390`; **`37/37` (`100.0%`, `0` survivors)** under external `Foundation-0/aletheia v2.0.0 @ 7227bcc5` — pinned receipt in [`../ROUND4_MUTATION_RECEIPTS.json`](../ROUND4_MUTATION_RECEIPTS.json))
  - `test_judegomila_r5.py` (4/4 isolated `-I` standalone stdout SHA-256: `90030b5fb53e87e7a66d34099294bd0cabf03c5637f573c4f532f4f1c58e1c46`; `12` test groups PASS)
  - `JUDEGOMILA_ZETA_DBN_AUDIT_REPORT.md` (this report)
- **Exact Standalone Reproduction Commands (from `studies/zeta-dbn-dini-inertia/`):**
  ```bash
  for f in "-I -B" "-I -O -B" "-I -B -W error" "-I -O -B -W error"; do
    PYTHONDONTWRITEBYTECODE=1 python3 $f judegomila_zeta_dbn_tomography.py | sha256sum
    PYTHONDONTWRITEBYTECODE=1 python3 $f hardened_dini_and_r5_mutator.py | sha256sum
    PYTHONDONTWRITEBYTECODE=1 python3 $f test_judegomila_r5.py | sha256sum
  done
  # Fail-closed check when external third-party clones are absent (exits nonzero):
  PYTHONDONTWRITEBYTECODE=1 python3 -I -B judegomila_zeta_dbn_tomography.py --require-live-repos
  ```
- **Falsification Criteria:** This audit fails if (1) any exact rational Polymath 15 identity, `-O` negative-truncation proof, pure-$\mathbb{Q}/\mathbb{Q}[i]$ operator proof, or fail-closed `--require-live-repos` refusal fails independent verification, (2) `hardened_dini_and_r5_mutator.py` drops below `100.0%` (`37/37`) under external `Foundation-0/aletheia v2.0.0 mutate --max-mutants 0` or breaks under `python3 -I -O -B`, (3) when run against the pinned external clones, either clone differs from its pinned commit SHA or any of the `326` Lean 4 finding counts / `10/10` stdlib `dbn-audit` replays fails to reproduce, or (4) `aletheia v2.0.0 audit-check` fails on `studies/zeta-dbn-dini-inertia/`.
