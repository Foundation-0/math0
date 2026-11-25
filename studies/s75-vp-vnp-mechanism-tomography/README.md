# Formal Trust-Boundary Audit & Mechanism Tomography of `anthropics/formal-math/vp-vnp`

Machine-checkable forensic audit, zero-float executable mechanism tomography, and standalone pure-`Init` Lean 4 companion certificates examining the formalization of algebraic complexity separations (`VP != VNP` over arbitrary fields and border-complexity closure) in [`anthropics/formal-math/vp-vnp`](https://github.com/anthropics/formal-math/tree/11b6c7e3/vp-vnp) (commit `11b6c7e3`, Lean `4.33.1`, Mathlib `0df444a3`, checked via `comparator`/`nanoda`).

> **Epistemic status:** Static trust-boundary scanning, live CI `nanoda` artifact cross-checking, exact rational/integer/finite-field mechanism replay (`7/7` oracles), and standalone pure-`Init` Lean `4.36.0` kernel checking (`15/15` theorems) are machine-verified. Independent human mathematician line-by-line semantic review of upstream `Statement.lean` against `paper.pdf` has **not** been completed; see [Open Epistemic Obligations](#open-epistemic-obligations).

## 1. Trust-Boundary Forensic Audit & Live CI Verification

A full static trust-boundary audit of the `324` Lean files (`72,932` lines) in `anthropics/formal-math/vp-vnp` (`11b6c7e3`) verified:

- **Zero soundness findings across `323/323` non-`Challenge.lean` files (`72,899` lines):** `0` `sorry`/`admit`, `0` custom `axiom` declarations, `0` `native_decide`/`Lean.ofReduceBool`/`Lean.trustCompiler`, `0` `unsafe`/`@[implemented_by]`/`@[extern]`/`@[csimp]`, `0` environment-mutation/metaprogramming bypasses, and `0` non-standard imports.
- **`Challenge.lean` isolation:** `Challenge.lean` (`33` lines) contains solely the `5` expected `comparator` target theorem `sorry` stubs.
- **Live CI `nanoda` corroboration:** Cross-checked against GitHub Actions CI `nanoda` verification run `#45272623486`, confirming `1,012/1,012` token parity on target statements and `87/87` Appendix Q Table 3 symbols.

Full forensic tables and per-mechanism breakdowns are documented in [VP_VNP_MECHANISM_REPORT.md](VP_VNP_MECHANISM_REPORT.md).

## 2. Executable Pure-Exact Mechanism Tomography (`7` Oracles, `0` Floats)

All `7` core algebraic mechanisms are re-implemented from scratch using pure exact arithmetic over $\mathbb{Z}$, $\mathbb{Q}$, and $\mathbb{F}_p$ (zero IEEE-754 floating-point arithmetic, pure Python stdlib) in [s75_vp_vnp_mechanism_probe.py](s75_vp_vnp_mechanism_probe.py), independently audited and replayed by [verify_s75_vp_vnp.py](verify_s75_vp_vnp.py), and sealed in [s75_vp_vnp_certificate.json](s75_vp_vnp_certificate.json) (`payload_sha256 = 8391bbc2bad5063761ba9eaede41c236a8ce048c70ebb6524bc854d776cb3979`).

| # | Mechanism & Upstream Reference | Key Exact Witnesses |
|---|---|---|
| 1 | **Meixner Crossing-Wire Identity** (App. B, Prop. B.2) | `36/36` reciprocal checks (`y^n B(r,n)(1/y) = C(r,n)(y)`), `216/216` truncated orthogonality identities, `16/16` reflection checks; 4-party $4\times 4$ $\mathbb{Z}[X]$ determinant $\Psi(X)$ with $\deg \Psi = 16$, $\theta = 16$, rank profile peaking at `4`. |
| 2 | **CAT(0) Rank-Metric Dichotomy & `Remark D.3` Tightening** (App. C–D, Thm. C.1, Thm. D.2, Remark D.3) | `64/64` cube pairs verified, tree CN-gap `2`, exact rank histograms on $\mathrm{Mat}_2(\mathbb{F}_2)$ (`[1, 9, 6]`) and $\mathrm{Mat}_3(\mathbb{F}_2)$ (`[1, 49, 294, 168]`); **independent tightening of Remark D.3 down to $\mu = 2$** (see below). |
| 3 | **Flat-Case Permanent Gadget & Hub Balanced Cuts** (App. E, Prop. E.1, Prop. E.10, Thm. E.11) | $9\times 9$ exact permanent `31075` over $\mathbb{Q}$ (`1` mod $3$, `0` mod $5$) vs. char-$2$ cleared collapse (`0` vs. true `1`); `334/334` balanced cuts with $\min(81\|x\|_2^2 / k^3) = 21/4 \ge 4$; `5/5` cubic-to-quartic scaling checks yielding the $m^{c(\log_2 m)^{1/3}}$ exponent. |
| 4 | **Characteristic-2 `perm` vs. `HC` Separation** (App. M, Prop. M.2) | Over $\mathbb{F}_2$, $\det = \mathrm{perm} = 0 \ne 1 = \mathrm{HC}$ in $3\times 3$ and $4\times 4$; `39`-vertex division-free XOR-gadget exact $\mathrm{HC} = 27$ over $\mathbb{Z}$ (`1` mod $2$, `0` mod $3$, `2` mod $5$); Pólya $3\times 3$ obstruction (`0/512` valid sign maps). |
| 5 | **Contracting Unitriangular Words & $\mathrm{SL}_3$ Tower** (App. F & H, Lem. F.2) | `44/44` endpoint-1 and `95/95` general rank-1 blocks in $U_4(\mathbb{F}_2)/U_5(\mathbb{F}_2)$ with tight generator multiplicities `4` and `16`; `54/54` commutator identities in $\mathrm{SL}_3(\mathbb{F}_2[s]/(s^3))$. |
| 6 | **Low-Degree Parse Trees, Boolean Barrier & Diagonalization** (Sec. 2.5, App. K, Lem. K.2, Thm. K.6) | Verified over $\mathbb{Z}, \mathbb{F}_2, \mathbb{F}_3, \mathbb{F}_5$ (output degree `5`); explicit `8/8`-point Boolean-zero garbage $(x_1^2 + x_1)x_2 x_3$ obliterating the formal degree-3 homogeneous part (`1` vs. `0` terms); finite-field squaring periods (`F_3: 1`, `F_5: 1`, `F_7: 2`). |
| 7 | **Border-Complexity Laurent Closure & Isolation** (App. N, Lem. N.2, Lem. N.3, Prop. N.4) | Laurent cutoff $N = 2^L\Delta = 16$ verified over $\mathbb{Z}$ and $\mathbb{F}_2$; covering inequality at $n = 32$ (`276,922,881 < 4,294,967,296`); $\sigma_3$ isolation preserving exact $\varepsilon^0$ coefficient (`7` after $\sigma_3$, `17` via mod-$2^4$ extraction). |

### Independent Tightening of Remark D.3 ($\mu = 2$, $\det(G) = -1/4$)

Upstream Remark D.3 establishes that the rank metric $d(A, B) = \sqrt{\mathrm{rk}(A - B)}$ on $\mathrm{Mat}_\mu(\mathbb{F}_2)$ is non-Euclidean for sufficiently large $\mu$. Oracle 2 and theorem `remark_D3_rank_metric_non_euclidean` tighten this to the sharp minimal dimension **$\mu = 2$** (and by upper-left block embedding, every $\mu \ge 2$):

- **5-point subset:** $\{0, E_{00}, E_{01}, E_{11}, E_{00} + E_{11}\} \subset \mathrm{Mat}_2(\mathbb{F}_2)$.
- **Exact Gram obstruction:** For $G_{ij} = \tfrac{1}{2}\bigl(\mathrm{rk}(A_i) + \mathrm{rk}(A_j) - \mathrm{rk}(A_i - A_j)\bigr)$ on the four nonzero points,
  $$\det(G) = -\frac{1}{4} < 0, \qquad u^T G u = -1 < 0 \quad\text{at } u = (2, -1, 2, -2)^T.$$

## 3. Standalone Pure-`Init` Lean 4 Companion (`15/15` Theorems)

[VpVnpMechanismCerts.lean](VpVnpMechanismCerts.lean) compiles directly under Lean `4.36.0` with **zero external imports** (pure `Init`, zero Mathlib, zero warnings, zero `sorryAx`, standard axioms only):

- **Meixner identity:** `meixner_reciprocal_verified_5x5`, `meixner_orthogonality_verified_R5`
- **Remark D.3 ($\mu \ge 2$):** `remark_D3_rank_metric_non_euclidean`
- **Prop. E.1 & char-2 separation:** `prop_E1_squarefree_factor2`, `prop_E1_char2_collapse`, `char2_hc3_separates_from_perm3_and_det3`, `char0_perm3_separates_from_det3`
- **Flat-case cuts & exponent:** `prop_E10_balanced_cut_bound`, `thm_E11_exponent_scaling`
- **Unitriangular factorization:** `lem_F2_U4_rank1_word`
- **Boolean barrier & Laurent cutoff & diagonalization:** `sec25_boolean_garbage_vanishes_on_bits`, `sec25_boolean_garbage_corrupts_formal_deg3`, `lem_N2_cutoff_preserves_nonpositive_exponents`, `thm_K6_diagonalization_int`, `thm_K6_diagonalization_mod`

## 4. Open Epistemic Obligations

1. **Human statement review pending:** Machine compilation and `nanoda` checking confirm proof soundness relative to `Statement.lean`, not semantic equivalence between `Statement.lean` and the prose statements in `paper.pdf`.
2. **Non-constructive / non-effective bounds:** Upstream Theorem D.2 relies on a non-constructive dichotomy with a non-effective threshold $m_0(p)$.
3. **Lean-only program-correctness lemmas:** Four upstream results (`Prop. I.1`, `Thm. H.2(d,e)`, `Thm. J.3`, `Prop. N.4`) are verified in Lean without full standalone prose proofs in `paper.pdf`.
4. **External / unformalized corollaries:** Upstream `Remark N.6` (Mulmuley–Sohoni border determinantal corollary) and external Strassen division elimination sit outside the core `comparator` targets.

## 5. Files & Reproducible Verification

| File | Role |
|---|---|
| [README.md](README.md) | Study overview, key findings, epistemic boundaries, and verification commands. |
| [VP_VNP_MECHANISM_REPORT.md](VP_VNP_MECHANISM_REPORT.md) | Complete forensic audit and 7-mechanism tomography report. |
| [s75_vp_vnp_mechanism_probe.py](s75_vp_vnp_mechanism_probe.py) | Pure-stdlib, zero-float exact algebraic probe implementing Oracles 1–7. |
| [verify_s75_vp_vnp.py](verify_s75_vp_vnp.py) | Independent verifier, strict canonical JSON checker, and live Lean 4 runner/axiom auditor. |
| [s75_vp_vnp_certificate.json](s75_vp_vnp_certificate.json) | Canonical SHA-256-sealed JSON witness certificate (`payload_sha256 = 8391bbc2...`). |
| [VpVnpMechanismCerts.lean](VpVnpMechanismCerts.lean) | Standalone pure-`Init` Lean 4 companion (`15` kernel-checked theorems). |
| [test_s75_vp_vnp_r5.py](test_s75_vp_vnp_r5.py) | Comprehensive fail-closed regression and adversarial test suite (`13` test groups). |

Run from `studies/s75-vp-vnp-mechanism-tomography/` (Python 3.10+, zero third-party packages; Lean `4.36.0` on `PATH` for `--verify-lean`):

```bash
python3 -I -B verify_s75_vp_vnp.py --check s75_vp_vnp_certificate.json --json
python3 -I -B verify_s75_vp_vnp.py --verify-lean VpVnpMechanismCerts.lean --json
python3 -I -B test_s75_vp_vnp_r5.py
python3 -I -O -B test_s75_vp_vnp_r5.py
python3 -I -B -W error test_s75_vp_vnp_r5.py
```
