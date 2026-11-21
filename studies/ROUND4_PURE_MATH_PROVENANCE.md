# Provenance and Status: Round-4 Pure-Mathematics Studies (`AUDIT-049`–`AUDIT-053R`)

**Status: independently verified by clean-room zero-shared-code checkers (`N1`, `0` unresolved defects); submitted via Draft PR, pending `math0` maintainer review.**

This drop packages five self-contained, zero-dependency Python 3 standard-library (`int`, `fractions.Fraction`, `decimal.Decimal`) mathematical studies produced during Foundation-0's Wave 2 Round 4B/4C/4D research cycle. Every study emits **zero floating-point numbers in its JSON certificates**, contains **zero bare `assert`s**, runs bit-identically across all four isolated interpreter modes (`-I -B`, `-I -O -B`, `-I -B -W error`, `-I -O -B -W error`), and passes `aletheia v1.2.0 audit-check`.

No external third-party repositories or PDFs are vendored here. The three studies that also conducted read-only external Lean 4 / C / TypeScript forensics (`AUDIT-049`, `AUDIT-050`, `AUDIT-052`) run **100% of their exact pure-$\mathbb{Q}/\mathbb{Q}[i]$ mathematics and R5 verification suites live in standalone mode**, while transparently referencing their sealed certificates/reports for the external-repository forensic records.

---

## Studies Included

| Directory | Audit ID & Status | Oracle Class & Novelty | Exact Core Mathematics & Verification Scope | Report |
|---|---|---|---|---|
| [`aletheia-operator-calculus/`](aletheia-operator-calculus/) | `AUDIT-051` (`VERIFIED`, `68/68` `100%` R5 killed) | `exact`, **`N1`** | Canonical 8-glyph executable Unicode `Sm` operator calculus (`⧄ ⧅ ⦷ ⟠ ⧇ ⦺ ⩩ ⫩`; `0 / 227,540` Lean 4 collisions) with Unicode + ASCII parser, `13` 1-line compressed exact theorems, and `6` commutator probes (`C1` `[⧄_D, ⦷_χ]` Nonlinear Loewner Screening Positivity even on Krein-indefinite screens; `C2` singular Schur associator breakdown; `C3` `[⧄_B, ⟠_G]` Matrix-Jensen; `C4` Rank-2 Woodbury `[⦷_χ, ⧇]`; `C5` exact vs. float64 refusal; `C6` Unconditional Linear Monopole Subadditivity & Rational Metric on $H^1(G, B; \mathbb{Z}_2)$). | [ALETHEIA_OPERATOR_CALCULUS.md](aletheia-operator-calculus/ALETHEIA_OPERATOR_CALCULUS.md), [GLYPH_REGISTRY.md](aletheia-operator-calculus/GLYPH_REGISTRY.md) |
| [`euler-3d-craik-criminale-polytope/`](euler-3d-craik-criminale-polytope/) | `AUDIT-053R` (`VERIFIED`, `17/17` `100%` R5 killed) | `exact+anchor`, **`N1`** | Independent pure-$\mathbb{Q}$ algebraic & Farkas-polytope audit of Alpöge–Buckmaster–Coiculescu's 3D Euler singularity preprint (`tristanbuckmaster-cc.pdf`, `0` false alarms): `10/10` 1-step inequalities (`3` exact active facets) + `3` constructive Farkas dual obstructions ($\beta_h > 0$ mandatory, sharp headroom $\eta_D < 1/3$, transverse trick `(5.16)` mandatory at $\alpha_a = 3/4$); `13/13` Appendix C inequalities & pure-integer Lemma 1.3 tower; $4\times 4$ saddle-point Leray pressure projection $I - k k^\top/\|k\|^2$ as exact Schur complement (`SF-01 #23`); Sections 2–6 Craik–Criminale ODEs & Arnold–Brenier `(4.7)`. | [BUCKMASTER_EULER_CC_AUDIT_REPORT.md](euler-3d-craik-criminale-polytope/BUCKMASTER_EULER_CC_AUDIT_REPORT.md) |
| [`fluid-pde-lean-signed-tree/`](fluid-pde-lean-signed-tree/) | `AUDIT-052` (`VERIFIED`, `6/6` `SignedTree` mutants + `10/10` R3 controls) | `exact+anchor`, **`N1`** | Pure-$\mathbb{Q}$ `SignedTree` multifrontal Schur-complement verifier (`SF-01 #24`: exact + Gershgorin-perturbed telescoping coercivity, global inertia `(4,0,2)` vs. `(4,0,0)` on $\ker(F_-^\top)$, $O(6,\mathbb{Q})$ invariance), Nov 20 weight shift `1521/1445` at $\kappa=19$, and exact 2D Kuhn triangulation Sperner parity `1`; paired with sealed `8,678`-file (`3,077,719`-line) `aletheia v1.2.0` Lean 4 forensics record across `tristanbuckmaster/{navier-stokes,fluid_lean}` and `openai/NavierStokesAndEuler`. | [REPORT_R4D_1_BUCKMASTER_FLUID_LEAN.md](fluid-pde-lean-signed-tree/REPORT_R4D_1_BUCKMASTER_FLUID_LEAN.md) |
| [`zeta-dbn-dini-inertia/`](zeta-dbn-dini-inertia/) | `AUDIT-049` (`VERIFIED`, `37/37` `100%` R5 killed) | `exact+anchor`, **`N1`** | Exact rational Polymath 15 Theorem 1.2 re-verification ($\Lambda \le 893927/5000000 = 0.1787854$, exact PT/barrier/Prop 4.10/Dini slacks), hardened `-O`-immune Dini y-transfer log auditor & truncation formatters (`J-01`/`J-02` reference closure), pure-$\mathbb{Q}$ Bunch–Kaufman Sylvester–Schur inertia (`frozen-rung/Inertia.lean`), pure-$\mathbb{Q}[i]$ singular Schur 4-axiom Moore–Penrose proof (`check_frame_geometry.py`), and exact degree-4 backward-heat PDE witness (`flow_blindness/Main.lean`); paired with `326`-file Lean 4 census & `aletheia/cli.py:94` CLI overwrite defect report. | [JUDEGOMILA_ZETA_DBN_AUDIT_REPORT.md](zeta-dbn-dini-inertia/JUDEGOMILA_ZETA_DBN_AUDIT_REPORT.md) |
| [`canculus-schur-pgl2-cuts/`](canculus-schur-pgl2-cuts/) | `AUDIT-050` (`VERIFIED`, `33/33` `100%` R5 killed) | `exact+anchor`, **`N1`** | Hardened exact normal-form adaptation closure & De Morgan involution $\operatorname{Tr}(\operatorname{Tr}(M)) = M$ (`Eq. 5.6` minimal cuts, `Prop. 7.8` non-upward-closedness), exact $2\times 2$ Schur complement (`SF-01 #22`, $S = 1 + \alpha g h$, $\alpha_{\mathrm{crit}} = 7/27$) $\cap$ 1D $PGL(2, \mathbb{Q})$ cross-ratio invariance (`3/2`), exact tropical $(\min, \max, +)$ Bellman–Ford timed closure, and epistemic-graph governance gates (closing `CANC-B1..B4` against `judegomila/canculus` & `OnCo`). | [JUDEGOMILA_CANCULUS_ONCO_REPORT.md](canculus-schur-pgl2-cuts/JUDEGOMILA_CANCULUS_ONCO_REPORT.md) |

---

## Standalone Verification Commands & 4-Mode Isolated `-I` R4 Digests

All commands below were run directly from `studies/` under all four isolated interpreter modes (`-I -B`, `-I -O -B`, `-I -B -W error`, `-I -O -B -W error`) with `PYTHONDONTWRITEBYTECODE=1`, exiting with code `0` and producing bit-identical stdout across all four modes:

| Study | Command (from `studies/`) | 4/4 Isolated `-I` Stdout SHA-256 |
|---|---|---|
| `aletheia-operator-calculus` | `python3 -I -B aletheia-operator-calculus/aletheia_calculus.py --json` | `69ee26ceb845f0493f1a01a09eee9c212a118af5f4286a134a36ab3152c908a4` |
| `aletheia-operator-calculus` | `python3 -I -B aletheia-operator-calculus/test_aletheia_calculus_r5.py` | `8be9f7ca1f142b16c6a65b79d973bf1d092d529ed4ea59a018858733cfe8b9ca` |
| `euler-3d-craik-criminale-polytope` | `python3 -I -B euler-3d-craik-criminale-polytope/buckmaster_euler_cc_audit.py --json` | `10a0a751d255131e7f878078c97b0b3a1e0f5f151c9174ebfbf6ad953e251626` |
| `euler-3d-craik-criminale-polytope` | `python3 -I -B euler-3d-craik-criminale-polytope/test_buckmaster_euler_cc_r5.py` | `ed6f3a899d8f6c5eb3cd64fd30ee5a9ac680303a6952cff9cebbaacab091bf1d` |
| `fluid-pde-lean-signed-tree` | `python3 -I -B fluid-pde-lean-signed-tree/buckmaster_fluid_lean_audit.py` | `0caa31366f36065be03b1adddd7755571bc14dbb998a8bd90d152fc55800a9a3` |
| `fluid-pde-lean-signed-tree` | `python3 -I -B fluid-pde-lean-signed-tree/test_r5_buckmaster_fluid_lean.py` | `9f3cb0fe3353b04c26d275cd8613ade6f51296584ad4e0727330888a664fb067` |
| `zeta-dbn-dini-inertia` | `python3 -I -B zeta-dbn-dini-inertia/judegomila_zeta_dbn_tomography.py` | `a7f8ea5ccc5f92eb3529cd097a1054391ab84c798228e85f79207c2cf485e116` |
| `zeta-dbn-dini-inertia` | `python3 -I -B zeta-dbn-dini-inertia/hardened_dini_and_r5_mutator.py` | `e907524d267a0b04e69ea9f2e516e8d65acdda9bae276c9c8a63523498c39390` |
| `zeta-dbn-dini-inertia` | `python3 -I -B zeta-dbn-dini-inertia/test_judegomila_r5.py` | `90030b5fb53e87e7a66d34099294bd0cabf03c5637f573c4f532f4f1c58e1c46` |
| `canculus-schur-pgl2-cuts` | `python3 -I -B canculus-schur-pgl2-cuts/canculus_onco_bridge.py --json` | `2574213dfcb656bc9f16d3086736d9ab1cdb8f3c763dcc2d3d70a478924b1c9b` |
| `canculus-schur-pgl2-cuts` | `python3 -I -B canculus-schur-pgl2-cuts/test_canculus_onco_r5.py` | `329ec34c362e3872dbbe807498f6a05ba41bcb6c24bc156e88f9435c159cff9b` |

---

## Strict Law-4 Prior-Art Attribution (`N0` vs. `N1`)

Each study report contains a complete `N0` prior-art quarantine table crediting all classical and upstream authors (Sylvester, Schur, Haynsworth, Farkas, Sperner, Kuhn, Polymath 15 / Rodgers–Tao, Platt–Trudgian, Craik–Criminale, Arnold–Brenier, Alpöge–Buckmaster–Coiculescu, `judegomila`, `tristanbuckmaster`, `openai/NavierStokesAndEuler`). None of those classical or upstream results are claimed as new here; all five studies are honestly classified **`N1`** (exact clean-room verification engines, constructive duals, executable operator calculus, and zero-float hardening).
