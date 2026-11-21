# Round 4D Arm R4D-1 (`AUDIT-052`): Cross-Repo Lean 4 Forensic Tomography of `tristanbuckmaster/{navier-stokes,fluid_lean}` vs. `openai/NavierStokesAndEuler` & Pure-$\mathbb{Q}$ `SignedTree` Multifrontal Schur-Complement Certifier

> **Audit ID:** `AUDIT-052` (`SF-01 #24` $\cap$ `SF-04` $\cap$ `AUDIT-002`/`015R`/`027`/`041`)  
> **Owner:** `spectral-prover` (Wave 2 — Round 4D, Arm R4D-1)  
> **Oracle Class:** `exact+anchor` (100% pure Python 3 stdlib `int` + `fractions.Fraction`; **ZERO floats** anywhere in code or emitted JSON; **ZERO bare `assert`s**)  
> **Honest Law-4 Novelty Rating:** **`N1`** (commit-pinned empirical 3-repo `8,678`-file Lean 4 / Comparator forensic audit + exact pure-$\mathbb{Q}$ executable verifier & adversarial refutation suite for Alpöge–Buckmaster's multifrontal `Certificate.SignedTree` Schur-complement coercivity engine; all upstream mathematical proofs quarantined as `N0`)  
> **External Governance:** Strictly **READ-ONLY** on all external repositories (`0` external PRs, issues, or comments).

---

## 0. Executive Summary

We perform a commit-pinned, zero-false-positive forensic audit across **8,678 Lean 4 files (3,077,719 lines)** and **11 `comparator*.json` configurations** spanning three landmark fluid-PDE formalization repositories:
1. **`tristanbuckmaster/navier-stokes`** (`ad53419de079eb8f95f60313473374624a348546`, pushed `2026-11-20`, Lean `v4.33.1`, L. Alpöge & T. Buckmaster — conditional formalization of **unforced 3D Navier–Stokes** finite-time blow-up on $\mathbb{R}^3$ and $\mathbb{T}^3$ via a backward discretely self-similar profile with 19-fold azimuthal symmetry).
2. **`tristanbuckmaster/fluid_lean`** (`d0124689230b58b4f86e7b90ac59de06404b3b6b`, pushed `2026-09-08`, Lean `v4.32.2`, Claude / Anthropic under L. Alpöge — three unconditional **forced** blow-up formalizations: `affinecore`, `boussinesq-blowup`, `euler-blowup`).
3. **`openai/NavierStokesAndEuler`** (`f9e8bc5b38b6e212696e8a30e3e91517af887bbd`, pushed `2026-09-10`, Lean `v4.34.0-rc2`, GPT-6 Astra / Codex — unconditional **forced** 3D Navier–Stokes Clay alternatives (C)/(D) and **unforced** 3D Euler blow-up).

**Five Verified Findings:**
1. **Zero Proof-Body Trust Escapes Across All 8,663 Proof Files (`aletheia v1.2.0 --lean-audit`):** Every non-Challenge proof module across all 5 sub-projects (`8,663 / 8,663 = 100.0%`) contains **`0` `sorry`s, `0` custom `axiom`s, `0` `native_decide`, `0` `debug.skipKernelTC`, `0` `implemented_by`/`extern`/`unsafe`/`partial def`**. All `31` `LEAN4_SORRY` findings reside strictly inside the `15` intentional Comparator Challenge specification files. (The `170` `LEAN4_VACUOUS_SIGNATURE_NOTICE` hits in `fluid_lean/euler-blowup` were inspected and confirmed to be benign internal build-guard markers `theorem ..._aux_hbguard : True := trivial`, zero main-theorem vacuity.)
2. **Concrete `CS-10` Comparator Config & External-Kernel Trust Gap on `tristanbuckmaster/navier-stokes` (`0/6` PASS vs. `5/5` PASS on `fluid_lean` & `openai`):**
   - Live `aletheia v1.2.0 --comparator-config` (`validate_comparator_config`) passes `3/3` on `tristanbuckmaster/fluid_lean` (`enable_nanoda: true`) and `2/2` on `openai/NavierStokesAndEuler` (`enable_nanoda: true`), yet **FAILS `6/6` on `tristanbuckmaster/navier-stokes`** because ALL `6/6` `comparator*.json` files set **`"enable_nanoda": false`** (disabling the independent Rust kernel checker `nanoda`, echoing `AUDIT-036`'s `openai/math` finding).
   - **Data & Kernel-Arithmetic Contrast (`0` vs. `22,297` `decide +kernel` calls):** `fluid_lean` closes its forced Boussinesq (`13,547` `decide +kernel`) and Euler (`8,750` `decide +kernel`) interval certificates **100% inside the Lean kernel** (`0` `native_decide`). By contrast, `tristanbuckmaster/navier-stokes` contains **`0` `decide +kernel`** calls, **no numerical certificate data** (cited SHA-256 `3f7a335b84b6c7631742cacc5343dfcd11cf72f5221ff79b2b9268790b4b22c5` not yet released), and relies on external 128-bit Arb/FLINT interval code not present in the repository (`README.md:34–39`).
   - **Unrebuilt 20-Nov-2026 Patch & Coverage Inventory:** `README.md:45–49` discloses that the 20 November 2026 cell-layer patch (`modeWeight` changed from $m^2+\frac14$ to $(|m|+\frac12)^2$, zero cell constant, non-vanishing harmonics) **was not rebuilt** when assembled. Static audit confirms `AdjointRemainderAzimuthalParts.lean:18`, `AdjointRemainderAzimuthal.lean:88–91`, `CellLayerChallenge.lean:3584`, and `StatementDefs.lean` remain textually synchronized, and exact rational algebra proves $(|m|+\frac12)^2 - (m^2+\frac14) \equiv |m| \ge 0$ (strictly relaxing the azimuthal remainder bound for all $m \neq 0$, e.g. by exact factor **`1521/1445`** at Appendix C's $\kappa = 19$ symmetry order). Additionally, `scripts/PrintAxioms.lean` checks `27` theorems while the `6` `comparator*.json` files list `19` (`8` auxiliary/consequence theorems unlisted, matching `lean/NOTICE:13`).
   - **Independent Provenance Check (Pairwise SHA-256 Overlap):** `fluid_lean` shares `32`–`37` vendored `cm24-r2`/`CZCore` files across its three sub-projects; `tristanbuckmaster/*` and `openai/NavierStokesAndEuler` have **`0`** shared `.lean` file hashes.
3. **Exact Pure-$\mathbb{Q}$ Verification of Alpöge–Buckmaster's Multifrontal `Certificate.SignedTree` Coercivity Engine (`CellLayerChallenge.lean:2051–2210`, `SF-01 #24`):**
   We extract the exact finite-dimensional spectral core of `tristanbuckmaster/navier-stokes` — a **multifrontal sparse Schur-complement elimination tree (`SignedTree`)** with weighted-Gershgorin enclosures (`PassesRealNodeEnclosure`), telescoping `NullPair` (`+N, -N`) balancing, positive/negative columns $F_+, F_-$, and root-count guard `|Column| <= |B|` (`PassesPivotCount`) — and implement a zero-float verbatim pure-$\mathbb{Q}$ verifier:
   - Certifies both an **exact zero-slack 3-node multifrontal tree with `NullPair` cancellation** and a **perturbed weighted-Gershgorin interval-enclosure tree** ($E, F \ge 0$, $R_\nu \neq 0$, non-uniform weights $w_j > 0$), proving via exact Bunch–Kaufman inertia (`AUDIT-041`) and Bareiss leading minors (`AUDIT-027`) that $M_{\mathrm{total}} \succeq D_{\mathrm{slack}} - F_- F_-^\top$, global inertia is `(4, 0, 2)` (`n_- = 2 \le |B| = 2`, `n_+ = 4 \ge |A| = 4`), the restriction to $\ker(F_-^\top)$ is strictly PD `(4, 0, 0)` (all `4/4` leading minors $> 0$, `R_opt = R_{H4} = 4`), positive `AUDIT-002 R_opt` holds on $M_{\mathrm{total}}$, and inertia is `0`-residual $O(6, \mathbb{Q})$ Householder invariant.
   - Kills **`6/6` adversarial `SignedTree` mutants** (violating `row_bound`, `slack_le`, `root_front_nonneg`, `column_count > |B|`, `every_variable_pivoted`, and `error_matrix_nonneg`), proving every clause of `PassesRealNodeEnclosure` and `PassesPivotCount` is load-bearing.
4. **Exact 2D Sperner Grid-Simplex Witness for `FixedPointBox.lean:49–61` (`AUDIT-015R` Bridge):** Pure-$\mathbb{Q}$ verification of the discrete Kuhn-triangulation Sperner labeling (`lab x i := x i != 0 ∧ f(pt x) i <= pt x i`) on $[0, 1]^2$ at odd resolution $p = 7$ (`98` Kuhn simplices), certifying exact odd parity (`1` complete simplex) enclosing the unique rational fixed point `(1/2, 1/2)`.
5. **Bidirectional Symbiosis:** Documents concretely how `fluid_lean`'s `decide +kernel` fixed-point rational tables + our `AUDIT-027` Reduced Bareiss PSD / `AUDIT-015R` Bernstein box certifiers provide a direct zero-float blueprint for replacing external Arb/FLINT verification of `SignedTree` enclosures with kernel-decided rational certificates.

---

## 1. Strict Law-4 `N0` Prior-Art Quarantine

All PDE theorems, Lean 4 formalizations, Brouwer/Sperner fixed-point theory, Gershgorin circle / Sylvester inertia / multifrontal LDL$^\top$ theory, and the upstream repositories (`tristanbuckmaster/navier-stokes`, `tristanbuckmaster/fluid_lean`, `openai/NavierStokesAndEuler`) are quarantined as **`N0`**. The honest **`N1`** contribution of `AUDIT-052` is the commit-pinned empirical 3-repo `aletheia v1.2.0` forensic comparison, the verbatim pure-$\mathbb{Q}$ executable `SignedTree` Schur-enclosure & Sperner verifier, and the adversarial mutant refutation suite.

---

## 2. Three-Repo `aletheia v1.2.0` Forensic Comparison (`8,678` Files, `3,077,719` Lines)

| Subproject | Pinned Commit | Toolchain | `.lean` Files | Total Lines | Clean Proof Files | Challenge `sorry`s | Non-`sorry` Trust Escapes | `decide +kernel` | `native_decide` | `aletheia v1.2.0` Comparator Audit |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---|
| `tristanbuckmaster/navier-stokes` (`lean/`) | `ad53419de079` | `v4.33.1` | `2,271` | `618,331` | `2,261 / 2,261` | `24` (`10` files) | `0` | **`0`** | `0` | **`0/6 FAIL`** (`enable_nanoda: false` on all 6!) |
| `tristanbuckmaster/fluid_lean` (`affinecore/`) | `d0124689230b` | `v4.32.2` | `1,181` | `353,285` | `1,180 / 1,180` | `1` (`Challenge.lean`) | `0` | `0` | `0` | **`1/1 PASS`** (`enable_nanoda: true`) |
| `tristanbuckmaster/fluid_lean` (`boussinesq-blowup/`) | `d0124689230b` | `v4.32.2` | `1,453` | `486,170` | `1,452 / 1,452` | `1` (`Challenge.lean`) | `0` | **`13,547`** | `0` | **`1/1 PASS`** (`enable_nanoda: true`) |
| `tristanbuckmaster/fluid_lean` (`euler-blowup/`) | `d0124689230b` | `v4.32.2` | `1,114` | `975,942` | `1,113 / 1,113` | `1` (`Challenge.lean`) | `0` | **`8,750`** | `0` | **`1/1 PASS`** (`enable_nanoda: true`) |
| `openai/NavierStokesAndEuler` | `f9e8bc5b38b6` | `v4.34.0-rc2` | `2,659` | `643,991` | `2,657 / 2,657` | `4` (`2` files) | `0` | `0` | `0` | **`2/2 PASS`** (`enable_nanoda: true`) |
| **Total** | — | — | **`8,678`** | **`3,077,719`** | **`8,663 / 8,663`** | **`31`** (`15` files) | **`0`** | **`22,297`** | **`0`** | **`5/11 PASS`** |

### Key Architectural & Trust-Boundary Contrast
- **Mathematical Scope:** `fluid_lean` proves **forced** 2D Boussinesq & 3D Euler blow-up unconditionally; `openai/NavierStokesAndEuler` proves **forced** 3D Navier–Stokes (Clay alternatives (C)/(D)) and **unforced** 3D Euler unconditionally; `tristanbuckmaster/navier-stokes` proves **unforced** 3D Navier–Stokes (disproving Clay (A)/(B)) **conditionally on `CellSystemCondition`**, whose numerical certificate (`SHA-256: 3f7a335b...`) and 128-bit Arb/FLINT interval checker are external and not yet released.
- **20-Nov-2026 Unrebuilt Patch (`navier-stokes/README.md:45–49`):** `modeWeight k = |k| + 1/2` satisfies $(|m|+\frac12)^2 - (m^2+\frac14) = |m| \ge 0$, relaxing `AzimuthalBounded` by exact factor **`1521/1445`** at $\kappa = 19$. Textually synced across `AdjointRemainderAzimuthalParts.lean:18`, `AdjointRemainderAzimuthal.lean:88–91`, `CellLayerChallenge.lean:3584`, and `StatementDefs.lean`; formal kernel rebuild of the patched tree remains pending.
- **Comparator Coverage (`navier-stokes/lean/NOTICE:13`):** `27` declarations checked in `scripts/PrintAxioms.lean`, `19` covered by the `6` `comparator*.json` files, `8` auxiliary/consequence theorems unlisted.

---

## 3. Multifrontal `SignedTree` Schur-Complement Verifier (`SF-01 #24`)

From `CellLayerChallenge.lean:2089–2210`, each node $\nu$ of `SignedTree A B` satisfies
$$R_\nu := M_\nu - D_{\mathrm{piv}}(\delta_\nu) - F_{+,\nu} F_{+,\nu}^\top + F_{-,\nu} F_{-,\nu}^\top - S_\nu, \qquad w_i \sum_j \frac{|(R_\nu)_{ij}| + E_{ij} + F_{ij}}{w_j} \le r_i,$$
with `slack(ν, j) <= δ_ν(j) - r_j` (`slack > 0`), `front[root] >= 0`, every variable pivoted, and `|Column| <= |B|`. Telescoping all internal fronts and cancelling `NullPair (+N, -N)` pairs proves
$$M_{\mathrm{total}} = \sum_{l \in \mathrm{Leaves}} L_l \;\succeq\; D_{\mathrm{slack}} - F_- F_-^\top \quad \Longrightarrow \quad n_-(M_{\mathrm{total}}) \le |B|, \;\; M_{\mathrm{total}}|_{\ker(F_-^\top)} \succ 0.$$

- **Exact 3-Node Tree (`|A|=4, |B|=2`, `1` `NullPair`, `2` negative columns):** `PassesRealNodeEnclosure` & `PassesPivotCount` PASS; global inertia `(4, 0, 2)`, surplus PSD `(4, 2, 0)`, restricted $\ker(F_-^\top)$ strictly PD `(4, 0, 0)` (all `4/4` leading Bareiss minors $> 0$, `R_opt = R_{H4} = 4`), positive `AUDIT-002 R_opt` on $M_{\mathrm{total}}$, `0`-residual $O(6, \mathbb{Q})$ Householder invariant.
- **Perturbed Weighted-Gershgorin Tree ($E, F \ge 0$, $R_\nu \neq 0$, non-uniform $w > 0$, `max_gershgorin_ratio = 1`):** PASSES all enclosure bounds; global inertia `(4, 0, 2)`, surplus PSD `(6, 0, 0)`, restricted $\ker(F_-^\top)$ strictly PD `(4, 0, 0)`.
- **Adversarial Mutant Suite:** **`6/6` KILLED** (`row_bound`, `slack_le`, `root_front_nonneg`, `column_count > |B|`, `every_variable_pivoted`, `error_matrix_nonneg`), plus `6` additional structural/enclosure mutant tests in `test_r5_buckmaster_fluid_lean.py` and `10/10` R3 type/domain negative controls.

---

## 4. Exact Reproduction Commands (4-Mode Isolated `-I` R4 + `aletheia audit-check`)

```bash
for f in "-I -B" "-I -O -B" "-I -B -W error" "-I -O -B -W error"; do
  python3 $f buckmaster_fluid_lean_audit.py | sha256sum
  python3 $f test_r5_buckmaster_fluid_lean.py 2>/dev/null | sha256sum
done

PYTHONPATH=../../../publish/aletheia python3 -B -W error -m aletheia audit-check . \
  --scripts buckmaster_fluid_lean_audit.py test_r5_buckmaster_fluid_lean.py --json
```
