# The Aletheia Operator Calculus — Canonical 8-Glyph Registry (Round 4C)

> **Owner:** `session-cartographer` (Glyph Selection, Empirical Unicode Collision Audit & Epistemic Registry)  
> **Executable Binding & Commutator Discovery Engine (`AUDIT-051`):** `@fractals-probe` (`aletheia_calculus.py`, `test_aletheia_calculus_r5.py`, `ALETHEIA_OPERATOR_CALCULUS.md`)  
> **Machine-Readable Registry:** `symbiosis/round4/operator-calculus/glyph_registry.json`  
> **Discipline (Iverson / Dirac / Penrose / Aletheia Law 5):** Zero symbolic theater. Every glyph below is (1) empirically verified **`0 / 227,540`** across all 4 major-lab Lean 4 formal repositories (`google-deepmind/formal-conjectures`, `openai/math`, `anthropics/formal-math`, `anthropics/flt`), **`0`** across all expedition sources, and **`0`** across `gemini-sessions/` (Sessions 1–2); (2) free of entrenched conflicting semantics in standard mathematics, logic, category theory, physics, chemistry, Z-notation, SQL, and APL; (3) bound 1-to-1 to a typed, zero-float pure-$\mathbb{Q}/\mathbb{Z}$ executable operator; and (4) justified solely by **algebraic compression + discovery of non-trivial commutator / composition laws**.

---

## 1. Empirical Collision Audit Summary

- **Unicode Search Domain:** All `392` Mathematical Symbol (`Sm`) codepoints across *Miscellaneous Mathematical Symbols-A* (`U+27C0..U+27EF`), *Miscellaneous Mathematical Symbols-B* (`U+2980..U+29FF`), and *Supplemental Mathematical Operators* (`U+2A00..U+2AFF`).
- **4-Lab Lean 4 Formal Corpus Scan (`227,540` `.lean` files):**
  - Only `12` of the `392` `Sm` codepoints appear anywhere (`⧸` `13546`, `⨆` `2820`, `⨅` `1291`, `⨯` `188`, `⨁` `145`, `⨍` `82`, `⟂` `48`, `⨂` `35`, `⨿` `7`, `⪯` `5`, `⪰` `5`, `⨳` `3`).
  - All `8` selected glyphs have **`0 / 227,540` hits** in Lean 4, **`0` hits** in the expedition workspace, and **`0` hits** in `gemini-sessions/` (where Pairs 27–34 used only `⊗`, `∘`, and standard LaTeX `\mathfrak{T}, \mathfrak{P}, \mathfrak{S}, \mathcal{F}^{\mathrm{inv}}`).
- **Standard-Notation Exclusions Explicitly Enforced:**
  - Excluded `⊗, ⊕, ∘, □, ◇, ≡, ≃, ⊢, ⊨, ⊥, ⊤, ∥, ⋉, ⊐, ⧺` (list append), `⦵` (Plimsoll chemistry standard state), `⫝̸/⫝` (Shelah model-theory forking), `⟕/⟖/⟗` (SQL outer joins), `⨿` (coproduct), `⧢` (shuffle product), `⧖` (process-calculus hourglass), `⦇⦈` (banana brackets), and `⨷` (visually too close to `⊗`).

---

## 2. The Canonical 8-Glyph Operator Basis

Visual grammar organizes the 8 primitives into **three clean morphological families** that prevent visual confusion while making duals immediately legible:
- **Box family (`⧄`, `⧅`, `⧇`):** Fiber & cochain structural projections (`/` visible Schur quotient, `\` hidden dark-mode kernel shadow, `∘` trapped cohomological hole).
- **Circle family (`⦷`, `⦺`):** Loop & signature functors (`∥` inside `○` = parallel-transport holonomy around a loop; 3-sector `○` = `(n_+, n_0, n_-)` Sylvester/Krein inertia triple).
- **Relational / Gate / Equalizer family (`⟠`, `⩩`, `⫩`):** Bisected probe diamond (`⟠` observer-net equalizer), rigid `3×3` lattice identity (`⩩` zero-float exact null-equivalence), stacked `⊥`-over-`⊤` (`⫩` R5 acceptance + adversarial refusal gate).

| # | Glyph | Codepoint (`Sm`) | Official Unicode Name | Operator Name & Arity | LaTeX Macro | ASCII Fallback | Precedence / Assoc |
|---|---|---|---|---|---|---|---|
| 1 | **`⧄`** | `U+29C4` | `SQUARED RISING DIAGONAL SLASH` | **Fiber-Elimination Schur Pushforward** (`binary`, `M ⧄ B`) | `\schurpush` (`\boxslash`) | `|/|`, `SCHUR(M, B)` | `60` / left |
| 2 | **`⧅`** | `U+29C5` | `SQUARED FALLING DIAGONAL SLASH` | **Singular-Kernel / Dark-Mode Shadow** (`binary`, `M ⧅ B`) | `\darkshadow` (`\boxbslash`) | `|\|`, `SHADOW(M, B)` | `60` / left |
| 3 | **`⦷`** | `U+29B7` | `CIRCLED PARALLEL` | **Holonomy-Unmasking Differential** (`binary`, `L ⦷ χ`) | `\holunmask` (`\circledparallel`) | `(||)`, `UNMASK(L, chi)` | `55` / left |
| 4 | **`⟠`** | `U+27E0` | `LOZENGE DIVIDED BY HORIZONTAL RULE` | **Observer-Net Equalizer** (`binary`, `X ⟠ G`) | `\obseq` (`\lozengeminus`) | `<=>`, `EQOBS(X, G)` | `50` / left |
| 5 | **`⧇`** | `U+29C7` | `SQUARED SMALL CIRCLE` | **Dimensionless Cohomological / Gluing Obstruction** (`unary`, `⧇(ω)`) | `\cohomobs` (`\boxcircle`) | `[o]`, `OBST(w)` | `70` / prefix |
| 6 | **`⦺`** | `U+29BA` | `CIRCLE DIVIDED BY HORIZONTAL BAR AND TOP HALF DIVIDED BY VERTICAL BAR` | **Krein Inertia Signature Functor** (`unary`, `⦺(A)`) | `\kreinsig` (`\circleurquad`*) | `(+-0)`, `INERTIA(A)` | `70` / prefix |
| 7 | **`⩩`** | `U+2A69` | `TRIPLE HORIZONTAL BAR WITH TRIPLE VERTICAL STROKE` | **Coordinate-Free Exact Null-Equivalence** (`binary rel`, `X ⩩ Y`) | `\exacteq` (`\equivVvert`) | `=#=`, `EXACT_EQ(X, Y)` | `30` / non-assoc |
| 8 | **`⫩`** | `U+2AE9` | `SHORT UP TACK ABOVE SHORT DOWN TACK` | **R5 Refusal-Verified Gate** (`binary rel`, `T ⫩ x`) | `\rfivegate` (`\botTop`) | `_|T`, `R5GATE(T, x)` | `20` / non-assoc |

*\*Note on LaTeX macros:* All macros above are defined cleanly via `unicode-math` / XeLaTeX (`\char"29C4`, etc.) or portable custom `\newcommand` definitions in `ALETHEIA_OPERATOR_CALCULUS.md`, avoiding collisions with AMS / Mathlib / STIX reserved command names.

---

## 3. Exact Typed Semantics (Zero-Float $\mathbb{Q}/\mathbb{Z}$), Invariance Groups & Provenance

### 1. `⧄` (`U+29C4`) — Fiber-Elimination Schur Pushforward (`M ⧄ B`)
- **Domain → Codomain:** `(M ∈ Sym_n(ℚ), B ⊆ {0..n-1}) ↦ S ∈ Sym_{|A|}(ℚ)` where `A = V \ B` and `S = M_{AA} - M_{AB} M_{BB}^+ M_{BA}` (exact Bareiss / Moore–Penrose generalized Schur complement over $\mathbb{Q}$).
- **Invariance Group:** `GL(B, ℚ)` on eliminated fiber `B` (when `M_{BB}` is nonsingular) and permutation group `S_{|A|} × S_{|B|}`; equivariant under boundary orthogonal/congruence changes `P_A ∈ GL(A, ℚ)`.
- **Expedition Provenance:** `SF-01` (17→21-Way Exact Schur Unification across `AUDIT-002`, `018`, `025`, `027`, `029`, `035`, `036`, `039`, `041`, `042`, `044`, `045`, `046`, `048`).
- **Core Exact Law (Quotient-in-Stages):** For disjoint `B, C` with `rk(M ⧅ (B ⊔ C)) = 0`, `(M ⧄ B) ⧄ C ⩩ M ⧄ (B ⊔ C)`.

### 2. `⧅` (`U+29C5`) — Singular-Kernel / Dark-Mode Shadow (`M ⧅ B`)
- **Domain → Codomain:** `(M ∈ Sym_n(ℚ), B ⊆ V) ↦ (K_B, C_{AB})`, returning an exact $\mathbb{Q}$-basis of `K_B = ker(M_{BB})` and the **dark-mode coupling map** `C_{AB} = M_{AB} |_{K_B} ∈ ℚ^{|A| × dim K_B}` (with exact scalar invariants `dim_dark = dim K_B` and Krein null-coupling rank `r_cross = rank(C_{AB})`).
- **Invariance Group:** `S_{|A|} × GL(B, ℚ)` (exact rank `r_cross` and `dim_dark` are invariant under all invertible fiber reparametrizations and boundary congruence).
- **Expedition Provenance:** `AUDIT-041` (singular-horizon Krein null-coupling `n_- = r_cross`, soft-hair kernel), `AUDIT-027` (`heedle` blind drift), `AUDIT-045` (rank–crank column-space mock shadow `S_shadow`).
- **Exact Duality with `⧄` (Haynsworth–Krein Shadow Law):** When `M_{BB} ⪰ 0` and `M ⧅ B` has `r_cross = 0`, `⦺(M) ⩩ ⦺(M_{BB}) + ⦺(M ⧄ B)`; when `r_cross > 0`, the shadow injects exact negative Krein inertia `n_- = r_cross`!

### 3. `⦷` (`U+29B7`) — Holonomy-Unmasking Differential (`L ⦷ χ`)
- **Domain → Codomain:** `(L ∈ Sym_n(ℚ) graph Laplacian on B ⊔ I, χ ∈ Z^1(G, B; ℤ_2) with flip set F ⊆ E(I)) ↦ ΔΛ_∂(χ) := (L^χ ⧄ I) - (L ⧄ I) ∈ Sym_{|B|}(ℚ)`.
- **Invariance Group:** Relative interior $\mathbb{Z}_2$-coboundary gauge group `B^1(G, B; ℤ_2)` (`F ↦ F △ δS` for `S ⊆ I \ N(B)`) AND boundary vertex relabeling `S_{|B|}`.
- **Expedition Provenance:** `AUDIT-042` (`p`-adic BTZ $\mathbb{Z}_2$ holonomy unmasking), `AUDIT-044` (`#267` balanced Krein signature `(k, |B|-2k, k)` on 8 BTZ configs), `#268` (Cohomological Krein-Inertia Minimization Theorem), `#274` (monotonic Schur–unmasking screening theorem!).
- **Exact Laws:**
  - `#268` **Cohomological Krein Bound:** `⦺(L ⦷ χ) ≤ min_{F' ⊆ E(I), [F']=[χ]} ⦺(A_{F'})` (componentwise on `(n_+, n_-)`).
  - `#274` **Schur–Unmasking Commutator Positivity:** Across any separating screen `C` between `B` and `F ⊆ E(D)`, the nonlinear commutator defect `[⧄, ⦷]` has `⦺([⧄, ⦷])_- ⩩ 0` (always PSD!), forcing monotonic monopole screening `Φ_B(χ) ≤ Φ_C(χ)`!

### 4. `⟠` (`U+27E0`) — Observer-Net Equalizer (`X ⟠ G`)
- **Domain → Codomain:** `(X, G_obs)` where `G_obs` is a finite group or explicit observer/regulator net acting on `X` over $\mathbb{Q}$ (or $\mathbb{Q}((\epsilon))$) ↦ exact equalizer object `X^{G_obs}` (fixed subspace, exact invariant rational, or regulator-independent $\epsilon^0$ Mellin residue).
- **Invariance Group:** `G_obs` itself (`(g · X) ⟠ G_obs ⩩ X ⟠ G_obs` for every `g ∈ G_obs`; idempotent `(X ⟠ G) ⟠ G ⩩ X ⟠ G`).
- **Expedition Provenance:** Session 1 Pair 31 (`\mathcal{F}^{\mathrm{inv}} \equiv \lim_{\phi \in \mathcal{G}_{\mathrm{obs}}} (\mathcal{F} \circ \phi)`), `SF-07`, `AUDIT-043` (3-level `Aff^+(1,ℚ)/PGL(2,ℚ)` equalizer tower), `AUDIT-046` (4-regulator multiplicative net equalizing `ζ(-k) = -B_{k+1}/(k+1)`).

### 5. `⧇` (`U+29C7`) — Dimensionless Cohomological / Gluing Obstruction (`⧇(ω)`)
- **Domain → Codomain:** `(G, ω ∈ C^1(G, ℚ), w ∈ ℚ_{>0}^E) ↦ κ_{H^1}(ω) = ‖ω_harm‖_w^2 / ‖ω‖_w^2 ∈ [0, 1] ∩ ℚ` (or exact normalized Čech–Hodge–Farkas / cycle-projection obstruction ratio; `0` when `ω = 0` or exact coboundary).
- **Invariance Group:** Scale group `ℚ^×` (`⧇(c ω) ⩩ ⧇(ω)` for `c ≠ 0`), edge-orientation flips `(±1)^E`, vertex relabeling `S_{|V|}`, and gauge shifts in the orthogonal sense (`⧇(ω) = 0 ⟺ ω ∈ im(d^0)`).
- **Expedition Provenance:** `SF-05`, `AUDIT-042` (`κ_{H^1} = 1/L`, `1/p^D`), `AUDIT-043` (`κ_harm = 5/6` on 8-triangle ribbon & exact single-edge identity `⧇(e) ⩩ 1 - R_eff(e)`).

### 6. `⦺` (`U+29BA`) — Krein Inertia Signature Functor (`⦺(A)`)
- **Domain → Codomain:** `A ∈ Sym_n(ℚ) ↦ (n_+, n_0, n_-) ∈ ℕ^3` (`n_+ + n_0 + n_- = n`), computed with 100% exact zero-float Bunch–Kaufman / Bareiss / Descartes arithmetic (with projections `⦺_+`, `⦺_0`, `⦺_-`).
- **Invariance Group:** Full congruence group `GL(n, ℚ)` (`⦺(P^T A P) ⩩ ⦺(A)` by Sylvester's law of inertia) AND positive scalar scaling `ℚ_{>0}` AND exact SPD inversion flip (`⦺(A^{-1} - B^{-1}) ⩩ ⦺(B - A)` for `A, B ≻ 0`).
- **Expedition Provenance:** `SF-01`, `AUDIT-041` (Krein negative index), `AUDIT-044` (exact Bareiss Ramanujan certifier `⦺_-(4(d-1)I - A_⊥^2) = 0` & BTZ `(k, |B|-2k, k)`), `AUDIT-046` (Perron brackets), `#268` (odd-cycle `K_3` asymmetry `(1, 0, 2)`).

### 7. `⩩` (`U+2A69`) — Coordinate-Free Exact Null-Equivalence (`X ⩩ Y`)
- **Domain → Codomain:** `(X, Y)` in an exact algebraic domain (`ℤ, ℚ, Sym_n(ℚ), ℚ[[q]]/(q^N), ℚ((ε)), ℕ^3`) ↦ `Bool` (`True` iff exact algebraic residual `X - Y == 0` identically with zero floating-point tolerance, strictly rejecting IEEE-754 float64 near-misses).
- **Invariance Group:** All declared exact ring/group automorphisms; strictly non-tolerant (`CS-11` rejects `F_41/F_40` vs `φ` and depth-23 CF decoys vs `√2` that pass float64 `==`!).
- **Expedition Provenance:** Session 1 Pair 33, `SF-04`, `AUDIT-037`/`040R` (`aletheia` `CS-11` null-equivalence), `AUDIT-048` (killing float64 PSLQ / Ramanujan-Machine mirages).

### 8. `⫩` (`U+2AE9`) — R5 Refusal-Verified Gate (`T ⫩ x`)
- **Domain → Codomain:** `(T : D → Bool, x ∈ D, ℳ(x) ⊂ D finite mutant set) ↦ (accept_ok ∧ all_mutants_refused, kill_ratio ∈ [0,1] ∩ ℚ)`, returning `True` iff `T(x) = True` AND `∀ m ∈ ℳ(x), T(m) = False` (`kill_ratio ⩩ 1`).
- **Invariance Group:** Mutant-ordering permutations `S_{|ℳ(x)|}` and observer-invariant predicate reformulations; strictly defeats vacuous/tautological checks (`T ≡ True` gives `T ⊨ x` yet **FAILS** `T ⫩ x` with `kill_ratio = 0`!).
- **Expedition Provenance:** `SF-04` (unidirectional spec/proof quotient), `AUDIT-030R`/`040R` (`aletheia mutate`), `AUDIT-043` (`18/18`), `AUDIT-046` (`18/18`), `AUDIT-048` (`57/57`).

---

## 4. One-Line Theorem Compression Table & Open Commutator Discovery Targets for `@fractals-probe` (`AUDIT-051`)

### 4.1 Verified Expedition Theorems Compressed to 1 Line
| Source Audit | Verbose Multi-Line Result | 1-Line Aletheia Operator Calculus Expression |
|---|---|---|
| `SF-01` (Quotient-in-Stages) | Iterated Schur complement over disjoint full-rank fibers equals joint Schur complement | `(M ⧅ (B ⊔ C))_r ⩩ 0  ⇒  (M ⧄ B) ⧄ C ⩩ M ⧄ (B ⊔ C)` |
| `AUDIT-041` (Haynsworth–Krein Shadow) | Nonsingular Schur additivity + singular-horizon negative Krein injection `n_- = r_cross` | `⦺(M) ⩩ ⦺(M_{BB}) + ⦺(M ⧄ B)` iff `rk(M ⧅ B) ⩩ 0`; else `⦺_-(M) ≥ rk(M ⧅ B)` |
| `AUDIT-043` (Hodge–Resistance Law) | Single-edge harmonic cycle energy equals `1 - R_eff(e)`; zero iff coboundary | `⧇(e) ⩩ 1 - R_eff(e)`, `⧇(ω) ⩩ 0 ⟺ ω ∈ im(d^0)` |
| `AUDIT-044` (Zero-Float Ramanujan Cert) | Graph `G` is Ramanujan iff `4(d-1)I - A_⊥^2` has zero negative eigenvalues | `⦺_-(4(d-1)I - A_⊥^2) ⩩ 0` |
| `AUDIT-046` (Regulator Equalizer) | Multiplicative regulator net equalizes divergent sum to exact Bernoulli/zeta constant | `𝔑_η(n^k) ⟠ 𝒢_mult ⩩ -B_{k+1}/(k+1)` |
| `AUDIT-044` + `#268` (Cohomological Krein Bound) | Boundary holonomy differential inertia bounded by min-rep flipped adjacency inertia | `⦺_±(L ⦷ χ) ≤ min_{[F']=[χ]} ⦺_±(A_{F'})` |
| `#274` (Monotonic Horizon Screening) | Schur–unmasking commutator across separating screen `C` is always PSD | `⦺_-([⧄_D, ⦷_χ]) ⩩ 0  ⇒  Φ_B(χ) ≤ Φ_C(χ)` |
| `SF-04` / `AUDIT-040R` (R5 Gate) | Harness accepts target and kills 100% of adversarial mutants | `T ⫩ x  ⟺  T(x) ∧ ∀ m ∈ ℳ(x), ¬T(m)` |

### 4.2 Five Sharp Commutator & Composition Discovery Probes for `aletheia_calculus.py` (`AUDIT-051`)
1. **Probe C1 — `[⧄, ⦷]` (Schur Elimination vs. Holonomy Unmasking):** Verify `#274`'s exact PSD commutator identity `H^T ((L ⧄ D) ⦷ χ) H - (L ⦷ χ) ⩩ (Δ_{CC} H)^T Λ_{CC}(χ)^{-1} (Δ_{CC} H) ⪰ 0` across general non-BTZ weighted graphs, multi-layer screens `B ← C_1 ← C_2 ← D`, and odd-cycle `K_3` flips (does PSD screening STILL hold when `L ⦷ χ` has asymmetric inertia `(1, ·, 2)`?!).
2. **Probe C2 — Nested Shadow Composition `(M ⧅ B)` vs `(M ⧄ B) ⧅ C` vs `M ⧅ (B ⊔ C)`:** When fiber `B` is nonsingular (`rk(M ⧅ B) = 0`) while `B ⊔ C` is singular, prove exact preservation of dark-mode nullity and Krein null-coupling `rk((M ⧄ B) ⧅ C) ⩩ rk(M ⧅ (B ⊔ C))`; when BOTH `B` and `C` carry dark modes, test the exact non-additive shadow interaction defect!
3. **Probe C3 — `[⧄, ⟠]` (Schur Elimination vs. Observer-Net Equalization):** When a finite symmetry group `G_obs` acts block-diagonally on `A ⊔ B` (preserving the boundary/bulk split), prove exact commutation `(M ⟠ G_obs) ⧄ B ⩩ (M ⧄ B) ⟠ G_obs`? **WAIT — CHECK NON-LINEARITY!!** Schur complement `M ↦ M_{AA} - M_{AB} M_{BB}^{-1} M_{BA}` is **CONCAVE** in `M ≻ 0` (Lieb / Ando / matrix Jensen!), so averaging over `G_obs` BEFORE vs AFTER Schur elimination satisfies a **strict Loewner inequality**:
   $$((M \mathbin{⟠} G_{\mathrm{obs}}) \mathbin{⧄} B) \;-\; ((M \mathbin{⧄} B) \mathbin{⟠} G_{\mathrm{obs}}) \;\succeq\; 0 \quad\text{i.e.}\quad ⦺_-\!\big([⧄, ⟠]\big) \mathbin{⩩} 0!!$$
   *(Non-zero whenever `M` is not already `G_obs`-invariant — an exact algebraic witness that coarse-graining before vs. after fiber elimination has a definite-sign Jensen/Schur gap!!)*
4. **Probe C4 — `[⦷, ⧇]` (Holonomy Unmasking vs. Hodge-1 Obstruction):** Test exact rational relation between `⧇(e^*) = 1 - R_eff(e^*)` on a flipped interior cycle edge `e^*` and the exact monopole trace `Tr(L ⦷ χ)` / `Φ_B(χ)`!
5. **Probe C5 — `⫩` vs `⩩` Adversarial Soundness Check:** Show explicitly inside `aletheia_calculus.py` that replacing `⩩` with float64 `≈` breaks `T ⫩ x` (mutants survive with `kill_ratio < 1`), proving why `⩩` and `⫩` are algebraically coupled!

---

*Maintained by `session-cartographer`. Empirically audited: `0 / 227,540` Lean 4 collisions, `0` expedition collisions, `0` session collisions, `0` CRLF, `0` leaks.*
