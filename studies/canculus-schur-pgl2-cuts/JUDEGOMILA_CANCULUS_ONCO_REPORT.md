# Wave 2 Round 4B — Arm R4B-2 (`AUDIT-050`): Exact-Operator Cross-Pollination & Tomography of `judegomila/canculus` and `judegomila/OnCo`

**Audit ID:** `AUDIT-050` | **Oracle Class:** `exact+anchor` | **Honest Novelty Grade:** `N1` (clean-room live tomography, exact rational/combinatorial normal-form & Schur/$PGL(2)$/tropical bridges, and epistemic-graph reverse extraction; zero fabricated `N2` claim)  
**Ethical Posture:** **STRICTLY READ-ONLY** on all external repositories (`0` external PRs, `0` external issues, `0` external comments).

---

## 1. Pinned Read-Only Upstream Sources & Law-4 `N0` Quarantine

| Upstream Repository (Read-Only) | Pinned Commit SHA | Core Files Inspected Full-Text |
|---|---|---|
| `judegomila/canculus` | `ef76861b4e84adc7c629713df72fe53a99928c71` | `README.md`, `src/lib/calculus.ts`, `src/lib/models.ts`, `src/lib/calculus.test.ts` |
| `judegomila/OnCo` | `d43842087851281084d0f9e7171f555635361e7f` | `README.md`, `AGENTS.md`, `src/lib/graph.ts`, `src/lib/schema.ts`, `scripts/{validate,provenance,change-class}.ts`, `packages/onco-mcp/src/server.ts` |

**Strict Law-4 `N0` Prior-Art Quarantine:** Monotone Boolean route antichains, De Morgan hypergraph transversal duality (Berge 1989), Tarski least fixed-point closure (Tarski 1955), Prop. 7.8 non-upward-closed robustness, and the BRAF–EGFR / PTEN reciprocal models belong to Gomila (2026, `canculus`); linear feedback Schur complements and 1D $PGL(2)$ Möbius cross-ratios are classical; tropical shortest-hyperpath relaxation generalizes Bellman–Ford (1958); and OnCo's single-direction backlinks, link-sense disambiguation, git-blame provenance, semantic diff classification, and grounded MCP architecture belong to Gomila (`OnCo`).

---

## 2. Outgoing Live Tomography on `judegomila/canculus@ef76861b` (`src/lib/calculus.ts`)

Every defect below was **reproduced live in Node.js** directly against unmodified `judegomila/canculus@ef76861b/src/lib/calculus.ts`:

| ID | Exact Site (`calculus.ts`) | Live Witness Executed on Unmodified Upstream | Upstream Output | Hardened Clean-Room Closure (`canculus_onco_bridge.py`) |
|---|---|---|---|---|
| `CANC-B1` | `L148` (`family.has(routeKey(p))`) | `R0 = [["M"], ["B","M","E"]]` vs `minimalAntichain(R0) = [["M"]]` with rule `prereq=[["B","M","E"]] -> [["G"]]` under `U={"M"}` | **Normal form flips verdict:** `unnorm.robust = false`, `norm.robust = true` (violates NF functoriality!) | `semantic_adaptation_closure` uses upward-closure entailment `any(s <= p for s in family)`: `NF(F(R0)) == NF(F(NF(R0)))` (`robust=False` on both) |
| `CANC-B2b` | `L166` (default `universe` omits `R0`/guard caps) | `adaptationClosure(sys.baseline, sys.rules, new Set(["B"]), sys.ctx)` (exact call in `calculus.test.ts:87` on flagship `brafSystem()`!) | `robust = false`, `trace.length = 1` (`rho_EGFR` fired!), YET **`rulesEncoded = 0`** ("no mechanisms encoded"!) | Mandatory `universe` + existential coverage `rules_encoded_exact` |
| `CANC-B2a` | `L120-121` (`guard(everything, ctx)`) | Non-monotone monotherapy guard `U.has("B") && !U.has("G")` WITH full 6-cap `universe` | `robust = false`, `trace.length = 1`, YET **`rulesEncoded = 0`** (evaluating only top set `U = V` misses exclusion guards!) | `rules_encoded_exact` tests existential satisfiability over $2^V$ (`rules_encoded == 1`) |
| `CANC-B3` | `L316, 334` (float64 `alphaCrit` rounding) | `u=1, g=3, h=3, theta=0.3` (exact $\alpha_{\mathrm{crit}} = 7/27$) | `r(alphaCrit) = 0.29999999999999993` (`diff = -5.55e-17`) $\implies$ **`r >= theta` FLIPS TO `false`** at exact criticality! | Pure `Fraction` `alpha_crit_exact`: $\alpha_{\mathrm{crit}} = 7/27$, $r(7/27) = 3/10 \equiv \theta$ (`r >= theta == True`) |
| `CANC-B4` | `L22` (`routeKey`) & `L362` (`while (changed)`) | `sameRoute(["B"], ["B","B"])`, `sameRoute(["A+B"], ["A","B"])`, and negative-delay rule | `false` (breaks idempotence $B \land B \equiv B$), `true` (`"+"` delimiter collision), and unbounded loop on `delay < 0` | `frozenset[str]` routes (idempotent, collision-free) + `delay < 0` `ValueError` refusal + Bellman–Ford iteration cap |

---

## 3. Beyond-Language Exact-Operator Cross-Pollination (`SF-01` / `SF-02` / `SF-04` / `SF-05`)

Stripping oncology labels (`BRAF`, `EGFR`, `PTEN`, `melanoma`) reveals exact structural isomorphisms across our expedition:

1. **Route Normal Forms & De Morgan Transversals (`WEFT-T5` / `Moissanite-Labs/weft#227`):** `minimal_antichain` & `minimal_transversals` realize the exact **Free Distributive Lattice De Morgan Involution $\operatorname{Tr}(\operatorname{Tr}(M)) \equiv M$** (verified on BRAF-CRC), while `CANC-B1` is an exact instance of `SF-04` normal-form confluence violation (`F(NF(x)) != NF(F(x))`).
2. **Prop. 7.8 Non-Upward-Closed Robustness (`AUDIT-043` `SF-05`):** On $V=\{a,b,c\}$, $U_1=\{a\} \subset U_2=\{a,b\} \subset U_3=\{a,b,c\}$ transitions `True -> False -> True` — a direct combinatorial model of observer/intervention-dependent state spaces (where adding an intervention changes the reachable route family $R^*_{U,c}$).
3. **Linear Feedback Release = Exact $2 \times 2$ Schur Complement (`SF-01` #22) $\cap$ 1D $PGL(2, \mathbb{Q})$ Möbius Cross-Ratio (`SF-02` / `scry#4` / `AUDIT-046`):**
   $$\begin{pmatrix} 1 & h \\ -\alpha g & 1 \end{pmatrix}\begin{pmatrix} r \\ y \end{pmatrix} = \begin{pmatrix} u \\ 0 \end{pmatrix} \implies S(\alpha) = 1 + \alpha g h, \quad r(\alpha) + h\, y(\alpha) \equiv u$$
   Both $r(\alpha)$ and $y(\alpha)$ preserve exact 4-point $PGL(2, \mathbb{Q})$ cross-ratios (`CR(alpha) == CR(r) == CR(y)` identically over `Fraction`).
4. **Timed Closure = Exact Tropical $(\min, \max, +)$ Hyperpath Relaxation (`AUDIT-029` / `AUDIT-043` `SF-05`):** Reproduces BRAF-CRC (`delay=12`, robust at `T=6`, fails at `T=24`) and BRAF-melanoma (`delay=1440`, robust at `T=168`, fails at `T=2160`) with exact zero-gap primal–dual Bellman–Ford witness certificates.

---

## 4. Incoming Reverse Extraction from `judegomila/OnCo@d4384208` $\to$ `cross_pollination_graph.json` & `Foundation-0/aletheia`

Full-text inspection of `OnCo`'s ~19,000-record cited oncology knowledge graph surfaced **five production-hardened epistemic-graph patterns** directly transferable to our own epistemic web (`cross_pollination_graph.json`) and `aletheia` v1.2+:

1. **Single-Direction Edge Declaration + Build-Time Derived Backlinks (`src/lib/graph.ts:12-44`):** Refuses duplicate IDs and dangling references at graph construction time while eliminating bidirectional-sync drift.
2. **Zero-Tolerance Link-Sense Disambiguation (`scripts/validate.ts:5-23`):** Enforces *"resolves $\ne$ right referent"* — rejecting typed fields pointing to glossary stubs or wrong-context namesakes (`cancers: ["brain-mets"]` where `brain-mets` has `kind: "term"`), while **ratcheting** non-zero secondary audit classes (`scripts/link-sense-audit.test.ts`, isomorphic to `aletheia ratchet`).
3. **Line-Level Git-Blame Provenance with Automated Private-Name Redaction (`scripts/provenance.ts:27-125`):** Maps every entity record to its newest surviving `git blame --line-porcelain` commit SHA/author/date and scrubs private project identifiers before emitting public provenance JSON.
4. **Fail-Closed Semantic Diff Governance (`scripts/change-class.ts`):** Separates `data` refreshes from `product`/schema changes requiring explicit owner approval (inspecting inside `package.json` to distinguish `scripts` from dependencies, and failing closed to `product` on unrecognized config files).
5. **Extractive Zero-Generation Grounded MCP + Deep-Value Compare (`packages/onco-mcp/src/server.ts:29-51, 80-95`):** Assembles grounded responses solely from cited structured fields (explicitly stating `"OnCo has no record of this"` on gaps), and compares raw deep structures (`isDeepStrictEqual`) rather than truncated CLI display summaries (`SF-04` anti-projection-collapse).

*(All 4 operational gates are prototyped cleanly in `canculus_onco_bridge.py` Part 4 and mutation-tested to `100.0%` R5 kill rate.)*

---

## 5. Verification Summary & Falsification Criteria

- **Artifacts (`symbiosis/round4/judegomila-canculus-onco/`):** `canculus_onco_bridge.py`, `test_canculus_onco_r5.py`, `canculus_onco_results.json`, `JUDEGOMILA_CANCULUS_ONCO_REPORT.md`.
- **4-Mode Isolated R4 Parity (`-I -B`, `-I -O -B`, `-I -B -W error`, `-I -O -B -W error`):** **`4/4` bit-identical** on `canculus_onco_bridge.py --json` (`SHA-256: 2574213dfcb656bc9f16d3086736d9ab1cdb8f3c763dcc2d3d70a478924b1c9b`, exact match to `canculus_onco_results.json`); `7/7` unittest tests pass in `0.02s` across all 4 isolated modes.
- **`aletheia v1.2.0 audit-check`:** **`PASS`** (`4` files, `0` CRLF, `0` `__pycache__`, `0` `/home/` leaks, `0` bare `assert`s, `0` unseeded RNG, `0` JSON errors, `1/1` isolated R4 script passed).
- **`aletheia v1.2.0 mutate --add-cwd`:** **`33/33` (`100.0%`) KILLED, `0` SURVIVORS**.
- **Falsification Criteria:** Fails if any of `CANC-B1..B4` does not reproduce live on `judegomila/canculus@ef76861b`, if any exact rational De Morgan / NF-functoriality / Schur-conservation / $PGL(2)$ cross-ratio / tropical-dual / OnCo-gate assertion fails, if any refusal-site mutant survives `aletheia mutate --add-cwd`, or if any R4/`audit-check` gate fails.
