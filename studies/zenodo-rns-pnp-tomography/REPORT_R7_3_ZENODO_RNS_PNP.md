# Wave 2 Round 7 — Arm R7-3 (`AUDIT-070`): Exact Mathematical, Algorithmic & Forensic Tomography of Zenodo `23644664` (*Proyecto RNS / P-NP*, V00–V03)

- **Arm / Owner:** Arm R7-3 (`spectral-prover`), target audit `AUDIT-070`
- **Target Record (strictly read-only, `0` external writes):** Manuel Romero, *Proyecto RNS / P-NP: Tratado Integral de Física Geométrica, Unificación Estructural y Reducción Jerárquica en Problemas de Complejidad NP (Colección Completa V00–V03)*, DOI `10.5281/zenodo.23644664`, `https://zenodo.org/records/23644664` (`12` published `.md`/`.zip` files downloaded and MD5-verified against `record_23644664.json` `sha256:6198464c...`).
- **Oracle Class & Honest Novelty (Law-4):** `exact+anchor` | **`N1`** (rigorous adversarial falsification of extraordinary `P = NP` / exactness / `70x` claims paired with minimal exact zero-float counterexamples, honest Law-2 verification of reproducible heuristic gains, and exact 8-glyph operator mapping; strict `R7-N0-05/06/11/12` quarantine).

---

## 1. Executive Verdict

**Verdict on Extraordinary Claims (`P = NP`, "exact deterministic polynomial-time resolution", universal `70x` TSP speedup): `FALSIFIED` by minimal zero-float exact counterexamples and live execution of the author's own unmodified code.**

**Law-2 Steelman Verdict (What *Does* Reproduce Honestly):**
Three narrow heuristic benchmarks from `Code V01`/`Code V03` genuinely reproduce their stated numbers on easy/small regimes:
- `Code V01/rns_scheduling_benchmark.py` (`M=4, N=40`, `U[50,150]`): live output matches **`LPT 13/100` vs `RNS 68/100`** verbatim (classical LPT + 1-1 / 2-1 swap local search in a dense-integer birthday-paradox regime).
- `Code V01/rns_knapsack_benchmark.py` (`N=100` random `U[1000,10000]` subset-sum): live output matches **`232947/232947` (`0` slack)** verbatim (dense pair sums easily cover small residual slack).
- `Code V03/gemini-code-1792866285549.py` (`queen5_5.col`): live output matches **greedy `8` -> clique+DSATUR `5` exact** verbatim (textbook Brélaz 1979 DSATUR + greedy clique initialization).
- Spatial L1-cache batching (`00A V00a.md`, `M=60`, `14.4 KB` local matrices) genuinely reduces distance-matrix memory (`34.33 MiB -> 14.4 KB` active block) and distance-matrix entry count by **`9,000,000 / 182,500 = 3600/73` (`~49.3x`)** — a well-known spatial-tiling hardware locality effect (Karp 1977), NOT a complexity-class breakthrough.

---

## 2. Live Forensic Audit of `Code V00..V03.zip` vs. Treatise Claims (`V00a..V03.md`)

Pinned archive SHA-256 digests (all MD5-verified against Zenodo API):
- `Code V00.zip`: `13b63a9e38bb0395...` (`9` files; `1792852737867.py` == `1792853404109.py`)
- `Code V01.zip`: `2710ac5dc90a7eed...` (`11` files)
- `Code V02.zip`: `059a283348f672c1...` (`4` files — **100% byte-for-byte identical** to `Code V01`'s `rns_*_benchmark.py`!)
- `Code V03.zip`: `52f8ff0b16b726c3...` (`6` files; `gemini-code-1792867608655.py` is raw Markdown saved as `.py` -> `SyntaxError` at L6; `gemini-code-1792866299911.py` is a notebook fragment missing `N_q6`/`adj_q6`)

| ID | Treatise Claim (`file:line`) | Untouched Author Code & Live Result | Exact Diagnosis |
|---|---|---|---|
| **`RNS-EMP-01`** | `V02.md:71-73`, `V03.md:100`: $16\times 16$ grid (256 nodes) reaches **`25.600` (`0.00%` exact)**, beating 2-opt's `26.400 (+3.12%)`. | `Code V01/rns_tsp_benchmark.py` (identical in `Code V02`): **`Costo RNS obtenido: 26643 \| Error: 4.07%`**! | **Worse than the `26.400` 2-opt baseline!** Each $8\times 8$ quadrant sub-cycle stalls at `6646` (vs exact `6400`), `4 * 6646 = 26584` + `59` patching penalty = `26643`. |
| **`RNS-EMP-02`** | `V02.md:87-88`, `V03.md:116`: 3-SAT Modular (`N=24`) reduces backtracks by **`48.7%`** vs blind order via `W_jj`. | `Code V01/rns_3sat_benchmark.py:81-89`: **`Backtracks Orden Ciego: 3`**, **`Backtracks Tensor RNS: 18 (Reduccion notable)`**! | **`6x` (`+500%`) MORE backtracks**, yet L89 hardcodes `"(Reduccion notable)"`! Moreover, `L56-62` does NOT compute $W=B^\top B$ — it computes a buggy Jeroslow–Wang/MOMS score (`sum 1/|unass|^2`) that fails to skip already-satisfied clauses! |
| **`RNS-EMP-03`** | `00A V00a.md:235-239`, `V02.md:76`: `N=3000, M=60` achieves **`70x` speedup** (`0.008s` matrix + `0.019s` tour). | `Code V00/gemini-code-1792854013867.py` (`N=3000, BATCH_SIZE=60`): **TIMES OUT (`>30 s`)**! | `patch_tours` (`L79-91, 135-137`) runs sequential $O(N^2)$ edge-pair scans: $\sum_{k=1}^{49}(60k)(60) = \mathbf{4,410,000}$ pairs (`5` `distance_euc` calls per inner pair + `73,500` outer `d_u` calls = **`22,123,500` `distance_euc` calls**, `2.46x` the `9,000,000` global matrix entries!), making end-to-end execution `>50x` slower than the `0.558s` global matrix. |
| **`RNS-EMP-04`** | `Code V00/rns_benchmark_suite.py` (automated SAT + Subset-Sum suite). | `python3 -B rns_benchmark_suite.py`: **`SyntaxError` at `L195`** (unterminated multiline string `print("\n"`). | Suite cannot parse or execute unmodified; `W_jj` (`L63`) is merely static variable occurrence count. |

---

## 3. Exact Zero-Float Formal Disproofs of `V03 Anexo` Theorems (`2.1`, `3.2`, `4.1`, `5.1`, `6.1`)

All five formal theorems in `03 TRATADO ANALÍTICO FORMAL V03.md` are audited with pure Python 3 stdlib zero-float exact oracles in [zenodo_rns_pnp_audit.py](zenodo_rns_pnp_audit.py):

1. **Gramian Blindness Theorem on 3-SAT (Obstruction to `Teorema 2.1` $W = B^\top B$ & `P = NP`):**
   - Construct the exact simple 3-CNF encoding of **Tseitin($K_4$, $b$)** (`n = 6` variables, `m = 16` distinct 3-clauses, zero duplicates):
     $x_1 \oplus x_2 \oplus x_3 = 0,\; x_1 \oplus x_4 \oplus x_5 = 0,\; x_2 \oplus x_4 \oplus x_6 = 0,\; x_3 \oplus x_5 \oplus x_6 = b$.
   - For $b = 0$: **`8/64` exact models (`SAT`)**. For $b = 1$: **`0/64` exact models (`UNSAT`)**.
   - **Exact Identity:** $W_{\mathrm{SAT}} = B_{\mathrm{SAT}}^\top B_{\mathrm{SAT}} = 8 I_6 = B_{\mathrm{UNSAT}}^\top B_{\mathrm{UNSAT}} = W_{\mathrm{UNSAT}}$ AND linear bias $\mathbf{1}^\top B_{\mathrm{SAT}} = \mathbf{0} = \mathbf{1}^\top B_{\mathrm{UNSAT}}$.
   - **Consequence:** No solver whose signal depends solely on $W = B^\top B$ and linear bias can distinguish SAT from UNSAT; the true separator is $\mathbb{Z}_2$ cohomology $\mathbin{⧇}(\Phi_{\mathrm{UNSAT}}) = 1 \ne 0 = \mathbin{⧇}(\Phi_{\mathrm{SAT}})$ (directly bridging to Arm R7-4 `Frobenius` Tseitin / `AUDIT-044`).
2. **Zero-Float Bareiss Inertia Refutation of `Teorema 3.2` (`V03 Anexo:67-73`, $M = (A_0 + I)^2$):**
   - On the 10-vertex 2-community graph $G_{10} = K_{4,4}(\{0..7\}) \cup \{(7,8)\} \cup K_2(\{8,9\})$ with $A = A_0 + I_{10}$ and $M = A^2$, BOTH pure-integer Bareiss congruence and independent Faddeev–LeVerrier/Descartes certify identically:
     `inertia(A - 3I) = (1, 9, 0)` ($\implies \lambda_2(A) < 3 \implies \lambda_2(A)^2 < 9$) and `inertia(A + 3I) = (9, 1, 0)` ($\implies \lambda_{\min}(A) < -3 \implies \lambda_{\min}(A)^2 > 9 > \lambda_2(A)^2$).
   - Thus squaring $A$ promotes the **most negative** internal bipartite oscillation of $K_{4,4}$ into $\lambda_2(M)$, destroying community separation!
   - *(Law-2 Steelman Repair: replace $M = (A_0 + I)^2$ with PSD shifted adjacency $A_0 + d_{\max} I \succeq 0$ — verified `inertia = (10, 0, 0)` at $d_{\max}=5$ — or standard combinatorial Laplacian $L = D - A_0 \succeq 0$.)*
3. **Pythagorean Exact-Enumeration Refutation of `Teorema 4.1` ("Ley de la Acera", `V03 Anexo:83-94`):**
   - Exact 5-point configuration $v_0=(0,0),\; v_1=(0,8),\; v_2=(-15,0),\; v_3=(15,0),\; v_4=(0, M)$ (`(8, 15, 17)` triple) gives unique shortest intra-cluster edge $s_0 = d(v_0, v_1) = 8$ and exact cluster-to-exterior gap $g_0 = \min_{u \in \{0..3\}} d(u, v_4) = d(v_1, v_4) = M - 8$, so $\sigma_0 = (M - 8)/8 \to \infty$ exceeds ANY finite $\tau > 1$ (at $M=8008$, $g_0 = 8000$ and $\sigma_0 = \mathbf{1000}$ exact).
   - Over ALL 12 undirected Hamiltonian cycles (letting $R = \sqrt{M^2 + 225} > M$), the unique optimal tour WITHOUT $(0,1)$ is `[0, 3, 4, 1, 2]` with exact length $L_{\mathrm{opt}} = 39 + M + R$, while the minimum cycle WITH $(0,1)$ is `[0, 1, 2, 4, 3]` with length $40 + 2R$ (other cycles with $(0,1)$ have $45 + M + R$ and $55 + M + R$). Thus EVERY cycle containing $(0,1)$ exceeds $L_{\mathrm{opt}}$ by at least $1 + (R - M) > \mathbf{+1 > 0}$ for ALL $M > 8$ (and $\ge +1$ under TSPLIB `EUC_2D` integer rounding: at $M=8008$, Held–Karp certifies `opt_cost = 16055` on `[0, 3, 4, 1, 2]` vs exhaustive best forcing `(0,1)` = `16056` on `[0, 1, 2, 4, 3]`), falsifying `Teorema 4.1` unconditionally.
4. **Exact Minimal Counterexamples to `Teorema 5.1` (`V03 Anexo:103-115`, Extended Pivot $\Delta' = \Delta + P$):**
   - **0-1 Knapsack (`N=3`):** `w=[1,1,1000], v=[2,2,1000], C=1000` -> exact DP OPT = **`1000`**, RNS 1-1/1-2 pivot stalls at **`4`** (`249/250 = 99.6%` error; generalizes to unbounded $1 - 4/C \to 100\%$ failure).
   - **Subset-Sum (`N=5`):** `w=v=[52,25,25,25,25], C=100` -> exact DP OPT = **`100`**, RNS stalls at **`77`** (`23/100 = 23%` error).
   - **Scheduling $P \parallel C_{\max}$ (`M=2, N=7` & `M=3, N=9`):** `d=[36,29,24,16,14,12,11]` has exact partition OPT = **`71`** (`{36,24,11}`, `{29,16,14,12}`), yet RNS stalls at **`76`** (`5/71` gap); 3-Partition `d=[30,29,29,28,26,25,20,14,12]` has exact OPT = **`71`**, yet RNS stalls at **`75`** (`4/71` gap).
   - Plus code-vs-treatise complexity bug: `V03 Anexo:114` claims $O(N^2)$ via two-pointer search, while both `rns_knapsack_benchmark.py:43-55` and `rns_scheduling_benchmark.py:41-55` implement nested $O(N^3)$ loops.
5. **Exact Refutation of `Teorema 6.1` (`V03 Anexo:119-135`, Deterministic Deposit Collapse) & Mycielski $M_4$ Gap:**
   - On any symmetric regular configuration ($K_4$, $D=V$, $V \setminus D = \emptyset$), $|\mathcal{A}_t(v)| = 3 > 2$ permanently; no deterministic collapse instant $t^*$ exists without branching.
   - On Graph Coloring (`V03`), exact Mycielski graph $M_4$ (`11` vertices, `20` edges) is verified triangle-free ($\omega = 2$) yet non-3-colorable and 4-colorable ($\chi = 4$, gap $\chi - \omega = 2$, unbounded in $M_k$), refuting clique-saturation exactness.

---

## 4. Law-4 Prior-Art Mapping (`R7-N0-05/06/11/12`) & 8-Glyph Bridge

| RNS Term in Zenodo `23644664` | Established Prior Art (`N0` Quarantine) | Exact 8-Glyph Operator Bridge (`AUDIT-051`) |
|---|---|---|
| Tensor Gramiano $W = B^\top B$ + Rank-1 Update (`Teorema 2.1`) | Gram matrix / Sherman–Morrison–Woodbury (1950); static $W_{jj}$ = CNF degree; `rns_3sat` = Jeroslow–Wang (1990) / MOMS | `W_SAT ⩩ W_UNSAT ⩩ 8*I_6`, requiring `W ⧄ S` (`SF-01`) + `⧇(Phi)` (`SF-05` $\mathbb{Z}_2$ cohomology, linking to Arm R7-4) |
| Axioma Auto-Lazo $A_{ii}=1$, $M=A^2$ (`Teorema 3.1/3.2`) | Shifted adjacency / lazy random walk (Chung 1997); Fiedler vector (1973); spectral clustering (Shi–Malik 2000) | `⦺(A - 3I) ⩩ (1, 9, 0)` & `⦺(A + 3I) ⩩ (9, 1, 0)` proves squaring inversion; fixed by $A_0 + d_{\max}I \succeq 0$ |
| Seed & Grow + Macro-TSP + Cosido (`00A V00a.md`) | Karp planar partitioning (1977), NN + 2-opt (Croes 1958), Christofides (1976), Lin–Kernighan (1973), Arora PTAS (1998) | `L_best_with - L_opt = 1 + (R - M) > +1` refutes `Teorema 4.1` for all $\sigma_0 = (M-8)/8 \to \infty$ |
| Pivote Ampliado $\Delta' = \Delta + P$ (`Teorema 5.1`) | LPT (Graham 1969) + 1-1 / 1-2 / $k$-exchange local search (Finn–Horowitz 1979) | Certified `249/250`, `23/100`, `5/71`, `4/71` suboptimality witnesses (`⫩` R5 verified) |
| Camarilla + Saturación de Masa + Pivote Cromático (`Code V03`) | DSATUR (Brélaz 1979) + Kempe chain swap (1879) | Exact Mycielski $M_4$ certifies $\omega=2 < \chi=4$ |

---

## 5. Artifacts in `studies/zenodo-rns-pnp-tomography/`

- [zenodo_rns_pnp_audit.py](zenodo_rns_pnp_audit.py)
- [test_r5_zenodo_rns_pnp.py](test_r5_zenodo_rns_pnp.py)
- [zenodo_rns_pnp_certificate.json](zenodo_rns_pnp_certificate.json)
- [REPORT_R7_3_ZENODO_RNS_PNP.md](REPORT_R7_3_ZENODO_RNS_PNP.md)
