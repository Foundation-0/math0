# Exact Mean-Preserving Contraction & Flag Re-Pivoting Scan of Frontier `#7000` (`CrocSwap/integer-mult-bounds`)

**Scoped Audit & Formal Certificate Package**: `research/frontier7000-spread-scan`  
**Audited Frontier**: [`CrocSwap/integer-mult-bounds`](https://github.com/CrocSwap/integer-mult-bounds) Selected PR `#7000` ([`certificates/selected-result.json`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/certificates/selected-result.json), $\kappa = \frac{363005817}{100000000000} = 0.00363005817$, `audited_source_head = 93effe2a135bf57b9e484cb630d8dd057159aec9`)  
**Certificate SHA-256**: `9ab85cab12899f2f30c94e60b2b9fcaf03ec7e8f5e0511a58ce6515605f20ad3`  
**License**: Apache-2.0

## 1. Exact Three-Stratum Decomposition of Frontier `#7000`'s `117,612` Paid Calls

Inspecting [`research/shared-wire-split-composition/FULL-RESULT.json`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/research/shared-wire-split-composition/FULL-RESULT.json), [`certificates/frontier7000/CLAIM.json`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/certificates/frontier7000/CLAIM.json), [`docs/research/pr-intake-evidence/pr7000-application/PROOF-REVIEW.md`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/docs/research/pr-intake-evidence/pr7000-application/PROOF-REVIEW.md), and [`research/shared-wire-split-composition/CONSTRUCTION.md`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/research/shared-wire-split-composition/CONSTRUCTION.md) reveals that the Frontier `#7000` power-sum equation
$$\Delta(c) = \sum_{(r, T_r) \in T} T_r \, r^{1-c} - \sum_{(r, P_r) \in P} P_r \, r^{1-c} = 0$$
has exact root $\kappa_{\text{raw}} \in \left(\frac{363005817468836708593357676489}{10^{32}}, \frac{363005817468836708593357676490}{10^{32}}\right)$, productive rank mass $321,364$ (`23,392` fields = `18 × 1,080` helpers + `3,952` roots), paid rank mass $319,844$ (`117,612` calls), and exact rank surplus $S = 1,520$. Crucially, `P` partitions into **three structurally distinct strata**:

1. **Stratum A — `18` Native Invocations (`18 × 6,310 = 113,580` calls, `96.57%` of `P`, rank mass `197,316`)**: Local `MOVE` frame quotients $L C_r R$ on 9 native slots (`r ∈ {1..8}`), with per-invocation histogram `native.paid = {1: 4075, 2: 828, 3: 811, 4: 241, 5: 320, 6: 17, 7: 12, 8: 6}`. **This is the sole live arena for mean-preserving spreads.**
2. **Stratum B — Caller `QUERY` Scratch Leaves (`416` calls at `r = 1`, mass `416`)**: Boundary-locked at the minimum positive rank $r = 1$ (zero spread headroom).
3. **Stratum C — Caller Whole-Idle Stage-Block Unions (`3,616` calls on $8\mathbb{Z} \cap [8, 64]$, mass `122,112`)**: `{8: 704, 16: 416, 24: 416, 32: 416, 40: 416, 48: 416, 56: 416, 64: 416}`. Locked to multiples of `8` by 8-slot stage-block dimensions per [`CONSTRUCTION.md`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/research/shared-wire-split-composition/CONSTRUCTION.md).

Meanwhile, in [`CLAIM.json`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/certificates/frontier7000/CLAIM.json) and [`EFREE-RESULT.json`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/research/paired-query-only-bit/EFREE-RESULT.json), the paired BIT supplier already supports `complex_BIT_premise = 376669/100000000 = 0.00376669` (`+1.3663e-4` above Complex) and `admitted_BIT_saving = 12039/3125000 = 0.00385248` (`+2.2242e-4` above Complex). Thus the **Complex caller is 100% of the active exponent bottleneck** across the next `+3.76%` of $\kappa$.

## 2. Complete Symmetric Pairwise Spread Spectrum on `native.paid` (`1 <= r - d < r + d <= 8`)

Because native frames act on `9` slots (`max paid rank <= 8`), two rank-$5$ `MOVE`s ($5 + 5 = 10 > 9$) **cannot** be coalesced into a single native `MOVE`, yet **can** be spread into $(2, 8)$, $(3, 7)$, or $(4, 6)$ while keeping call count (`117,612`), rank mass (`319,844`), and surplus (`S = 1,520`) strictly invariant:

| Symmetric Spread | Integer Concavity Witness | Max Local (`Global`) Pairs | $\Delta\kappa$ per Local Pair | Bucket Max $\Delta\kappa$ | Saturated $\kappa$ |
| :--- | :--- | ---: | ---: | ---: | ---: |
| `(2, 2) -> (1, 3)` | `2^4 < 1^1 · 3^3` | `414` (`7452`) | `+8.178632e-08` | `+3.417808e-05` | `0.003664236258` |
| `(3, 3) -> (2, 4)` | `3^6 < 2^2 · 4^4` | `405` (`7290`) | `+5.302580e-08` | `+2.160294e-05` | `0.003651661110` |
| `(3, 3) -> (1, 5)` | `3^6 < 1^1 · 5^5` | `405` (`7290`) | `+2.272348e-07` | `+9.441885e-05` | `0.003724477027` |
| `(4, 4) -> (3, 5)` | `4^8 < 3^3 · 5^5` | `120` (`2160`) | `+3.938645e-08` | `+4.732478e-06` | `0.003634790653` |
| `(4, 4) -> (2, 6)` | `4^8 < 2^2 · 6^6` | `120` (`2160`) | `+1.631652e-07` | `+1.968503e-05` | `0.003649743200` |
| `(4, 4) -> (1, 7)` | `4^8 < 1^1 · 7^7` | `120` (`2160`) | `+3.948193e-07` | `+4.799927e-05` | `0.003678057442` |
| `(5, 5) -> (4, 6)` | `5^10 < 4^4 · 6^6` | `160` (`2880`) | `+3.136110e-08` | `+5.024665e-06` | `0.003635082839` |
| `(5, 5) -> (3, 7)` | `5^10 < 3^3 · 7^7` | `160` (`2880`) | `+1.281743e-07` | `+2.062346e-05` | `0.003650681639` |
| `(5, 5) -> (2, 8)` | `5^10 < 2^2 · 8^8` | `160` (`2880`) | `+3.003271e-07` | `+4.869183e-05` | `0.003678750004` |
| `(6, 6) -> (5, 7)` | `6^12 < 5^5 · 7^7` | `8` (`144`) | `+2.606231e-08` | `+2.085089e-07` | `0.003630266684` |
| `(6, 6) -> (4, 8)` | `6^12 < 4^4 · 8^8` | `8` (`144`) | `+1.057866e-07` | `+8.464652e-07` | `0.003630904640` |
| `(7, 7) -> (6, 8)` | `7^14 < 6^6 · 8^8` | `6` (`108`) | `+2.229862e-08` | `+1.337958e-07` | `0.003630191970` |

## 3. Per-Bucket `[1, 8]` Jensen Concavity Tax & BIT-Ceiling Crossings

Projecting each interior bucket $r \in \{2..7\}$ onto the `[1, 8]` extreme ray $r = \frac{8-r}{7} \cdot 1 + \frac{r-1}{7} \cdot 8$ (`7` calls of rank $r \mapsto (8-r)$ calls of rank `1` + $(r-1)$ calls of rank `8`) isolates `99.07%` of all spreadable concavity mass inside **$r \in \{2, 3, 4, 5\}$**:

| Bucket | Local Calls | Global Calls (`×18`) | `[1, 8]` Integer Balayage $\Delta\kappa$ | Resulting $\kappa$ |
| :--- | ---: | ---: | ---: | ---: |
| `r = 2` | `828` | `14904` | `+1.326392e-04` | `0.003762697350` |
| `r = 3` | `811` | `14598` | `+1.941790e-04` | `0.003824237134` |
| `r = 4` | `241` | `4338` | `+6.046509e-05` | `0.003690523267` |
| `r = 5` | `320` | `5760` | `+7.418555e-05` | `0.003704243728` |
| `r = 6` | `17` | `306` | `+2.952640e-06` | `0.003633010814` |
| `r = 7` | `12` | `216` | `+1.159599e-06` | `0.003631217773` |

- **Global `[1, 8]` Bauer–Karamata Extreme-Point Ceiling** (`native.paid -> {1: 5645, 5: 1, 8: 664}`): $\kappa_{\text{bal}} = 0.004141907509$ (`+5.118493e-04`, **`+14.10%`**), exceeding both `complex_BIT_premise` (`0.00376669`) and `admitted_BIT_saving` (`0.00385248`).
- **Minimal Symmetric Pair Recipe Crossing `complex_BIT_premise` (`0.00376669`)**: Spreading `120` local pairs of `(4,4)->(1,7)`, `160` local pairs of `(5,5)->(2,8)`, and `160` local pairs of `(3,3)->(1,5)` (`440` local pairs = `7920` global pairs) certifies $\kappa = 0.003766795470 > 0.00376669$.

## 4. Physical Reversibility Criterion: `GL_9` Commuting-Spectator Flag Re-Pivoting vs. Mod-4 Phase Lock

Arithmetic histogram feasibility does **not** by itself establish a physical supplier (`AGENTS.md`). In `PROOF-REVIEW.md` Section 2, two consecutive `MOVE`s $U_0 \xrightarrow{Q_1} U_1 \xrightarrow{Q_2} U_2$ around an intervening contact operator $C$ at frame $U_1$ admit a reversible rank-preserving spread $(r, r) \to (r - d, r + d)$ **if and only if**:
1. **Commuting Deferred Factor**: $Q_1 = S \, Q'_1$ where $\operatorname{rank}(Q'_1 - I_9) = r - d$, $\operatorname{rank}(Q_2 S - I_9) = r + d \le 8$, and $S$ commutes with $C$ ($C S = S C$, i.e., $S$ acts only on spectator axes untouched by the intervening `ADD`/`QUERY`), giving exact end-to-end operator identity $Q_2 C Q_1 = (Q_2 S) C Q'_1$ (proved in `Frontier7000SpreadBounds.lean` and verified on explicit `18 × 18` `GL_9(Z)` matrices in `check_spread_scan.py` and `c11_frontier7000_scanner.c`).
2. **Boundary & Mod-4 Phase Preservation**: Re-pivoting $U_1 \mapsto U'_1$ must keep scalar contacts between equal frames and preserve degree-two phase polynomials modulo 4 across the `104` main-boundary pairs and `14,400` caller contacts. Whenever $C$ couples actively to all $r$ quotient axes of $Q_1$ (`C_coupled` control in our certificate), $C S \neq S C$ and the spread is physically obstructed without a paid compensatory adapter.
