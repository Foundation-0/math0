# Track S20e: Coupled Multi-Entity Farkas Dual Cuts & Deadlock Obstructions on Open Sokoban Frontier Rooms (`III-14`, `III-20`, `III-21`)

- **Track:** `S20e` (`track-s20e-sokoban-coupled-farkas-obstructions`)
- **Oracle Class:** `exact` (pure Python 3 standard library; `int` and `fractions.Fraction` only; `0` floats on trust paths; `0` bare `assert`s; `0` external dependencies; Zone-B fail-closed I/O & public API boundaries)
- **Novelty Classification:** `N1` (new pure-$\mathbb{Z}/\mathbb{Q}$ coupled multi-entity Farkas dual certificates, concrete non-separable deadlock cut-set witnesses, and Law-2b residual gap diagnostics built atop `N0` classical LP duality / cost partitioning and `ahrazzle/soko` catalog baselines)
- **Scope Honesty (`closes_global_frontier_optimality: false`):** Strictly lifts root exact LP lower bounds across **all 3** open *Heroes of Sokoban Part III* Frontier rooms (`III-14`: `21 -> 24`, `III-20`: `3 -> 9`, `III-21`: `21 -> 30`) with exact strong duality (`primal == dual` in $\mathbb{Q}$) and `0` Bellman consistency violations, while explicitly documenting the remaining residual gaps below global search floors (`20`, `68`, `240`).

---

## 1. Executive Results Table (All 3 Open Frontier Rooms)

| Room | Board | Prior 1-Box / 1-Hero Best Root (`soko`) | **Track S20e Coupled Farkas Root (`primal == dual` in $\mathbb{Q}$)** | Strict Gain | Global Search Floor / Known Route | Residual Gap (Floor / Known) | Concrete Edges Checked (`Bellman Violations`) |
|---|---|---:|---:|---:|---:|---:|---:|
| **`III-14`** | `15×7` (`B, D`, `9` switches `}`) | `21` (`h_vault`; `h_dir=11`, `1-hero=10`) | **`24`** (`9 + 1 + 14`) | **`+3`** (`+14.3%`) | `44` / `48` | `20` / `24` | `296` (`0`) |
| **`III-20`** | `15×9` (`F, T, W, P, D`, `12` Goblins, no Bard) | `3` (`soko#53` C2 `ceil(14/5)`) | **`9`** (`1 + 1 + 3 + 4`) | **`+6`** (`3.00×`) | `77` / `84` | `68` / `75` | `284` (`0`) |
| **`III-21`** | `23×13` (all `6` heroes, `6` Goblins, `8` crates) | `21` (`soko#53` C2 `h_OC`) | **`30`** (`1+1+1+2 + 6 + 18 + 1`) | **`+9`** (`+42.9%`) | `270` / `316` | `240` / `286` | `571` (`0`) |

- **Fractional Shared-Action Farkas Witness (`FRAC_SHARED`):** Two coupled quotients sharing action `SHARED` with fractional rational cost partition $(w_1, w_2) = (1/3, 2/3)$ plus private actions `PRIV_1`, `PRIV_2` certify strictly non-integral individual potentials $h_1(s_0) = 5/3$, $h_2(s_0) = 7/3$ with exact zero strong duality gap $5/3 + 7/3 = 4 = \lambda_{\text{SHARED}}(2) + \lambda_{\text{PRIV\_1}}(1) + \lambda_{\text{PRIV\_2}}(1)$.
- **Concrete Non-Separable Deadlock Cut-Set Witnesses (`3/3` Verified):**
  - `III-14` (`III-14_bard_5x5_rigid_2crate_blowoff_deadlock`): `43`-state closed Farkas cut-set ($d^* = +\infty$) under Bard's $5\times 5$ Chebyshev rigid-aura $y_1 = y_2$ coupling vs. **both** 1-crate projections finite (`dist = 8` on `56` states and `dist = 8` on `65` states).
  - `III-20` (`III-20_goblin_ring_no_priest_deadlock`): `5`-state closed Farkas cut-set ($d^* = +\infty$) for Fighter facing `III-20`'s 4-Goblin ring around `G` without Priest vs. 1-entity Goblin-blind projection finite (`dist = 3`, `15` states); coupling Priest `P` restores exact win in **`9` steps** (independently replayed route `ARDARDLAR`).
  - `III-21` (`III-21_wizard_sealed_alcove_deadlock`): `3`-state closed Farkas cut-set ($d^* = +\infty$) for Wizard sealed behind `III-21`'s 2-thick `#` alcove barrier without Druid vs. 1-entity wall-blind projection finite (`dist = 5`, `21` states).
- **Negative Law-2b `must_fail` Control (`III-21_naive_unpartitioned_l1_sum`):** Naive unpartitioned 6-hero $L_1$ sum (`h_0 = 48`) suffers **`22` concrete Bellman violations** on `III-21`'s 316-key route with **`max_1step_drop = 9`** (cleanly falsified).

---

## 2. Exact Coupled Action-Class Farkas Formulation

Given $M$ finite quotient transition graphs $Q_m = (V_m, s_{0,m}, G_m, E_m)$ labeled by disjoint concrete action classes $a \in \mathcal{A}$ and rational cost partition $w_{m,a} \in \mathbb{Q}_{\ge 0}$ satisfying $\sum_{m=1}^M w_{m,a} \le 1$ ($\forall a \in \mathcal{A}$):

- **Primal LP:** $\max \sum_{m=1}^M h_m(s_{0,m})$ subject to $h_m(g) = 0$ ($\forall g \in G_m$) and $h_m(u) - h_m(v) \le w_{m,a}$ ($\forall (u, v, a) \in E_m$).
- **Farkas Dual LP:** $\min \sum_{a \in \mathcal{A}} \lambda_a$ subject to unit $s_{0,m} \to G_m$ flow conservation ($y_{m,e} \ge 0$) in every $Q_m$ and $\sum_{e \in E_m(a)} y_{m,e} \le \lambda_a$ ($\forall m, a$).
- **Global 1-Step Consistency & Strong Duality:** Whenever every $\pi_m$ is a sound quotient homomorphism for each concrete action class $a$, $H(s) = \sum_m h_m(\pi_m(s))$ satisfies $H(s) - H(s') \le \sum_m w_{m,a} \le 1$ globally, and $\lceil H(s) \rceil$ preserves 1-step consistency. Our zero-shared-code verifier (`verify_coupled_farkas_certificate` in `sokoban_farkas_audit.py`) independently checks every primal inequality, cost-partition sum, dual flow conservation equation, dual capacity bound, and exact equality $\sum_m h_m(s_{0,m}) = \sum_a \lambda_a$ in `Fraction` arithmetic.

### Per-Room Coupled Quotient Decompositions (Board-Derived from `FRONTIER_CATALOG`)
1. **`III-14` (`24 = 9 + 1 + 14`):**
   - `Q_1` (`D_W2C`, `9`): Exact perimeter wall-to-crate harvest supply deficit (`9` switches `S_9`, `0` initial non-perimeter weighing objects).
   - `Q_2` (`A_SW`, `1`): Exact active-hero switch parity (`D` cannot push/move crates, so at least 1 `'A'` switch `D -> B` is mandatory while `weighed_nonhero < 9`).
   - `Q_3` (`MOVE_BD`, `14`): Coupled Bard-conservation + 9-switch supply + Druid vault quotient. Because Druid can never move Bard or any `*` crate without petrification, Bard's own displacement satisfies exact conservation $b_R - b_L = g_{B,x} - B_x$ and $b_D - b_U = g_{B,y} - B_y$ while moving 9 distinct supply objects onto $S_9 = \{4,5,6\}\times\{2,3,4\}$, lifting movement steps from `h_dir = 11` to **`14`**.
2. **`III-20` (`9 = 1 + 1 + 3 + 4`):**
   - `Q_1` (`D_W2C_L`, `1`) & `Q_2` (`D_W2C_R`, `1`): Pairwise-disjoint `#`-wall cuts sealing Priest `4@(1,4)` (`C20_L`, `0` goals) and the 4 right-vault goals `(13,1),(13,3),(13,5),(13,7)` (`C20_R`, `0` heroes).
   - `Q_3` (`A_SW`, `3`): Real 6-state cyclic 5-hero post-breach `'A'`-switch automaton (`W(3) -> P(4) -> D(6) -> post`), charging `+1` mandatory switch away from Druid while non-Druid heroes remain off-goal.
   - `Q_4` (`M_OCC_MOVE`, `4`): Moveable+Hero occupancy set $\mathcal{M}(s) \cup B_{20,L} \cup B_{20,R}$ directional frontier to `G20_R`. Because Wizard ray-swaps permute elements within $\mathcal{M}(s)$ without altering occupancy ($\Delta = 0$) and no Bard exists in `III-20`, this bound is **100% Wizard-swap invariant** and triples `soko#53`'s `h_OC = 3`.
3. **`III-21` (`30 = 1 + 1 + 1 + 2 + 6 + 18 + 1`):**
   - `Q_1..Q_4` (`5`): Four **pairwise-disjoint** sealed-component Druid breach cuts (`B21_DRU = 1`, `B21_BARD = 1`, `B21_BG = 1`, 2-thick Wizard alcove `R21_WIZ = 2`), verified pairwise disjoint (`require_pairwise_disjoint`).
   - `Q_5` (`A_SW`, `6`): Real 7-state cyclic 6-hero post-breach switch automaton (`F(1)->T(2)->W(3)->P(4)->B(5)->D(6)->post`).
   - `Q_6` (`DRU_PRE_MAZE` + `D_W2C_OTHER`, `18`): Complete full-board `23×13` concrete pre-release Druid maze quotient (**`569` vertices, `1,709` edges**, `18`-edge tight Farkas dual unit flow) derived directly from `Part3Oracle(III-21)`. While Wizard remains sealed inside `C21_WIZ`, `#` walls block all Wizard warpballs out of `C21_WIZ`, so Druid moves at speed $\le 1$ cell/step through the maze with at most `1` free crossing of `B21_BG`.
   - `Q_7` (`WIZ_POST_GOAL`, `1`): Post-release Wizard goal step (`0` on goal, `1` off goal; constant `1` throughout `wiz_sealed`, hence immune to Bard cross-wall co-movement).

---

## 3. Law-4 Novelty Accounting (`N0` vs `N1`) & Law-2b Residual Gaps

### `N0` Classical & Prior-Art Quarantine
- Farkas' lemma (1902), LP strong duality, shortest-path Bellman potentials, and optimal cost partitioning.
- *Heroes of Sokoban Part III* puzzle specification and catalog boards/routes (`III-14`, `III-20`, `III-21`) in `ahrazzle/soko`.
- Prior root bounds (`III-14`: `max_manhattan=10`, `h_dir=11`, `h_vault=21`; `III-20`: `soko#53` C2 `h_OC = ceil(14/5) = 3`; `III-21`: `soko#53` C2 `h_OC = 21`) and global search floors (`44`, `77`, `270`).

### `N1` New Contributions in Track S20e
- Pure-$\mathbb{Z}/\mathbb{Q}$ action-class cost-partitioned multi-quotient Farkas LP solver and zero-shared-code independent primal/dual verifier (`sokoban_farkas_oracle.py`, `sokoban_farkas_audit.py`).
- Strictly tighter root exact-$\mathbb{Q}$ Farkas lower bounds on all 3 open Frontier rooms (`21 -> 24`, `3 -> 9`, `21 -> 30`), including the full-board `569`-vertex concrete `III-21` pre-release Druid maze Farkas dual and Wizard-swap-invariant `III-20` occupancy frontier.
- Three concrete non-separable multi-entity Farkas deadlock cut-set witnesses grounded directly in `III-14`, `III-20`, and `III-21` (with `9`-step Priest-escort restoration witness `ARDARDLAR`).

### Law-2b Honest Residual Gap Diagnosis
These root coupled Farkas cuts do **not** close global optimality on `III-14`, `III-20`, or `III-21`:
- **`III-14` (`24` vs floor `44` / known `48`, gap `20` / `24`):** `(b_L, b_R, b_U, b_D)` conservation still relaxes multi-crate spatial collision inside Bard's $5\times 5$ aura, omitting the `3` column-6 `* -> #` petrifications, `4` extra `'A'` switches, and `13` repositioning steps in the `48`-key route.
- **`III-20` (`9` vs floor `77` / known `84`, gap `68` / `75`):** The `84`-key route uses `A=23`, `W=26` (`13` ray swaps), `P=14`, `D=10`, `F=6`, `T=5`; capturing the remaining `68` keys requires coupling non-local Wizard 4-cycles with 12-Goblin simultaneous lethality.
- **`III-21` (`30` vs floor `270` / known `316`, gap `240` / `286`):** The `316`-key route uses `A=75`, `F=100`, `B=39` (`36` multi-entity aura moves), `D=37` (`10` `w2c`, `1` `c2w`), `P=29`, `T=27`, `W=9`; closing `30 -> 270` requires simultaneously coupling all `6` heroes, `8` crates, and `6` Goblins across the full `23×13` board.

---

## 4. Verification & Adversarial Hardening Receipts

- **4-Mode `-I` Isolation Parity (`-I -B`, `-I -O -B`, `-I -B -W error`, `PYTHONHASHSEED=42 -I -B`):**
  - `--standalone --json` bit-identical across all 4 modes: `file_sha256 = d3a4fa873b025a88e9091125a20034ad9af37b453365f4c92b398635ee5c7476`, `payload_sha256 = e0d449bec8b6f9c0192ddcfea2e080659ff416f6ff3a6ccf08fda2b87c099aa3`, `canonical_sha256 = 7f4fd01369a0abee649f55f6cafd23bb36f8ac26397842e014beda46bcf07340`.
  - `--check sokoban_farkas_certificate.json` returns `valid: true` across all 4 modes; `test_sokoban_farkas_r5.py` passes **`12/12 OK`** across all 4 modes (`0` warnings, `0` bare `assert`s).
- **Live `aletheia v2.0.0 mutate --max-mutants 0 --work-root . --add-cwd` (`-I -O -B -W error`):**
  - `sokoban_farkas_oracle.py`: **`86/86` (`100.0%`, `survived=0`, `truncated=False`) KILLED** (`0` timeouts).
  - `sokoban_farkas_audit.py`: **`64/64` (`100.0%`, `survived=0`, `truncated=False`) KILLED** (`0` timeouts).
  - **Combined:** **`150/150` (`100.0%`) KILLED**.
- **Exhaustive AST `BoolOp` (`and` $\leftrightarrow$ `or`) Raise-Guard Sweep:**
  - `sokoban_farkas_oracle.py`: **`15/15`** + `sokoban_farkas_audit.py`: **`5/5`** = **`20/20` (`100.0%`, `survived=[]`) KILLED**.
- **Live `Track S19c` Zone-B CLI Fuzzer (`zone_b_fuzzer.py --target-cli`):**
  - **`23/23` (`100.0%`, `bypasses=0`, `crashes=0`, `status: PASS`)**.
- **Zone-B Public-API & I/O Hardening:** Exact `type()` enforcement (`bool`, `int`/`str`/`Fraction`/`Path` subclasses rejected), `MAX_INT_BITS = 2048` / `MAX_INT_DIGITS = 616` (zero untrusted-int stringification), strict canonical rational strings (rejecting `"007"`, `"-0"`, `"2/4"`, `"3/1"`), iterative `MAX_JSON_DEPTH = 64` (blocking `1,500`-deep & cyclic structures), unpaired UTF-16 surrogate & non-ASCII hex rejection before `hmac.compare_digest`, unnormalized raw-component + `PWD` symlink refusal, non-blocking `stat.S_ISREG` guard on both `--check` and `--write` (zero FIFO hang), and `audit-check --strict-ancestors --safety-scan PASS`.
