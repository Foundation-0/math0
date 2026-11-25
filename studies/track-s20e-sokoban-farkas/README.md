# Track S20e: Coupled Multi-Entity Farkas Dual Cuts & Deadlock Obstructions on Open Sokoban Frontier Rooms (`III-14`, `III-20`, `III-21`)

Self-contained pure-$\mathbb{Z}/\mathbb{Q}$ (`int` + `fractions.Fraction`, zero IEEE-754 floats, zero bare `assert`s, zero external dependencies) coupled action-class Farkas LP certifier and zero-shared-code primal/dual verifier for all three open *Heroes of Sokoban Part III* Frontier rooms:

- **Strict Exact-$\mathbb{Q}$ Root Lower-Bound Lifts (`primal == dual` in $\mathbb{Q}$, `0` Bellman violations):**
  - **`III-14` (`15×7`):** `21 -> 24` (`+3`, `+14.3%`; `9 + 1 + 14`; `296` concrete edges checked, `0` violations; residual gap `20` vs floor `44`).
  - **`III-20` (`15×9`):** `3 -> 9` (`+6`, `3.00×`; `1 + 1 + 3 + 4`, Wizard-swap-invariant occupancy frontier; `284` concrete edges checked, `0` violations; residual gap `68` vs floor `77`).
  - **`III-21` (`23×13`):** `21 -> 30` (`+9`, `+42.9%`; `1 + 1 + 1 + 2 + 6 + 18 + 1`, including full-board `569`-vertex / `1,709`-edge concrete pre-release Druid maze Farkas dual; `571` concrete edges checked, `0` violations; residual gap `240` vs floor `270`).
- **Fractional Cost-Partition Strong Duality Witness (`FRAC_SHARED`):** Strictly non-integral potentials $h_1 = 5/3$, $h_2 = 7/3$ under $(w_1, w_2) = (1/3, 2/3)$ with exact strong duality $5/3 + 7/3 = 4$.
- **Concrete Non-Separable Multi-Entity Deadlock Cut-Set Witnesses (`3/3`):** `III-14` (`43`-state Bard rigid-aura blow-off vs finite `dist = 8` 1-crate projections), `III-20` (`5`-state Goblin-ring deadlock without Priest vs `9`-step Priest-escort win `ARDARDLAR`), and `III-21` (`3`-state Wizard sealed-alcove deadlock without Druid), plus negative `must_fail` control (`III-21_naive_unpartitioned_l1_sum`: `22` Bellman violations, `max_1step_drop = 9`).
- **Honest Scope (`N1`, `closes_global_frontier_optimality: false`):** Does not claim global optimality closure; residual gaps below global search floors (`20`, `68`, `240`) are explicitly quantified.

## Quick Verification

```bash
cd studies/track-s20e-sokoban-farkas

# 1. Zero-skip R5 test suite across all three isolated R4 modes
python3 -I -B test_sokoban_farkas_r5.py
python3 -I -O -B test_sokoban_farkas_r5.py
python3 -I -B -W error test_sokoban_farkas_r5.py

# 2. Independent fail-closed certificate verification & standalone replay
python3 -I -B sokoban_farkas_audit.py --check sokoban_farkas_certificate.json --json
python3 -I -B sokoban_farkas_audit.py --standalone --json | cmp -s - sokoban_farkas_certificate.json
```

See [`SOKOBAN_FARKAS_AUDIT_REPORT.md`](SOKOBAN_FARKAS_AUDIT_REPORT.md) for the complete mathematical formulation, per-room quotient decompositions, and hardening receipts (`150/150` AST mutation kills, `20/20` `BoolOp` kills, `23/23` CLI fuzz cases).
