# A363609: a(k^3) = 6k(k+2), the cube is the optimal polycube of k^3 dice

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A363609  
**Date:** 2026-10-19

## Result

Each standard die has opposite faces summing to 7, all dice have the same chirality, and each die may take any of its 24 rotations. Build a face-connected polycube from n dice. A face is visible when the neighbouring cell is empty; faces underneath and faces facing an internal cavity also count. a(n) is the least possible number of visible pips. Claim: for every k > 1, a(k^3) = 6(k+2)k.

## Assessment

The value 6k(k+2) splits as surface area 6k^2 plus 12k. That second term counts the pairs of perpendicular exposed faces on the cube. The proof matches this split. First it checks a finite inequality for one die: the pips shown are at least the number of exposed faces plus the number of exposed perpendicular pairs. Then it bounds the faces by projections and Loomis-Whitney, as in the known surface-area result (A193416). It bounds the perpendicular pairs by taking an extreme cell in each slice, then uses |P| <= l1*l2*l3 and AM-GM. The edge term is a neat observation, but it is a direct analogue of the standard projection argument. The whole proof fits in about a page and uses only standard tools, so a competent mathematician working on the problem would likely find it quickly.

*Follows from:* Discrete Loomis-Whitney inequality (Loomis and Whitney 1949), the standard projection bound behind A193416's a(n^3)=6n^2, and AM-GM, together with a 64-case finite check per die

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A363609](https://oeis.org/A363609) as [`def statement`](../../lean/Math0/Statements/OEIS/A363609.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A363609.lean`](../../lean/Math0/Frontier/OEIS/A363609.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A363609 Conjecture: a(k^3) = 6*(k+2)*k for k > 1.  (Unattributed formula line. Entry by _Matt Donahoe_, Jun 11 2023; last edit #45, Sep 03 2023.)

Referees: I found no prior resolution.
- OEIS A363609, by Matt Donahoe, Jun 11 2023 (revision #45, Sep 03 2023): the local mirror is identical to oeis/oeisdata main on GitHub, and it still states the formula as "Conjecture: a(k^3) = 6*(k+2)*k for k > 1".
- Michael S. Branicky's formulas in the same entry, Jun 11 and Jun 15 2023: these give only upper bounds and loose bounds.
- Donahoe's program, https://github.com/mdonahoe/oeis/blob/main/A363609/dice.py, with its out.txt: a heuristic search over box-plus-slab layouts, with no optimality proof.
- OEIS A193416, minimum surface area of polycubes: the unweighted analogue, a(n^3) = 6n^2.
- AMC 10A 2002 Problem 18 (https://artofproblemsolving.com/wiki/index.php/2002_AMC_10A_Problems/Problem_18): computes the minimum for the 3x3x3 cube alone, 90. It does not show that the cube is optimal among all polycubes.
- Loomis and Whitney, Bull. AMS 55 (1949) 961-962: the classical inequality behind the projection step.
- Searches of arXiv, MathOverflow, Math StackExchange, Puzzling and SeqFan turned up no proof and no counterexample.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a363609,
  author       = {{math0}},
  title        = {{A363609: a(k^3) = 6k(k+2), the cube is the optimal polycube of k^3 dice}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a363609}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
