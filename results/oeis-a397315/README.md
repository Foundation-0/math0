# A397315: a 14-point blackout of the 5 x 8 grid refutes T(n,m) = n + m

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Discrete geometry  
**Source problem:** OEIS A397315  
**Date:** 2026-10-18

## Result

Pemmasani's conjecture in OEIS A397315 says this. Let T(n,k) be the largest number of points that can be blacked out of the grid {0..k-1} x {0..n-1} so that every lattice rectangle (tilted rectangles included) is still determined by its set of visible vertices. Then T(n,m) = n + m whenever min(n,m) >= 4, except T(4,4) = 7 and T(4,5) = T(5,4) = 8. We prove the negation. The 5 x 8 grid (n = 5, k = 8) has a valid blackout of 14 points, so T(5,8) >= 14, which is more than the predicted 5 + 8 = 13.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A397315](https://oeis.org/A397315) as [`Math0.Statements.A397315.statement`](../../lean/Math0/Statements/OEIS/A397315.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A397315.lean`](../../lean/Math0/Frontier/OEIS/A397315.lean) refutes (proves the negation of) it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: T(n,m) = n+m whenever min(n,m) >= 4, except T(4,4) = 7 and T(4,5) = 8 (verified on seven cells through 6 X 6)." (entry by _Arjun Pemmasani_, Sep 02 2026; comment in the entry, which was last revised Sep 12 2026)

Referees: The refutation is in Arjun Pemmasani's GitHub repository "Kagey-Problems" (https://github.com/apemm/Kagey-Problems), which the OEIS entry A397315 links in its %H line. These are the files that record it:
- kagey-problems/problem001/data/ledger.md, "Outcomes, part 2 (2026-10-17)", commit 45b175b, 2026-10-17: blackout(5,8) = 14 and blackout(6,8) = 15. The 5 x 8 maximum blackouts form one orbit of 4.
- The JIS paper draft kagey-problems/problem001/jis/pemmasani.tex, file sections/sec07_five.tex. Its Theorem "the guess fails" states f(5,8) = 14 and f(6,8) = 15. Theorem "five rows" states f(5,m) = m+6 for every m >= 8.
- The Lean proof kagey-problems/lean/KageyProblems/Problem001/Kernel.lean, theorem kfvalue_5_8 (f(5,8) = 14, kernel-checked), commit 8df4162, 2026-10-18. CollarBoards.lean has fval_five: f(5,m) = m+6 for m >= 8.
- kagey-problems/problem001/README.md says: "The guess f = h+m for both sides at least 4 fails at 5 x 8 and 6 x 8."

The source problem is Peter Kagey's Open Problem Collection, Problem 001 (https://peterkagey.com/problems/001/); his page lists no values. The companion entry A399580 has nothing on 5 x 8. Neither OEIS entry, in the local mirror or on GitHub (#38 and #24), has been updated with the refutation yet.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a397315,
  author       = {{math0}},
  title        = {{A397315: a 14-point blackout of the 5 x 8 grid refutes T(n,m) = n + m}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a397315}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
