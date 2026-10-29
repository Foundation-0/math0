# Layman's floor formula for collinear triples in a 3 × n grid (A057566), as printed until its October 2026 correction, fails at n = 24

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A057566  
**Date:** 2026-10-21

## Result

Let a(n) be the number of 3-element collinear subsets of the 3 × n grid {0,1,2} × {0,...,n-1}. Layman's conjecture (OEIS A057566, Oct 2000), as printed in the entry until 21 Oct 2026, says that for every n ≥ 3, a(n) = 5*floor((2n^3 - 3n^2 - n)/24) + floor((2(n-1)^3 - 3(n-1)^2 - (n-1))/24) + n. The frozen statement is this conjecture for all n ≥ 3. We prove it is false: the identity fails at n = 24. On 21 Oct 2026, after this statement was frozen, OEIS corrected the formula to a(n) = 5*floor((2n^3 - 3n^2 - 2n + 3)/24) + floor((2(n-1)^3 - 3(n-1)^2 - 2(n-1) + 3)/24) + n. This result concerns only the formula as printed before that correction; the corrected formula is not refuted, and it agrees with a brute-force count for n <= 60 and with the proved closed form 3*C(n,3) + n + 2*floor((n-1)^2/4) for n <= 20000.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A057566](https://oeis.org/A057566) as [`Math0.Statements.A057566.statement`](../../lean/Math0/Statements/OEIS/A057566.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A057566.lean`](../../lean/Math0/Frontier/OEIS/A057566.lean) refutes (proves the negation of) it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Correction (noted 26 Oct 2026): OEIS A057566 now reads "Conjecture: a(n) = 5*floor((2n^3 - 3n^2 - 2n + 3)/24) + floor((2(n-1)^3 - 3(n-1)^2 - 2(n-1) + 3)/24) + n, which fits all of the listed terms. [Corrected by Alper Ferudun, Oct 21 2026]" (oeisdata, checked 26 Oct 2026). The statement here was frozen from the earlier text, quoted below, which is what the Lean file refutes. Reported in review of math0 PR #1.

Conjecture as stated in OEIS: %F A057566 Conjecture: a(n) = 5*floor((2n^3 - 3n^2 - n)/24) + floor((2(n-1)^3 - 3(n-1)^2 - (n-1))/24) + n, which fits all of the listed terms. (John W. Layman, author of the entry, Oct 04 2000)

Referees: There is no explicit published refutation, but OEIS already contains everything needed:
- A057566 data lists a(24) = 6360. Layman's formula gives 6365 there. Paolo Xausa's b-file (2024) covers n = 0..10000.
- A057566 %F, R. J. Mathar, May 23 2010: a(n) = n^3/2 - n^2 + n + (1-(-1)^n)/4, with recurrence signature (3,-2,-2,3,-1) and g.f. x(1-x+4x^2+2x^3)/((1+x)(x-1)^4).
- A262402, proof by N. J. A. Sloane, Dec 16 2017, following Jared Nash's formula and his linked PDF "Formula for number of triangles in a 3 X n grid". It proves the number of collinear triples with one point per row in a 3 x n grid is n + 2*floor((n-1)^2/4). Hence a(n) = 3*C(n,3) + n + 2*floor((n-1)^2/4).
- A334704 (N. J. A. Sloane and Tom Duff, 2020) tabulates collinear-triple counts for n x k grids up to 50 x 50; row 3 is A057566.
- I searched the web (arXiv including 2609.25133, general search) and found no explicit statement that Layman's floor conjecture fails.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a057566,
  author       = {{math0}},
  title        = {{Layman's floor formula for collinear triples in a 3 × n grid (A057566), as printed until its October 2026 correction, fails at n = 24}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a057566}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
