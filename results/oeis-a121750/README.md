# Mathar's order-6 recurrence for A121750 (even-length columns in deco polyominoes) holds for all n >= 7

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A121750  
**Date:** 2026-10-24

## Result

Let a(n) be the total number of columns of even length over all deco polyominoes of height n (OEIS A121750). The polyominoes are encoded as column lists, as in the statement file. Then for every n >= 7:
a(n) - (n+2)a(n-1) + (-n^2+4n-2)a(n-2) + (n^3-3n^2-4n+11)a(n-3) - (n-1)(n^2-11n+26)a(n-4) + (-n^3+5n^2+7n-43)a(n-5) + (n-3)(n-5)^2 a(n-6) = 0.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A121750](https://oeis.org/A121750) as [`Math0.Statements.A121750.statement`](../../lean/Math0/Statements/OEIS/A121750.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A121750.lean`](../../lean/Math0/Frontier/OEIS/A121750.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F Conjecture D-finite with recurrence a(n) +(-n-2)*a(n-1) +(-n^2+4*n-2)*a(n-2) +(n^3-3*n^2-4*n+11)*a(n-3) -(n-1)*(n^2-11*n+26)*a(n-4) +(-n^3+5*n^2+7*n-43)*a(n-5) +(n-3)*(n-5)^2*a(n-6)=0. - R. J. Mathar, Jul 26 2022

Referees: I found no published proof of this recurrence. Sources checked:
- OEIS A121750, local mirror and upstream raw oeisdata (revision #13, 2024-08-20, still says 'Conjecture'). Cross-references A121748, A121747, A121749, A121751 also contain no proof.
- E. Barcucci, S. Brunetti, F. Del Ristoro, 'Succession rules and deco polyominoes', RAIRO ITA 34 (2000) 1-14. Full text read; it does not treat even-length columns.
- E. Barcucci, A. Del Lungo, R. Pinzani, TCS 159 (1996) 29-42.
- E. Deutsch, E. Pergola, R. Pinzani, 'Six bijections between deco polyominoes and permutations', arXiv:0810.2876. It gives the definition of directed height and has no even-column results.
- S. B. Ekhad, X. Yang, D. Zeilberger, arXiv:1707.04654. It predates the 2022 conjecture.
- S. Fried, arXiv:2410.07237; JIS 28 (2025) Art. 25.4.3; JIS vol. 29 fried21; arXiv:2607.24832. None covers A121750.
- T. Niu, arXiv:2605.15500, 2605.04369, 2605.08444, 2605.16553 (2026). None covers A121750.
- M. Kauers, C. Koutschan, arXiv:2303.02793. Does not cover A121750.

Note: the order-6 recurrence would follow routinely from Deutsch's first-order recurrence in the same entry (holonomic closure). That recurrence is stated in the entry without proof.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a121750,
  author       = {{math0}},
  title        = {{Mathar's order-6 recurrence for A121750 (even-length columns in deco polyominoes) holds for all n >= 7}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a121750}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
