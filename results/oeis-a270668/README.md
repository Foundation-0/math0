# Mathar's generating function for column 3 of A270668 (domino tilings of (4k+1)x5 boards with central hole)

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A270668  
**Date:** 2026-10-25

## Result

Let c_k = T(2k, 2) be the number of domino tilings of the (4k+1) x 5 board with its central cell removed (c_0 = 1 for the 1 x 5 strip with its middle cell removed). Then, in Q[[x]],
  sum_{k>=0} c_k x^k = (-1 - 4x + 543x^2 - 6238x^3 + 17032x^4 - 6238x^5 + 543x^6 - 4x^7 - x^8) / ((x-1)(x^2-7x+1)(x^2-23x+1)(x^4-161x^3+576x^2-161x+1)).
This is R. J. Mathar's 2016 conjectured g.f. for "column 3" of OEIS A270668. Equivalently, (sum c_k x^k) * den = num.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A270668](https://oeis.org/A270668) as [`Math0.Statements.A270668.statement`](../../lean/Math0/Statements/OEIS/A270668.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A270668.lean`](../../lean/Math0/Frontier/OEIS/A270668.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A270668 Conjectured g.f. for column 3: ( -1 -4*x +543*x^2 -6238*x^3 +17032*x^4 -6238*x^5 +543*x^6 -4*x^7 -x^8 ) / ( (x-1) *(x^2-7*x+1) *(x^2-23*x+1) *(x^4 -161*x^3 +576*x^2 -161*x +1) ). - _R. J. Mathar_, Mar 23 2016

Referees: R. J. Mathar, "A270668: Domino tilings with one monomer in the center", PDF linked from OEIS A270668 (https://oeis.org/A270668/a270668.pdf), dated Apr 13 2016. It counts the 5 x (2m+1) floor with a central monomer by the transfer-matrix method: 50 states, nine centre configurations, and left/right Hadamard products of rational g.f.s in x = z^5. It appears to derive the column-3 g.f. that Mathar had conjectured on Mar 23 2016 in OEIS A270668 (still labelled "Conjectured" there). I saw its content only through search-engine extracts; the full PDF could not be downloaded. Related but not resolving: OEIS A143659 / M. Ciucu arXiv:0710.4500 (diagonal); A189003/A189006 (5xn corner-removed, same characteristic polynomial t^4-15t^3+32t^2-15t+1); A003775, A006238; B. E. Tenner, EJC 11(2) R17 (2005); Byun-Goddard arXiv:2502.05918; Stanley EC1 section 4.2.5 (Hadamard products of rational series). No prior Lean or other formalization found.

## Citation

```bibtex
@misc{math0:oeis-a270668,
  author       = {{math0}},
  title        = {{Mathar's generating function for column 3 of A270668 (domino tilings of (4k+1)x5 boards with central hole)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a270668}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
