# Alexandersson's recurrence for the row polynomials of A395454 holds (rows counted from 1)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A395454  
**Date:** 2026-10-24

## Result

Let E2(j,i) be the second-order Eulerian numbers (A201637): E2(0,0)=1, E2(0,i)=0 for i>=1, and E2(j+1,i) = (2j+1-i)E2(j,i-1) + (i+1)E2(j,i). Let T(n,k) = sum_{j=0}^n (-1)^{n-j} C(n,j) E2(j,n-k), the triangle A395454, and let P_m(t) = sum_{k=0}^m T(m,k) t^k be its row polynomials in the entry's numbering (P_0 = 1, P_1 = 0, P_2 = 2t, ...). Then for every m >= 2, in Z[t],
P_m = (m-1)(1+t) P_{m-1} + (t - t^2) P'_{m-1} + 2(m-1) t P_{m-2}.
Equivalently, with the rows counted from 1 (P1(n) = P_{n-1}), for every n >= 3: P1(n) = (n - 2t + nt - 2) P1(n-1) + (t - t^2) P1'(n-1) + t(2n-4) P1(n-2). This is Alexandersson's conjecture in the form fixed by the frozen statement.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A395454](https://oeis.org/A395454) as [`Math0.Statements.A395454.statement`](../../lean/Math0/Statements/OEIS/A395454.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A395454.lean`](../../lean/Math0/Frontier/OEIS/A395454.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A395454 Conjecture: Let P(n) be the generating polynomial (in t) of row n. Then P(n) = (n - 2*t + n*t - 2)*P(n-1) + (t - t^2)*P'(n-1) + t*(2*n-4)*P(n-2). - Per W. Alexandersson, Jun 27 2026

Referees: No earlier resolution found. Closest related work:
- S.-M. Ma and Y.-N. Yeh, "Eulerian polynomials, Stirling permutations of the second kind and perfect matchings," Electron. J. Combin. 24(4) (2017) #P4.27, arXiv:1607.01311. Its Thm 17 is an analogous recurrence for Stirling-derangement polynomials by cycle ascent plateaus (a different family). Its Cor 18 is the A053871 row-sum recurrence. Its Prop 9 implies that A395454 row n is the distribution of n - casc over Stirling derangements.
- G.-H. Duh, Y.-C. R. Lin, S.-M. Ma and Y.-N. Yeh, arXiv:1612.07391 (2016).
- S.-M. Ma, S. Kitaev, J. Yeh and Y.-N. Yeh, arXiv:2601.20665 (2026).
- S. Fried, "Further proofs of conjectures from the OEIS," arXiv:2607.24832 (2026). Does not cover A395454.

OEIS A395454 (#30, Oct 14 2026; Luschny's entry, Alexandersson's conjecture of Jun 27 2026) still lists the formula as a conjecture, with no proof recorded in any comment, %E line or link. Read with the entry's offset-0 numbering the formula is false; read with rows counted from 1 it holds.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a395454,
  author       = {{math0}},
  title        = {{Alexandersson's recurrence for the row polynomials of A395454 holds (rows counted from 1)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a395454}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
