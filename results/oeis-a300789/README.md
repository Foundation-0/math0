# Domino-tileable Young diagrams are exactly the colour-balanced ones (A300789)

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A300789  
**Date:** 2026-10-18

## Result

For every integer partition y = (y_1 >= y_2 >= ... >= y_m), the Young diagram of y can be tiled by dominoes if and only if the number of odd parts in even positions equals the number of odd parts in odd positions. So the Heinz numbers of domino-tileable partitions (A300789) are exactly the Heinz numbers of partitions whose odd parts appear as often in even as in odd positions. Equivalently, a(n) = b(n) for all n >= 1, where a(n) and b(n) are the n-th smallest Heinz numbers of the two classes.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A300789](https://oeis.org/A300789) as [`Math0.Statements.A300789.statement`](../../lean/Math0/Statements/OEIS/A300789.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A300789.lean`](../../lean/Math0/Frontier/OEIS/A300789.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C A300789 This sequence is conjectured to be the Heinz numbers of integer partitions in which the odd parts appear as many times in even as in odd positions.  (_Gus Wiseman_, Mar 12 2018)

Referees: Already known, so the Lean proof is a first formalization, not a new result:
- Classical 2-core / beta-number theory. I.G. Macdonald, Symmetric Functions and Hall Polynomials (2nd ed. 1995), Ch. I §1 Ex. 8, pp. 12-15: the r-core is empty iff the beta-numbers are equidistributed mod r. D.E. Littlewood, Modular representations of symmetric groups, Proc. Roy. Soc. A 209 (1951) 333-353.
- Explicit statement of the parity form. S.P. Albion, "Proof of some Littlewood identities conjectured by Lee, Rains and Warnaar", arXiv:2108.12766, Lemma 2.1: empty 2-core (i.e. domino-tileable) iff {lambda_i + 2n - i} has n even and n odd elements, which is equivalent to the A300789 parity condition.
- Black = white criterion for Young diagrams. Codeforces Round 609 editorial, problem 1268B/1269D "Domino for Young" (Dec 2019, codeforces.com/blog/entry/72358).
- OEIS. A304710 (A. P. Heinz, May 2018) states the equivalence as fact: "number of partitions of 2n where the number of odd parts in even positions differs from the number of odd parts in odd positions". A000712 has Meeussen's 2013 comment and Karlsson's Dec 2025 comment. Heinz's Maple program and b-file for A300789 use the criterion.
- The A300789 entry itself (rev #11, May 22 2018, local mirror = GitHub) still says "conjectured" and has no %E updates.

## Citation

```bibtex
@misc{math0:oeis-a300789,
  author       = {{math0}},
  title        = {{Domino-tileable Young diagrams are exactly the colour-balanced ones (A300789)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a300789}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
