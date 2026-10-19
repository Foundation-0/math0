# A115026 has a term greater than 370: a(119) = 371

**Classification:** First formal proof of a known result  
**Area:** Sequences and series  
**Source problem:** OEIS A115026  
**Date:** 2026-10-18

## Result

Let F(m) be the sum of d^L over the decimal digits d of m, where L is the number of digits of m (A101337). For n >= 1, a(n) is the smallest element of the cycle that the orbit n, F(n), F(F(n)), ... eventually enters (A115026). Harvey P. Dale conjectured that a(n) <= 370 for all n >= 1. This is false: a(119) = 371.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A115026](https://oeis.org/A115026) as [`Math0.Statements.A115026.statement`](../../lean/Math0/Statements/OEIS/A115026.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A115026.lean`](../../lean/Math0/Frontier/OEIS/A115026.lean) refutes (proves the negation of) it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: no term is greater than 370. - _Harvey P. Dale_, Jun 08 2022"

Referees: OEIS A151543, "Smallest precursor of n-th cycle in the 'Recurring Digital Invariant Variant' problem" (N. J. A. Sloane, May 15 2009, based on an email from Eric Angelini, Feb 18 2009, with a cycle table by Hans Havermann). Its table entry "13 { 119, 1, {371}}" names 119 as the smallest number whose orbit under A101337 ends in the fixed point 371, so a(119) = 371. The same table has "19 { 407, 1, {407}}" and other cycles with minima above 370. Related pre-2022 OEIS entries: A151544 (2009) lists the cycle elements, including 371 and 407. A157714 (Havermann, Mar 2009) lists numbers in cycles of period greater than 1, such as 2929 and 18829. A005188 lists the narcissistic numbers 153, 370, 371, 407, 1634, ...; since 371 is a fixed point, a(371) = 371 > 370 trivially. Angelini's page "A Recurring Digital Invariant Variant" is at cetteadressecomportecinquantesignes.com/RecurDigit.htm, with a cached copy at oeis.org/A151543/a151543.pdf. The A115026 entry itself (revision #12, Jun 08 2022, unchanged upstream) still states the conjecture and has no correction or %E extension. Web searches found no explicit published retraction of Dale's comment. Sources: https://oeis.org/A115026, https://oeis.org/A151543, https://en.wikipedia.org/wiki/Narcissistic_number

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a115026,
  author       = {{math0}},
  title        = {{A115026 has a term greater than 370: a(119) = 371}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a115026}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
