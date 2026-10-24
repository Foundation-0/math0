# Divisors of the terms of row n of A176206 are the parts of the partitions of n

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A176206  
**Date:** 2026-10-24

## Result

Row n of A176206 lists n - k repeated p(k) times for k = 0, ..., n-1, where p is the partition function. Pol's conjecture says that for every n >= 1, the multiset of all divisors of all terms of row n equals the multiset of all parts of all partitions of n. Divisors and parts are counted with multiplicity: each term t of the row contributes each divisor of t once, and each partition contributes all of its parts.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A176206](https://oeis.org/A176206) as [`Math0.Statements.A176206.statement`](../../lean/Math0/Statements/OEIS/A176206.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A176206.lean`](../../lean/Math0/Frontier/OEIS/A176206.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C Conjecture: all divisors of all terms in row n are also all parts of all partitions of n. (Omar E. Pol, Nov 2020)

Referees: OEIS A066633 (number of k's in all partitions of n): g.f. x^k/(1-x^k)*Prod 1/(1-x^m) by V. Jovovic (Jan 2002); T(n,k) = Sum_{j<n, j==n mod k} P(j) by J. L. Arregui (Apr 2002); T(n+k,k) = T(n,k) + A000041(n), proved in M. Ghosh Dastidar and S. Sen Gupta, "Generalization of a few results in Integer Partitions", arXiv:1111.0094, Lemma 1. A related classical bijection appears in arXiv:1610.01863 ("On Stanley's theorem and its generalizations") and arXiv:1007.3459. M. Merca, "A note on a classical connection between partitions and divisors" (aos.ro), also counts the k's in all partitions of n. OEIS A338156 states the A176206 divisor/partition correspondence as fact. Sources: https://oeis.org/A066633 (read from local mirror), https://arxiv.org/abs/1111.0094, https://arxiv.org/pdf/1610.01863, https://arxiv.org/pdf/1007.3459, https://aos.ro/?p=14363

## Citation

```bibtex
@misc{math0:oeis-a176206,
  author       = {{math0}},
  title        = {{Divisors of the terms of row n of A176206 are the parts of the partitions of n}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a176206}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
