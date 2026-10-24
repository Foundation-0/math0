# A211343: positive entries are smallest parts of consecutive-part partitions; last positive column is A109814(n)

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A211343  
**Date:** 2026-10-24

## Result

Let T(n,k) be the triangle in which column k (k >= 1) begins in row k(k+1)/2 and lists 1, 0^(k-1), 2, 0^(k-1), 3, ... going down. In other words, for 1 <= k and k(k+1)/2 <= n we have T(n,k) = j/k + 1 when k divides j = n - k(k+1)/2, and T(n,k) = 0 otherwise. Two claims are made. (1) For n >= 1 and any entry (n,k) of the triangle with T(n,k) > 0, n has a partition into k consecutive parts m, m+1, ..., m+k-1, and T(n,k) is the smallest part of every such partition. (2) For n >= 1, A109814(n), the largest k such that n is a sum of k consecutive positive integers, is the largest column k of row n with T(n,k) > 0.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A211343](https://oeis.org/A211343) as [`Math0.Statements.A211343.statement`](../../lean/Math0/Statements/OEIS/A211343.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A211343.lean`](../../lean/Math0/Frontier/OEIS/A211343.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C Conjecture 1: T(n,k) is the smallest part of the partition of n into k consecutive parts, if T(n,k) > 0. %C Conjecture 2: the last positive integer in the row n is in the column A109814(n). (Omar E. Pol, Apr 30 2017)

Referees: OEIS (local mirror): A261699 comment by Peter Munn, Jul 30 2017 ("A211343(n,k) = abs(n/d - d/2) + 1/2, smallest part"; one-to-one link between odd divisors and partitions into k consecutive parts). A286013 comment by Peter Munn, Jun 18 2017 (trapezoid proof of the largest-part companion conjecture, which carries over directly to smallest parts). A285898 comment by David A. Corneth, Apr 28 2017 (n has a partition into k consecutive parts iff (n - C(k,2))/k is a positive integer). A196020 formula by Max Alekseyev, Nov 18 2013 (T(n,k) = 2n/k - k on the support), combined with the A211343 formula T = floor((1+A196020)/2). A237048 property by Hartmut F. W. Hoft, Oct 2014. A286000 "Theorem" (Pol). A379632 (Pol, Dec 2024: "Positive terms of A211343", "Right border gives A118235"). A118235 (smallest part of partitions into consecutive parts). A109814 (Jaap Spies / David W. Wilson: 2n = k(2m+k-1)). The classical background is Sylvester's enumeration of partitions into consecutive parts. Not retrievable (web.archive.org unreachable): Joerg Arndt, SeqFan, Jun 3 2017, proof of the A285914/A204217 conjectures. Web searches found no counterexample and no paper on A211343 specifically.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a211343,
  author       = {{math0}},
  title        = {{A211343: positive entries are smallest parts of consecutive-part partitions; last positive column is A109814(n)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a211343}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
