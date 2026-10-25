# Row lengths of the Schreier-set triangle A373345 are A007895 (number of Zeckendorf summands)

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A373345  
**Date:** 2026-10-25

## Result

Let A371176 be the increasing sequence of positive integers k whose binary weight (number of ones) is at most the ruler function v2(2k), i.e. at most one more than the index of the lowest set bit. Equivalently, these are the encodings sum 2^(s-1) of the finite Schreier sets S, meaning nonempty sets of positive integers with |S| <= min S. Row n of A373345 is the Schreier set encoded by A371176(n). Claim: for every n >= 1, row n has exactly as many elements as the Zeckendorf representation of n has terms. In the formal statement, (T n).length = (Nat.zeckendorf n).length.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A373345](https://oeis.org/A373345) as [`Math0.Statements.A373345.statement`](../../lean/Math0/Statements/OEIS/A373345.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A373345.lean`](../../lean/Math0/Frontier/OEIS/A373345.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %Y A373345 Cf. A007895 (conjectured row lengths) ... (Paolo Xausa, Jun 01 2024). Likewise %Y A373557 Cf. ... A007895 (conjectured row lengths) (Paolo Xausa, Jun 09 2024).

Referees: OEIS A371176 (Mikhail Kurkov, 2024): the formula a(n) = b(n)*A001316(b(n))/2 with b(n) = A048679(n), and the recursion a(n) = 2^(A072649(n)-1) + [c(n)>0]*2*a(c(n)), were present by Apr 20 2024 (oeisdata commit 6ea59dd), before the A373345 conjecture of Jun 1 2024. Both were stated without proof and imply popcount(A371176(n)) = A007895(n). Kurkov's comment of Oct 21 2024 states the explicit Zeckendorf-rewriting description of A371176(n).
H. V. Chu, "The Fibonacci Sequence and Schreier-Zeckendorf Sets", J. Integer Sequences 22 (2019), Art. 19.6.5 (arXiv:1906.10962), Theorem 3: a cardinality-preserving bijection between Schreier sets and Zeckendorf sets, which also preserves colex/binary order.
GitHub issue https://github.com/the-omega-institute/trureturing/issues/9050 ("Research: full Schreier-Zeckendorf row-length identity (OEIS A373345)", Sep 20 2026): an informal paper proof of exactly this identity, with no Lean formalization.
Background only: A. Bird, "Jozef Schreier, Schreier sets and the Fibonacci sequence", Out Of The Norm blog, 2012, gives the binary ordering and the R/S block recursion but does not mention Zeckendorf. H. V. Chu, arXiv:2606.21865 (2026), is a survey and does not state the identity.
No prior Lean formalization found.

## Citation

```bibtex
@misc{math0:oeis-a373345,
  author       = {{math0}},
  title        = {{Row lengths of the Schreier-set triangle A373345 are A007895 (number of Zeckendorf summands)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a373345}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
