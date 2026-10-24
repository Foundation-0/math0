# The inverse of the 1/Catalan band triangle (A127767) has integer entries

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A127767  
**Date:** 2026-10-24

## Result

Let C(n) be the Catalan numbers. Let A be the infinite lower-triangular matrix with A(n,k) = 1/C(n) if k ≤ n ≤ 2k and A(n,k) = 0 otherwise. Let T be its inverse, which is also lower triangular. Then every entry T(n,k) with 0 ≤ k ≤ n is an integer. In the frozen statement, T is defined by forward substitution: T(n,k) = C(n)·([n=k] − Σ_{j<n} A(n,j)·T(j,k)) for k ≤ n, and T(n,k) = 0 for k > n.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A127767](https://oeis.org/A127767) as [`Math0.Statements.A127767.statement`](../../lean/Math0/Statements/OEIS/A127767.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A127767.lean`](../../lean/Math0/Frontier/OEIS/A127767.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C It is conjectured that all elements of the triangle are integers. (Paul Barry, Jan 28 2007)

Referees: - OEIS A127767 (P. Barry, Jan 28 2007). Local mirror and current GitHub oeisdata, #11 Sep 30 2018: the conjecture is still marked as conjectured, with no proof or formula. Cross-references: A127768, A127769, A127770, A000108.
- OEIS A101688: the 0/1 triangle [k<=n<=2k].
- OEIS A111967: inverse of A101688. It is an integer triangle because A101688 is unitriangular. T(n,k) = A000108(k)·A111967(n,k) is the identity that settles A127767.
- OEIS A127749, R. J. Mathar, Apr 21 2021: T(n,k) = (2k+1)·A111967(n,k). This is the same factorisation applied to a sibling triangle. It is the closest prior use of the method, but it does not resolve A127767.
- OEIS A127793: the integrality conjecture for the 1/floor((n+2)/2) sibling was proved by FUNG Cheok Yin (Sep 2022) and by S. Fried, "On the inverse of a certain triangular matrix and its connection to the largest odd divisor", Notes Num. Theor. Disc. Math. 32(2) (2026) 255-262, doi:10.7546/nntdm.2026.32.2.255-262 (https://nntdm.net/papers/nntdm-32/NNTDM-32-2-255-262.pdf). This covers A127793 only; there is no general remark that would cover A127767.
- Siblings with the same still-open integrality conjecture, all settled by the same argument: A127710, A127711, A127755, A127771.
- No relevant hits on arXiv, MathOverflow/MSE or SeqFan for A127767.

## Citation

```bibtex
@misc{math0:oeis-a127767,
  author       = {{math0}},
  title        = {{The inverse of the 1/Catalan band triangle (A127767) has integer entries}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a127767}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
