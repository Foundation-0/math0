# The triple-gcd Pascal triangle A129455: T(n,k) is an integer, divisible by C(n,k), and T(n,k)/C(n,k) is a sixth power

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A129455  
**Date:** 2026-10-25

## Result

Let G(m) = A129454(m+1) = prod_{i,j,k=1..m} gcd(i,j,k), so G(0) = 1. For all 0 <= k <= n: (1) G(k)·G(n-k) divides G(n), so T(n,k) = G(n)/(G(k)G(n-k)) is an integer; (2) the binomial coefficient C(n,k) divides T(n,k); (3) T(n,k)/C(n,k) = m^6 for some natural number m. This is Peter Bala's 2007 conjecture from OEIS A129455, with the Lean T defined by natural-number division as in the frozen statement.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A129455](https://oeis.org/A129455) as [`Math0.Statements.A129455.statement`](../../lean/Math0/Statements/OEIS/A129455.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A129455.lean`](../../lean/Math0/Frontier/OEIS/A129455.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: It appears that the T(n,k) are always integers. This would follow from the conjectured prime factorization given in A129454. Calculation suggests that the binomial coefficients C(n,k) divide T(n,k) and that T(n,k)/C(n,k) are perfect sixth powers. (Peter Bala, Apr 16 2007)

Referees: OEIS A129455, A129454 and A129453: the local mirror matches GitHub oeisdata (revisions #9, #8 and #9, Feb 2024), and all three still state the claims as conjectures. OEIS A092287: Greathouse (Apr 2013) confirmed the square-case prime factorization. Wanli Ma, "Generalized factorials characterized by Dirichlet convolution", arXiv:2509.13354 (Sept 2025), Section 2.2 and Theorems 2.5-2.6: proves that the q-tuple gcd product equals prod_p p^{sum floor(n/p^i)^q}, and that the generalized binomial coefficients for superadditive x are integers. With q=3 this implies only the integrality part of A129455; the paper does not mention A129454/A129455, C(n,k) divisibility or sixth powers. A.B. Mingarelli, "Abstract factorials", arXiv:0705.4299 / NNTDM 19 (2013): general framework, no gcd products. A224479/A224497 (Forgues, Luschny 2013): square-case formulas G2(n) = n!*A224479(n)^2, the analogue of the perfect-square property of A129453, but nothing for the cubic case. I found no source proving that C(n,k) divides T(n,k) or that T(n,k)/C(n,k) is a sixth power for A129455.

## Citation

```bibtex
@misc{math0:oeis-a129455,
  author       = {{math0}},
  title        = {{The triple-gcd Pascal triangle A129455: T(n,k) is an integer, divisible by C(n,k), and T(n,k)/C(n,k) is a sixth power}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a129455}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
