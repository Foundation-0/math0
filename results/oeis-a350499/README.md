# Kurkov's recursion computes the free cumulants (A350499)

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A350499  
**Date:** 2026-10-29

## Result

Take indeterminate moments m_1, m_2, ... over Z, and set m_0 = 1. Let M(x) = x + m_1 x^2 + m_2 x^3 + ..., let W = M^<-1> be its compositional inverse, and let C(x) = x / W(x) = sum c_n x^n, so c_n are the free cumulants. Kurkov's array is defined by R(1,k) = m_k and, for n > 1, R(n,k) = R(n-1,k+1) - sum_{j=1}^{n-1} R(j,k) R(n-j,1). Claim: R(n,1) = c_n for every n >= 1, as an identity in Z[m_1, m_2, ...].

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A350499](https://oeis.org/A350499) as [`Math0.Statements.A350499.statement`](../../lean/Math0/Statements/OEIS/A350499.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A350499.lean`](../../lean/Math0/Frontier/OEIS/A350499.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: free cumulants in terms of the free moments are R(n,1) for n > 0 where R(n,k) = R(n-1,k+1) - Sum_{j=1..n-1} R(j,k)*R(n-j,1) for n > 1, k > 0 with R(1,k) = m_k for k > 0. - _Mikhail Kurkov_, Mar 30 2025

Referees: The conjecture is an immediate special case of the free-cumulant "products as arguments" formula, using the identification R(n,k) = κ_n(a^k, a, …, a):
- R. Speicher, "Multiplicative functions on the lattice of non-crossing partitions and free convolution", Math. Ann. 298 (1994) 611–628. This contains the case where one argument is a product.
- B. Krawczyk and R. Speicher, "Combinatorics of free cumulants", J. Combin. Theory Ser. A 90 (2000) 267–292, arXiv:math/9905094, Theorem 2.2.
- A. Nica and R. Speicher, Lectures on the Combinatorics of Free Probability, LMS Lecture Note Series 335, CUP 2006, Theorem 11.12.

Applying the formula to κ_{n−1}(a^k·a, a, …, a) gives Kurkov's recursion directly.

No explicit prior proof of Kurkov's formulation was found. OEIS A350499 (%I #63, Apr 04 2025; same in the current oeisdata) still lists it as "Conjecture … – Mikhail Kurkov, Mar 30 2025". The related entries A134264 and A133437 and the entry's own links (Copeland's blog, MathOverflow 412573, Zhou arXiv:1405.5296) do not address it.

## Citation

```bibtex
@misc{math0:oeis-a350499,
  author       = {{math0}},
  title        = {{Kurkov's recursion computes the free cumulants (A350499)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a350499}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
