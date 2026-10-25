# Schulte's conjectures on A281000, T(n,k) = C(2n+1,2k+1)·Cat(n-k): antidiagonal sums and matrix inverse

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A281000  
**Date:** 2026-10-25

## Result

Let T(n,k) = C(2n+1,2k+1)·C(2n-2k,n-k)/(n+1-k) = C(2n+1,2k+1)·Cat(n-k) for 0 ≤ k ≤ n, and T(n,k) = 0 for k > n. Let N(n,j) = C(n-1,j-1)·C(n,j-1)/j be the Narayana numbers, s = A001003 the little Schröder numbers, with s(0) = 1 and s(n) = Σ_{j=1..n} 2^{j-1} N(n,j) for n ≥ 1, and b = A103365 the first column of the inverse of the lower-unitriangular Narayana matrix, so that Σ_{j=1..n} N(n,j) b(j) = [n = 1]. Then:
(1) for every n ≥ 0, Σ_{k=0..⌊n/2⌋} T(n-k,k) = s(n+1);
(2) (corrected reading) for every n ≥ 0, Σ_{k=0..n} T(n,k)(2k+1)Cat(k)·b(k+1) = 0^n;
(3) for every N, the inverse over ℚ of the N×N leading block of T is the N×N leading block of U(n,k) = T(n,k)·b(n+1-k).

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A281000](https://oeis.org/A281000) as [`Math0.Statements.A281000.statement`](../../lean/Math0/Statements/OEIS/A281000.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A281000.lean`](../../lean/Math0/Frontier/OEIS/A281000.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A281000 Conjectures: (1) Antidiagonal sums equal A001003(n+1); (2) Sum_{k=0..n} (-1)^k*T(n,k)*(2*k+1)*A000108(k)*A103365(k) = A000007(n); (3) Matrix inverse equals T(n,k)*A103365(n+1-k). (Werner Schulte, Jan 12 2017)

Referees: No prior resolution found. Sources checked:
- Local OEIS mirror: A281000 (#17, Nov 25 2018), A280580, A103365, A103364, A238390, A097610, A001003, A006318, A126120, A180874. No entry other than A281000 itself mentions A281000.
- arXiv 2607.24832 and 2410.07237 (Sela Fried, proofs of OEIS conjectures); no mention.
- arXiv 2608.11941 (Adamczewski, "OEIS Open") and the epoch-research/LeanOpenProblems-results repo; A281000 is not among its conjectures.
- Web searches on arXiv, MathOverflow, the OEIS wiki and SeqFan; no hits.

Closest prior material, which makes the result routine without explicitly resolving it:
- T. Copeland, comment in A238390 (Jan 30 2016): the inverse pair C(n,k)·A126120(n−k) ↔ C(n,k)·m(n−k), with m(2j) = (−1)^j·A238390(j). Its odd–odd block gives conjecture (3).
- V. Kotesovec, Mathematica in A103365 (2014), and P. D. Hanna's g.f. (2009): link A103365 to x/BesselJ(1,2x), so (−1)^j·A238390(j) = Cat(j)·A103365(j+1).
- P. Bala, A103364 (2013): generalized Riordan array (1/E(y), y).
- P. Barry, A097610 (Apr 2010): diagonal sums of the Motzkin triangle are the aerated large Schröder numbers. Restricting to an odd number of level steps gives half of that, which is conjecture (1).

## Citation

```bibtex
@misc{math0:oeis-a281000,
  author       = {{math0}},
  title        = {{Schulte's conjectures on A281000, T(n,k) = C(2n+1,2k+1)·Cat(n-k): antidiagonal sums and matrix inverse}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a281000}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
