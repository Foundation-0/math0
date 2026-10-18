# An equiangular decagon with sides in arithmetic progression (A215010)

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A215010  
**Date:** 2026-10-18

## Result

Garcia's conjecture (OEIS A215010) says that hexagons are the only equiangular simple convex polygons whose integer side lengths are the N terms t, t+d, ..., t+(N-1)d (with d ≥ 1) of an arithmetic progression, in some order. Formally: if N ≥ 3, every side t + σ(k)·d is positive, and Σ_k (t + σ(k)d)·exp(2πik/N) = 0 for a permutation σ of Fin N, then N = 6. We prove that this is false. Take N = 10 and t = d = 1, with consecutive sides (1, 4, 5, 8, 9, 2, 3, 6, 7, 10), so σ = (0, 3, 4, 7, 8, 1, 2, 5, 6, 9). This gives an equiangular decagon.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A215010](https://oeis.org/A215010) as [`Math0.Statements.A215010.statement`](../../lean/Math0/Statements/OEIS/A215010.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A215010.lean`](../../lean/Math0/Frontier/OEIS/A215010.lean) refutes (proves the negation of) it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: hexagons are the only simple convex polygons with equal interior angles with such property, due to the fact that cos(Pi/3) = 1/2." Here 'such property' means integer side lengths in arithmetic progression t+m*d, as in the entry name. (entry by _Robin Garcia_, Jul 31 2012)

Referees: Prior refutations, all at least as old as or published soon after Garcia's 2012 conjecture:

(1) OEIS A118887 (H. Pfoertner, May 03 2006). "Number of ways to place n objects with weights 1,...,n evenly spaced around a circle so it balances." T. D. Noe, Sep 13 2005: "Also number of equiangular polygons whose sides are some permutation of 1,2,3,...,n." The data have included a(10)=24, a(12)=732, a(14)=720, a(15)=48 since the first revision in 2006. W. Edwin Clark (Sep 14 2005) proved there are no solutions when n is a prime power. J. Sondow (Oct 17 2013) records that Murray Klamkin proved solutions exist when n is not a prime power, and adds the formula a(A024619(n)) > 0. The problem was proposed by Brendan McKay on the SeqFan mailing list, Sep 12 2005. https://oeis.org/A118887

(2) G. J. Woeginger, "Nothing new about equiangular polygons", Amer. Math. Monthly 120(9) (2013) 849–850, doi:10.4169/amer.math.monthly.120.09.849. Abstract: "We survey results on equiangular n-vertex polygons with edge lengths in arithmetic progression. Such a polygon exists if and only if n has at least two distinct prime factors." This is exactly the A215010 setting, and it gives n = 10, 12, 14, 15, ... as counterexamples.

(3) Supporting references:
- D. Ball, "Equiangular polygons", Math. Gazette 86 (2002) 396–407.
- A. Bernoff, "Bernoff's Puzzler", MuddMath Newsletter 4(1) (2005), p. 10.
- M. Munteanu and L. Munteanu, "Rational equiangular polygons", Applied Math. 4 (2013) 1460–1465, doi:10.4236/am.2013.410197.
- U. Abel, "Coincidence of the barycentre and the geometric centre of weighted points", Math. Gazette (online Oct 2019). It restates the criterion: at least two distinct prime factors.

A215010 itself (history checked through revision #43, Jan 23 2015) never cites any of these, and its conjecture remains uncorrected. I found no earlier formalization in Lean or any other proof assistant.

## Citation

```bibtex
@misc{math0:oeis-a215010,
  author       = {{math0}},
  title        = {{An equiangular decagon with sides in arithmetic progression (A215010)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a215010}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
