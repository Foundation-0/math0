# The corrected floor formula for collinear triples in a 3 x n grid (OEIS A057566) holds for all n

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A057566 (formula as corrected on 21 Oct 2026)  
**Date:** 2026-10-29

## Result

Let a(n) be the number of 3-element collinear subsets of the grid {0,1,2} x {0,...,n-1}. Then for every n >= 0, a(n) = 5*floor((2n^3 - 3n^2 - 2n + 3)/24) + floor((2(n-1)^3 - 3(n-1)^2 - 2(n-1) + 3)/24) + n, with true floors (equivalently integer floor division, since both numerators are nonnegative for n >= 0).

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A057566 (formula as corrected on 21 Oct 2026)](https://oeis.org/A057566) as [`Math0.Statements.A057566b.statement`](../../lean/Math0/Statements/OEIS/A057566b.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A057566b.lean`](../../lean/Math0/Frontier/OEIS/A057566b.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: a(n) = 5*floor((2n^3 - 3n^2 - 2n + 3)/24) + floor((2(n-1)^3 - 3(n-1)^2 - 2(n-1) + 3)/24) + n, which fits all of the listed terms. [Corrected by _Alper Ferudun_, Oct 21 2026] (OEIS A057566, %F line; original conjecture by John W. Layman, Oct 2000)

Referees: - OEIS A057566 revision #30 (Oct 22 2026): corrected floor conjecture (Layman 2000, corrected by Alper Ferudun Oct 21 2026), still marked "Conjecture". The same entry has R. J. Mathar's formula (May 23 2010), a(n) = n^3/2 - n^2 + n + (1-(-1)^n)/4, with g.f. x*(1-x+4x^2+2x^3)/((1+x)(x-1)^4) and the order-5 recurrence. The floor formula is equivalent to this closed form by a mod-24 residue check.
- OEIS A334704 (Sloane 2020, data by Tom Duff): A057566 is row 3 of the m x n collinear-triple array. Cross-references checked: A000938 (Larrosa Cañestro gcd-sum formula, 2010; Guy & Kelly, Canad. Math. Bull. 11 (1968)), A047264, A010686.
- Ko Yun Tung, Puk Hoi Chun, Yeung Wai Kwan, "On the generalisations of the No-Three-in-Line problem", Hang Lung Mathematics Awards 2025 (bronze), Thm 2.2.1: exact count S(p,q) of collinear triples by slope in an m x n lattice. It specializes to the 3 x n case.
- No explicit proof of the floor form itself was found. Searched: arXiv 2607.24832 (S. Fried, Further proofs of conjectures from the OEIS) and arXiv 2609.25133 (neither treats A057566), MSE/MO, SeqFan archives, and the web.

## Citation

```bibtex
@misc{math0:oeis-a057566b,
  author       = {{math0}},
  title        = {{The corrected floor formula for collinear triples in a 3 x n grid (OEIS A057566) holds for all n}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a057566b}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
