# A127752 mod 2 is the first Feigenbaum symbolic sequence A035263

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A127752  
**Date:** 2026-10-25

## Result

Let A(n,k) = 1/(3n+1) if k <= n <= 2k and 0 otherwise (n, k >= 0), and let a(n) be the row sums of the inverse of this lower-triangular matrix. Equivalently, a is defined by forward substitution: a(n) = 3n+1 - sum_{j<n, n<=2j} a(j). Let A035263 be the trajectory of 1 under the morphism 0 -> 11, 1 -> 10 (offset 1). Then for every n >= 0, a(n) mod 2 = A035263(n+1). This is Paul Barry's 2007 conjecture.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A127752](https://oeis.org/A127752) as [`Math0.Statements.A127752.statement`](../../lean/Math0/Statements/OEIS/A127752.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A127752.lean`](../../lean/Math0/Frontier/OEIS/A127752.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: a(n) mod 2 is first Feigenbaum symbolic sequence A035263 (conjecture). (Paul Barry, Jan 28 2007; checked to 2048 terms by Antti Karttunen, Sep 29 2018)

Referees: OEIS A127752 (P. Barry, Jan 28 2007; current version #11, Feb 11 2021) still says "(conjecture)", with A. Karttunen's 2018 check of the first 2048 terms. A127751 (#5) still calls it conjectural, and the related A127750, A127749 and A111967 conjectures (Fredholm-Rueppel parity for the 1/(2n+1) triangle) remain open. Checked and not relevant: S. Fried, "On the inverse of a certain triangular matrix and its connection to the largest odd divisor", NNTDM 32(2) (2026) 255-262, which covers A127793 and A000265, not A127752; S. Fried, JIS 28 (2025) Art. 25.4.3 and JIS 29 (2026) Art. 26.1.8; S. Fried, arXiv:2607.24832. No prior proof or counterexample found, and no existing formalization in formal-conjectures.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a127752,
  author       = {{math0}},
  title        = {{A127752 mod 2 is the first Feigenbaum symbolic sequence A035263}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a127752}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
