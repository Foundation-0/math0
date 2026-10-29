# A127752 mod 2 is the first Feigenbaum symbolic sequence A035263

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A127752  
**Date:** 2026-10-25

## Result

Let A(n,k) = 1/(3n+1) if k <= n <= 2k and 0 otherwise (n, k >= 0), and let a(n) be the row sums of the inverse of this lower-triangular matrix. Equivalently, a is defined by forward substitution: a(n) = 3n+1 - sum_{j<n, n<=2j} a(j). Let A035263 be the trajectory of 1 under the morphism 0 -> 11, 1 -> 10 (offset 1). Then for every n >= 0, a(n) mod 2 = A035263(n+1). This is Paul Barry's 2007 conjecture.

## Assessment

The whole argument is to write row n of A s = 1 as a window sum, sum_{j=ceil(n/2)}^{n} s(j) = 3n+1, and subtract consecutive rows. This gives s(2m+2)=3 and s(2m+1)=s(m)+3, which also yields a closed form in terms of the 2-adic valuation of n+1. Parity then follows by a one-line induction against the recursion a(2n)=1-a(n), a(2n+1)=1, which is already listed in A035263. This is a half-page, standard telescoping argument that a competent mathematician would find within minutes. Most of the effort went into the formalization (morphic-word indexing, matrix-inverse link), not into new mathematics.

*Follows from:* The row-n equation of the lower-triangular system A s = 1, i.e. sum_{ceil(n/2)<=j<=n} s(j) = 3n+1. Taking differences of consecutive rows gives s(0)=1, s(2m+2)=3 and s(2m+1)=s(m)+3. Compare this with the formula a(2n)=1-a(n), a(2n+1)=1 already listed in A035263 (equivalently, the parity of the 2-adic valuation of 2n).

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A127752](https://oeis.org/A127752) as [`Math0.Statements.A127752.statement`](../../lean/Math0/Statements/OEIS/A127752.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A127752.lean`](../../lean/Math0/Frontier/OEIS/A127752.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

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
