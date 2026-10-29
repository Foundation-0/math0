# Schulte's conjectures on A281000, T(n,k) = C(2n+1,2k+1)·Cat(n-k): antidiagonal sums and matrix inverse

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A281000  
**Date:** 2026-10-25

## Result

Let T(n,k) = C(2n+1,2k+1)·C(2n-2k,n-k)/(n+1-k) = C(2n+1,2k+1)·Cat(n-k) for 0 ≤ k ≤ n, and T(n,k) = 0 for k > n. Let N(n,j) = C(n-1,j-1)·C(n,j-1)/j be the Narayana numbers, s = A001003 the little Schröder numbers, with s(0) = 1 and s(n) = Σ_{j=1..n} 2^{j-1} N(n,j) for n ≥ 1, and b = A103365 the first column of the inverse of the lower-unitriangular Narayana matrix, so that Σ_{j=1..n} N(n,j) b(j) = [n = 1]. Then:
(1) for every n ≥ 0, Σ_{k=0..⌊n/2⌋} T(n-k,k) = s(n+1);
(2) (corrected reading) for every n ≥ 0, Σ_{k=0..n} T(n,k)(2k+1)Cat(k)·b(k+1) = 0^n;
(3) for every N, the inverse over ℚ of the N×N leading block of T is the N×N leading block of U(n,k) = T(n,k)·b(n+1-k).

## Assessment

The inverse in (3) is immediate once you see that T and the Narayana triangle are both diagonal conjugates of the same Toeplitz matrix built from c(j) = 1/(j!(j+1)!). Inverting that Toeplitz matrix is exactly the reciprocal power series that Hanna's g.f. in A103365 already records. Conjecture (2), read as its evidently intended column-0 case, is just the first column of T*T^{-1} = I. Conjecture (1) takes about a page, either with Vandermonde's identity and Cloitre's Narayana formula for A001003 or with the Motzkin bivariate g.f. that Barry's A097610 comment points to. The paper itself calls the result routine, and none of these steps needs a new idea.

*Follows from:* The scaling T(n,k) = (2n+1)!/(2k+1)! * c(n-k) with c(j) = 1/(j!(j+1)!), together with P. D. Hanna's g.f. in A103365 (A(x) = 1/B(x), B(x) = Sum x^n/[n!(n+1)!/2^n]), gives (3) at once; T. Copeland's inverse-pair comment in A238390 (Jan 30 2016) gives the same. (2) is the first column of (3). (1) follows from P. Barry's comment in A097610 (diagonal sums of the Motzkin triangle are the aerated large Schroeder numbers) plus a short g.f. parity argument, or from a Vandermonde/Narayana binomial identity.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A281000](https://oeis.org/A281000) as [`Math0.Statements.A281000.statement`](../../lean/Math0/Statements/OEIS/A281000.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A281000.lean`](../../lean/Math0/Frontier/OEIS/A281000.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

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

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

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
