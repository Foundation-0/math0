# The row sums of the generalized Deutsch triangle A188474 are A137398

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A188474  
**Date:** 2026-10-29

## Result

Let T(n,k) = sum_{j=0}^{n-k+1} (j/(n+2-j)) C(n+2-j, n-k+1) C(n+2-j, k+1) 2^(j-1), computed in Q, for 0 <= k <= n. Let A137398(m) be the number of subsequences p of S = (0,1,...,2m-1) of length m with 0 in p such that, with q the complementary subsequence, no index i < m has the property that exchanging p(i) and q(i) leaves both p and q strictly increasing. Then for every n >= 0, sum_{k=0}^{n} T(n,k) = A137398(n+2). (This is Paul Barry's 2011 conjecture "Row sums are A137398(n+1)", in the current offset of A137398.)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A188474](https://oeis.org/A188474) as [`Math0.Statements.A188474.statement`](../../lean/Math0/Statements/OEIS/A188474.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A188474.lean`](../../lean/Math0/Frontier/OEIS/A188474.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C A188474 Row sums are A137398(n+1) (conjecture). Diagonal sums are A188476. (_Paul Barry_, Apr 01 2011)

Referees: No prior explicit resolution of Barry's conjecture found. The A188474 entry (local mirror, revision #6, Mar 30 2012) still marks the row-sum claim as "(conjecture)". The relevant prior material that makes it nearly immediate:
- **Callan's comment on OEIS A137398 (Nov 25 2021).** A137398 counts Grand Dyck paths starting with U with no peak at height 1 and no valley at height −1, with g.f. satisfying F = x(C−1)+2x(C−1)F. This is exactly the row-sum g.f. of A188474.
- **OEIS A137398 G.f. line.** 2x²/(1−2x−4x²+√(1−4x)), the same function after rationalizing; the original authors' recurrence a(n)=2a(n−1)+2a(n−2)+Σ C(k)a(n−k−1) is also on the entry.
- **OEIS A100754 (E. Deutsch).** Deutsch's g.f. tzr/(1−tzr) with the Narayana function r, from which Barry's r-family g.f. follows.
- **Goy & Shattuck, Carpathian Math. Publ. 15(2) (2023) 420–436, arXiv:2303.10223.** Thm 5 eq. (25) proves that a Fine-number determinant equals A137398, taking A137398's recurrence as its definition. It does not address A188474.

Searches came up empty for arXiv, the web generally, and SeqFan (not specifically found or checked). They covered "A188474", "A137398", "generalized Deutsch triangle", the term string 1,2,7,22,74,252,875,3078, and Barry's Riordan/Pascal-like papers (JIS 2007, 2011, 2019; arXiv 2606.22070).

## Citation

```bibtex
@misc{math0:oeis-a188474,
  author       = {{math0}},
  title        = {{The row sums of the generalized Deutsch triangle A188474 are A137398}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a188474}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
