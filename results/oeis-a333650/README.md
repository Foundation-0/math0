# Domino towers of height 2 and of height n-1, n-2, n-3 (A333650): all four Kagey/Luschny conjectures

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A333650  
**Date:** 2026-10-19

## Result

Let T(n,k) count domino towers (brick-wall pattern: a brick of layer i has a left end ≡ i mod 2 in half-brick units; the bottom layer is a contiguous row of b ≥ 1 bricks, normalised to start at 0; each brick above the base overlaps a brick below by at least half a brick) with n bricks and k layers. Then:
(1) for n > 1, T(n,2) = A000071(n+2) = F(n+2) - 1;
(2) for n ≥ 2, T(n,n-1) = A339252(n-2), where a(0)=1, a(1)=4, a(2)=11, a(m+3)=4a(m+2)-4a(m+1);
(3) for n ≥ 3, T(n,n-2) = A339254(n-3), where a(0..4)=1,7,24,70,193 and a(m+5)=6a(m+4)-12a(m+3)+8a(m+2);
(4) for n ≥ 4, T(n,n-3) = A339029(n-4), the coefficients of (1+4x-20x^2+8x^3+33x^4-4x^5-33x^6)/(1-2x)^4.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A333650](https://oeis.org/A333650) as [`Math0.Statements.A333650.statement`](../../lean/Math0/Statements/OEIS/A333650.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A333650.lean`](../../lean/Math0/Frontier/OEIS/A333650.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C A333650 Conjecture: For n > 1, T(n,2) = A000071(n+2).  [entry author _Peter Kagey_, Mar 31 2020]; Conjecture: T(n,n-1) = A339252(n-2). - _Peter Kagey_, Nov 21 2020; Conjecture: T(n,n-2) = A339254(n-3). - _Peter Luschny_, Nov 29 2020; Conjecture: T(n,n-3) = A339029(n-4). - _Peter Luschny_, Dec 01 2020 (summarised by Luschny as T(2n+k, n+k) = d_n(n+k-1), k>=1, 0<=n<=3).

Referees: OEIS A333650 (Kagey, Mar 2020; conjectures by Kagey Nov 21 2020 and Luschny Nov 29 / Dec 1 2020; still marked Conjecture as of revision #68, Aug 12 2022). A339494 (Luschny, Dec 2020): unproved remark that towers of height <=2 by base size form the binomial triangle C(k,n-k) (A030528), whose row sums are Fibonacci numbers, which is essentially the height-2 argument. A339495 assumes the height-2 formula. A339252, A339254, A339029: closed forms of the target sequences only. Definition of domino towers: A264746, A320314; Bona, Handbook of Enumerative Combinatorics, pp. 25-27; Gouyou-Beauchamps & Viennot 1988; Bétréma & Penaud 1993; Zeilberger arXiv:1208.2258. Related papers with no height enumeration: Ekhad & Zeilberger arXiv:1212.4105; T. M. Brown, Convex Domino Towers (JIS 2017, arXiv:1608.01562) and k-omino towers (arXiv:1608.01563); A. Haupt, S-omino towers (JIS 2021, arXiv:1810.10428); Ardila arXiv:1409.2562. Math StackExchange 2949131 and 3659431 (Kagey): symmetric towers and the 4^(n-1) variant only. No prior proof or counterexample of any of the four conjectures found.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a333650,
  author       = {{math0}},
  title        = {{Domino towers of height 2 and of height n-1, n-2, n-3 (A333650): all four Kagey/Luschny conjectures}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a333650}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
