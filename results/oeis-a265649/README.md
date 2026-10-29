# A265649: both of Werner Schulte's closed forms hold

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A265649  
**Date:** 2026-10-29

## Result

Let T(0,0)=1, T(0,k)=0 for k>0, and T(n,k) = T(n-1,k-1) + (2n-1+k)·T(n-1,k) for n ≥ 1, with T(n,-1)=0. Then (i) for all 0 ≤ k ≤ n, T(n,k) = 2^(n-k)·(n-k)!·C(n,k)·Σ_{j=0}^{n-k} (-1/4)^j·C(2j+k,j)·C(n,j+k). (ii) For all n ≥ 1 and 0 ≤ k ≤ n, T(n,k) = (-1)^k·Σ_{j=0}^{n-1} A001497(n-1,j)·A021009(j+1,k). Here A001497(n,m) = (2n-m)!/(m!(n-m)!2^(n-m)) is the Bessel triangle and A021009(n,m) = (-1)^m·n!·C(n,m)/m! is the signed Laguerre triangle, both zero outside 0 ≤ m ≤ n.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A265649](https://oeis.org/A265649) as [`Math0.Statements.A265649.statement`](../../lean/Math0/Statements/OEIS/A265649.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A265649.lean`](../../lean/Math0/Frontier/OEIS/A265649.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A265649 Conjecture: T(n,k) = 2^(n-k)*(n-k)!*binomial(n,k)*(Sum_{j=0..n-k} (-1/4)^j* binomial(2*j+k,j)*binomial(n,j+k)).  %F A265649 Conjecture: T(n,k) = (-1)^k*Sum_{j=0..n-1} A001497(n-1,j)*A021009(j+1,k). (_Werner Schulte_, Dec 11 2015)

Referees: No explicit prior proof of either formula was found, and OEIS A265649 (rev. #40, Mar 2024) still marks both as "Conjecture". Both are immediate special cases of known results:
(1) L. C. Hsu and P. J.-S. Shiue, "A unified approach to generalized Stirling numbers", Adv. Appl. Math. 20 (1998) 366-384: generalized Stirling numbers S(n,k;α,β,r), whose defining connection relation directly gives the product formula.
(2) R. S. Maier, "Boson Operator Ordering Identities from Generalized Stirling and Eulerian Numbers", arXiv:2308.10332 (v4, 9 Feb 2024), linked from the A265649 entry. Eq. (18) gives the product formula S(α,γ;r1+r2) = S(α,β;r1)S(β,γ;r2). §5, p. 19 identifies A265649 = S_{n,k}(-2,1;1). Pp. 17-18 identify A001497 = b̂^(1) = S(-2,-1;1) and A021009 = L̂^(1) = S(-1,1;1) (signed), and Thm 5.1 (ii'), (iv') gives their closed forms. Eq. (72) states the r=0 analogue S(-2,1;0) = S(-2,-1;0)S(-1,1;0) of Conjecture 2. Thm 5.2(vi) gives a different, proved 2F1 closed form for S_{n,k}(-2,1;1).
Conjecture 2 = S(-2,-1;0)·S(-1,1;1), and Conjecture 1 = S(-2,2;2)·S(2,1;-1), reindexed; both checked numerically.
Also checked, with no A265649 resolution found: P. Barry, arXiv:1702.04011, Example 1 (displays the array as the exponential Riordan array [1/sqrt(1-2x), 1/sqrt(1-2x)-1], with no proof of the conjectures); S. Fried's OEIS-conjecture series (arXiv:2410.07237; JIS 28 (2025) Art. 25.4.3; JIS 29 (2026) Art. 26.1.8; arXiv:2607.24832); cross-referencing entries A370419, A347204 and A035342.

## Citation

```bibtex
@misc{math0:oeis-a265649,
  author       = {{math0}},
  title        = {{A265649: both of Werner Schulte's closed forms hold}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a265649}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
