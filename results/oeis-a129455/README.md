# The triple-gcd Pascal triangle A129455: T(n,k) is an integer, divisible by C(n,k), and T(n,k)/C(n,k) is a sixth power

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A129455  
**Date:** 2026-10-25

## Result

Let G(m) = A129454(m+1) = prod_{i,j,k=1..m} gcd(i,j,k), so G(0) = 1. For all 0 <= k <= n: (1) G(k)·G(n-k) divides G(n), so T(n,k) = G(n)/(G(k)G(n-k)) is an integer; (2) the binomial coefficient C(n,k) divides T(n,k); (3) T(n,k)/C(n,k) = m^6 for some natural number m. This is Peter Bala's 2007 conjecture from OEIS A129455, with the Lean T defined by natural-number division as in the frozen statement.

## Assessment

Counting multiples of each prime power gives the Legendre-type formula v_p(G(n)) = sum_t floor(n/p^t)^3, which A129454 already points to and which is published in general form. With A = floor(k/p^t), B = floor((n-k)/p^t) and a carry c in {0,1}, the identity (A+B+c)^3 = A^3+B^3+c+3[AB(A+B)+c(A+B)(A+B+1)] has an even bracket. By Kummer's theorem the carries c add up to v_p(C(n,k)), so all three claims follow at once. The whole argument is under a page of standard elementary number theory and needs no new idea. Bala's comment itself says integrality would follow from the factorization.

*Follows from:* The prime factorization v_p(A129454(n+1)) = sum_t floor(n/p^t)^3 conjectured in A129454 (cubic analogue of the A092287 formula Greathouse confirmed; stated for general q in Ma, arXiv:2509.13354), together with Legendre's formula and Kummer's carry theorem for v_p(C(n,k)).

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A129455](https://oeis.org/A129455) as [`Math0.Statements.A129455.statement`](../../lean/Math0/Statements/OEIS/A129455.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A129455.lean`](../../lean/Math0/Frontier/OEIS/A129455.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: It appears that the T(n,k) are always integers. This would follow from the conjectured prime factorization given in A129454. Calculation suggests that the binomial coefficients C(n,k) divide T(n,k) and that T(n,k)/C(n,k) are perfect sixth powers. (Peter Bala, Apr 16 2007)

Referees: OEIS A129455, A129454 and A129453: the local mirror matches GitHub oeisdata (revisions #9, #8 and #9, Feb 2024), and all three still state the claims as conjectures. OEIS A092287: Greathouse (Apr 2013) confirmed the square-case prime factorization. Wanli Ma, "Generalized factorials characterized by Dirichlet convolution", arXiv:2509.13354 (Sept 2025), Section 2.2 and Theorems 2.5-2.6: proves that the q-tuple gcd product equals prod_p p^{sum floor(n/p^i)^q}, and that the generalized binomial coefficients for superadditive x are integers. With q=3 this implies only the integrality part of A129455; the paper does not mention A129454/A129455, C(n,k) divisibility or sixth powers. A.B. Mingarelli, "Abstract factorials", arXiv:0705.4299 / NNTDM 19 (2013): general framework, no gcd products. A224479/A224497 (Forgues, Luschny 2013): square-case formulas G2(n) = n!*A224479(n)^2, the analogue of the perfect-square property of A129453, but nothing for the cubic case. I found no source proving that C(n,k) divides T(n,k) or that T(n,k)/C(n,k) is a sixth power for A129455.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a129455,
  author       = {{math0}},
  title        = {{The triple-gcd Pascal triangle A129455: T(n,k) is an integer, divisible by C(n,k), and T(n,k)/C(n,k) is a sixth power}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a129455}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
