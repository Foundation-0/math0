# A116184: Adamchuk's conjectures on 37^3 dividing the numerator of sum_{k=1}^{36} 1/k^n

**Classification:** New result (open problem settled)  
**Area:** Number theory  
**Source problem:** OEIS A116184  
**Date:** 2026-10-19

## Result

Let H(n) = sum_{k=1}^{36} 1/k^n, a rational number. Claim (a): for every k >= 0, 37^3 divides the numerator of H(3 + 36k). Claim (b): if p > 37 is a prime and 37^3 divides the numerator of H(p), then p = 37k - 1 for some natural number k, that is, p ≡ -1 (mod 37).

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A116184](https://oeis.org/A116184) as [`Math0.Statements.A116184.statement`](../../lean/Math0/Statements/OEIS/A116184.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A116184.lean`](../../lean/Math0/Frontier/OEIS/A116184.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: All terms of the arithmetic progression 3+36k belong to a(n). ... It appears that all primes in a(n) that are greater than 37 are of the form 37k-1. (Alexander Adamchuk, Apr 08 2007)

Referees: No explicit prior resolution of the A116184 conjecture found. OEIS A116184 is unchanged (rev #6, Feb 16 2025) with no %E line or resolving comment, and no other mirror entry cross-references it. Classical ingredients that make it an easy corollary:
- J.W.L. Glaisher, Q. J. Math. 31 (1900) 321-353: H(p-1,m) ≡ -m(m+1)/(2(m+2))·p^2·B_{p-2-m} (mod p^3) for odd m ≤ p-3.
- Z.-H. Sun, "Congruences concerning Bernoulli numbers and Bernoulli polynomials", Discrete Appl. Math. 105 (2000) 193-223: Thm 5.1(a) (k ≤ p-4) and the power-sum formula S_k ≡ pB_k + (p^2/2)kB_{k-1} + (p^3/6)k(k-1)B_{k-2} (mod p^3), as quoted in C. Levaillant, arXiv:2005.09434, Results 2 and 4.
- J. Zhao, arXiv:math/0301252: (p, p-2n-1) is irregular iff H(p-1, 2n-1) ≡ 0 (mod p^3) for p ≥ 2n+3.
- Kummer congruences, plus (37,32) being an irregular pair.
- R. Meštrović, arXiv:1111.3057, eq. (22).
- OEIS A007408 comment (Adamchuk 2006): 37^3 | numerator of H(36,3), i.e. the k=0 case.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a116184,
  author       = {{math0}},
  title        = {{A116184: Adamchuk's conjectures on 37^3 dividing the numerator of sum_{k=1}^{36} 1/k^n}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a116184}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
