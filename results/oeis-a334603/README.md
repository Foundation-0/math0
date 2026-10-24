# The period of 1/11^n is 2 * 11^(n-1)

**Classification:** First formal proof of a known result  
**Area:** Number theory  
**Source problem:** OEIS A334603  
**Date:** 2026-10-18

## Result

For every n >= 1, the period of the decimal expansion of 1/11^n is 2 * 11^(n-1). Equivalently, the multiplicative order of 10 modulo 11^n is 2 * 11^(n-1). This is the FORMULA conjecture of OEIS A334603.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A334603](https://oeis.org/A334603) as [`Math0.Statements.A334603.statement`](../../lean/Math0/Statements/OEIS/A334603.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A334603.lean`](../../lean/Math0/Frontier/OEIS/A334603.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Comment: "Conjecture proposed by the authors in References page 205: if p is a prime with gcd(p,30) = 1 and if the period of 1/p is m then the period of 1/p^n is m*p^(n-1)." Formula: "a(n) = 2 * 11^(n-1) [conjectured, see comments]." (_Bernard Schott_, May 07 2020)

Referees: The result is classical; no formalization of this specific statement was found.

Classical theory: Gauss, Disquisitiones Arithmeticae (1801), on orders modulo p^n and on periods of decimal fractions with prime-power denominators (Arts. 85-89, 312-318). Standard elementary number theory texts (Ireland-Rosen; Niven-Zuckerman-Montgomery) state the lifting lemma: if p is odd and a^{ord_p a} = 1 + p*c with p ∤ c, then ord_{p^n}(a) = p^{n-1} * ord_p(a). Mathlib's ZMod.orderOf_one_add_mul_prime is that lemma for 1 + p*a.

Explicit decimal-period statements:
- K. A. Ross, "Repeating Decimals: A Period Piece", Mathematics Magazine 83 (2010), 33-45. If n is the largest exponent with period(1/p^n) = period(1/p), then period(1/p^a) = period(1/p) * p^(a-n) for a > n. For p = 11, period(1/121) = 22 ≠ 2, so n = 1.
- S. Yao and A. Toyohara, "The length of the repeating decimal", arXiv:2507.01295 (2025), Theorem 2.1: l_{p^n} = p^{n-(m_p+1)} * l_p, where m_p = v_p((10^{l_p} - 1)/p). For p = 11 this gives m = v_11(9) = 0, so l_{11^n} = 2*11^(n-1).
- Wikipedia, "Repeating decimal": the period of 1/p^2 is usually p*T_p, with the only known exceptions 3, 487 and 56598313.
- OEIS A045616 (primes with 10^(p-1) ≡ 1 mod p^2) lists exactly these exceptions, and 11 is not among them.
- John D. Cook, "Reciprocals of prime powers" (blog, 2021-09-28) checks 1/121 explicitly: period 22.

In the OEIS itself, A055272 has a Sep 2026 comment by E. Rodríguez proving the analogous 7^n case with the same lifting argument.

Side note: the general conjecture of De Koninck and Mercier quoted in the A334603 comments (not the formalized statement) is false at p = 487.

Sources: https://arxiv.org/abs/2507.01295 ; https://en.wikipedia.org/wiki/Repeating_decimal ; https://www.johndcook.com/blog/2021/09/28/reciprocals-of-prime-powers/ ; https://oeis.org/A045616 (read from the local mirror)

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a334603,
  author       = {{math0}},
  title        = {{The period of 1/11^n is 2 * 11^(n-1)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a334603}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
