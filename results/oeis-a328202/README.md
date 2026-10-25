# The gcd of the interior binomial coefficients of row n equals Λ-exp(n)·Λ-exp(n−1) (A328202, Maiga's conjecture)

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A328202  
**Date:** 2026-10-25

## Result

For every n ≥ 4, let G(n) = gcd{ C(n,k) : 2 ≤ k ≤ n−2 }. Let L(m) = p if m = p^t is a prime power (p prime, t ≥ 1), and L(m) = 1 otherwise (A014963, the exponential of the von Mangoldt function). Then G(n) = L(n)·L(n−1).

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A328202](https://oeis.org/A328202) as [`Math0.Statements.A328202.statement`](../../lean/Math0/Statements/OEIS/A328202.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A328202.lean`](../../lean/Math0/Frontier/OEIS/A328202.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A328202 a(n) = A014963(n) * A014963(n - 1) (conjecture). - _Jon Maiga_, Oct 08 2019; also %C (From _Robert Israel_, Oct 16 2019): 'If p is a Fermat prime > 3, a(p)=2*p. If p is a Mersenne prime, a(p+1)=2*p. Conjecture: these are the only cases where a(n)>n.'

Referees: G. Kaplan and D. Levy, "GCD of truncated rows in Pascal's triangle", Integers 4 (2004), #A14 (https://math.colgate.edu/~integers/e14/e14.pdf). Theorem 4 with Theorem 7 at t=1 (h(n,1)=1 for n>=4), or equivalently Theorem 9, gives g(n,2) = lcm(g(n-1,1), g(n,1)) = A014963(n)*A014963(n-1). This proves the A328202 formula in 2004, before the 2019 OEIS conjecture, and the paper's Table 2 matches the sequence data. Also relevant: H. Joris, C. Oestreicher and J. Steinig, "The greatest common divisor of certain sets of binomial coefficients", J. Number Theory 21 (1985) 101-119, which gives a general formula for gcd{C(n,k): r<=k<=s} (not checked directly). Background: Ram (1909) for the g(n,1) case. The OEIS entry (rev #46, Oct 10 2026) still labels the formula "(conjecture)" and does not cite these papers.

## Citation

```bibtex
@misc{math0:oeis-a328202,
  author       = {{math0}},
  title        = {{The gcd of the interior binomial coefficients of row n equals Λ-exp(n)·Λ-exp(n−1) (A328202, Maiga's conjecture)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a328202}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
