# A262957: Israel's b(n), c(n) are coprime integers and a(n) = b(n)

**Classification:** New result (open problem settled)  
**Area:** Number theory  
**Source problem:** OEIS A262957  
**Date:** 2026-10-18

## Result

Let cf(n) be the value of 1 - 1/(2 + 1/(3 - 1/(4 + ... (n+1) + (-1)^(n+1)/1))), where the integers 1, ..., n+1 are used, the sign after k is (-1)^k, and the innermost tail is 1. Let a(n) be the numerator of cf(n) in lowest terms. Robert Israel defined b and c by b(1)=2, b(2)=3, c(1)=3, c(2)=5 and, for both, x(n+1) = (((-1)^n(n-1) + n(n+2)) x(n) - (1 + (-1)^n(n+1)) x(n-1)) / (n - (-1)^n). Claim (Israel's conjecture, OEIS A262957): for every n >= 1, b(n) and c(n) are integers with gcd(b(n), c(n)) = 1, and a(n) = b(n).

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A262957](https://oeis.org/A262957) as [`Math0.Statements.A262957.statement`](../../lean/Math0/Statements/OEIS/A262957.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A262957.lean`](../../lean/Math0/Frontier/OEIS/A262957.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: b(n) and c(n) are coprime for all n, so that a(n) = b(n). I have verified this for n <= 10000. - _Robert Israel_, Dec 22 2015 [b(1)=2, b(2)=3, c(1)=3, c(2)=5, b(n+1) = (((-1)^n*(n-1)+n*(n+2))*b(n) - (1+(-1)^n*(n+1))*b(n-1))/(n-(-1)^n), same recurrence for c]

Referees: OEIS A262957 (local mirror, rev #80, Mar 2025): Robert Israel's comment of Dec 22 2015 states the conjecture, verified for n <= 10000, and it is still listed as open. Peter Bala, "A note on A262957 and A263295" (Dec 24 2015, linked from the OEIS entry): proves the simple continued fraction expansion [0;1,1,2,1,3,4,1,5,6,...] of the limit, but not Israel's recurrence or the coprimality. The cross-referenced entries A263295, A346590, A244279 and A244280 contain no proof. A262957 is absent from Tom Adamczewski, "OEIS Open: How many conjectures can language models turn into theorems?", arXiv:2608.11941 (2026), and from the epoch-research/LeanOpenProblems and LeanOpenProblems-results repositories. Web searches of arXiv, MathOverflow, Math StackExchange and SeqFan found no prior resolution. The proof uses the classical determinant identity for continued-fraction convergents (p_{k+1}q_k - p_k q_{k+1} = ±1).

## Citation

```bibtex
@misc{math0:oeis-a262957,
  author       = {{math0}},
  title        = {{A262957: Israel's b(n), c(n) are coprime integers and a(n) = b(n)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a262957}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
