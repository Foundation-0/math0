# A249151(k) = k exactly when k + 1 is prime (Karttunen's conjecture, A249434/A249151)

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A249434  
**Date:** 2026-10-25

## Result

Let P(k) = prod_{j=0..k} C(k,j) be the product of row k of Pascal's triangle. For every k >= 0, k is the largest m with m! | P(k) if and only if k+1 is prime. Equivalently, A249151(k) = k iff k+1 is prime, so A006093 = {k : A249151(k) = k}.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A249434](https://oeis.org/A249434) as [`Math0.Statements.A249434.statement`](../../lean/Math0/Statements/OEIS/A249434.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A249434.lean`](../../lean/Math0/Frontier/OEIS/A249434.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C A249434 It seems that A006093 gives all those k for which A249151(k) = k. If that is true, then this is a disjoint union of A006093 and A249429. (_Antti Karttunen_, Nov 02 2014; the same claim appears in A249151: 'A006093 seems to give all such k, that a(k) = k', and %Y A249434 'Subsequences: A006093 (conjectured)')

Referees: OEIS A249434, A249151, A249431 (Antti Karttunen, Oct/Nov 2014; latest revisions Aug–Sep 2025 still say "seems"/"conjectured"; no %E proof record). J. C. Lagarias and H. Mehta, "Products of binomial coefficients and unreduced Farey fractions", arXiv:1409.4145 (Int. J. Number Theory 2016): formulas for ord_p of the row product G_n, including ord_p(G_n) = 0 iff n = a·p^k − 1 with 1 ≤ a ≤ p−1. This is a related ingredient, but the paper does not state or prove the conjecture. L. Du and J. C. Lagarias, arXiv:2006.15439, and Du–Lagarias–Yangjit, arXiv:2112.14422: related, but they do not address the conjecture. The conjecture is not in the AlphaProof Nexus / formal-conjectures auto_oeis set of 492 (Tsoukalas et al., arXiv:2605.22763) or in OEIS Open (Adamczewski, arXiv:2608.11941). No MathOverflow, Math StackExchange or SeqFan resolution was found.

## Citation

```bibtex
@misc{math0:oeis-a249434,
  author       = {{math0}},
  title        = {{A249151(k) = k exactly when k + 1 is prime (Karttunen's conjecture, A249434/A249151)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a249434}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
