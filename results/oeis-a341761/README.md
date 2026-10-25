# The subword complexity polynomial S(n,x) has leading coefficient n(n+1)/2 (A341761, Guo's conjecture)

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A341761  
**Date:** 2026-10-24

## Result

For a word w, complexity(w) is the number of distinct nonempty factors (contiguous subwords) of w. Let S(n,x) be the sum of complexity(w) over all x^n words w of length n on an alphabet of x letters. For every n >= 0 there is a polynomial P in Q[X] with P(x) = S(n,x) for every natural number x, and the coefficient of x^n in P is n(n+1)/2.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A341761](https://oeis.org/A341761) as [`Math0.Statements.A341761.statement`](../../lean/Math0/Statements/OEIS/A341761.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A341761.lean`](../../lean/Math0/Frontier/OEIS/A341761.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: the coefficient of x^n in S(n,x) is n*(n+1)/2. (Shiyao Guo, entry author, Feb 19 2021)

Referees: OEIS A341761 (Shiyao Guo, 2021; still labelled "Conjecture" in rev #33, Mar 2024), cross-referenced with OEIS A340885. Shiyao Guo (Mivik), "On the Expected Subword Complexity of Random Words", https://mivik.moe/2021/research/expected-subword-complexity-en/, and the Chinese version https://mivik.moe/2021/research/expected-subword-complexity/ (updated 2026-03-26, still calls it an unproven conjecture). Related work that does not settle it: S. Janson, S. Lonardi, W. Szpankowski, "On average sequence complexity", TCS 326 (2004); I. Gheorghiciuc, M. D. Ward, "On correlation polynomials and subword complexity", DMTCS Proc. AH (AofA 2007), https://dmtcs.episciences.org/3553; Ahmadi and Ward, "Asymptotic Analysis of the kth Subword Complexity" (Entropy, 2020); Ivanko (Trudy IMM UrO RAN, 2008). I found no prior proof.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a341761,
  author       = {{math0}},
  title        = {{The subword complexity polynomial S(n,x) has leading coefficient n(n+1)/2 (A341761, Guo's conjecture)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a341761}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
