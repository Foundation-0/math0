# A249151(k) = k exactly when k + 1 is prime (Karttunen's conjecture, A249434/A249151)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A249434  
**Date:** 2026-10-25

## Result

Let P(k) = prod_{j=0..k} C(k,j) be the product of row k of Pascal's triangle. For every k >= 0, k is the largest m with m! | P(k) if and only if k+1 is prime. Equivalently, A249151(k) = k iff k+1 is prime, so A006093 = {k : A249151(k) = k}.

## Assessment

The prime case takes one line: v_p(C(p,j)) = 1 for 0<j<p, so p^(p-1) exactly divides P(p). For composite n = k+1 the proof uses the standard row-product formula in A001142 to write v_q(P(k)/k!) as a sum over j < n. Splitting that sum by powers of q gives a closed form, q^e f(u) - R s(u) + e. A short digit-sum inequality, (q-1) f(u) >= s(u) whenever f(u) >= 1, then shows the excess is either negative or greater than e. All of this is about a page of elementary p-adic valuation bookkeeping (Legendre/Kummer-type sums) that someone fluent in such calculations would find quickly, so it is routine. The fact that the conjecture stayed open in the OEIS reflects lack of attention, not hidden difficulty.

*Follows from:* A001142's product formula P(k) = prod_{j=1..k} j^(2j-1-k), giving P(k)/k! = prod_{j<n} j^(2j-n-1) with n = k+1, together with Legendre's formula. Lagarias–Mehta (arXiv:1409.4145) also give closed forms for ord_p of the row product.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A249434](https://oeis.org/A249434) as [`Math0.Statements.A249434.statement`](../../lean/Math0/Statements/OEIS/A249434.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A249434.lean`](../../lean/Math0/Frontier/OEIS/A249434.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C A249434 It seems that A006093 gives all those k for which A249151(k) = k. If that is true, then this is a disjoint union of A006093 and A249429. (_Antti Karttunen_, Nov 02 2014; the same claim appears in A249151: 'A006093 seems to give all such k, that a(k) = k', and %Y A249434 'Subsequences: A006093 (conjectured)')

Referees: OEIS A249434, A249151, A249431 (Antti Karttunen, Oct/Nov 2014; latest revisions Aug–Sep 2025 still say "seems"/"conjectured"; no %E proof record). J. C. Lagarias and H. Mehta, "Products of binomial coefficients and unreduced Farey fractions", arXiv:1409.4145 (Int. J. Number Theory 2016): formulas for ord_p of the row product G_n, including ord_p(G_n) = 0 iff n = a·p^k − 1 with 1 ≤ a ≤ p−1. This is a related ingredient, but the paper does not state or prove the conjecture. L. Du and J. C. Lagarias, arXiv:2006.15439, and Du–Lagarias–Yangjit, arXiv:2112.14422: related, but they do not address the conjecture. The conjecture is not in the AlphaProof Nexus / formal-conjectures auto_oeis set of 492 (Tsoukalas et al., arXiv:2605.22763) or in OEIS Open (Adamczewski, arXiv:2608.11941). No MathOverflow, Math StackExchange or SeqFan resolution was found.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

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
