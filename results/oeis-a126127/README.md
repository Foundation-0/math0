# A126127: Israel's conjectured bivariate g.f. of the inverse square of A061554 holds

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A126127  
**Date:** 2026-10-29

## Result

Let M be the infinite lower-triangular matrix with M(n,k) = binomial(n, floor((n-k)/2)) for 0 <= k <= n (A061554), and let T = M^(-2) (A126127). Then, as formal power series in x, y over Q, sum_{n>=0} sum_{k=0}^{n} T(n,k) x^n y^k = (1-x)(1-x+x^2) / (1 - xy + 3x^2 - x^3 y + x^4).

## Assessment

A130777, which A126127 itself points to as the inverse of A061554, already identifies M^(-1) as the Riordan array ((1-x)/(1+x^2), x/(1+x^2)). The conjecture is about the square of that array. Squaring it with the standard Riordan product rule and simplifying two short rational functions gives the stated g.f. in a few lines. The Lean proof avoids Riordan machinery and uses recurrences instead, but that is formalization effort, not a new mathematical idea.

*Follows from:* The cross-referenced entry A130777 says it is the inverse of A061554 and gives it as the Riordan array ((1-x)/(1+x^2), x/(1+x^2)) (Paul Barry, 2009). Its row-polynomial o.g.f. (1-z)/(1-xz+z^2) is the bivariate g.f. of M^(-1). The standard Riordan group product (g,f)*(h,l) = (g*(h o f), l o f) then gives M^(-2) = (g*(g o f), f o f), where g*(g o f) = (1-x)(1-x+x^2)/(1+3x^2+x^4) and f o f = x(1+x^2)/(1+3x^2+x^4). That is exactly Israel's g.f.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A126127](https://oeis.org/A126127) as [`Math0.Statements.A126127.statement`](../../lean/Math0/Statements/OEIS/A126127.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A126127.lean`](../../lean/Math0/Frontier/OEIS/A126127.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A126127 G.f. as triangle (conjectured): (1-x)*(1-x+x^2)/(1-x*y+3*x^2-x^3*y+x^4). - _Robert Israel_, Jul 07 2019

Referees: OEIS A126127 (Gary W. Adamson, 2006): conjectured g.f. by Robert Israel, Jul 07 2019, still marked conjectured upstream (oeisdata seq/A126/A126127.seq, %I #10, no %E edits). OEIS A130777: "Inverse of triangle in A061554", Riordan array ((1-x)/(1+x^2), x/(1+x^2)) by Paul Barry, May 21 2009; together with the standard Riordan group product rule (Shapiro, Getu, Woan, Woodson, 1991), this makes the conjecture an immediate corollary, but no source found states or proves the g.f. of the square. OEIS A061554: Riordan array (1/(1-x-x^2c(x^2)), x c(x^2)) by Philippe Deléham, 2007. Web searches (OEIS, arXiv, MathOverflow/Math StackExchange, SeqFan) found no prior proof or counterexample.

## Citation

```bibtex
@misc{math0:oeis-a126127,
  author       = {{math0}},
  title        = {{A126127: Israel's conjectured bivariate g.f. of the inverse square of A061554 holds}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a126127}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
