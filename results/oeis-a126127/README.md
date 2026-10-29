# A126127: Israel's conjectured bivariate g.f. of the inverse square of A061554 holds

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A126127  
**Date:** 2026-10-29

## Result

Let M be the infinite lower-triangular matrix with M(n,k) = binomial(n, floor((n-k)/2)) for 0 <= k <= n (A061554), and let T = M^(-2) (A126127). Then, as formal power series in x, y over Q, sum_{n>=0} sum_{k=0}^{n} T(n,k) x^n y^k = (1-x)(1-x+x^2) / (1 - xy + 3x^2 - x^3 y + x^4).

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
