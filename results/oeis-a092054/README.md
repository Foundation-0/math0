# Convergents of [1; 1/2, 1/3, ..., 1/n]: numerator + denominator = 2^(v2(n!) + v2((n+1)!)) (A092054)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Number theory  
**Source problem:** OEIS A092054  
**Date:** 2026-10-21

## Result

For every n >= 1, write the convergent [1; 1/2, 1/3, ..., 1/n] = 1 + 1/(1/2 + 1/(1/3 + ... + 1/(1/n))) in lowest terms as p/q. Then p + q is a power of 2, namely p + q = 2^a(n). Here a(n) is the base-2 logarithm, and a(n) = Sum_{k=1..n} A001511(floor((k+1)/2)) = 2n + 1 - s2(n) - s2(n+1) = A011371(n) + A011371(n+1). In these formulas A001511 is the ruler function, s2 = A000120 is the binary digit sum, and A011371(m) = m - s2(m).

## Assessment

The proof writes the convergents as P(n)/Q(n) using a three-term recurrence and checks closed forms for P and P+Q by a short induction. The odd parts of the factorials divide the odd double factorial because C(2m,m) is an integer, and Legendre's formula gives the exponent. Each step is standard: the link to Wallis products and the power-of-2 property are already recorded in the cross-referenced entries, and the manuscript itself calls the result a short consequence of classical facts. The informal argument is about a page; most of the work went into the Lean formalization.

*Follows from:* The cross-referenced entries already link the convergents to the partial Wallis products (A001902 and A092053 comments; Ordowski's [1;1,1/2,...,1/n] formula in A001901/A001902; Draim 1969), and A001901 is recorded as a subsequence of the powers of 2. Combine this with the closed form W(2m) = 16^m/((2m+1)·C(2m,m)^2), Kummer's theorem v2(C(2m,m)) = s2(m) (also in A056982 for even n), and Legendre's formula v2(m!) = m - s2(m).

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A092054](https://oeis.org/A092054) as [`Math0.Statements.A092054.statement`](../../lean/Math0/Statements/OEIS/A092054.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A092054.lean`](../../lean/Math0/Frontier/OEIS/A092054.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: It appears that a(n) = Sum_{k=1..n} A001511(floor((k+1)/2)). Equivalently, a(n) = 2n + 1 - A000120(n) - A000120(n+1) = A011371(n) + A011371(n+1). - _Franklin T. Adams-Watters_, Feb 02 2006

Referees: No prior explicit proof of A092054's conjectured formula found. Relevant partial or adjacent sources:
- OEIS A092054 (#43, Aug 09 2026): the formula is still marked "It appears".
- M. A. Suchenek, "Elementary Yet Precise Worst-Case Analysis of Floyd's Heap-Construction Program", Fundamenta Informaticae 120 (2012) 75-92, doi:10.3233/FI-2012-751. It proves 2N-2s2(N)-e2(N) for heap construction, which is algebraically equivalent to the conjectured formula. It does not prove the continued-fraction statement; the link to A092054 rests only on an OEIS comment.
- OEIS A001901: reduced Wallis numerators, "Subsequence of A000079" (powers of 2). Ordowski (2024): A001901(n) = numerator of [1;1,1/2,...,1/n].
- OEIS A056982 (Weisstein): 4^A005187(n) = denominator of prod_{k<=n}(1-1/(4k^2)). This gives the even-index exponent.
- OEIS A001902 and A092053 (Hanna 2004): the convergent numerators are the Wallis denominators.
- N. A. Draim, "Pi in the form of a continued fraction with infinite terms", Fibonacci Quarterly 7.3 (1969) 275-276, https://www.mathstat.dal.ca/FQ/Scanned/7-3/draim.pdf: Wallis partial products equal the convergents of a continued fraction with partial numerators (n-1)n.
- Kummer/Legendre: v2(C(2m,m)) = s2(m), v2(m!) = m - s2(m).

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a092054,
  author       = {{math0}},
  title        = {{Convergents of [1; 1/2, 1/3, ..., 1/n]: numerator + denominator = 2^(v2(n!) + v2((n+1)!)) (A092054)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a092054}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
