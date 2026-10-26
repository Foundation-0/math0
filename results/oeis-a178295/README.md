# A178295: collinear 4-subsets of {0,...,4}^n number 9^n/2 + 3*7^n/2 - 2*5^n (Mathar's conjecture, all three formulas)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A178295  
**Date:** 2026-10-24

## Result

Let a(n) be the number of 4-element subsets of the grid {0,...,4}^n whose points lie on one line. Collinearity means that all 2x2 minors of the difference vectors vanish. Then three things hold. (1) a(n) = 9^n/2 + 3*7^n/2 - 2*5^n for every n >= 0. (2) a(n) = 21 a(n-1) - 143 a(n-2) + 315 a(n-3) for every n >= 3. (3) As formal power series over Q, sum a(n) x^n = x(-5+41x) / ((9x-1)(7x-1)(5x-1)).

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A178295](https://oeis.org/A178295) as [`Math0.Statements.A178295.statement`](../../lean/Math0/Statements/OEIS/A178295.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A178295.lean`](../../lean/Math0/Frontier/OEIS/A178295.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: a(n) = 9^n/2+3*7^n/2-2*5^n. a(n)= +21*a(n-1) -143*a(n-2) +315*a(n-3). G.f.: x*(-5+41*x)/((9*x-1)*(7*x-1)*(5*x-1)). [_R. J. Mathar_, May 24 2010]

Referees: No published resolution of the A178295 formula was found. Local mirror oeisdata seq/A178/A178295.seq (%I #15, Jul 22 2025): the formula is still labelled "Conjecture [R. J. Mathar, May 24 2010]", with no %E lines and no cross-references to it.

Related sources:
- **R. J. Mathar, "Points on a line in the finite d-dimensional simple cubic lattice"** (oeis.org/A178294/a178294.pdf). Its abstract calls it a "mostly speculative summary", fitting Hardin's tables to Ehrhart polynomials. I saw only search snippets and an independent report, not the full text: the mirror has only an LFS pointer, and oeis.org and the Wayback Machine were inaccessible.
- **the-omega-institute/trureturing, GitHub issue #7376 (Sep 12–13, 2026).** A Lean proof of sibling A178294 (triples in the 4^n grid). Its literature check found "no proof or refutation as of 2026-09-13" and says the Mathar PDF gives the formula only as a fit. It does not mention A178295.
- **Classical full-line count ((k+2)^n - k^n)/2**, which gives the (7^n-5^n)/2 ingredient (A081200, itself still labelled a Hardin conjecture in OEIS):
  - P. Erdős and J. L. Selfridge, J. Combin. Theory Ser. A 14 (1973) 298-301.
  - S. W. Golomb and A. W. Hales, "Hypercube Tic-Tac-Toe", MSRI Publ. 42 (2002), Theorem 1.
  - L. Moser's proof, via Honsberger.
  - O. Patashnik, Math. Mag. 53 (1980).
- **Same-batch siblings, still labelled conjectures:** A081199, A081200, A081201, A178294, A178296-A178299.
- **Checked, no relevant result:** arXiv:2609.25133 (Kudriashov, Sep 2026), arXiv:2404.02369, arXiv:1107.0327.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a178295,
  author       = {{math0}},
  title        = {{A178295: collinear 4-subsets of {0,...,4}^n number 9^n/2 + 3*7^n/2 - 2*5^n (Mathar's conjecture, all three formulas)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a178295}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
