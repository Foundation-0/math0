# A223395: walks on the 4 x 4 grid graph satisfy Hardin's recurrence, Barker's g.f. and closed form

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A223395  
**Date:** 2026-10-24

## Result

Let a(n) be the number of walks with n vertices in the 4 x 4 grid graph P4 x P4 (the number of n x 1 arrays over the nodes 0..15 where vertically adjacent entries are adjacent nodes). Then (1) a(n) = 3a(n-1) + 2a(n-2) - 4a(n-3) for all n >= 4 (in Z); (2) (1 - x)(1 - 2x - 4x^2) * sum_{n>=1} a(n) x^n = 8x(2 - 3x^2) as formal power series over Z; (3) a(n) = (8 + (11 - 5 sqrt5)(1 - sqrt5)^n + (1 + sqrt5)^n (11 + 5 sqrt5)) / 5 for all n >= 1 (in R).

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A223395](https://oeis.org/A223395) as [`Math0.Statements.A223395.statement`](../../lean/Math0/Statements/OEIS/A223395.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A223395.lean`](../../lean/Math0/Frontier/OEIS/A223395.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Empirical: a(n) = 3*a(n-1) + 2*a(n-2) - 4*a(n-3)." and "Conjectures from _Colin Barker_, Aug 20 2018: G.f.: 8*x*(2 - 3*x^2) / ((1 - x)*(1 - 2*x - 4*x^2)) ..."

Referees: OEIS sources (local mirror):
- A223395 (R. H. Hardin, Mar 19 2013; Barker's conjectures added Aug 20 2018; rev #7). The recurrence is still "Empirical" and the g.f. and closed form are still "Conjectures"; there are no %E lines.
- A223402 (rev #8, Oct 03 2025). The column k=1 recurrence is still listed as empirical.
- A223372 (the 3x3 analogue, also empirical).
- A081057 (P. D. Hanna 2003; g.f. and recurrence by M. Somos and V. Jovovic, Mar 2003; R. J. Mathar, Oct 2010: "apparently" counts walks from a corner of the 4x4 board; D. Scambler, Oct 2010: decomposition into independent horizontal and vertical walks, giving a binomial convolution of Fibonacci numbers; I. M. Gessel 2022). It has the same signature (3,2,−4), but for corner-start walks only. I observed that A223395(n) = 2(A081057(n) + A081057(n+1)); this identity is not recorded anywhere.
- A052899 (same signature; R. Jehn's Oct 2024 comment on walks leaving a 4x4 board).

General theory (implies the result routinely but does not state it):
- D. Cvetković, M. Doob, H. Sachs, Spectra of Graphs (1980), Thm 1.11: the generating function of total walk counts, in terms of the characteristic polynomials of G and its complement.
- P. Rowlinson, "The main eigenvalues of a graph: a survey", Appl. Anal. Discrete Math. 1 (2007) 455–471.
- The classical spectrum of P_m□P_n, {2cos(iπ/(m+1)) + 2cos(jπ/(n+1))}.

Checked and not relevant (they concern a different Hardin family):
- R. Dougherty-Bliss & M. Kauers, "Hardinian Arrays", arXiv:2309.00487.
- G. Spahn & R. Dougherty-Bliss, "Rectangular Hardinian Arrays" (2024).

Web searches (arXiv, MathOverflow/MSE, general) found no explicit prior proof of the A223395 recurrence, g.f. or closed form.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a223395,
  author       = {{math0}},
  title        = {{A223395: walks on the 4 x 4 grid graph satisfy Hardin's recurrence, Barker's g.f. and closed form}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a223395}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
