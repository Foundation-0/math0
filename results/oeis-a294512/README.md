# Lang's conjecture a(n) = A250400(n+1)/(n+1) for A294512 fails at n = 164

**Classification:** New result (open problem settled)  
**Area:** Sequences and series  
**Source problem:** OEIS A294512  
**Date:** 2026-10-18

## Result

Let V(n) = sum_{k=0}^{n} 1/((k+1)(3k+1)) and let a(n) be the denominator of V(n) in lowest terms (OEIS A294512). Let A250400(m) be the numerator, in lowest terms, of the harmonic mean m / sum_{j=1}^{m} 1/(j(3j-2)) of the first m octagonal numbers. Lang's conjecture (A294512, FORMULA, 2017) says that A250400(n+1)/(n+1) = a(n) in Q for every n >= 0. This is false. The first failure is at n = 164, where A250400(165)/165 = a(164)/11.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A294512](https://oeis.org/A294512) as [`Math0.Statements.A294512.statement`](../../lean/Math0/Statements/OEIS/A294512.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A294512.lean`](../../lean/Math0/Frontier/OEIS/A294512.lean) refutes (proves the negation of) it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: A294512 (Denominators of partial sums of the reciprocals of octagonal numbers), FORMULA: "a(n) = A250400(n+1)/(n+1), n >= 0. [conjecture]." (entry by _Wolfdieter Lang_, Nov 01 2017). Companion A294513 (Lang, Nov 02 2017): "a(n) = 2*A250327(n+1)/(n+1) [conjecture]."

Referees: OEIS A294512 (W. Lang, Nov 01 2017; history #1-#13, last edit Nov 12 2017, formula "a(n) = A250400(n+1)/(n+1), n >= 0. [conjecture]" still present). OEIS A250401 (C. Barker 2014; Lang comment Nov 01 2017 conditional on "n+1 divides A250400(n+1)", still present, history #1-#19). OEIS A250400 (C. Barker, Nov 21 2014, b-file n=1..1000, which contains A250400(165) = 15*a(164)). Sibling Lang conjectures in A294513, A294515 are unresolved there too. Not in google-deepmind/formal-conjectures (FormalConjectures/OEIS); not in Tsoukalas et al. / Epoch OEIS Open (arXiv 2608.11941; github.com/epoch-research/LeanOpenProblems-results; SeqFan thread "Language models resolving OEIS conjectures", Aug 2026). No SeqFan, MathOverflow, MSE or arXiv discussion found. Independent check: the failures for n < 3000 are exactly n = 164 (gcd 11) and n = 2413 (gcd 17).

## Citation

```bibtex
@misc{math0:oeis-a294512,
  author       = {{math0}},
  title        = {{Lang's conjecture a(n) = A250400(n+1)/(n+1) for A294512 fails at n = 164}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a294512}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
