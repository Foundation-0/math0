# 3^(3^18) + 2 is divisible by 31^2, so Hilliard's squarefree conjecture (A083020) fails

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A083020  
**Date:** 2026-10-21

## Result

The conjecture (Cino Hilliard, 2003, OEIS A083020) says that 3^(3^n) + 2 is squarefree for every n ≥ 0. We prove it is false: 31^2 = 961 divides 3^(3^18) + 2, so that number is not squarefree.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A083020](https://oeis.org/A083020) as [`def statement`](../../lean/Math0/Statements/OEIS/A083020.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A083020.lean`](../../lean/Math0/Frontier/OEIS/A083020.lean) refutes (proves the negation of) it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C A083020 Conjecture: These numbers have no repeating factors or 3^(3^n) + 2 is squarefree. (entry by Cino Hilliard, May 31 2003)

Referees: I found no prior resolution. Sources checked: the OEIS A083020 entry (local mirror and https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A083/A083020.seq, revision #20 of Jan 04 2026, which still states the conjecture with no refutation), cross-referenced/related entries A055777, A129290, A129291, A113913, A140331 and A061678, R. Stephan's "Prove or Disprove. 100 Conjectures from the OEIS" (arXiv:math/0409509, which does not contain A083020), and primepuzzles.net Conjecture 107 (unrelated). I also ran web searches for "3^(3^n)+2 squarefree", "Cino Hilliard 3^3^n+2 seqfan" and "3^{3^n}+2 squarefree mathoverflow/stackexchange". None of these reported a counterexample or a proof.

## Citation

```bibtex
@misc{math0:oeis-a083020,
  author       = {{math0}},
  title        = {{3^(3^18) + 2 is divisible by 31^2, so Hilliard's squarefree conjecture (A083020) fails}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a083020}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
