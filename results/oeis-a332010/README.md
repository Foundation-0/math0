# A332010: the average first letter of one-descent derangements has denominator 2^(n-2)

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A332010  
**Date:** 2026-10-19

## Result

For every n ≥ 2, take the derangements of {1, ..., n} (in one-line notation) that have exactly one descent. The average of their first letters, written in lowest terms, has denominator 2^(n-2). This is Kagey's conjecture T(n,1) = 2^(n-2) in OEIS A332010.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A332010](https://oeis.org/A332010) as [`Math0.Statements.A332010.statement`](../../lean/Math0/Statements/OEIS/A332010.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A332010.lean`](../../lean/Math0/Frontier/OEIS/A332010.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: T(n, 1) = 2^(n-2)." (A332010, entry by Peter Kagey, Feb 04 2020)

Referees: No prior resolution found.
- OEIS A332010 and A332009 (Peter Kagey, Feb 04 2020; last edits Mar 30 2024) still state "Conjecture: T(n,1) = 2^(n-2)" and "Conjecture: T(n,1) = A083329(n-1)", with no proof recorded in comments or %E lines. I checked both the local mirror and raw.githubusercontent oeisdata.
- Related known facts:
  - A219836 (Callan 2012; links to Fu–Lin–Zeng arXiv:1507.05184 and Alexandersson arXiv:2609.07325) gives a recurrence implying there are 2^(n-2) derangements with one descent. That is only the unreduced denominator.
  - M. Conger, arXiv math/0508112, proves E[π(1) | des = k] = k+1 over all permutations; this is the analogue for all permutations that the A332010 comment cites.
  - Kagey, arXiv:2112.05281, treats expected π(1) given k-cycles and does not address derangements by descents.
  - Eriksen–Freij–Wästlund, arXiv:0811.1925 / EJC 16 (2009) R32, and Han–Xin (2007) cover derangements with prescribed descent sets, with no first-letter averages.
- Searches of Math StackExchange, arXiv and SeqFan found nothing. MathOverflow was not reachable through the search tool.

## Citation

```bibtex
@misc{math0:oeis-a332010,
  author       = {{math0}},
  title        = {{A332010: the average first letter of one-descent derangements has denominator 2^(n-2)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a332010}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
