# Kagey's order-10 recurrence for no-leaf subgraphs of the 5 × n grid holds

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A320099  
**Date:** 2026-10-29

## Result

Let a(n) be the number of edge subsets S of the 5 × n grid graph (all vertices kept) such that no vertex has degree exactly 1 in S (OEIS A320099). Then for every n > 10, a(n) = 103 a(n-1) + 1063 a(n-2) - 1873 a(n-3) - 20274 a(n-4) + 44071 a(n-5) - 10365 a(n-6) - 20208 a(n-7) + 5959 a(n-8) + 2300 a(n-9) - 500 a(n-10). This is an identity of integers.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A320099](https://oeis.org/A320099) as [`Math0.Statements.A320099.statement`](../../lean/Math0/Statements/OEIS/A320099.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A320099.lean`](../../lean/Math0/Frontier/OEIS/A320099.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A320099 Conjecture: a(n) = 103*a(n-1) + 1063*a(n-2) - 1873*a(n-3) - 20274*a(n-4) + 44071*a(n-5) - 10365*a(n-6) - 20208*a(n-7) + 5959*a(n-8) + 2300*a(n-9) - 500*a(n-10) for n > 10. (_Peter Kagey_, Oct 05 2018)

Referees: - OEIS A320099 (Peter Kagey, Oct 05 2018; latest revision #20, Jun 09 2019): the recurrence is still listed as "Conjecture", with no proof recorded.
- Related entries with no proof for 5×n: A320097 (4×n; Kagey's conjecture and Colin Barker's empirical generating function, both unproved in OEIS), A301976 (3×n, Barker's conjectures), A320101 (the n×k table) and A093129 (2×n).
- Prior formal work on a different sequence: the-omega-institute/trureturing issue #7458 and PR #7536 (Sep 13, 2026) give a Lean transfer-matrix proof of the 3×n recurrence (A301976). The repository has no issue or pull request for A320099 or A320097.
- Peter Kagey's problem page https://peterkagey.com/problems/083/ covers only the 2×n case.
- General transfer-matrix background: Raff, arXiv:0809.2551; Golin et al., ANALCO 2005.
- No arXiv, MathOverflow, Math StackExchange or SeqFan source proving or refuting the order-10 recurrence for the 5×n grid was found.

## Citation

```bibtex
@misc{math0:oeis-a320099,
  author       = {{math0}},
  title        = {{Kagey's order-10 recurrence for no-leaf subgraphs of the 5 × n grid holds}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a320099}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
