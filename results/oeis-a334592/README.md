# Records of the XOR-triangle zero count A334592 are exactly the powers of two

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A334592  
**Date:** 2026-10-26

## Result

Let a(n) be the number of zeros in the XOR-triangle whose top row is the binary expansion of n, with the most significant bit first. Each later row is the XOR of adjacent pairs in the row above, down to a row of length 1. Then n is a record position (n >= 1 and a(m) < a(n) for all 1 <= m < n) if and only if n = 2^k for some k >= 0.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A334592](https://oeis.org/A334592) as [`Math0.Statements.A334592.statement`](../../lean/Math0/Statements/OEIS/A334592.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A334592.lean`](../../lean/Math0/Frontier/OEIS/A334592.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C A334592 Conjecture: Records occur at powers of two. (entry by _Peter Kagey_, May 07 2020)

Referees: The key fact is published. H. Harborth, "Solution of Steinhaus's problem with plus and minus signs", J. Combin. Theory Ser. A 12 (1972) 253-259, is credited with observing that the minimum weight of a nonzero binary Steinhaus triangle of size n is n. J. M. Brunat and M. Maureso prove it in "Small and large weights in Steinhaus triangles" (arXiv:1707.06698, 2017), Theorem 4.4: for n >= 4, w1 = n and W1 = {1^n, 10^(n-1), 0^(n-1)1}. Their extended abstract is "Extreme weights in Steinhaus triangles", Electron. Notes Discrete Math. 54 (2016) 349-354. The A334592 record conjecture is an immediate corollary: a(n) <= T(L) - L = T(L-1) = a(2^(L-1)). The OEIS entries A334592 and A334593 (local mirror, still at #19 / #22 from May 2020) have no %E note marking the conjecture resolved. The MathOverflow thread q/359138 linked from the entry could not be fetched. Other sources seen: arXiv:1702.03236 (Chappelon, periodic balanced binary triangles) and arXiv:2508.05159 (balanced Steinhaus triangles, which mentions Chang 1983 on the smallest weights).

## Citation

```bibtex
@misc{math0:oeis-a334592,
  author       = {{math0}},
  title        = {{Records of the XOR-triangle zero count A334592 are exactly the powers of two}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a334592}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
