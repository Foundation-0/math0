# ∑_{i=1..n} C(2n-i-1, i-1)/i is never an integer for n > 1 (A175385)

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Number theory  
**Source problem:** OEIS A175385  
**Date:** 2026-10-18

## Result

For every integer n ≥ 2, the rational number S(n) = ∑_{i=1}^{n} C(2n-i-1, i-1)/i is not an integer. This is the Shevelev–Seidov conjecture from OEIS A175385.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A175385](https://oeis.org/A175385) as [`Math0.Statements.A175385.statement`](../../lean/Math0/Statements/OEIS/A175385.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A175385.lean`](../../lean/Math0/Frontier/OEIS/A175385.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: We conjecture that Sum_{i=1..n} ((1/i)*C(2n-i-1,i-1)) is not an integer for n>1. (Vladimir Shevelev, Zak Seidov, Apr 24 2010)

Referees: OEIS A175386 (cross-reference of A175385), comment by Ralf Stephan, May 25 2026: the conjecture was proved by an autonomous AI agent (AlphaProof Nexus). Lean file: https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/OEIS/oeis_175386_conjecture_0.lean (theorem target_theorem_0: for n > 1, the denominator of S(n) is not 1; checked, no sorry). Papers: G. Tsoukalas et al., "Advancing Mathematics Research with AI-Driven Formal Proof Search", arXiv:2605.22763 (May 2026); T. Adamczewski, "OEIS Open: How many conjectures can language models turn into theorems?", arXiv:2608.11941 (Aug 2026), cited by OEIS for the proof on p. 15, Appendix A. Classical implication: P. S. Bruckman, "Lucas Pseudoprimes Are Odd", Fibonacci Quarterly 32(2) (1994) 155-157 (https://www.mathstat.dal.ca/FQ/Scanned/32-2/bruckman2.pdf). No even composite N has N | L_N − 1, and with 2n·S(n) = L_{2n} − 1 this settles the conjecture. The A175385 entry itself (https://oeis.org/A175385, history up to #14, Mar 2023) records no proof.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a175385,
  author       = {{math0}},
  title        = {{∑_{i=1..n} C(2n-i-1, i-1)/i is never an integer for n > 1 (A175385)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a175385}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
