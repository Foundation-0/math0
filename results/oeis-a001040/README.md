# Kurkov's rook-tour conjecture for A001040: 2·n!·a(n) counts opposite-line Hamiltonian paths of K_n □ K_2

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A001040  
**Date:** 2026-10-29

## Result

For every n ≥ 1, take the n × 2 board with squares (i,c), i ∈ [n], c ∈ {0,1}. Two different squares are a rook move apart when they share a row i or a line c (this is the graph K_n □ K_2). An open tour is a sequence that visits every square exactly once, with consecutive squares a rook move apart; a tour and its reversal count separately. Count the tours whose first and last squares lie on different lines. Kurkov conjectured that this count is 2·n!·a(n), where a(0)=0, a(1)=1 and a(m+1) = m·a(m) + a(m−1) (OEIS A001040). The statement is proved.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A001040](https://oeis.org/A001040) as [`Math0.Statements.A001040.statement`](../../lean/Math0/Statements/OEIS/A001040.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed before the proof, and CI checks that this order holds and that the frozen hash never changes. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A001040.lean`](../../lean/Math0/Frontier/OEIS/A001040.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C A001040 Conjecture: 2*n!*a(n) is the number of open tours by a rook on an (n X 2) chessboard which ends at the opposite line of length n. - _Mikhail Kurkov_, Nov 19 2019

Referees: OEIS sources (read from the local mirror):
- A001040: Kurkov's conjecture, Nov 19 2019, still marked as a conjecture in revision #140 of Oct 15 2026. The entry also has Paul Barry's 2004 formula a(n+1) = Sum_k C(n-k,k)(n-k)!/k!.
- A001053: the companion same-line conjecture, still open in revision #131 of Oct 22 2026.
- A096121: Hugo van der Sanden, 2004, counts directed Hamiltonian paths of the 2 x n rook graph. It contains:
  - the recurrence a(n+1) = n(n+1)(a(n)+a(n-1));
  - an unattributed "Further refinement" formula whose two summands are exactly the opposite-line and same-line counts, though they are not labeled as such;
  - Kurkov's Feb 2019 conjecture that the total is 2*n!*A102038(n);
  - Grossman's 2024 shoe-arrangement reading;
  - a citation of Y. Cha's 2011 FSU thesis, Example 5.1.1, which I could not open (HTTP 403).
- A102038: equals A001040 + A001053.
- A269565: Andrew Howroyd's array of directed Hamiltonian paths in K_n x K_m.
- A360878: Andrew Howroyd's May 2025 switch-decomposition formula for undirected paths.
- A276356 and A089039: the Hamiltonian-cycle analogue.

Other sources:
- MathOverflow q/469606 (Kurkov, Apr 2024), "On a A089039 and pair of sequences with simple recursion". I read it: Max Alekseyev proves only the cycle formula, using Zeilberger's algorithm.
- Web searches found no prior proof of the path refinement. They covered arXiv, MSE, MO, Google-style queries on rook tours of 2 x n boards, Hamiltonian paths of K_n x K_2, and the shoe or jealousy-free linear arrangements.

## Citation

```bibtex
@misc{math0:oeis-a001040,
  author       = {{math0}},
  title        = {{Kurkov's rook-tour conjecture for A001040: 2·n!·a(n) counts opposite-line Hamiltonian paths of K_n □ K_2}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a001040}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
