# The Johnson graph J(18, 9) has chromatic number at least 11

**Classification:** First formal proof of a known result  
**Area:** Combinatorics  
**Source problem:** Erdős Problem #835  
**Date:** 2026-10-17

## Result

Let J(18, 9) be the Johnson graph. Its vertices are the 9-element subsets of an 18-element set, and two vertices are adjacent when they share exactly 8 elements. Then χ(J(18, 9)) > 9 + 1, so χ(J(18, 9)) ≥ 11. This is the case k = 9 of Erdős Problem 835, which asks whether χ(J(2k, k)) = k + 1 for some k > 2.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos835_johnsonGraph_18_9_chromaticNumber.lean`](../../lean/Math0/ErdosProblems/Erdos835_johnsonGraph_18_9_chromaticNumber.lean) proves the upstream statement [`Erdos835.johnsonGraph_18_9_chromaticNumber`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/835.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Erdős Problem 835 (erdosproblems.com/835). problems.yaml lists its status as "verifiable" and its formal_status as "unformalized"; there is no "(Lean)" marker. The general question stays open, but the k = 9 case is known. The odd-k lower bound χ(J(2k,k)) > k+1 follows from Johnson's bound for constant-weight codes (S. M. Johnson, 1962) through α(J(2k,k)) ≤ A(2k,4,k). For k = 9 this gives α ≤ 4420 and χ ≥ ⌈48620/4420⌉ = 11. The bound is tabulated on A. E. Brouwer's Johnson-graphs page (aeb.win.tue.nl/graphs/Johnson.html). Ma and Tang (2025, github.com/QuanyuTang/erdos-problem-835) prove χ(J(2k,k)) > k+1 for every k > 2 with k+1 composite, which includes k = 9. No previous sorry-free Lean proof was found: in formal_conjectures, indepNum_johnson_le_johnsonBound is sorry, and every upstream lower-bound statement depends on it or is itself sorry.

## Citation

```bibtex
@misc{math0:erdos835-johnsongraph-18-9-chromaticnumber,
  author       = {{math0}},
  title        = {{The Johnson graph J(18, 9) has chromatic number at least 11}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos835-johnsongraph-18-9-chromaticnumber}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
