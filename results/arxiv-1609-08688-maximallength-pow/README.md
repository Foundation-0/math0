# Supermultiplicativity of F gives arbitrarily large m with F(m) ≥ m^α (Gowers–Long)

**Classification:** First formal proof of a known result  
**Area:** Combinatorics  
**Source problem:** arXiv:1609.08688  
**Date:** 2026-10-17

## Result

Let F(n) be the largest length of a sequence of triples in {1,…,n}^3 that is 2-increasing: every earlier triple is strictly smaller than every later one in at least two of the three coordinates. Let n > 1 be a natural number and e a real number with F(n) = n^e. Then (m : ℝ)^e ≤ F(m) for arbitrarily large natural numbers m, i.e. ∃ᶠ m in atTop.

## Verification

The Lean file [`lean/Math0/Arxiv/Arxiv_1609_08688_maximalLength_pow.lean`](../../lean/Math0/Arxiv/Arxiv_1609_08688_maximalLength_pow.lean) proves the upstream statement [`Arxiv.«1609.08688».maximalLength_pow`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Arxiv/1609.08688/sIncreasingrTuples.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

W. T. Gowers and J. Long, "The length of an s-increasing sequence of r-tuples", arXiv:1609.08688; Combinatorics, Probability and Computing 30 (2021), 686–721. Section 1 notes that F is supermultiplicative, F(mn) ≥ F(m)F(n), using the lexicographic product of sequences. So F(n) = n^α implies F(n^k) ≥ n^{αk}, which gives arbitrarily large m with F(m) ≥ m^α. This is the upstream statement `maximalLength_pow`, which is tagged "research solved" and was proved upstream only by sorry. I found no existing Lean formalization.

## Citation

```bibtex
@misc{math0:arxiv-1609-08688-maximallength-pow,
  author       = {{math0}},
  title        = {{Supermultiplicativity of F gives arbitrarily large m with F(m) ≥ m^α (Gowers–Long)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/arxiv-1609-08688-maximallength-pow}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
