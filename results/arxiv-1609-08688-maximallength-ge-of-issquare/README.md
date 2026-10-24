# Gowers–Long lower bound: F(k²) ≥ k³ for 2-increasing sequences of triples

**Classification:** First formal proof of a known result  
**Area:** Combinatorics  
**Source problem:** arXiv:1609.08688  
**Date:** 2026-10-17

## Result

Say that a triple a = (a_1,a_2,a_3) is 2-less than b = (b_1,b_2,b_3) if a_i < b_i for at least two coordinates i. A finite sequence of triples is 2-increasing if every earlier term is 2-less than every later term. Let F(n) be the largest length of a 2-increasing sequence of triples with all coordinates in {1,...,n}. (Formally, F(n) is the sSup in ℕ of the set of such lengths.) If n is a perfect square then (√n)^3 ≤ F(n), i.e. F(k^2) ≥ k^3 for every natural number k.

## Verification

The Lean file [`lean/Math0/Arxiv/Arxiv_1609_08688_maximalLength_ge_of_isSquare.lean`](../../lean/Math0/Arxiv/Arxiv_1609_08688_maximalLength_ge_of_isSquare.lean) proves the upstream statement [`Arxiv.«1609.08688».maximalLength_ge_of_isSquare`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Arxiv/1609.08688/sIncreasingrTuples.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research solved`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

The source is W. T. Gowers and J. Long, "The length of an s-increasing sequence of r-tuples", arXiv:1609.08688, published in Combinatorics, Probability and Computing 30 (2021), 686–721. Proposition 1.4 states F(n) ≤ n^2 for all n, and F(n) ≥ n^{3/2} when n is a perfect square, using the lexicographic construction of triples ((a,b),(a,c),(b,c)). The result is known and elementary. In formal-conjectures, both the pinned checkout and the latest upstream HEAD (d9ce556, 2026-10-17) still leave `maximalLength_ge_of_isSquare` as `sorry`. The upper bound `maximalLength_le` is already proved upstream. I found no existing Lean proof of the lower bound.

## Citation

```bibtex
@misc{math0:arxiv-1609-08688-maximallength-ge-of-issquare,
  author       = {{math0}},
  title        = {{Gowers–Long lower bound: F(k²) ≥ k³ for 2-increasing sequences of triples}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/arxiv-1609-08688-maximallength-ge-of-issquare}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
