# OEIS A363482: apart from 49, every denominator of 1/(2-3/(3-4/(...(n-1)-n/(-5)))) is 1 or a prime

**Classification:** New result (open problem settled)  
**Area:** Number theory  
**Source problem:** OEIS A363482  
**Date:** 2026-10-18

## Result

For n >= 3 let t_n = -5 and t_k = k - (k+1)/t_{k+1} for k = n-1, ..., 2. Let a(n) be the denominator, in lowest terms, of 1/t_2 = 1/(2-3/(3-4/(...(n-1)-n/(-5)))). Then for every n >= 3, either a(n) = 49, or a(n) = 1, or a(n) is prime. This is Bouras' conjecture (2023). The value 49 occurs only at n = 6.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A363482](https://oeis.org/A363482) as [`Math0.Statements.A363482.statement`](../../lean/Math0/Statements/OEIS/A363482.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A363482.lean`](../../lean/Math0/Frontier/OEIS/A363482.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: Except for 49, every term of this sequence is either a prime or 1. (Mohammed Bouras, Jun 04 2023; 'The conjecture holds through n=10000' - Bill McEachen, Jul 08 2025)

Referees: No prior resolution of A363482 found. Sources checked:
- OEIS A363482 (local mirror, identical to upstream oeisdata #29, Jul 13 2025): conjecture plus a numerical check to n = 10000 (McEachen), no proof.
- Bouras, "A New Primes-Generating Sequence", arXiv:2509.09745 (2025): lists A363482 as the k=5 case of n^2+(k-2)n-k, with observations only.
- Epoch OEIS Open benchmark (github.com/epoch-research/LeanOpenProblems-results, metadata/oeis/conjectures.json): A363482 is absent.
- google-deepmind/formal-conjectures: no A363482 file.
- google-deepmind/alphaproof-nexus-results: no A363482 file.

Related prior results on sibling sequences:
- A363102 (endpoint -2) proved: T. Adamczewski, "OEIS Open: How many conjectures can language models turn into theorems?", arXiv:2608.11941 (2026), Appendix A; also AlphaProof Nexus oeis_a363102_conjecture_1.lean.
- A356247 (endpoint -1) proved: B. Cloitre, "On the sequence A356247" (2025, OEIS-hosted PDF a356247_1.pdf; not readable here).
- A363347 (endpoint -4) conjectures 1-2 proved: AlphaProof Nexus oeis_363347_conjecture_2.lean; Adamczewski, arXiv:2608.11941.

The proof here follows the same template as the A363102 proof.

## Citation

```bibtex
@misc{math0:oeis-a363482,
  author       = {{math0}},
  title        = {{OEIS A363482: apart from 49, every denominator of 1/(2-3/(3-4/(...(n-1)-n/(-5)))) is 1 or a prime}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a363482}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
