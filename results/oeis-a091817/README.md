# Quet's integrality conjecture for A091817 holds

**Classification:** First formal proof of a known result  
**Area:** Number theory  
**Source problem:** OEIS A091817  
**Date:** 2026-10-18

## Result

For every prime p >= 3, write H(p-3) = 1 + 1/2 + ... + 1/(p-3) = N/D in lowest terms (H(0) = 0/1). Then p divides 2N - 3D. Equivalently, every term a(n) = (2N - 3D)/p of OEIS A091817 (p the (n+1)-th prime, n >= 1) is an integer.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A091817](https://oeis.org/A091817) as [`Math0.Statements.A091817.statement`](../../lean/Math0/Statements/OEIS/A091817.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A091817.lean`](../../lean/Math0/Frontier/OEIS/A091817.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Leroy Quet conjectures that the terms are always integral. This is true for p < 3*10^4. (Entry: (2*numerator(H(p-3)) - 3*denominator(H(p-3)))/p, Bouayoun and Stephan, Mar 07 2004)

Referees: - OEIS A091817 and its history (oeis.org/history?seq=A091817): the conjecture is still stated as open, verified for p < 3*10^4, and has no proof note.
- Classical source: H(p-1) ≡ 0 (mod p) (Wolstenholme 1862; Hardy & Wright, An Introduction to the Theory of Numbers, Thm 115).
- Explicit reflection congruence H_{p-k} ≡ H_{k-1} (mod p), 1 <= k <= p-1: Z.-W. Sun & L.-L. Zhao, "Arithmetic theory of harmonic numbers (II)", Colloq. Math. 130 (2013), 67-78, arXiv:0911.4433 (proof of (2.2)). Taking k = 3 gives H_{p-3} ≡ 3/2 (mod p), which settles the conjecture at once.
- The same lemma is cited in arXiv:1108.2361 (Lemma 2.1 of its ref. [13]) and arXiv:1803.02966.
- Analogous k = 2 fact in OEIS A064169 (Adamchuk, Jun 09 2006: p divides a(p-2)).
- No prior formalization found:
  - not in google-deepmind/formal-conjectures (checked locally at commit c77fdd4);
  - not among the OEIS Open benchmark statements (Adamczewski, arXiv:2608.11941);
  - no other formal proof turned up in searches.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a091817,
  author       = {{math0}},
  title        = {{Quet's integrality conjecture for A091817 holds}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a091817}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
