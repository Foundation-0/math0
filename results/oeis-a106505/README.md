# A106505: common sides of A/2A primitive triangles are periodic mod 8, so a(n+5) = a(n) + 8

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A106505  
**Date:** 2026-10-19

## Result

Let IsSide(c) mean there are natural numbers x, y such that x, y, c are the sides of a non-degenerate triangle in which the angle opposite y is twice the angle opposite x, and gcd(x, y, c) = 1. Let a(n) be the n-th smallest such c (1-indexed): 5, 7, 9, 11, 13, 15, 16, 17, ... Then a(n+5) = a(n) + 8 for every n > 2 (Ralf Stephan's conjecture in OEIS A106505).

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A106505](https://oeis.org/A106505) as [`Math0.Statements.A106505.statement`](../../lean/Math0/Statements/OEIS/A106505.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A106505.lean`](../../lean/Math0/Frontier/OEIS/A106505.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: for n>2, a(n+5) = a(n) + 8. - _Ralf Stephan_, Nov 16 2010." Also: "Empirical g.f.: ... - _Colin Barker_, Oct 05 2013"

Referees: No earlier proof found. OEIS A106505 (GitHub oeisdata main, rev #21, Apr 23 2021) still states it as a conjecture (Ralf Stephan, Nov 16 2010), with an empirical g.f. by Colin Barker (2013). OEIS A321499 (M. F. Hasler, Nov 2018; rev #24, Feb 2025) proves that {d²(2m+d)} = odd numbers > 1 together with multiples of 8 > 8, and records a(n+5) = a(n) + 8 for A321499 (D. A. Corneth). It still says "Cf. A106505 (conjectured to be the sequence without the 3)". The closely related A321501 complement analysis (Hasler) is also there. Related OEIS entries: A343063 and A343064 (B. Schott, 2021), which give the parametrization a = m² − k², b = mk, c = k² with gcd(m,k) = 1 and k < m < 2k, but no set characterization; and A229849, which says A106505 "seems" to give those values. Parametrization background: M. N. Deshpande, Math. Gazette (2002); K. Zelator, arXiv 1208.0497; R. S. Luthar (1984). None of these addresses the conjecture. Not covered in S. Fried, arXiv 2410.07237 or arXiv 2607.24832, nor in Adamczewski's OEIS Open benchmark (arXiv 2608.11941), which uses the Tsoukalas et al. dataset in epoch-research/LeanOpenProblems; also absent from google-deepmind/formal-conjectures.

## Citation

```bibtex
@misc{math0:oeis-a106505,
  author       = {{math0}},
  title        = {{A106505: common sides of A/2A primitive triangles are periodic mod 8, so a(n+5) = a(n) + 8}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a106505}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
