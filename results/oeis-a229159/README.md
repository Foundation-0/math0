# Every odd prime is a side of a Heronian triangle (A229159)

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A229159  
**Date:** 2026-10-18

## Result

For every prime p > 2 there are natural numbers x, y, z, A such that x, y, z satisfy the strict triangle inequalities (x < y + z, y < x + z, z < x + y), Heron's formula 16 A^2 = (x+y+z)(-x+y+z)(x-y+z)(x+y-z) holds in Z, and at least one of x, y, z equals p.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A229159](https://oeis.org/A229159) as [`Math0.Statements.A229159.statement`](../../lean/Math0/Statements/OEIS/A229159.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A229159.lean`](../../lean/Math0/Frontier/OEIS/A229159.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: for all prime p > 2 there exists an integer-sided triangle with integer area where at least one side is of length p." (entry by _Michel Lagneau_, Sep 17 2013)

Referees: Classical formula (n, (n^2-1)/2, (n^2+1)/2) for odd n, credited to the Pythagoreans (Proclus, Commentary on Euclid's Elements I.47; H. Eves, An Introduction to the History of Mathematics, sec. 3-4; cf. Euclid, Elements X, Lemma 1 before Prop. 29). OEIS A046079, comment by Richard R. Forberg, May 31 2013: "For odd n: L = (n^2-1)/2 and H = L+1". In the same entry, Ant King (Jan 29 2011) notes that for n > 2 the n with exactly one Pythagorean triangle on leg n are the primes and their doubles. OEIS A042965 (Sloane, May 30 2014): the primes that are a difference of two squares are exactly the odd primes. Related: A009004 (short legs of Pythagorean triangles). Mathlib has the Pythagorean triple classification (Mathlib/NumberTheory/PythagoreanTriples.lean) but not this Heronian statement. I found no source that addresses A229159's conjecture directly; it is resolved immediately by the classical formula.

## Citation

```bibtex
@misc{math0:oeis-a229159,
  author       = {{math0}},
  title        = {{Every odd prime is a side of a Heronian triangle (A229159)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a229159}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
