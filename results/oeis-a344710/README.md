# A344710: non-obtuse lattice triangles with sides >= sqrt(n) have |det| > (sqrt 3 / 2) n

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A344710  
**Date:** 2026-10-18

## Result

For every n >= 1, let a(n) be the least value of |det(B-A, C-A)| (twice the area) over lattice triangles ABC in Z^2 that are non-degenerate and non-obtuse and have all three squared side lengths >= n. Then sqrt(3/4) * n < a(n). This is Waldmann's conjectured inequality in OEIS A344710.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A344710](https://oeis.org/A344710) as [`Math0.Statements.A344710.statement`](../../lean/Math0/Statements/OEIS/A344710.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A344710.lean`](../../lean/Math0/Frontier/OEIS/A344710.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Formula: "a(n) > sqrt(3/4)*n (conjectured)." Comment: "Conjectured next terms (from the conjectured inequality a(n) > sqrt(3/4)*n) are a(50,...,64) ?= 45, 48, 48, 52, 55, 55, 55, 55, 55, 56, 56, 56, 56, 56, 56." (entry by _Jonathan F. Waldmann_, May 26 2021). A344845 has the same inequality a(n) > sqrt(3/4)*m (conjectured), by the same author, May 29 2021.

Referees: A. Mazel, I. Stuhl, Y. Suhov, "High-density hard-core model on Z^2 and norm equations in ring Z[...]", arXiv:1909.11648 (v1 25 Sep 2019; v3 22 Jun 2023). Lemma 3.4.4, eq. (3.1): sqrt(3)D^2/2 < S(D) < sqrt(3)D^2/2 + sqrt(2)D. S(D) is twice the minimal area of non-obtuse Z^2-triangles with sides >= D, so A344710(n) = S(sqrt n). The paper calls the lower bound "obvious". D. Krachun, "Triangles on Z^2 and sliding phenomenon" / "Extreme Gibbs measures for high-density hard-core model on Z^2", arXiv:1912.07566 (Dec 2019 / Jun 2020). Definition 2.1 gives the same S(D) for all D > 0, and Theorem 2 gives S(D) = (sqrt3/2)D^2 + O(D^{4/5}). The underlying inequality is the classical one: a non-obtuse triangle with all sides >= D has area >= (sqrt3/4)D^2, since area = (1/2)ab sin C with the largest angle C in [60,90] degrees. Equality would need an equilateral lattice triangle, and Z^2 has none. OEIS A344710 and A344845 (local mirror and GitHub, revisions #84/#52 of Feb 2022) still list the inequality as conjectured.

## Citation

```bibtex
@misc{math0:oeis-a344710,
  author       = {{math0}},
  title        = {{A344710: non-obtuse lattice triangles with sides >= sqrt(n) have |det| > (sqrt 3 / 2) n}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a344710}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
