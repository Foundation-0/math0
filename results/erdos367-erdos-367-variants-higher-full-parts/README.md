# Erdős 367 (higher full parts): the product of r-full parts beats n^(1+ε) infinitely often

**Classification:** First formal proof of a known result  
**Area:** Number theory  
**Source problem:** Erdős Problem #367  
**Date:** 2026-10-17

## Result

Let $B_r(m)=\prod_{p^a\,\|\,m,\ a\ge r} p^a$ be the $r$-full part of $m$ (with $B_r(0)=1$). For all integers $r\ge 3$ and $k\ge 2$ there is some $\varepsilon=\varepsilon(r,k)>0$ such that
$$\limsup_{n\to\infty}\frac{\prod_{n\le m<n+k}B_r(m)}{n^{1+\varepsilon}}=\infty$$
(in the extended reals; the upstream statement has the ratio as a real number cast to EReal). We prove this with $\varepsilon = 1/(2r)$.

## Verification

The Lean file [`lean/Math0/ErdosProblems/Erdos367_erdos_367_variants_higher_full_parts.lean`](../../lean/Math0/ErdosProblems/Erdos367_erdos_367_variants_higher_full_parts.lean) proves the upstream statement [`Erdos367.erdos_367.variants.higher_full_parts`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/367.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research open`). Its final command `#math0_proves` checks that our theorem's type is syntactically identical to the upstream statement and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

- Erdős–Graham [ErGr80, p.68]; erdosproblems.com/367, listed as open, with formal_status "unformalized" in problems.yaml.
- Forum thread erdosproblems.com/forum/thread/367:
  - Woett/van Doorn, 20 Nov 2025, post #1766: proposes the reading ε = ε(r,k).
  - Scott Hughes, 10 Jun 2026, post #6910: claims an affirmative answer for all r,k ≥ 2 with any ε < (r+1)/r². His construction is n = (t^r−1)^r for odd r and (t^r+1)^r − 1 for even r. His accompanying paper is "Powerful parts of consecutive integers and Davenport–Zannier polynomials".
- Hughes's partial Lean formalization, github.com/scottdhughes/erdos367 (module RFullLowerBound): covers only the odd-r pointwise inequality, with no even r and no limsup statement.
- formal_conjectures commit 2e3d4a09 (Sep 2026): made ε existential and explicitly mentions Hughes's resolution. - Erdős & Graham, Old and New Problems and Results in Combinatorial Number Theory (1980), p.68; the source of the B_r question.
- erdosproblems.com/367, statement last edited 23 Mar 2026: still literal "every ε>0" wording; status open (also open in local problems.yaml, formalized 2026-08-20).
- Forum thread erdosproblems.com/forum/thread/367:
  - post-1766, Woett (van Doorn), 20 Nov 2025: proposes the ε=ε(r,k) reading.
  - post-6910, ScottHughes, 10 Jun 2026: claims an affirmative resolution for all r,k≥2 with any ε<(r+1)/r², via n=(t^r−1)^r (odd r) and n=(t^r+1)^r−1 (even r). These constructions trivially give ε<1/r.
- github.com/scottdhughes/erdos367:
  - 

## Citation

```bibtex
@misc{math0:erdos367-erdos-367-variants-higher-full-parts,
  author       = {{math0}},
  title        = {{Erdős 367 (higher full parts): the product of r-full parts beats n^(1+ε) infinitely often}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/erdos367-erdos-367-variants-higher-full-parts}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
