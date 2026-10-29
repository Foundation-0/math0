# Ternary digits of 2^n: column k has least period 2*3^(k-1) and balanced digits for k ≥ 2

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A265210  
**Date:** 2026-10-24

## Result

Let T(n,k) be the k-th base-3 digit (from the least significant end) of 2^n, i.e. the digit at the place 3^(k-1). Column k consists of the rows n with 3^(k-1) ≤ 2^n. Then for every k ≥ 1: (i) p(k) = 2*3^(k-1) is a period of column k (T(n+p(k),k) = T(n,k) for every row n in the column), and no q with 0 < q < p(k) is a period; (ii) for k ≥ 2, in every block of p(k) consecutive rows m, ..., m+p(k)-1 (m in the column) the digits 0, 1 and 2 occur equally often (in fact exactly 2*3^(k-2) times each). This is Conjecture 1 of OEIS A265210 (L. Edson Jeffery, 2015).

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A265210](https://oeis.org/A265210) as [`Math0.Statements.A265210.statement`](../../lean/Math0/Statements/OEIS/A265210.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A265210.lean`](../../lean/Math0/Frontier/OEIS/A265210.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture 1: The sequence in column k is periodic, with period p(k) = 2*3^(k-1) = A008776(k-1), k >= 1, and in which the numbers 0,1,2 appear with equal frequency, for each k>1. (_L. Edson Jeffery_, Dec 04 2015)

Referees: E. de Faria and C. Tresser, "On Sloane's persistence problem", arXiv:1307.1188 (2013), Section 3.1, Lemma 3 and the paragraph after it. It shows 2^n mod 3^k has minimum period 2*3^(k-1) and that every allowable length-k ternary tail appears exactly once per period. This predates the Dec 2015 OEIS conjecture.
J. C. Lagarias, "Ternary expansions of powers of 2", J. London Math. Soc. 79 (2009) 562-588, arXiv:math/0512006, proof of Thm 1.4, eq. (3.3): 2 is a primitive root mod 3^k, so 2^n runs over all units mod 3^k.
Y. N. Aliyev, "Digits of powers of 2 in ternary numeral system", Notes Number Theory Discrete Math. 29(3) (2023) 474-485, Lemmas 3.2-3.3 and Observation I. It gives ord_{3^(n+1)} 2 = 2*3^n and shows the last-k-digit tails are periodic with period 2*3^(k-1) and run through all endings that don't end in 0.
Also standard textbook material (2 is a primitive root mod 3^k; e.g. LeVeque, Rosen) and the A008776 comment (J. Song, 2021).
OEIS A265210 itself (rev. #18, Dec 2015) still lists the statement as a conjecture and has no proof note. The single-column least-period refinement is not stated explicitly in these sources, but it is a short elementary consequence of the same facts.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a265210,
  author       = {{math0}},
  title        = {{Ternary digits of 2^n: column k has least period 2*3^(k-1) and balanced digits for k ≥ 2}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a265210}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
