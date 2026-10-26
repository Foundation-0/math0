# The row-LCM of denominators of the cube of the mean matrix is n · lcm(1..n)²

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A119936  
**Date:** 2026-10-24

## Result

Let A be the lower-triangular matrix with A(i,j) = 1/i for j ≤ i and 0 otherwise. Its cube has entries r(n,m) = (1/n) Σ_{m ≤ l ≤ k ≤ n} 1/(k l) for 1 ≤ m ≤ n. Let a(n) be the lcm, over m = 1..n, of the reduced denominators of r(n,m). Then for every n ≥ 1, a(n)/n³ = A002944(n)² = (lcm(1..n)/n)². Equivalently, a(n) = n · lcm(1,…,n)². This is the equation that OEIS A119936 (Wolfdieter Lang, 2006) labels a conjecture.

## Assessment

The divisibility a(n) | n·lcm(1..n)^2 is immediate, because each product kl divides lcm(1..n)^2. For the reverse divisibility, take each prime p separately and use the column m equal to the largest multiple of p^e that is at most n, where p^e ≤ n < p^{e+1}. In that column, k = l = m is the only term whose valuation reaches -2e, so the full p-power survives in the denominator. This is the textbook unique-minimal-valuation trick used for harmonic sums. The whole argument fits in under a page, and the scout record set it out almost in full before any formalization, so it is a short, standard proof and not a new idea.

*Follows from:* The standard p-adic argument in which a sum has a single term of minimal valuation, the same idea as the classical proof that the harmonic numbers H_n are not integers (Taeisinger/Kürschák), applied to the explicit formula r(n,m) = (1/n) Σ_{m≤l≤k≤n} 1/(kl) and to v_p(lcm(1..n)) = floor(log_p n).

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A119936](https://oeis.org/A119936) as [`Math0.Statements.A119936.statement`](../../lean/Math0/Statements/OEIS/A119936.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A119936.lean`](../../lean/Math0/Frontier/OEIS/A119936.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %F A119936 a(n)/n^3 = A027451(n) = A002944(n)^2 (the second equation is a conjecture). (Wolfdieter Lang, Jul 20 2006)

Referees: I found no prior proof or counterexample.
- OEIS A119936 (Lang 2006, edit #22 Nov 2019) still calls a(n)/n^3 = A002944(n)^2 a conjecture.
- A027451 states (lcm(1..n)/n)^2 as a formula (Meijer, 2009) without proof. Detlefs' comment there begins "It appears".
- A120078 and A120079 say "conjectured to be A027451".
- Crowley, arXiv:1207.1126, says only that a denominator "appears to be" A119936.
- Fried's OEIS-conjecture series does not mention A119936 or the related sequences: arXiv:2410.07237 / JIS 25.4.3, JIS 26.1.8, arXiv:2606.09913, arXiv:2607.24832.
- Sloane, math/0409509: no mention.
- Web, MSE/MO and SeqFan searches turned up nothing.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a119936,
  author       = {{math0}},
  title        = {{The row-LCM of denominators of the cube of the mean matrix is n · lcm(1..n)²}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a119936}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
