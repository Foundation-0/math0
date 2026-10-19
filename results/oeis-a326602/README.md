# A326602: a(n) is odd iff n is a square

**Classification:** New result (open problem settled)  
**Area:** Sequences and series  
**Source problem:** OEIS A326602  
**Date:** 2026-10-18

## Result

Let A(x) = Sum_{n>=0} (x^(2n-1)+1)^n x^n / (1+x^(2n+1))^(n+1) in Z[[x]] (the n=0 summand is 1/(1+x)), and let a(n) = [x^(2n)] A(x). Then for every n >= 0, a(n) is odd if and only if n is a perfect square (n = k^2 for some k >= 0, so 0 counts as a square).

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A326602](https://oeis.org/A326602) as [`Math0.Statements.A326602.statement`](../../lean/Math0/Statements/OEIS/A326602.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A326602.lean`](../../lean/Math0/Frontier/OEIS/A326602.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: A326602 (G.f.: Sum_{n>=0} (x^(2n-1)+1)^n x^n/(1+x^(2n+1))^(n+1), an even function; a(n) = [x^(2n)]): "a(n) is odd iff n is square (conjecture)." (_Paul D. Hanna_, Aug 08 2019). Same family: A323689 (Sum (x^n+i)^n/(1+i x^n)^(n+1)): "Odd terms occur only at n = k^2 for k >= 0 (conjecture);" (Hanna, Feb 14 2019); A323675 (Sum x^n (x^n+i)^n/(1+i x^(n+1))^(n+1)): "It appears that odd terms occur only at n*(n+1)" (Hanna, Feb 10 2019); A323690 (Sum (x^(n+1)+i)^n/(1+i x^n)^(n+1)): "the first column consists of all the odd terms" (triangle rows start at n(n+1)) (Hanna, Feb 13 2019).

Referees: No prior resolution of A326602 found.
- OEIS A326602 (local mirror and upstream oeisdata) is still at revision #19, Aug 11 2019, and still says "a(n) is odd iff n is square (conjecture)". No later edits or proof links.

Closest prior work (same involution or parity method, different sequences):
- A323557 (odd terms only at n(n+1)): proved by AlphaProof Nexus (github.com/google-deepmind/alphaproof-nexus-results, APNOutputs/OEIS/oeis_323557_conjecture_0.lean) and in T. Adamczewski, "OEIS Open: How many conjectures can language models turn into theorems?", arXiv:2608.11941, Appendix A. Also R. Stephan's comment of Jun 01 2026 on A323557.
- A325046: S. Fried, "Proof of a conjecture stated in A325046" (OEIS a325046.pdf, 2025), and "Further proofs of conjectures from the OEIS", arXiv:2607.24832, Sec. 3.8 / Thm 50.

Neither arXiv paper mentions A326602, and A326602 is absent from google-deepmind/formal-conjectures, so it was not in the Tsoukalas et al. or OEIS Open benchmark sets.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a326602,
  author       = {{math0}},
  title        = {{A326602: a(n) is odd iff n is a square}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a326602}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
