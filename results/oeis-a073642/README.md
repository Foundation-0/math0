# Yanev's identity for A073642 (sum of the positions of the 1-bits)

**Classification:** New result (open problem settled)  
**Area:** Sequences and series  
**Source problem:** OEIS A073642  
**Date:** 2026-10-20

## Result

Let a(n) be the sum of the positions of the 1-bits of n (if n = 2^b + 2^c + ... with distinct exponents, then a(n) = b + c + ...). Let A011371(n) = n - s(n), where s(n) is the number of 1's in the binary expansion of n; by Legendre's formula this equals v2(n!). Let A007814(k) = v2(k), the 2-adic valuation. Then for every n > 0, a(n) = (3*A011371(n) - Sum_{k=1..n} A007814(k)^2)/2, with the right-hand side computed exactly in Q.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A073642](https://oeis.org/A073642) as [`Math0.Statements.A073642.statement`](../../lean/Math0/Statements/OEIS/A073642.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A073642.lean`](../../lean/Math0/Frontier/OEIS/A073642.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: A073642 (if n = 2^b+2^c+..., a(n)=b+c+...): "Conjecture: a(n) = (3*A011371(n) - Sum_{k=1..n} A007814(k)^2)/2 for n > 0. - _Velin Yanev_, Sep 09 2017". Siblings: A059906: "Conjecture: a(n) = n - (1/2)*Sum_{k=1..n} (sqrt(2)^A007814(k) + (-sqrt(2))^A007814(k)) = -Sum_{k=1..n} (-1)^k * 2^floor(k/2) * floor(n/2^k). - _Velin Yanev_, Dec 01 2016". A048702: "Conjecture: a(n) = 2^floor(log_2(n)) * Sum_{i=1..n} 1/(2^v_2(i))" and "Conjecture: a(n) = n*2^floor(log_2(n)) - Sum_{i=1..floor(log_2(n))} 2^(floor(log_2(n)) - i)*floor(n/(2^i))."

Referees: I found no prior resolution.
- **OEIS entry.** A073642 (#121, Jul 05 2026) still lists "Conjecture ... Velin Yanev, Sep 09 2017", with no proof note or %E edit about it.
- **Related OEIS entries.** A011371, A007814, A029931, A115364, A198192 and A198193 contain no such identity, and no OEIS sequence holds the partial sums of A007814(k)^2.
- **Fried, "Proofs of some conjectures of Yanev" (2025).** This OEIS attachment covers only A000188, A001157 and A006519, and A073642 does not link to it.
- **Fried's OEIS papers.** None of these mentions A073642: arXiv:2410.07237, JIS 28 (2025) Art. 25.4.3, JIS 29 (2026) Art. 26.1.8, and arXiv:2607.24832.
- **Formalization datasets.** A073642 is not in google-deepmind/formal-conjectures, in Epoch's OEIS Open / LeanOpenProblems (arXiv:2608.11941), or in alphaproof-nexus-results.
- **Ingredients of the proof.** These are classical: Legendre's formula v2(n!) = n - s2(n), and Sum_{k<=n} f(v2(k)) = Sum_j (f(j)-f(j-1)) floor(n/2^j). The identity also follows from Gutkovskiy's 2019 g.f. in the entry.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a073642,
  author       = {{math0}},
  title        = {{Yanev's identity for A073642 (sum of the positions of the 1-bits)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a073642}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
