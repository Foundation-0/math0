# Even and odd legs with odd prime factors ≡ 3 (mod 4): a(n)/n → π (A354571, A354570)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A354571  
**Date:** 2026-10-20

## Result

A354571 lists the even legs k of primitive Pythagorean triangles in increasing order, each repeated once per triangle. A leg is included when every odd prime factor of k is ≡ 3 (mod 4) and k has at least one odd prime factor. A354570 lists the odd legs k in the same way, for k whose prime factors are all ≡ 3 (mod 4). Selle's conjecture says that a(n)/n → π for A354571 and A354570(n)/n → π. The formal `statement` is the conjunction of these two limits, with each sequence read as the n-th term of the list where k appears #legTriangles(k) times.

## Assessment

The proof counts primitive triangles with a given leg using coprime factorizations, which gives the classical multiplicity 2^(omega-1). That reduces both counting functions to the summatory function of a multiplicative weight g, whose Dirichlet series is (1-2^-s)zeta(s)/L(s,chi_4). The Wiener–Ikehara (or Delange) theorem, together with L(1,chi_4) = pi/4 and the fact that L(s,chi_4) has no zeros on Re s = 1, then gives S(N) ~ 2N/pi. A short dyadic summation and the inversion from the counting function to the n-th term finish the proof. Each step is a textbook application of standard analytic number theory, and the manuscript itself calls it routine. Most of the work went into formalization: Wiener–Ikehara had to be proved from scratch in Lean. That effort does not make the mathematics substantial.

*Follows from:* Classical count of primitive Pythagorean triangles with a given leg (2^(omega-1) coprime factorizations), combined with the Wiener–Ikehara / Delange Tauberian theorem applied to sum_{m odd, all p|m ≡ 3 mod 4} 2^omega(m) m^-s = (1-2^-s) zeta(s)/L(s,chi_4), with L(1,chi_4) = pi/4 and L(s,chi_4) ≠ 0 on Re s = 1.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A354571](https://oeis.org/A354571) as [`Math0.Statements.A354571.statement`](../../lean/Math0/Statements/OEIS/A354571.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A354571.lean`](../../lean/Math0/Frontier/OEIS/A354571.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: lim_{n->oo} a(n)/n = Pi. Also, lim_{n->oo} A354570(n)/n = Pi." (Lothar Selle, Jun 04 2022; same text in A354570)

Referees: No prior resolution found.
- OEIS A354571 and A354570 (Lothar Selle, Jun 2022; last edited Aug 2022) still state lim a(n)/n = Pi as a conjecture. Checked in the local mirror and in upstream raw.githubusercontent.com/oeis/oeisdata.
- Selle, "Kleines Handbuch Pythagoreische Zahlentripel" (BoD 2022), ch. 2.3.10, is cited only for the equality of the two limits; I could not access the book.
- Related unproved Selle conjectures appear in A120427, A120890 and A354569.
- Web searches (arXiv, MathOverflow, Math.SE, SeqFan) found no proof or counterexample.
- The underlying asymptotic is a standard consequence of Wiener–Ikehara/Delange applied to (1-2^-s)zeta(s)/L(s,chi4), using L(1,chi4) = pi/4. D. N. Lehmer (Amer. J. Math. 22, 1900) treats similar Pythagorean counting asymptotics, but not this restricted case.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a354571,
  author       = {{math0}},
  title        = {{Even and odd legs with odd prime factors ≡ 3 (mod 4): a(n)/n → π (A354571, A354570)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a354571}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
