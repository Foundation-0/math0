# A356360: the continued-fraction denominators are 1 or prime

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Number theory  
**Source problem:** OEIS A356360  
**Date:** 2026-10-20

## Result

For n >= 3, let a(n) be the denominator, in lowest terms, of the continued fraction 1/(2 - 3/(3 - 4/(4 - ... ((n-1) - n/(n+1))))). Then every a(n) is 1 or a prime. This is the conjecture Mohammed Bouras stated in OEIS A356360 (2022).

## Assessment

The gcd formula already in the entry gives a(n) | 2n-1 at once, so the prime case is immediate. The composite case needs only that an odd composite c = 2m+3 with m >= 4 divides m!, a textbook Wilson-style lemma with a short case split on whether c = p^2. Together with checking n = 3, 4, 5 directly, the whole argument fits in under a page and uses no new idea. The longer Lean development is formalization effort and does not make the mathematics deeper.

*Follows from:* The closed form and gcd formula already in the entry, a(n) = (2n-1)/gcd(2n-1, A051403(n-2)+A051403(n-3)), proved as Theorem 1.1 of Bouras's linked paper. Combined with A051403(j) = (j+2)*A003422(j+1)/2, this reduces the question to the elementary fact that an odd composite 2m+3 with m >= 4 divides m!. The same denominator-of-factorial pattern appears in A145737 (Detlefs: a(n) = denominator(n!*3n(n+1)/(2(2n+1))) = 2n+1 if prime, else 1).

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A356360](https://oeis.org/A356360) as [`Math0.Statements.A356360.statement`](../../lean/Math0/Statements/OEIS/A356360.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A356360.lean`](../../lean/Math0/Frontier/OEIS/A356360.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: A356360: "Conjecture: The sequence contains only 1's and the primes." (_Mohammed Bouras_, Oct 15 2022). The same sentence appears in A369797 (Feb 2024), A370726 (Feb 2024) and A372763 ('Conjecture 1', May 2024). A372761: "Conjecture 1: Except for 4, the sequence contains only 1's and the primes." A362086: "Conjecture: Except for 9, every term of this sequence is either a prime or 1." A363482: "Conjecture: Except for 49, every term of this sequence is either a prime or 1." (all by Bouras)

Referees: OEIS A356360 (mirror 2026-10-17, rev #31 Aug 2024): still marked "Conjecture". It has an unproved comment "Same as A128059(n), A145737(n-1), A097302(n-2) for n>5", and its formula "a(n)=2n-1 if prime else 1 (n != 5)" is labeled "From the conjecture". M. Bouras, "The Distribution Of Prime Numbers And The Continued Fractions", Zenodo doi:10.5281/zenodo.7212512 (2022; also viXra 2209.0101): proves only the closed form (Thm 1.1) and states Conjecture 3.1, verified to n=10000. M. Bouras, "A New Primes-Generating Sequence", arXiv:2509.09745 (2025), Table 2 (k=1 row = A356360): observation only, no proof. Bouras slides, Zenodo 10992128: "Conjecture 2", no proof. AlphaProof Nexus results / formal-conjectures auto_oeis THEOREM_MAPPING and T. Adamczewski, "OEIS Open", arXiv:2608.11941: A356360 is not included; only the sibling A372761 Conj. 2 was resolved. Related but distinct: A356247 conjectures proved by B. Cloitre (2025, OEIS attachment). No prior proof or counterexample found.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a356360,
  author       = {{math0}},
  title        = {{A356360: the continued-fraction denominators are 1 or prime}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a356360}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
