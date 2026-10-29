# Kagey's conjecture for A278212: a(n) = floor(A275815(n)/2), via exact bishop and queen maxima from flow (LP-dual) certificates

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A278212  
**Date:** 2026-10-24

## Result

For every n >= 1, let a(n) be the largest total number of moves that same-colored bishops can make on an n x n board, and queenMax(n) the same for queens. A piece can only move to an empty square, and every square it passes must be empty. Then a(n) = floor(queenMax(n)/2). More precisely, the proof shows the following. For bishops, a(4) = 20, a(5) = 38 and a(n) = 4(n-2)^2 for n >= 6. For queens, queenMax(4) is 40 or 41, queenMax(5) is 76 or 77, queenMax(6) is 128 or 129, and queenMax(n) = 8(n-2)^2 for n >= 7. That last formula also settles Alec Jones's conjecture on A275815 for n >= 7. The cases n <= 3 come from the listed values.

## Assessment

Earlier rated substantial, because the queen upper bound 8(n-2)^2 seemed to need the computer-found LP-dual certificates used in the Lean proof. That bound turns out to have a one-page elementary proof for n >= 8: count moves line by line, which leaves only the empty border squares to pay for, and let each interior queen pay 2 units along each of its lines to an empty border square at most 2 squares away. A one-page charging proof of the queen bound for n >= 8 was found while assessing A275815 and then verified by two independent checks (a hand re-derivation and an exhaustive and randomized computer search for counterexamples): see results/oeis-a275815/short-proof.md. It is not formalized in Lean. With it, the whole result is a short argument plus small finite cases, so it is now rated routine. The bishop half was always routine.

*Follows from:* Howroyd's per-diagonal bound in the entry (with a short corner argument) for bishops; for queens, the one-page charging proof in results/oeis-a275815/short-proof.md (verified 29 Oct 2026, not formalized).

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  *Revised:* First rated substantial, by the assessor and again by a second, adversarial assessor (26 Oct 2026), because the queen bound seemed to need computer-found certificates. Revised to routine on 29 Oct 2026, after a one-page proof of that bound was found and independently verified (results/oeis-a275815/short-proof.md). (2026-10-29)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A278212](https://oeis.org/A278212) as [`Math0.Statements.A278212.statement`](../../lean/Math0/Statements/OEIS/A278212.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A278212.lean`](../../lean/Math0/Frontier/OEIS/A278212.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: a(n) = floor(A275815(n)/2). - _Peter Kagey_, Nov 24 2016" (also A275815: "Conjecture: a(n) = 8(n-2)^2 for n >= 6. - _Alec Jones_, Nov 16 2016")

Referees: I found no prior resolution, only computation and partial bounds:
- OEIS A278212 (#36, Nov 19 2023): Kagey's 2016 conjecture is still listed as open. It records Chai Wah Wu's bounds 4(n-2)² ≤ a(n) ≤ 4n² (Nov 2016), Andrew Howroyd's a(n) ≤ 4(n-2)²+4 (Oct 2023), and terms a(7)–a(50) computed by Christian Sievers with an ILP (PuLP), after M. S. Branicky's a(6).
- OEIS A275815 (#43, Jul 2021): Alec Jones's conjecture a(n)=8(n-2)² for n≥6 is still a conjecture, with keyword "more". It records Wu's bounds 8(n-2)² ≤ a(n) ≤ 8n² and terms a(7)–a(32) computed by Jim Randell with MiniZinc.
- Jim Randell, Enigma 69 "Maximum queen moves" (enigmaticcode.wordpress.com, 2013, comments through 2025): the 6×6 case is verified by computer and the border formula is called "presumed". There is no general proof.
- Related entries A278211, A278213 and A278214 contain no proof.
- Searches of arXiv, MathOverflow, Math StackExchange, Puzzling, SeqFan and Google Scholar-style queries found no general proof or counterexample.

Short proof (29 Oct 2026): the queen upper bound M <= 8(n-2)^2 also has a one-page charging proof for n >= 8, written up in results/oeis-a275815/short-proof.md and checked by two independent agents; it is not formalized in Lean.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a278212,
  author       = {{math0}},
  title        = {{Kagey's conjecture for A278212: a(n) = floor(A275815(n)/2), via exact bishop and queen maxima from flow (LP-dual) certificates}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a278212}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
