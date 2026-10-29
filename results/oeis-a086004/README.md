# There are no 5-Rotation Cycle Primes (A086004, Conjecture 2)

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Sequences and series  
**Source problem:** OEIS A086004  
**Date:** 2026-10-19

## Result

Let rot be the rotation of A086002. For a number n with d decimal digits, rot(n) swaps the block of the first floor(d/2) digits with the block of the last floor(d/2) digits; when d is odd, the centre digit stays where it is. Let f(n) = n + rot(n). Then no prime p has f(p), f^2(p), f^3(p), f^4(p) and f^5(p) all prime.

## Assessment

The proof is a one-page argument about decimal digits. It reuses Mathar's factorization for even digit counts and Wu's setup from A261458, where the first four iterates must keep the same odd number of digits. On top of that it makes one simple observation: the centre digit M becomes 2M mod 10, and if M is at most 4 then f(n) is fixed by the rotation, so the next iterate is 2f(n) and cannot be prime. A five-case check on the centre digit (it must run 9, 8, 6, 2) then finishes the proof. Wu stopped at six steps in 2015, but the extra step uses a short and standard idea that a competent mathematician working from the material in the entry and its cross-references would find quickly.

*Follows from:* Mathar's factorization f(n) = (10^k+1)(a+b) for even digit counts (A086004 comment) and Wu's no-carry, fixed-digit-length argument in A261458, together with the elementary block decomposition f(n) = 10^(m+1)S + 2M*10^m + S

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A086004](https://oeis.org/A086004) as [`Math0.Statements.A086004.statement`](../../lean/Math0/Statements/OEIS/A086004.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A086004.lean`](../../lean/Math0/Frontier/OEIS/A086004.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture 2: There are no 5-Rotation Cycle Primes." (A086004, entry by _Chuck Seggelin_, Jul 07 2003. Conjecture 1 was settled by R. J. Mathar in 2009. Chai Wah Wu added on Aug 20 2015 that 4-rotation cycle primes exist (A261458), and in A261458 he proved there are none surviving 6 applications.)

Referees: I found no prior resolution. OEIS A086004 (Seggelin 2003, last edited Jun 2025) still lists Conjecture 2 as open. OEIS A261458 (Chai Wah Wu, Aug 2015) proves the weaker statement that no chain of 6 steps exists, using a leading-digit/carry argument, and gives 4-step examples such as 10010905789. Mathar's 2009 comment on A086004 proves Conjecture 1 (even digit counts) only. Web searches (OEIS-indexed pages, arXiv, StackExchange-style queries, primepuzzles) found nothing on the 5-step case. The SeqFan archive could not be reached from here, so it was not checked.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a086004,
  author       = {{math0}},
  title        = {{There are no 5-Rotation Cycle Primes (A086004, Conjecture 2)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a086004}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
