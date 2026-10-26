# A334595: a(n) = 1 iff n is a power of two, and the records occur exactly at 1 and 2^k + 1

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A334595  
**Date:** 2026-10-24

## Result

Let a(n) be the number obtained as follows. Write n in binary, most significant bit first. Build the XOR-triangle whose first row is that bit string; each later row is the pairwise XOR of adjacent entries of the row above. Read the right side of the triangle from the top-right corner downward, and interpret it as a binary numeral with the first entry as the most significant bit. Then:
(1) For n >= 1, a(n) = 1 if and only if n is a power of two.
(2) The record positions are exactly {1} together with {2^k + 1 : k >= 1}. Here n >= 1 is a record position when a(n) > a(m) for every 1 <= m < n.

## Assessment

Reverse the row, so that the right diagonal becomes the left diagonal. The digits of a(n) are then the GF(2) binomial transform of the bits of n. That transform is a classical involution, and A334727 already records it for this family. So a is a bijection on L-bit strings with a(n) < 2^L. Both conjectures then come down to working out three explicit preimages, of 1, of 2^L-1 and of 2^L-2, which takes about a page of elementary argument. No new idea was needed. The length of the Lean formalization does not make the mathematics substantial.

*Follows from:* The classical fact that the binomial transform over GF(2) (the Pascal matrix mod 2) is an involution. This is the self-inverse XOR binomial transform of A099884, and also the self-inverse permutation stated in the sibling entry A334727, which gives the left-diagonal version of A334595. Reading the right diagonal of a row is the same as reading the left diagonal of the reversed row.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A334595](https://oeis.org/A334595) as [`Math0.Statements.A334595.statement`](../../lean/Math0/Statements/OEIS/A334595.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A334595.lean`](../../lean/Math0/Frontier/OEIS/A334595.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: Conjecture: Records occur at 1 and at 2^n + 1.  /  Conjecture: a(n) = 1 if and only if n is a power of two. (_Peter Kagey_, May 07 2020)

Referees: I found no earlier proof or counterexample for either A334595 conjecture.
- OEIS A334595 (Peter Kagey, May 2020): unchanged since revision #18 (May 09 2020), with both statements still labeled "Conjecture".
- MathOverflow 359138, "Number triangle" (user DSM, with answers by YCor and Ilya Bogdanov): treats the boundary operator φ_k with φ_k^3 = 1 and counts rotationally symmetric triangles (A334556/A334596). It does not address records or a(n) = 1.
- OEIS A334727 (Rémy Sigrist, 2020): states that the left-diagonal map is a self-inverse permutation.
- Paul D. Hanna's XOR binomial transform entries (OEIS A099884, A099900, A099902): note that the transform is self-inverse.
These are the known ingredients that make the result elementary. Web searches of SeqFan, arXiv, MathOverflow and Math StackExchange found no resolution.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a334595,
  author       = {{math0}},
  title        = {{A334595: a(n) = 1 iff n is a power of two, and the records occur exactly at 1 and 2^k + 1}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a334595}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
