# The Golomb-row triangle A113676 and Levine's sequence A014644

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Discrete geometry  
**Source problem:** OEIS A113676  
**Date:** 2026-10-20

## Result

Let G be Golomb's sequence A001462 (G(1)=1, G(2)=G(3)=2, G(4)=G(5)=3, ...; n occurs G(n) times, nondecreasing). Let H be G with one 2 removed: H(1)=1 and H(j)=G(j+1) for j>=2. Cut H into consecutive rows: row 1 is [H(1)], and row n+2 has as many terms as the sum of row n+1. Let a(n) be the length of row n. Levine's array has row 1 = [1,1], and row k+1 lists 1 c_1 times, 2 c_2 times, ..., where row k = [c_1, c_2, ...]. A014644(k) is the last term of Levine row k. Claim (both conjectures of van Lamoen and Hanna, 2005): (1) for every n>=2, a(n) = A014644(n+2) - A014644(n+1); (2) the last term of row 1 is A014644(1), and for every n>=2 the last term of row n is A014644(n+1).

## Assessment

The one real idea is that each Levine row from row 2 on is a prefix of Golomb's sequence, so its sum is the length of the next row. That is immediate from Golomb's self-describing property and is already known: A014643 hints at it and Claes and Miyamoto state it. Everything else is a telescoping sum and a short induction showing that the triangle's rows are the blocks of G between consecutive Levine row lengths; both conjectures then follow. The whole argument fits in about a page of elementary steps, and the manuscript itself calls the result "a short consequence" of known facts.

*Follows from:* The fact that from row 2 on, the rows of Levine's array (A014643) are initial segments of Golomb's sequence A001462. A014643's cross-reference note "Rows converge to A001462" points to this, and Claes and Miyamoto, arXiv:2602.10992, p. 3, eqs. (3)-(4) state it: the Levine step maps the first n Golomb terms to the first A001463(n) terms. Golomb's self-describing property gives it at once.

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A113676](https://oeis.org/A113676) as [`Math0.Statements.A113676.statement`](../../lean/Math0/Statements/OEIS/A113676.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A113676.lean`](../../lean/Math0/Frontier/OEIS/A113676.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C Conjecture: a(n) for n>1 gives first differences of Lionel Levine's sequence A014644(n) for n>=3. %C Conjecture: Final elements of the rows form A014644 except for duplicate 2. (Floor van Lamoen and Paul D. Hanna, Nov 06 2005)

Referees: No prior proof found.
- OEIS A113676 (van Lamoen & Hanna, Nov 2005; rev #9, Mar 2025) still lists both conjectures.
- OEIS A001462 has van Lamoen's related conjecture (Nov 06 2005), still unresolved in the Aug 2026 revision.
- OEIS A014643 has the %Y note "Rows converge to A001462".
- J. Claes and R. Miyamoto, "Golombic and Levine sequences", arXiv:2602.10992 [math.CO] (Feb 2026), p. 3, eqs. (3)–(4). It observes that Γ maps the first n Golomb terms to the first A001463(n) terms (so the A014643 rows are Golomb prefixes), and that |a| = #Γa and #a = (Γa)(|a|). These are the key ingredients, but the paper does not mention A113676 or prove its conjectures.
- Cross-checked entries: A014644, A014643, A011784, A012257, A001463, A113722, A113724, A113730 and A304679. None records a resolution.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a113676,
  author       = {{math0}},
  title        = {{The Golomb-row triangle A113676 and Levine's sequence A014644}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a113676}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
