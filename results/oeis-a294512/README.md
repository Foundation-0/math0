# Lang's conjecture a(n) = A250400(n+1)/(n+1) for A294512 fails at n = 164

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Difficulty (independent assessment):** routine  
**Area:** Sequences and series  
**Source problem:** OEIS A294512  
**Date:** 2026-10-18

## Result

Let V(n) = sum_{k=0}^{n} 1/((k+1)(3k+1)) and let a(n) be the denominator of V(n) in lowest terms (OEIS A294512). Let A250400(m) be the numerator, in lowest terms, of the harmonic mean m / sum_{j=1}^{m} 1/(j(3j-2)) of the first m octagonal numbers. Lang's conjecture (A294512, FORMULA, 2017) says that A250400(n+1)/(n+1) = a(n) in Q for every n >= 0. This is false. The first failure is at n = 164, where A250400(165)/165 = a(164)/11.

## Assessment

Since the harmonic mean is (n+1)/V(n), the conjecture holds exactly when n+1 is coprime to the numerator of V(n). Checking that condition with exact rational arithmetic finds the first failure at n = 164, where 11 divides both 165 and num V(164). The Lean proof confirms the identity 11*A250400(165) = 165*a(164) by kernel evaluation. The paper's hand argument for why 11 divides the numerator is a nice touch but not needed: the result is a direct finite search, and the relevant value was already in Barker's A250400 table. This is a genuine counterexample to the conjecture as intended, not a degenerate case.

*Follows from:* A harmonic-mean identity that follows straight from the definitions in A294512/A250400: H(n+1) = (n+1)/V(n), so A250400(n+1) = (n+1)*a(n)/gcd(n+1, numerator V(n)). Barker's b-file for A250400 (m <= 1000) already lists A250400(165) = 15*a(164).

*How this was judged:* an independent assessor agent, asked to judge the difficulty of the mathematics and not to inflate it, rated it **routine**. Routine means a short or standard argument, a consequence of material already in the OEIS entry, its cross-references or the literature, or a finite search; substantial means a non-standard idea or a long argument that does not follow readily from such material.  (2026-10-26)

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A294512](https://oeis.org/A294512) as [`Math0.Statements.A294512.statement`](../../lean/Math0/Statements/OEIS/A294512.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A294512.lean`](../../lean/Math0/Frontier/OEIS/A294512.lean) refutes (proves the negation of) it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: A294512 (Denominators of partial sums of the reciprocals of octagonal numbers), FORMULA: "a(n) = A250400(n+1)/(n+1), n >= 0. [conjecture]." (entry by _Wolfdieter Lang_, Nov 01 2017). Companion A294513 (Lang, Nov 02 2017): "a(n) = 2*A250327(n+1)/(n+1) [conjecture]."

Referees: OEIS A294512 (W. Lang, Nov 01 2017; history #1-#13, last edit Nov 12 2017, formula "a(n) = A250400(n+1)/(n+1), n >= 0. [conjecture]" still present). OEIS A250401 (C. Barker 2014; Lang comment Nov 01 2017 conditional on "n+1 divides A250400(n+1)", still present, history #1-#19). OEIS A250400 (C. Barker, Nov 21 2014, b-file n=1..1000, which contains A250400(165) = 15*a(164)). Sibling Lang conjectures in A294513, A294515 are unresolved there too. Not in google-deepmind/formal-conjectures (FormalConjectures/OEIS); not in Tsoukalas et al. / Epoch OEIS Open (arXiv 2608.11941; github.com/epoch-research/LeanOpenProblems-results; SeqFan thread "Language models resolving OEIS conjectures", Aug 2026). No SeqFan, MathOverflow, MSE or arXiv discussion found. Independent check: the failures for n < 3000 are exactly n = 164 (gcd 11) and n = 2413 (gcd 17).

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a294512,
  author       = {{math0}},
  title        = {{Lang's conjecture a(n) = A250400(n+1)/(n+1) for A294512 fails at n = 164}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a294512}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
