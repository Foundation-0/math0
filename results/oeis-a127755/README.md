# The inverse of the triangle 1/n! [k ≤ n ≤ 2k] is an integer triangle

**Classification:** New result (conjecture settled; no earlier resolution found)  
**Area:** Discrete geometry  
**Source problem:** OEIS A127755  
**Date:** 2026-10-26

## Result

Let A(n,k) = 1/n! if k ≤ n ≤ 2k and A(n,k) = 0 otherwise (n, k ≥ 0), viewed as an infinite lower-triangular matrix over Q. Let T be its inverse, computed by forward substitution: T(n,k) = n!·([n = k] − Σ_{j<n} A(n,j) T(j,k)) for k ≤ n, and T(n,k) = 0 for k > n. Then T(n,k) is an integer for all 0 ≤ k ≤ n. This was conjectured by Paul Barry in OEIS A127755.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A127755](https://oeis.org/A127755) as [`Math0.Statements.A127755.statement`](../../lean/Math0/Statements/OEIS/A127755.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A127755.lean`](../../lean/Math0/Frontier/OEIS/A127755.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C A127755 It is conjectured that this is an integer triangle. Row sums are A127756. (_Paul Barry_, Jan 28 2007)

Referees: I found no prior proof or counterexample for A127755. Sources checked:
- Local mirror and current GitHub oeisdata entry for A127755 (revision #5, Sep 29 2018), still marked conjectured.
- Related OEIS entries: A127756; A101688 (the 0/1 triangle [k<=n<=2k]); A111967 (its inverse, by Barry, 2005), with A127755(n,k) = k!·A111967(n,k).
- A127749: R. J. Mathar (Apr 21 2021) gives T(n,k) = (2k+1)·A111967(n,k), the same diagonal-scaling argument applied to the 1/(2n+1) sibling.
- A127793: FUNG Cheok Yin (Sep 2022) gives a formula implying integrality for the 1/floor((n+2)/2) sibling. Sela Fried, "On the inverse of a certain triangular matrix and its connection to the largest odd divisor", Notes Num. Theor. Disc. Math. 32(2) (2026) 255-262, doi:10.7546/nntdm.2026.32.2.255-262, proves it; the paper does not mention A127755.
- Sibling integrality conjectures that are also still open in OEIS: A127710, A127711, A127771.
- Web searches (OEIS/SeqFan/arXiv/MathOverflow/MSE-style queries) found nothing more.

## Citation

```bibtex
@misc{math0:oeis-a127755,
  author       = {{math0}},
  title        = {{The inverse of the triangle 1/n! [k ≤ n ≤ 2k] is an integer triangle}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a127755}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
