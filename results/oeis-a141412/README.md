# Denominators of Curtz's polynomials are Farhi's d(n+1,k+1) (A141412, Marcus's conjecture)

**Classification:** First formal proof of a known result  
**Area:** Discrete geometry  
**Source problem:** OEIS A141412  
**Date:** 2026-10-20

## Result

Let P(0,x)=1 and P(n+1,x) = (-1)^(n+1)/(n+2) + x * sum_{i=0}^{n} (-1)^i/(i+1) * P(n-i,x) over Q, and let c(n,k) = [x^k] P(n,x) (computed by the matching recursion c in the statement file). Let T(n,k) be the reduced denominator of c(n,k), and let d(n,k) be the reduced denominator of |s(n,k)| * k!/n!, where |s(n,k)| is the unsigned Stirling number of the first kind (Nat.stirlingFirst). Then T(n,k) = d(n+1,k+1) for every 0 <= k <= n. The proof gives this for all n and k.

## Verification

The statement was formalized by math0 (not by a third party) from the conjecture in [OEIS A141412](https://oeis.org/A141412) as [`Math0.Statements.A141412.statement`](../../lean/Math0/Statements/OEIS/A141412.lean). Its definitions are checked by the kernel against the OEIS data. A separate agent reviewed it for fidelity to the OEIS text and froze it (by hash) before any proof attempt. The statement and its frozen hash were committed together with the proof, so the order (freeze, then proof) is recorded only in the pipeline's logs, not in the git history. Its fidelity to the OEIS text is a judgement, not a machine check, so the conjecture as stated in OEIS is quoted in the notes below for comparison. The Lean file [`lean/Math0/Frontier/OEIS/A141412.lean`](../../lean/Math0/Frontier/OEIS/A141412.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: "Conjecture: T(n, k) = d(n+1, k+1), with d(n,k) = denominator(A000254(n, k)*k!/n!) where A000254 are the unsigned Stirling numbers of the 1st kind. See d(n,k) in Farhi link. - _Michel Marcus_, Oct 18 2018"

Referees: P. Flajolet, X. Gourdon and B. Salvy, "Sur une famille de polynômes issus de l'analyse numérique", Gazette des Mathématiciens 55 (1993) 67-78, also INRIA Research Report RR-1857 (Feb 1993), https://inria.hal.science/inria-00074815/document. Eq. (3) is the generating function log(1+z)/(z(1-x·log(1+z))), and eq. (6) is P_n(x) = (-1)^n/(n+1)! Σ_k s_{n+1,k+1}(k+1)!(-x)^k, which gives the conjecture at once. This paper is cited in A141412's own %D line. The OEIS records the same identity in A140749 %F (Paul Curtz, Jul 17 2008, numerators = those of A048594(n+1,k+1)/(n+1)!) and A141412 %F (G. C. Greubel, Oct 24 2023, "Equals denominators of A048594(n+1,k+1)/(n+1)!"), with A048594's column e.g.f. log(1+x)^k. Farhi's d(n,k) comes from B. Farhi, arXiv:1810.07560 (Funct. Approx. Comment. Math. 61 (2019)). I found no earlier formal proof.

## Manuscript

[paper.pdf](paper.pdf) ([source](paper.tex))

## Citation

```bibtex
@misc{math0:oeis-a141412,
  author       = {{math0}},
  title        = {{Denominators of Curtz's polynomials are Farhi's d(n+1,k+1) (A141412, Marcus's conjecture)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a141412}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
