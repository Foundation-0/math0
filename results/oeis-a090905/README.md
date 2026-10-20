# A090905: every row ends at twice the largest prime of the previous row (Murthy's conjecture proved)

**Classification:** New result (open problem settled)  
**Area:** Discrete geometry  
**Source problem:** OEIS A090905  
**Date:** 2026-10-20

## Result

Split 1, 2, 3, ... into consecutive groups. Group 1 is (1). Group n+1 starts right after group n. Its length is the least k ≥ len(n) such that the product of group n divides the product of group n+1. Let B_k be the Bertrand primes A006992: B_1 = 2, and B_{k+1} is the largest prime below 2B_k.

Claim: for every n > 4,
- group n-1 has a largest prime p,
- the last term of group n is 2p,
- p = B_{n-1}.

## Verification

The statement was formalized by math0 from the conjecture in [OEIS A090905](https://oeis.org/A090905) as [`Math0.Statements.A090905.statement`](../../lean/Math0/Statements/OEIS/A090905.lean). Its definitions are checked by the kernel against the OEIS data, and it was reviewed for fidelity and frozen before any proof attempt. The Lean file [`lean/Math0/Frontier/OEIS/A090905.lean`](../../lean/Math0/Frontier/OEIS/A090905.lean) proves it; the final command `#math0_settles` checks that our theorem's type is exactly the statement or its negation and that both use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Conjecture as stated in OEIS: %C Conjecture: For n > 4 the last term of the n-th group is 2p where p is the largest prime in the (n-1)th group. And these are the Bertrand primes. (Amarnath Murthy, Dec 13 2003)

Referees: I found no prior proof or refutation.
- OEIS A090904, A090905, A090906 and A090907 (Murthy, Dec 2003; last edited Dec 2016) state the claim only as a conjecture. A090907 adds "verified for 4<n<21".
- A090906 has an unproved %F by M. Bouayoun (Mar 2004) giving the row lengths as 2*(A006992(n)-A006992(n-1)). It is off by one index.
- A381901 (A. Niedermaier, Mar 2025) defines the same triangle with no bound on row length and asserts a(n) = 2*A006992(n-1) for n >= 5, without proof.
- Related: A113117 and A113118 (L. Quet, 2006), A093911 (Murthy's variant), and A006992 (Bertrand primes).
- The key analytic input is Nagura's theorem (J. Nagura, Proc. Japan Acad. 28 (1952) 177-181: for x >= 25 there is a prime between x and 6x/5). The Lean development reproves the form it needs (a prime in (5x/3, 2x) for x >= 83) from scratch.
- Searches of arXiv, MathOverflow/MSE, SeqFan-style queries and the formal-conjectures repository found no prior resolution and no prior formalization.

## Citation

```bibtex
@misc{math0:oeis-a090905,
  author       = {{math0}},
  title        = {{A090905: every row ends at twice the largest prime of the previous row (Murthy's conjecture proved)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/oeis-a090905}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
