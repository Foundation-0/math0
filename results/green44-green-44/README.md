# Sieving [N] by half the classes mod 1000 primes below N^{9/10} can leave more than N/10 (Green's Problem 44 refuted as formalized)

**Classification:** Independent formal proof (an implying Lean proof already exists elsewhere)  
**Area:** Number theory  
**Source problem:** Ben Green's 100 open problems, #44  
**Date:** 2026-10-17

## Result

Green's Open Problem 44 (from Erdős 1980, Section 6, Problem 3): sieve [N] by removing half the residue classes mod p_i, for primes 2 ≤ p_1 < ... < p_1000 < N^{9/10}. Does the remaining set have size at most N/10? The formal statement Green44.green_44 says yes: for all N, all strictly increasing p : Fin 1000 → ℕ of primes with p_999^10 < N^9, and all A_i ⊆ ZMod p_i with |A_i| = ⌊p_i/2⌋, the set {x ∈ [1,N] : x mod p_i ∉ A_i for all i} has 10·|remaining| ≤ N. We prove the negation. Counterexample: N = 100000, p_0 < ... < p_999 the 1000 consecutive primes 20011, ..., 30161, and A_i the upper half {⌈p_i/2⌉, ..., p_i − 1} of the residues mod p_i.

## Verification

The Lean file [`lean/Math0/GreensOpenProblems/Green44_green_44.lean`](../../lean/Math0/GreensOpenProblems/Green44_green_44.lean) refutes (proves the negation of) the upstream statement [`Green44.green_44`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/GreensOpenProblems/44.lean) (formal-conjectures at commit `c77fdd4`, upstream category `research open`). Its final command `#math0_refutes` checks that our theorem's type is syntactically identical to the upstream statement (negated) and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Notes

Sources:
- Erdős, "A survey of problems in combinatorial number theory", Ann. Discrete Math. 6 (1980) 89-115, p.107, §6 Problem 3 (scan at https://users.renyi.hu/~p_erdos/1980-03.pdf).
- B. Green, 100 Open Problems, Problem 44 (https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf, Dec 2025 version; no update recorded).
- Erdős Problem #1202 (https://www.erdosproblems.com/1202): "resolved in the negative by Price and GPT-5.4 Pro". It identifies the problem with Green #44. Last edited 2026-04-12; local DB marks it solved on 2026-04-04. Write-up: https://www.overleaf.com/read/qyhdmrchqnvb.
- #1202 forum thread (https://www.erdosproblems.com/forum/thread/1202): Z. Hunter and T. Bloom, 16-17 Apr 2026, on large-sieve bounds and refinements.
- Justin Sun Prize catalog entry JSP-001007 (TheJustinSunPrize/awards, problems/catalog-1001-1022.md): "Solved, Price and GPT-5.4 Pro".
- Existing Lean formalization: github.com/tester-lean/awards @ f26433803cfbd924569aebbdcc1c39321ecb9971, submissions/jsp-001007. Theorems JSP001007.green44_counterexample (every k ≥ 1, all large N, more than N/10 survivors, p^10 < N^9, |A_i| = (p-1)/2) and JSP001007.not_green44_conjecture. Submitted as https://github.com/TheJustinSunPrize/awards/issues/104 on 2026-09-16; pending and unreviewed. Its header cites formal-conjectures Green44.
- Upstream formal-conjectures main: GreensOpenProblems/44.lean is still tagged "research open"; there is no ErdosProblems/1202.lean. - **Erdős's original:** Erdős, "A

## Citation

```bibtex
@misc{math0:green44-green-44,
  author       = {{math0}},
  title        = {{Sieving [N] by half the classes mod 1000 primes below N^{9/10} can leave more than N/10 (Green's Problem 44 refuted as formalized)}},
  howpublished = {\url{https://github.com/Foundation-0/math0/tree/main/results/green44-green-44}},
  note         = {Produced by Claude (Anthropic); Lean-verified},
  year         = {2026}
}
```
