# `cubic-general-frames-and-2adic-obstruction`

Self-contained mathematical proofs, exact JSON certificates, standard-library Python verifiers, and C++20 OpenMP solver advancing the 3-query dyadic cubic-repair frontier in [`CrocSwap/integer-mult-bounds`](https://github.com/CrocSwap/integer-mult-bounds) ([PR #6653](https://github.com/CrocSwap/integer-mult-bounds/pull/6653), [PR #7475](https://github.com/CrocSwap/integer-mult-bounds/pull/7475), [PR #7478](https://github.com/CrocSwap/integer-mult-bounds/pull/7478), [PR #7479](https://github.com/CrocSwap/integer-mult-bounds/pull/7479)).

## Quick Reproduction

```bash
# 1. Zero-dependency standard-library verification (< 1 second)
python3 -B verify.py

# 2. Independent 5-point evaluation & 2x2 shear-matrix oracle (< 1 second)
python3 -B independent_check.py

# 3. Compile & run C++20 unconditional 99-arity odd-S certifier (3 <= r <= 200, ~9s on 2 cores)
g++ -O3 -march=native -fopenmp -Wall -Wextra cubic_leapfrog_prover.cpp -o cubic_leapfrog_prover
./cubic_leapfrog_prover --rmax 200

# 4. Search higher even-S arities (e.g. 201..250) via norm-divisor leapfrog
./cubic_leapfrog_prover --search 201 250
```

## Scope & Limitations

This is a standalone algebraic/combinatorial proof and certificate package (`no kappa`); it does not modify `certificates/selected-result.json` or claim a new conditional integer-multiplication exponent $\kappa$ above [PR #7000](https://github.com/CrocSwap/integer-mult-bounds/pull/7000) / [PR #7481](https://github.com/CrocSwap/integer-mult-bounds/pull/7481). Licensed under Apache-2.0.
