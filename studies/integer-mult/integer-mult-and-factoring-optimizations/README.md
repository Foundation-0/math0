# Verified Mathematical Optimizations: `CrocSwap/integer-mult-bounds` & `1337isnot1337/integer-factoring`

## 1. `CrocSwap/integer-mult-bounds` (`integer-mult-bounds/`)
- **`odd_s_general_frame_breakthroughs.py` & `odd_s_cubic_witnesses.json`:**
  Refutes the odd-`S` non-monic 3-query dyadic cubic-repair impossibility conjecture (`S = r(r-1)/2` odd) by certifying **5 strictly new general-frame arities** (`r in {14, 18, 55, 71, 82}`), all 5 proved `IMPOSSIBLE_OVER_Z3` under monic (`u_j = 1`) frames:
  1. `r = 14` (`S = 91, K = 33^2`): rows `(5, 29), (1, -7), (1, 6)` with exact dyadic weights `-91/32, -49/32, 357` and `det((5, 29), (1, 6)) = +1` in `SL_2(Z)` (co-hosted register pair in 3 elementary shears, 4 total shears).
  2. `r = 18` (`S = 153`): `(27, 95), (1, 18), (21, 74)`.
  3. `r = 55` (`S = 1485`): `(7, 48), (1, 9), (5, 237)`.
  4. `r = 71` (`S = 2485`): `(7, 257), (1, -14), (5, 186)`.
  5. `r = 82` (`S = 3321`): even-`u_0` (`[0:1] mod 2`) rows `(2, 97), (1, -10), (1, 47)`.
- Also copy the C++ general-frame search tool `fast_cubic_unlock.cpp`.

## 2. `1337isnot1337/integer-factoring` (`integer-factoring/`)
- **`ramanujan_shell_divisor_bound.py` & `ramanujan_shell_benchmarks.json`:**
  Upgrades [`research/optimized-divisor-count-bound.md`](https://github.com/1337isnot1337/integer-factoring/blob/main/research/optimized-divisor-count-bound.md) via pure zero-float `O((log n)^4)`-bit-op Dyadic-Shell Ramanujan-Lagrangian duality + `30030`-wheel inclusion-exclusion (`(a + 1)^64 <= 2^{U_a}`, `O(log n)` register bits, zero prime enumeration up to `2^s`), shrinking `q_*(n)` by **`29.4%` to `59.3%`** across `n in [32, 65536]` (`n=64: 33 -> 18`, `n=1024: 335 -> 139`, `n=4096: 1011 -> 440`) (shrinks auxiliary rings `Z/2^{q+1}Z`, cyclic support `K = 2^q`, and singleton-bucket rounds `k` without altering the main `alpha = 1/2` saving exponent).
