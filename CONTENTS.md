# Contents

**10 results, every one checked by the Lean kernel against a statement published by a third party.**

| Classification | Count |
|---|---|
| New result (open problem settled) | 0 |
| First formal proof of a known result | 5 |
| Independent formal proof (an implying Lean proof already exists elsewhere) | 3 |
| Misformalization found (upstream statement does not match the problem) | 2 |

## First formal proof of a known result

| # | Result | Area | Upstream statement | Lean |
|---|---|---|---|---|
| 1 | [Maximal tensor rank is at most twice the generic rank (Blekherman–Teitler)](results/arxiv-0805-3777-ismaxrank-le-two-mul-isgenericrank/README.md) | Algebraic geometry, Linear algebra | [`Arxiv.«0805.3777».isMaxRank_le_two_mul_isGenericRank`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/Arxiv/0805.3777/TensorRank.lean) | [Arxiv_0805_3777_isMaxRank_le_two_mul_isGenericRank.lean](lean/Math0/Arxiv/Arxiv_0805_3777_isMaxRank_le_two_mul_isGenericRank.lean) |
| 2 | [Projective planes exist for every prime-power order (Erdős 723, existence variant)](results/erdos723-erdos-723-variants-prime-power-is-projplane-order/README.md) | Combinatorics | [`Erdos723.erdos_723.variants.prime_power_is_projplane_order`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/723.lean) | [Erdos723_erdos_723_variants_prime_power_is_projplane_order.lean](lean/Math0/ErdosProblems/Erdos723_erdos_723_variants_prime_power_is_projplane_order.lean) |
| 3 | [Grechuk's example: 1117175146 is not a prime plus at most three powers of two](results/erdos10-erdos-10-variants-grechuk-example/README.md) | Combinatorics, Number theory | [`Erdos10.erdos_10.variants.grechuk_example`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/10.lean) | [Erdos10_erdos_10_variants_grechuk_example.lean](lean/Math0/ErdosProblems/Erdos10_erdos_10_variants_grechuk_example.lean) |
| 4 | [Erdős 1048: the component of {|zⁿ| ≤ 1} containing 0 has diameter exactly 2](results/erdos1048-erdos-1048-variants-diam-ge-two-is-best/README.md) | Complex analysis | [`Erdos1048.erdos_1048.variants.diam_ge_two_is_best`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1048.lean) | [Erdos1048_erdos_1048_variants_diam_ge_two_is_best.lean](lean/Math0/ErdosProblems/Erdos1048_erdos_1048_variants_diam_ge_two_is_best.lean) |
| 5 | [Goodman–Goodman covering theorem for balls in ℝ^d (Erdős 1121, higher-dimensional variant)](results/erdos1121-erdos-1121-variants-higher-dimension/README.md) | Discrete geometry | [`Erdos1121.erdos_1121.variants.higher_dimension`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1121.lean) | [Erdos1121_erdos_1121_variants_higher_dimension.lean](lean/Math0/ErdosProblems/Erdos1121_erdos_1121_variants_higher_dimension.lean) |

## Independent formal proof (an implying Lean proof already exists elsewhere)

| # | Result | Area | Upstream statement | Lean |
|---|---|---|---|---|
| 1 | [Rademacher's theorem: ⌊n²/4⌋+1 edges force ⌊n/2⌋ triangles](results/erdos1010-erdos-1010-variants-rademacher/README.md) | Combinatorics | [`Erdos1010.erdos_1010.variants.rademacher`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1010.lean) | [Erdos1010_erdos_1010_variants_rademacher.lean](lean/Math0/ErdosProblems/Erdos1010_erdos_1010_variants_rademacher.lean) |
| 2 | [Müller's set avoids sums equal to powers of two and has density 1/2 (Erdős 1136)](results/erdos1136-erdos-1136-variants-mueller/README.md) | Number theory | [`Erdos1136.erdos_1136.variants.mueller`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1136.lean) | [Erdos1136_erdos_1136_variants_mueller.lean](lean/Math0/ErdosProblems/Erdos1136_erdos_1136_variants_mueller.lean) |
| 3 | [Sets avoiding sums equal to powers of two have lower density at most 1/2 (Müller)](results/erdos1136-erdos-1136-variants-upper-bound/README.md) | Number theory | [`Erdos1136.erdos_1136.variants.upper_bound`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/1136.lean) | [Erdos1136_erdos_1136_variants_upper_bound.lean](lean/Math0/ErdosProblems/Erdos1136_erdos_1136_variants_upper_bound.lean) |

## Misformalization found (upstream statement does not match the problem)

| # | Result | Area | Upstream statement | Lean |
|---|---|---|---|---|
| 1 | [Erdős 142 (Θ variant): no k-independent order of magnitude for r_k(N)](results/erdos142-erdos-142-variants-istheta/README.md) | Number theory | [`Erdos142.erdos_142.variants.isTheta`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/142.lean) | [Erdos142_erdos_142_variants_isTheta.lean](lean/Math0/ErdosProblems/Erdos142_erdos_142_variants_isTheta.lean) |
| 2 | [Erdős 142: no single k-independent asymptotic formula for r_k(N)](results/erdos142-erdos-142/README.md) | Number theory | [`Erdos142.erdos_142`](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/142.lean) | [Erdos142_erdos_142.lean](lean/Math0/ErdosProblems/Erdos142_erdos_142.lean) |
