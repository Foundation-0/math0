/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Audit
import Math0.Arxiv.Arxiv_0805_3777_isMaxRank_le_two_mul_isGenericRank
import Math0.Arxiv.Arxiv_1609_08688_maximalLength_ge_of_isSquare
import Math0.Arxiv.Arxiv_1609_08688_maximalLength_pow
import Math0.Arxiv.Arxiv_2602_05192_four_2
import Math0.Arxiv.Arxiv_2605_12342_conjecture_1_variants_rank_3_3
import Math0.Arxiv.Arxiv_math_0608009_poisson_conjecture_variants_dimension_three
import Math0.Arxiv.Arxiv_math_0608009_poisson_conjecture_variants_jacobian_implication
import Math0.Books.Bugeaud06_problem_10_6_variant_1
import Math0.Books.Bugeaud08_problem_10_8_variants_quadratic
import Math0.Books.Bugeaud09_problem_10_9_variants_dimH_lt_one
import Math0.Books.Bugeaud09_problem_10_9_variants_measure_zero
import Math0.Books.Equidistribution_isAccumulationPoint_three_halves_pow_infinite
import Math0.ErdosProblems.Erdos1000_erdos_1000_variants_limsup_eq_one
import Math0.ErdosProblems.Erdos1000_erdos_1000_variants_not_tendsto_zero
import Math0.ErdosProblems.Erdos1008_erdos_1008_variants_lower_bound
import Math0.ErdosProblems.Erdos1010_erdos_1010_variants_rademacher
import Math0.ErdosProblems.Erdos1026_erdos_1026_variants_upper_bound
import Math0.ErdosProblems.Erdos1048_erdos_1048_variants_diam_ge_two_is_best
import Math0.ErdosProblems.Erdos1098_erdos_1098_variants_upper_bound
import Math0.ErdosProblems.Erdos10_erdos_10_variants_grechuk_example
import Math0.ErdosProblems.Erdos1119_erdos_1119_variants_erdos_wetzel
import Math0.ErdosProblems.Erdos1121_erdos_1121_variants_higher_dimension
import Math0.ErdosProblems.Erdos1136_erdos_1136_variants_mueller
import Math0.ErdosProblems.Erdos1136_erdos_1136_variants_multiples_of_three
import Math0.ErdosProblems.Erdos1136_erdos_1136_variants_upper_bound
import Math0.ErdosProblems.Erdos1148_erdos_1148_variants_weaker
import Math0.ErdosProblems.Erdos1180_erdos_1180_variants_optimal
import Math0.ErdosProblems.Erdos1193_erdos_1193_parts_i
import Math0.ErdosProblems.Erdos1193_erdos_1193_parts_ii
import Math0.ErdosProblems.Erdos142_erdos_142
import Math0.ErdosProblems.Erdos142_erdos_142_variants_isTheta
import Math0.ErdosProblems.Erdos319_erdos_319
import Math0.ErdosProblems.Erdos367_erdos_367_variants_higher_full_parts
import Math0.ErdosProblems.Erdos409_erdos_409_parts_i
import Math0.ErdosProblems.Erdos723_erdos_723_variants_prime_power_is_projplane_order
import Math0.ErdosProblems.Erdos750_erdos_750_variants_c_gt_quarter
import Math0.ErdosProblems.Erdos775_erdos_775_variants_moon_moser
import Math0.ErdosProblems.Erdos816_erdos_816_variants_complete_bipartite
import Math0.ErdosProblems.Erdos834_erdos_834_parts_ii
import Math0.ErdosProblems.Erdos835_johnsonGraph_18_9_chromaticNumber
import Math0.Frontier.OEIS.A005590
import Math0.Frontier.OEIS.A062887
import Math0.Frontier.OEIS.A071685
import Math0.Frontier.OEIS.A075855
import Math0.Frontier.OEIS.A086004
import Math0.Frontier.OEIS.A090905
import Math0.Frontier.OEIS.A091817
import Math0.Frontier.OEIS.A097154
import Math0.Frontier.OEIS.A106505
import Math0.Frontier.OEIS.A113676
import Math0.Frontier.OEIS.A115026
import Math0.Frontier.OEIS.A116184
import Math0.Frontier.OEIS.A120069
import Math0.Frontier.OEIS.A175385
import Math0.Frontier.OEIS.A195249
import Math0.Frontier.OEIS.A201060
import Math0.Frontier.OEIS.A209802
import Math0.Frontier.OEIS.A215010
import Math0.Frontier.OEIS.A229159
import Math0.Frontier.OEIS.A262957
import Math0.Frontier.OEIS.A294512
import Math0.Frontier.OEIS.A300789
import Math0.Frontier.OEIS.A308222
import Math0.Frontier.OEIS.A308359
import Math0.Frontier.OEIS.A323695
import Math0.Frontier.OEIS.A326407
import Math0.Frontier.OEIS.A326602
import Math0.Frontier.OEIS.A332010
import Math0.Frontier.OEIS.A333650
import Math0.Frontier.OEIS.A334603
import Math0.Frontier.OEIS.A335012
import Math0.Frontier.OEIS.A338885
import Math0.Frontier.OEIS.A342992
import Math0.Frontier.OEIS.A344710
import Math0.Frontier.OEIS.A348484
import Math0.Frontier.OEIS.A355076
import Math0.Frontier.OEIS.A355339
import Math0.Frontier.OEIS.A356360
import Math0.Frontier.OEIS.A357216
import Math0.Frontier.OEIS.A362086
import Math0.Frontier.OEIS.A363482
import Math0.Frontier.OEIS.A363609
import Math0.Frontier.OEIS.A367119
import Math0.Frontier.OEIS.A369366
import Math0.Frontier.OEIS.A375522
import Math0.Frontier.OEIS.A386538
import Math0.Frontier.OEIS.A392943
import Math0.Frontier.OEIS.A393794
import Math0.Frontier.OEIS.A394981
import Math0.Frontier.OEIS.A397315
import Math0.GreensOpenProblems.Green44_green_44
import Math0.OEIS.OeisA51903_conjecture2
import Math0.OEIS.OeisA51903_conjecture3

/-!
# math0

Root module: imports every verified result. Building it re-runs every audit (`#math0_proves`,
`#math0_refutes`, `#math0_answers`), so `lake build` fails on any `sorry`, non-standard axiom, or
mismatch with the upstream statement.
-/
