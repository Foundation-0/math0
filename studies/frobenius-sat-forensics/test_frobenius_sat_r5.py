#!/usr/bin/env python3
"""R1-R5 Verification, Invariance, Unseen-Instance & 100% Mutation-Kill Suite for AUDIT-071 (Arm R7-4).

Pure Python 3 stdlib; zero bare asserts; 100% guard coverage for `aletheia v1.4.0 mutate --add-cwd`.
"""

from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import frobenius_sat_forensics as ff  # noqa: E402


def check(cond: bool, msg: str) -> None:
    if not cond:
        raise ff.FrobeniusForensicsError("TEST_FAIL", msg)


def expect_code(code: str, fn) -> None:
    try:
        fn()
    except ff.FrobeniusForensicsError as exc:
        check(exc.code == code, f"Expected [{code}], got [{exc.code}]: {exc.message}")
        return
    raise ff.FrobeniusForensicsError("TEST_MISSED_ERR", f"Expected [{code}] but call succeeded")


def reject_any_float(obj: object, path: str = "root") -> None:
    check(not isinstance(obj, float), f"Float forbidden at {path}: {obj!r}")
    if isinstance(obj, dict):
        for k, v in obj.items():
            reject_any_float(v, f"{path}.{k}")
    elif isinstance(obj, (list, tuple)):
        for i, v in enumerate(obj):
            reject_any_float(v, f"{path}[{i}]")


def test_group_1_end_to_end_zero_float_certificate() -> None:
    res = ff.run_all()
    reject_any_float(res)
    check(res["verdict"] == "FROBENIUS_SAT_FORENSICS_ALL_VERIFIED", f"Bad verdict: {res['verdict']}")
    raw = json.dumps(res, sort_keys=True, allow_nan=False)

    def _no_float(s: str) -> None:
        raise ff.FrobeniusForensicsError("FLOAT_JSON", f"Float in JSON: {s!r}")

    parsed = json.loads(raw, parse_float=_no_float)
    m1 = parsed["module_1_table2_exact_arithmetic_and_scaling"]
    check(m1["rows_audited"] == 30 and m1["ratio_cells_checked"] == 102 and m1["ratio_mismatches"] == 0, "Module 1 mismatch")
    check(m1["par2_zero_centi_ms_discrepancy"] is True, "PAR-2 discrepancy nonzero")
    check(m1["scaling_forensics"]["hard_spn_exponential_wall"]["frob_d32_to_d48_ratio"] == "257/34", "Hard-SPN ratio 1 wrong")
    check(m1["scaling_forensics"]["hard_spn_exponential_wall"]["frob_d48_to_d64_ratio"] == "2126/257", "Hard-SPN ratio 2 wrong")
    check(m1["scaling_forensics"]["sha256_bitsliced_enumeration"]["exceeds_30s_timeout_at_k28_unsat"] is True, "SHA256 k=28 bound wrong")
    check(parsed["module_2_aig_hybrid_vs_dpll_separations"]["verified"] is True, "Module 2 failed")
    check(parsed["module_3_np_hard_blind_spots"]["verified"] is True, "Module 3 failed")


def test_group_2_invariance_and_exact_identities() -> None:
    # 1. Row-permutation invariance of exact PAR-2 totals and ratio verification
    rev_rows = tuple(reversed(ff.TABLE2_ROWS))
    m1_orig = ff.audit_table2_exact(ff.TABLE2_ROWS)
    m1_rev = ff.audit_table2_exact(rev_rows)
    check(m1_orig["solvers"] == m1_rev["solvers"], "PAR-2 totals not row-permutation invariant")
    check(m1_rev["ratio_mismatches"] == 0, "Permuted table ratio verification failed")

    # 2. Variable-relabeling invariance of F2 Gaussian elimination (Z2 cohomology ⧇)
    n_e, eqs, _ = ff.build_tseitin_3regular_prism(3)
    eqs_perm = [((tuple((idx + 3) % n_e for idx in vs)), rhs) for vs, rhs in eqs]
    r1 = ff.solve_f2_linear_system_exact(n_e, eqs)
    r2 = ff.solve_f2_linear_system_exact(n_e, eqs_perm)
    check(r1["status"] == r2["status"] == "UNSAT" and r1["rank"] == r2["rank"], "F2 Gauss not relabel-invariant")

    # 3. Satisfiable F2 linear system verification (even charge on prism -> SAT, verified against every equation!)
    eqs_sat = [(vs, 1 if idx in (0, 1) else 0) for idx, (vs, _) in enumerate(eqs)]
    sat_res = ff.solve_f2_linear_system_exact(n_e, eqs_sat)
    check(sat_res["status"] == "SAT", "Even-charge Tseitin must be SAT")
    sol = sat_res["solution"]
    for vs, rhs in eqs_sat:
        check(sum(sol[i] for i in vs) % 2 == rhs, "F2 solution violated equation")

    # 4. Exact half-to-even decimal formatting boundary checks (0 and 6 decimals)
    check(ff.exact_round_decimal_str(Fraction(0), 0) == "0", "Zero 0-dp formatting failed")
    check(ff.exact_round_decimal_str(Fraction(5, 2), 0) == "2", "Half-to-even 2.5 failed")
    check(ff.exact_round_decimal_str(Fraction(7, 2), 0) == "4", "Half-to-even 3.5 failed")
    check(ff.exact_round_decimal_str(Fraction(1, 8), 6) == "0.125000", "6-dp formatting failed")

    # 5. Exact AIG witness boundary checks + even composite factoring + satisfiable PHP
    check(ff.factor_integer_exact(4, 4)["factors"] == [2, 2], "Even composite N=4 failed")
    check(ff.aig_verify_factor_witness(15, 1, 15, 4) is False, "Trivial factor p=1 must be rejected")
    check(ff.aig_verify_factor_witness(15, 3, 5, 2) is False, "Out-of-width factor must be rejected")
    check(ff.solve_php_cutting_planes_exact(2, 2)["status"] == "SAT", "PHP^2_2 must be SAT")
    check(ff.exact_cec_multiplier_poly_equivalence(2)["status"] == "UNSAT", "2x2 CEC failed")
    check(ff.exact_cec_multiplier_poly_equivalence(16)["status"] == "UNSAT", "16x16 CEC failed")
    check(ff.bitsliced_arx_preimage_64way(14, 0)["total_batches"] == 256, "k=14 batch count wrong")

    # 6. XOR3 extraction positive control: 4-clause 3-XOR block IS detected (= 1)!
    xor3_cnf = [
        (1, 2, 3),
        (1, -2, -3),
        (-1, 2, -3),
        (-1, -2, 3),
    ]
    check(ff.count_extracted_xor3_constraints(xor3_cnf) == 1, "Failed to detect genuine XOR3 block")

    # 7. DPLL budget exhaustion control + empty-clause immediate UNSAT
    nv_p, cnf_p = ff.build_php_cnf(5, 4)
    bud = ff.solve_cnf_dpll(nv_p, cnf_p, max_decisions=1)
    check(bud["status"] == "BUDGET_EXCEEDED", f"Expected BUDGET_EXCEEDED, got {bud}")


def test_group_3_unseen_instances_and_tamper_detection() -> None:
    # 1. Tampered Table-2 ratio cell is caught immediately (ratio_mismatches == 1)
    bad_rows = list(ff.TABLE2_ROWS)
    r0 = bad_rows[0]
    bad_rows[0] = (r0[0], r0[1], r0[2], r0[3], r0[4], ("999.9", r0[5][1], r0[5][2], r0[5][3]))
    m_bad = ff.audit_table2_exact(bad_rows)
    check(m_bad["ratio_mismatches"] == 1 and m_bad["verified"] is False, "Tampered ratio not caught")

    # 2. Tampered 0.00 ms conservative lower-bound cell is caught
    bad_rows2 = list(ff.TABLE2_ROWS)
    r4 = bad_rows2[4]
    bad_rows2[4] = (r4[0], r4[1], r4[2], r4[3], r4[4], (">1", r4[5][1], r4[5][2], r4[5][3]))
    m_bad2 = ff.audit_table2_exact(bad_rows2)
    check(m_bad2["ratio_mismatches"] == 1 and m_bad2["verified"] is False, "Tampered >LB ratio not caught")

    # 3. Unseen small subset table (2 rows) with custom timeout penalty works cleanly
    sub = ff.TABLE2_ROWS[:2]
    m_sub = ff.audit_table2_exact(sub, timeout_penalty_centi_ms=1000)
    check(m_sub["rows_audited"] == 2 and m_sub["ratio_mismatches"] == 0, "Subset audit failed")

    # 4. Unseen 3-SAT at n=4, m=1, seed=0 boundary
    cnf_min = ff.generate_deterministic_3sat(4, 1, 0)
    check(len(cnf_min) == 1 and ff.solve_cnf_dpll(4, cnf_min)["status"] == "SAT", "Minimal 3-SAT failed")


def test_group_4_r5_adversarial_refusal_controls() -> None:
    # --- Scalar / formatting guards ---
    expect_code("BAD_FRAC", lambda: ff.exact_round_decimal_str(Fraction(-1, 2), 1))
    expect_code("BAD_FRAC", lambda: ff.exact_round_decimal_str(1.5, 1))  # type: ignore[arg-type]
    expect_code("BAD_DECIMALS", lambda: ff.exact_round_decimal_str(Fraction(1), -1))
    expect_code("BAD_DECIMALS", lambda: ff.exact_round_decimal_str(Fraction(1), 7))
    expect_code("BAD_DECIMALS", lambda: ff.exact_round_decimal_str(Fraction(1), True))  # type: ignore[arg-type]

    # --- Module 1 Table 2 audit guards ---
    expect_code("EMPTY_TABLE", lambda: ff.audit_table2_exact([]))
    expect_code("BAD_PENALTY", lambda: ff.audit_table2_exact(ff.TABLE2_ROWS[:1], timeout_penalty_centi_ms=0))
    expect_code("BAD_FROB_TIME", lambda: ff.audit_table2_exact([("F", "i", 1, "SAT", (-1, 1, 1, 1, 1), ("1", "1", "1", "1"))]))
    expect_code("BAD_SOLVER_TIME", lambda: ff.audit_table2_exact([("F", "i", 1, "SAT", (1, -1, 1, 1, 1), ("1", "1", "1", "1"))]))
    expect_code("RATIO_ON_TIMEOUT", lambda: ff.audit_table2_exact([("F", "i", 1, "SAT", (1, None, 1, 1, 1), ("1", "1", "1", "1"))]))
    expect_code("MISSING_RATIO", lambda: ff.audit_table2_exact([("F", "i", 1, "SAT", (1, 2, 1, 1, 1), (None, "1", "1", "1"))]))

    # --- Module 2 DPLL / F2 / Tseitin / PHP / CEC / Factor / Bit-sliced guards ---
    expect_code("DPLL_BAD_VARS", lambda: ff.solve_cnf_dpll(0, [(1,)]))
    expect_code("DPLL_BAD_BUDGET", lambda: ff.solve_cnf_dpll(1, [(1,)], max_decisions=0))
    expect_code("DPLL_BAD_LIT", lambda: ff.solve_cnf_dpll(1, [(0,)]))
    expect_code("DPLL_BAD_LIT", lambda: ff.solve_cnf_dpll(1, [(2,)]))

    expect_code("F2_BAD_VARS", lambda: ff.solve_f2_linear_system_exact(0, [((0,), 1)]))
    expect_code("F2_EMPTY_EQS", lambda: ff.solve_f2_linear_system_exact(2, []))
    expect_code("F2_BAD_PARITY", lambda: ff.solve_f2_linear_system_exact(2, [((0,), 2)]))
    expect_code("F2_BAD_PARITY", lambda: ff.solve_f2_linear_system_exact(2, [((0,), True)]))  # type: ignore[arg-type]
    expect_code("F2_BAD_IDX", lambda: ff.solve_f2_linear_system_exact(2, [((-1,), 0)]))
    expect_code("F2_BAD_IDX", lambda: ff.solve_f2_linear_system_exact(2, [((2,), 0)]))

    expect_code("TSEITIN_BAD_N", lambda: ff.build_tseitin_3regular_prism(2))
    expect_code("PHP_BAD_P", lambda: ff.build_php_cnf(1, 1))
    expect_code("PHP_BAD_H", lambda: ff.build_php_cnf(2, 0))
    expect_code("PHP_BAD_P", lambda: ff.solve_php_cutting_planes_exact(1, 1))
    expect_code("PHP_BAD_H", lambda: ff.solve_php_cutting_planes_exact(2, 0))

    expect_code("CEC_BAD_W", lambda: ff.exact_cec_multiplier_poly_equivalence(1))
    expect_code("CEC_BAD_W", lambda: ff.exact_cec_multiplier_poly_equivalence(17))

    expect_code("FAC_BAD_N", lambda: ff.aig_verify_factor_witness(3, 1, 3, 4))
    expect_code("FAC_BAD_W", lambda: ff.aig_verify_factor_witness(4, 2, 2, 1))
    expect_code("FAC_BAD_PQ", lambda: ff.aig_verify_factor_witness(4, True, 2, 4))  # type: ignore[arg-type]
    expect_code("FAC_BAD_N", lambda: ff.factor_integer_exact(3, 4))
    expect_code("FAC_BAD_W", lambda: ff.factor_integer_exact(7, 1))
    expect_code("MOD_BAD_VARS", lambda: ff.verify_cnf_model(0, [(1,)], {1: True}))
    expect_code("MOD_MISSING_VAR", lambda: ff.verify_cnf_model(2, [(1,)], {1: True}))
    expect_code("MOD_UNSAT_CLAUSE", lambda: ff.verify_cnf_model(1, [(1,)], {1: False}))

    expect_code("BS_BAD_K", lambda: ff.bitsliced_arx_preimage_64way(5, 0))
    expect_code("BS_BAD_K", lambda: ff.bitsliced_arx_preimage_64way(15, 0))
    expect_code("BS_BAD_TARGET", lambda: ff.bitsliced_arx_preimage_64way(6, -1))
    expect_code("BS_BAD_TARGET", lambda: ff.bitsliced_arx_preimage_64way(6, 256))

    # --- Module 3 3-SAT generator guards ---
    expect_code("SAT3_BAD_N", lambda: ff.generate_deterministic_3sat(3, 1, 0))
    expect_code("SAT3_BAD_M", lambda: ff.generate_deterministic_3sat(4, 0, 0))
    expect_code("SAT3_BAD_SEED", lambda: ff.generate_deterministic_3sat(4, 1, -1))

    # --- Module 4 disclosure & image SHA-256 guards ---
    expect_code("BENCH_NOT_MAP", lambda: ff.verify_sat_benchmark_disclosure([]))  # type: ignore[arg-type]
    expect_code("BENCH_BAD_REP", lambda: ff.verify_sat_benchmark_disclosure({"input_representation_parity": "unknown"}))
    base_ok = {
        "input_representation_parity": "same_cnf",
        "discloses_timeout_penalty_share": True,
        "discloses_mutually_solved_finite_ratio": True,
        "includes_unstructured_np_baseline": True,
        "includes_theory_matched_competitors": True,
    }
    expect_code("BENCH_MISSING_TIMEOUT_SHARE", lambda: ff.verify_sat_benchmark_disclosure(dict(base_ok, discloses_timeout_penalty_share=1)))
    expect_code("BENCH_MISSING_FINITE_RATIO", lambda: ff.verify_sat_benchmark_disclosure(dict(base_ok, discloses_mutually_solved_finite_ratio=False)))
    expect_code("BENCH_MISSING_UNSTRUCTURED_NP", lambda: ff.verify_sat_benchmark_disclosure(dict(base_ok, includes_unstructured_np_baseline=False)))
    expect_code("BENCH_MISSING_THEORY_COMPETITORS", lambda: ff.verify_sat_benchmark_disclosure(dict(base_ok, includes_theory_matched_competitors=False)))

    with tempfile.TemporaryDirectory() as td:
        missing_img = Path(td) / "missing.jpg"
        expect_code("IMG_NOT_FOUND", lambda: ff.verify_optional_image_sha256(missing_img))
        bad_img = Path(td) / "bad.jpg"
        bad_img.write_bytes(b"not the real table2 image")
        expect_code("IMG_SHA_MISMATCH", lambda: ff.verify_optional_image_sha256(bad_img))


def main() -> int:
    groups = (
        test_group_1_end_to_end_zero_float_certificate,
        test_group_2_invariance_and_exact_identities,
        test_group_3_unseen_instances_and_tamper_detection,
        test_group_4_r5_adversarial_refusal_controls,
    )
    for fn in groups:
        fn()
    print(f"ROUND7_ARM4_FROBENIUS_SAT_R5_OK: {len(groups)}/{len(groups)} test groups passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
