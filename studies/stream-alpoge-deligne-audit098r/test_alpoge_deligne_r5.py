"""R5 mutation-hardened verification suite for alpoge_deligne_certifier.py (AUDIT-098)."""

from __future__ import annotations

from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import sys
from typing import Any

_HERE = str(Path(__file__).resolve().parent)
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import alpoge_deligne_certifier as cert


def expect_true(cond: bool, msg: str = "expected True") -> None:
    if not cond:
        raise AssertionError(msg)


def expect_false(cond: bool, msg: str = "expected False") -> None:
    if cond:
        raise AssertionError(msg)


def expect_eq(actual: Any, expected: Any, msg: str = "") -> None:
    if actual != expected:
        raise AssertionError(f"expected {expected!r}, got {actual!r}" + (f": {msg}" if msg else ""))


def expect_raises(exc_type: type[BaseException], fn: Any, *, match: str = "") -> None:
    try:
        fn()
    except exc_type as exc:
        if match and match not in str(exc):
            raise AssertionError(f"expected {match!r} in {str(exc)!r}") from exc
        return
    raise AssertionError(f"expected {exc_type.__name__} to be raised")


def test_cyclotomic_ring_exact_identities() -> None:
    # 1 + zeta_p + ... + zeta_p^{p-1} = 0 for primes p = 2, 3, 5, 7
    for p in (2, 3, 5, 7):
        acc = cert.cyc_zero(p)
        for e in range(p):
            acc = cert.cyc_add(acc, cert.cyc_power(p, e))
        expect_eq(cert.cyc_as_int(acc), 0, f"cyclotomic sum mod {p}")
        # zeta_p * conj(zeta_p) = 1
        z1 = cert.cyc_power(p, 1)
        prod = cert.cyc_mul(p, z1, cert.cyc_conj(p, z1))
        expect_eq(cert.cyc_as_int(prod), 1, f"norm(zeta_{p}) == 1")
        # Non-integer cyclotomic element returns None from cyc_as_int when p >= 3
        if p >= 3:
            expect_eq(cert.cyc_as_int(z1), None)
    # Scaling and error guards
    expect_eq(cert.cyc_scale_int(3, cert.cyc_power(5, 0)), (3, 0, 0, 0))
    expect_raises(ValueError, lambda: cert.cyc_zero(1))
    expect_raises(ValueError, lambda: cert.cyc_zero(True))
    expect_raises(ValueError, lambda: cert.cyc_power(1, 0))
    expect_raises(ValueError, lambda: cert.cyc_power(True, 0))
    expect_raises(ValueError, lambda: cert.cyc_add((1, 0), (1, 0, 0)))
    expect_raises(ValueError, lambda: cert.cyc_mul(5, (1, 0), (1, 0, 0, 0)))
    expect_raises(ValueError, lambda: cert.cyc_mul(5, (1, 0, 0, 0), (1, 0)))


def test_gf4_and_legendre_field_axioms() -> None:
    # F_4 multiplication table: w^2 = w + 1 (2*2 == 3), w*(w+1) = 1 (2*3 == 1), trace(2)=trace(3)=1
    expect_eq(cert.gf4_add(2, 3), 1)
    expect_eq(cert.gf4_mul(2, 2), 3)
    expect_eq(cert.gf4_mul(2, 3), 1)
    expect_eq(cert.gf4_mul(3, 3), 2)
    expect_eq(cert.gf4_mul(0, 3), 0)
    expect_eq(cert.gf4_trace(0), 0)
    expect_eq(cert.gf4_trace(1), 0)
    expect_eq(cert.gf4_trace(2), 1)
    expect_eq(cert.gf4_trace(3), 1)
    # Legendre symbol mod 5: squares {1, 4} -> +1, non-squares {2, 3} -> -1, 0 -> 0
    expect_eq([cert.legendre_mod_p(a, 5) for a in range(5)], [0, 1, -1, -1, 1])


def test_unitarity_and_path_sum_guards() -> None:
    u5 = cert.verify_path_kernel_unitarity_fp(5, 1, 2)
    expect_true(u5["passed"])
    expect_true(u5["all_diag_equal_q_pow_d"])
    expect_true(u5["all_offdiag_zero"])
    expect_eq(u5["matrix_size"], 5)

    u4 = cert.verify_path_kernel_unitarity_f4(1, 3)
    expect_true(u4["passed"])
    expect_eq(u4["matrix_size"], 4)

    expect_raises(ValueError, lambda: cert.verify_path_kernel_unitarity_fp(5, 1, 0))
    expect_raises(ValueError, lambda: cert.verify_path_kernel_unitarity_fp(5, 1, 5))
    expect_raises(ValueError, lambda: cert.verify_path_kernel_unitarity_f4(1, 0))
    expect_raises(ValueError, lambda: cert.verify_path_kernel_unitarity_f4(1, 4))
    expect_raises(ValueError, lambda: cert.compute_path_sum_fp(3, 1, 1, {}, 0))

    # Non-integer remainder raises ValueError cleanly
    bad_weights = {
        0: [[cert.cyc_power(3, 1)] * 3, [cert.cyc_power(3, 0)] * 3],
        1: [[cert.cyc_power(3, 0)] * 3, [cert.cyc_power(3, 0)] * 3],
        2: [[cert.cyc_power(3, 0)] * 3, [cert.cyc_power(3, 0)] * 3],
    }
    expect_raises(ValueError, lambda: cert.compute_path_sum_fp(3, 1, 2, bad_weights, 0))


def test_all_six_witnesses_and_strict_values() -> None:
    w1 = cert.certify_witness_w1_affine_line_conic()
    expect_true(w1["passed"])
    expect_eq(len(w1["cases"]), 5)
    expect_eq([c["p"] for c in w1["cases"]], [2, 3, 5, 7, 11])
    expect_eq([c["R_direct"] for c in w1["cases"]], [-2, -3, -5, -7, -11])
    expect_eq([c["signed_effective_trace"] for c in w1["cases"]], [2, 3, 5, 7, 11])
    expect_true(w1["singular_negative_control"]["violates_smooth_remainder_minus_p"])
    expect_eq(w1["singular_negative_control"]["R_singular"], 42)

    w2 = cert.certify_witness_w2_gm_nonvanishing_h1c()
    expect_true(w2["passed"])
    expect_eq(len(w2["cases"]), 5)
    expect_eq([c["signed_effective_trace"] for c in w2["cases"][:3]], [4, 6, 8])
    expect_eq([c["signed_effective_trace"] for c in w2["cases"][3:]], [11, 15])
    expect_eq([c["K_trace"] for c in w2["cases"][3:]], [10, 14])
    expect_true(w2["smooth_nongeneric_wl_negative_control"]["demonstrates_smooth_alone_insufficient_for_wl"])
    expect_eq(w2["smooth_nongeneric_wl_negative_control"]["R_nongeneric"], -14)

    w3 = cert.certify_witness_w3_elliptic_noether_b2()
    expect_true(w3["passed"])
    expect_eq(len(w3["cases"]), 3)
    expect_eq([c["a_p_trace"] for c in w3["cases"]], [-3, -1, -1])
    expect_eq([c["M_affine_points"] for c in w3["cases"]], [8, 8, 12])
    for c in w3["cases"]:
        expect_true(c["Y_smooth_at_Fp_points"])
        expect_eq(c["R_direct"], c["R_from_chars"])
        expect_true(c["R_sq"] <= c["hs03_bound_sq"])
    # Negative control for smoothness helper: singular point at c=1 on E/F_11 and at c=0 on E/F_5
    pts5 = cert._elliptic_affine_points(5, 1, 1)
    expect_false(cert._is_elliptic_path_hypersurface_smooth_fp(5, 1, pts5, 0, 0, 0, 0, 0))
    pts11 = cert._elliptic_affine_points(11, 1, 6)
    expect_false(cert._is_elliptic_path_hypersurface_smooth_fp(11, 1, pts11, 1, 1, 2, 1, 1))

    w4 = cert.certify_witness_w4_higher_dim_and_char2()
    expect_true(w4["passed"])
    expect_eq(len(w4["cases"]), 3)
    expect_eq([c["R_direct"] for c in w4["cases"]], [-4, -9, -16])
    expect_eq([c["R_from_chars"] for c in w4["cases"]], [-4, -9, -16])
    for c in w4["cases"]:
        expect_true(c["unitarity_passed"])

    w5 = cert.certify_witness_w5_lisse_quadratic_twist()
    expect_true(w5["passed"])
    expect_eq(len(w5["cases"]), 3)
    for c in w5["cases"]:
        expect_eq(c["M_twist"], 0)
        expect_eq(abs(c["R_nongeneric_smooth"]), c["p"] * (c["p"] - 1))
        expect_true(c["genericity_drop_confirmed"])
        expect_eq(c["R_generic"], c["R_generic_from_chars"])

    w6 = cert.certify_witness_w6_hs01_and_ad03_kummer()
    expect_true(w6["passed"])
    expect_true(w6["hs01_effective_positive"]["zero_pole_cancellation"])
    expect_eq(w6["hs01_effective_positive"]["distinct_eigenvalues"], 2)
    expect_false(w6["hs01_virtual_cancellation_control"]["zero_pole_cancellation"])
    expect_eq(w6["hs01_virtual_cancellation_control"]["surviving_poles"], [])
    kum = w6["ad03_kummer_extension_witness"]
    expect_true(kum["weil_relation_FTF_inv_eq_T_pow_inv_q"])
    expect_true(kum["t_minus_i_nonzero_nilpotent_unique_1d_subspace"])
    expect_true(kum["distinct_frobenius_weights"])
    expect_true(kum["indecomposable_refutes_hexagon_L89_91_direct_sum"])

    # Input validation guards on verify_hs01_rational_poles
    expect_raises(ValueError, lambda: cert.verify_hs01_rational_poles([(Fraction(0), 1)]))
    expect_raises(ValueError, lambda: cert.verify_hs01_rational_poles([(1, 1)]))  # type: ignore[list-item]
    expect_raises(ValueError, lambda: cert.verify_hs01_rational_poles([(Fraction(2), True)]))


def test_top_level_certificate_and_cli() -> None:
    rep = cert.run_all_certifications()
    expect_true(rep["passed"])
    expect_true(rep["all_witnesses_passed"])
    expect_eq(rep["witness_count"], 6)
    expect_eq(rep["honest_novelty_tier"], "N0")
    expect_eq(len(rep["canonical_inner_sha256"]), 64)

    # CLI --json output and text output
    old_stdout = sys.stdout
    buf_json = io.StringIO()
    buf_txt = io.StringIO()
    try:
        sys.stdout = buf_json
        rc1 = cert.main(["--json"])
        sys.stdout = buf_txt
        rc2 = cert.main([])
    finally:
        sys.stdout = old_stdout
    expect_eq(rc1, 0)
    expect_eq(rc2, 0)
    parsed = json.loads(buf_json.getvalue())
    expect_eq(parsed["canonical_inner_sha256"], rep["canonical_inner_sha256"])
    expect_true("AUDIT-098 passed=True" in buf_txt.getvalue())

    # Validate clean certificate and reject every tampered variant with single-guard isolation (rehashed!)
    val_ok = cert.validate_certificate(parsed)
    expect_true(val_ok["valid"])
    expect_eq(val_ok["witness_count"], 6)
    expect_eq(val_ok["canonical_inner_sha256"], rep["canonical_inner_sha256"])

    inner_keys = (
        "audit_id",
        "target",
        "execution_mode",
        "honest_novelty_tier",
        "main_proof_verdict",
        "hexagon_v1_erratum",
        "witness_count",
        "all_witnesses_passed",
        "witnesses",
    )

    def _rehash(d: dict[str, Any]) -> dict[str, Any]:
        out = dict(d)
        inner = {k: out.get(k) for k in inner_keys}
        out["canonical_inner_sha256"] = hashlib.sha256(
            json.dumps(inner, sort_keys=True, separators=(",", ":")).encode("utf-8")
        ).hexdigest()
        return out

    expect_raises(ValueError, lambda: cert.validate_certificate([]), match="mapping")
    # AD98-BYPASS-03: unbound extra top-level key rejected
    expect_raises(ValueError, lambda: cert.validate_certificate({**parsed, "forged_claim": "N2"}), match="top-level keys")
    missing_key = dict(parsed)
    del missing_key["audit_id"]
    expect_raises(ValueError, lambda: cert.validate_certificate(missing_key), match="top-level keys")
    # AD98-BYPASS-02: recursive float smuggling rejected (constructed via json.loads so zero float literals in source)
    smuggled = json.loads("3.14159")
    bad_float_w = [dict(w) for w in parsed["witnesses"]]
    bad_float_w[0]["smuggled_float"] = smuggled
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witnesses": bad_float_w})), match="floating-point")
    # Metadata & exact string field guards
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "schema": "wrong"})), match="schema")
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "audit_id": "OTHER"})), match="audit_id")
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "execution_mode": "fake"})), match="execution_mode")
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "honest_novelty_tier": "N1"})), match="N0")
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "main_proof_verdict": "WRONG"})), match="main_proof_verdict")
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "hexagon_v1_erratum": "NONE"})), match="hexagon_v1_erratum")
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "target": ""})), match="target")
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "target": 123})), match="target")
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "passed": 1})), match="booleans")
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "all_witnesses_passed": 1})), match="booleans")
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "passed": False})), match="passed=True")
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "all_witnesses_passed": False})), match="passed=True")
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witness_count": True})), match="witness_count")
    expect_raises(ValueError, lambda: cert.validate_certificate({**parsed, "witness_count": Fraction(6, 1)}), match="witness_count")
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witnesses": tuple(parsed["witnesses"])})), match="witness_count")
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witness_count": 5})), match="witness_count")
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witness_count": 5, "witnesses": parsed["witnesses"][:-1]})), match="witness_count")
    swapped = list(parsed["witnesses"])
    swapped[0], swapped[1] = swapped[1], swapped[0]
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witnesses": swapped})), match="witness_ids")
    bad_w = [dict(w) for w in parsed["witnesses"]]
    bad_w[0]["passed"] = False
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witnesses": bad_w})), match="every witness")
    # AD98-BYPASS-01: hollow shell witnesses & tampered witness payloads rejected
    hollow = _rehash({**parsed, "witnesses": [{"witness_id": wid, "passed": True} for wid in cert.EXPECTED_WITNESS_IDS]})
    expect_raises(ValueError, lambda: cert.validate_certificate(hollow), match="case records")
    # W1 cases type/count/element & negative control guards
    w1_short = [dict(w) for w in parsed["witnesses"]]
    w1_short[0]["cases"] = w1_short[0]["cases"][:-1]
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witnesses": w1_short})), match="case records")
    w1_bad_case = [dict(w) for w in parsed["witnesses"]]
    w1_bad_case[0]["cases"] = [{**c} for c in w1_bad_case[0]["cases"]]
    w1_bad_case[0]["cases"][0]["passed"] = False
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witnesses": w1_bad_case})), match="failing case")
    w1_nonmap_case = [dict(w) for w in parsed["witnesses"]]
    w1_nonmap_case[0]["cases"] = ["bad"] + list(w1_nonmap_case[0]["cases"][1:])
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witnesses": w1_nonmap_case})), match="failing case")
    w1_bad_ctrl = [dict(w) for w in parsed["witnesses"]]
    w1_bad_ctrl[0]["singular_negative_control"] = {"violates_smooth_remainder_minus_p": False}
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witnesses": w1_bad_ctrl})), match="negative control")
    w1_nonmap_ctrl = [dict(w) for w in parsed["witnesses"]]
    w1_nonmap_ctrl[0]["singular_negative_control"] = "bad"
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witnesses": w1_nonmap_ctrl})), match="negative control")
    # W6 payload guards (eff, virt, kum: non-mapping and wrong flag)
    w6_bad_eff = [dict(w) for w in parsed["witnesses"]]
    w6_bad_eff[5]["hs01_effective_positive"] = {"zero_pole_cancellation": False}
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witnesses": w6_bad_eff})), match="hs01_effective_positive")
    w6_nonmap_eff = [dict(w) for w in parsed["witnesses"]]
    w6_nonmap_eff[5]["hs01_effective_positive"] = []
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witnesses": w6_nonmap_eff})), match="hs01_effective_positive")
    w6_bad_virt = [dict(w) for w in parsed["witnesses"]]
    w6_bad_virt[5]["hs01_virtual_cancellation_control"] = {"zero_pole_cancellation": True}
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witnesses": w6_bad_virt})), match="hs01_virtual_cancellation_control")
    w6_nonmap_virt = [dict(w) for w in parsed["witnesses"]]
    w6_nonmap_virt[5]["hs01_virtual_cancellation_control"] = []
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witnesses": w6_nonmap_virt})), match="hs01_virtual_cancellation_control")
    w6_bad_kum = [dict(w) for w in parsed["witnesses"]]
    w6_bad_kum[5]["ad03_kummer_extension_witness"] = {"indecomposable_refutes_hexagon_L89_91_direct_sum": False}
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witnesses": w6_bad_kum})), match="ad03_kummer_extension_witness")
    w6_nonmap_kum = [dict(w) for w in parsed["witnesses"]]
    w6_nonmap_kum[5]["ad03_kummer_extension_witness"] = []
    expect_raises(ValueError, lambda: cert.validate_certificate(_rehash({**parsed, "witnesses": w6_nonmap_kum})), match="ad03_kummer_extension_witness")
    # SHA-256 format (length, type, lowercase hex) and mismatch guards
    expect_raises(ValueError, lambda: cert.validate_certificate({**parsed, "canonical_inner_sha256": "deadbeef"}), match="64-hex")
    expect_raises(ValueError, lambda: cert.validate_certificate({**parsed, "canonical_inner_sha256": 123}), match="64-hex")
    expect_raises(ValueError, lambda: cert.validate_certificate({**parsed, "canonical_inner_sha256": "A" * 64}), match="64-hex")
    expect_raises(ValueError, lambda: cert.validate_certificate({**parsed, "canonical_inner_sha256": "0" * 64}), match="mismatch")


def run_all() -> None:
    for fn in (
        test_cyclotomic_ring_exact_identities,
        test_gf4_and_legendre_field_axioms,
        test_unitarity_and_path_sum_guards,
        test_all_six_witnesses_and_strict_values,
        test_top_level_certificate_and_cli,
    ):
        fn()


if __name__ == "__main__":
    run_all()
    print("test_alpoge_deligne_r5: ALL OK (5/5)")
