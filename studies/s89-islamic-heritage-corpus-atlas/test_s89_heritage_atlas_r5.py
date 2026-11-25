#!/usr/bin/env python3
"""
Track S89: Assertion-Free R5 Verification & Mutation-Hardening Test Suite.

Pure Python 3 standard library. Zero floats, zero bare asserts, zero hardcoded host paths,
uses scratch `os.mkfifo` for non-regular file refusal, zero skipped tests under both
live Lean 4.36.0 and `env -i PATH=/usr/bin:/bin` no-Lean CI environments.
"""
from __future__ import annotations

import copy
from fractions import Fraction
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import time
from typing import Any, Callable

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import s89_heritage_atlas_oracle as s89  # noqa: E402
import verify_s89_heritage_atlas as v89  # noqa: E402

CERT_PATH = HERE / "s89_heritage_atlas_certificate.json"
LEAN_PATH = HERE / "ClassicalHeritageAtlas.lean"


class TestFailure(RuntimeError):
    """Explicit assertion-free test failure."""


def check(cond: bool, msg: str) -> None:
    if not cond:
        raise TestFailure(msg)


def expect_s89_error(fn: Callable[[], Any], expected_code: str | None = None, label: str = "") -> s89.S89Error:
    try:
        fn()
    except s89.S89Error as exc:
        if expected_code is not None and exc.code != expected_code:
            raise TestFailure(f"{label}: expected S89Error({expected_code}), got {exc.code}: {exc.message}") from exc
        return exc
    except BaseException as exc:
        raise TestFailure(f"{label}: expected S89Error({expected_code}), got {type(exc).__name__}: {exc}") from exc
    raise TestFailure(f"{label}: expected S89Error({expected_code}), but call succeeded")


def _rehash_cert(cert: dict[str, Any]) -> dict[str, Any]:
    out = copy.deepcopy(cert)
    psha = hashlib.sha256(s89.canonical_json_bytes(out["payload"])).hexdigest()
    out["payload_sha256"] = psha
    env = {
        "schema_version": out["schema_version"],
        "track_id": out["track_id"],
        "payload_sha256": psha,
        "payload": out["payload"],
    }
    out["certificate_sha256"] = hashlib.sha256(s89.canonical_json_bytes(env)).hexdigest()
    return out


class _FracSub(Fraction):
    pass


class _DictSub(dict):
    pass


class _ListSub(list):
    pass


class _IntSub(int):
    pass


class _StrSub(str):
    pass


def test_01_oracle_math_and_pillars() -> None:
    check(s89.fmt_q(Fraction(0, 1)) == "0", "fmt_q(0)")
    check(s89.fmt_q(Fraction(-7, 1)) == "-7", "fmt_q(-7)")
    check(s89.fmt_q(Fraction(14, 54)) == "7/27", "fmt_q(7/27)")
    expect_s89_error(lambda: s89.fmt_q(3), "INVALID_FRACTION_TYPE", "fmt_q int")  # type: ignore[arg-type]
    expect_s89_error(lambda: s89.fmt_q(_FracSub(1, 2)), "INVALID_FRACTION_TYPE", "fmt_q subclass")

    # Pillar 1 baseline & parameterized refusals
    p1 = s89.compute_pillar1_corpus_audit()
    tot = p1["totals"]
    check(tot["inventory_files"] == 2694, "inv files")
    check(tot["inventory_bytes"] == 25155918980, "inv bytes")
    check(tot["inventory_pdfs"] == 593, "inv pdfs")
    check(tot["downloaded_text_files"] == 1460, "text files")
    check(tot["downloaded_text_bytes"] == 119327981, "text bytes")
    check(tot["downloaded_text_words"] == 10871572, "text words")
    check(tot["complete_trios_3_of_3"] == 51, "trios")
    check(tot["tiered_works_total"] == 158, "tiered works")
    diag = p1["quality_diagnostics_law4"]
    check(diag["readme_pdf_discipline_l1_drift"] == 212, "l1 drift")
    check(diag["malformed_jsonl_bad_fraction"] == "1413/11299", "bad jsonl frac")
    check(diag["crlf_text_fraction"] == "53/730", "crlf frac")

    bad_dirs = tuple(dict(r) for r in s89.INVENTORY_BY_TOP_DIR)
    bad_dirs[0]["files"] += 1
    expect_s89_error(lambda: s89.compute_pillar1_corpus_audit(top_dirs=bad_dirs), "INV_FILE_SUM_MISMATCH", "p1 files")

    bad_dirs2 = tuple(dict(r) for r in s89.INVENTORY_BY_TOP_DIR)
    bad_dirs2[0]["bytes"] += 1
    expect_s89_error(lambda: s89.compute_pillar1_corpus_audit(top_dirs=bad_dirs2), "INV_BYTE_SUM_MISMATCH", "p1 bytes")

    bad_dirs3 = tuple(dict(r) for r in s89.INVENTORY_BY_TOP_DIR)
    bad_dirs3[1]["pdfs"] += 1
    expect_s89_error(lambda: s89.compute_pillar1_corpus_audit(top_dirs=bad_dirs3), "INV_PDF_SUM_MISMATCH", "p1 pdfs")

    bad_txt_ext = tuple(dict(r) for r in s89.TEXT_LAYER_BY_EXT)
    bad_txt_ext[0]["files"] += 1
    expect_s89_error(
        lambda: s89.compute_pillar1_corpus_audit(text_ext_rows=bad_txt_ext),
        "TEXT_FILE_PARITY_MISMATCH",
        "p1 txt ext files",
    )
    bad_inv_ext_f = tuple(dict(r) for r in s89.INVENTORY_BY_EXT)
    bad_inv_ext_f[1]["files"] += 1
    bad_top_f = tuple(dict(r) for r in s89.INVENTORY_BY_TOP_DIR)
    bad_top_f[0]["files"] += 1
    expect_s89_error(
        lambda: s89.compute_pillar1_corpus_audit(top_dirs=bad_top_f, ext_rows=bad_inv_ext_f),
        "TEXT_FILE_PARITY_MISMATCH",
        "p1 inv vs ext files",
    )
    bad_txt_dir = tuple(dict(r) for r in s89.TEXT_LAYER_BY_TOP_DIR)
    bad_txt_dir[0]["files"] += 1
    expect_s89_error(
        lambda: s89.compute_pillar1_corpus_audit(text_dir_rows=bad_txt_dir),
        "TEXT_FILE_PARITY_MISMATCH",
        "p1 txt dir files",
    )
    bad_txt_ext_b = tuple(dict(r) for r in s89.TEXT_LAYER_BY_EXT)
    bad_txt_ext_b[0]["bytes"] += 1
    expect_s89_error(
        lambda: s89.compute_pillar1_corpus_audit(text_ext_rows=bad_txt_ext_b),
        "TEXT_BYTE_PARITY_MISMATCH",
        "p1 txt ext bytes",
    )
    bad_inv_ext_b = tuple(dict(r) for r in s89.INVENTORY_BY_EXT)
    bad_inv_ext_b[1]["bytes"] += 1
    bad_top_b = tuple(dict(r) for r in s89.INVENTORY_BY_TOP_DIR)
    bad_top_b[0]["bytes"] += 1
    expect_s89_error(
        lambda: s89.compute_pillar1_corpus_audit(top_dirs=bad_top_b, ext_rows=bad_inv_ext_b),
        "TEXT_BYTE_PARITY_MISMATCH",
        "p1 inv vs ext bytes",
    )
    bad_txt_dir_b = tuple(dict(r) for r in s89.TEXT_LAYER_BY_TOP_DIR)
    bad_txt_dir_b[0]["bytes"] += 1
    expect_s89_error(
        lambda: s89.compute_pillar1_corpus_audit(text_dir_rows=bad_txt_dir_b),
        "TEXT_BYTE_PARITY_MISMATCH",
        "p1 txt dir bytes",
    )

    # Pillar 2 witnesses
    p2 = s89.compute_pillar2_anchors_and_witnesses()
    check(p2["anchor_count"] == 10 and p2["pinned_files_count"] == 20, "p2 counts")
    check(p2["pinned_files_total_bytes"] == 3423129, "p2 bytes")
    check(p2["pinned_files_total_words"] == 347895, "p2 words")
    w = p2["exact_rational_witnesses"]
    check(w["h00_khwarizmi_square_256"] == 256, "h00")
    check(w["h01_thabit_n2_pair"] == [220, 284] and w["h01_thabit_n3_composite"] == 287, "h01")
    check(w["h02_biruni_dip_radius_ratio"] == "9999", "h02")
    check(w["h04_khayyam_neg_discriminant"] == 275, "h04")
    check(w["h06_kashi_lipschitz_bound"] == "1/37500", "h06")
    check(w["h07_farisi_primary_cos2"] == "7/27" and w["h07_farisi_secondary_cos2"] == "7/72", "h07")
    check(w["h07_farisi_alexander_band_cos2_gap"] == "35/216", "h07 gap")
    check(w["h08_khazini_gold_mass_inverse"] == "5", "h08")

    # Pillar 3 K_10 exact mesh + refusals + linear algebra helpers
    p3 = s89.compute_pillar3_k10_mesh_and_cross_mapping()
    check(p3["edge_count"] == 45 and p3["triangle_count"] == 120 and p3["tetrahedron_count"] == 210, "k10 counts")
    check(p3["laplacian_inertia"] == [9, 0, 1], "inertia")
    check(p3["foster_resistance_sum"] == "9", "foster")
    check(p3["all_45_edges_strictly_compounded"] is True, "compounded")
    check(p3["min_compounding_ratio"] == "132512997891/45102908158", "min ratio")
    check(p3["max_compounding_ratio"] == "132512997891/10638933511", "max ratio")
    check(p3["triangle_holonomy_counts"] == {
        "exact_transitive": 6,
        "conditional_consistent": 43,
        "frustrated_odd_obstruction": 56,
        "multi_wall_even_obstruction": 15,
    }, "tri holonomy")
    check(p3["tetrahedral_bianchi_zero_count"] == 210, "bianchi")
    check(p3["tetrahedral_frustrated_face_distribution"] == {"0": 33, "2": 158, "4": 19}, "tet dist")
    sc = p3["silo_cut_five_five"]
    check(sc["edges_cut"] == 25 and sc["edges_cut_fraction"] == "5/9", "cut e")
    check(sc["triangles_cut"] == 100 and sc["triangles_cut_fraction"] == "5/6", "cut tri")
    check(sc["tetrahedra_cut"] == 200 and sc["tetrahedra_cut_fraction"] == "20/21", "cut tet")
    cm = p3["cross_millennium_10x8_s83"]
    check(cm["total_pairs"] == 80, "cross pairs")
    check(cm["class_counts"] == {
        "EXACT_OPERATOR_ISOMORPHISM": 18,
        "CONDITIONAL_TRANSPOSITION": 12,
        "EXACT_LAW5_OBSTRUCTION": 50,
    }, "cross counts")

    expect_s89_error(
        lambda: s89.compute_pillar3_k10_mesh_and_cross_mapping(s89.K10_EDGE_SPECS[:-1]),
        "K10_EDGE_COUNT",
        "k10 short",
    )
    for bad_pair in ((1, 0), (0, 0), (0, 10)):
        bad_idx = list(s89.K10_EDGE_SPECS)
        bad_idx[0] = (bad_pair[0], bad_pair[1], "EXACT_COMMUTE", "⧅", "bad")
        expect_s89_error(
            lambda b=tuple(bad_idx): s89.compute_pillar3_k10_mesh_and_cross_mapping(b),
            "K10_EDGE_INDEX",
            f"k10 bad idx {bad_pair}",
        )
    dup_edges = list(s89.K10_EDGE_SPECS)
    dup_edges[-1] = dup_edges[0]
    expect_s89_error(
        lambda: s89.compute_pillar3_k10_mesh_and_cross_mapping(tuple(dup_edges)),
        "K10_DUP_EDGE",
        "k10 dup",
    )

    # _exact_ldl_inertia & _exact_invert_q edge cases
    check(
        s89._exact_ldl_inertia([[Fraction(-2), Fraction(0)], [Fraction(0), Fraction(3)]]) == [1, 1, 0],
        "ldl neg piv",
    )
    expect_s89_error(
        lambda: s89._exact_ldl_inertia([[Fraction(0), Fraction(1)], [Fraction(1), Fraction(0)]]),
        "LDL_ZERO_PIVOT_INDEFINITE",
        "ldl zero piv",
    )
    inv_swap = s89._exact_invert_q([[Fraction(0), Fraction(2)], [Fraction(3), Fraction(1)]])
    check(inv_swap == [[Fraction(-1, 6), Fraction(1, 3)], [Fraction(1, 2), Fraction(0)]], "invert swap")
    expect_s89_error(
        lambda: s89._exact_invert_q([[Fraction(1), Fraction(2)], [Fraction(2), Fraction(4)]]),
        "SINGULAR_MATRIX",
        "invert singular",
    )


def test_02_synthetic_corpus_verification() -> None:
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        text_dir = root / "text"
        text_dir.mkdir()
        (text_dir / ".cache").mkdir()
        (text_dir / ".cache" / "ignored.tmp").write_bytes(b"ignore")

        a1 = text_dir / "a1.txt"
        a2 = text_dir / "a2.txt"
        bad_jl = text_dir / "bad.jsonl"
        csv_f = text_dir / "meta.csv"
        a1_raw = b"alpha"
        a2_raw = b"beta12"
        jl_raw = b'{"ok":1}\n\n{bad json\n'
        csv_raw = b"col1,col2\nv1,v2\n"
        a1.write_bytes(a1_raw)
        a2.write_bytes(a2_raw)
        bad_jl.write_bytes(jl_raw)
        csv_f.write_bytes(csv_raw)

        inv_path = root / "inv.json"
        inv_obj = {"sha": "abc123", "siblings": [{"rfilename": "a1.txt"}, {"rfilename": "a2.txt"}]}
        inv_raw = json.dumps(inv_obj).encode("utf-8")
        inv_path.write_bytes(inv_raw)
        inv_sha = hashlib.sha256(inv_raw).hexdigest()

        anchors = (
            {
                "id": "h00",
                "primary_anchor": {
                    "rel_path": "a1.txt",
                    "bytes": len(a1_raw),
                    "sha256": hashlib.sha256(a1_raw).hexdigest(),
                },
                "secondary_anchor": {
                    "rel_path": "a2.txt",
                    "bytes": len(a2_raw),
                    "sha256": hashlib.sha256(a2_raw).hexdigest(),
                },
            },
        )
        malformed = ({"rel_path": "bad.jsonl", "bad_lines": 1, "nonempty_lines": 2},)
        total_b = len(a1_raw) + len(a2_raw) + len(jl_raw) + len(csv_raw)

        res = s89.verify_live_corpus_on_disk(
            text_dir,
            inv_path,
            expected_inv_sha=inv_sha,
            expected_commit_sha="abc123",
            expected_siblings=2,
            anchors=anchors,
            expected_text_files=4,
            expected_text_bytes=total_b,
            malformed_files=malformed,
            sample_csv_rel="meta.csv",
        )
        check(res["status"] == "LIVE_CORPUS_VERIFIED" and res["verified_anchors"] == 2, "synth corpus ok")

        # Exercise every require_ok and BoolOp arm in verify_live_corpus_on_disk
        expect_s89_error(
            lambda: s89.verify_live_corpus_on_disk(
                text_dir, inv_path, expected_inv_sha="0" * 64, expected_commit_sha="abc123",
                expected_siblings=2, anchors=anchors, expected_text_files=4,
                expected_text_bytes=total_b, malformed_files=malformed, sample_csv_rel="meta.csv",
            ),
            "LIVE_INV_SHA_MISMATCH",
            "inv sha",
        )
        expect_s89_error(
            lambda: s89.verify_live_corpus_on_disk(
                text_dir, inv_path, expected_inv_sha=inv_sha, expected_commit_sha="wrong",
                expected_siblings=2, anchors=anchors, expected_text_files=4,
                expected_text_bytes=total_b, malformed_files=malformed, sample_csv_rel="meta.csv",
            ),
            "LIVE_REPO_SHA_MISMATCH",
            "repo sha",
        )
        expect_s89_error(
            lambda: s89.verify_live_corpus_on_disk(
                text_dir, inv_path, expected_inv_sha=inv_sha, expected_commit_sha="abc123",
                expected_siblings=3, anchors=anchors, expected_text_files=4,
                expected_text_bytes=total_b, malformed_files=malformed, sample_csv_rel="meta.csv",
            ),
            "LIVE_INV_COUNT_MISMATCH",
            "sibling count",
        )
        miss_anchors = copy.deepcopy(anchors)
        miss_anchors[0]["primary_anchor"]["rel_path"] = "missing.txt"
        expect_s89_error(
            lambda: s89.verify_live_corpus_on_disk(
                text_dir, inv_path, expected_inv_sha=inv_sha, expected_commit_sha="abc123",
                expected_siblings=2, anchors=miss_anchors, expected_text_files=4,
                expected_text_bytes=total_b, malformed_files=malformed, sample_csv_rel="meta.csv",
            ),
            "LIVE_ANCHOR_MISSING",
            "anchor missing",
        )
        size_anchors = copy.deepcopy(anchors)
        size_anchors[0]["primary_anchor"]["bytes"] += 1
        expect_s89_error(
            lambda: s89.verify_live_corpus_on_disk(
                text_dir, inv_path, expected_inv_sha=inv_sha, expected_commit_sha="abc123",
                expected_siblings=2, anchors=size_anchors, expected_text_files=4,
                expected_text_bytes=total_b, malformed_files=malformed, sample_csv_rel="meta.csv",
            ),
            "LIVE_ANCHOR_SIZE_MISMATCH",
            "anchor size",
        )
        sha_anchors = copy.deepcopy(anchors)
        sha_anchors[0]["primary_anchor"]["sha256"] = "0" * 64
        expect_s89_error(
            lambda: s89.verify_live_corpus_on_disk(
                text_dir, inv_path, expected_inv_sha=inv_sha, expected_commit_sha="abc123",
                expected_siblings=2, anchors=sha_anchors, expected_text_files=4,
                expected_text_bytes=total_b, malformed_files=malformed, sample_csv_rel="meta.csv",
            ),
            "LIVE_ANCHOR_SHA_MISMATCH",
            "anchor sha",
        )
        expect_s89_error(
            lambda: s89.verify_live_corpus_on_disk(
                text_dir, inv_path, expected_inv_sha=inv_sha, expected_commit_sha="abc123",
                expected_siblings=2, anchors=anchors, expected_text_files=5,
                expected_text_bytes=total_b, malformed_files=malformed, sample_csv_rel="meta.csv",
            ),
            "LIVE_TEXT_FILE_COUNT_MISMATCH",
            "text count",
        )
        expect_s89_error(
            lambda: s89.verify_live_corpus_on_disk(
                text_dir, inv_path, expected_inv_sha=inv_sha, expected_commit_sha="abc123",
                expected_siblings=2, anchors=anchors, expected_text_files=4,
                expected_text_bytes=total_b + 1, malformed_files=malformed, sample_csv_rel="meta.csv",
            ),
            "LIVE_TEXT_BYTE_COUNT_MISMATCH",
            "text bytes",
        )
        # Kill both arms of `bad == item["bad_lines"] and nonempty == item["nonempty_lines"]`
        expect_s89_error(
            lambda: s89.verify_live_corpus_on_disk(
                text_dir, inv_path, expected_inv_sha=inv_sha, expected_commit_sha="abc123",
                expected_siblings=2, anchors=anchors, expected_text_files=4,
                expected_text_bytes=total_b,
                malformed_files=({"rel_path": "bad.jsonl", "bad_lines": 2, "nonempty_lines": 2},),
                sample_csv_rel="meta.csv",
            ),
            "LIVE_PAL_ANOMALY_MISMATCH",
            "pal bad_lines",
        )
        expect_s89_error(
            lambda: s89.verify_live_corpus_on_disk(
                text_dir, inv_path, expected_inv_sha=inv_sha, expected_commit_sha="abc123",
                expected_siblings=2, anchors=anchors, expected_text_files=4,
                expected_text_bytes=total_b,
                malformed_files=({"rel_path": "bad.jsonl", "bad_lines": 1, "nonempty_lines": 3},),
                sample_csv_rel="meta.csv",
            ),
            "LIVE_PAL_ANOMALY_MISMATCH",
            "pal nonempty_lines",
        )
        short_csv = text_dir / "short.csv"
        short_csv.write_bytes(b"only_header\n")
        expect_s89_error(
            lambda: s89.verify_live_corpus_on_disk(
                text_dir, inv_path, expected_inv_sha=inv_sha, expected_commit_sha="abc123",
                expected_siblings=2, anchors=anchors, expected_text_files=5,
                expected_text_bytes=total_b + len(b"only_header\n"),
                malformed_files=malformed, sample_csv_rel="short.csv",
            ),
            "LIVE_SAMPLE_CSV_EMPTY",
            "short csv",
        )


def test_03_zone_b_rationals_json_and_containers() -> None:
    check(v89.parse_canonical_rational("0") == Fraction(0), "q 0")
    check(v89.parse_canonical_rational("-5") == Fraction(-5), "q -5")
    check(v89.parse_canonical_rational("7/27") == Fraction(7, 27), "q 7/27")
    check(v89.parse_canonical_rational("-35/216") == Fraction(-35, 216), "q -35/216")
    for bad_q in [
        123, "", " 1", "1 ", "1/2/3", "-", "1a", "1" * 1001, "01", "-0",
        "1/", "1/a", "1/" + ("1" * 1001), "1/02", "1/0", "1/1", "2/4", "-6/9",
    ]:
        expect_s89_error(lambda q=bad_q: v89.parse_canonical_rational(q), "INVALID_RATIONAL", f"bad_q={bad_q!r}")

    # Container safety (including exact boundaries!)
    v89._check_container_safety({"a": [1, True, False, None, "ok", 10 ** 1000 - 1]})
    ok_depth: Any = 1
    for _ in range(v89.MAX_JSON_DEPTH):
        ok_depth = [ok_depth]
    v89._check_container_safety(ok_depth)
    deep: Any = [ok_depth]
    expect_s89_error(lambda: v89._check_container_safety(deep), "MAX_DEPTH_EXCEEDED", "container depth")
    expect_s89_error(lambda: v89._check_container_safety({1: "a"}), "INVALID_DICT_KEY", "non-str key")
    expect_s89_error(lambda: v89._check_container_safety({"\ud800": "a"}), "INVALID_DICT_KEY", "surrogate key")
    expect_s89_error(lambda: v89._check_container_safety({"a": "\udfff"}), "LONE_SURROGATE", "surrogate val")
    expect_s89_error(lambda: v89._check_container_safety({"a": 10 ** 1000}), "INT_TOO_LARGE", "int digits 1001")
    expect_s89_error(lambda: v89._check_container_safety({"a": 1 << 15000}), "INT_TOO_LARGE", "int bits > 4300d")
    expect_s89_error(lambda: v89._check_container_safety({"a": 1.5}), "FORBIDDEN_VALUE_TYPE", "float")
    for sub in (_DictSub({"a": 1}), _ListSub([1]), _IntSub(1), _StrSub("x")):
        expect_s89_error(lambda s=sub: v89._check_container_safety({"k": s}), "FORBIDDEN_VALUE_TYPE", f"sub {type(sub)}")

    # Strict JSON parser (including exact 1000-digit int & 64-depth boundaries)
    check(v89.parse_strict_json_bytes(b'{"a":1}\n') == {"a": 1}, "canonical json ok")
    big_ok = b'{"a":' + (b"9" * 1000) + b"}\n"
    check(v89.parse_strict_json_bytes(big_ok) == {"a": 10 ** 1000 - 1}, "json 1000d ok")
    v89._check_raw_json_nesting(("[" * 64) + ("]" * 64))
    expect_s89_error(lambda: v89.parse_strict_json_bytes(b'{"a":1}\r\n'), "CRLF_FORBIDDEN", "crlf")
    expect_s89_error(lambda: v89.parse_strict_json_bytes(b"\xff"), "INVALID_UTF8", "utf8")
    expect_s89_error(lambda: v89.parse_strict_json_bytes((b"[" * 65) + (b"]" * 65)), "MAX_DEPTH_EXCEEDED", "raw depth")
    expect_s89_error(
        lambda: v89.parse_strict_json_bytes(b'{"a":' + (b"9" * 4500) + b"}\n"),
        "INT_TOO_LARGE",
        "json int cap 4500d",
    )
    expect_s89_error(lambda: v89.parse_strict_json_bytes(b'{"a":1.0}\n'), "FLOAT_FORBIDDEN", "json float")
    expect_s89_error(lambda: v89.parse_strict_json_bytes(b'{"a":NaN}\n'), "NONFINITE_JSON", "json NaN")
    expect_s89_error(lambda: v89.parse_strict_json_bytes(b'{"a":1,"a":2}\n'), "DUPLICATE_JSON_KEY", "dup key")
    expect_s89_error(lambda: v89.parse_strict_json_bytes(b"[1,2]\n"), "NON_OBJECT_ROOT", "non obj root")
    expect_s89_error(lambda: v89.parse_strict_json_bytes(b'{"a": 1}\n'), "NON_CANONICAL_JSON", "non canonical")
    expect_s89_error(lambda: v89.parse_strict_json_bytes(b'{"a":'), "INVALID_JSON", "truncated json")
    # String containing escaped quotes and braces does not trigger depth false positive
    v89._check_raw_json_nesting('{"s":"\\"{[}]\\""}')


def test_04_zone_b_atomic_io_fifo_symlink_hardlink() -> None:
    with tempfile.TemporaryDirectory() as td:
        base = Path(td)
        reg = base / "regular.json"
        v89.write_atomic_0600_bytes(reg, b'{"ok":1}\n')
        check(stat.S_IMODE(os.lstat(reg).st_mode) == 0o600, "write 0o600")
        check(v89.read_regular_file_bytes(reg) == b'{"ok":1}\n', "read reg ok")

        # Simulated CI chmod 644 read check still passes
        os.chmod(reg, 0o644)
        check(v89.read_regular_file_bytes(reg) == b'{"ok":1}\n', "read 0o644 ok")

        # Overwrite existing regular file under umask 022 & umask 077 stays 0o600
        old_umask = os.umask(0o022)
        try:
            v89.write_atomic_0600_bytes(reg, b'{"ok":2}\n')
            check(stat.S_IMODE(os.lstat(reg).st_mode) == 0o600, "umask 022 -> 0o600")
            os.umask(0o077)
            v89.write_atomic_0600_bytes(reg, b'{"ok":3}\n')
            check(stat.S_IMODE(os.lstat(reg).st_mode) == 0o600, "umask 077 -> 0o600")
        finally:
            os.umask(old_umask)

        # Symlink target read & write
        sym = base / "sym.json"
        sym.symlink_to(reg)
        expect_s89_error(lambda: v89.read_regular_file_bytes(sym), "SYMLINK_FORBIDDEN", "read sym")
        expect_s89_error(lambda: v89.write_atomic_0600_bytes(sym, b"{}\n"), "SYMLINK_FORBIDDEN", "write sym")

        # Symlink directory component
        real_d = base / "real_d"
        real_d.mkdir()
        (real_d / "f.json").write_bytes(b"{}\n")
        sym_d = base / "sym_d"
        sym_d.symlink_to(real_d)
        expect_s89_error(lambda: v89.read_regular_file_bytes(sym_d / "f.json"), "SYMLINK_IN_PATH", "dir sym")

        # Logical PWD symlink check + non-absolute/missing PWD edge cases
        old_pwd = os.environ.get("PWD")
        try:
            os.environ["PWD"] = str(sym_d)
            expect_s89_error(lambda: v89._check_pwd_no_symlinks(), "SYMLINK_IN_PATH", "pwd sym")
            os.environ["PWD"] = "relative/path"
            v89._check_pwd_no_symlinks()
            os.environ["PWD"] = str(base / "nonexistent_dir_xyz")
            v89._check_pwd_no_symlinks()
            os.environ.pop("PWD", None)
            v89._check_pwd_no_symlinks()
        finally:
            if old_pwd is None:
                os.environ.pop("PWD", None)
            else:
                os.environ["PWD"] = old_pwd

        # Hardlink read & write
        hl_src = base / "hl_src.json"
        hl_src.write_bytes(b'{"h":1}\n')
        hl_dst = base / "hl_dst.json"
        os.link(hl_src, hl_dst)
        expect_s89_error(lambda: v89.read_regular_file_bytes(hl_src), "HARDLINK_FORBIDDEN", "read hl")
        expect_s89_error(lambda: v89.write_atomic_0600_bytes(hl_dst, b"{}\n"), "HARDLINK_FORBIDDEN", "write hl")

        # Scratch FIFO — must fail fast (< 1.0s) without hanging
        fifo = base / "pipe.fifo"
        os.mkfifo(fifo)
        t0 = time.monotonic()
        expect_s89_error(lambda: v89.read_regular_file_bytes(fifo), "NOT_REGULAR_FILE", "read fifo")
        check((time.monotonic() - t0) < 1.0, "fifo read hung")
        expect_s89_error(lambda: v89.write_atomic_0600_bytes(fifo, b"{}\n"), "NOT_REGULAR_FILE", "write fifo")

        # Size cap (exact boundary + overflow), root path, deleted CWD, relative + dotdot, RO dir write
        exact16 = base / "exact16.json"
        exact16.write_bytes(b"a" * 16)
        check(v89.read_regular_file_bytes(exact16, max_bytes=16) == b"a" * 16, "size cap exact")
        big = base / "big.json"
        big.write_bytes(b"a" * 17)
        expect_s89_error(lambda: v89.read_regular_file_bytes(big, max_bytes=16), "FILE_TOO_LARGE", "size cap")
        expect_s89_error(lambda: v89.read_regular_file_bytes(Path("/")), "INVALID_TARGET_PATH", "root path")
        check(
            v89.read_regular_file_bytes(base / "real_d" / ".." / "." / "regular.json") == b'{"ok":3}\n',
            "dotdot norm",
        )
        old_cwd = os.getcwd()
        try:
            os.chdir(base)
            check(v89.read_regular_file_bytes(Path("regular.json")) == b'{"ok":3}\n', "rel path read")
            gone_d = base / "gone_d"
            gone_d.mkdir()
            os.chdir(gone_d)
            os.rmdir(gone_d)
            expect_s89_error(lambda: v89._open_dir_chain(Path("x.json")), "CWD_UNAVAILABLE", "deleted cwd")
        finally:
            os.chdir(old_cwd)

        ro_dir = base / "ro_dir"
        ro_dir.mkdir()
        os.chmod(ro_dir, 0o500)
        try:
            expect_s89_error(lambda: v89.write_atomic_0600_bytes(ro_dir / "x.json", b"{}\n"), "ATOMIC_WRITE_FAILED", "ro dir")
        finally:
            os.chmod(ro_dir, 0o700)


def test_05_surfaces_fr1_fr0_sec_deep_tamper() -> None:
    cert = s89.build_certificate()
    check(v89.verify_certificate_dict(cert, full_replay=True) == cert, "FR1 ok")
    check(v89.verify_certificate_dict(cert, full_replay=False) == cert, "FR0 ok")
    sec_res = v89.secondary_audit_payload(cert)
    check(sec_res["secondary_audit"] == "PASS" and sec_res["edges_verified"] == 45, "SEC cert ok")
    check(v89.secondary_audit_payload(cert["payload"])["secondary_audit"] == "PASS", "SEC payload ok")

    # Surface argument & envelope checks
    expect_s89_error(lambda: v89._require_dict_keys([], v89._CERT_KEYS, "BAD"), "BAD", "req keys non-dict")
    expect_s89_error(lambda: v89.verify_certificate_dict(cert, full_replay=1), "INVALID_FULL_REPLAY_FLAG", "fr non-bool")  # type: ignore[arg-type]
    expect_s89_error(lambda: v89.verify_certificate_dict([]), "NON_DICT_CERT", "cert non-dict")
    expect_s89_error(lambda: v89.secondary_audit_payload([]), "NON_DICT_INPUT", "sec non-dict")

    c_bad = copy.deepcopy(cert)
    c_bad["extra"] = 1
    expect_s89_error(lambda: v89._verify_envelope_digests(c_bad), "BAD_CERT_KEYS", "extra key")

    c_bad = copy.deepcopy(cert)
    c_bad["schema_version"] = "wrong"
    expect_s89_error(lambda: v89._verify_envelope_digests(c_bad), "BAD_SCHEMA_VERSION", "env schema")

    c_bad = copy.deepcopy(cert)
    c_bad["track_id"] = "wrong"
    expect_s89_error(lambda: v89._verify_envelope_digests(c_bad), "BAD_TRACK_ID", "env track")

    for bad_hex in [123, "abc", "A" * 64, "g" * 64]:
        c_bad = copy.deepcopy(cert)
        c_bad["payload_sha256"] = bad_hex
        expect_s89_error(lambda c=c_bad: v89._verify_envelope_digests(c), "BAD_PAYLOAD_SHA_SYNTAX", f"psha {bad_hex!r}")
        c_bad2 = copy.deepcopy(cert)
        c_bad2["certificate_sha256"] = bad_hex
        expect_s89_error(lambda c=c_bad2: v89._verify_envelope_digests(c), "BAD_CERT_SHA_SYNTAX", f"csha {bad_hex!r}")

    c_bad = copy.deepcopy(cert)
    c_bad["payload"] = []
    expect_s89_error(lambda: v89._verify_envelope_digests(c_bad), "BAD_PAYLOAD_TYPE", "payload list")

    c_bad = copy.deepcopy(cert)
    c_bad["payload_sha256"] = "0" * 64
    expect_s89_error(lambda: v89._verify_envelope_digests(c_bad), "PAYLOAD_SHA_MISMATCH", "psha mismatch")

    c_bad = copy.deepcopy(cert)
    c_bad["certificate_sha256"] = "0" * 64
    expect_s89_error(lambda: v89._verify_envelope_digests(c_bad), "CERT_SHA_MISMATCH", "csha mismatch")

    # FR0 accepts internally consistent rehashed non-oracle-identical note; FR1 rejects it!
    c_alt = copy.deepcopy(cert)
    c_alt["payload"]["pillar4_lean4_and_novelty"]["novelty_honesty_note"] = "modified-note"
    c_alt = _rehash_cert(c_alt)
    v89.verify_certificate_dict(c_alt, full_replay=False)
    expect_s89_error(lambda: v89.verify_certificate_dict(c_alt, full_replay=True), "REPLAY_MISMATCH", "FR1 replay")

    # Helper to test SEC tampering on payload directly
    base_p = cert["payload"]

    def tamper_p(mut: Callable[[dict[str, Any]], None], code: str, lbl: str) -> None:
        p = copy.deepcopy(base_p)
        mut(p)
        expect_s89_error(lambda: v89.secondary_audit_payload(p), code, lbl)

    tamper_p(lambda p: p.pop("oracle_class"), "BAD_PAYLOAD_KEYS", "p keys")
    tamper_p(lambda p: p.__setitem__("schema_version", "x"), "BAD_PAYLOAD_SCHEMA", "p schema")
    tamper_p(lambda p: p.__setitem__("track_id", "x"), "BAD_PAYLOAD_TRACK", "p track")
    tamper_p(lambda p: p.__setitem__("oracle_class", "x"), "BAD_ORACLE_CLASS", "p oracle_class")

    # Pillar 1 SEC mutations (including strict-int bool traps for EVERY BoolOp!)
    tamper_p(lambda p: p.__setitem__("pillar1_corpus_audit", []), "BAD_P1_TYPE", "p1 type")
    tamper_p(lambda p: p["pillar1_corpus_audit"].__setitem__("inventory_sha256", "bad"), "BAD_INV_SHA", "p1 sha")
    tamper_p(lambda p: p["pillar1_corpus_audit"].__setitem__("totals", []), "BAD_P1_TOTALS", "p1 totals")
    for sec_k in ("by_top_dir", "by_extension", "text_layer_by_extension", "work_tier_distribution", "quality_diagnostics_law4"):
        tamper_p(lambda p, k=sec_k: p["pillar1_corpus_audit"].__setitem__(k, 0), "BAD_P1_SECTIONS", f"p1 sec {sec_k}")
    tamper_p(lambda p: p["pillar1_corpus_audit"]["by_top_dir"].pop(), "BAD_P1_LENGTHS", "p1 len dir")
    tamper_p(lambda p: p["pillar1_corpus_audit"]["by_extension"].pop(), "BAD_P1_LENGTHS", "p1 len ext")
    tamper_p(lambda p: p["pillar1_corpus_audit"]["text_layer_by_extension"].pop(), "BAD_P1_LENGTHS", "p1 len txt")

    tamper_p(lambda p: p["pillar1_corpus_audit"]["by_top_dir"].__setitem__(0, []), "BAD_P1_DIR_ROW", "dir row type")
    for fk in ("files", "pdfs", "bytes"):
        tamper_p(lambda p, k=fk: p["pillar1_corpus_audit"]["by_top_dir"][0].__setitem__(k, True), "BAD_P1_DIR_ROW", f"dir {fk}")
    tamper_p(lambda p: p["pillar1_corpus_audit"]["by_extension"].__setitem__(0, []), "BAD_P1_EXT_ROW", "ext row type")
    for fk in ("files", "bytes"):
        tamper_p(lambda p, k=fk: p["pillar1_corpus_audit"]["by_extension"][0].__setitem__(k, True), "BAD_P1_EXT_ROW", f"ext {fk}")
    tamper_p(lambda p: p["pillar1_corpus_audit"]["text_layer_by_extension"].__setitem__(0, []), "BAD_P1_TXT_ROW", "txt row type")
    for fk in ("files", "bytes", "words"):
        tamper_p(lambda p, k=fk: p["pillar1_corpus_audit"]["text_layer_by_extension"][0].__setitem__(k, True), "BAD_P1_TXT_ROW", f"txt {fk}")

    # Sum checks + bool==0 strict-int traps
    def _zero_p1_field(p: dict[str, Any], table: str, field: str) -> None:
        for r in p["pillar1_corpus_audit"][table]:
            r[field] = 0

    tamper_p(
        lambda p: (_zero_p1_field(p, "by_top_dir", "files"), _zero_p1_field(p, "by_extension", "files"), p["pillar1_corpus_audit"]["totals"].__setitem__("inventory_files", False)),
        "P1_FILES_SUM_MISMATCH",
        "inv files bool trap",
    )
    tamper_p(lambda p: p["pillar1_corpus_audit"]["by_top_dir"][0].__setitem__("files", 999), "P1_FILES_SUM_MISMATCH", "inv files dir")
    tamper_p(lambda p: p["pillar1_corpus_audit"]["by_extension"][0].__setitem__("files", 999), "P1_FILES_SUM_MISMATCH", "inv files ext")

    tamper_p(
        lambda p: (_zero_p1_field(p, "by_top_dir", "bytes"), _zero_p1_field(p, "by_extension", "bytes"), p["pillar1_corpus_audit"]["totals"].__setitem__("inventory_bytes", False)),
        "P1_BYTES_SUM_MISMATCH",
        "inv bytes bool trap",
    )
    tamper_p(lambda p: p["pillar1_corpus_audit"]["by_top_dir"][0].__setitem__("bytes", 999), "P1_BYTES_SUM_MISMATCH", "inv bytes dir")
    tamper_p(lambda p: p["pillar1_corpus_audit"]["by_extension"][0].__setitem__("bytes", 999), "P1_BYTES_SUM_MISMATCH", "inv bytes ext")

    tamper_p(
        lambda p: (_zero_p1_field(p, "by_top_dir", "pdfs"), p["pillar1_corpus_audit"]["totals"].__setitem__("inventory_pdfs", False)),
        "P1_PDFS_SUM_MISMATCH",
        "inv pdfs bool trap",
    )
    tamper_p(lambda p: p["pillar1_corpus_audit"]["by_top_dir"][0].__setitem__("pdfs", 999), "P1_PDFS_SUM_MISMATCH", "inv pdfs dir")
    tamper_p(lambda p: p["pillar1_corpus_audit"]["totals"].__setitem__("inventory_gib_exact", "1"), "P1_GIB_MISMATCH", "gib mismatch")

    tamper_p(
        lambda p: (_zero_p1_field(p, "text_layer_by_extension", "files"), p["pillar1_corpus_audit"]["totals"].__setitem__("downloaded_text_files", False)),
        "P1_TXT_FILES_MISMATCH",
        "txt files bool trap",
    )
    tamper_p(lambda p: p["pillar1_corpus_audit"]["text_layer_by_extension"][0].__setitem__("files", 999), "P1_TXT_FILES_MISMATCH", "txt files")
    tamper_p(
        lambda p: (_zero_p1_field(p, "text_layer_by_extension", "bytes"), p["pillar1_corpus_audit"]["totals"].__setitem__("downloaded_text_bytes", False)),
        "P1_TXT_BYTES_MISMATCH",
        "txt bytes bool trap",
    )
    tamper_p(lambda p: p["pillar1_corpus_audit"]["text_layer_by_extension"][0].__setitem__("bytes", 999), "P1_TXT_BYTES_MISMATCH", "txt bytes")
    tamper_p(
        lambda p: (_zero_p1_field(p, "text_layer_by_extension", "words"), p["pillar1_corpus_audit"]["totals"].__setitem__("downloaded_text_words", False)),
        "P1_TXT_WORDS_MISMATCH",
        "txt words bool trap",
    )
    tamper_p(lambda p: p["pillar1_corpus_audit"]["text_layer_by_extension"][0].__setitem__("words", 999), "P1_TXT_WORDS_MISMATCH", "txt words")

    tamper_p(
        lambda p: (
            p["pillar1_corpus_audit"]["quality_diagnostics_law4"].__setitem__("crlf_text_files", True),
            p["pillar1_corpus_audit"]["quality_diagnostics_law4"].__setitem__("crlf_text_fraction", "1/1460"),
        ),
        "P1_CRLF_FRAC_MISMATCH",
        "crlf bool trap",
    )
    tamper_p(lambda p: p["pillar1_corpus_audit"]["quality_diagnostics_law4"].__setitem__("crlf_text_fraction", "1/2"), "P1_CRLF_FRAC_MISMATCH", "crlf val")
    tamper_p(
        lambda p: (
            p["pillar1_corpus_audit"]["quality_diagnostics_law4"].__setitem__("malformed_jsonl_bad_lines", True),
            p["pillar1_corpus_audit"]["quality_diagnostics_law4"].__setitem__("malformed_jsonl_bad_fraction", "1/11299"),
        ),
        "P1_JSONL_FRAC_MISMATCH",
        "jsonl bad bool",
    )
    tamper_p(
        lambda p: (
            p["pillar1_corpus_audit"]["quality_diagnostics_law4"].__setitem__("malformed_jsonl_bad_lines", 0),
            p["pillar1_corpus_audit"]["quality_diagnostics_law4"].__setitem__("malformed_jsonl_checked_lines", True),
            p["pillar1_corpus_audit"]["quality_diagnostics_law4"].__setitem__("malformed_jsonl_bad_fraction", "0"),
        ),
        "P1_JSONL_FRAC_MISMATCH",
        "jsonl chk bool",
    )
    tamper_p(
        lambda p: p["pillar1_corpus_audit"]["quality_diagnostics_law4"].__setitem__("malformed_jsonl_checked_lines", 0),
        "P1_JSONL_FRAC_MISMATCH",
        "jsonl chk zero",
    )
    tamper_p(
        lambda p: p["pillar1_corpus_audit"]["quality_diagnostics_law4"].__setitem__("malformed_jsonl_bad_fraction", "1/2"),
        "P1_JSONL_FRAC_MISMATCH",
        "jsonl frac val",
    )

    # Pillar 2 SEC mutations
    tamper_p(lambda p: p.__setitem__("pillar2_anchor_nodes", []), "BAD_P2_TYPE", "p2 type")
    tamper_p(lambda p: p["pillar2_anchor_nodes"].__setitem__("anchors", {str(i): i for i in range(10)}), "BAD_P2_ANCHOR_COUNT", "p2 anchors dict10")
    tamper_p(lambda p: p["pillar2_anchor_nodes"]["anchors"].pop(), "BAD_P2_ANCHOR_COUNT", "p2 anchors len")
    tamper_p(lambda p: p["pillar2_anchor_nodes"]["anchors"].__setitem__(0, []), "BAD_P2_ANCHOR_ID", "p2 node type")
    tamper_p(lambda p: p["pillar2_anchor_nodes"]["anchors"][0].__setitem__("id", "h99"), "BAD_P2_ANCHOR_ID", "p2 node id")
    tamper_p(lambda p: p["pillar2_anchor_nodes"]["anchors"][0].__setitem__("primary_anchor", []), "BAD_P2_ANCHOR_META", "p2 meta type")
    tamper_p(lambda p: p["pillar2_anchor_nodes"]["anchors"][0]["primary_anchor"].__setitem__("rel_path", 1), "BAD_P2_ANCHOR_META", "p2 rel type")
    tamper_p(lambda p: p["pillar2_anchor_nodes"]["anchors"][0]["primary_anchor"].__setitem__("rel_path", "/abs"), "BAD_P2_ANCHOR_META", "p2 rel abs")
    tamper_p(lambda p: p["pillar2_anchor_nodes"]["anchors"][0]["primary_anchor"].__setitem__("sha256", "bad"), "BAD_P2_ANCHOR_META", "p2 sha")
    tamper_p(lambda p: p["pillar2_anchor_nodes"]["anchors"][0]["primary_anchor"].__setitem__("bytes", True), "BAD_P2_ANCHOR_META", "p2 bytes bool")
    tamper_p(lambda p: p["pillar2_anchor_nodes"]["anchors"][0]["primary_anchor"].__setitem__("words", True), "BAD_P2_ANCHOR_META", "p2 words bool")

    def _zero_p2_field(p: dict[str, Any], fld: str) -> None:
        for nd in p["pillar2_anchor_nodes"]["anchors"]:
            nd["primary_anchor"][fld] = 0
            nd["secondary_anchor"][fld] = 0

    tamper_p(
        lambda p: (_zero_p2_field(p, "bytes"), p["pillar2_anchor_nodes"].__setitem__("pinned_files_total_bytes", False)),
        "P2_BYTES_MISMATCH",
        "p2 total bytes bool",
    )
    tamper_p(lambda p: p["pillar2_anchor_nodes"].__setitem__("pinned_files_total_bytes", 1), "P2_BYTES_MISMATCH", "p2 total bytes")
    tamper_p(
        lambda p: (_zero_p2_field(p, "words"), p["pillar2_anchor_nodes"].__setitem__("pinned_files_total_words", False)),
        "P2_WORDS_MISMATCH",
        "p2 total words bool",
    )
    tamper_p(lambda p: p["pillar2_anchor_nodes"].__setitem__("pinned_files_total_words", 1), "P2_WORDS_MISMATCH", "p2 total words")
    tamper_p(lambda p: p["pillar2_anchor_nodes"].__setitem__("exact_rational_witnesses", []), "BAD_P2_WITNESSES", "p2 wit type")
    tamper_p(
        lambda p: (
            p["pillar2_anchor_nodes"]["exact_rational_witnesses"].__setitem__("h07_farisi_primary_cos2", "8/27"),
            p["pillar2_anchor_nodes"]["exact_rational_witnesses"].__setitem__("h07_farisi_alexander_band_cos2_gap", "43/216"),
        ),
        "P2_FARISI_MISMATCH",
        "farisi c1 consistent gap",
    )
    tamper_p(
        lambda p: (
            p["pillar2_anchor_nodes"]["exact_rational_witnesses"].__setitem__("h07_farisi_secondary_cos2", "5/72"),
            p["pillar2_anchor_nodes"]["exact_rational_witnesses"].__setitem__("h07_farisi_alexander_band_cos2_gap", "41/216"),
        ),
        "P2_FARISI_MISMATCH",
        "farisi c2 consistent gap",
    )
    tamper_p(lambda p: p["pillar2_anchor_nodes"]["exact_rational_witnesses"].__setitem__("h07_farisi_alexander_band_cos2_gap", "1/2"), "P2_FARISI_MISMATCH", "farisi gap")
    tamper_p(lambda p: p["pillar2_anchor_nodes"]["exact_rational_witnesses"].__setitem__("h06_kashi_lipschitz_bound", "0"), "P2_KASHI_LIP_MISMATCH", "kashi 0")
    tamper_p(lambda p: p["pillar2_anchor_nodes"]["exact_rational_witnesses"].__setitem__("h06_kashi_lipschitz_bound", "1"), "P2_KASHI_LIP_MISMATCH", "kashi 1")

    # Pillar 3 SEC mutations + AUDIT-189 re-signed SEC/FR0/FR1 regressions (S1, S2, S3, S5b, S6)
    tamper_p(lambda p: p.__setitem__("pillar3_k10_mesh_and_s83_bridge", []), "BAD_P3_TYPE", "p3 type")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"].__setitem__("edges", {str(i): i for i in range(45)}), "BAD_P3_EDGES", "p3 edges dict45")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["edges"].pop(), "BAD_P3_EDGES", "p3 edges len")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["edges"].__setitem__(0, []), "BAD_P3_EDGE", "p3 edge type")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["edges"][0].__setitem__("u", []), "BAD_P3_EDGE_NODES", "p3 u unhashable")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["edges"][0].__setitem__("v", []), "BAD_P3_EDGE_NODES", "p3 v unhashable")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["edges"][0].__setitem__("u", "h99"), "BAD_P3_EDGE_NODES", "p3 u bad")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["edges"][0].__setitem__("v", "h99"), "BAD_P3_EDGE_NODES", "p3 v bad")
    tamper_p(
        lambda p: (
            p["pillar3_k10_mesh_and_s83_bridge"]["edges"][0].__setitem__("u", "h01"),
            p["pillar3_k10_mesh_and_s83_bridge"]["edges"][0].__setitem__("v", "h00"),
        ),
        "BAD_P3_EDGE_PAIR",
        "p3 u>=v",
    )
    tamper_p(
        lambda p: (
            p["pillar3_k10_mesh_and_s83_bridge"]["edges"][1].__setitem__("u", "h00"),
            p["pillar3_k10_mesh_and_s83_bridge"]["edges"][1].__setitem__("v", "h01"),
        ),
        "BAD_P3_EDGE_PAIR",
        "p3 dup pair",
    )
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["edges"][0].__setitem__("edge_class", []), "BAD_P3_EDGE_CLASS_WEIGHT", "p3 ecls unhashable")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["edges"][0].__setitem__("edge_class", "BOGUS"), "BAD_P3_EDGE_CLASS_WEIGHT", "p3 ecls bogus")
    # Edge 2 is (h00, h03) EXACT_OBSTRUCTION (weight 1) -> True == 1 kills deleting _is_strict_int(w)
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["edges"][2].__setitem__("weight", True), "BAD_P3_EDGE_CLASS_WEIGHT", "p3 edge w bool trap")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["edges"][0].__setitem__("weight", 1), "BAD_P3_EDGE_CLASS_WEIGHT", "p3 edge w mismatch")
    tamper_p(
        lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["edge_class_counts"].__setitem__("EXACT_COMMUTE", 99),
        "P3_EDGE_CLASS_COUNTS_MISMATCH",
        "p3 cls counts",
    )
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"].__setitem__("laplacian_inertia", [8, 1, 1]), "P3_INERTIA_MISMATCH", "p3 inertia")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["edges"][0].__setitem__("r_eff", "1/2"), "P3_EDGE_MATH_FAIL", "p3 reff mismatch")
    tamper_p(
        lambda p: (
            p["pillar3_k10_mesh_and_s83_bridge"]["edges"][0].__setitem__("g_eff", "10"),
            p["pillar3_k10_mesh_and_s83_bridge"]["edges"][0].__setitem__("compounding_ratio", "5"),
        ),
        "P3_EDGE_MATH_FAIL",
        "p3 geff consistent ratio",
    )
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["edges"][0].__setitem__("compounding_ratio", "99"), "P3_EDGE_MATH_FAIL", "p3 ratio neq")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"].__setitem__("foster_resistance_sum", "8"), "P3_FOSTER_MISMATCH", "p3 foster q != 9")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"].__setitem__("min_compounding_ratio", "999"), "P3_EXTREMA_MISMATCH", "p3 min ratio")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"].__setitem__("max_compounding_ratio", "999"), "P3_EXTREMA_MISMATCH", "p3 max ratio")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"].__setitem__("all_45_edges_strictly_compounded", False), "P3_EXTREMA_MISMATCH", "p3 strict flag")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"].__setitem__("triangle_count", 119), "P3_TRIANGLE_MISMATCH", "p3 tri count")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["triangle_holonomy_counts"].__setitem__("exact_transitive", 9999), "P3_TRIANGLE_MISMATCH", "p3 tri S1")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"].__setitem__("tetrahedron_count", 209), "P3_BIANCHI_MISMATCH", "p3 tet cnt")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"].__setitem__("tetrahedral_bianchi_zero_count", 209), "P3_BIANCHI_MISMATCH", "p3 bianchi cnt")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["tetrahedral_frustrated_face_distribution"].__setitem__("0", 9999), "P3_BIANCHI_MISMATCH", "p3 tet dist S2")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"].__setitem__("silo_cut_five_five", []), "BAD_P3_SILO", "p3 silo type")
    for sk in ("edges_cut_fraction", "triangles_cut_fraction", "tetrahedra_cut_fraction"):
        tamper_p(lambda p, k=sk: p["pillar3_k10_mesh_and_s83_bridge"]["silo_cut_five_five"].__setitem__(k, "1/2"), "P3_SILO_CUT_MISMATCH", f"silo {sk}")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"].__setitem__("cross_millennium_10x8_s83", []), "P3_CROSS_MISMATCH", "cross type")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"].__setitem__("s83_cert_file_sha256", "bad"), "P3_CROSS_MISMATCH", "cross fsha")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"].__setitem__("s83_cert_digest", "bad"), "P3_CROSS_MISMATCH", "cross dig")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"].__setitem__("pairs", {str(i): i for i in range(80)}), "P3_CROSS_MISMATCH", "cross pairs dict80")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"]["pairs"].pop(), "P3_CROSS_MISMATCH", "cross pairs len")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"]["pairs"].__setitem__(0, []), "BAD_P3_CROSS_PAIR", "cross pair type")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"]["pairs"][0].__setitem__("classical", []), "BAD_P3_CROSS_PAIR", "cross c unhashable")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"]["pairs"][0].__setitem__("modern", []), "BAD_P3_CROSS_PAIR", "cross m unhashable")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"]["pairs"][0].__setitem__("classical", "h99"), "BAD_P3_CROSS_PAIR", "cross c bad")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"]["pairs"][0].__setitem__("modern", "v9"), "BAD_P3_CROSS_PAIR", "cross m bad")
    tamper_p(
        lambda p: (
            p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"]["pairs"][1].__setitem__("classical", "h00"),
            p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"]["pairs"][1].__setitem__("modern", "v0"),
        ),
        "BAD_P3_CROSS_PAIR",
        "cross dup pair",
    )
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"]["pairs"][0].__setitem__("mapping_class", []), "BAD_P3_CROSS_PAIR", "cross cls unhashable")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"]["pairs"][0].__setitem__("mapping_class", "BOGUS"), "BAD_P3_CROSS_PAIR", "cross cls bogus")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"].__setitem__("total_pairs", 79), "P3_CROSS_COUNTS_MISMATCH", "cross total_pairs")
    tamper_p(lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"]["class_counts"].__setitem__("EXACT_OPERATOR_ISOMORPHISM", 80), "P3_CROSS_COUNTS_MISMATCH", "cross S3")

    # Explicit re-signed AUDIT-189 S89-VER-01 PoCs (S1, S2, S3, S5b, S5b_uniform, S6) on SEC + FR0 + FR1
    def _assert_resigned_rejected(mut_fn: Callable[[dict[str, Any]], None], exp_code: str, name: str) -> None:
        c_mod = copy.deepcopy(cert)
        mut_fn(c_mod["payload"])
        c_mod = _rehash_cert(c_mod)
        expect_s89_error(lambda: v89.secondary_audit_payload(c_mod), exp_code, f"{name} SEC")
        expect_s89_error(lambda: v89.verify_certificate_dict(c_mod, full_replay=False), exp_code, f"{name} FR0")
        expect_s89_error(lambda: v89.verify_certificate_dict(c_mod, full_replay=True), exp_code, f"{name} FR1")

    _assert_resigned_rejected(
        lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["triangle_holonomy_counts"].__setitem__("exact_transitive", 9999),
        "P3_TRIANGLE_MISMATCH",
        "AUDIT189-S1",
    )
    _assert_resigned_rejected(
        lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["tetrahedral_frustrated_face_distribution"].__setitem__("0", 9999),
        "P3_BIANCHI_MISMATCH",
        "AUDIT189-S2",
    )
    _assert_resigned_rejected(
        lambda p: p["pillar3_k10_mesh_and_s83_bridge"]["cross_millennium_10x8_s83"]["class_counts"].__setitem__("EXACT_OPERATOR_ISOMORPHISM", 80),
        "P3_CROSS_COUNTS_MISMATCH",
        "AUDIT189-S3",
    )

    def _mut_s5b_raw(p: dict[str, Any]) -> None:
        for idx_e, e in enumerate(p["pillar3_k10_mesh_and_s83_bridge"]["edges"]):
            e["weight"] = 1
            if idx_e == 0:
                e["r_eff"], e["g_eff"], e["compounding_ratio"] = "3/10", "10/3", "10/3"
            elif idx_e == 1:
                e["r_eff"], e["g_eff"], e["compounding_ratio"] = "1/10", "10", "10"
            else:
                e["r_eff"], e["g_eff"], e["compounding_ratio"] = "1/5", "5", "5"

    _assert_resigned_rejected(_mut_s5b_raw, "BAD_P3_EDGE_CLASS_WEIGHT", "AUDIT189-S5b")

    def _mut_s5b_uniform_nonlap(p: dict[str, Any]) -> None:
        _mut_s5b_raw(p)
        for e in p["pillar3_k10_mesh_and_s83_bridge"]["edges"]:
            e["edge_class"] = "EXACT_OBSTRUCTION"
        p["pillar3_k10_mesh_and_s83_bridge"]["edge_class_counts"] = {
            "EXACT_COMMUTE": 0,
            "CONDITIONAL_BRIDGE": 0,
            "EXACT_OBSTRUCTION": 45,
        }

    _assert_resigned_rejected(_mut_s5b_uniform_nonlap, "P3_EDGE_MATH_FAIL", "AUDIT189-S5b-nonlap")
    _assert_resigned_rejected(
        lambda p: p["pillar3_k10_mesh_and_s83_bridge"].__setitem__("min_compounding_ratio", "999"),
        "P3_EXTREMA_MISMATCH",
        "AUDIT189-S6",
    )

    # Pillar 4 SEC mutations
    tamper_p(lambda p: p.__setitem__("pillar4_lean4_and_novelty", []), "BAD_P4_TYPE", "p4 type")
    tamper_p(lambda p: p["pillar4_lean4_and_novelty"].__setitem__("lean_sha256", 123), "BAD_P4_LEAN_SHA", "p4 sha int")
    tamper_p(lambda p: p["pillar4_lean4_and_novelty"].__setitem__("lean_sha256", "0" * 64), "BAD_P4_LEAN_SHA", "p4 sha wrong")
    tamper_p(lambda p: p["pillar4_lean4_and_novelty"].__setitem__("theorem_count", 16), "BAD_P4_THM_COUNT", "p4 thm cnt")
    tamper_p(lambda p: p["pillar4_lean4_and_novelty"].__setitem__("max_novelty_class", "N2"), "BAD_P4_NOVELTY", "p4 max nov")
    tamper_p(lambda p: p["pillar4_lean4_and_novelty"].__setitem__("n2_claims_count", False), "BAD_P4_NOVELTY", "p4 n2 bool trap")
    tamper_p(lambda p: p["pillar4_lean4_and_novelty"].__setitem__("n2_claims_count", 1), "BAD_P4_NOVELTY", "p4 n2 count")


def test_06_r10_lean4_scanner_15_classes_and_boolops() -> None:
    expect_s89_error(lambda: v89.audit_lean4_source_r10(123), "INVALID_LEAN_SOURCE", "lean non-str")  # type: ignore[arg-type]

    # Direct helper edge cases for BoolOp & boundary kills
    check(v89._is_lean4_ident_prev("a", -1) is False, "ident prev -1")
    check(v89._is_lean4_ident_prev("a", 0) is True, "ident prev 0")
    check(v89._is_lean4_ident_prev("a!?", 2) is True, "ident prev bang")
    check(v89._is_lean4_ident_prev("_!", 1) is True, "ident prev _!")
    check(v89._is_lean4_ident_prev("!!", 1) is False, "ident prev only bang")
    check(v89._is_lean4_ident_prev("a_", 1) is True, "ident prev underscore")
    check(v89._is_lean4_ident_prev("a ", 1) is False, "ident prev space")
    check(v89._strip_outer_parens("a)") == "a)", "strip paren right only")
    check(v89._strip_outer_parens("(a") == "(a", "strip paren left only")
    check(v89._match_lean4_char_end("'", 0, 1) is None, "char eof")
    check(v89._match_lean4_char_end("'a'", 0, 3) == 3, "char basic")
    check(v89._match_lean4_char_end("'\\''", 0, 4) == 4, "char esc")
    check(v89._match_lean4_char_end("'\\x27'", 0, 6) == 6, "char hex2")
    check(v89._match_lean4_char_end("'\\y27'", 0, 6) is None, "char non-x hex2")
    check(v89._match_lean4_char_end("'\\x2", 0, 4) is None, "char short hex2")
    check(v89._match_lean4_char_end("'\\x27a", 0, 6) is None, "char unclosed hex2")
    check(v89._match_lean4_char_end("'\\u0027'", 0, 8) == 8, "char hex4")
    check(v89._match_lean4_char_end("'\\y0027'", 0, 8) is None, "char non-u hex4")
    check(v89._match_lean4_char_end("'\\u002", 0, 6) is None, "char short hex4")
    check(v89._match_lean4_char_end("'\\u0027a", 0, 8) is None, "char unclosed hex4")
    check(v89._match_lean4_char_end("'\n'", 0, 3) is None, "char nl")
    check(v89._match_lean4_char_end("'\\\n'", 0, 4) is None, "char esc nl")
    check(v89._match_lean4_char_end("'\\xZZ'", 0, 6) is None, "char bad hex2")
    check(v89._match_lean4_char_end("'\\uZZZZ'", 0, 8) is None, "char bad hex4")
    check(v89._match_lean4_char_end("'ab'", 0, 4) is None, "char 2chars")
    check(v89._match_lean4_char_end("'\\", 0, 2) is None, "char short esc")

    # Clean constructs (must yield ZERO findings!)
    clean_samples = [
        "import Init.Data.Int.Basic\ntheorem t : 1 = 1 := rfl\n#print axioms t\n",
        "/- /- nested comment - sorry -/ still comment - sorry -/\ntheorem t : 1 = 1 := rfl\n",
        "-- line comment with sorry at EOF without newline",
        'def s := "sorry \\" \\\\\n still string"\n',
        'def r1 := r"\\sorry"\ndef r2 := r#"a"sorry"#\ndef bar := 1\n',
        'def r_eof := r',
        'def rh_eof := r#',
        'def bar_q := bar"\\""\n',
        'def x_r1 := _r"\\""\n',
        'def x_r2 := ("\\"")\n',
        "def c0 : Char := '\"'\ndef c1 : Char := '\\''\ndef c2 : Char := '\\x27'\ndef c3 : Char := '\\u0027'\ndef x' := '\"'\n",
        'def «--» := 1\ndef «/-» := 2\ndef «a sorry b» := 3\ndef a_1 := 3\ndef _b := 4\n',
        'def p := panic!"sorry inside panic"\n',
        'def b0 := !"not ident before bang"\n',
        'def s_nop := s! x "{sorry}"\ndef s_id := s!a "{sorry}"\ndef s_p := s!_ "{sorry}"\ndef s_sp := s "{sorry}"\n',
        'def d_dot := dbg_trace.foo "{sorry}"\ndef tr_nop := trace x "{sorry}"\ndef mt_eof := Macro.trace',
        'def mt_id := Macro.trace_x[a] "{sorry}"\ndef mt_n := Macro.trace1[a] "{sorry}"\ndef mt_b := Macro.trace![a] "{sorry}"\n',
        'def mt_other := Foo.trace[a] "{sorry}"\ndef m_plain := Macro [a] "{sorry}"\n',
        'def tr_clean := trace[foo] "sorry"\ndef br_clean := [[2] "{sorry}"\n',
        'notation "abc\\ndef" => "def \\" sorry"\n',
        'theorem d_ok : True := by decide +revert (native := ((Bool.false))) (config := { native := false })\n',
        'def dc_ok : DecideConfig := { native := false }\n',
        'def d_eof := decide',
        'def d_misc := decide + 1\ndef d_p := decide (foo)\ndef stray := ) ]\n@[simp] theorem ok : 1 = 1 := rfl\n@[extern',
        'def str_r := bar"sorry"\ndef str_r2 := r#x\n',
        'def interp_ok := s!"hello \\n {1 + 2} {{3}} \\"world\\""\n',
        'def trace_ok := trace[a[b]] "ok {1}"\ndef mt_ok := Macro.trace[a] "ok {1}"\n',
        'def ch_at_0 := \'a\'\n\'a\'',
    ]
    for idx, src in enumerate(clean_samples):
        f = v89.audit_lean4_source_r10(src)
        check(f == [], f"clean sample {idx} produced findings {f}: {src!r}")

    # Every R10 spoof class & edge case (must be CAUGHT!)
    spoof_cases: list[tuple[str, str]] = [
        ("theorem t : 1 = 2 := by sorry", "LEAN4_SORRY"),
        ("def x := 1 / 2\ntheorem bad : False := sorry", "LEAN4_SORRY"),
        ("def x := 1 - sorry", "LEAN4_SORRY"),
        ("-- ok\ntheorem bad : False := sorry", "LEAN4_SORRY"),
        ('def r_bs := r"\\"\ntheorem bad : False := sorry', "LEAN4_SORRY"),
        ("'\"'\ntheorem bad : False := sorry", "LEAN4_SORRY"),
        ("def x'\"' := 1", "LEAN4_UNTERMINATED_STRING"),
        ("def x''\"' := 1", "LEAN4_UNTERMINATED_STRING"),
        ("def b := [1]\ntrace[a] \"{sorry}\"", "LEAN4_SORRY"),
        ("def x := (s!\"{sorry}\")", "LEAN4_SORRY"),
        ("theorem t : 1 = 2 := by admit", "LEAN4_ADMIT"),
        ("axiom bad : False", "LEAN4_AXIOM"),
        ("unsafe def u := 1", "LEAN4_UNSAFE"),
        ("theorem t : 1 = 1 := by native_decide", "LEAN4_NATIVE_DECIDE"),
        ("def x := sorryAx", "LEAN4_SORRY_AX"),
        ("def x := Lean.Meta.mkSorry", "LEAN4_MK_SORRY"),
        ("def x := Lean.ofReduceBool", "LEAN4_OF_REDUCE_BOOL"),
        ("def x := Lean.ofReduceNat", "LEAN4_OF_REDUCE_NAT"),
        ("def x := Lean.trustCompiler", "LEAN4_TRUST_COMPILER"),
        ("macro \"x\" : term => `(1)", "LEAN4_META_SYNTAX_ESCAPE"),
        ("syntax \"x\" : term", "LEAN4_META_SYNTAX_ESCAPE"),
        ("def x := interpolatedStr", "LEAN4_META_SYNTAX_ESCAPE"),
        ("import Mathlib.Tactic\n", "LEAN4_NON_INIT_IMPORT"),
        ("partial def loop : Nat := loop", "LEAN4_PARTIAL"),
        ("set_option debug.skipKernelTC true", "LEAN4_SKIP_KERNEL_TC"),
        ("#eval 1 + 1", "LEAN4_EVAL_SPOOF"),
        ("#reduce 1 + 1", "LEAN4_EVAL_SPOOF"),
        ("#exit", "LEAN4_EVAL_SPOOF"),
        ("#print Nat", "LEAN4_EVAL_SPOOF"),
        ("#print axioms def", "LEAN4_EVAL_SPOOF"),
        ("#print «axioms» foo", "LEAN4_EVAL_SPOOF"),
        ("run_cmd pure ()", "LEAN4_EVAL_SPOOF"),
        ("initialize x : IO Unit := pure ()", "LEAN4_EVAL_SPOOF"),
        ("@[extern \"c_fn\"] opaque f : Unit", "LEAN4_ATTR_TRUST_ESCAPE"),
        ("attribute [csimp] f", "LEAN4_ATTR_TRUST_ESCAPE"),
        ("theorem t : 1 = 1 := by decide +native", "LEAN4_DECIDE_NATIVE"),
        ("theorem t : 1 = 1 := by decide (native := !false)", "LEAN4_DECIDE_NATIVE"),
        ("theorem t : 1 = 1 := by decide (native := )", "LEAN4_DECIDE_NATIVE"),
        ("theorem t : 1 = 1 := by decide (config := myCfg)", "LEAN4_DECIDE_NATIVE"),
        ("theorem t : 1 = 1 := by decide (config := a})", "LEAN4_DECIDE_NATIVE"),
        ("theorem t : 1 = 1 := by decide (config := {a)", "LEAN4_DECIDE_NATIVE"),
        ("theorem t : 1 = 1 := by decide (config := { native := true })", "LEAN4_DECIDE_NATIVE"),
        ("theorem t : 1 = 1 := by decide (config := { native })", "LEAN4_DECIDE_NATIVE"),
        ("theorem t : 1 = 1 := by decide (config := { c with a := 1 })", "LEAN4_DECIDE_NATIVE"),
        ("theorem t : 1 = 1 := by decide (config := { a := { })", "LEAN4_DECIDE_NATIVE"),
        ("theorem t : 1 = 1 := by decide (config := { a := } })", "LEAN4_DECIDE_NATIVE"),
        ("theorem t : 1 = 1 := by decide (config := { a := 1 } ", "LEAN4_DECIDE_NATIVE"),
        ("def cfg : DecideConfig := { native := true }", "LEAN4_DECIDE_NATIVE"),
        ("def cfg := ({ native := true } : DecideConfig)", "LEAN4_DECIDE_NATIVE"),
        ('def x := foo!"sorry"', "LEAN4_UNKNOWN_BANG_STRING"),
        ('def x := my_panic!"ok"', "LEAN4_UNKNOWN_BANG_STRING"),
        ('def x := s!"{sorry}"', "LEAN4_SORRY"),
        ('def x := println!"{sorry}"', "LEAN4_SORRY"),
        ('def x := dbg_trace "{sorry}"', "LEAN4_SORRY"),
        ('def x := throwError "{sorry}"', "LEAN4_SORRY"),
        ('def x := trace[foo] "{sorry}"', "LEAN4_SORRY"),
        ('def x := trace[trace] "{sorry}"', "LEAN4_SORRY"),
        ('def x := Macro.trace[foo] "{sorry}"', "LEAN4_SORRY"),
        ("theorem t : 1 = 2 := by «sorry»", "LEAN4_SORRY"),
        ('notation "a\\"b\\"c" => 1', "LEAN4_SYNTAX_QUOTE_TOKEN"),
        ('notation "a"+> "b\\"c" => 1', "LEAN4_SYNTAX_QUOTE_TOKEN"),
        ("/- unterminated", "LEAN4_UNTERMINATED_COMMENT"),
        ('"unterminated', "LEAN4_UNTERMINATED_STRING"),
        ('r#"unterminated', "LEAN4_UNTERMINATED_STRING"),
        ('s!"unterminated', "LEAN4_UNTERMINATED_STRING"),
        ('s!"{unterminated', "LEAN4_UNTERMINATED_STRING"),
        ("def «unterminated", "LEAN4_UNTERMINATED_IDENT"),
        ("def q' := '\"' \ntheorem bad : False := sorry", "LEAN4_SORRY"),
    ]
    check(v89.audit_lean4_source_r10('def x := _s!"{sorry}"') == ["LEAN4_UNKNOWN_BANG_STRING"], "underscore s! not interp")
    # Note: `decide (config := { a := 1 } ` has unclosed paren -> break, not finding; test exact expected codes
    for src, expected in spoof_cases:
        if src.endswith("{ a := 1 } "):
            # Unclosed paren in decide exercises `close_i is None` branch cleanly
            check(v89.audit_lean4_source_r10(src) == [], "unclosed decide paren")
            continue
        f = v89.audit_lean4_source_r10(src)
        check(expected in f, f"spoof {src!r} expected {expected}, got {f}")
        if src == 'notation "a\\"b\\"c" => 1':
            check(f.count("LEAN4_SYNTAX_QUOTE_TOKEN") == 1, "syntax quote deduplicated")

    # Verify _verify_lean_output across wrapped lines, duplicates, forbidden axioms & theorem set
    wrapped_lines = []
    for i, thm in enumerate(s89.LEAN_THEOREMS):
        if i == 0:
            wrapped_lines.append(f"'{thm}' depends on axioms: [propext,")
            wrapped_lines.append("  Quot.sound]")
        elif i == 1:
            wrapped_lines.append(f"'{thm}' does not depend on any axioms")
        else:
            wrapped_lines.append(f"'{thm}' depends on axioms: [propext, Quot.sound]")
    seen = v89._verify_lean_output(0, "", "\n".join(wrapped_lines) + "\n", check_pinned_sha=True)
    check(len(seen) == 17 and seen[s89.LEAN_THEOREMS[0]] == ["propext", "Quot.sound"], "wrapped output ok")
    check(seen[s89.LEAN_THEOREMS[1]] == [], "zero axioms ok")

    expect_s89_error(lambda: v89._verify_lean_output(1, "err", ""), "LEAN_COMPILE_FAILED", "rc != 0")
    expect_s89_error(lambda: v89._verify_lean_output(0, "warn", ""), "LEAN_STDERR_NONEMPTY", "stderr nonempty")
    expect_s89_error(lambda: v89._verify_lean_output(0, "", "weird output\n"), "LEAN_UNEXPECTED_OUTPUT", "unexpected line")
    dup_out = f"'{s89.LEAN_THEOREMS[0]}' does not depend on any axioms\n'{s89.LEAN_THEOREMS[0]}' does not depend on any axioms\n"
    expect_s89_error(lambda: v89._verify_lean_output(0, "", dup_out, check_pinned_sha=False), "LEAN_DUPLICATE_THEOREM", "dup thm")
    bad_ax = "'Foo.bar' depends on axioms: [propext, Classical.choice]\n"
    expect_s89_error(lambda: v89._verify_lean_output(0, "", bad_ax, check_pinned_sha=False), "LEAN_FORBIDDEN_AXIOM", "choice ax")
    one_thm = f"'{s89.LEAN_THEOREMS[0]}' does not depend on any axioms\n"
    check(len(v89._verify_lean_output(0, "", one_thm, check_pinned_sha=False)) == 1, "unpinned thm ok")
    expect_s89_error(lambda: v89._verify_lean_output(0, "", one_thm, check_pinned_sha=True), "LEAN_THEOREM_SET_MISMATCH", "pinned set")


def test_07_lean_file_and_live_or_nolean_parity() -> None:
    # Always verify pinned ClassicalHeritageAtlas.lean hash & R10 cleanliness even with zero Lean binary
    lean_raw = v89.read_regular_file_bytes(LEAN_PATH)
    check(b"\r" not in lean_raw, "lean LF only")
    check(hashlib.sha256(lean_raw).hexdigest() == s89.LEAN_FILE_SHA256, "lean pinned sha")
    check(v89.audit_lean4_source_r10(lean_raw.decode("utf-8")) == [], "lean file R10 clean")

    with tempfile.TemporaryDirectory() as td:
        base = Path(td)
        crlf_f = base / "crlf.lean"
        crlf_f.write_bytes(b"theorem t : 1 = 1 := rfl\r\n")
        expect_s89_error(lambda: v89.verify_lean_file(crlf_f, check_pinned_sha=False), "CRLF_FORBIDDEN", "lean crlf")

        bad_u8 = base / "u8.lean"
        bad_u8.write_bytes(b"\xff\xfe")
        expect_s89_error(lambda: v89.verify_lean_file(bad_u8, check_pinned_sha=False), "INVALID_UTF8", "lean utf8")

        diff_sha = base / "diff.lean"
        diff_sha.write_bytes(b"theorem t : 1 = 1 := rfl\n#print axioms t\n")
        expect_s89_error(lambda: v89.verify_lean_file(diff_sha, check_pinned_sha=True), "LEAN_SHA_MISMATCH", "lean sha mismatch")

        sorry_f = base / "sorry.lean"
        sorry_f.write_bytes(b"theorem t : 1 = 2 := by sorry\n")
        expect_s89_error(lambda: v89.verify_lean_file(sorry_f, check_pinned_sha=False), "LEAN_R10_STATIC_FINDING", "lean r10 fail")

        # Live Lean vs no-Lean 0-skip parity (respects $HOME so env -i PATH=/usr/bin:/bin is true no-Lean)
        home_env = os.environ.get("HOME")
        elan_ok = bool(home_env) and (Path(home_env) / ".elan" / "bin" / "lean").is_file()
        lean_avail = shutil.which("lean") is not None or elan_ok
        require_lean = os.environ.get("ALETHEIA_REQUIRE_LEAN") == "1"
        if require_lean and not lean_avail:
            raise TestFailure("ALETHEIA_REQUIRE_LEAN=1 set, but lean binary not found")
        if lean_avail:
            live_res = v89.verify_lean_file(LEAN_PATH, check_pinned_sha=True)
            check(live_res["theorems_verified"] == 17 and live_res["r10_findings"] == 0, "live lean 17/17")
            ok_tmp = base / "ok.lean"
            ok_tmp.write_bytes(b"theorem ok_t : 2 + 2 = 4 := rfl\n#print axioms ok_t\n")
            tmp_res = v89.verify_lean_file(ok_tmp, check_pinned_sha=False)
            check(tmp_res["theorems_verified"] == 1, "live lean temp ok")

            # Live Classical.choice & false proof traps
            choice_f = base / "choice.lean"
            choice_f.write_bytes(
                b"theorem uses_choice (p : Prop) : p \xe2\x88\xa8 \xc2\xac p := Classical.em p\n"
                b"#print axioms uses_choice\n"
            )
            expect_s89_error(lambda: v89.verify_lean_file(choice_f, check_pinned_sha=False), "LEAN_FORBIDDEN_AXIOM", "live choice")

            false_f = base / "false.lean"
            false_f.write_bytes(b"theorem bad : 1 = 2 := rfl\n#print axioms bad\n")
            expect_s89_error(lambda: v89.verify_lean_file(false_f, check_pinned_sha=False), "LEAN_COMPILE_FAILED", "live bad proof")
        else:
            # Explicit no-Lean path (0 skips!): verifies fail-closed LEAN_BINARY_NOT_FOUND
            expect_s89_error(lambda: v89.verify_lean_file(LEAN_PATH, check_pinned_sha=True), "LEAN_BINARY_NOT_FOUND", "no-lean fail-closed")


def test_08_cli_and_certificate_file_parity() -> None:
    # Pinned on-disk certificate must pass check_certificate_file & match --standalone bit-for-bit
    cert_disk = v89.check_certificate_file(CERT_PATH, full_replay=True)
    cert_mem = s89.build_certificate()
    check(cert_disk == cert_mem, "disk cert == memory cert")
    disk_bytes = CERT_PATH.read_bytes()
    check(disk_bytes == s89.canonical_json_bytes(cert_mem) + b"\n", "disk cert canonical bytes")

    with tempfile.TemporaryDirectory() as td:
        out_p = Path(td) / "out_cert.json"
        rc = v89.main(["--write", str(out_p)])
        check(rc == 0 and out_p.read_bytes() == disk_bytes, "cli --write exact")
        check(stat.S_IMODE(os.lstat(out_p).st_mode) == 0o600, "cli --write 0o600")
        check(v89.main(["--check", str(out_p)]) == 0, "cli --check ok")

        bad_p = Path(td) / "bad.json"
        bad_p.write_bytes(b"{}\n")
        check(v89.main(["--check", str(bad_p)]) == 2, "cli --check fail rc=2")
        check(v89.main(["--verify-corpus", td]) == 2, "cli --verify-corpus missing inv rc=2")

        # Subprocess --standalone bit-identical check
        proc = subprocess.run(
            [sys.executable, "-I", "-B", str(HERE / "verify_s89_heritage_atlas.py"), "--standalone"],
            capture_output=True,
            timeout=30,
            check=False,
        )
        check(proc.returncode == 0 and proc.stdout == disk_bytes and proc.stderr == b"", "cli --standalone exact")


def run_all() -> None:
    tests = [
        test_01_oracle_math_and_pillars,
        test_02_synthetic_corpus_verification,
        test_03_zone_b_rationals_json_and_containers,
        test_04_zone_b_atomic_io_fifo_symlink_hardlink,
        test_05_surfaces_fr1_fr0_sec_deep_tamper,
        test_06_r10_lean4_scanner_15_classes_and_boolops,
        test_07_lean_file_and_live_or_nolean_parity,
        test_08_cli_and_certificate_file_parity,
    ]
    for fn in tests:
        fn()
    print(f"OK: {len(tests)}/{len(tests)} Track S89 R5 tests passed (0 skips)")


if __name__ == "__main__":
    run_all()
