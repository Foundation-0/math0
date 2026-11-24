#!/usr/bin/env python3
"""Track S41 (Portals 43 + 45): Zone-B Hardened CLI, Replay & Strict-Keyset Secondary Auditor.

Zero external dependencies, zero AST float literals, zero float() calls, zero bare
asserts, zero .isdigit(), zero mathematical RNG (secrets.token_hex(8) used exclusively
for collision-free atomic temp file naming under concurrent writers).

Provides full pure-Z/Q/F_q deterministic replay complemented by a field-complete,
strict-keyset secondary_audit_payload (enforced under both full_replay=True and
full_replay=False via verify_certificate_dict), atomic per-component dir_fd traversal,
dir_fd PWD symlink checking, 65,536-byte streaming capped reads, durable 0o600 atomic
writes (threading.Lock + counter + secrets.token_hex(8) + EEXIST retry + os.fsync(fd) +
pre-replace fstat.st_nlink==1 + target st_nlink<=1 + os.replace(..., dir_fd) +
os.fsync(dfd)), deleted-CWD handling, and strict zero-abbreviation CLI parsing.
"""
from __future__ import annotations

import errno
from fractions import Fraction
import hashlib
import os
from pathlib import Path
import secrets
import stat
import sys
import threading
from typing import Any, Sequence

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

from praxis_we_tomography_oracle import (
    BN254_Q,
    BN254_SEED_T,
    HARD_MAX_BYTES_CAP,
    MAX_JSON_BYTES,
    PraxisTomographyError,
    SCHEMA_VERSION,
    TRACK_ID,
    build_standalone_certificate,
    canonical_json_bytes,
    constant_time_hex64_equal,
    evaluate_lemma_b2_bound,
    format_decimal_trunc,
    parse_bounded_int,
    parse_exact_rational,
    parse_strict_json_text,
    require_bool,
    require_hex64,
    require_int,
    require_str,
    validate_certificate_payload,
)

_EXACT_PATH_TYPE = type(Path("."))
_READ_CHUNK_BYTES = 65536
_TMP_LOCK = threading.Lock()
_TMP_COUNTER = 0
_TMP_MAX_ATTEMPTS = 32

_P1_KEYS = frozenset({
    "field_q",
    "n_forms",
    "c0",
    "omega",
    "k1",
    "k2",
    "nu",
    "eval_points_d",
    "chunk_j_delta",
    "chunk_jp_deltap",
    "copy_count_3n_over_2",
    "quadratic_pair_count_n_n1_over_2",
    "capelli_irreducible_t4_minus_c0",
    "qap_rw_allowed_nu_ndiv_k",
    "eq4_key_remainder_zero",
    "eq4_oth_remainder_zero",
    "neg_control_non_passing_rejected",
    "example52_v_formula_exact",
    "eq5_tie_divisions_exact",
    "eq7_mask_identity_exact",
    "lemma54_exact_match",
    "kappa_expected",
    "kappa_recovered",
    "search_center_cw",
    "search_offset_t",
    "r_w_exact",
    "ciphertext_sha256",
    "decryption_recovered_exact_kappa",
    "decryption_recovered_exact_message",
    "pillar_verified",
})
_P2_KEYS = frozenset({
    "example21_true_witness_count",
    "example21_unsat_witness_count",
    "rank1_witness_passes",
    "rank2_sos_praxis_cheat",
    "rank3_linear_tensor_and_moore",
    "rank4_alternating_sum_cheat",
    "polya_1913_obstruction",
    "pillar_verified",
})
_P2_R2_KEYS = frozenset({
    "exact_rank_over_q",
    "all_tests_passed_over_q",
    "all_15_minors_nonneg_psd",
    "principal_minors_by_size",
    "fig4_f101_phi1_values",
    "fig4_f101_det",
    "fig4_f101_kills_mixture",
    "praxis_quad_ties_broken_by_repeat",
})
_P2_R3_KEYS = frozenset({
    "linear_tensor_exact_rank",
    "all_linear_ties_hold",
    "quad_ties_broken_by_linear_tensor",
    "quad_alt_sum_leaks_row0_or_diag",
    "moore_det_indep_f257_4",
    "moore_indep_nonzero",
    "moore_dep_control_zero",
})
_P2_R4_KEYS = frozenset({
    "exact_rank_f257",
    "booleanity_passed",
    "row0_zero",
    "diag_zero",
    "nonzero_stack",
    "praxis_ties_all_3_hold",
})
_P2_POLYA_KEYS = frozenset({
    "total_3x3_matrices",
    "f2_perm_eq_det_count",
    "z_valid_sign_flip_count",
    "max_permutation_matches_out_of_6",
})
_P3_KEYS = frozenset({
    "bn254_seed_t",
    "bn254_q_str",
    "pocklington_prime_verified",
    "pocklington_factored_f_bits",
    "table4_core",
    "divisibility_q_mod_2dR_eq_1",
    "divisibility_n_divides_q_minus_1",
    "divisibility_h_ord_divides_q_minus_1",
    "capelli_irreducible_t4608_minus_5",
    "g_bounds_exact",
    "search_range_2B_plus_1_lt_q",
    "p1_chunk_bounds_hold",
    "p2_group_coverage_holds",
    "p4_lifting_24beta4_lt_q3",
    "p4_lifting_beta_2_188_lt_q3",
    "prop57_counts",
    "lemma_b2",
    "appendix_c_hair_sahai",
    "pillar_verified",
})
_P3_T4_KEYS = frozenset({
    "N",
    "nc",
    "Fmax",
    "nu",
    "H_order",
    "D",
    "J",
    "Delta",
    "Jp",
    "Deltap",
    "n",
    "c0",
    "dR",
    "k",
    "ell",
    "K1",
    "K2",
    "g",
    "theta_q",
})
_P3_PROP57_KEYS = frozenset({"n1", "n2", "two_n2", "L1", "L2", "LT", "L", "df", "eps_f_q"})
_P3_B2_KEYS = frozenset({"E_2_q", "E_2_101_minus_E_2_q", "E_diff_margin_trunc8", "b2_e2_lt_2_neg122", "b2_e_diff_le_1_minus_2_neg100"})
_P3_HS_KEYS = frozenset({"R", "K", "m", "k_prop_c1_lower_bound", "hs_r3_fails_eq10", "hs_r4_m4_fails_m5_passes_eq10", "hs_prop_c1_gt_2_55_14"})
_P4_KEYS = frozenset({"security_accounting", "table6_lean_vs_paper_deltas", "cs19_sealed_witness_bridge", "pillar_verified"})
_P4_SEC_KEYS = frozenset({
    "reduction_time_bits",
    "msis_matzov_bits",
    "reduction_loss_bits",
    "reduction_loss_decimal",
    "reduction_loss_factor_sq",
    "bn254_etnfs_bits",
    "ggm_target_bits",
    "etnfs_margin_above_ggm_bits",
    "heavy_cheat_lattice_bits",
    "reported_ciphertext_gib_str",
})
_P4_T6_ROW_KEYS = frozenset({"id", "lean_scope", "paper_scope"})
_P4_CS19_KEYS = frozenset({
    "commitment_ciphertext_sha256",
    "valid_witness_kappa",
    "valid_witness_unmasked_exact",
    "invalid_witness_rejected",
    "invalid_witness_status",
})
_PAYLOAD_KEYS = frozenset({
    "oracle_class",
    "novelty_classification",
    "literature_anchors_n0",
    "zero_floats_exact_arithmetic",
    "all_verified",
    "pillar1_executable_praxis_protocol",
    "pillar2_rank_gap_and_polya_obstructions",
    "pillar3_table4_admissibility_and_hair_sahai",
    "pillar4_honest_scope_and_cs19_bridge",
})
_EXPECTED_LITERATURE_ANCHORS = [
    "Tse, Vanjani, Vesely (Nov 2026): Praxis \u2014 Practical Witness Encryption for NP",
    "Hair, Sahai (2026): Witness Encryption from Bounded-Factor MinRank",
    "Polya (1913): Aufgabe 424 (Permanent-to-Determinant Sign-Flip Obstruction)",
    "Lasserre (2001) / Schoenebeck (2008): Sum-of-Squares Semidefinite Hierarchy",
]
_EXPECTED_P1_CIPHERTEXT_SHA256 = "0bf45d6cb0e43ea3173cee4ae42ad3630032925064a0a933da8c530c1201fde2"
_EXPECTED_P2_MOORE_DET_INDEP = [0, 0, 96, 0]
_EXPECTED_P4_CS19_COMMITMENT_SHA256 = "949ca5f6aec7ed7d249499b779b957f7e3f868c288cf559f9676c26031c24ade"
_EXPECTED_P4_TABLE6_ROWS = [
    {
        "id": "T6-01",
        "lean_scope": "Fixed Table 4 parameters with 256-bit messages and seeds",
        "paper_scope": "General admissible parameters (P1)-(P5) and 100-bit messages/seeds",
    },
    {
        "id": "T6-02",
        "lean_scope": "Key derived from opaque sign-class name([kappa]_T)",
        "paper_scope": "Key derived directly from group element [kappa]_T",
    },
    {
        "id": "T6-03",
        "lean_scope": "Exhaustive short-multiple search and logged H_key monitor; counts oracle calls only",
        "paper_scope": "Polynomial-time Lenstra/HNF LIFT (Lemma B.9) and unlogged monitor with explicit runtime t_R",
    },
    {
        "id": "T6-04",
        "lean_scope": "Leaves Groth16 honest setup trapdoor and definition faithfulness outside Lean kernel",
        "paper_scope": "Explicitly assumes Groth16 universal-circuit honest setup (Table 5) and manual definition audit",
    },
]


# ---------------------------------------------------------------------------
# Zone-B Hardened Atomic dir_fd File I/O
# ---------------------------------------------------------------------------

def _require_utf8_str(raw: str, label: str) -> str:
    try:
        raw.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise PraxisTomographyError("INVALID_UTF8_SURROGATE", f"{label} contains lone UTF-16 surrogate") from exc
    return raw


def _step_dir_fd_chain(start_fd: int, components: Sequence[str], label: str) -> int:
    """Atomically traverse directory components via openat(O_RDONLY|O_DIRECTORY|O_NOFOLLOW)."""
    dfd = start_fd
    for comp in components:
        try:
            nxt = os.open(comp, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=dfd)
        except OSError as exc:
            if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                try:
                    is_sym = stat.S_ISLNK(os.lstat(comp, dir_fd=dfd).st_mode)
                except OSError:
                    is_sym = True
                os.close(dfd)
                if is_sym:
                    raise PraxisTomographyError("SYMLINK_FORBIDDEN", f"symlink forbidden at {label}") from exc
                raise PraxisTomographyError("PATH_STAT_ERROR", f"non-directory ancestor at {label}") from exc
            os.close(dfd)
            raise PraxisTomographyError("FILE_IO_ERROR", f"cannot traverse {label}: {type(exc).__name__}") from exc
        os.close(dfd)
        dfd = nxt
    return dfd


def _check_pwd_no_symlinks() -> None:
    pwd_env = os.environ.get("PWD")
    if pwd_env is None or not pwd_env.startswith("/"):
        return
    _require_utf8_str(pwd_env, "PWD")
    pwd_parts = [p for p in Path(pwd_env).parts[1:] if p not in ("", ".")]
    try:
        root_fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    except OSError as exc:
        raise PraxisTomographyError("CWD_UNAVAILABLE", f"cannot open root: {type(exc).__name__}") from exc
    end_fd = _step_dir_fd_chain(root_fd, pwd_parts, "pwd_ancestor")
    os.close(end_fd)


def _open_parent_dir_fd(path: Any) -> tuple[int, str]:
    """Validate exact Path and atomically pin parent dir_fd against TOCTOU swaps."""
    if type(path) is not _EXACT_PATH_TYPE:
        raise PraxisTomographyError("INVALID_PATH_TYPE", "path must be exact pathlib.Path")
    raw_str = str(path)
    if "\x00" in raw_str:
        raise PraxisTomographyError("INVALID_PATH", "path contains NUL byte")
    _require_utf8_str(raw_str, "path")

    if path.is_absolute():
        raw_parts = [p for p in path.parts[1:] if p not in ("", ".")]
        try:
            start_fd = os.open(path.anchor, os.O_RDONLY | os.O_DIRECTORY)
        except OSError as exc:
            raise PraxisTomographyError("FILE_IO_ERROR", f"cannot open root anchor: {type(exc).__name__}") from exc
    else:
        try:
            os.getcwd()
            start_fd = os.open(".", os.O_RDONLY | os.O_DIRECTORY)
        except OSError as exc:
            raise PraxisTomographyError("CWD_UNAVAILABLE", f"current working directory unavailable: {type(exc).__name__}") from exc
        try:
            _check_pwd_no_symlinks()
        except PraxisTomographyError:
            os.close(start_fd)
            raise
        raw_parts = [p for p in path.parts if p not in ("", ".")]

    if not raw_parts or raw_parts[-1] == "..":
        os.close(start_fd)
        raise PraxisTomographyError("NON_REGULAR_FILE", "target path names a directory")

    dfd = _step_dir_fd_chain(start_fd, raw_parts[:-1], "path_component")
    return dfd, raw_parts[-1]


def require_safe_path(path: Any) -> Path:
    """Verify exact Path type, CWD/PWD safety, ancestor traversal, and non-symlink leaf."""
    dfd, leaf = _open_parent_dir_fd(path)
    try:
        try:
            st = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            return path
        except OSError as exc:
            raise PraxisTomographyError("PATH_STAT_ERROR", f"cannot lstat target: {type(exc).__name__}") from exc
        if stat.S_ISLNK(st.st_mode):
            raise PraxisTomographyError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf")
        return path
    finally:
        os.close(dfd)


def read_regular_bytes_capped(path: Path, max_bytes: int = MAX_JSON_BYTES) -> bytes:
    """Stream regular file in bounded 65536-byte chunks via dir_fd + O_NOFOLLOW."""
    cap = require_int(max_bytes, "max_bytes", lo=1, hi=HARD_MAX_BYTES_CAP)
    dfd, leaf = _open_parent_dir_fd(path)
    fd = -1
    try:
        try:
            fd = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=dfd)
        except OSError as exc:
            if exc.errno == errno.ELOOP:
                raise PraxisTomographyError("SYMLINK_FORBIDDEN", "symlink forbidden at leaf") from exc
            raise PraxisTomographyError("FILE_READ_ERROR", f"cannot open file: {type(exc).__name__}") from exc
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise PraxisTomographyError("NON_REGULAR_FILE", "target is not a regular file")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(fd, _READ_CHUNK_BYTES)
            if not chunk:
                break
            total += len(chunk)
            if total > cap:
                raise PraxisTomographyError("FILE_TOO_LARGE", f"file exceeds {cap} bytes")
            chunks.append(chunk)
        return b"".join(chunks)
    except PraxisTomographyError:
        raise
    except OSError as exc:
        raise PraxisTomographyError("FILE_READ_ERROR", f"failed reading file: {type(exc).__name__}") from exc
    finally:
        if fd >= 0:
            os.close(fd)
        os.close(dfd)


def write_regular_file_bytes(path: Path, payload: bytes) -> None:
    """Thread-safe atomic 0o600 dir_fd write with EEXIST retry, fsync, and st_nlink guards."""
    global _TMP_COUNTER
    if type(payload) is not bytes:
        raise PraxisTomographyError("INVALID_WRITE_DATA", "payload must be exact bytes")
    dfd, leaf = _open_parent_dir_fd(path)
    tmp_fd = -1
    created_tmp = False
    tmp_name = ""
    try:
        try:
            st = os.lstat(leaf, dir_fd=dfd)
        except FileNotFoundError:
            st = None
        except OSError as exc:
            raise PraxisTomographyError("FILE_WRITE_ERROR", f"cannot stat target: {type(exc).__name__}") from exc
        if st is not None:
            if stat.S_ISLNK(st.st_mode):
                raise PraxisTomographyError("SYMLINK_FORBIDDEN", "cannot write to symlink target")
            if not stat.S_ISREG(st.st_mode):
                raise PraxisTomographyError("NON_REGULAR_FILE", "cannot write to non-regular file")
            if st.st_nlink > 1:
                raise PraxisTomographyError("HARDLINK_FORBIDDEN", "cannot write through hardlinked file")

        try:
            for _ in range(_TMP_MAX_ATTEMPTS):
                with _TMP_LOCK:
                    _TMP_COUNTER += 1
                    seq = _TMP_COUNTER
                cand = f".s41_praxis_tmp_{os.getpid()}_{seq}_{secrets.token_hex(8)}"
                try:
                    tmp_fd = os.open(
                        cand,
                        os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_NONBLOCK,
                        0o600,
                        dir_fd=dfd,
                    )
                    tmp_name = cand
                    created_tmp = True
                    break
                except FileExistsError:
                    continue
            if not created_tmp:
                raise PraxisTomographyError("TEMP_RETRY_EXHAUSTED", "exhausted atomic temp file retries")
            view = memoryview(payload)
            written = 0
            while written < len(payload):
                written += os.write(tmp_fd, view[written:])
            os.fsync(tmp_fd)
            if os.fstat(tmp_fd).st_nlink != 1:
                raise PraxisTomographyError("HARDLINK_FORBIDDEN", "temp file hardlinked before replace")
            os.replace(tmp_name, leaf, src_dir_fd=dfd, dst_dir_fd=dfd)
            created_tmp = False
            os.close(tmp_fd)
            tmp_fd = -1
            os.fsync(dfd)
        except PraxisTomographyError:
            raise
        except OSError as exc:
            raise PraxisTomographyError("FILE_WRITE_ERROR", f"failed atomic write: {type(exc).__name__}") from exc
    finally:
        if tmp_fd >= 0:
            os.close(tmp_fd)
        if created_tmp:
            try:
                os.unlink(tmp_name, dir_fd=dfd)
            except OSError:
                pass
        os.close(dfd)


# ---------------------------------------------------------------------------
# Field-Complete Strict-Keyset Secondary Audit (Enforced Under full_replay=False)
# ---------------------------------------------------------------------------

def _require_exact_dict_keys(obj: Any, expected: frozenset[str], code: str, label: str) -> dict[str, Any]:
    if type(obj) is not dict or frozenset(obj.keys()) != expected:
        raise PraxisTomographyError(code, f"{label} keys mismatch")
    return obj


def secondary_audit_payload(payload: Any) -> dict[str, Any]:
    """Field-complete strict-keyset algebraic & type audit across all 4 Track S41 pillars."""
    if type(payload) is not dict:
        raise PraxisTomographyError("AUDIT_PAYLOAD_TYPE", "payload must be strict dict")
    if frozenset(payload.keys()) != _PAYLOAD_KEYS:
        raise PraxisTomographyError("AUDIT_PAYLOAD_KEYS", "payload top-level keys mismatch")
    if not require_bool(payload["all_verified"], "all_verified"):
        raise PraxisTomographyError("AUDIT_ALL_VERIFIED_FALSE", "payload.all_verified must be True")
    if not all((
        require_str(payload["oracle_class"], "oracle_class", max_len=32) == "exact",
        require_str(payload["novelty_classification"], "novelty_classification", max_len=32) == "N1",
        require_bool(payload["zero_floats_exact_arithmetic"], "zero_floats_exact_arithmetic"),
    )):
        raise PraxisTomographyError("AUDIT_PAYLOAD_META", "payload metadata mismatch")
    anchors = payload["literature_anchors_n0"]
    if type(anchors) is not list or [require_str(a, "lit", max_len=256) for a in anchors] != _EXPECTED_LITERATURE_ANCHORS:
        raise PraxisTomographyError("AUDIT_LITERATURE_ANCHORS", "literature_anchors_n0 mismatch")

    try:
        # Pillar 1: Executable small-prime-field Praxis core protocol
        p1 = _require_exact_dict_keys(payload["pillar1_executable_praxis_protocol"], _P1_KEYS, "AUDIT_P1_KEYS", "pillar1")
        if not all((
            require_int(p1["field_q"], "p1.q") == 257,
            require_int(p1["n_forms"], "p1.n") == 4,
            require_int(p1["c0"], "p1.c0") == 3,
            require_int(p1["omega"], "p1.omega") == pow(3, 64, 257),
            require_int(p1["k1"], "p1.k1") == 2,
            require_int(p1["k2"], "p1.k2") == 1,
            require_int(p1["nu"], "p1.nu") == 2,
            require_int(p1["eval_points_d"], "p1.D") == 9,
            p1["chunk_j_delta"] == [2, 5],
            p1["chunk_jp_deltap"] == [2, 2],
            require_int(p1["copy_count_3n_over_2"], "p1.copies") == 6,
            require_int(p1["quadratic_pair_count_n_n1_over_2"], "p1.pairs") == 10,
        )):
            raise PraxisTomographyError("AUDIT_P1_PARAMS", "Pillar 1 small-field Praxis parameters mismatch")
        if not all((
            require_bool(p1["capelli_irreducible_t4_minus_c0"], "p1.cap"),
            require_bool(p1["qap_rw_allowed_nu_ndiv_k"], "p1.rw"),
            require_bool(p1["eq4_key_remainder_zero"], "p1.eq4k"),
            require_bool(p1["eq4_oth_remainder_zero"], "p1.eq4o"),
            require_bool(p1["neg_control_non_passing_rejected"], "p1.neg"),
            require_bool(p1["example52_v_formula_exact"], "p1.ex52"),
            require_bool(p1["eq5_tie_divisions_exact"], "p1.eq5"),
            require_bool(p1["eq7_mask_identity_exact"], "p1.eq7"),
            require_bool(p1["lemma54_exact_match"], "p1.l54"),
            require_bool(p1["decryption_recovered_exact_kappa"], "p1.kap"),
            require_bool(p1["decryption_recovered_exact_message"], "p1.msg"),
            require_bool(p1["pillar_verified"], "p1.ver"),
        )):
            raise PraxisTomographyError("AUDIT_P1_FLAGS", "Pillar 1 protocol certification flags must all be True")
        kap_exp = require_int(p1["kappa_expected"], "p1.kap_exp", lo=1, hi=256)
        kap_rec = require_int(p1["kappa_recovered"], "p1.kap_rec", lo=1, hi=256)
        cw = require_int(p1["search_center_cw"], "p1.cw")
        t_off = require_int(p1["search_offset_t"], "p1.t")
        r_w = require_int(p1["r_w_exact"], "p1.rw")
        ct_sha = require_hex64(p1["ciphertext_sha256"], "p1.ct_sha")
        if not all((
            kap_exp == 65,
            kap_rec == 65,
            cw == 10,
            t_off == 2,
            r_w == 12,
            constant_time_hex64_equal(ct_sha, _EXPECTED_P1_CIPHERTEXT_SHA256, "p1.ct_sha"),
        )):
            raise PraxisTomographyError("AUDIT_P1_DECRYPT", "Pillar 1 kappa, search offset, or ciphertext digest mismatch")

        # Pillar 2: Rank-1/2/3/4 cheats, Moore determinant, SOS PSD & Polya (1913)
        p2 = _require_exact_dict_keys(payload["pillar2_rank_gap_and_polya_obstructions"], _P2_KEYS, "AUDIT_P2_KEYS", "pillar2")
        if not all((
            require_int(p2["example21_true_witness_count"], "p2.tw") == 1,
            require_int(p2["example21_unsat_witness_count"], "p2.uw") == 0,
            require_bool(p2["rank1_witness_passes"], "p2.r1"),
            require_bool(p2["pillar_verified"], "p2.ver"),
        )):
            raise PraxisTomographyError("AUDIT_P2_BASE", "Pillar 2 Example 2.1 witness counts or rank-1 flag mismatch")
        r2 = _require_exact_dict_keys(p2["rank2_sos_praxis_cheat"], _P2_R2_KEYS, "AUDIT_P2_R2_KEYS", "p2.r2")
        minors = _require_exact_dict_keys(
            r2["principal_minors_by_size"],
            frozenset({"size_1", "size_2", "size_3", "size_4"}),
            "AUDIT_P2_R2_MINORS",
            "p2.r2.minors",
        )
        if not all((
            require_int(r2["exact_rank_over_q"], "p2.r2.rank") == 2,
            require_bool(r2["all_tests_passed_over_q"], "p2.r2.tests"),
            require_bool(r2["all_15_minors_nonneg_psd"], "p2.r2.psd"),
            minors["size_1"] == ["1", "1", "1/2", "1"],
            minors["size_2"] == ["0", "1/4", "0", "1/4", "0", "1/4"],
            minors["size_3"] == ["0", "0", "0", "0"],
            minors["size_4"] == ["0"],
            r2["fig4_f101_phi1_values"] == [61, 94],
            require_int(r2["fig4_f101_det"], "p2.r2.det") == 68,
            require_bool(r2["fig4_f101_kills_mixture"], "p2.r2.fig4"),
            require_bool(r2["praxis_quad_ties_broken_by_repeat"], "p2.r2.ties"),
        )):
            raise PraxisTomographyError("AUDIT_P2_R2", "Pillar 2 rank-2 SOS/Praxis witness mismatch")
        r3 = _require_exact_dict_keys(p2["rank3_linear_tensor_and_moore"], _P2_R3_KEYS, "AUDIT_P2_R3_KEYS", "p2.r3")
        mdet = r3["moore_det_indep_f257_4"]
        if type(mdet) is not list:
            raise PraxisTomographyError("AUDIT_P2_R3", "moore_det_indep_f257_4 must be strict list")
        mdet_ints = [require_int(x, "mdet") for x in mdet]
        if not all((
            require_int(r3["linear_tensor_exact_rank"], "p2.r3.rank") == 3,
            require_bool(r3["all_linear_ties_hold"], "p2.r3.lt"),
            require_bool(r3["quad_ties_broken_by_linear_tensor"], "p2.r3.qt"),
            require_bool(r3["quad_alt_sum_leaks_row0_or_diag"], "p2.r3.leak"),
            mdet_ints == _EXPECTED_P2_MOORE_DET_INDEP,
            require_bool(r3["moore_indep_nonzero"], "p2.r3.mnz"),
            require_bool(r3["moore_dep_control_zero"], "p2.r3.mdz"),
        )):
            raise PraxisTomographyError("AUDIT_P2_R3", "Pillar 2 rank-3 tensor or Moore determinant witness mismatch")
        r4 = _require_exact_dict_keys(p2["rank4_alternating_sum_cheat"], _P2_R4_KEYS, "AUDIT_P2_R4_KEYS", "p2.r4")
        if not all((
            require_int(r4["exact_rank_f257"], "p2.r4.rank") == 4,
            require_bool(r4["booleanity_passed"], "p2.r4.bool"),
            require_bool(r4["row0_zero"], "p2.r4.r0"),
            require_bool(r4["diag_zero"], "p2.r4.dg"),
            require_bool(r4["nonzero_stack"], "p2.r4.nz"),
            require_bool(r4["praxis_ties_all_3_hold"], "p2.r4.ties"),
        )):
            raise PraxisTomographyError("AUDIT_P2_R4", "Pillar 2 rank-4 alternating-sum cheat witness mismatch")
        pol = _require_exact_dict_keys(p2["polya_1913_obstruction"], _P2_POLYA_KEYS, "AUDIT_P2_POLYA_KEYS", "p2.polya")
        if not all((
            require_int(pol["total_3x3_matrices"], "pol.tot") == 512,
            require_int(pol["f2_perm_eq_det_count"], "pol.f2") == 512,
            require_int(pol["z_valid_sign_flip_count"], "pol.z") == 0,
            require_int(pol["max_permutation_matches_out_of_6"], "pol.max") == 5,
        )):
            raise PraxisTomographyError("AUDIT_P2_POLYA", "Pillar 2 Polya (1913) 0/512 obstruction mismatch")

        # Pillar 3: Table 4 BN254 admissibility, Prop 5.7, Lemma B.2 E(u), Appendix C
        p3 = _require_exact_dict_keys(payload["pillar3_table4_admissibility_and_hair_sahai"], _P3_KEYS, "AUDIT_P3_KEYS", "pillar3")
        t4 = _require_exact_dict_keys(p3["table4_core"], _P3_T4_KEYS, "AUDIT_P3_T4_KEYS", "p3.t4")
        p57 = _require_exact_dict_keys(p3["prop57_counts"], _P3_PROP57_KEYS, "AUDIT_P3_P57_KEYS", "p3.p57")
        b2 = _require_exact_dict_keys(p3["lemma_b2"], _P3_B2_KEYS, "AUDIT_P3_B2_KEYS", "p3.b2")
        hs = _require_exact_dict_keys(p3["appendix_c_hair_sahai"], _P3_HS_KEYS, "AUDIT_P3_HS_KEYS", "p3.hs")
        q_val = parse_bounded_int(p3["bn254_q_str"], "p3.q")
        t_seed = require_int(p3["bn254_seed_t"], "p3.t")
        if not all((
            t_seed == BN254_SEED_T,
            q_val == BN254_Q,
            require_bool(p3["pocklington_prime_verified"], "p3.pock"),
            require_int(p3["pocklington_factored_f_bits"], "p3.fbits") == 161,
            require_int(t4["N"], "t4.N") == 391693,
            require_int(t4["nc"], "t4.nc") == 1694,
            require_int(t4["Fmax"], "t4.Fmax") == 2047,
            require_int(t4["nu"], "t4.nu") == 2048,
            require_int(t4["H_order"], "t4.H") == (1 << 22),
            require_int(t4["D"], "t4.D") == 3861007,
            require_int(t4["J"], "t4.J") == 11,
            require_int(t4["Delta"], "t4.Delta") == 351001,
            require_int(t4["Jp"], "t4.Jp") == 11,
            require_int(t4["Deltap"], "t4.Deltap") == 315392,
            require_int(t4["n"], "t4.n") == 4608,
            require_int(t4["c0"], "t4.c0") == 5,
            require_int(t4["dR"], "t4.dR") == 64,
            require_int(t4["k"], "t4.k") == 71,
            require_int(t4["ell"], "t4.ell") == 6121,
            require_int(t4["K1"], "t4.K1") == 192,
            require_int(t4["K2"], "t4.K2") == 12,
            require_int(t4["g"], "t4.g") == 1736375024658487,
            parse_exact_rational(t4["theta_q"], "t4.theta") == Fraction((1 << 20) - 1, 1 << 221),
        )):
            raise PraxisTomographyError("AUDIT_P3_TABLE4", "Pillar 3 Table 4 or BN254 parameter mismatch")
        if not all((
            require_bool(p3["divisibility_q_mod_2dR_eq_1"], "p3.d1"),
            require_bool(p3["divisibility_n_divides_q_minus_1"], "p3.d2"),
            require_bool(p3["divisibility_h_ord_divides_q_minus_1"], "p3.d3"),
            require_bool(p3["capelli_irreducible_t4608_minus_5"], "p3.cap"),
            require_bool(p3["g_bounds_exact"], "p3.gb"),
            require_bool(p3["search_range_2B_plus_1_lt_q"], "p3.sr"),
            require_bool(p3["p1_chunk_bounds_hold"], "p3.p1"),
            require_bool(p3["p2_group_coverage_holds"], "p3.p2"),
            require_bool(p3["p4_lifting_24beta4_lt_q3"], "p3.p4a"),
            require_bool(p3["p4_lifting_beta_2_188_lt_q3"], "p3.p4b"),
            require_bool(p3["pillar_verified"], "p3.ver"),
        )):
            raise PraxisTomographyError("AUDIT_P3_FLAGS", "Pillar 3 admissibility flags must all be True")
        n1_exp = (2 * 192 + 1) * (391693 + 1) + 351001 + (2047 * 1694) // 11
        n2_exp = 6 * 12 * (391693 + 1) + 3 * 12 + (3 * 4608 // 2) * 22 + 13 * 4608 - 8
        l1_exp, l2_exp, lt_exp = n1_exp + 1, 2 * n2_exp + 1, 2
        l_exp = l1_exp + l2_exp + lt_exp
        df_exp = 3 * 3861007 + 2 * 4608 + 2 * 192 + 6
        eps_exp = Fraction(df_exp + 61, BN254_Q - 3861007)
        if not all((
            require_int(p57["n1"], "p57.n1") == n1_exp,
            require_int(p57["n2"], "p57.n2") == n2_exp,
            require_int(p57["two_n2"], "p57.2n2") == 2 * n2_exp,
            require_int(p57["L1"], "p57.L1") == l1_exp,
            require_int(p57["L2"], "p57.L2") == l2_exp,
            require_int(p57["LT"], "p57.LT") == lt_exp,
            require_int(p57["L"], "p57.L") == l_exp,
            require_int(p57["df"], "p57.df") == df_exp,
            parse_exact_rational(p57["eps_f_q"], "p57.eps") == eps_exp,
        )):
            raise PraxisTomographyError("AUDIT_P3_PROP57", "Pillar 3 Proposition 5.7 counts mismatch")
        nf_exp = (1 << 254) - l_exp - 3 * (1 << 101) - 1
        th_exp = Fraction((1 << 20) - 1, 1 << 221)
        e2_exp = evaluate_lemma_b2_bound(2, l1_exp, l2_exp, lt_exp, eps_exp, th_exp, nf_exp, lam=100)
        ediff_exp = evaluate_lemma_b2_bound(1 << 101, l1_exp, l2_exp, lt_exp, eps_exp, th_exp, nf_exp, lam=100) - e2_exp
        if not all((
            parse_exact_rational(b2["E_2_q"], "b2.e2") == e2_exp,
            parse_exact_rational(b2["E_2_101_minus_E_2_q"], "b2.ediff") == ediff_exp,
            b2["E_diff_margin_trunc8"] == format_decimal_trunc((Fraction(1, 1) - Fraction(1, 1 << 100)) - ediff_exp, places=8),
            require_bool(b2["b2_e2_lt_2_neg122"], "b2.f1"),
            require_bool(b2["b2_e_diff_le_1_minus_2_neg100"], "b2.f2"),
        )):
            raise PraxisTomographyError("AUDIT_P3_LEMMAB2", "Pillar 3 Lemma B.2 E(u) exact values mismatch")
        if not all((
            require_int(hs["R"], "hs.R") == 4,
            require_int(hs["K"], "hs.K") == 219348150,
            require_int(hs["m"], "hs.m") == 85917354266100,
            require_int(hs["k_prop_c1_lower_bound"], "hs.k") == 39888960295450910,
            require_bool(hs["hs_r3_fails_eq10"], "hs.r3"),
            require_bool(hs["hs_r4_m4_fails_m5_passes_eq10"], "hs.r4"),
            require_bool(hs["hs_prop_c1_gt_2_55_14"], "hs.c1"),
        )):
            raise PraxisTomographyError("AUDIT_P3_HAIR_SAHAI", "Pillar 3 Appendix C Hair-Sahai bounds mismatch")

        # Pillar 4: Honest scope ledger & CS-19 sealed-witness bridge
        p4 = _require_exact_dict_keys(payload["pillar4_honest_scope_and_cs19_bridge"], _P4_KEYS, "AUDIT_P4_KEYS", "pillar4")
        sec_acc = _require_exact_dict_keys(p4["security_accounting"], _P4_SEC_KEYS, "AUDIT_P4_SEC_KEYS", "p4.sec")
        cs19 = _require_exact_dict_keys(p4["cs19_sealed_witness_bridge"], _P4_CS19_KEYS, "AUDIT_P4_CS19_KEYS", "p4.cs19")
        t6_rows = p4["table6_lean_vs_paper_deltas"]
        if not all((
            parse_exact_rational(sec_acc["reduction_time_bits"], "p4.red") == Fraction(108, 1),
            parse_exact_rational(sec_acc["msis_matzov_bits"], "p4.msis") == Fraction(207, 2),
            parse_exact_rational(sec_acc["reduction_loss_bits"], "p4.loss") == Fraction(9, 2),
            sec_acc["reduction_loss_decimal"] == "4.5",
            require_int(sec_acc["reduction_loss_factor_sq"], "p4.lsq") == 512,
            require_int(sec_acc["bn254_etnfs_bits"], "p4.etnfs") == 103,
            require_int(sec_acc["ggm_target_bits"], "p4.ggm") == 100,
            require_int(sec_acc["etnfs_margin_above_ggm_bits"], "p4.emarg") == 3,
            require_int(sec_acc["heavy_cheat_lattice_bits"], "p4.hc") == 173,
            sec_acc["reported_ciphertext_gib_str"] == "7.88",
            require_bool(p4["pillar_verified"], "p4.ver"),
        )):
            raise PraxisTomographyError("AUDIT_P4_SECURITY", "Pillar 4 reduction-loss or ETNFS accounting mismatch")
        if type(t6_rows) is not list:
            raise PraxisTomographyError("AUDIT_P4_TABLE6", "Table 6 must be a list of delta entries")
        t6_checked: list[dict[str, str]] = []
        for idx, row in enumerate(t6_rows):
            rd = _require_exact_dict_keys(row, _P4_T6_ROW_KEYS, "AUDIT_P4_TABLE6", f"p4.t6[{idx}]")
            rid = require_str(rd["id"], f"t6[{idx}].id", max_len=32)
            l_sc = require_str(rd["lean_scope"], f"t6[{idx}].lean", max_len=256)
            p_sc = require_str(rd["paper_scope"], f"t6[{idx}].paper", max_len=256)
            t6_checked.append({"id": rid, "lean_scope": l_sc, "paper_scope": p_sc})
        if t6_checked != _EXPECTED_P4_TABLE6_ROWS:
            raise PraxisTomographyError("AUDIT_P4_TABLE6", "Table 6 delta rows mismatch")
        cs19_sha = require_hex64(cs19["commitment_ciphertext_sha256"], "p4.cs19.sha")
        cs19_kap = require_int(cs19["valid_witness_kappa"], "p4.cs19.kap", lo=1, hi=256)
        if not all((
            constant_time_hex64_equal(cs19_sha, _EXPECTED_P4_CS19_COMMITMENT_SHA256, "p4.cs19.sha"),
            cs19_kap == 21,
            require_bool(cs19["valid_witness_unmasked_exact"], "p4.cs19.ok"),
            require_bool(cs19["invalid_witness_rejected"], "p4.cs19.rej"),
            cs19["invalid_witness_status"] == "NON_WITNESS_REJECTED",
        )):
            raise PraxisTomographyError("AUDIT_P4_CS19", "Pillar 4 CS-19 sealed-witness bridge mismatch")
    except PraxisTomographyError:
        raise
    except (KeyError, TypeError, AttributeError) as exc:
        raise PraxisTomographyError("AUDIT_SCHEMA_ERROR", f"malformed payload structure: {type(exc).__name__}") from exc

    return {
        "secondary_audit_passed": True,
        "pillars_checked": 4,
        "table6_deltas_checked": len(t6_rows),
        "polya_matrices_checked": pol["total_3x3_matrices"],
    }


def verify_certificate_dict(cert: Any, full_replay: bool = True) -> dict[str, Any]:
    """Verify certificate dict under full_replay=True or False, ALWAYS running secondary_audit_payload."""
    res = validate_certificate_payload(cert, full_replay=full_replay)
    sec = secondary_audit_payload(cert["payload"])
    res["secondary_audit"] = sec
    return res


def check_certificate_file(path: Path) -> dict[str, Any]:
    raw = read_regular_bytes_capped(path)
    if b"\r" in raw:
        raise PraxisTomographyError("CRLF_FORBIDDEN", "CRLF line endings forbidden in certificate")
    if not raw.endswith(b"\n"):
        raise PraxisTomographyError("MISSING_TRAILING_LF", "certificate must end with a single LF")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise PraxisTomographyError("INVALID_UTF8", "certificate is not valid UTF-8") from exc
    cert = parse_strict_json_text(text, require_object=True)
    canonical_raw = canonical_json_bytes(cert)
    if raw != canonical_raw + b"\n":
        raise PraxisTomographyError("NON_CANONICAL_BYTES", "certificate bytes are not canonical ASCII JSON + LF")
    res = verify_certificate_dict(cert, full_replay=True)
    res["canonical_sha256"] = hashlib.sha256(canonical_raw).hexdigest()
    res["file_sha256"] = hashlib.sha256(raw).hexdigest()
    return res


def write_certificate_file(path: Path) -> dict[str, Any]:
    cert = build_standalone_certificate()
    canonical_raw = canonical_json_bytes(cert)
    raw = canonical_raw + b"\n"
    write_regular_file_bytes(path, raw)
    return {
        "written": True,
        "schema": SCHEMA_VERSION,
        "track_id": TRACK_ID,
        "payload_sha256": cert["payload_sha256"],
        "certificate_sha256": cert["certificate_sha256"],
        "file_sha256": hashlib.sha256(raw).hexdigest(),
    }


# ---------------------------------------------------------------------------
# Strict Zero-Abbreviation Fail-Closed CLI Parsing
# ---------------------------------------------------------------------------

def _validate_cli_path_value(flag: str, val: str) -> Path:
    _require_utf8_str(val, f"{flag}.path")
    if not val or val.startswith("-"):
        raise PraxisTomographyError("INVALID_PATH_ARG", f"{flag} path cannot be empty or flag-like")
    return Path(val)


def _parse_cli_argv(argv: Sequence[str]) -> tuple[str, Path | None, bool]:
    if type(argv) not in (list, tuple) or any(type(item) is not str for item in argv):
        raise PraxisTomographyError("INVALID_ARGV", "argv must be exact list/tuple of strict str")
    mode: str | None = None
    target: Path | None = None
    as_json = False
    i = 0
    n = len(argv)
    while i < n:
        tok = _require_utf8_str(argv[i], "argv")
        if tok == "--json":
            if as_json:
                raise PraxisTomographyError("DUPLICATE_FLAG", "duplicate --json flag")
            as_json = True
            i += 1
        elif tok == "--standalone":
            if mode is not None:
                raise PraxisTomographyError("CONFLICTING_MODE", "multiple mode flags forbidden")
            mode = "standalone"
            i += 1
        elif tok in ("--check", "--write"):
            if mode is not None:
                raise PraxisTomographyError("CONFLICTING_MODE", "multiple mode flags forbidden")
            if i + 1 >= n:
                raise PraxisTomographyError("MISSING_PATH_ARG", f"{tok} requires a path argument")
            mode = "check" if tok == "--check" else "write"
            target = _validate_cli_path_value(tok, argv[i + 1])
            i += 2
        elif tok.startswith("--check=") or tok.startswith("--write="):
            if mode is not None:
                raise PraxisTomographyError("CONFLICTING_MODE", "multiple mode flags forbidden")
            flag_name, raw_val = tok.split("=", 1)
            mode = "check" if flag_name == "--check" else "write"
            target = _validate_cli_path_value(flag_name, raw_val)
            i += 1
        else:
            raise PraxisTomographyError("UNKNOWN_FLAG", f"unrecognized CLI argument: {tok}")

    if mode is None:
        mode = "standalone"
    return mode, target, as_json


def main(argv: Sequence[str] | None = None) -> int:
    raw_argv: Any = sys.argv[1:] if argv is None else argv
    try:
        mode, target, as_json = _parse_cli_argv(raw_argv)
        if mode == "standalone":
            out: dict[str, Any] = build_standalone_certificate()
        elif mode == "write":
            out = write_certificate_file(target)  # type: ignore[arg-type]
        else:
            out = check_certificate_file(target)  # type: ignore[arg-type]
    except PraxisTomographyError as exc:
        err = {"valid": False, "error_code": exc.code, "error_message": exc.message}
        sys.stderr.write(canonical_json_bytes(err).decode("ascii") + "\n")
        return 2

    if as_json:
        sys.stdout.write(canonical_json_bytes(out).decode("ascii") + "\n")
    else:
        sys.stdout.write(
            f"OK {SCHEMA_VERSION} payload_sha256={out['payload_sha256']} "
            f"certificate_sha256={out['certificate_sha256']}\n"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
