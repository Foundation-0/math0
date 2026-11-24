"""Dual-mode (standalone_pinned_replay + live_portal_audit) runner and strict
--verify FILE validator for the MiniMax-AI/Research Cryptography Portal Audit.

Pure Python 3 stdlib. Zero floats. Zero bare assert statements. Zero subprocess calls.
"""

import argparse
import hashlib
import json
import os
import re
import stat
import sys

_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
if _SCRIPT_DIR not in sys.path:
    sys.path.insert(0, _SCRIPT_DIR)

from minimax_cryptanalysis_oracle import (
    MAX_INT_BITS,
    MAX_INT_DIGITS,
    MinimaxCryptError,
    REQUIRED_LEAN_FILES,
    UPSTREAM_COMMIT,
    _strict_equal,
    audit_background_goppa_and_hawk_identities_exact,
    audit_bentsum_walsh_exact,
    audit_fast_algebraic_and_blender_exact,
    canonical_json_bytes,
    canonical_sha256,
    certify_minimax_cryptanalysis_audit_exact,
    require_exact_bool,
    require_exact_int,
    require_hex_sha1,
    require_hex_sha256,
    require_non_empty_str,
    snf_2adic_valuations_exact,
    verify_no_floats,
)


OPERATOR_LABELS = (
    "bentsum_walsh_hadamard_weight_congruence_and_anf",
    "aradi_orthogonal_island_collapse_and_blind_column_audit",
    "colm_gf2_128_rabin_irred_transplant_and_tau_obstruction",
    "sbcvole_gf2_257_single_signature_linear_key_recovery",
    "blender256_standard_iv_parity_and_2adic_snf_closure",
    "tii_mceliece_binary_goppa_primal_shortening_identity",
    "hawk_parity_sublattice_index_and_exact_lll_gram_conditioning",
)

# Pinned declared upstream metadata from MiniMax-AI/Research @ 57842cef92e84eaf8e2535b12f48ba5586080ddd
STANDALONE_PORTAL_FIXTURE = {
    "diag_source": "standalone_pinned_fixture",
    "upstream_commit": UPSTREAM_COMMIT,
    "bentsum_lean": {
        "files_checked": 5,
        "banned_construct_findings": 0,
        "lean_file_sha256": {
            "BentSum.lean": "6bcd5557d4cc90b94e2dde3781b667261376d454363f2ee53c533540e73127de",
            "BentSum/Basic.lean": "db88b32349a4815f9050892e4d89e698b7e2b9743221e257d1dd53f134707961",
            "BentSum/Congruence.lean": "8ff756e7dd01ace03e83de619906ab6427779fd55a579958c8d1044eaaf3693b",
            "BentSum/Counterexample.lean": "d03e1786d2e894266aece0a82841fecef31c445c043c9af668dd01bb3682c5ea",
            "BentSum/Derivative.lean": "53e614fa14c3ac2436b6f611a4f1fbba731031ef7c767b0f7e95ca0ebc0af72b",
        },
    },
    "blender_snf_witness": {
        "witness_sha256": "6dbb69faecd65810b70e4b396a347fb20a76170ffa90fb81260c3a8508d828eb",
        "unshifted_count": 80,
        "shifted_multi_count": 101,
        "unshifted_snf_exps": [0, 0, 1, 1, 2, 2, 3, 3],
        "shifted_multi_snf_exps": [0, 0, 1, 1, 1, 1, 1, 1],
        "f2_xor_fail_count": 100,
        "mod32_superposition_pass_count": 100,
    },
    "blender_issues_text_checks": {
        "issue1_global_minimum_claim_present": True,
        "issue2_sec33_w0246_in_x_notx_present": True,
    },
    "tii_94_summary": {
        "summary_sha256": "c7bc0c0c56e967d5d0a5cbbc2800451d928c3faf5f4f5ac582c8dfafa2d8227f",
        "total_solved": 94,
        "route_a_solved": 89,
        "route_b_solved": 5,
        "first_bloods": 55,
    },
}

PINNED_PORTAL_DIGESTS = {
    "lean_file_sha256": dict(STANDALONE_PORTAL_FIXTURE["bentsum_lean"]["lean_file_sha256"]),
    "blender_snf_witness_sha256": STANDALONE_PORTAL_FIXTURE["blender_snf_witness"]["witness_sha256"],
    "tii_94_summary_sha256": STANDALONE_PORTAL_FIXTURE["tii_94_summary"]["summary_sha256"],
}

# Lexical token scan for 12 Lean 4 soundness-bypass patterns (not Lean kernel elaboration)
_LEAN_BANNED_WORD_RE = re.compile(
    r"\b(sorry|sorryAx|axiom|native_decide|unsafe|implemented_by|admit|extern|ofReduceBool|ofReduceNat)\b"
)
_LEAN_DECIDE_NATIVE_RE = re.compile(
    r"\bdecide(?:\s+[+-][A-Za-z_][A-Za-z0-9_]*)*\s+\+native\b"
    r"|\bdecide\s*\(\s*config\s*:=\s*(?:\(\s*)*\{[^}]*\bnative\s*:=\s*true\b[^}]*\}(?:\s*:\s*[^)]*)?(?:\s*\))*\s*\)"
    r"|\bDecideConfig\b[^:=;\n]*:=\s*(?:\(\s*)*\{[^}]*\bnative\s*:=\s*true\b[^}]*\}"
    r"|\{[^}]*\bnative\s*:=\s*true\b[^}]*\}\s*:\s*(?:[A-Za-z_][A-Za-z0-9_]*\.)*DecideConfig\b"
    r"|\{[^}]*\bnative\s*:=\s*true\b[^}]*:\s*(?:[A-Za-z_][A-Za-z0-9_]*\.)*DecideConfig\b[^}]*\}"
)
_LEAN_SKIP_KERNEL_TC_RE = re.compile(
    r"\b(?:set_option\s+(?:debug\.)?)?skipKernelTC\b"
)


def _is_lean_ident_char(ch):
    return ch.isalnum() or ch == "_"


def _strip_lean_comments(text):
    """Strip Lean 4 comments (-- ..., nested /- ... -/) and string/raw-string/char literals.

    Handles multi-hash raw strings r#"..."#, zero-hash raw strings r"..." (where backslash is
    NOT an escape character), and interpolated strings s!"..." / m!"..." / f!"..." (stripping
    literal text and escaped \\{ / \\} while retaining live {...} expressions for scanning).
    """
    out = []
    i = 0
    n = len(text)
    depth = 0
    interp_stack = []
    while i < n:
        if depth > 0:
            if text[i : i + 2] == "/-":
                depth += 1
                i += 2
            elif text[i : i + 2] == "-/":
                depth -= 1
                i += 2
            else:
                i += 1
        elif interp_stack and interp_stack[-1] == 0:
            ch = text[i]
            if ch == "\\":
                i += 2
            elif ch == '"':
                interp_stack.pop()
                out.append('""')
                i += 1
            elif ch == "{":
                interp_stack[-1] = 1
                out.append(" ")
                i += 1
            else:
                i += 1
        elif text[i : i + 2] == "--":
            nl = text.find("\n", i)
            if nl == -1:
                break
            out.append("\n")
            i = nl + 1
        elif text[i : i + 2] == "/-":
            depth = 1
            i += 2
        elif (
            text[i] in ("s", "m", "f")
            and text[i + 1 : i + 3] == '!"'
            and (i == 0 or not _is_lean_ident_char(text[i - 1]))
        ):
            interp_stack.append(0)
            i += 3
        elif text[i] == "r" and (i == 0 or not _is_lean_ident_char(text[i - 1])):
            j = i + 1
            while j < n and text[j] == "#":
                j += 1
            if j < n and text[j] == '"':
                hashes = j - (i + 1)
                i = j + 1
                closing = '"' + ("#" * hashes)
                end_pos = text.find(closing, i)
                if end_pos == -1:
                    out.append('""')
                    i = n
                else:
                    out.append('""')
                    i = end_pos + len(closing)
            else:
                out.append(text[i])
                i += 1
        elif text[i] == '"':
            i += 1
            while i < n:
                ch = text[i]
                if ch == "\\":
                    i += 2
                elif ch == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append('""')
        elif text[i] == "'" and (i == 0 or not _is_lean_ident_char(text[i - 1])):
            if i + 3 < n and text[i + 1] == "\\" and text[i + 3] == "'":
                out.append("''")
                i += 4
            elif i + 2 < n and text[i + 1] not in ("'", "\n", "\\") and text[i + 2] == "'":
                out.append("''")
                i += 3
            else:
                out.append(text[i])
                i += 1
        elif interp_stack and text[i] == "{":
            interp_stack[-1] += 1
            out.append("{")
            i += 1
        elif interp_stack and text[i] == "}":
            interp_stack[-1] -= 1
            if interp_stack[-1] == 0:
                out.append(" ")
            else:
                out.append("}")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def scan_lean4_lexical(text):
    """Lexical token scan over comment/string-stripped Lean 4 source (not Lean kernel elaboration)."""
    stripped = _strip_lean_comments(text)
    findings = []
    for m in _LEAN_BANNED_WORD_RE.finditer(stripped):
        findings.append(m.group(1))
    for _ in _LEAN_DECIDE_NATIVE_RE.finditer(stripped):
        findings.append("decide +native")
    for _ in _LEAN_SKIP_KERNEL_TC_RE.finditer(stripped):
        findings.append("set_option debug.skipKernelTC")
    return findings


def _parse_strict_json_text(text, label="json"):
    """Parse JSON strictly: reject floats, NaN/Inf, duplicate keys, oversized ints, and deep nesting."""

    def _reject_float(raw):
        raise MinimaxCryptError("FLOAT_FORBIDDEN", f"float literal {raw!r} forbidden in {label}")

    def _reject_const(raw):
        raise MinimaxCryptError("FLOAT_FORBIDDEN", f"non-finite literal {raw!r} forbidden in {label}")

    def _parse_bounded_int(raw):
        digits = raw[1:] if raw.startswith("-") else raw
        if len(digits) > MAX_INT_DIGITS:
            raise MinimaxCryptError("INT_TOO_LARGE", f"integer exceeds {MAX_INT_DIGITS} digits in {label}")
        return int(raw)

    def _no_dup_pairs(pairs):
        out = {}
        for k, v in pairs:
            if k in out:
                raise MinimaxCryptError("DUPLICATE_KEY", f"duplicate JSON key {k!r} in {label}")
            out[k] = v
        return out

    try:
        parsed = json.loads(
            text,
            parse_float=_reject_float,
            parse_constant=_reject_const,
            parse_int=_parse_bounded_int,
            object_pairs_hook=_no_dup_pairs,
        )
    except MinimaxCryptError:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise MinimaxCryptError("INVALID_JSON", f"malformed JSON in {label}: {exc}") from None

    verify_no_floats(parsed, label, allow_fraction=False)
    return parsed


def _read_bytes_strict(path, label):
    try:
        st = os.lstat(path)
    except OSError:
        raise MinimaxCryptError("FILE_MISSING", f"{label} not found: {path}") from None
    if stat.S_ISLNK(st.st_mode) or not stat.S_ISREG(st.st_mode):
        raise MinimaxCryptError("FILE_MISSING", f"{label} is not a regular file: {path}")
    try:
        with open(path, "rb") as fh:
            return fh.read()
    except OSError as exc:
        raise MinimaxCryptError("FILE_UNREADABLE", f"{label} unreadable: {exc}") from None


def _decode_utf8_strict(raw_bytes, label):
    try:
        return raw_bytes.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise MinimaxCryptError("INVALID_UTF8", f"{label} is not valid UTF-8: {exc}") from None


def _resolve_live_git_commit(research_dir, explicit_commit=None):
    """Read and validate .git/HEAD against UPSTREAM_COMMIT; refuse missing .git unless explicit_commit is given."""
    git_dir = os.path.join(research_dir, ".git")
    head_path = os.path.join(git_dir, "HEAD")
    if not os.path.isfile(head_path):
        if explicit_commit is None:
            raise MinimaxCryptError(
                "GIT_DIR_MISSING",
                "research_dir has no .git/HEAD; pass explicit upstream_commit to audit a non-git archive",
            )
        commit = require_hex_sha1(explicit_commit, "upstream_commit")
        if commit != UPSTREAM_COMMIT:
            raise MinimaxCryptError("COMMIT_MISMATCH", f"explicit upstream_commit {commit} != pinned {UPSTREAM_COMMIT}")
        return commit

    head_txt = _decode_utf8_strict(_read_bytes_strict(head_path, ".git/HEAD"), ".git/HEAD").strip()
    if head_txt.startswith("ref:"):
        ref_name = head_txt[4:].strip()
        if not ref_name or ref_name.startswith("/") or ".." in ref_name:
            raise MinimaxCryptError("UNSAFE_GIT_REF", f"invalid git ref {ref_name!r}")
        ref_path = os.path.join(git_dir, ref_name)
        if os.path.isfile(ref_path):
            commit = _decode_utf8_strict(_read_bytes_strict(ref_path, f".git/{ref_name}"), f".git/{ref_name}").strip()
        else:
            packed_path = os.path.join(git_dir, "packed-refs")
            commit = None
            if os.path.isfile(packed_path):
                packed_txt = _decode_utf8_strict(
                    _read_bytes_strict(packed_path, ".git/packed-refs"), ".git/packed-refs"
                )
                for line in packed_txt.splitlines():
                    s = line.strip()
                    if s.startswith(("#", "^")):
                        continue
                    parts = s.split()
                    if len(parts) == 2 and parts[1] == ref_name:
                        commit = parts[0]
                        break
            if commit is None:
                raise MinimaxCryptError("INVALID_COMMIT", f"unresolvable git ref {ref_name}")
    else:
        commit = head_txt

    commit = require_hex_sha1(commit, "git.HEAD")
    if commit != UPSTREAM_COMMIT:
        raise MinimaxCryptError("COMMIT_MISMATCH", f".git/HEAD {commit} != pinned {UPSTREAM_COMMIT}")
    if explicit_commit is not None:
        exp_c = require_hex_sha1(explicit_commit, "upstream_commit")
        if exp_c != commit:
            raise MinimaxCryptError("COMMIT_MISMATCH", f"explicit upstream_commit {exp_c} != .git/HEAD {commit}")
    return commit


def _validate_tii_challenges_live(challenges, ra_s, rb_s, fb_s):
    """Validate every challenge entry in verified_tii_94_summary.json and cross-check summary totals."""
    seen_secs = set()
    derived_ra = 0
    derived_rb = 0
    derived_fb = 0
    for idx, ch in enumerate(challenges):
        if type(ch) is not dict:
            raise MinimaxCryptError("INVALID_TII_CHALLENGE", f"challenges[{idx}] must be dict")
        sec = require_exact_int(ch.get("sec"), f"challenges[{idx}].sec", min_value=1)
        if sec in seen_secs:
            raise MinimaxCryptError("INVALID_TII_CHALLENGE", f"duplicate sec={sec}")
        seen_secs.add(sec)
        n_v = require_exact_int(ch.get("n"), f"challenges[{idx}].n", min_value=1)
        m_v = require_exact_int(ch.get("m"), f"challenges[{idx}].m", min_value=1)
        t_v = require_exact_int(ch.get("t"), f"challenges[{idx}].t", min_value=1)
        k_v = require_exact_int(ch.get("k"), f"challenges[{idx}].k", min_value=1)
        mt_v = require_exact_int(ch.get("mt"), f"challenges[{idx}].mt", min_value=1)
        if mt_v != m_v * t_v or k_v != n_v - mt_v:
            raise MinimaxCryptError("INVALID_TII_CHALLENGE", f"challenges[{idx}] dimension mismatch")
        chk_out = require_exact_int(ch.get("official_checker_output"), f"challenges[{idx}].official_checker_output")
        rref_ok = require_exact_bool(ch.get("rref_bit_identical"), f"challenges[{idx}].rref_bit_identical")
        irred_ok = require_exact_bool(ch.get("g_is_irreducible"), f"challenges[{idx}].g_is_irreducible")
        if chk_out != 1 or not rref_ok or not irred_ok:
            raise MinimaxCryptError("INVALID_TII_CHALLENGE", f"challenges[{idx}] failed verification flags")
        route = require_non_empty_str(ch.get("route"), f"challenges[{idx}].route")
        if route.startswith("Route-A"):
            derived_ra += 1
        elif route.startswith("Route-B"):
            derived_rb += 1
        else:
            raise MinimaxCryptError("INVALID_TII_CHALLENGE", f"challenges[{idx}] unexpected route {route}")
        if require_exact_bool(ch.get("first_blood"), f"challenges[{idx}].first_blood"):
            derived_fb += 1
    if derived_ra != ra_s or derived_rb != rb_s or derived_fb != fb_s:
        raise MinimaxCryptError("TII_SUM_MISMATCH", "challenge rows contradict summary totals")


def load_live_portal_summary(research_dir, upstream_commit=None):
    """Strictly read-only live inspection of a local MiniMax-AI/Research snapshot with pin enforcement."""
    if not os.path.isdir(research_dir):
        raise MinimaxCryptError("DIR_MISSING", f"research_dir not found: {research_dir}")
    live_commit = _resolve_live_git_commit(research_dir, explicit_commit=upstream_commit)
    crypto_dir = os.path.join(research_dir, "Cryptography")

    # 1. BentSum Lean 4 lexical purity + pinned SHA-256 enforcement
    lean_root = os.path.join(crypto_dir, "BentSum", "lean")
    lean_shas = {}
    banned_hits = 0
    for rel in REQUIRED_LEAN_FILES:
        raw = _read_bytes_strict(os.path.join(lean_root, rel), f"lean:{rel}")
        got_sha = hashlib.sha256(raw).hexdigest()
        exp_sha = PINNED_PORTAL_DIGESTS["lean_file_sha256"][rel]
        if got_sha != exp_sha:
            raise MinimaxCryptError("PIN_HASH_MISMATCH", f"lean:{rel} sha256 {got_sha} != pinned {exp_sha}")
        lean_shas[rel] = got_sha
        banned_hits += len(scan_lean4_lexical(_decode_utf8_strict(raw, f"lean:{rel}")))

    # 2. Blender SNF witness JSON + pinned SHA-256 enforcement + live 2-adic SNF
    snf_path = os.path.join(crypto_dir, "Blender", "artifacts", "snf_steering", "witnesses", "snf_audit_vectors.json")
    snf_bytes = _read_bytes_strict(snf_path, "snf_audit_vectors.json")
    snf_sha = hashlib.sha256(snf_bytes).hexdigest()
    if snf_sha != PINNED_PORTAL_DIGESTS["blender_snf_witness_sha256"]:
        raise MinimaxCryptError(
            "PIN_HASH_MISMATCH",
            f"snf_audit_vectors.json sha256 {snf_sha} != pinned {PINNED_PORTAL_DIGESTS['blender_snf_witness_sha256']}",
        )
    snf_data = _parse_strict_json_text(_decode_utf8_strict(snf_bytes, "snf_audit_vectors.json"), "snf_audit_vectors.json")
    if type(snf_data) is not dict:
        raise MinimaxCryptError("INVALID_JSON", "snf_audit_vectors.json root must be dict")
    unsh_vecs = snf_data.get("unshifted_eqlen_eqcsum")
    sh_vecs = snf_data.get("shifted_multi_eqlen_eqcsum")
    if (
        type(unsh_vecs) is not list
        or not unsh_vecs
        or type(sh_vecs) is not list
        or len(sh_vecs) < 2
    ):
        raise MinimaxCryptError("INVALID_BLENDER_WITNESS", "missing SNF vector lists")
    unsh_exps = snf_2adic_valuations_exact(unsh_vecs, 32)
    sh_exps = snf_2adic_valuations_exact(sh_vecs, 32)
    if len(unsh_exps) != 8 or len(sh_exps) != 8:
        raise MinimaxCryptError("INVALID_BLENDER_WITNESS", "SNF vectors must have width 8")
    m32 = 0xFFFFFFFF
    s_base = (0x12345678, 0x9ABCDEF0, 0x13579BDF, 0x2468ACE0, 0xCAFEBABE, 0xDEADBEEF, 0x0F1E2D3C, 0x4B5A6978)
    ntests = min(len(sh_vecs) - 1, 100)
    f2_fail = 0
    mod_pass = 0
    for idx in range(ntests):
        v1 = sh_vecs[idx]
        v2 = sh_vecs[idx + 1]
        y10 = [(s + a) & m32 for s, a in zip(s_base, v1)]
        y01 = [(s + b) & m32 for s, b in zip(s_base, v2)]
        y11 = [(s + a + b) & m32 for s, a, b in zip(s_base, v1, v2)]
        if any((a ^ b ^ c ^ d) != 0 for a, b, c, d in zip(s_base, y10, y01, y11)):
            f2_fail += 1
        if all(((a - b - c + d) & m32) == 0 for a, b, c, d in zip(s_base, y10, y01, y11)):
            mod_pass += 1

    # 3. Blender paper/main.tex checks for open Issues #1 and #2
    btex_path = os.path.join(crypto_dir, "Blender", "paper", "main.tex")
    btex = _decode_utf8_strict(_read_bytes_strict(btex_path, "Blender/paper/main.tex"), "Blender/paper/main.tex")
    issue1_hit = "global minimum" in btex and "two-step silent-carry healing family" in btex
    issue2_hit = "steer $W_0, W_2, W_4, W_6 \\in \\{x, \\neg x\\}$" in btex

    # 4. TII-McEliece 94-challenge campaign summary + pinned SHA-256 enforcement
    tii_path = os.path.join(
        crypto_dir, "TII-McEliece", "artifacts", "goppa_key_recovery", "witnesses", "verified_tii_94_summary.json"
    )
    tii_bytes = _read_bytes_strict(tii_path, "verified_tii_94_summary.json")
    tii_sha = hashlib.sha256(tii_bytes).hexdigest()
    if tii_sha != PINNED_PORTAL_DIGESTS["tii_94_summary_sha256"]:
        raise MinimaxCryptError(
            "PIN_HASH_MISMATCH",
            f"verified_tii_94_summary.json sha256 {tii_sha} != pinned {PINNED_PORTAL_DIGESTS['tii_94_summary_sha256']}",
        )
    tii_data = _parse_strict_json_text(
        _decode_utf8_strict(tii_bytes, "verified_tii_94_summary.json"), "verified_tii_94_summary.json"
    )
    if type(tii_data) is not dict:
        raise MinimaxCryptError("INVALID_JSON", "verified_tii_94_summary.json root must be dict")
    challenges = tii_data.get("challenges")
    if type(challenges) is not list or not challenges:
        raise MinimaxCryptError("INVALID_TII_SUMMARY", "challenges must be non-empty list")
    tot_s = require_exact_int(tii_data.get("total_solved"), "tii.total_solved", min_value=1)
    ra_s = require_exact_int(tii_data.get("route_a_solved"), "tii.route_a_solved", min_value=0, max_value=tot_s)
    rb_s = require_exact_int(tii_data.get("route_b_solved"), "tii.route_b_solved", min_value=0, max_value=tot_s)
    fb_s = require_exact_int(tii_data.get("first_bloods"), "tii.first_bloods", min_value=0, max_value=tot_s)
    _validate_tii_challenges_live(challenges, ra_s, rb_s, fb_s)
    if ra_s + rb_s != tot_s:
        raise MinimaxCryptError("TII_SUM_MISMATCH", "route_a_solved + route_b_solved != total_solved")

    return {
        "diag_source": "live_portal_read",
        "upstream_commit": live_commit,
        "bentsum_lean": {
            "files_checked": len(lean_shas),
            "banned_construct_findings": banned_hits,
            "lean_file_sha256": lean_shas,
        },
        "blender_snf_witness": {
            "witness_sha256": snf_sha,
            "unshifted_count": len(unsh_vecs),
            "shifted_multi_count": len(sh_vecs),
            "unshifted_snf_exps": unsh_exps,
            "shifted_multi_snf_exps": sh_exps,
            "f2_xor_fail_count": f2_fail,
            "mod32_superposition_pass_count": mod_pass,
        },
        "blender_issues_text_checks": {
            "issue1_global_minimum_claim_present": issue1_hit,
            "issue2_sec33_w0246_in_x_notx_present": issue2_hit,
        },
        "tii_94_summary": {
            "summary_sha256": tii_sha,
            "total_solved": tot_s,
            "route_a_solved": ra_s,
            "route_b_solved": rb_s,
            "first_bloods": fb_s,
        },
    }


def certify_from_summary(mode, live_portal_inspected, summary):
    p1 = audit_bentsum_walsh_exact()
    p2 = audit_fast_algebraic_and_blender_exact()
    p3 = audit_background_goppa_and_hawk_identities_exact()
    axes = {
        "bentsum_walsh_hadamard_and_anf": p1["passed"],
        "fast_algebraic_and_blender_computed": p2["passed"],
        "background_goppa_and_hawk_identities": p3["passed"],
    }
    return certify_minimax_cryptanalysis_audit_exact(
        mode=mode,
        live_portal_inspected=live_portal_inspected,
        operator_labels=OPERATOR_LABELS,
        portal_summary_raw=summary,
        pillar1_result=p1,
        pillar2_result=p2,
        pillar3_result=p3,
        three_axis_checks=axes,
    )


def run_audit(live=False, research_dir=None, upstream_commit=None):
    if not live and research_dir is None:
        return certify_from_summary("standalone_pinned_replay", False, STANDALONE_PORTAL_FIXTURE)
    if research_dir is None:
        raise MinimaxCryptError("PATH_REQUIRED", "--live requires --research-dir <path>")
    summary = load_live_portal_summary(research_dir, upstream_commit=upstream_commit)
    return certify_from_summary("live_portal_audit", True, summary)


def verify_certificate_bytes(raw_bytes, research_dir=None, upstream_commit=None):
    """Strictly verify a canonical JSON certificate by parsing strictly and re-deriving all pillars."""
    if not isinstance(raw_bytes, bytes):
        raise MinimaxCryptError("INVALID_BYTES", "certificate input must be bytes")
    if b"\r" in raw_bytes:
        raise MinimaxCryptError("CRLF_FORBIDDEN", "certificate must use LF line endings (no CR/CRLF)")
    text = _decode_utf8_strict(raw_bytes, "certificate")
    body_text = text[:-1] if text.endswith("\n") else text

    parsed = _parse_strict_json_text(body_text, "certificate")
    if type(parsed) is not dict:
        raise MinimaxCryptError("INVALID_CERTIFICATE", "certificate root must be JSON object")
    if body_text.encode("utf-8") != canonical_json_bytes(parsed):
        raise MinimaxCryptError("NON_CANONICAL_JSON", "certificate bytes are not canonical JSON")

    saved_sha = require_hex_sha256(parsed.get("certificate_sha256"), "certificate_sha256")
    mode = require_non_empty_str(parsed.get("mode"), "mode")
    if mode not in ("standalone_pinned_replay", "live_portal_audit"):
        raise MinimaxCryptError("INVALID_MODE", f"unsupported mode {mode}")
    live_flag = require_exact_bool(parsed.get("live_portal_inspected"), "live_portal_inspected")
    if live_flag != (mode == "live_portal_audit"):
        raise MinimaxCryptError("MODE_MISMATCH", "live_portal_inspected contradicts mode")
    commit = require_hex_sha1(parsed.get("upstream_commit"), "upstream_commit")
    if commit != UPSTREAM_COMMIT:
        raise MinimaxCryptError("COMMIT_MISMATCH", f"upstream_commit {commit} != pinned {UPSTREAM_COMMIT}")
    all_passed = require_exact_bool(parsed.get("all_gates_passed"), "all_gates_passed")
    verdict = require_non_empty_str(parsed.get("verdict"), "verdict")
    if not all_passed:
        raise MinimaxCryptError("GATE_FAILED", "certificate all_gates_passed is False")
    if verdict != "AUDITED_MINIMAX_CRYPTANALYSIS_PORTAL":
        raise MinimaxCryptError("INVALID_VERDICT", f"unexpected verdict {verdict}")

    body_no_hash = {k: v for k, v in parsed.items() if k != "certificate_sha256"}
    recomputed_sha = canonical_sha256(body_no_hash)
    if recomputed_sha != saved_sha:
        raise MinimaxCryptError("HASH_MISMATCH", f"certificate_sha256 {saved_sha} != recomputed {recomputed_sha}")

    if mode == "live_portal_audit":
        if research_dir is None:
            raise MinimaxCryptError(
                "LIVE_DIR_REQUIRED",
                "verifying a live_portal_audit certificate requires --research-dir <path>",
            )
        expected = run_audit(live=True, research_dir=research_dir, upstream_commit=upstream_commit)
    else:
        if research_dir is not None:
            raise MinimaxCryptError(
                "MODE_MISMATCH",
                "standalone_pinned_replay certificate cannot be verified with --research-dir",
            )
        expected = run_audit(live=False, research_dir=None)

    if not _strict_equal(parsed, expected):
        raise MinimaxCryptError("CERTIFICATE_MISMATCH", "certificate payload contradicts oracle re-derivation")

    return {
        "verified": True,
        "mode": mode,
        "live_portal_inspected": live_flag,
        "upstream_commit": commit,
        "certificate_sha256": saved_sha,
        "file_sha256": hashlib.sha256(raw_bytes).hexdigest(),
    }


def verify_certificate_file(path, research_dir=None, upstream_commit=None):
    """Open certificate strictly (no newline translation) and run full re-derivation verification."""
    raw = _read_bytes_strict(path, "certificate")
    return verify_certificate_bytes(raw, research_dir=research_dir, upstream_commit=upstream_commit)


def main(argv=None):
    parser = argparse.ArgumentParser(description="MiniMax-AI/Research Cryptanalysis Clean-Room Audit")
    parser.add_argument("--standalone", action="store_true", help="Offline pinned replay (default)")
    parser.add_argument("--live", action="store_true", help="Live read-only audit against MiniMax-AI/Research snapshot")
    parser.add_argument("--research-dir", default=None, help="Path to local MiniMax-AI/Research checkout")
    parser.add_argument("--upstream-commit", default=None, help="Explicit 40-hex upstream commit for non-git archive")
    parser.add_argument("--verify", default=None, metavar="FILE", help="Strictly verify a canonical JSON certificate")
    parser.add_argument("--json", action="store_true", help="Emit canonical JSON to stdout (default output format)")
    parser.add_argument("--output", default=None, help="Optional path to write canonical JSON certificate")
    args = parser.parse_args(argv)

    if args.verify is not None:
        try:
            receipt = verify_certificate_file(
                args.verify,
                research_dir=args.research_dir,
                upstream_commit=args.upstream_commit,
            )
        except MinimaxCryptError as exc:
            sys.stderr.write(f"VERIFY_FAILED {exc.code}: {exc.detail}\n")
            return 1
        sys.stdout.write(canonical_json_bytes(receipt).decode("utf-8") + "\n")
        return 0

    use_live = args.live or (args.research_dir is not None)
    try:
        cert = run_audit(live=use_live, research_dir=args.research_dir, upstream_commit=args.upstream_commit)
    except MinimaxCryptError as exc:
        sys.stderr.write(f"AUDIT_FAILED {exc.code}: {exc.detail}\n")
        return 2
    raw = canonical_json_bytes(cert)
    if args.output:
        with open(args.output, "wb") as fh:
            fh.write(raw)
            fh.write(b"\n")
    sys.stdout.write(raw.decode("utf-8") + "\n")
    return 0 if cert["all_gates_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
