"""Dual-mode (live_portal_audit + standalone_pinned_replay) audit runner for
Track S14 (AUDIT-109): MiniMax-AI/Research Cryptography Portal Clean-Room Audit.

Pure Python 3 stdlib. Zero floats. Zero bare assert statements. Zero subprocess calls.
"""

import argparse
import hashlib
import json
import os
import re
import sys

_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
if _SCRIPT_DIR not in sys.path:
    sys.path.insert(0, _SCRIPT_DIR)

from minimax_cryptanalysis_oracle import (
    MinimaxCryptError,
    REQUIRED_LEAN_FILES,
    UPSTREAM_COMMIT,
    audit_bentsum_lean_and_walsh_exact,
    audit_fast_algebraic_and_errata_exact,
    audit_law5_math0_siliquant_operators_exact,
    canonical_json_bytes,
    certify_minimax_cryptanalysis_audit_exact,
    require_exact_bool,
    require_exact_int,
    require_hex_sha1,
    require_non_empty_str,
    snf_2adic_valuations_exact,
)


OPERATOR_LABELS = (
    "bentsum_walsh_hadamard_weight_congruence_and_lean4_purity",
    "aradi_orthogonal_island_collapse_and_blind_column_audit",
    "colm_gf2_128_fade_transplant_and_tau_obstruction",
    "sbcvole_gf2_257_single_signature_linear_key_recovery",
    "blender256_parity_obstruction_errata_and_2adic_snf_steering",
    "tii_mceliece_goppa_primal_shortening_quadratic_compression",
    "hawk_parity_sublattice_index_and_unimodular_gram_preconditioning",
)

# Pinned from MiniMax-AI/Research @ 57842cef92e84eaf8e2535b12f48ba5586080ddd
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

_LEAN_BANNED_RE = re.compile(r"\b(sorry|sorryAx|axiom|native_decide|unsafe|implemented_by|admit)\b")


def _is_lean_ident_char(ch):
    return ch.isalnum() or ch == "_"


def _strip_lean_comments(text):
    """Remove Lean comments (-- ..., nested /- ... -/) while respecting string & char literals."""
    out = []
    i = 0
    n = len(text)
    depth = 0
    while i < n:
        if depth == 0:
            if text[i : i + 2] == "--":
                nl = text.find("\n", i)
                if nl == -1:
                    break
                out.append("\n")
                i = nl + 1
            elif text[i : i + 2] == "/-":
                depth = 1
                i += 2
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
            else:
                out.append(text[i])
                i += 1
        else:
            if text[i : i + 2] == "/-":
                depth += 1
                i += 2
            elif text[i : i + 2] == "-/":
                depth -= 1
                i += 2
            else:
                i += 1
    return "".join(out)


def _read_bytes_strict(path, label):
    if not os.path.isfile(path):
        raise MinimaxCryptError("FILE_MISSING", f"{label} not found: {path}")
    with open(path, "rb") as fh:
        return fh.read()


def _resolve_live_git_commit(research_dir):
    """Read and validate .git/HEAD when present (rejecting malformed refs or commit drift)."""
    git_dir = os.path.join(research_dir, ".git")
    head_path = os.path.join(git_dir, "HEAD")
    if not os.path.isfile(head_path):
        return UPSTREAM_COMMIT
    head_txt = _read_bytes_strict(head_path, ".git/HEAD").decode("utf-8").strip()
    if head_txt.startswith("ref:"):
        ref_name = head_txt[4:].strip()
        if not ref_name or ref_name.startswith("/") or ".." in ref_name:
            raise MinimaxCryptError("UNSAFE_GIT_REF", f"invalid git ref {ref_name!r}")
        ref_path = os.path.join(git_dir, ref_name)
        if os.path.isfile(ref_path):
            commit = _read_bytes_strict(ref_path, f".git/{ref_name}").decode("utf-8").strip()
        else:
            packed_path = os.path.join(git_dir, "packed-refs")
            commit = None
            if os.path.isfile(packed_path):
                for line in _read_bytes_strict(packed_path, ".git/packed-refs").decode("utf-8").splitlines():
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
    return commit


def _validate_tii_challenges_live(challenges, ra_s, rb_s, fb_s):
    """Validate every challenge entry in verified_tii_94_summary.json and cross-check summary totals."""
    seen_secs = set()
    derived_ra = 0
    derived_rb = 0
    derived_fb = 0
    for idx, ch in enumerate(challenges):
        if not isinstance(ch, dict):
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


def load_live_portal_summary(research_dir):
    """Strictly read-only live inspection of a local MiniMax-AI/Research snapshot."""
    if not os.path.isdir(research_dir):
        raise MinimaxCryptError("DIR_MISSING", f"research_dir not found: {research_dir}")
    live_commit = _resolve_live_git_commit(research_dir)
    crypto_dir = os.path.join(research_dir, "Cryptography")

    # 1. BentSum Lean 4 purity + exact file hashes
    lean_root = os.path.join(crypto_dir, "BentSum", "lean")
    lean_shas = {}
    banned_hits = 0
    for rel in REQUIRED_LEAN_FILES:
        raw = _read_bytes_strict(os.path.join(lean_root, rel), f"lean:{rel}")
        lean_shas[rel] = hashlib.sha256(raw).hexdigest()
        stripped = _strip_lean_comments(raw.decode("utf-8"))
        banned_hits += len(_LEAN_BANNED_RE.findall(stripped))

    # 2. Blender SNF witness JSON + live 2-adic SNF & GF(2) vs (Z/2^32Z)^8 test
    snf_path = os.path.join(crypto_dir, "Blender", "artifacts", "snf_steering", "witnesses", "snf_audit_vectors.json")
    snf_bytes = _read_bytes_strict(snf_path, "snf_audit_vectors.json")
    snf_data = json.loads(snf_bytes.decode("utf-8"))
    if not isinstance(snf_data, dict):
        raise MinimaxCryptError("INVALID_JSON", "snf_audit_vectors.json root must be dict")
    unsh_vecs = snf_data.get("unshifted_eqlen_eqcsum")
    sh_vecs = snf_data.get("shifted_multi_eqlen_eqcsum")
    if (
        not isinstance(unsh_vecs, list)
        or not unsh_vecs
        or not isinstance(sh_vecs, list)
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
    btex = _read_bytes_strict(btex_path, "Blender/paper/main.tex").decode("utf-8")
    issue1_hit = "global minimum" in btex and "two-step silent-carry healing family" in btex
    issue2_hit = "steer $W_0, W_2, W_4, W_6 \\in \\{x, \\neg x\\}$" in btex

    # 4. TII-McEliece 94-challenge campaign summary
    tii_path = os.path.join(crypto_dir, "TII-McEliece", "artifacts", "goppa_key_recovery", "witnesses", "verified_tii_94_summary.json")
    tii_bytes = _read_bytes_strict(tii_path, "verified_tii_94_summary.json")
    tii_data = json.loads(tii_bytes.decode("utf-8"))
    if not isinstance(tii_data, dict):
        raise MinimaxCryptError("INVALID_JSON", "verified_tii_94_summary.json root must be dict")
    challenges = tii_data.get("challenges")
    if not isinstance(challenges, list) or not challenges:
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
            "witness_sha256": hashlib.sha256(snf_bytes).hexdigest(),
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
            "summary_sha256": hashlib.sha256(tii_bytes).hexdigest(),
            "total_solved": tot_s,
            "route_a_solved": ra_s,
            "route_b_solved": rb_s,
            "first_bloods": fb_s,
        },
    }


def certify_from_summary(mode, live_portal_inspected, summary):
    p1 = audit_bentsum_lean_and_walsh_exact(summary)
    p2 = audit_fast_algebraic_and_errata_exact(summary)
    p3 = audit_law5_math0_siliquant_operators_exact(summary)
    axes = {
        "bentsum_lean_purity_and_walsh_hadamard": p1["passed"],
        "fast_algebraic_operators_and_peer_errata": p2["passed"],
        "law5_tii_mceliece_and_hawk_lattice_operators": p3["passed"],
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


def run_audit(live=False, research_dir=None):
    if not live and research_dir is None:
        return certify_from_summary("standalone_pinned_replay", False, STANDALONE_PORTAL_FIXTURE)
    if research_dir is None:
        raise MinimaxCryptError("PATH_REQUIRED", "--live requires --research-dir <path>")
    summary = load_live_portal_summary(research_dir)
    return certify_from_summary("live_portal_audit", True, summary)


def main(argv=None):
    parser = argparse.ArgumentParser(description="Track S14 (AUDIT-109) MiniMax-AI/Research Cryptanalysis Audit")
    parser.add_argument("--standalone", action="store_true", help="Offline pinned replay (default)")
    parser.add_argument("--live", action="store_true", help="Live read-only audit against MiniMax-AI/Research snapshot")
    parser.add_argument("--research-dir", default=None, help="Path to local MiniMax-AI/Research checkout (implies live)")
    parser.add_argument("--json", action="store_true", help="Emit canonical JSON to stdout (default output format)")
    parser.add_argument("--output", default=None, help="Optional path to write canonical JSON certificate")
    args = parser.parse_args(argv)

    use_live = args.live or (args.research_dir is not None)
    cert = run_audit(live=use_live, research_dir=args.research_dir)
    raw = canonical_json_bytes(cert)
    if args.output:
        with open(args.output, "wb") as fh:
            fh.write(raw)
            fh.write(b"\n")
    sys.stdout.write(raw.decode("utf-8") + "\n")
    return 0 if cert["all_gates_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
