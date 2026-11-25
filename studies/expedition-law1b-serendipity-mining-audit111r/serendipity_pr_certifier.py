#!/usr/bin/env python3
"""
Clean-Room Zero-Float Certifier for Track S12: Law-1b Unmerged-PR Serendipity Mining.

Pure Python 3 stdlib (`int`, `fractions.Fraction`). Zero floats. Zero bare asserts.
Modes:
  - Default / `--standalone`: Deterministic offline verification over embedded exact witnesses
    and pinned snapshot digests (suitable for air-gapped Zone-B snapshots without intake root).
  - `--live --intake-root <dir>`: Re-hashes and verifies every frozen intake JSON file on disk
    (`intake_summary.json`, all 8 `*_prs.json`, `Moissanite-Labs__heedle_issues.json`, and
    `deep_diffs/DEEP_MINING_MANIFEST.json` + all 40 deep-diff PR JSONs) alongside M1..M6.
  - `--check <cert.json>`: Strict JSON duplicate-key/float-free structural verification of a
    saved certificate file.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from typing import Any

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import serendipity_pr_oracle as spo


# Frozen 8-repo intake digests from read-only GitHub snapshot (2026-11-22)
PINNED_REPO_SNAPSHOTS: list[dict[str, Any]] = [
    {
        "repo": "Foundation-0/math0",
        "fetched": 20,
        "open": 10,
        "closed_unmerged": 1,
        "merged": 9,
        "prs_json_sha256": "976d6c50aac13b6e2ff24d40a0e9be9042f1e9a60ee44fbbd00e796f73c7deee",
    },
    {
        "repo": "Moissanite-Labs/exo",
        "fetched": 500,
        "open": 213,
        "closed_unmerged": 20,
        "merged": 267,
        "prs_json_sha256": "667e67a210341f35d3c1011a833ee9ec4ba05979ccaa34078436fc78c6767240",
    },
    {
        "repo": "Moissanite-Labs/heedle",
        "fetched": 4,
        "open": 1,
        "closed_unmerged": 0,
        "merged": 3,
        "prs_json_sha256": "6056665aa73cc933fd3b75893c03cb040fdbae0e126d0e6b2acf063e0656c7d7",
    },
    {
        "repo": "Moissanite-Labs/siliquant",
        "fetched": 17,
        "open": 5,
        "closed_unmerged": 3,
        "merged": 9,
        "prs_json_sha256": "3e3c0f1e04abd5485097be64e4efb53eada2d97c79e0bbec0adf676f9146bbee",
    },
    {
        "repo": "Moissanite-Labs/weft-loom",
        "fetched": 31,
        "open": 9,
        "closed_unmerged": 0,
        "merged": 22,
        "prs_json_sha256": "4f04a6e3f8c98c2158de0e48d02aa58ce710c33a6cdaf569591a1e002390bd55",
    },
    {
        "repo": "NandhaKishorM/laya",
        "fetched": 800,
        "open": 52,
        "closed_unmerged": 56,
        "merged": 692,
        "prs_json_sha256": "d52729dcd73e4d87f75881ce45974001c115497cf28f6ea42b6ae35a064beeb2",
    },
    {
        "repo": "NandhaKishorM/vegaml",
        "fetched": 61,
        "open": 6,
        "closed_unmerged": 8,
        "merged": 47,
        "prs_json_sha256": "3fca3f41b058d0601a77e36a8b3e9d94f7ac0a82ce4b5a8291ca32187faa53f9",
    },
    {
        "repo": "chuanqisun/spaceship",
        "fetched": 4,
        "open": 0,
        "closed_unmerged": 3,
        "merged": 1,
        "prs_json_sha256": "60ec0ef10a46db698db6570d2b17f0d20f2fe01d8ef7835665fcc00ddf1f05b1",
    },
]

# Canonical 24 pinned mined unmerged PR records across all 8 portals (12 open + 12 closed_unmerged;
# 11 EXECUTED_EXACT_WITNESS + 13 CATALOGED_LEAD; all 9 mechanism classes; honest novelty N0).
CANONICAL_MINED_ENTRIES: list[dict[str, Any]] = [
    {
        "repo": "NandhaKishorM/laya",
        "number": 1465,
        "status": "open",
        "head_sha": "a0de02125ea73f2270f89ff5e142c9b65f3075dc",
        "snapshot_sha256": "5ff56e7dc06533e00140b5a8c1b495f0fcaa68704d12cd503aafe9cf45af9f0e",
        "mechanism_class": "DENOMINATOR_OR_WEIGHT_BIAS",
        "evidence_standing": "EXECUTED_EXACT_WITNESS",
        "operator_id": "M1_MICROBATCH_WEIGHTING",
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Micro-batch item-count weighted loss accumulation eliminates CS-10 uneven-window bias",
    },
    {
        "repo": "NandhaKishorM/laya",
        "number": 698,
        "status": "closed_unmerged",
        "head_sha": "b2209594cab792bf0a0e108dee366ededeaf3d7d",
        "snapshot_sha256": "f740f90f2ffa10ab78dfb133b920ddf67ef5fbaf0242c442e322da8ea2ba4d28",
        "mechanism_class": "QUANTILE_OR_INDEX_BOUNDARY",
        "evidence_standing": "EXECUTED_EXACT_WITNESS",
        "operator_id": "M2_NEAREST_RANK_QUANTILE",
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Exact nearest-rank p95 ceil(19n/20)-1 fixes +1 overshoot on every multiple of 20",
    },
    {
        "repo": "NandhaKishorM/laya",
        "number": 693,
        "status": "closed_unmerged",
        "head_sha": "db63c8627cc811b40a3967a7af22e5a631f62946",
        "snapshot_sha256": "9a9084a0d03c098dfd014486ad5054384fb3b17732e452a59a7a16e0a5f794e8",
        "mechanism_class": "AFFINE_OR_RANGE_PROJECTION",
        "evidence_standing": "EXECUTED_EXACT_WITNESS",
        "operator_id": "M3_AFFINE_SCORE_PROJECTION",
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Bare score projection preserves non-zero minimum offset instead of self-cancelling",
    },
    {
        "repo": "NandhaKishorM/laya",
        "number": 683,
        "status": "closed_unmerged",
        "head_sha": "b9923438bdda188f7f4ee56282c383584a8de5d8",
        "snapshot_sha256": "d37be3796614e4ac4389d53830b71feadaebb4cd8d65a95a25b4b34d9e14244e",
        "mechanism_class": "AFFINE_OR_RANGE_PROJECTION",
        "evidence_standing": "EXECUTED_EXACT_WITNESS",
        "operator_id": "M3_AFFINE_SCORE_PROJECTION",
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Independent closed-unmerged confirmation of minimum-offset preservation on bare score",
    },
    {
        "repo": "NandhaKishorM/vegaml",
        "number": 57,
        "status": "open",
        "head_sha": "a7d5ccba0e28dfe083d636de8c84a8feb8a6cabd",
        "snapshot_sha256": "fd9f71e81a31fda2c33ba6735259b3091c51e7c783ec93ab8abfd02bbcdb5583",
        "mechanism_class": "ALGEBRAIC_KERNEL_EQUIVALENCE",
        "evidence_standing": "EXECUTED_EXACT_WITNESS",
        "operator_id": "M4_SPAN_POOLING_EQUIVALENCE",
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Direct contiguous span pooling equals scatter-add/bincount with 0 Q-residual and clears _cap",
    },
    {
        "repo": "Moissanite-Labs/exo",
        "number": 490,
        "status": "closed_unmerged",
        "head_sha": "ed43f23f3418238c4819eb08c203c40e4a1fba25",
        "snapshot_sha256": "ee557e63680ec04d5e50f2633da679d19b632472f247bb5334abadf7a44de890",
        "mechanism_class": "LEXER_OR_PARSER_SECURITY_BYPASS",
        "evidence_standing": "EXECUTED_EXACT_WITNESS",
        "operator_id": "M5_BACKTICK_LINE_CONTINUATION",
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Bash drops odd backslash-newline inside backticks before command lexing",
    },
    {
        "repo": "Moissanite-Labs/exo",
        "number": 911,
        "status": "open",
        "head_sha": "518b1706df69f5f098574cfd2889a768ce07a709",
        "snapshot_sha256": "a2e5cd5f9698ae34b48c64ceaaa36c05517deef8ac355323c717fe9dac55976a",
        "mechanism_class": "LEXER_OR_PARSER_SECURITY_BYPASS",
        "evidence_standing": "EXECUTED_EXACT_WITNESS",
        "operator_id": "M5_HEREDOC_TERMINATOR",
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Unquoted heredoc terminator joins odd backslash-newlines; <<- strips tabs on joined line only",
    },
    {
        "repo": "Moissanite-Labs/exo",
        "number": 1136,
        "status": "open",
        "head_sha": "f0df8ef7a9b880675a518a7188983a96eaad10b6",
        "snapshot_sha256": "c9c221c326ad470ca1d4b9dfdcc85e0d2f52e7acd87dea86a744767c1e9c5f25",
        "mechanism_class": "LEXER_OR_PARSER_SECURITY_BYPASS",
        "evidence_standing": "EXECUTED_EXACT_WITNESS",
        "operator_id": "M5_XARGS_GETOPT_COMMAND",
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "GNU/BSD xargs getopt parsing prevents option values masking invoked command",
    },
    {
        "repo": "Moissanite-Labs/exo",
        "number": 402,
        "status": "closed_unmerged",
        "head_sha": "ecaa3eccd7f1a5497cc9be5595c4f4899885eb38",
        "snapshot_sha256": "392f3b64f0caeed4cc88b323e12b9974f1b52fad88cce7768c614ed22cdf4965",
        "mechanism_class": "LEXER_OR_PARSER_SECURITY_BYPASS",
        "evidence_standing": "EXECUTED_EXACT_WITNESS",
        "operator_id": "M5_GH_TARGET_REPO",
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "gh target resolved from -R/operands only, never option values such as --body/--duplicate-of",
    },
    {
        "repo": "Moissanite-Labs/exo",
        "number": 428,
        "status": "closed_unmerged",
        "head_sha": "c8a89531c4ab1b73987da68d9a8d8663996150cb",
        "snapshot_sha256": "5100b085b572c55c53f3e204f1181711d5424ce4b060f0790986be950ecaec60",
        "mechanism_class": "CRYPTO_PIN_OR_STATE_MACHINE",
        "evidence_standing": "EXECUTED_EXACT_WITNESS",
        "operator_id": "M5_PINNED_PEER_ENVELOPE",
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Peer envelope verified strictly against seat pinned key, never mutable presence file",
    },
    {
        "repo": "Moissanite-Labs/exo",
        "number": 1192,
        "status": "open",
        "head_sha": "2817df6ea27e6b1f376892bc4e489891f7f65aed",
        "snapshot_sha256": "719457d3d3162ec4365c21d4067522f21fc5da96f5f26523a12aa7e678267a0e",
        "mechanism_class": "CRYPTO_PIN_OR_STATE_MACHINE",
        "evidence_standing": "EXECUTED_EXACT_WITNESS",
        "operator_id": "M5_WAKE_BUDGET_FSM",
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Wake-budget FSM renewed only on principal turn; peer/bus/job/stop cannot reset cap",
    },
    {
        "repo": "NandhaKishorM/laya",
        "number": 1411,
        "status": "closed_unmerged",
        "head_sha": "bbb53b26c52e2664e06206a275a92a95e1421d79",
        "snapshot_sha256": "584c23ede3fd66556032a999847c8a99b8ad96d668468d365e74205e4efeba04",
        "mechanism_class": "QUANTILE_OR_INDEX_BOUNDARY",
        "evidence_standing": "CATALOGED_LEAD",
        "operator_id": None,
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "10**400 JSON integer temperature raises OverflowError in float() unless caught fail-closed",
    },
    {
        "repo": "NandhaKishorM/laya",
        "number": 925,
        "status": "closed_unmerged",
        "head_sha": "1db7c88d65f8b05149bf72bd9127c38ff318ca21",
        "snapshot_sha256": "deb28af25587e187ce747ca27453e2a0a16bbed12b795f15b174c91943478076",
        "mechanism_class": "CRYPTO_PIN_OR_STATE_MACHINE",
        "evidence_standing": "CATALOGED_LEAD",
        "operator_id": None,
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "apply_confidence_gate leaves stale low_confidence flag on re-gate unless cleared per call",
    },
    {
        "repo": "NandhaKishorM/laya",
        "number": 783,
        "status": "closed_unmerged",
        "head_sha": "51ee966e364a2ff6f302fa6008209316f0be421c",
        "snapshot_sha256": "1a4659d11755be4ffa49626b537261881a9d41b6dae5a3ee265dbdabdba24438",
        "mechanism_class": "AFFINE_OR_RANGE_PROJECTION",
        "evidence_standing": "CATALOGED_LEAD",
        "operator_id": None,
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Canonical sorting of unordered choice criteria restores Gate-2 permutation invariance",
    },
    {
        "repo": "NandhaKishorM/laya",
        "number": 1210,
        "status": "open",
        "head_sha": "74a2253c2e8c2a325ab1b8461bb0d595e5476d58",
        "snapshot_sha256": "74ce147bb1899f063d89fa3e2a9f72546aa984e5d0d652bab64d90e83af4f000",
        "mechanism_class": "EMPIRICAL_REFUTATION_OR_FREEZE",
        "evidence_standing": "CATALOGED_LEAD",
        "operator_id": None,
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Three-seed panel refutes single-seed 1.85pt soft-CE lead over rlcd (0.7763 vs 0.7762)",
    },
    {
        "repo": "NandhaKishorM/laya",
        "number": 1524,
        "status": "open",
        "head_sha": "1d9aaae8b352e58a41baf6b7cb50344c6fb26cf5",
        "snapshot_sha256": "360fae5dd77dc678a0db567ad318206b2213fd1496e0ee4c7c3fb6a67ccad5a2",
        "mechanism_class": "CRYPTO_PIN_OR_STATE_MACHINE",
        "evidence_standing": "CATALOGED_LEAD",
        "operator_id": None,
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Fused ONNX export verifier must receive selected checkpoint instead of cached English weights",
    },
    {
        "repo": "NandhaKishorM/vegaml",
        "number": 40,
        "status": "open",
        "head_sha": "aa1ad172d8b28745230e3054854dd9e07399deae",
        "snapshot_sha256": "7d06f15c057ac884469b62a57c46895aa72dbb0a2afc41014fea3eaeb7c4c9bc",
        "mechanism_class": "EXACT_CERTIFIER_OR_DOMAIN_TOOL",
        "evidence_standing": "CATALOGED_LEAD",
        "operator_id": None,
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Standalone inference-only Rust port of VegaML runtime (2,367 LOC)",
    },
    {
        "repo": "chuanqisun/spaceship",
        "number": 5,
        "status": "closed_unmerged",
        "head_sha": "7633dbee79799944d757e6d6993607174bee88fe",
        "snapshot_sha256": "12b1a9ba78d930d1c566c958d7a190156e8562234a8fe037b401609d5c826a15",
        "mechanism_class": "INTERNAL_STEERING_OR_ARCHITECTURE",
        "evidence_standing": "CATALOGED_LEAD",
        "operator_id": None,
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "In-browser WebGPU hidden-state steering and attention-box biasing with unsteered replay",
    },
    {
        "repo": "chuanqisun/spaceship",
        "number": 3,
        "status": "closed_unmerged",
        "head_sha": "6521fc710147478be20a44b5400e256e34ec3a4b",
        "snapshot_sha256": "9f6f8c80442f4c4e409a7ed1a73119303a834ccdf0916e89fa93a5ef910be960",
        "mechanism_class": "INTERNAL_STEERING_OR_ARCHITECTURE",
        "evidence_standing": "CATALOGED_LEAD",
        "operator_id": None,
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Four-pane parallel model comparison arena (spec-003) over shared opening prompt",
    },
    {
        "repo": "Moissanite-Labs/heedle",
        "number": 8,
        "status": "open",
        "head_sha": "7de102ecf56ba99e277f7c9d021c2e66eab55e8c",
        "snapshot_sha256": "a99b8648485b15c6b2e46b3e82b0ff2ee72045489d38f0d496914db390d96850",
        "mechanism_class": "INTERNAL_STEERING_OR_ARCHITECTURE",
        "evidence_standing": "CATALOGED_LEAD",
        "operator_id": None,
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Proposed session queue beside Heedle instrument paired with Issues #2/#3/#6 tide/1 OKLCH host",
    },
    {
        "repo": "Moissanite-Labs/siliquant",
        "number": 11,
        "status": "closed_unmerged",
        "head_sha": "eb44099edde6b50ee1df63dbde5da3819be48c64",
        "snapshot_sha256": "88f1ceae3c484847c0e7467f077df2fea6f6a7ed4e58b5d8336289ffb8972484",
        "mechanism_class": "EXACT_CERTIFIER_OR_DOMAIN_TOOL",
        "evidence_standing": "CATALOGED_LEAD",
        "operator_id": None,
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Exact region-gain Phi formula and closed-form scale proof for ball/cross-polytope codebooks",
    },
    {
        "repo": "Moissanite-Labs/weft-loom",
        "number": 44,
        "status": "open",
        "head_sha": "e660cd3de1ebd8fac33c60a3f65f5ccabb5ed9f1",
        "snapshot_sha256": "26b6e847ec561742089947a1fdf7810711c0b4e9a7c768d803c75f33b75fa6e0",
        "mechanism_class": "EMPIRICAL_REFUTATION_OR_FREEZE",
        "evidence_standing": "CATALOGED_LEAD",
        "operator_id": None,
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Sign-lineage exact chance law for gated MLPs, two validity checks, and sign-flip evasion",
    },
    {
        "repo": "Moissanite-Labs/weft-loom",
        "number": 25,
        "status": "open",
        "head_sha": "ba1ca3e3590a9e7b269c5b9f1a9ade18ba7a65ae",
        "snapshot_sha256": "5cacc7fd6bcdee1ba96de2d346b581ddcc1a46788aa96c47161522a2ee7fc819",
        "mechanism_class": "EMPIRICAL_REFUTATION_OR_FREEZE",
        "evidence_standing": "CATALOGED_LEAD",
        "operator_id": None,
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Pre-freeze cancellation of CBC Experiment C catching information-theoretic identifiability trap",
    },
    {
        "repo": "Foundation-0/math0",
        "number": 3,
        "status": "open",
        "head_sha": "d94ad5d4869abf586d7e97d237c539b504ae5877",
        "snapshot_sha256": "9b272c406135cfb11048e7a088714d8e9a35c68409c0216fd153acf6ded26462",
        "mechanism_class": "EXACT_CERTIFIER_OR_DOMAIN_TOOL",
        "evidence_standing": "CATALOGED_LEAD",
        "operator_id": None,
        "honest_novelty": "N0",
        "prior_art_record": None,
        "operator_summary": "Stdlib GF(q) (q in 2..9) exact minimum-distance checker with Brouwer-Zimmermann certificates",
    },
]

CERT_TOP_KEYS = frozenset(
    {
        "schema",
        "mode",
        "honest_novelty",
        "external_writes",
        "intake_verification",
        "operator_witnesses",
        "law1b_gate",
        "must_fail_controls",
        "must_fail_controls_verified",
        "all_checks_passed",
        "canonical_sha256",
    }
)


def _reject_json_float(raw: str) -> Any:
    raise spo.SerendipityError("JSON_FLOAT_FORBIDDEN", raw)


def _reject_json_constant(raw: str) -> Any:
    raise spo.SerendipityError("JSON_CONSTANT_FORBIDDEN", raw)


def _no_duplicate_json_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise spo.SerendipityError("JSON_DUPLICATE_KEY", k)
        out[k] = v
    return out


MAX_JSON_INT_DIGITS = 1000


def _parse_bounded_json_int(raw: str) -> int:
    digits = raw[1:] if raw.startswith("-") else raw
    if len(digits) > MAX_JSON_INT_DIGITS:
        raise spo.SerendipityError("JSON_INT_TOO_LARGE", str(len(digits)))
    return int(raw)


def loads_strict_json(raw_bytes: bytes) -> Any:
    if b"\r" in raw_bytes:
        raise spo.SerendipityError("JSON_CRLF_FORBIDDEN")
    try:
        text = raw_bytes.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise spo.SerendipityError("JSON_INVALID_UTF8") from exc
    try:
        return json.loads(
            text,
            parse_float=_reject_json_float,
            parse_constant=_reject_json_constant,
            parse_int=_parse_bounded_json_int,
            object_pairs_hook=_no_duplicate_json_keys,
        )
    except spo.SerendipityError:
        raise
    except (json.JSONDecodeError, ValueError) as exc:
        raise spo.SerendipityError("JSON_DECODE_ERROR", str(exc)) from exc


def _build_pinned_mined_entries() -> list[dict[str, Any]]:
    """Return the exact 24 canonical pinned mined PR records."""
    return [dict(e) for e in CANONICAL_MINED_ENTRIES]


def _expect_serendipity_error(fn: Any, expected_code: str) -> dict[str, Any]:
    try:
        fn()
    except spo.SerendipityError as exc:
        return {
            "rejected": exc.code == expected_code,
            "expected_code": expected_code,
            "actual_code": exc.code,
        }
    return {
        "rejected": False,
        "expected_code": expected_code,
        "actual_code": None,
    }


def run_operator_witnesses() -> dict[str, Any]:
    """Execute all 5 exact pure-Z/Q mined-PR operators (M1..M5) with real positive & negative controls."""
    # M1: laya#1465 uneven micro-batch (4, 2) and (2, 1) windows
    m1_4_2 = spo.certify_m1_microbatch_weighting(["1", "1", "1", "1", "4", "4"], [4, 2])
    m1_2_1 = spo.certify_m1_microbatch_weighting(["1/5", "1/5", "4/5"], [2, 1])

    # M2: laya#698 p95 across n=1..100 (exact overshoot on multiples of 20: 20,40,60,80,100)
    m2_p95 = spo.certify_m2_nearest_rank_quantile(list(range(1, 101)), "19/20")

    # M3: laya#693/#683 minimum=1, maximum=3, raw_score=0 and 2
    m3_lo = spo.certify_m3_affine_score_projection(1, 3, "0")
    m3_hi = spo.certify_m3_affine_score_projection(1, 3, "2")

    # M4: vegaml#57 exact contiguous span pooling vs scatter-add + bincount
    m4_pool = spo.certify_m4_span_pooling_equivalence(
        [["1", "2", "3"], ["5", "4", "1"], ["2", "0", "8"], ["4", "6", "2"], ["7", "1", "5"], ["9", "3", "1"]],
        [[0, 2], [3, 6]],
    )

    # M5: exo#490, #911, #1136, #402, #428, #1192 exact deterministic witnesses
    m5_backtick_joined = spo.collapse_backtick_line_continuations("un\\\nlink_sim --force")
    m5_backtick_even = spo.collapse_backtick_line_continuations("echo a\\\\\nb")
    m5_heredoc_unquoted = spo.match_heredoc_logical_terminator(
        ["payload", "E\\", "OF"], "EOF", quoted_delimiter=False, strip_leading_tabs=False
    )
    m5_heredoc_quoted = spo.match_heredoc_logical_terminator(
        ["payload", "E\\", "OF"], "EOF", quoted_delimiter=True, strip_leading_tabs=False
    )
    m5_heredoc_tab_second_line = spo.match_heredoc_logical_terminator(
        ["payload", "E\\", "\tF"], "EF", quoted_delimiter=False, strip_leading_tabs=True
    )
    m5_xargs_long = spo.parse_xargs_command_token(["xargs", "--max-args", "1", "sync_tool", "arg"])
    m5_xargs_prefix = spo.parse_xargs_command_token(["xargs", "--max-a", "1", "sync_tool"])
    m5_xargs_clustered = spo.parse_xargs_command_token(["xargs", "-rn", "1", "sync_tool"])
    m5_xargs_bsd = spo.parse_xargs_command_token(["xargs", "-J", "%", "sync_tool"])
    m5_gh_body_link = spo.resolve_gh_target_repo(
        ["gh", "issue", "comment", "1", "--body", "https://github.com/internal/secret", "-R", "public/repo"]
    )
    m5_gh_dup_link = spo.resolve_gh_target_repo(
        ["gh", "issue", "close", "1", "--duplicate-of", "https://github.com/internal/secret", "https://github.com/public/repo/issues/1"]
    )
    m5_pinned_ok = spo.verify_pinned_peer_envelope("seat-a", "KEY-PINNED-A", "KEY-PINNED-A", {"seat-a": "KEY-PINNED-A"})
    m5_forged_presence = spo.verify_pinned_peer_envelope("seat-a", "KEY-ATTACKER", "KEY-ATTACKER", {"seat-a": "KEY-PINNED-A"})
    m5_unpinned = spo.verify_pinned_peer_envelope("seat-new", "KEY-ATTACKER", "KEY-ATTACKER", {"seat-a": "KEY-PINNED-A"})
    m5_wake_peer_no_renew = spo.simulate_wake_budget_fsm(
        ["schedule_wake", "wake_turn", "schedule_wake", "wake_turn", "peer_turn", "schedule_wake", "wake_turn"],
        max_wakes=2,
    )
    m5_wake_principal_renew = spo.simulate_wake_budget_fsm(
        ["schedule_wake", "wake_turn", "schedule_wake", "wake_turn", "principal_turn", "schedule_wake", "wake_turn"],
        max_wakes=2,
    )

    return {
        "m1_microbatch_4_2": m1_4_2,
        "m1_microbatch_2_1": m1_2_1,
        "m2_p95_n1_to_100": m2_p95,
        "m3_affine_score_lo": m3_lo,
        "m3_affine_score_hi": m3_hi,
        "m4_span_pooling": m4_pool,
        "m5_exo_lexer_and_state": {
            "exo490_backtick_odd_joined": m5_backtick_joined,
            "exo490_backtick_even_preserved": m5_backtick_even,
            "exo911_heredoc_unquoted_idx": m5_heredoc_unquoted,
            "exo911_heredoc_quoted_idx": m5_heredoc_quoted,
            "exo911_heredoc_tab_second_line_idx": m5_heredoc_tab_second_line,
            "exo1136_xargs_long": m5_xargs_long,
            "exo1136_xargs_prefix": m5_xargs_prefix,
            "exo1136_xargs_clustered": m5_xargs_clustered,
            "exo1136_xargs_bsd": m5_xargs_bsd,
            "exo402_gh_body_vs_flag_r": m5_gh_body_link,
            "exo402_gh_dup_vs_operand": m5_gh_dup_link,
            "exo428_pinned_ok": m5_pinned_ok,
            "exo428_forged_presence_rejected": m5_forged_presence,
            "exo428_unpinned_held": m5_unpinned,
            "exo1192_peer_cannot_renew_budget": m5_wake_peer_no_renew,
            "exo1192_principal_renews_budget": m5_wake_principal_renew,
        },
    }


def verify_live_intake(intake_root: Path) -> dict[str, Any]:
    """Verify SHA-256 digests and schema consistency of the frozen 8-repo PR intake on disk."""
    if not intake_root.is_dir():
        raise spo.SerendipityError("INTAKE_ROOT_NOT_DIR")
    summary_path = intake_root / "intake_summary.json"
    manifest_path = intake_root / "deep_diffs" / "DEEP_MINING_MANIFEST.json"
    heedle_issues_path = intake_root / "Moissanite-Labs__heedle_issues.json"
    for req_p in (summary_path, manifest_path, heedle_issues_path):
        if not req_p.is_file():
            raise spo.SerendipityError("INTAKE_REQUIRED_FILE_MISSING", req_p.name)

    summary_bytes = summary_path.read_bytes()
    manifest_bytes = manifest_path.read_bytes()
    heedle_bytes = heedle_issues_path.read_bytes()

    summary_obj = loads_strict_json(summary_bytes)
    manifest_obj = loads_strict_json(manifest_bytes)
    heedle_obj = loads_strict_json(heedle_bytes)

    if not isinstance(summary_obj, dict) or len(summary_obj) != len(PINNED_REPO_SNAPSHOTS):
        raise spo.SerendipityError("INTAKE_SUMMARY_REPO_COUNT_MISMATCH")

    verified_repos: list[dict[str, Any]] = []
    for pinned in PINNED_REPO_SNAPSHOTS:
        repo = pinned["repo"]
        if repo not in summary_obj:
            raise spo.SerendipityError("INTAKE_REPO_MISSING_FROM_SUMMARY", repo)
        slug_path = intake_root / f"{repo.replace('/', '__')}_prs.json"
        if not slug_path.is_file():
            raise spo.SerendipityError("INTAKE_REPO_PRS_FILE_MISSING", slug_path.name)
        raw_prs = slug_path.read_bytes()
        actual_sha = hashlib.sha256(raw_prs).hexdigest()
        if actual_sha != pinned["prs_json_sha256"]:
            raise spo.SerendipityError("INTAKE_REPO_SHA256_MISMATCH", repo)
        prs_list = loads_strict_json(raw_prs)
        if not isinstance(prs_list, list) or len(prs_list) != pinned["fetched"]:
            raise spo.SerendipityError("INTAKE_REPO_PR_LIST_LEN_MISMATCH", repo)
        n_open = sum(1 for p in prs_list if p.get("status") == "open")
        n_cu = sum(1 for p in prs_list if p.get("status") == "closed_unmerged")
        n_m = sum(1 for p in prs_list if p.get("status") == "merged")
        if (n_open, n_cu, n_m) != (pinned["open"], pinned["closed_unmerged"], pinned["merged"]):
            raise spo.SerendipityError("INTAKE_REPO_STATUS_COUNTS_MISMATCH", repo)
        verified_repos.append(
            {
                "repo": repo,
                "fetched": len(prs_list),
                "open": n_open,
                "closed_unmerged": n_cu,
                "merged": n_m,
                "prs_json_sha256": actual_sha,
            }
        )

    if not isinstance(manifest_obj, list) or len(manifest_obj) == 0:
        raise spo.SerendipityError("INTAKE_DEEP_MANIFEST_EMPTY")
    deep_dir = intake_root / "deep_diffs"
    deep_open = 0
    deep_cu = 0
    manifest_by_key: dict[tuple[str, int], dict[str, Any]] = {}
    for row in manifest_obj:
        if not isinstance(row, dict) or "file" not in row or "sha256" not in row:
            raise spo.SerendipityError("INTAKE_MANIFEST_ROW_INVALID")
        fpath = deep_dir / row["file"]
        if not fpath.is_file():
            raise spo.SerendipityError("INTAKE_DEEP_FILE_MISSING", row["file"])
        raw_deep = fpath.read_bytes()
        dsha = hashlib.sha256(raw_deep).hexdigest()
        if dsha != row["sha256"]:
            raise spo.SerendipityError("INTAKE_DEEP_FILE_SHA_MISMATCH", row["file"])
        dobj = loads_strict_json(raw_deep)
        if dobj.get("head_sha") != row.get("head_sha"):
            raise spo.SerendipityError("INTAKE_DEEP_HEAD_SHA_MISMATCH", row["file"])
        st = row.get("status")
        if st == "open":
            deep_open += 1
        elif st == "closed_unmerged":
            deep_cu += 1
        else:
            raise spo.SerendipityError("INTAKE_DEEP_UNEXPECTED_STATUS", str(st))
        manifest_by_key[(row["repo"], row["number"])] = row

    # Cross-check every canonical mined entry against the live deep manifest
    for ent in _build_pinned_mined_entries():
        key = (ent["repo"], ent["number"])
        if key not in manifest_by_key:
            raise spo.SerendipityError("INTAKE_CANONICAL_ENTRY_MISSING", f"{key[0]}#{key[1]}")
        mrow = manifest_by_key[key]
        if mrow["head_sha"] != ent["head_sha"] or mrow["sha256"] != ent["snapshot_sha256"]:
            raise spo.SerendipityError("INTAKE_CANONICAL_SHA_MISMATCH", f"{key[0]}#{key[1]}")

    if not isinstance(heedle_obj, list) or [i.get("number") for i in heedle_obj] != [2, 3, 6, 7]:
        raise spo.SerendipityError("INTAKE_HEEDLE_ISSUES_MISMATCH")

    return {
        "verified_on_disk": True,
        "intake_summary_sha256": hashlib.sha256(summary_bytes).hexdigest(),
        "deep_manifest_sha256": hashlib.sha256(manifest_bytes).hexdigest(),
        "heedle_issues_sha256": hashlib.sha256(heedle_bytes).hexdigest(),
        "repos_verified": len(verified_repos),
        "deep_pr_files_verified": len(manifest_obj),
        "deep_open_count": deep_open,
        "deep_closed_unmerged_count": deep_cu,
        "heedle_issues_verified": len(heedle_obj),
    }


def build_certificate(*, mode: str, intake_root: Path | None = None) -> dict[str, Any]:
    if mode not in ("live", "standalone"):
        raise spo.SerendipityError("CERT_INVALID_MODE", mode)
    if mode == "live":
        if intake_root is None:
            raise spo.SerendipityError("CERT_LIVE_REQUIRES_INTAKE_ROOT")
        intake_info = verify_live_intake(intake_root)
    else:
        intake_info = {
            "verified_on_disk": False,
            "intake_summary_sha256": "2456c15109f45fb78a4b43df7995aa0c93a8c8f9993a8c7db981971a859e587b",
            "deep_manifest_sha256": "c315b6621bf4a893de6a54fd021484a44d665d6260138a8b497d46d95934a8b1",
            "heedle_issues_sha256": "875808d793ef42baee5ea44f0ac3971912ee4a5d33e1069be776b1a5b2d9e623",
            "repos_verified": len(PINNED_REPO_SNAPSHOTS),
            "deep_pr_files_verified": 40,
            "deep_open_count": 19,
            "deep_closed_unmerged_count": 21,
            "heedle_issues_verified": 4,
        }

    mined_entries = _build_pinned_mined_entries()
    mining_spec = {
        "spec_version": "aletheia.law1b.v1",
        "external_writes": 0,
        "repos": PINNED_REPO_SNAPSHOTS,
        "mined_entries": mined_entries,
    }
    law1b_res = spo.certify_law1b_serendipity_mining(mining_spec)
    witnesses = run_operator_witnesses()

    # Must-fail controls (dynamically counted)
    must_fail = {
        "closed_unmerged_blind_spot_rejected": _expect_serendipity_error(
            lambda: spo.certify_law1b_serendipity_mining(
                {**mining_spec, "mined_entries": [e for e in mined_entries if e["status"] == "open"]}
            ),
            "L1B_CLOSED_UNMERGED_BLIND_SPOT",
        ),
        "nonzero_external_writes_rejected": _expect_serendipity_error(
            lambda: spo.certify_law1b_serendipity_mining({**mining_spec, "external_writes": 1}),
            "L1B_NONZERO_EXTERNAL_WRITES",
        ),
        "lead_claiming_n2_rejected": _expect_serendipity_error(
            lambda: spo.certify_law1b_serendipity_mining(
                {
                    **mining_spec,
                    "mined_entries": [
                        {**e, "honest_novelty": "N2"} if e["evidence_standing"] == "CATALOGED_LEAD" else e
                        for e in mined_entries
                    ],
                }
            ),
            "L1B_LEAD_CANNOT_CLAIM_ABOVE_N0",
        ),
        "witness_unknown_operator_rejected": _expect_serendipity_error(
            lambda: spo.certify_law1b_serendipity_mining(
                {
                    **mining_spec,
                    "mined_entries": [
                        {**e, "operator_id": "M99_BOGUS"} if e["evidence_standing"] == "EXECUTED_EXACT_WITNESS" else e
                        for e in mined_entries
                    ],
                }
            ),
            "L1B_WITNESS_UNKNOWN_OPERATOR",
        ),
        "witness_claiming_n2_without_prior_art_rejected": _expect_serendipity_error(
            lambda: spo.certify_law1b_serendipity_mining(
                {
                    **mining_spec,
                    "mined_entries": [
                        {**e, "honest_novelty": "N2", "prior_art_record": None}
                        if e["evidence_standing"] == "EXECUTED_EXACT_WITNESS"
                        else e
                        for e in mined_entries
                    ],
                }
            ),
            "L1B_NOVELTY_ABOVE_N0_REQUIRES_PRIOR_ART",
        ),
        "lead_with_operator_id_rejected": _expect_serendipity_error(
            lambda: spo.certify_law1b_serendipity_mining(
                {
                    **mining_spec,
                    "mined_entries": [
                        {**e, "operator_id": "M1_MICROBATCH_WEIGHTING"}
                        if e["evidence_standing"] == "CATALOGED_LEAD"
                        else e
                        for e in mined_entries
                    ],
                }
            ),
            "L1B_LEAD_FORBIDS_OPERATOR_ID",
        ),
        "uniform_hex_placeholder_sha_rejected": _expect_serendipity_error(
            lambda: spo.certify_law1b_serendipity_mining(
                {**mining_spec, "mined_entries": [{**mined_entries[0], "head_sha": "0" * 40}] + mined_entries[1:]}
            ),
            "L1B_ENTRY_INVALID_HEAD_SHA",
        ),
        "float_input_rejected": _expect_serendipity_error(
            lambda: spo.certify_m1_microbatch_weighting([0.5, 0.5], [1, 1]),
            "RATIONAL_INVALID_SYNTAX",
        ),
        "m4_overlapping_spans_rejected": _expect_serendipity_error(
            lambda: spo.certify_m4_span_pooling_equivalence([["1"], ["2"], ["3"]], [[0, 2], [1, 3]]),
            "M4_OVERLAPPING_SPANS",
        ),
    }

    m5 = witnesses["m5_exo_lexer_and_state"]
    all_ok = (
        law1b_res["certified"] is True
        and witnesses["m1_microbatch_4_2"]["exact_match"] is True
        and witnesses["m1_microbatch_4_2"]["uneven_bias_detected"] is True
        and witnesses["m1_microbatch_2_1"]["exact_match"] is True
        and witnesses["m2_p95_n1_to_100"]["overshoot_sizes"] == [20, 40, 60, 80, 100]
        and witnesses["m2_p95_n1_to_100"]["exact_divisibility_match"] is True
        and witnesses["m3_affine_score_lo"]["fixed_projected"] == 1
        and witnesses["m3_affine_score_lo"]["buggy_out_of_range"] is True
        and witnesses["m3_affine_score_hi"]["fixed_projected"] == 3
        and witnesses["m4_span_pooling"]["exact_equivalence"] is True
        and m5["exo490_backtick_odd_joined"] == "unlink_sim --force"
        and m5["exo911_heredoc_unquoted_idx"] == 2
        and m5["exo911_heredoc_quoted_idx"] == -1
        and m5["exo911_heredoc_tab_second_line_idx"] == -1
        and m5["exo1136_xargs_long"] == "sync_tool"
        and m5["exo1136_xargs_prefix"] == "sync_tool"
        and m5["exo1136_xargs_clustered"] == "sync_tool"
        and m5["exo1136_xargs_bsd"] == "sync_tool"
        and m5["exo402_gh_body_vs_flag_r"] == "public/repo"
        and m5["exo402_gh_dup_vs_operand"] == "https://github.com/public/repo/issues/1"
        and m5["exo428_pinned_ok"]["trusted"] is True
        and m5["exo428_forged_presence_rejected"]["trusted"] is False
        and m5["exo428_unpinned_held"]["decision"] == "HOLD_UNPINNED_SEAT"
        and m5["exo1192_peer_cannot_renew_budget"]["denied_wakes"] == 2
        and m5["exo1192_principal_renews_budget"]["denied_wakes"] == 0
        and all(ctrl["rejected"] is True for ctrl in must_fail.values())
    )

    body: dict[str, Any] = {
        "schema": "aletheia.track_s12.serendipity_pr_mining.v1",
        "mode": mode,
        "honest_novelty": "N0",
        "external_writes": 0,
        "intake_verification": intake_info,
        "operator_witnesses": witnesses,
        "law1b_gate": law1b_res,
        "must_fail_controls": must_fail,
        "must_fail_controls_verified": len(must_fail),
        "all_checks_passed": all_ok,
    }
    body["canonical_sha256"] = spo.canonical_sha256(body)
    return body


def validate_saved_certificate(cert_path: Path, *, intake_root: Path | None = None) -> dict[str, Any]:
    """Verify a saved certificate JSON strictly (no floats, no dup keys, exact inner SHA & recomputed parity).

    Live-mode certificates (`mode == "live"`) require `--intake-root` and re-hash the intake files on disk;
    standalone-mode certificates verify offline against deterministic standalone recomputation.
    """
    if not cert_path.is_file():
        raise spo.SerendipityError("CERT_FILE_NOT_FOUND")
    obj = loads_strict_json(cert_path.read_bytes())
    spo.verify_exact_json_value(obj)
    if not isinstance(obj, dict) or frozenset(obj.keys()) != CERT_TOP_KEYS:
        raise spo.SerendipityError("CERT_SCHEMA_MISMATCH")
    if obj["schema"] != "aletheia.track_s12.serendipity_pr_mining.v1":
        raise spo.SerendipityError("CERT_INVALID_SCHEMA")
    if obj["mode"] not in ("live", "standalone"):
        raise spo.SerendipityError("CERT_INVALID_MODE")
    if obj["honest_novelty"] != "N0":
        raise spo.SerendipityError("CERT_INVALID_NOVELTY")
    if not spo.is_strict_int(obj["external_writes"]) or obj["external_writes"] != 0:
        raise spo.SerendipityError("CERT_NONZERO_EXTERNAL_WRITES")
    if obj["all_checks_passed"] is not True:
        raise spo.SerendipityError("CERT_NOT_ALL_PASSED")
    if (
        not isinstance(obj["must_fail_controls"], dict)
        or not spo.is_strict_int(obj["must_fail_controls_verified"])
        or obj["must_fail_controls_verified"] != len(obj["must_fail_controls"])
    ):
        raise spo.SerendipityError("CERT_CONTROL_COUNT_MISMATCH")

    saved_sha = obj["canonical_sha256"]
    if not spo.is_nonuniform_lower_hex(saved_sha, 64):
        raise spo.SerendipityError("CERT_INVALID_CANONICAL_SHA")
    without_sha = {k: v for k, v in obj.items() if k != "canonical_sha256"}
    recomputed_sha = spo.canonical_sha256(without_sha)
    if recomputed_sha != saved_sha:
        raise spo.SerendipityError("CERT_CANONICAL_SHA_MISMATCH")

    # Cross-check intake_verification, operator witnesses, law1b gate & controls bit-for-bit.
    # Live certificates MUST re-verify the intake snapshot on disk via --intake-root.
    expected_standalone = build_certificate(mode="standalone")
    if obj["mode"] == "live":
        if intake_root is None:
            raise spo.SerendipityError("CERT_LIVE_REQUIRES_INTAKE_ROOT")
        expected_intake = verify_live_intake(intake_root)
    else:
        expected_intake = expected_standalone["intake_verification"]
    if not spo.strict_typed_equal(obj["intake_verification"], expected_intake):
        raise spo.SerendipityError("CERT_INTAKE_VERIFICATION_MISMATCH")
    if not spo.strict_typed_equal(obj["operator_witnesses"], expected_standalone["operator_witnesses"]):
        raise spo.SerendipityError("CERT_WITNESSES_MISMATCH")
    if not spo.strict_typed_equal(obj["law1b_gate"], expected_standalone["law1b_gate"]):
        raise spo.SerendipityError("CERT_LAW1B_GATE_MISMATCH")
    if not spo.strict_typed_equal(obj["must_fail_controls"], expected_standalone["must_fail_controls"]):
        raise spo.SerendipityError("CERT_CONTROLS_MISMATCH")

    return {"valid": True, "mode": obj["mode"], "canonical_sha256": saved_sha}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Track S12 Law-1b Unmerged-PR Serendipity Mining Certifier")
    parser.add_argument("--live", action="store_true", help="Verify frozen intake JSON files on disk")
    parser.add_argument("--standalone", action="store_true", help="Run deterministic offline standalone mode (default)")
    parser.add_argument("--intake-root", type=Path, default=None, help="Path to intake-serendipity-prs directory")
    parser.add_argument("--check", type=Path, default=None, help="Verify an existing certificate JSON file")
    parser.add_argument("--json", action="store_true", help="Emit canonical JSON output")
    args = parser.parse_args(argv)

    try:
        if args.check is not None:
            res = validate_saved_certificate(args.check, intake_root=args.intake_root)
            print(json.dumps(res, indent=2, sort_keys=True))
            return 0

        mode = "live" if args.live else "standalone"
        cert = build_certificate(mode=mode, intake_root=args.intake_root)
        print(json.dumps(cert, indent=2, sort_keys=True))
        return 0 if cert["all_checks_passed"] else 1
    except (spo.SerendipityError, OSError) as exc:
        code = exc.code if isinstance(exc, spo.SerendipityError) else type(exc).__name__
        print(json.dumps({"valid": False, "error_code": code, "detail": str(exc)}, sort_keys=True), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
