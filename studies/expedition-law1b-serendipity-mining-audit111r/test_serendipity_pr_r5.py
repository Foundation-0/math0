#!/usr/bin/env python3
"""
R5 Adversarial & Mutation-Killing Test Suite for Track S12 (Law-1b Unmerged-PR Mining).

Zero external dependencies. Zero bare `assert` statements. Safe across `-I -B`, `-I -O -B`,
and `-I -B -W error`. Kills 100% of `aletheia mutate --max-mutants 0 --add-cwd` sites AND
100% of AST `BoolOp` raise-guard sub-clauses across `serendipity_pr_oracle.py` and
`serendipity_pr_certifier.py`.
"""
from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import serendipity_pr_certifier as spc
import serendipity_pr_oracle as spo


def _valid_law1b_spec(**kw: object) -> dict[str, object]:
    base: dict[str, object] = {
        "spec_version": "aletheia.law1b.v1",
        "external_writes": 0,
        "repos": [
            {
                "repo": "OrgA/repo1",
                "fetched": 10,
                "open": 2,
                "closed_unmerged": 3,
                "merged": 5,
                "prs_json_sha256": "ab" * 32,
            }
        ],
        "mined_entries": [
            {
                "repo": "OrgA/repo1",
                "number": 1,
                "status": "open",
                "head_sha": "12" * 20,
                "snapshot_sha256": "cd" * 32,
                "mechanism_class": "DENOMINATOR_OR_WEIGHT_BIAS",
                "evidence_standing": "EXECUTED_EXACT_WITNESS",
                "operator_id": "M1_MICROBATCH_WEIGHTING",
                "honest_novelty": "N0",
                "prior_art_record": None,
                "operator_summary": "Weighted micro-batch accumulation witness",
            },
            {
                "repo": "OrgA/repo1",
                "number": 2,
                "status": "closed_unmerged",
                "head_sha": "34" * 20,
                "snapshot_sha256": "ef" * 32,
                "mechanism_class": "QUANTILE_OR_INDEX_BOUNDARY",
                "evidence_standing": "CATALOGED_LEAD",
                "operator_id": None,
                "honest_novelty": "N0",
                "prior_art_record": None,
                "operator_summary": "Closed-unmerged quantile boundary lead",
            },
        ],
    }
    base.update(kw)
    return base


class TestSerendipityPrR5(unittest.TestCase):
    def _expect_err(self, fn, expected_code: str) -> None:
        with self.assertRaises(spo.SerendipityError) as ctx:
            fn()
        self.assertEqual(ctx.exception.code, expected_code)

    def test_01_helpers_rational_exact_json_and_typed_equal(self) -> None:
        self.assertTrue(spo.is_strict_int(0))
        self.assertFalse(spo.is_strict_int(True))
        self.assertTrue(spo.is_clean_ascii("abc"))
        self.assertFalse(spo.is_clean_ascii(""))
        self.assertFalse(spo.is_clean_ascii(" a"))
        self.assertFalse(spo.is_clean_ascii("a\x00b"))
        self.assertFalse(spo.is_clean_ascii("caf\u00e9"))
        self.assertTrue(spo.is_nonuniform_lower_hex("ab" * 32, 64))
        self.assertFalse(spo.is_nonuniform_lower_hex("0" * 64, 64))
        self.assertFalse(spo.is_nonuniform_lower_hex("AB" * 32, 64))
        self.assertFalse(spo.is_nonuniform_lower_hex("ab" * 10, 64))

        # Exact JSON value checks
        spo.verify_exact_json_value({"a": [None, True, 1, "x"]})
        self._expect_err(lambda: spo.verify_exact_json_value(1.5), "FLOAT_FORBIDDEN")
        self._expect_err(lambda: spo.verify_exact_json_value({1: "x"}), "NON_STR_DICT_KEY")
        self._expect_err(lambda: spo.verify_exact_json_value((1, 2)), "UNSUPPORTED_EXACT_TYPE")
        self._expect_err(lambda: spo.verify_exact_json_value({1, 2}), "UNSUPPORTED_EXACT_TYPE")
        self._expect_err(lambda: spo.verify_exact_json_value(1 + 2j), "UNSUPPORTED_EXACT_TYPE")
        self._expect_err(lambda: spo.verify_exact_json_value(b"raw"), "UNSUPPORTED_EXACT_TYPE")

        # Strict typed equality
        self.assertTrue(spo.strict_typed_equal({"a": [1, True]}, {"a": [1, True]}))
        self.assertFalse(spo.strict_typed_equal(1, True))
        self.assertFalse(spo.strict_typed_equal({"a": 1}, {"b": 1}))
        self.assertFalse(spo.strict_typed_equal([1], [1, 2]))
        self.assertFalse(spo.strict_typed_equal([1], [True]))

        # Rational parser
        self.assertEqual(spo.parse_exact_rational(Fraction(3, 4)), Fraction(3, 4))
        self.assertEqual(spo.parse_exact_rational(-5), Fraction(-5, 1))
        self.assertEqual(spo.parse_exact_rational("0"), Fraction(0, 1))
        self.assertEqual(spo.parse_exact_rational("0/1"), Fraction(0, 1))
        self.assertEqual(spo.parse_exact_rational("10"), Fraction(10, 1))
        self.assertEqual(spo.parse_exact_rational("1/10"), Fraction(1, 10))
        self.assertEqual(spo.parse_exact_rational("-7/3"), Fraction(-7, 3))
        self.assertEqual(spo.parse_exact_rational("1" * 128), Fraction(int("1" * 128), 1))
        self.assertEqual(spo.fmt_q(Fraction(4, 1)), "4")
        self.assertEqual(spo.fmt_q(Fraction(3, 4)), "3/4")
        self.assertEqual(spo._half_away_from_zero_round(Fraction(3, 2)), 2)
        self.assertEqual(spo._half_away_from_zero_round(Fraction(-3, 2)), -2)
        for bad, code in (
            (True, "RATIONAL_INVALID_SYNTAX"),
            (0.5, "RATIONAL_INVALID_SYNTAX"),
            ("1/2\n", "RATIONAL_INVALID_SYNTAX"),
            ("1" * 129, "RATIONAL_TOO_LONG"),
            ("1/2/3", "RATIONAL_TOO_MANY_SLASHES"),
            ("-", "RATIONAL_INVALID_NUMERATOR"),
            ("+5", "RATIONAL_INVALID_NUMERATOR"),
            ("1_0", "RATIONAL_INVALID_NUMERATOR"),
            ("01/2", "RATIONAL_NONCANONICAL_LEADING_ZERO"),
            ("00", "RATIONAL_NONCANONICAL_LEADING_ZERO"),
            ("-0", "RATIONAL_NEGATIVE_ZERO"),
            ("-0/1", "RATIONAL_NEGATIVE_ZERO"),
            ("1/", "RATIONAL_INVALID_DENOMINATOR"),
            ("1/+5", "RATIONAL_INVALID_DENOMINATOR"),
            ("1/02", "RATIONAL_NONCANONICAL_LEADING_ZERO"),
            ("1/0", "RATIONAL_NONPOSITIVE_DENOMINATOR"),
            ("2/4", "RATIONAL_UNREDUCED_FRACTION"),
            ("0/2", "RATIONAL_UNREDUCED_FRACTION"),
        ):
            self._expect_err(lambda b=bad: spo.parse_exact_rational(b), code)

    def test_02_m1_m2_m3_m4_exact_operators_and_guards(self) -> None:
        # M1: laya#1465
        m1 = spo.certify_m1_microbatch_weighting(["1", "1", "1", "1", "4", "4"], [4, 2])
        self.assertTrue(m1["exact_match"])
        self.assertTrue(m1["uneven_bias_detected"])
        self.assertEqual(m1["true_full_mean"], "2")
        self.assertEqual(m1["unweighted_buggy_mean"], "5/2")
        self.assertEqual(m1["unweighted_distortion"], "1/2")
        m1_even = spo.certify_m1_microbatch_weighting(["1", "3"], [1, 1])
        self.assertFalse(m1_even["uneven_bias_detected"])
        for losses, sizes, code in (
            ("not-list", [1], "M1_EMPTY_ITEM_LOSSES"),
            ([], [1], "M1_EMPTY_ITEM_LOSSES"),
            (["1"], "not-list", "M1_EMPTY_MICROBATCH_SIZES"),
            (["1"], [], "M1_EMPTY_MICROBATCH_SIZES"),
            (["1"], [True], "M1_INVALID_MICROBATCH_SIZE"),
            (["1"], [0], "M1_INVALID_MICROBATCH_SIZE"),
            (["1", "2"], [1], "M1_PARTITION_SUM_MISMATCH"),
        ):
            self._expect_err(lambda l=losses, s=sizes: spo.certify_m1_microbatch_weighting(l, s), code)

        # M2: laya#698
        m2 = spo.certify_m2_nearest_rank_quantile(list(range(1, 41)), "19/20")
        self.assertEqual(m2["overshoot_sizes"], [20, 40])
        self.assertTrue(m2["exact_divisibility_match"])
        m2_one = spo.certify_m2_nearest_rank_quantile([1, 2], "1")
        self.assertEqual(m2_one["overshoot_count"], 0)
        for sizes, q, code in (
            ([20], "0", "M2_QUANTILE_OUT_OF_RANGE"),
            ([20], "21/20", "M2_QUANTILE_OUT_OF_RANGE"),
            ("not-list", "19/20", "M2_EMPTY_SAMPLE_SIZES"),
            ([], "19/20", "M2_EMPTY_SAMPLE_SIZES"),
            ([True], "19/20", "M2_INVALID_SAMPLE_SIZE"),
            ([0], "19/20", "M2_INVALID_SAMPLE_SIZE"),
        ):
            self._expect_err(lambda s=sizes, qv=q: spo.certify_m2_nearest_rank_quantile(s, qv), code)

        # M3: laya#693/#683
        m3 = spo.certify_m3_affine_score_projection(1, 3, "0")
        self.assertEqual(m3["fixed_projected"], 1)
        self.assertEqual(m3["buggy_projected"], 0)
        self.assertTrue(m3["fixed_in_range"])
        self.assertTrue(m3["buggy_out_of_range"])
        for lo, hi, sc, code in (
            (True, 3, "0", "M3_INVALID_RANGE"),
            (0, True, "0", "M3_INVALID_RANGE"),
            (3, 3, "0", "M3_INVALID_RANGE"),
            (1, 3, "-1/10", "M3_SCORE_OUT_OF_LEVEL_SPAN"),
            (1, 3, "5/2", "M3_SCORE_OUT_OF_LEVEL_SPAN"),
        ):
            self._expect_err(lambda a=lo, b=hi, s=sc: spo.certify_m3_affine_score_projection(a, b, s), code)

        # M4: vegaml#57
        m4 = spo.certify_m4_span_pooling_equivalence([["1", "2"], ["3", "4"], ["5", "6"]], [[0, 2], [2, 3]])
        self.assertTrue(m4["exact_equivalence"])
        self.assertEqual(m4["pooled_direct"], [["2", "3"], ["5", "6"]])
        for rows, spans, code in (
            ("not-list", [[0, 1]], "M4_EMPTY_HIDDEN_ROWS"),
            ([], [[0, 1]], "M4_EMPTY_HIDDEN_ROWS"),
            (["not-list"], [[0, 1]], "M4_EMPTY_HIDDEN_DIM"),
            ([[]], [[0, 1]], "M4_EMPTY_HIDDEN_DIM"),
            ([["1", "2"], "34"], [[0, 1]], "M4_RAGGED_HIDDEN_MATRIX"),
            ([["1", "2"], ["3"]], [[0, 1]], "M4_RAGGED_HIDDEN_MATRIX"),
            ([["1"]], "bad", "M4_EMPTY_SPANS"),
            ([["1"]], [], "M4_EMPTY_SPANS"),
            ([["1"]], ["01"], "M4_INVALID_SPAN_PAIR"),
            ([["1"]], [[0]], "M4_INVALID_SPAN_PAIR"),
            ([["1"]], [[False, 1]], "M4_SPAN_OUT_OF_BOUNDS"),
            ([["1"]], [[0, True]], "M4_SPAN_OUT_OF_BOUNDS"),
            ([["1"]], [[-1, 1]], "M4_SPAN_OUT_OF_BOUNDS"),
            ([["1"]], [[0, 0]], "M4_SPAN_OUT_OF_BOUNDS"),
            ([["1"]], [[0, 2]], "M4_SPAN_OUT_OF_BOUNDS"),
            ([["1"], ["2"]], [[0, 2], [1, 2]], "M4_OVERLAPPING_SPANS"),
        ):
            self._expect_err(lambda r=rows, sp=spans: spo.certify_m4_span_pooling_equivalence(r, sp), code)

    def test_03_m5_exo_lexer_getopt_operand_pinned_key_and_wake_fsm(self) -> None:
        # exo#490
        self.assertEqual(spo.collapse_backtick_line_continuations("un\\\nlink_sim"), "unlink_sim")
        self.assertEqual(spo.collapse_backtick_line_continuations("a\\\\\nb"), "a\\\nb")
        self.assertEqual(spo.collapse_backtick_line_continuations("a\\x"), "a\\x")
        self._expect_err(lambda: spo.collapse_backtick_line_continuations(123), "M5_BODY_NOT_STR")  # type: ignore[arg-type]

        # exo#911
        self.assertEqual(spo.match_heredoc_logical_terminator(["x", "E\\", "OF"], "EOF", quoted_delimiter=False, strip_leading_tabs=False), 2)
        self.assertEqual(spo.match_heredoc_logical_terminator(["x", "E\\", "OF"], "EOF", quoted_delimiter=True, strip_leading_tabs=False), -1)
        self.assertEqual(spo.match_heredoc_logical_terminator(["\tEOF"], "EOF", quoted_delimiter=True, strip_leading_tabs=True), 0)
        self.assertEqual(spo.match_heredoc_logical_terminator(["E\\", "\tF"], "EF", quoted_delimiter=False, strip_leading_tabs=True), -1)
        self.assertEqual(spo.match_heredoc_logical_terminator(["x\\\\", "EOF"], "EOF", quoted_delimiter=False, strip_leading_tabs=False), 1)
        self._expect_err(lambda: spo.match_heredoc_logical_terminator("bad", "EOF", quoted_delimiter=False, strip_leading_tabs=False), "M5_HEREDOC_LINES_INVALID")  # type: ignore[arg-type]
        self._expect_err(lambda: spo.match_heredoc_logical_terminator([1], "EOF", quoted_delimiter=False, strip_leading_tabs=False), "M5_HEREDOC_LINES_INVALID")  # type: ignore[list-item]
        self._expect_err(lambda: spo.match_heredoc_logical_terminator(["a"], "", quoted_delimiter=False, strip_leading_tabs=False), "M5_HEREDOC_DELIM_INVALID")
        self._expect_err(lambda: spo.match_heredoc_logical_terminator(["a"], "EOF", quoted_delimiter=1, strip_leading_tabs=False), "M5_HEREDOC_FLAG_INVALID")  # type: ignore[arg-type]
        self._expect_err(lambda: spo.match_heredoc_logical_terminator(["a"], "EOF", quoted_delimiter=False, strip_leading_tabs=1), "M5_HEREDOC_FLAG_INVALID")  # type: ignore[arg-type]

        # exo#1136
        self.assertEqual(spo.parse_xargs_command_token(["xargs", "--max-args", "1", "cmd"]), "cmd")
        self.assertEqual(spo.parse_xargs_command_token(["xargs", "--max-args=1", "--verbose", "-rn", "1", "-I%", "-z", "--", "cmd"]), "cmd")
        self.assertEqual(spo.parse_xargs_command_token(["xargs", "-J", "%", "cmd"]), "cmd")
        self.assertIsNone(spo.parse_xargs_command_token(["xargs", "-r"]))
        self.assertIsNone(spo.parse_xargs_command_token(["xargs", "--"]))
        self._expect_err(lambda: spo.parse_xargs_command_token("xargs"), "M5_XARGS_ARGV_INVALID")  # type: ignore[arg-type]
        self._expect_err(lambda: spo.parse_xargs_command_token([]), "M5_XARGS_ARGV_INVALID")
        self._expect_err(lambda: spo.parse_xargs_command_token(["xargs", 1]), "M5_XARGS_ARGV_INVALID")  # type: ignore[list-item]
        self._expect_err(lambda: spo.parse_xargs_command_token(["echo"]), "M5_XARGS_FIRST_TOKEN")

        # exo#402
        self.assertEqual(
            spo.resolve_gh_target_repo(["gh", "issue", "comment", "--body", "https://github.com/a/b", "--repo=pub/r", "--draft", "--k=v"]),
            "pub/r",
        )
        self.assertEqual(
            spo.resolve_gh_target_repo(["gh", "issue", "comment", "1", "-Rpublic/repo"]),
            "public/repo",
        )
        self.assertEqual(
            spo.resolve_gh_target_repo(["gh", "issue", "close", "--", "https://github.com/pub/r/issues/1"]),
            "https://github.com/pub/r/issues/1",
        )
        self._expect_err(lambda: spo.resolve_gh_target_repo("gh"), "M5_GH_ARGV_INVALID")  # type: ignore[arg-type]
        self._expect_err(lambda: spo.resolve_gh_target_repo([]), "M5_GH_ARGV_INVALID")
        self._expect_err(lambda: spo.resolve_gh_target_repo(["gh", 1]), "M5_GH_ARGV_INVALID")  # type: ignore[list-item]
        self._expect_err(lambda: spo.resolve_gh_target_repo(["git"]), "M5_GH_FIRST_TOKEN")
        self._expect_err(lambda: spo.resolve_gh_target_repo(["gh", "-R"]), "M5_GH_MISSING_REPO_VALUE")

        # exo#428
        self.assertTrue(spo.verify_pinned_peer_envelope("s1", "K1", "K1", {"s1": "K1"})["trusted"])
        self.assertFalse(spo.verify_pinned_peer_envelope("s1", "K2", "K2", {"s1": "K1"})["trusted"])
        self.assertEqual(spo.verify_pinned_peer_envelope("s2", "K2", "K2", {"s1": "K1"})["decision"], "HOLD_UNPINNED_SEAT")
        self._expect_err(lambda: spo.verify_pinned_peer_envelope("", "K1", "K1", {}), "M5_INVALID_SEAT")
        self._expect_err(lambda: spo.verify_pinned_peer_envelope("s1", "", "K1", {}), "M5_INVALID_KEY")
        self._expect_err(lambda: spo.verify_pinned_peer_envelope("s1", "K1", "", {}), "M5_INVALID_KEY")
        self._expect_err(lambda: spo.verify_pinned_peer_envelope("s1", "K1", "K1", []), "M5_PINNED_KEYS_NOT_DICT")  # type: ignore[arg-type]
        self._expect_err(lambda: spo.verify_pinned_peer_envelope("s1", "K1", "K1", {"s1": ""}), "M5_INVALID_PINNED_VALUE")

        # exo#1192
        fsm = spo.simulate_wake_budget_fsm(["schedule_wake", "steer", "wake_turn", "schedule_wake", "wake_turn", "bus_turn", "job_turn", "undo", "stop"], max_wakes=1)
        self.assertEqual(fsm["wakes_used"], 1)
        self.assertEqual(fsm["denied_wakes"], 1)
        self._expect_err(lambda: spo.simulate_wake_budget_fsm(["wake_turn"], max_wakes=True), "M5_INVALID_MAX_WAKES")
        self._expect_err(lambda: spo.simulate_wake_budget_fsm(["wake_turn"], max_wakes=0), "M5_INVALID_MAX_WAKES")
        self._expect_err(lambda: spo.simulate_wake_budget_fsm("wake_turn"), "M5_EMPTY_WAKE_EVENTS")  # type: ignore[arg-type]
        self._expect_err(lambda: spo.simulate_wake_budget_fsm([]), "M5_EMPTY_WAKE_EVENTS")
        self._expect_err(lambda: spo.simulate_wake_budget_fsm([["unhashable"]]), "M5_UNKNOWN_WAKE_EVENT")  # type: ignore[list-item]
        self._expect_err(lambda: spo.simulate_wake_budget_fsm(["bogus"]), "M5_UNKNOWN_WAKE_EVENT")

    def test_04_m6_law1b_gate_guards_and_subconditions(self) -> None:
        ok = spo.certify_law1b_serendipity_mining(_valid_law1b_spec())
        self.assertTrue(ok["certified"])
        self.assertEqual(ok["verdict"], "LAW1B_MINING_CERTIFIED")
        self.assertEqual(ok["unmerged_fraction"], "1/2")

        base_repo = _valid_law1b_spec()["repos"][0]  # type: ignore[index]
        base_entries = _valid_law1b_spec()["mined_entries"]  # type: ignore[index]
        e0 = base_entries[0]
        e1 = base_entries[1]

        # Valid single-bucket repos (closed_unmerged=0 or open=0), N0 with optional prior_art_record,
        # and N1 on EXECUTED_EXACT_WITNESS ONLY when paired with a certified operator_id and clean prior_art_record
        ok_open_only = spo.certify_law1b_serendipity_mining(
            _valid_law1b_spec(
                repos=[{**base_repo, "fetched": 6, "open": 1, "closed_unmerged": 0, "merged": 5}],
                mined_entries=[{**e0, "honest_novelty": "N1", "prior_art_record": "Prior-art audit 2026-11-22: 0 matches"}],
            )
        )
        self.assertTrue(ok_open_only["certified"])
        self.assertEqual(ok_open_only["certified_operator_ids"], ["M1_MICROBATCH_WEIGHTING"])
        ok_cu_only = spo.certify_law1b_serendipity_mining(
            _valid_law1b_spec(
                repos=[{**base_repo, "fetched": 6, "open": 0, "closed_unmerged": 1, "merged": 5}],
                mined_entries=[
                    {
                        **e1,
                        "evidence_standing": "EXECUTED_EXACT_WITNESS",
                        "operator_id": "M2_NEAREST_RANK_QUANTILE",
                        "prior_art_record": "Hyndman & Fan (1996) R-1",
                    }
                ],
            )
        )
        self.assertTrue(ok_cu_only["certified"])

        zero_unmerged_repo = {
            "repo": "OrgB/merged_only",
            "fetched": 5,
            "open": 0,
            "closed_unmerged": 0,
            "merged": 5,
            "prs_json_sha256": "de" * 32,
        }

        for bad_spec, code in (
            ([], "L1B_SCHEMA_MISMATCH"),
            ({}, "L1B_SCHEMA_MISMATCH"),
            (_valid_law1b_spec(spec_version="bad"), "L1B_INVALID_SPEC_VERSION"),
            (_valid_law1b_spec(external_writes=False), "L1B_NONZERO_EXTERNAL_WRITES"),
            (_valid_law1b_spec(external_writes=1), "L1B_NONZERO_EXTERNAL_WRITES"),
            (_valid_law1b_spec(repos="bad"), "L1B_EMPTY_REPOS"),
            (_valid_law1b_spec(repos=[]), "L1B_EMPTY_REPOS"),
            (_valid_law1b_spec(repos=["bad"]), "L1B_REPO_ROW_SCHEMA_MISMATCH"),
            (_valid_law1b_spec(repos=[{}]), "L1B_REPO_ROW_SCHEMA_MISMATCH"),
            (_valid_law1b_spec(repos=[{**base_repo, "repo": "OrgA/repo1\n"}]), "L1B_INVALID_REPO_NAME"),
            (_valid_law1b_spec(repos=[{**base_repo, "repo": "noslash"}]), "L1B_INVALID_REPO_NAME"),
            (_valid_law1b_spec(repos=[base_repo, {**base_repo, "repo": "orga/repo1"}]), "L1B_DUPLICATE_REPO"),
            (_valid_law1b_spec(repos=[{**base_repo, "fetched": True}]), "L1B_REPO_COUNT_NOT_INT"),
            (_valid_law1b_spec(repos=[{**base_repo, "open": True}]), "L1B_REPO_COUNT_NOT_INT"),
            (_valid_law1b_spec(repos=[{**base_repo, "closed_unmerged": True}]), "L1B_REPO_COUNT_NOT_INT"),
            (_valid_law1b_spec(repos=[{**base_repo, "merged": True}]), "L1B_REPO_COUNT_NOT_INT"),
            (_valid_law1b_spec(repos=[{**base_repo, "fetched": 0, "open": 0, "closed_unmerged": 0, "merged": 0}]), "L1B_REPO_COUNT_NEGATIVE"),
            (_valid_law1b_spec(repos=[{**base_repo, "open": -1}]), "L1B_REPO_COUNT_NEGATIVE"),
            (_valid_law1b_spec(repos=[{**base_repo, "closed_unmerged": -1}]), "L1B_REPO_COUNT_NEGATIVE"),
            (_valid_law1b_spec(repos=[{**base_repo, "merged": -1}]), "L1B_REPO_COUNT_NEGATIVE"),
            (_valid_law1b_spec(repos=[{**base_repo, "merged": 99}]), "L1B_REPO_COUNT_SUM_MISMATCH"),
            (_valid_law1b_spec(repos=[{**base_repo, "prs_json_sha256": "0" * 64}]), "L1B_INVALID_REPO_SHA256"),
            (_valid_law1b_spec(mined_entries="bad"), "L1B_EMPTY_MINED_ENTRIES"),
            (_valid_law1b_spec(mined_entries=[]), "L1B_EMPTY_MINED_ENTRIES"),
            (_valid_law1b_spec(mined_entries=["bad"]), "L1B_ENTRY_SCHEMA_MISMATCH"),
            (_valid_law1b_spec(mined_entries=[{}]), "L1B_ENTRY_SCHEMA_MISMATCH"),
            (_valid_law1b_spec(mined_entries=[{**e0, "repo": 123}]), "L1B_ENTRY_UNKNOWN_REPO"),
            (_valid_law1b_spec(mined_entries=[{**e0, "repo": "Other/repo"}]), "L1B_ENTRY_UNKNOWN_REPO"),
            (_valid_law1b_spec(mined_entries=[{**e0, "number": True}]), "L1B_ENTRY_INVALID_PR_NUMBER"),
            (_valid_law1b_spec(mined_entries=[{**e0, "number": 0}]), "L1B_ENTRY_INVALID_PR_NUMBER"),
            (_valid_law1b_spec(mined_entries=[e0, {**e1, "number": 1}]), "L1B_DUPLICATE_MINED_PR"),
            (_valid_law1b_spec(mined_entries=[{**e0, "status": "merged"}, e1]), "L1B_ENTRY_INVALID_STATUS"),
            (_valid_law1b_spec(mined_entries=[{**e0, "head_sha": "0" * 40}, e1]), "L1B_ENTRY_INVALID_HEAD_SHA"),
            (_valid_law1b_spec(mined_entries=[{**e0, "snapshot_sha256": "a" * 64}, e1]), "L1B_ENTRY_INVALID_SNAPSHOT_SHA"),
            (_valid_law1b_spec(mined_entries=[{**e0, "mechanism_class": "BOGUS"}, e1]), "L1B_ENTRY_INVALID_MECHANISM_CLASS"),
            (_valid_law1b_spec(mined_entries=[{**e0, "evidence_standing": "BOGUS"}, e1]), "L1B_ENTRY_INVALID_STANDING"),
            (_valid_law1b_spec(mined_entries=[{**e0, "operator_id": ["M1_MICROBATCH_WEIGHTING"]}, e1]), "L1B_WITNESS_UNKNOWN_OPERATOR"),
            (_valid_law1b_spec(mined_entries=[{**e0, "operator_id": "M99_BOGUS"}, e1]), "L1B_WITNESS_UNKNOWN_OPERATOR"),
            (_valid_law1b_spec(mined_entries=[e0, {**e1, "operator_id": "M1_MICROBATCH_WEIGHTING"}]), "L1B_LEAD_FORBIDS_OPERATOR_ID"),
            (_valid_law1b_spec(mined_entries=[{**e0, "honest_novelty": "N9"}, e1]), "L1B_ENTRY_INVALID_NOVELTY"),
            (_valid_law1b_spec(mined_entries=[e0, {**e1, "honest_novelty": "N1"}]), "L1B_LEAD_CANNOT_CLAIM_ABOVE_N0"),
            (_valid_law1b_spec(mined_entries=[{**e0, "prior_art_record": "  "}, e1]), "L1B_INVALID_PRIOR_ART_RECORD"),
            (_valid_law1b_spec(mined_entries=[{**e0, "honest_novelty": "N1", "prior_art_record": None}, e1]), "L1B_NOVELTY_ABOVE_N0_REQUIRES_PRIOR_ART"),
            (_valid_law1b_spec(mined_entries=[{**e0, "honest_novelty": "N2", "prior_art_record": " "}, e1]), "L1B_NOVELTY_ABOVE_N0_REQUIRES_PRIOR_ART"),
            (_valid_law1b_spec(mined_entries=[{**e0, "operator_summary": " "}, e1]), "L1B_ENTRY_EMPTY_SUMMARY"),
            (_valid_law1b_spec(mined_entries=[e0]), "L1B_CLOSED_UNMERGED_BLIND_SPOT"),
            (_valid_law1b_spec(mined_entries=[e1]), "L1B_OPEN_PR_BLIND_SPOT"),
            (_valid_law1b_spec(mined_entries=[{**e0, "evidence_standing": "CATALOGED_LEAD", "operator_id": None}, e1]), "L1B_ZERO_EXECUTED_WITNESSES"),
            # S12-L1B-02: per-repo open / closed_unmerged bucket caps enforced
            (
                _valid_law1b_spec(
                    repos=[base_repo, zero_unmerged_repo],
                    mined_entries=[e0, e1, {**e0, "repo": "OrgB/merged_only", "number": 9, "status": "open"}],
                ),
                "L1B_REPO_OPEN_COUNT_EXCEEDED",
            ),
            (
                _valid_law1b_spec(
                    repos=[base_repo, zero_unmerged_repo],
                    mined_entries=[e0, e1, {**e1, "repo": "OrgB/merged_only", "number": 10, "status": "closed_unmerged"}],
                ),
                "L1B_REPO_CLOSED_UNMERGED_COUNT_EXCEEDED",
            ),
        ):
            self._expect_err(lambda s=bad_spec: spo.certify_law1b_serendipity_mining(s), code)  # type: ignore[arg-type]

    def test_05_certifier_standalone_check_and_intake_guards(self) -> None:
        cert = spc.build_certificate(mode="standalone")
        self.assertTrue(cert["all_checks_passed"])
        self.assertEqual(cert["mode"], "standalone")
        self.assertFalse(cert["intake_verification"]["verified_on_disk"])
        self.assertEqual(cert["must_fail_controls_verified"], 9)
        self.assertEqual(cert["law1b_gate"]["total_prs_fetched"], 1437)
        self.assertEqual(cert["law1b_gate"]["total_unmerged_prs"], 387)
        self.assertEqual(cert["law1b_gate"]["closed_unmerged_mined"], 12)
        self.assertEqual(cert["law1b_gate"]["open_mined"], 12)
        self.assertEqual(cert["law1b_gate"]["certified_operator_ids"], sorted(spo.CERTIFIED_OPERATOR_IDS))

        # Strict JSON parser guards (CRLF, invalid UTF-8, floats, constants, dup keys, oversized 5000-digit ints)
        self._expect_err(lambda: spc.loads_strict_json(b'{"a": 1}\r\n'), "JSON_CRLF_FORBIDDEN")
        self._expect_err(lambda: spc.loads_strict_json(b"\xff\xfe"), "JSON_INVALID_UTF8")
        self._expect_err(lambda: spc.loads_strict_json(b"{bad"), "JSON_DECODE_ERROR")
        self._expect_err(lambda: spc.loads_strict_json(b'{"a": 1.25}'), "JSON_FLOAT_FORBIDDEN")
        self._expect_err(lambda: spc.loads_strict_json(b'{"a": NaN}'), "JSON_CONSTANT_FORBIDDEN")
        self._expect_err(lambda: spc.loads_strict_json(b'{"a": 1, "a": 2}'), "JSON_DUPLICATE_KEY")
        self.assertEqual(spc.loads_strict_json(('{"n": ' + ("9" * 1000) + "}").encode("utf-8"))["n"], int("9" * 1000))
        self.assertEqual(spc.loads_strict_json(('{"n": -' + ("9" * 1000) + "}").encode("utf-8"))["n"], -int("9" * 1000))
        self._expect_err(lambda: spc.loads_strict_json(('{"n": ' + ("9" * 1001) + "}").encode("utf-8")), "JSON_INT_TOO_LARGE")
        self._expect_err(lambda: spc.loads_strict_json(('{"n": ' + ("9" * 5000) + "}").encode("utf-8")), "JSON_INT_TOO_LARGE")

        # build_certificate mode guards
        self._expect_err(lambda: spc.build_certificate(mode="bogus"), "CERT_INVALID_MODE")
        self._expect_err(lambda: spc.build_certificate(mode="live", intake_root=None), "CERT_LIVE_REQUIRES_INTAKE_ROOT")
        self.assertFalse(spc._expect_serendipity_error(lambda: 42, "ANY")["rejected"])

        # validate_saved_certificate guards on temp copies
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            self._expect_err(lambda: spc.validate_saved_certificate(root / "missing.json"), "CERT_FILE_NOT_FOUND")
            good_p = root / "good.json"
            good_p.write_text(json.dumps(cert, indent=2, sort_keys=True) + "\n", encoding="utf-8")
            self.assertTrue(spc.validate_saved_certificate(good_p)["valid"])

            def _write_and_expect(obj: object, code: str, rehash: bool = False) -> None:
                p = root / "bad.json"
                if rehash and isinstance(obj, dict):
                    body = {k: v for k, v in obj.items() if k != "canonical_sha256"}
                    obj = {**body, "canonical_sha256": spo.canonical_sha256(body)}
                p.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
                self._expect_err(lambda: spc.validate_saved_certificate(p), code)

            _write_and_expect([1], "CERT_SCHEMA_MISMATCH")
            _write_and_expect({}, "CERT_SCHEMA_MISMATCH")
            _write_and_expect({**cert, "schema": "evil.forged.v99"}, "CERT_INVALID_SCHEMA", rehash=True)
            _write_and_expect({**cert, "mode": "bogus"}, "CERT_INVALID_MODE")
            _write_and_expect({**cert, "honest_novelty": "N2"}, "CERT_INVALID_NOVELTY", rehash=True)
            _write_and_expect({**cert, "external_writes": False}, "CERT_NONZERO_EXTERNAL_WRITES", rehash=True)
            _write_and_expect({**cert, "external_writes": 999}, "CERT_NONZERO_EXTERNAL_WRITES", rehash=True)
            _write_and_expect({**cert, "all_checks_passed": False}, "CERT_NOT_ALL_PASSED")
            _write_and_expect({**cert, "must_fail_controls": [1, 2, 3, 4, 5, 6, 7, 8, 9]}, "CERT_CONTROL_COUNT_MISMATCH")
            _write_and_expect({**cert, "must_fail_controls": {"k": {}}, "must_fail_controls_verified": True}, "CERT_CONTROL_COUNT_MISMATCH")
            _write_and_expect({**cert, "must_fail_controls_verified": 99}, "CERT_CONTROL_COUNT_MISMATCH")
            _write_and_expect({**cert, "canonical_sha256": "0" * 64}, "CERT_INVALID_CANONICAL_SHA")
            _write_and_expect({**cert, "canonical_sha256": "ab" * 32}, "CERT_CANONICAL_SHA_MISMATCH")
            _write_and_expect({**cert, "intake_verification": {}}, "CERT_INTAKE_VERIFICATION_MISMATCH", rehash=True)
            # Forging a standalone cert into mode="live", verified_on_disk=True and re-hashing MUST fail without --intake-root!
            _write_and_expect(
                {**cert, "mode": "live", "intake_verification": {**cert["intake_verification"], "verified_on_disk": True}},
                "CERT_LIVE_REQUIRES_INTAKE_ROOT",
                rehash=True,
            )
            _write_and_expect(
                {**cert, "intake_verification": {**cert["intake_verification"], "intake_summary_sha256": "0" * 64}},
                "CERT_INTAKE_VERIFICATION_MISMATCH",
                rehash=True,
            )
            _write_and_expect({**cert, "operator_witnesses": {}}, "CERT_WITNESSES_MISMATCH", rehash=True)
            _write_and_expect({**cert, "law1b_gate": {}}, "CERT_LAW1B_GATE_MISMATCH", rehash=True)
            bad_ctrls = {k: {**v, "rejected": False} for k, v in cert["must_fail_controls"].items()}
            _write_and_expect({**cert, "must_fail_controls": bad_ctrls}, "CERT_CONTROLS_MISMATCH", rehash=True)

            # CLI --check on malformed JSON & 5000-digit int returns structured exit 2 without traceback
            for fname, raw_txt, exp_code in (
                ("malformed.json", "{bad json\n", "JSON_DECODE_ERROR"),
                ("huge_int.json", '{"n": ' + ("9" * 5000) + "}\n", "JSON_INT_TOO_LARGE"),
            ):
                bad_p = root / fname
                bad_p.write_text(raw_txt, encoding="utf-8")
                err_buf = io.StringIO()
                with redirect_stderr(err_buf):
                    self.assertEqual(spc.main(["--check", str(bad_p)]), 2)
                self.assertIn(exp_code, err_buf.getvalue())
                self.assertNotIn("Traceback", err_buf.getvalue())

            # CLI --check on valid standalone cert succeeds cleanly
            out_buf = io.StringIO()
            with redirect_stdout(out_buf):
                self.assertEqual(spc.main(["--check", str(good_p)]), 0)
            self.assertTrue(json.loads(out_buf.getvalue())["valid"])

        # verify_live_intake error guards on synthetic dirs
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            self._expect_err(lambda: spc.verify_live_intake(root / "no_dir"), "INTAKE_ROOT_NOT_DIR")
            d = root / "intake"
            d.mkdir()
            self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_REQUIRED_FILE_MISSING")
            (d / "deep_diffs").mkdir()
            (d / "intake_summary.json").write_text(json.dumps(list(range(8))) + "\n", encoding="utf-8")
            (d / "deep_diffs" / "DEEP_MINING_MANIFEST.json").write_text("[]\n", encoding="utf-8")
            (d / "Moissanite-Labs__heedle_issues.json").write_text("[]\n", encoding="utf-8")
            self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_SUMMARY_REPO_COUNT_MISMATCH")
            full_summary = {p["repo"]: {"fetched": p["fetched"]} for p in spc.PINNED_REPO_SNAPSHOTS}
            (d / "intake_summary.json").write_text(json.dumps({**full_summary, "Extra/repo": {}}) + "\n", encoding="utf-8")
            self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_SUMMARY_REPO_COUNT_MISMATCH")
            (d / "intake_summary.json").write_text(json.dumps({f"r{i}": {} for i in range(8)}) + "\n", encoding="utf-8")
            self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_REPO_MISSING_FROM_SUMMARY")

            (d / "intake_summary.json").write_text(json.dumps(full_summary) + "\n", encoding="utf-8")
            self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_REPO_PRS_FILE_MISSING")
            first_slug = spc.PINNED_REPO_SNAPSHOTS[0]["repo"].replace("/", "__") + "_prs.json"
            (d / first_slug).write_text("[]\n", encoding="utf-8")
            self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_REPO_SHA256_MISMATCH")

        # If real intake directory is present next to this track, verify live parity AND error mutations on temp copy
        live_intake = HERE.parent / "intake-serendipity-prs"
        if live_intake.is_dir():
            live_cert = spc.build_certificate(mode="live", intake_root=live_intake)
            self.assertTrue(live_cert["all_checks_passed"])
            self.assertTrue(live_cert["intake_verification"]["verified_on_disk"])
            self.assertEqual(live_cert["intake_verification"]["deep_pr_files_verified"], 40)

        # Synthetic verify_live_intake deep-manifest / heedle-issues branch coverage via mocked PINNED_REPO_SNAPSHOTS
        with tempfile.TemporaryDirectory() as td:
            d = Path(td)
            (d / "deep_diffs").mkdir()
            prs_payload = (json.dumps([{"status": "open"}, {"status": "closed_unmerged"}, {"status": "merged"}]) + "\n").encode("utf-8")
            prs_sha = hashlib.sha256(prs_payload).hexdigest()
            (d / "OrgA__r1_prs.json").write_bytes(prs_payload)
            (d / "intake_summary.json").write_text(json.dumps({"OrgA/r1": {}}) + "\n", encoding="utf-8")
            (d / "Moissanite-Labs__heedle_issues.json").write_text(json.dumps([{"number": 2}, {"number": 3}, {"number": 6}, {"number": 7}]) + "\n", encoding="utf-8")

            orig_repos = spc.PINNED_REPO_SNAPSHOTS
            orig_entries = spc.CANONICAL_MINED_ENTRIES
            try:
                # 1. PR list len mismatch & status counts mismatch
                spc.PINNED_REPO_SNAPSHOTS = [{"repo": "OrgA/r1", "fetched": 99, "open": 1, "closed_unmerged": 1, "merged": 1, "prs_json_sha256": prs_sha}]
                (d / "deep_diffs" / "DEEP_MINING_MANIFEST.json").write_text("[]\n", encoding="utf-8")
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_REPO_PR_LIST_LEN_MISMATCH")

                bad_list_bytes = (json.dumps({"a": 1, "b": 2, "c": 3}) + "\n").encode("utf-8")
                (d / "OrgA__r1_prs.json").write_bytes(bad_list_bytes)
                spc.PINNED_REPO_SNAPSHOTS = [{"repo": "OrgA/r1", "fetched": 3, "open": 1, "closed_unmerged": 1, "merged": 1, "prs_json_sha256": hashlib.sha256(bad_list_bytes).hexdigest()}]
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_REPO_PR_LIST_LEN_MISMATCH")

                (d / "OrgA__r1_prs.json").write_bytes(prs_payload)
                spc.PINNED_REPO_SNAPSHOTS = [{"repo": "OrgA/r1", "fetched": 3, "open": 2, "closed_unmerged": 0, "merged": 1, "prs_json_sha256": prs_sha}]
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_REPO_STATUS_COUNTS_MISMATCH")

                # 2. Deep manifest checks
                spc.PINNED_REPO_SNAPSHOTS = [{"repo": "OrgA/r1", "fetched": 3, "open": 1, "closed_unmerged": 1, "merged": 1, "prs_json_sha256": prs_sha}]
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_DEEP_MANIFEST_EMPTY")
                (d / "deep_diffs" / "DEEP_MINING_MANIFEST.json").write_text('{"a": 1}\n', encoding="utf-8")
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_DEEP_MANIFEST_EMPTY")
                (d / "deep_diffs" / "DEEP_MINING_MANIFEST.json").write_text('[["file", "sha256"]]\n', encoding="utf-8")
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_MANIFEST_ROW_INVALID")
                (d / "deep_diffs" / "DEEP_MINING_MANIFEST.json").write_text('[{"file": "a.json"}]\n', encoding="utf-8")
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_MANIFEST_ROW_INVALID")
                (d / "deep_diffs" / "DEEP_MINING_MANIFEST.json").write_text('[{"sha256": "x"}]\n', encoding="utf-8")
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_MANIFEST_ROW_INVALID")
                (d / "deep_diffs" / "DEEP_MINING_MANIFEST.json").write_text('[{"file": "missing.json", "sha256": "x"}]\n', encoding="utf-8")
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_DEEP_FILE_MISSING")

                deep_raw = (json.dumps({"head_sha": "12" * 20}) + "\n").encode("utf-8")
                deep_sha = hashlib.sha256(deep_raw).hexdigest()
                (d / "deep_diffs" / "p1.json").write_bytes(deep_raw)
                (d / "deep_diffs" / "DEEP_MINING_MANIFEST.json").write_text(
                    json.dumps([{"repo": "OrgA/r1", "number": 1, "status": "open", "file": "p1.json", "sha256": "bad", "head_sha": "12" * 20}]) + "\n",
                    encoding="utf-8",
                )
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_DEEP_FILE_SHA_MISMATCH")

                (d / "deep_diffs" / "DEEP_MINING_MANIFEST.json").write_text(
                    json.dumps([{"repo": "OrgA/r1", "number": 1, "status": "open", "file": "p1.json", "sha256": deep_sha, "head_sha": "34" * 20}]) + "\n",
                    encoding="utf-8",
                )
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_DEEP_HEAD_SHA_MISMATCH")

                (d / "deep_diffs" / "DEEP_MINING_MANIFEST.json").write_text(
                    json.dumps([{"repo": "OrgA/r1", "number": 1, "status": "merged", "file": "p1.json", "sha256": deep_sha, "head_sha": "12" * 20}]) + "\n",
                    encoding="utf-8",
                )
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_DEEP_UNEXPECTED_STATUS")

                # 3. Canonical entry missing / head_sha mismatch / snapshot sha mismatch / heedle issues mismatch
                (d / "deep_diffs" / "DEEP_MINING_MANIFEST.json").write_text(
                    json.dumps([{"repo": "OrgA/r1", "number": 1, "status": "closed_unmerged", "file": "p1.json", "sha256": deep_sha, "head_sha": "12" * 20}]) + "\n",
                    encoding="utf-8",
                )
                spc.CANONICAL_MINED_ENTRIES = [{"repo": "OrgA/r1", "number": 99, "head_sha": "12" * 20, "snapshot_sha256": deep_sha}]
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_CANONICAL_ENTRY_MISSING")

                spc.CANONICAL_MINED_ENTRIES = [{"repo": "OrgA/r1", "number": 1, "head_sha": "34" * 20, "snapshot_sha256": deep_sha}]
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_CANONICAL_SHA_MISMATCH")

                spc.CANONICAL_MINED_ENTRIES = [{"repo": "OrgA/r1", "number": 1, "head_sha": "12" * 20, "snapshot_sha256": "cd" * 32}]
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_CANONICAL_SHA_MISMATCH")

                spc.CANONICAL_MINED_ENTRIES = [{"repo": "OrgA/r1", "number": 1, "head_sha": "12" * 20, "snapshot_sha256": deep_sha}]
                (d / "Moissanite-Labs__heedle_issues.json").write_text('{"a": 1}\n', encoding="utf-8")
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_HEEDLE_ISSUES_MISMATCH")
                (d / "Moissanite-Labs__heedle_issues.json").write_text('[{"number": 2}]\n', encoding="utf-8")
                self._expect_err(lambda: spc.verify_live_intake(d), "INTAKE_HEEDLE_ISSUES_MISMATCH")

                # 4. Synthetic verify_live_intake + live build_certificate + --check --intake-root SUCCESS path
                deep_raw2 = (json.dumps({"head_sha": "56" * 20}) + "\n").encode("utf-8")
                deep_sha2 = hashlib.sha256(deep_raw2).hexdigest()
                (d / "deep_diffs" / "p2.json").write_bytes(deep_raw2)
                (d / "deep_diffs" / "DEEP_MINING_MANIFEST.json").write_text(
                    json.dumps(
                        [
                            {"repo": "OrgA/r1", "number": 1, "status": "open", "file": "p1.json", "sha256": deep_sha, "head_sha": "12" * 20},
                            {"repo": "OrgA/r1", "number": 2, "status": "closed_unmerged", "file": "p2.json", "sha256": deep_sha2, "head_sha": "56" * 20},
                        ]
                    )
                    + "\n",
                    encoding="utf-8",
                )
                (d / "Moissanite-Labs__heedle_issues.json").write_text(
                    json.dumps([{"number": 2}, {"number": 3}, {"number": 6}, {"number": 7}]) + "\n",
                    encoding="utf-8",
                )
                spc.CANONICAL_MINED_ENTRIES = [
                    {
                        "repo": "OrgA/r1",
                        "number": 1,
                        "status": "open",
                        "head_sha": "12" * 20,
                        "snapshot_sha256": deep_sha,
                        "mechanism_class": "DENOMINATOR_OR_WEIGHT_BIAS",
                        "evidence_standing": "EXECUTED_EXACT_WITNESS",
                        "operator_id": "M1_MICROBATCH_WEIGHTING",
                        "honest_novelty": "N0",
                        "prior_art_record": None,
                        "operator_summary": "Synthetic open witness",
                    },
                    {
                        "repo": "OrgA/r1",
                        "number": 2,
                        "status": "closed_unmerged",
                        "head_sha": "56" * 20,
                        "snapshot_sha256": deep_sha2,
                        "mechanism_class": "QUANTILE_OR_INDEX_BOUNDARY",
                        "evidence_standing": "CATALOGED_LEAD",
                        "operator_id": None,
                        "honest_novelty": "N0",
                        "prior_art_record": None,
                        "operator_summary": "Synthetic closed-unmerged lead",
                    },
                ]
                live_info = spc.verify_live_intake(d)
                self.assertTrue(live_info["verified_on_disk"])
                self.assertEqual(live_info["repos_verified"], 1)
                self.assertEqual(live_info["deep_pr_files_verified"], 2)
                self.assertEqual(live_info["deep_open_count"], 1)
                self.assertEqual(live_info["deep_closed_unmerged_count"], 1)
                self.assertEqual(live_info["heedle_issues_verified"], 4)

                live_cert = spc.build_certificate(mode="live", intake_root=d)
                self.assertTrue(live_cert["all_checks_passed"])
                self.assertEqual(live_cert["mode"], "live")
                self.assertTrue(live_cert["intake_verification"]["verified_on_disk"])
                live_p = d / "live_cert.json"
                live_p.write_text(json.dumps(live_cert, indent=2, sort_keys=True) + "\n", encoding="utf-8")

                # Live cert fails without intake_root, succeeds with matching intake_root, fails on tampered live intake_verification
                self._expect_err(lambda: spc.validate_saved_certificate(live_p), "CERT_LIVE_REQUIRES_INTAKE_ROOT")
                check_res = spc.validate_saved_certificate(live_p, intake_root=d)
                self.assertTrue(check_res["valid"])
                self.assertEqual(check_res["mode"], "live")
                out_live = io.StringIO()
                with redirect_stdout(out_live):
                    self.assertEqual(spc.main(["--check", str(live_p), "--intake-root", str(d)]), 0)
                self.assertEqual(json.loads(out_live.getvalue())["mode"], "live")

                tampered_live_body = {
                    k: v for k, v in live_cert.items() if k != "canonical_sha256"
                }
                tampered_live_body["intake_verification"] = {
                    **live_cert["intake_verification"],
                    "verified_on_disk": False,
                }
                tampered_live = {
                    **tampered_live_body,
                    "canonical_sha256": spo.canonical_sha256(tampered_live_body),
                }
                tampered_live_p = d / "tampered_live.json"
                tampered_live_p.write_text(json.dumps(tampered_live, indent=2, sort_keys=True) + "\n", encoding="utf-8")
                self._expect_err(
                    lambda: spc.validate_saved_certificate(tampered_live_p, intake_root=d),
                    "CERT_INTAKE_VERIFICATION_MISMATCH",
                )
            finally:
                spc.PINNED_REPO_SNAPSHOTS = orig_repos
                spc.CANONICAL_MINED_ENTRIES = orig_entries


def run_deterministic_suite() -> int:
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(TestSerendipityPrR5)
    buf = io.StringIO()
    result = unittest.TextTestRunner(stream=buf, verbosity=0).run(suite)
    if not result.wasSuccessful():
        sys.stderr.write(buf.getvalue())
        return 1
    sys.stdout.write(f"PASS AUDIT-111R R5_TESTS={result.testsRun}/{result.testsRun}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(run_deterministic_suite())
