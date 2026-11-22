#!/usr/bin/env python3
"""R5 Mutation-Killing & Adversarial Security Verification Suite for AUDIT-077 (Arm R8-6).

Zero bare `assert` statements. Pure Python 3 stdlib `unittest`.
Designed for 100.0% R5 kill rate under `aletheia v1.4.0 mutate --add-cwd`.
"""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from typing import Any

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

import cpu_arc_governance_audit as mod


def _assert_no_floats(obj: Any, tc: unittest.TestCase, path: str = "root") -> None:
    tc.assertNotIsInstance(obj, float, f"Float leaked at {path}: {obj!r}")
    if isinstance(obj, dict):
        for k, v in obj.items():
            _assert_no_floats(v, tc, f"{path}.{k}")
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            _assert_no_floats(v, tc, f"{path}[{i}]")


def _valid_admission_kwargs() -> dict[str, Any]:
    return {
        "source_code": (
            "import math\n"
            "from fractions import Fraction\n"
            "def solve(ctx):\n"
            "    x = invoke_tool(ctx, 'unit_lookup', {'u': 'C'})\n"
            "    return {'v': Fraction(1, 2), 'x': x}\n"
        ),
        "builder_id": "builder_opus_01",
        "verifier_id": "verifier_aletheia_01",
        "builder_family": "anthropic_opus",
        "verifier_family": "symbolic_aletheia",
        "perturbation_pass_count": 2,
        "r5_mutants_killed": 1,
        "r5_mutants_total": 1,
        "callee_pins": {"convert_temp": "0123456789abcdef" * 4},
        "eval_log_overlap_fraction": Fraction(0, 1),
        "sandbox_cfg": {
            "unshare_all": True,
            "unshare_net": True,
            "clearenv": True,
            "seccomp_enabled": True,
            "worktree_path": "/tmp/worktree_01",
        },
        "allowed_tools": ("unit_lookup",),
    }


class TestExactHelpersAndSources(unittest.TestCase):
    def test_exact_helpers_and_guards(self) -> None:
        self.assertEqual(mod.frac_str(Fraction(4, 6)), "2/3")
        self.assertEqual(mod.frac_decimal_floor(Fraction(5, 2), 0), "2")
        self.assertEqual(mod.frac_decimal_floor(Fraction(-3, 2), 2), "-1.50")
        self.assertEqual(mod.ceil_pos_fraction(Fraction(1, 1)), 1)
        self.assertEqual(mod.ceil_pos_fraction(Fraction(10, 3)), 4)

        with self.assertRaisesRegex(ValueError, "CARC_ERR_EXACT_INT"):
            mod.frac_decimal_floor(Fraction(1, 2), True)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "CARC_ERR_DIGITS"):
            mod.frac_decimal_floor(Fraction(1, 2), -1)
        with self.assertRaisesRegex(ValueError, "CARC_ERR_EXACT_FRAC"):
            mod.ceil_pos_fraction(1.5)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "CARC_ERR_EXACT_FRAC"):
            mod.ceil_pos_fraction(True)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "CARC_ERR_CEIL_POS"):
            mod.ceil_pos_fraction(Fraction(0, 1))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_CEIL_POS"):
            mod.ceil_pos_fraction(Fraction(-1, 2))

    def test_anchor_and_staged_source_verifiers(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            sample = root / "doc.txt"
            sample.write_text("alpha\n  beta  \n", encoding="utf-8")
            self.assertEqual(mod.check_newline_anchors(sample, [(1, "alpha"), (2, "beta")]), 2)
            with self.assertRaisesRegex(ValueError, "CARC_ERR_ANCHOR_FILE_MISSING"):
                mod.check_newline_anchors(root / "missing.txt", [(1, "x")])
            with self.assertRaisesRegex(ValueError, "CARC_ERR_ANCHOR_LINE_OOB"):
                mod.check_newline_anchors(sample, [(0, "alpha")])
            with self.assertRaisesRegex(ValueError, "CARC_ERR_ANCHOR_LINE_OOB"):
                mod.check_newline_anchors(sample, [(4, "beta")])
            with self.assertRaisesRegex(ValueError, "CARC_ERR_ANCHOR_MISMATCH"):
                mod.check_newline_anchors(sample, [(1, "wrong")])

            with self.assertRaisesRegex(ValueError, "CARC_ERR_SOURCE_MISSING"):
                mod.verify_staged_cpu_arc_sources(root)
            for fname in mod.EXPECTED_CPU_ARC_FILES:
                (root / fname).write_bytes(b"corrupt")
            with self.assertRaisesRegex(ValueError, "CARC_ERR_SOURCE_HASH"):
                mod.verify_staged_cpu_arc_sources(root)

            with self.assertRaisesRegex(ValueError, "CARC_ERR_SANDBOX_MISSING"):
                mod.verify_warp_sandbox_script(root / "missing.sh")
            bad_sh = root / "warp-sandbox-exec.sh"
            bad_sh.write_text("#!/bin/sh\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "CARC_ERR_SANDBOX_HASH"):
                mod.verify_warp_sandbox_script(bad_sh)


class TestBreakEvenAndTablesR5(unittest.TestCase):
    def test_breakeven_exact_boundaries(self) -> None:
        # Exact passing boundaries (cache_cost=0, hit_rate=1, error_rates=0, sum=1, penalty=0)
        be_min = mod.compute_cpu_arc_breakeven_exact(
            Fraction(10, 1), Fraction(1, 1), Fraction(0, 1),
            hit_rate=Fraction(1, 1),
            explicit_fallback_rate=Fraction(0, 1),
            silent_error_rate=Fraction(0, 1),
            silent_error_penalty=Fraction(0, 1),
            extra_amortized_build_cost=Fraction(0, 1),
        )
        self.assertTrue(be_min["breaks_even"])
        self.assertEqual(be_min["breakeven_queries"], 10)

        # Exact zero net savings -> does NOT break even (kills <= vs <)
        be_zero = mod.compute_cpu_arc_breakeven_exact(
            Fraction(10, 1), Fraction(1, 1), Fraction(1, 1),
        )
        self.assertFalse(be_zero["breaks_even"])
        self.assertIsNone(be_zero["breakeven_queries"])

        # Exact sum of error rates == 1 boundary passes validation (and yields non-positive savings)
        be_sum1 = mod.compute_cpu_arc_breakeven_exact(
            Fraction(10, 1), Fraction(1, 1), Fraction(0, 1),
            explicit_fallback_rate=Fraction(1, 2),
            silent_error_rate=Fraction(1, 2),
            silent_error_penalty=Fraction(1, 1),
        )
        self.assertFalse(be_sum1["breaks_even"])

        # Refusal guards
        with self.assertRaisesRegex(ValueError, "CARC_ERR_COST_POS"):
            mod.compute_cpu_arc_breakeven_exact(Fraction(0, 1), Fraction(1, 1), Fraction(0, 1))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_COST_POS"):
            mod.compute_cpu_arc_breakeven_exact(Fraction(1, 1), Fraction(0, 1), Fraction(0, 1))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_COST_NONNEG"):
            mod.compute_cpu_arc_breakeven_exact(Fraction(1, 1), Fraction(1, 1), Fraction(-1, 10))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_COST_NONNEG"):
            mod.compute_cpu_arc_breakeven_exact(Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), silent_error_penalty=Fraction(-1, 1))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_COST_NONNEG"):
            mod.compute_cpu_arc_breakeven_exact(Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), extra_amortized_build_cost=Fraction(-1, 1))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_HIT_RATE"):
            mod.compute_cpu_arc_breakeven_exact(Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), hit_rate=Fraction(0, 1))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_HIT_RATE"):
            mod.compute_cpu_arc_breakeven_exact(Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), hit_rate=Fraction(101, 100))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_ERR_RATES"):
            mod.compute_cpu_arc_breakeven_exact(Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), explicit_fallback_rate=Fraction(-1, 10))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_ERR_RATES"):
            mod.compute_cpu_arc_breakeven_exact(Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), silent_error_rate=Fraction(-1, 10))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_ERR_RATES"):
            mod.compute_cpu_arc_breakeven_exact(
                Fraction(1, 1), Fraction(1, 1), Fraction(0, 1),
                explicit_fallback_rate=Fraction(6, 10),
                silent_error_rate=Fraction(5, 10),
            )


class TestAstSandboxFallbackAndAdmissionR5(unittest.TestCase):
    def test_ast_sandbox_blocks_all_escapes(self) -> None:
        ok = mod.audit_cpu_arc_python_ast(
            "import math\nfrom fractions import Fraction\n"
            "def f(ctx):\n    return {'x': invoke_tool(ctx, 'unit_lookup', {})}\n",
            allowed_tools=("unit_lookup",),
        )
        self.assertTrue(ok["ast_clean"])
        self.assertEqual(ok["function_count"], 1)
        self.assertEqual(ok["tools_invoked"], ["unit_lookup"])

        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_TYPE"):
            mod.audit_cpu_arc_python_ast(b"def f(): pass")  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_EMPTY"):
            mod.audit_cpu_arc_python_ast("   \n\t ")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_TOOLS_TYPE"):
            mod.audit_cpu_arc_python_ast("def f(): return 1", allowed_tools="unit_lookup")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_RING0_TOOL"):
            mod.audit_cpu_arc_python_ast("def f(): return 1", allowed_tools=("terminal",))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_SYNTAX"):
            mod.audit_cpu_arc_python_ast("def f(:\n")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_BARE_ASSERT"):
            mod.audit_cpu_arc_python_ast("def f(x):\n    assert x > 0\n    return x\n")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_IMPORT"):
            mod.audit_cpu_arc_python_ast("import os\ndef f(): return 1\n")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_IMPORT"):
            mod.audit_cpu_arc_python_ast("import collections\ndef f(): return collections._sys\n")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_IMPORT"):
            mod.audit_cpu_arc_python_ast("import math.sub\ndef f(): return 1\n")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_REL_IMPORT"):
            mod.audit_cpu_arc_python_ast("from . import foo\ndef f(): return 1\n")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_IMPORT"):
            mod.audit_cpu_arc_python_ast("from subprocess import Popen\ndef f(): return 1\n")
        # CARC-BYPASS-01a: stdlib re-exports like `from fractions import sys` & wildcards blocked
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_IMPORT_SYM"):
            mod.audit_cpu_arc_python_ast("from fractions import sys\ndef f(): return sys\n")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_IMPORT_SYM"):
            mod.audit_cpu_arc_python_ast("from math import *\ndef f(): return 1\n")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_PRIVATE_ATTR"):
            mod.audit_cpu_arc_python_ast("def f(): return ().__class__\n")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_PRIVATE_ATTR"):
            mod.audit_cpu_arc_python_ast("def f(x): return x._sys\n")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_FORBIDDEN_ATTR"):
            mod.audit_cpu_arc_python_ast("def f(ctx): return ctx.invoke_tool('terminal', {})\n", allowed_tools=("unit_lookup",))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_FORBIDDEN_ATTR"):
            mod.audit_cpu_arc_python_ast("def f(ctx): return ctx.do('hijack', {})\n")
        # CARC-BYPASS-01b: dunder names like __builtins__ blocked
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_BUILTIN"):
            mod.audit_cpu_arc_python_ast("def f(): return __builtins__['exec']('import os')\n")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_BUILTIN"):
            mod.audit_cpu_arc_python_ast("def f(s):\n    g = eval\n    return g(s)\n")
        # CARC-BYPASS-02: do() arity, dynamic target, kwargs unpack, aliasing
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_DO_ARITY"):
            mod.audit_cpu_arc_python_ast("def f(ctx): return do(ctx)\n")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_DYNAMIC_DO"):
            mod.audit_cpu_arc_python_ast("def f(ctx, q): return do(ctx, q, {})\n")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_DYNAMIC_DO"):
            mod.audit_cpu_arc_python_ast("def f(ctx, d): return do(ctx, **d)\n")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_DO_ALIAS"):
            mod.audit_cpu_arc_python_ast("def f(ctx):\n    call_do = do\n    return call_do(ctx, 'hijack', {})\n")
        # Valid literal keyword do(ctx, query='convert_temp') passes AST and records target
        ok_do = mod.audit_cpu_arc_python_ast("def f(ctx): return do(ctx, query='convert_temp', payloads={})\n")
        self.assertEqual(ok_do["do_targets"], ["convert_temp"])

        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_TOOL_ARITY"):
            mod.audit_cpu_arc_python_ast("def f(ctx): return invoke_tool(ctx)\n", allowed_tools=("unit_lookup",))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_DYNAMIC_TOOL"):
            mod.audit_cpu_arc_python_ast("def f(ctx, t): return invoke_tool(ctx, t, {})\n", allowed_tools=("unit_lookup",))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_DYNAMIC_TOOL"):
            mod.audit_cpu_arc_python_ast("def f(ctx, d): return invoke_tool(ctx, **d)\n", allowed_tools=("unit_lookup",))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_UNALLOWED_TOOL"):
            mod.audit_cpu_arc_python_ast("def f(ctx): return invoke_tool(ctx, name='terminal', args={})\n", allowed_tools=("unit_lookup",))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_UNALLOWED_TOOL"):
            mod.audit_cpu_arc_python_ast("def f(ctx): return invoke_tool(ctx, 'web_search', {})\n", allowed_tools=("unit_lookup",))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_TOOL_ALIAS"):
            mod.audit_cpu_arc_python_ast("def f(ctx): return [invoke_tool][0](ctx, 'terminal', {})\n", allowed_tools=("unit_lookup",))
        with self.assertRaisesRegex(ValueError, "CARC_ERR_AST_NO_FUNC"):
            mod.audit_cpu_arc_python_ast("x = 1 + 2\n")

    def test_fallback_contract_closes_fig12_bug(self) -> None:
        self.assertTrue(mod.validate_cpu_arc_fallback_contract(False)["fallback_to_source_llm"])
        self.assertTrue(mod.validate_cpu_arc_fallback_contract(None)["fallback_to_source_llm"])
        # Fig. 12 None value triggers fallback instead of false cache hit!
        r_none = mod.validate_cpu_arc_fallback_contract({"work value": None})
        self.assertTrue(r_none["fallback_to_source_llm"])
        self.assertEqual(r_none["reason"], "null_value_sentinel")
        # Fig. 12 unresolved text sentinel triggers fallback even without None!
        r_txt = mod.validate_cpu_arc_fallback_contract({"work with units": "Requires further calculation"})
        self.assertTrue(r_txt["fallback_to_source_llm"])
        self.assertEqual(r_txt["reason"], "unresolved_text_sentinel")
        # CARC-BYPASS-04: nested None and nested unresolved text trigger fallback!
        r_nested_none = mod.validate_cpu_arc_fallback_contract({"result": {"work value": None}, "ok": True})
        self.assertTrue(r_nested_none["fallback_to_source_llm"])
        self.assertEqual(r_nested_none["reason"], "null_value_sentinel")
        r_nested_list = mod.validate_cpu_arc_fallback_contract({"steps": ["step 1", "requires further calculation"]})
        self.assertTrue(r_nested_list["fallback_to_source_llm"])
        self.assertEqual(r_nested_list["reason"], "unresolved_text_sentinel")
        # Valid nested clean dict/list serves cache hit
        r_ok = mod.validate_cpu_arc_fallback_contract({"work value": 0, "steps": ["isochoric", "w = 0"], "meta": {"unit": "J"}})
        self.assertTrue(r_ok["serve_cache"])

        with self.assertRaisesRegex(ValueError, "CARC_ERR_RESULT_SHAPE"):
            mod.validate_cpu_arc_fallback_contract({})
        with self.assertRaisesRegex(ValueError, "CARC_ERR_RESULT_SHAPE"):
            mod.validate_cpu_arc_fallback_contract("string-not-dict")
        with self.assertRaisesRegex(ValueError, "CARC_ERR_RESULT_KEY"):
            mod.validate_cpu_arc_fallback_contract({"  ": 1})
        with self.assertRaisesRegex(ValueError, "CARC_ERR_RESULT_KEY"):
            mod.validate_cpu_arc_fallback_contract({1: "a"})  # type: ignore[dict-item]

    def test_entry_admission_gate_all_boundaries_and_redteam(self) -> None:
        res = mod.evaluate_cpu_arc_entry_admission(**_valid_admission_kwargs())
        self.assertTrue(res["admitted"])
        self.assertEqual(res["r5_kill_ratio"], "1/1")

        # ID type / whitespace / self-approval / same-family judging
        kw = _valid_admission_kwargs(); kw["builder_id"] = 123
        with self.assertRaisesRegex(ValueError, "CARC_ERR_ID_TYPE"):
            mod.evaluate_cpu_arc_entry_admission(**kw)
        kw = _valid_admission_kwargs(); kw["verifier_id"] = " verifier_aletheia_01"
        with self.assertRaisesRegex(ValueError, "CARC_ERR_ID_STRIP"):
            mod.evaluate_cpu_arc_entry_admission(**kw)
        kw = _valid_admission_kwargs(); kw["verifier_id"] = "BUILDER_OPUS_01"
        with self.assertRaisesRegex(ValueError, "CARC_ERR_SELF_APPROVAL"):
            mod.evaluate_cpu_arc_entry_admission(**kw)
        kw = _valid_admission_kwargs(); kw["verifier_family"] = "ANTHROPIC_OPUS"
        with self.assertRaisesRegex(ValueError, "CARC_ERR_SAME_FAMILY_JUDGE"):
            mod.evaluate_cpu_arc_entry_admission(**kw)

        # Perturbation count & R5 mutation kill boundaries
        kw = _valid_admission_kwargs(); kw["perturbation_pass_count"] = 1
        with self.assertRaisesRegex(ValueError, "CARC_ERR_PERTURBATION_MIN"):
            mod.evaluate_cpu_arc_entry_admission(**kw)
        kw = _valid_admission_kwargs(); kw["r5_mutants_total"] = 0; kw["r5_mutants_killed"] = 0
        with self.assertRaisesRegex(ValueError, "CARC_ERR_R5_MUTATE"):
            mod.evaluate_cpu_arc_entry_admission(**kw)
        kw = _valid_admission_kwargs(); kw["r5_mutants_total"] = 5; kw["r5_mutants_killed"] = 4
        with self.assertRaisesRegex(ValueError, "CARC_ERR_R5_MUTATE"):
            mod.evaluate_cpu_arc_entry_admission(**kw)

        # Callee SHA-256 pinning (anti do()-hijack + CARC-BYPASS-02 unmatched dummy pin)
        kw = _valid_admission_kwargs(); kw["callee_pins"] = ["bad"]  # type: ignore[assignment]
        with self.assertRaisesRegex(ValueError, "CARC_ERR_CALLEE_PINS_TYPE"):
            mod.evaluate_cpu_arc_entry_admission(**kw)
        kw = _valid_admission_kwargs()
        kw["source_code"] = "def solve(ctx): return do(ctx, 'sub_fn', {})\n"
        kw["callee_pins"] = {"unrelated_dummy": "a" * 64}
        with self.assertRaisesRegex(ValueError, "CARC_ERR_UNPINNED_DO_DISPATCH"):
            mod.evaluate_cpu_arc_entry_admission(**kw)
        # Matching pin admits cleanly
        kw["callee_pins"] = {"sub_fn": "a" * 64}
        self.assertTrue(mod.evaluate_cpu_arc_entry_admission(**kw)["admitted"])
        kw = _valid_admission_kwargs(); kw["callee_pins"] = {"fn": "A" * 64}
        with self.assertRaisesRegex(ValueError, "CARC_ERR_CALLEE_PIN_HEX"):
            mod.evaluate_cpu_arc_entry_admission(**kw)

        # Eval-log leakage (CARC-03 Appendix D 20% harvest blocked!)
        kw = _valid_admission_kwargs(); kw["eval_log_overlap_fraction"] = Fraction(-1, 10)
        with self.assertRaisesRegex(ValueError, "CARC_ERR_OVERLAP_RANGE"):
            mod.evaluate_cpu_arc_entry_admission(**kw)
        kw = _valid_admission_kwargs(); kw["eval_log_overlap_fraction"] = Fraction(11, 10)
        with self.assertRaisesRegex(ValueError, "CARC_ERR_OVERLAP_RANGE"):
            mod.evaluate_cpu_arc_entry_admission(**kw)
        kw = _valid_admission_kwargs(); kw["eval_log_overlap_fraction"] = Fraction(1, 5)
        with self.assertRaisesRegex(ValueError, "CARC_ERR_EVAL_LEAKAGE"):
            mod.evaluate_cpu_arc_entry_admission(**kw)

        # Sandbox config & protected host path boundary (warp-sandbox-exec.sh)
        kw = _valid_admission_kwargs(); kw["sandbox_cfg"] = "bad"  # type: ignore[assignment]
        with self.assertRaisesRegex(ValueError, "CARC_ERR_SANDBOX_CFG_TYPE"):
            mod.evaluate_cpu_arc_entry_admission(**kw)
        kw = _valid_admission_kwargs(); kw["sandbox_cfg"]["unshare_net"] = 1
        with self.assertRaisesRegex(ValueError, "CARC_ERR_EXACT_BOOL"):
            mod.evaluate_cpu_arc_entry_admission(**kw)
        kw = _valid_admission_kwargs(); kw["sandbox_cfg"]["seccomp_enabled"] = False
        with self.assertRaisesRegex(ValueError, "CARC_ERR_SANDBOX_FLAG"):
            mod.evaluate_cpu_arc_entry_admission(**kw)
        for bad_wt in ("relative/path", "/", "/tmp/worktree_01/", "/etc//warp", "/etc\\warp", "/tmp/a\x00b", "/tmp/../etc/warp", "/etc/./warp/keys", "/var/./lib/warp-ledger"):
            kw = _valid_admission_kwargs(); kw["sandbox_cfg"]["worktree_path"] = bad_wt
            with self.assertRaisesRegex(ValueError, "CARC_ERR_SANDBOX_WORKTREE"):
                mod.evaluate_cpu_arc_entry_admission(**kw)
        for prot_wt in ("/etc/warp", "/etc/warp/keys/sub", "/var/lib/warp"):
            kw = _valid_admission_kwargs(); kw["sandbox_cfg"]["worktree_path"] = prot_wt
            with self.assertRaisesRegex(ValueError, "CARC_ERR_SANDBOX_PROTECTED"):
                mod.evaluate_cpu_arc_entry_admission(**kw)


class TestEndToEndLiveAndStandaloneCpuArc(unittest.TestCase):
    def test_live_and_standalone_audit(self) -> None:
        cert = mod.run_audit(standalone=True)
        _assert_no_floats(cert, self)
        self.assertEqual(cert["staged_source_verification"]["mode"], "standalone")
        self.assertEqual(cert["staged_source_verification"]["verbatim_anchors_cataloged"], 24)
        self.assertEqual(cert["warp_sandbox_verification"]["verbatim_anchors_cataloged"], 7)

        sibling_pdf_dir = Path(__file__).resolve().parent.parent / "repos" / "cpu-arc"
        if sibling_pdf_dir.is_dir():
            live_cert = mod.run_audit(standalone=False)
            _assert_no_floats(live_cert, self)
            self.assertEqual(live_cert["staged_source_verification"]["files_verified"], 3)
            self.assertEqual(live_cert["staged_source_verification"]["verbatim_anchors_verified"], 24)
            self.assertEqual(live_cert["warp_sandbox_verification"]["verbatim_anchors_verified"], 7)
            self.assertEqual(live_cert["carc01_tables_and_breakeven_audit"], cert["carc01_tables_and_breakeven_audit"])
            self.assertEqual(live_cert["carc02_worked_example_defects"], cert["carc02_worked_example_defects"])

        tbl = cert["carc01_tables_and_breakeven_audit"]
        self.assertEqual(tbl["benchmarks_audited"], 8)
        self.assertTrue(tbl["all_8_builder_token_deficit_negative"])
        self.assertTrue(tbl["all_8_b_a_strictly_overpredicts_reported"])
        self.assertTrue(tbl["all_8_b_d_strictly_underpredicts_reported"])
        self.assertFalse(tbl["gsm8k_silent_error_collapse_witness"]["breaks_even"])
        self.assertEqual(tbl["gsm8k_silent_error_collapse_witness"]["net_savings_per_query_frac"], "-1/8000")

        by_name = {r["benchmark"]: r for r in tbl["rows"]}
        self.assertEqual(by_name["AIME '25"]["breakeven_ideal_queries"], 13)
        self.assertEqual(by_name["GSM8K"]["breakeven_ideal_queries"], 90)
        self.assertEqual(by_name["GSM8K"]["breakeven_half_hit_queries"], 179)

        d2 = cert["carc02_worked_example_defects"]
        self.assertEqual(d2["appendix_a_celsius_offset_delta_k_frac"], "3/20")
        self.assertEqual(d2["appendix_a_fahrenheit_32f_rel_err_frac"], "4823/5463")
        self.assertEqual(d2["appendix_a_m3_vs_dm3_pressure_error_factor"], "1000/1")
        self.assertEqual(d2["appendix_b_negation_false_positive_count"], 4)
        self.assertTrue(d2["appendix_b_fig12_breaks_fig1_fallback_contract"])
        self.assertEqual(len(json.dumps(cert, allow_nan=False)), len(json.dumps(cert)))


if __name__ == "__main__":
    unittest.main()
