#!/usr/bin/env python3
"""R1-R5, boundary, red-team bypass, and 100% mutation-kill test suite for AUDIT-080.

Runs cleanly under `python3 -I -O -B -W error test_score_centering_r5.py`.
Zero floats; zero bare assert statements.
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

import score_centering_tomography as sct


class TestScoreCenteringPrimitives(unittest.TestCase):
    def test_exact_type_and_choice_guards(self) -> None:
        self.assertEqual(sct.frac_str(Fraction(3, 4)), "3/4")
        self.assertEqual(sct.frac_str(2), "2/1")
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"exact-fraction:frac_str"):
            sct.frac_str(True)  # type: ignore[arg-type]
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"exact-fraction:frac_str"):
            sct.frac_str("1/2")  # type: ignore[arg-type]
        self.assertEqual(sct.vec_frac_str([Fraction(1, 2), Fraction(-3, 1)]), ["1/2", "-3/1"])

    def test_simplex_and_vector_refusals(self) -> None:
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"simplex-len:trainer_probs"):
            sct.softmax_scores([Fraction(1, 1)])
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"simplex-pos:trainer_probs\[1\]"):
            sct.softmax_scores([Fraction(1, 1), Fraction(0, 1)])
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"simplex-sum:trainer_probs"):
            sct.softmax_scores([Fraction(1, 2), Fraction(1, 3)])
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"simplex-nonneg:x\[0\]"):
            sct._validate_simplex([Fraction(-1, 2), Fraction(3, 2)], "x", allow_zero=True)
        self.assertEqual(
            sct._validate_simplex([Fraction(0, 1), Fraction(1, 1)], "x", allow_zero=True),
            (Fraction(0, 1), Fraction(1, 1)),
        )

        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"expected-vec-len"):
            sct.expected_vec([], [])
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"expected-vec-len"):
            sct.expected_vec([Fraction(1, 1)], [(Fraction(1, 1),), (Fraction(0, 1),)])
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"expected-vec-dim"):
            sct.expected_vec(
                [Fraction(1, 2), Fraction(1, 2)],
                [(Fraction(1, 1), Fraction(0, 1)), (Fraction(1, 1),)],
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"vec-sub-len"):
            sct.vec_sub([Fraction(1, 1)], [Fraction(1, 1), Fraction(0, 1)])
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"vec-add-len"):
            sct.vec_add([Fraction(1, 1)], [Fraction(1, 1), Fraction(0, 1)])
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"vec-linf-empty"):
            sct.vec_linf([])
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"exact-fraction:vec_scale"):
            sct.vec_scale(False, [Fraction(1, 1)])  # type: ignore[arg-type]

    def test_tail_scale_alpha_exact_and_boundaries(self) -> None:
        # Exact zero boundary for all 4 modes
        for mode in sct.ALLOWED_CORRECTION_MODES:
            self.assertEqual(sct.tail_scale_alpha(Fraction(0, 1), mode), Fraction(0, 1))
        # Vanilla SC unbounded
        self.assertEqual(sct.tail_scale_alpha(Fraction(7, 2), "none"), Fraction(7, 2))
        # TIS: alpha(rho) = min(1, 2*rho) -> boundary at rho = 1/2
        self.assertEqual(sct.tail_scale_alpha(Fraction(1, 4), "tis"), Fraction(1, 2))
        self.assertEqual(sct.tail_scale_alpha(Fraction(1, 2), "tis"), Fraction(1, 1))
        self.assertEqual(sct.tail_scale_alpha(Fraction(100, 1), "tis"), Fraction(1, 1))
        # MIS: 1 iff 1/5 <= rho <= 2 (exact closed boundaries!)
        self.assertEqual(sct.tail_scale_alpha(Fraction(1, 5) - Fraction(1, 100), "mis"), Fraction(0, 1))
        self.assertEqual(sct.tail_scale_alpha(Fraction(1, 5), "mis"), Fraction(1, 1))
        self.assertEqual(sct.tail_scale_alpha(Fraction(2, 1), "mis"), Fraction(1, 1))
        self.assertEqual(sct.tail_scale_alpha(Fraction(2, 1) + Fraction(1, 100), "mis"), Fraction(0, 1))
        # Unclipped IS: 1 for any rho > 0
        self.assertEqual(sct.tail_scale_alpha(Fraction(3, 7), "unclipped_is"), Fraction(1, 1))
        # Refusals: negative rho, bad mode, whitespace/case mode
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"rho-nonneg"):
            sct.tail_scale_alpha(Fraction(-1, 10), "none")
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"exact-choice:mode"):
            sct.tail_scale_alpha(Fraction(1, 1), "TIS")
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"exact-choice:mode"):
            sct.tail_scale_alpha(Fraction(1, 1), " tis ")


class TestScoreCenteringPillars(unittest.TestCase):
    def test_pillar1_exact_values(self) -> None:
        p1 = sct.analyze_pillar1_drift_kl_bias()
        kl = p1["kl_direction_disproof_sc_zhihu_01"]
        self.assertEqual(kl["expected_score_under_p"], ["0/1", "0/1", "0/1"])
        self.assertEqual(kl["expected_score_under_q"], ["-1/4", "1/4", "0/1"])
        self.assertEqual(kl["grad_forward_kl_q_p"], ["1/4", "-1/4", "0/1"])
        self.assertEqual(kl["neg_grad_forward_kl_q_p"], ["-1/4", "1/4", "0/1"])
        self.assertTrue(kl["equals_neg_forward_kl_grad"])
        self.assertEqual(kl["grad_reverse_kl_p_q_div_ln2"], ["3/8", "-5/16", "-1/16"])
        self.assertEqual(kl["collinearity_det_coord_0_2"], "1/64")
        self.assertFalse(kl["equals_any_scalar_multiple_of_reverse_kl_grad"])

        ds = p1["drift_signal_invariance"]
        self.assertEqual(ds["mean_advantage_q"], "1/1")
        self.assertEqual(ds["drift_vec"], ["-1/4", "1/4", "0/1"])
        self.assertEqual(ds["signal_cov_raw"], ["3/4", "-1/2", "-1/4"])
        self.assertEqual(ds["signal_cov_centered"], ["3/4", "-1/2", "-1/4"])
        self.assertEqual(ds["g_off"], ["1/2", "-1/4", "-1/4"])
        self.assertEqual(ds["g_sc"], ["3/4", "-1/2", "-1/4"])
        self.assertTrue(ds["zero_drift_exact"])
        self.assertTrue(ds["signal_invariance_exact"])

        b = p1["bias_sign_and_witnesses_sc_zhihu_02"]
        self.assertEqual(b["delta_negative_sc_better"]["delta_l1_exact"], "-1/2")
        self.assertEqual(b["delta_negative_sc_better"]["delta_l2_sq_exact"], "-1/8")
        self.assertEqual(b["delta_negative_sc_better"]["delta_linf_exact"], "-1/4")
        self.assertTrue(b["delta_negative_sc_better"]["err_sc_equals_delta_cov"])
        self.assertTrue(b["delta_negative_sc_better"]["err_off_equals_delta_cov_minus_drift"])
        pos = b["delta_positive_sc_worse_and_zhihu_sign_flip"]
        self.assertEqual(pos["err_off_exact"], ["0/1", "0/1"])
        self.assertEqual(pos["err_sc"], ["-1/4", "1/4"])
        self.assertEqual(pos["delta_l1_exact"], "1/2")
        self.assertEqual(pos["delta_l2_sq_exact"], "1/8")
        self.assertEqual(pos["delta_linf_exact"], "1/4")
        self.assertEqual(pos["delta_l1_zhihu_l112_bug"], "-1/2")
        self.assertTrue(pos["err_sc_equals_delta_cov"])
        self.assertTrue(pos["err_off_equals_delta_cov_minus_drift"])
        self.assertEqual(b["advantage_mismatch_identity"]["delta_l1_exact"], "0/1")

    def test_pillar2_exact_values(self) -> None:
        p2 = sct.analyze_pillar2_topk_singularity_and_tail_scales()
        tk = p2["topk_exact_identities"]
        self.assertEqual(tk["rho"], "2/1")
        self.assertEqual(tk["head_residuals"], ["-3/4", "-1/4"])
        self.assertEqual(tk["head_residual_sum"], "-1/1")
        self.assertTrue(tk["head_residual_sum_equals_one_minus_rho"])
        self.assertEqual(tk["q_hat_reconstructed"], ["1/4", "1/4", "1/4", "1/4"])
        self.assertEqual(tk["q_hat_mass"], "1/1")
        self.assertEqual(tk["grad_topk_correction"], ["-1/4", "0/1", "1/8", "1/8"])
        self.assertTrue(tk["grad_equals_q_hat_minus_p"])
        self.assertEqual(tk["full_vocab_logit_grad_sum"], "0/1")
        self.assertEqual(tk["drift_under_q_hat"], ["0/1", "0/1", "0/1", "0/1"])
        self.assertEqual(tk["drift_under_true_q_tail_shape_bias"], ["0/1", "0/1", "1/8", "-1/8"])
        self.assertTrue(tk["tail_shape_matches_closed_form"])
        self.assertEqual(tk["tail_shape_bias_l1"], "1/4")

        sg = p2["singularity_and_eps_blowup_sc_sing_01"]
        self.assertEqual(sg["rho_exact_unfloored"], "1000000/1")
        self.assertEqual(sg["rho_eps_floored"], "100000/1")
        self.assertEqual(sg["reconstructed_q_hat_total_mass"], "91/100")
        self.assertEqual(sg["simplex_mass_deficit"], "9/100")

        rows = p2["tail_scale_dichotomy"]
        self.assertEqual(len(rows), 7)
        self.assertEqual(rows[0]["alpha_mis_sc"], "0/1")
        self.assertEqual(rows[1]["alpha_mis_sc"], "1/1")
        self.assertEqual(rows[-1]["alpha_vanilla_sc"], "100000/1")
        self.assertEqual(rows[-1]["alpha_tis_sc"], "1/1")
        self.assertEqual(rows[-1]["alpha_mis_sc"], "0/1")

    def test_pillar3_repo_code_oracles(self) -> None:
        p3 = sct.analyze_pillar3_repo_code_oracles()
        self.assertEqual(p3["SC-CODE-01_double_centering"]["single_centered_drift"], ["0/1", "0/1", "0/1"])
        self.assertEqual(p3["SC-CODE-01_double_centering"]["double_centered_drift"], ["1/4", "-1/4", "0/1"])
        self.assertTrue(p3["SC-CODE-01_double_centering"]["drift_sign_flipped"])
        c2 = p3["SC-CODE-02_seq_is_breaks_zero_drift"]
        self.assertTrue(c2["offdiag_score_seq_zero"])
        self.assertEqual(c2["topr_readme_l133_adv_pos1_expected_grad"], ["0/1", "0/1"])
        self.assertEqual(c2["topr_readme_l133_adv_neg1_expected_grad"], ["-3/16", "3/16"])
        self.assertEqual(c2["topr_readme_l133_adv_neg1_drift_l1"], "3/8")
        self.assertEqual(c2["gspo_readme_l132_adv_pos1_expected_grad"], ["-1/8", "1/8"])
        self.assertEqual(c2["gspo_readme_l132_adv_pos1_drift_l1"], "1/4")
        self.assertEqual(c2["gspo_readme_l132_adv_neg1_expected_grad"], ["-3/8", "3/8"])
        self.assertEqual(c2["gspo_readme_l132_adv_neg1_drift_l1"], "3/4")
        c3 = p3["SC-CODE-03_zero_tail_and_missing_support"]
        self.assertEqual(c3["spurious_positive_kl_lower_bound"], "1/50000")
        self.assertEqual(c3["buggy_remaining_drift"], ["1/8", "1/8", "-1/8", "-1/8"])
        self.assertEqual(c3["hardened_alpha"], "0/1")
        self.assertEqual(c3["hardened_remaining_drift"], ["0/1", "0/1", "0/1", "0/1"])
        self.assertTrue(p3["SC-CODE-05_tautological_k_eq_v_minus_1"]["q_hat_identically_equals_q"])

    def test_pillar4_hardened_gate_and_bridges(self) -> None:
        p4 = sct.analyze_pillar4_hardened_gate_and_bridges()
        r = p4["hardened_gate_receipts"]
        self.assertEqual(r["healthy_exact_centered"]["gate_status"], "EXACT_CENTERED")
        self.assertEqual(r["healthy_exact_centered"]["residuals"], ["-3/4", "-1/4"])
        self.assertTrue(r["healthy_exact_centered"]["residual_l1_within_bound"])
        self.assertEqual(r["healthy_exact_centered"]["correction_logit_grad_sum"], "0/1")
        self.assertEqual(r["peaked_trainer_damped_fallback"]["gate_status"], "DAMPED_FALLBACK_REQUIRED")
        self.assertEqual(r["peaked_trainer_damped_fallback"]["rho_effective"], "10/1")
        self.assertTrue(r["peaked_trainer_damped_fallback"]["residual_l1_within_bound"])
        self.assertEqual(r["peaked_trainer_damped_fallback"]["correction_logit_grad_sum"], "0/1")
        self.assertEqual(r["zero_tail_unclipped_is_guarded"]["gate_status"], "ZERO_TAIL_SUPPORT_GUARDED")
        self.assertEqual(r["zero_tail_unclipped_is_guarded"]["alpha"], "0/1")
        self.assertEqual(r["zero_tail_unclipped_is_guarded"]["residuals"], ["1/4", "1/4"])
        self.assertTrue(r["zero_tail_unclipped_is_guarded"]["residual_l1_within_bound"])
        self.assertEqual(r["zero_tail_unclipped_is_guarded"]["correction_logit_grad_sum"], "0/1")

        b1 = p4["bridge_audit_073r_songe_sng01"]
        self.assertEqual(b1["off_policy_drift"], ["3/16", "-3/16", "0/1"])
        self.assertTrue(b1["matches_plus_three_quarters_grad_kl"])
        b2 = p4["bridge_audit_074r_inkling_loom_ir03"]
        self.assertEqual(b2["loom_kept_vocab_fraction"], "32/100029")
        self.assertEqual(b2["hidden_pre_truncation_tail_mass_tv"], "35/64")
        self.assertEqual(b2["centering_mismatch_l1"], "35/32")


class TestRedTeamHardenedContractAndGate(unittest.TestCase):
    def _valid_spec(self, **overrides: object) -> dict[str, object]:
        base: dict[str, object] = {
            "batch_mode": "topk_head",
            "has_full_vocab": False,
            "has_topk_head": True,
            "is_level": "token",
            "is_stat": "ratio",
            "score_center": True,
        }
        base.update(overrides)
        return base

    def test_batch_contract_accepts_and_blocks_all_bypasses(self) -> None:
        ok_topk = sct.validate_batch_contract(self._valid_spec())
        self.assertEqual(ok_topk["contract_status"], "VALID")
        ok_full = sct.validate_batch_contract(
            self._valid_spec(batch_mode="full_vocab", has_full_vocab=True, has_topk_head=False, is_level="none")
        )
        self.assertEqual(ok_full["batch_mode"], "full_vocab")
        ok_disabled = sct.validate_batch_contract(
            self._valid_spec(
                batch_mode="none",
                has_full_vocab=False,
                has_topk_head=False,
                is_level="seq_mean",
                is_stat="tv",
                score_center=False,
            )
        )
        self.assertFalse(ok_disabled["score_center"])
        self.assertEqual(ok_disabled["batch_mode"], "none")

        # Red-team refusals
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"batch-spec-dict"):
            sct.validate_batch_contract(["not-a-dict"])
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"batch-spec-unknown-keys:extra"):
            sct.validate_batch_contract(self._valid_spec(extra=1))
        missing_spec = self._valid_spec()
        del missing_spec["is_stat"]
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"batch-spec-missing-keys:is_stat"):
            sct.validate_batch_contract(missing_spec)
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"exact-choice:batch_mode"):
            sct.validate_batch_contract(self._valid_spec(batch_mode=" topk_head "))
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"batch-bool:has_full_vocab"):
            sct.validate_batch_contract(self._valid_spec(has_full_vocab=0))
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"batch-bool:has_topk_head"):
            sct.validate_batch_contract(self._valid_spec(has_topk_head=1))
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"batch-bool:score_center"):
            sct.validate_batch_contract(self._valid_spec(score_center=1))
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"sc-missing-sampler-logprobs"):
            sct.validate_batch_contract(
                self._valid_spec(batch_mode="none", has_full_vocab=False, has_topk_head=False)
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"sc-double-centering-forbidden"):
            sct.validate_batch_contract(self._valid_spec(has_full_vocab=True, has_topk_head=True))
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"batch-mode-mismatch"):
            sct.validate_batch_contract(self._valid_spec(batch_mode="full_vocab", has_full_vocab=False, has_topk_head=True))
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"batch-mode-mismatch"):
            sct.validate_batch_contract(
                self._valid_spec(
                    score_center=False, batch_mode="full_vocab", has_full_vocab=False, has_topk_head=True
                )
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"batch-ambiguous-vocab-sources"):
            sct.validate_batch_contract(
                self._valid_spec(
                    score_center=False, batch_mode="full_vocab", has_full_vocab=True, has_topk_head=True
                )
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"is-none-requires-ratio"):
            sct.validate_batch_contract(
                self._valid_spec(
                    score_center=False,
                    batch_mode="none",
                    has_full_vocab=False,
                    has_topk_head=False,
                    is_level="none",
                    is_stat="tv",
                )
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"sc-seq-level-is-forbidden"):
            sct.validate_batch_contract(self._valid_spec(is_level="seq_mean"))
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"sc-seq-level-is-forbidden"):
            sct.validate_batch_contract(self._valid_spec(is_level="seq_sum"))
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"sc-tv-stat-forbidden"):
            sct.validate_batch_contract(self._valid_spec(is_stat="tv"))
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"seq-sum-requires-ratio"):
            sct.validate_batch_contract(
                self._valid_spec(
                    score_center=False,
                    batch_mode="none",
                    has_full_vocab=False,
                    has_topk_head=False,
                    is_level="seq_sum",
                    is_stat="tv",
                )
            )

    def test_hardened_gate_modes_and_exact_boundaries(self) -> None:
        p = (Fraction(1, 2), Fraction(1, 4), Fraction(1, 8), Fraction(1, 8))
        # Mode coverage: tis with exact boundaries p_tail == tail_floor, rho == rho_max, pigeonhole ==
        res_tis = sct.evaluate_hardened_topk_score_centering(
            trainer_probs=p,
            sampler_head_probs=(Fraction(1, 4), Fraction(1, 4)),
            topk_ids=(0, 1),
            sampled_token=3,
            advantage=Fraction(2, 1),
            correction_mode="tis",
            tail_floor=Fraction(1, 4),
            rho_max=Fraction(2, 1),
        )
        # p_tail = 1/4 == tail_floor, q_tail = 1/2, rho = 2 == rho_max -> EXACT_CENTERED!
        self.assertEqual(res_tis["gate_status"], "EXACT_CENTERED")
        self.assertEqual(res_tis["alpha"], "1/1")
        # token 0: p/q = 2 -> eff_mass = 1/2; token 1: p/q = 1 -> eff_mass = 1/4 -> residuals = (0, 0)
        self.assertEqual(res_tis["residuals"], ["0/1", "0/1"])

        # Valid top-K head containing a zero-prob tied token (q_head = (1, 0), q_tail = 0)
        res_zero_head_tok = sct.evaluate_hardened_topk_score_centering(
            trainer_probs=p,
            sampler_head_probs=(Fraction(1, 1), Fraction(0, 1)),
            topk_ids=(0, 1),
            sampled_token=0,
            advantage=Fraction(1, 1),
            correction_mode="tis",
        )
        self.assertEqual(res_zero_head_tok["gate_status"], "ZERO_TAIL_SUPPORT_GUARDED")
        self.assertEqual(res_zero_head_tok["residuals"], ["1/2", "0/1"])

        # MIS with genuine top-2 head: token 0 ratio = (1/12)/(1/3) = 1/4 < 1/2 (dropped -> 0), token 1 ratio = 1 (kept -> 1/3)
        p_mis_drop = (Fraction(1, 12), Fraction(1, 3), Fraction(7, 24), Fraction(7, 24))
        res_mis = sct.evaluate_hardened_topk_score_centering(
            trainer_probs=p_mis_drop,
            sampler_head_probs=(Fraction(1, 3), Fraction(1, 3)),
            topk_ids=(0, 1),
            sampled_token=1,
            advantage=Fraction(1, 1),
            correction_mode="mis",
        )
        # q_tail = 1/3, p_tail = 7/12 -> rho = 4/7 in [1/5, 2] -> alpha = 1
        self.assertEqual(res_mis["alpha"], "1/1")
        self.assertEqual(res_mis["residuals"], ["-1/12", "0/1"])

        # MIS exact closed boundaries ratio = 1/2 and ratio = 5 on genuine top-2 head (V=6, n_tail=4)
        p_mis = (
            Fraction(1, 4),
            Fraction(5, 8),
            Fraction(1, 32),
            Fraction(1, 32),
            Fraction(1, 32),
            Fraction(1, 32),
        )
        res_mis_bd = sct.evaluate_hardened_topk_score_centering(
            trainer_probs=p_mis,
            sampler_head_probs=(Fraction(1, 2), Fraction(1, 8)),
            topk_ids=(0, 1),
            sampled_token=1,
            advantage=Fraction(1, 1),
            correction_mode="mis",
        )
        # 4 * min(1/2, 1/8) = 1/2 >= 3/8 (valid top-2); token 0 ratio=1/2 (kept -> 1/4); token 1 ratio=5 (kept -> 5/8)
        # rho = (3/8)/(1/8) = 3 > 2 -> MIS alpha = 0
        self.assertEqual(res_mis_bd["alpha"], "0/1")
        self.assertEqual(res_mis_bd["residuals"], ["1/4", "5/8"])

        # Damped branch triggered strictly by rho > rho_max even when p_tail >= tail_floor
        p_cap = (Fraction(7, 16), Fraction(7, 16), Fraction(1, 16), Fraction(1, 16))
        res_rho_cap = sct.evaluate_hardened_topk_score_centering(
            trainer_probs=p_cap,
            sampler_head_probs=(Fraction(1, 3), Fraction(1, 3)),
            topk_ids=(0, 1),
            sampled_token=0,
            advantage=Fraction(1, 1),
            correction_mode="none",
            tail_floor=Fraction(1, 20),
            rho_max=Fraction(2, 1),
        )
        # p_tail = 1/8 >= 1/20, q_tail = 1/3 -> rho = 8/3 > 2, damped = (23/60)/(7/40) = 46/21 > 2 -> capped to 2
        self.assertEqual(res_rho_cap["gate_status"], "DAMPED_FALLBACK_REQUIRED")
        self.assertEqual(res_rho_cap["rho_effective"], "2/1")

        # Damped branch where damped formula < rho_max (verifies min(rho_max, damped) takes damped!)
        res_damped_below_cap = sct.evaluate_hardened_topk_score_centering(
            trainer_probs=(Fraction(1, 2), Fraction(49, 100), Fraction(1, 200), Fraction(1, 200)),
            sampler_head_probs=(Fraction(4, 10), Fraction(4, 10)),
            topk_ids=(0, 1),
            sampled_token=0,
            advantage=Fraction(1, 1),
            correction_mode="none",
            tail_floor=Fraction(1, 10),
            rho_max=Fraction(10, 1),
        )
        # p_tail = 1/100 < 1/10, q_tail = 1/5 -> damped = (1/5 + 1/10)/(1/100 + 1/10) = 30/11 < 10
        self.assertEqual(res_damped_below_cap["gate_status"], "DAMPED_FALLBACK_REQUIRED")
        self.assertEqual(res_damped_below_cap["rho_effective"], "30/11")

        # Exact closed boundaries: rho_max == 1 and qv == 1 (M048, M051)
        res_bd_exact = sct.evaluate_hardened_topk_score_centering(
            trainer_probs=p,
            sampler_head_probs=(Fraction(1, 1),),
            topk_ids=(0,),
            sampled_token=0,
            advantage=Fraction(1, 1),
            correction_mode="none",
            rho_max=Fraction(1, 1),
        )
        self.assertEqual(res_bd_exact["gate_status"], "ZERO_TAIL_SUPPORT_GUARDED")
        self.assertEqual(res_bd_exact["q_tail"], "0/1")

    def test_hardened_gate_red_team_refusals(self) -> None:
        p = (Fraction(1, 2), Fraction(1, 4), Fraction(1, 4))
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"topk-ids-len"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p, sampler_head_probs=(), topk_ids=(), sampled_token=0, advantage=Fraction(1, 1)
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"topk-ids-len"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p,
                sampler_head_probs=(Fraction(1, 2), Fraction(1, 4), Fraction(1, 4)),
                topk_ids=(0, 1, 2),
                sampled_token=0,
                advantage=Fraction(1, 1),
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"sampler-head-len"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p,
                sampler_head_probs=(Fraction(1, 2),),
                topk_ids=(0, 1),
                sampled_token=0,
                advantage=Fraction(1, 1),
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"exact-int:topk_ids\[0\]"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p,
                sampler_head_probs=(Fraction(1, 2),),
                topk_ids=(True,),  # type: ignore[arg-type]
                sampled_token=0,
                advantage=Fraction(1, 1),
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"topk-id-range:-1"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p, sampler_head_probs=(Fraction(1, 2),), topk_ids=(-1,), sampled_token=0, advantage=Fraction(1, 1)
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"topk-id-range:3"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p, sampler_head_probs=(Fraction(1, 2),), topk_ids=(3,), sampled_token=0, advantage=Fraction(1, 1)
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"topk-id-duplicate:1"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p,
                sampler_head_probs=(Fraction(1, 4), Fraction(1, 4)),
                topk_ids=(1, 1),
                sampled_token=0,
                advantage=Fraction(1, 1),
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"sampled-token-range"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p, sampler_head_probs=(Fraction(1, 2),), topk_ids=(0,), sampled_token=3, advantage=Fraction(1, 1)
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"sampled-token-range"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p, sampler_head_probs=(Fraction(1, 2),), topk_ids=(0,), sampled_token=-1, advantage=Fraction(1, 1)
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"tail-floor-range"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p,
                sampler_head_probs=(Fraction(1, 2),),
                topk_ids=(0,),
                sampled_token=0,
                advantage=Fraction(1, 1),
                tail_floor=Fraction(0, 1),
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"tail-floor-range"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p,
                sampler_head_probs=(Fraction(1, 2),),
                topk_ids=(0,),
                sampled_token=0,
                advantage=Fraction(1, 1),
                tail_floor=Fraction(1, 1),
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"rho-max-ge-one"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p,
                sampler_head_probs=(Fraction(1, 2),),
                topk_ids=(0,),
                sampled_token=0,
                advantage=Fraction(1, 1),
                rho_max=Fraction(9, 10),
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"sampler-head-range:0"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p,
                sampler_head_probs=(Fraction(-1, 10),),
                topk_ids=(0,),
                sampled_token=0,
                advantage=Fraction(1, 1),
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"sampler-head-range:0"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p,
                sampler_head_probs=(Fraction(11, 10),),
                topk_ids=(0,),
                sampled_token=0,
                advantage=Fraction(1, 1),
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"sampler-head-sum-exceeds-one"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p,
                sampler_head_probs=(Fraction(3, 4), Fraction(1, 2)),
                topk_ids=(0, 1),
                sampled_token=0,
                advantage=Fraction(1, 1),
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"sampler-head-zero-mass"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p,
                sampler_head_probs=(Fraction(0, 1), Fraction(0, 1)),
                topk_ids=(0, 1),
                sampled_token=2,
                advantage=Fraction(1, 1),
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"topk-pigeonhole-dominance"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=(Fraction(1, 2), Fraction(1, 4), Fraction(1, 8), Fraction(1, 8)),
                sampler_head_probs=(Fraction(1, 100), Fraction(1, 100)),
                topk_ids=(0, 1),
                sampled_token=2,
                advantage=Fraction(1, 1),
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"sampled-token-zero-sampler-prob"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p,
                sampler_head_probs=(Fraction(0, 1), Fraction(1, 1)),
                topk_ids=(0, 1),
                sampled_token=0,
                advantage=Fraction(1, 1),
            )
        with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"sampled-tail-token-zero-q-tail"):
            sct.evaluate_hardened_topk_score_centering(
                trainer_probs=p,
                sampler_head_probs=(Fraction(1, 2), Fraction(1, 2)),
                topk_ids=(0, 1),
                sampled_token=2,
                advantage=Fraction(1, 1),
            )


class TestLiveRepoAuditAndCLI(unittest.TestCase):
    def _build_synthetic_repos(self, root: Path, detached_head: bool = False) -> None:
        # Build minimal synthetic files matching exact digests & anchors ONLY by patching PINNED_SOURCE_DIGESTS
        # or test real staged repos when present; here we test tamper refusal with patched digests!
        for rel_path in sct.PINNED_SOURCE_DIGESTS:
            fp = root / rel_path
            fp.parent.mkdir(parents=True, exist_ok=True)
            lines = ["line"] * 170
            for _, a_rel, line_no, needle in sct.VERBATIM_ANCHORS:
                if a_rel == rel_path:
                    lines[line_no - 1] = needle
            fp.write_text("\n".join(lines) + "\n", encoding="utf-8")
        git_dir = root / "score-centering" / "repo" / ".git"
        git_dir.mkdir(parents=True, exist_ok=True)
        if detached_head:
            (git_dir / "HEAD").write_text(sct.PINNED_REPO_COMMIT + "\n", encoding="utf-8")
        else:
            (git_dir / "HEAD").write_text("ref: refs/heads/main\n", encoding="utf-8")
            ref_file = git_dir / "refs" / "heads" / "main"
            ref_file.parent.mkdir(parents=True, exist_ok=True)
            ref_file.write_text(sct.PINNED_REPO_COMMIT + "\n", encoding="utf-8")

    def _compute_digests(self, root: Path) -> dict[str, dict[str, object]]:
        out: dict[str, dict[str, object]] = {}
        for rel_path in sct.PINNED_SOURCE_DIGESTS:
            data = (root / rel_path).read_bytes()
            out[rel_path] = {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
        return out

    def test_live_repo_verifier_and_tamper_refusals(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"repos-dir-missing"):
                sct.audit_live_repos(root / "nonexistent")

            self._build_synthetic_repos(root, detached_head=False)
            digests = self._compute_digests(root)
            with patch.object(sct, "PINNED_SOURCE_DIGESTS", digests):
                ok = sct.audit_live_repos(root)
                self.assertEqual(ok["mode"], "live_read_only")
                self.assertEqual(ok["verified_files"], len(digests))
                self.assertEqual(ok["verified_anchors"], len(sct.VERBATIM_ANCHORS))
                self.assertEqual(ok["pinned_repo_commit"], sct.PINNED_REPO_COMMIT)

                # Detached HEAD branch
                (root / "score-centering" / "repo" / ".git" / "HEAD").write_text(
                    sct.PINNED_REPO_COMMIT + "\n", encoding="utf-8"
                )
                ok_det = sct.audit_live_repos(root)
                self.assertEqual(ok_det["pinned_repo_commit"], sct.PINNED_REPO_COMMIT)

                # Wrong commit SHA refusal
                (root / "score-centering" / "repo" / ".git" / "HEAD").write_text(
                    "0" * 40 + "\n", encoding="utf-8"
                )
                with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"repo-commit-mismatch"):
                    sct.audit_live_repos(root)

                # Missing ref target refusal
                (root / "score-centering" / "repo" / ".git" / "HEAD").write_text(
                    "ref: refs/heads/missing\n", encoding="utf-8"
                )
                with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"repo-git-ref-missing"):
                    sct.audit_live_repos(root)

                # Path-traversal & symlink-escape ref refusals
                outside_sha = root / "outside_sha.txt"
                outside_sha.write_text(sct.PINNED_REPO_COMMIT + "\n", encoding="utf-8")
                (root / "score-centering" / "repo" / ".git" / "HEAD").write_text(
                    "ref: ../../../outside_sha.txt\n", encoding="utf-8"
                )
                with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"repo-git-ref-invalid"):
                    sct.audit_live_repos(root)

                (root / "score-centering" / "repo" / ".git" / "HEAD").write_text(
                    "ref: refs/heads/../../../../outside_sha.txt\n", encoding="utf-8"
                )
                with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"repo-git-ref-invalid"):
                    sct.audit_live_repos(root)

                evil_link = root / "score-centering" / "repo" / ".git" / "refs" / "heads" / "evil"
                evil_link.symlink_to(outside_sha)
                (root / "score-centering" / "repo" / ".git" / "HEAD").write_text(
                    "ref: refs/heads/evil\n", encoding="utf-8"
                )
                with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"repo-git-ref-escape"):
                    sct.audit_live_repos(root)
                evil_link.unlink()

                # Missing HEAD file refusal
                (root / "score-centering" / "repo" / ".git" / "HEAD").unlink()
                with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"repo-git-head-missing"):
                    sct.audit_live_repos(root)

            # Restore detached HEAD, test anchor mismatch and anchor line range
            self._build_synthetic_repos(root, detached_head=True)
            target_file = root / "score-centering" / "repo" / "losses.py"
            bad_lines = target_file.read_text(encoding="utf-8").splitlines()
            bad_lines[138] = "tampered line"
            target_file.write_text("\n".join(bad_lines) + "\n", encoding="utf-8")
            with patch.object(sct, "PINNED_SOURCE_DIGESTS", self._compute_digests(root)):
                with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"anchor-text-mismatch:SC-CODE-01-FULL"):
                    sct.audit_live_repos(root)

            target_file.write_text("short\n", encoding="utf-8")
            with patch.object(sct, "PINNED_SOURCE_DIGESTS", self._compute_digests(root)):
                with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"anchor-line-range:SC-CODE-01-FULL"):
                    sct.audit_live_repos(root)
                # Exact closed boundary line_no == 1 == len(lines) (M061, M062)
                with patch.object(
                    sct,
                    "VERBATIM_ANCHORS",
                    (("SINGLE-LINE-BD", "score-centering/repo/losses.py", 1, "short"),),
                ):
                    ok_single = sct.audit_live_repos(root)
                    self.assertEqual(ok_single["verified_anchors"], 1)

            # Test SHA-256 mismatch (same byte length!) and byte-length mismatch and missing file
            self._build_synthetic_repos(root, detached_head=True)
            orig_digests = self._compute_digests(root)
            readme_p = root / "score-centering" / "repo" / "README.md"
            raw = readme_p.read_bytes()
            readme_p.write_bytes(b"X" + raw[1:])
            with patch.object(sct, "PINNED_SOURCE_DIGESTS", orig_digests):
                with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"source-sha256-mismatch"):
                    sct.audit_live_repos(root)
            readme_p.write_bytes(raw + b"!")
            with patch.object(sct, "PINNED_SOURCE_DIGESTS", orig_digests):
                with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"source-bytes-mismatch"):
                    sct.audit_live_repos(root)
            readme_p.unlink()
            with patch.object(sct, "PINNED_SOURCE_DIGESTS", orig_digests):
                with self.assertRaisesRegex(sct.ScoreCenteringAuditError, r"source-file-missing"):
                    sct.audit_live_repos(root)

    def test_standalone_cert_zero_float_and_cli_paths(self) -> None:
        cert1 = sct.build_certificate(repos_dir=None)
        cert2 = sct.build_certificate(repos_dir=None)
        self.assertEqual(cert1["certificate_sha256"], cert2["certificate_sha256"])
        self.assertEqual(cert1["live_source_verification"]["mode"], "standalone_pure_q")

        def _reject_float(token: str) -> None:
            raise AssertionError(f"float-token-found:{token}")

        with tempfile.TemporaryDirectory() as tmp:
            cert_path = Path(tmp) / "out.json"
            buf_json = io.StringIO()
            with patch("sys.stdout", buf_json):
                rc = sct.main(["--json", "--write-cert", str(cert_path)])
            self.assertEqual(rc, 0)
            written = cert_path.read_text(encoding="utf-8")
            self.assertEqual(buf_json.getvalue(), written)
            parsed = json.loads(written, parse_float=_reject_float)
            self.assertEqual(parsed["certificate_sha256"], cert1["certificate_sha256"])

            buf_human = io.StringIO()
            with patch("sys.stdout", buf_human):
                rc_h = sct.main([])
            self.assertEqual(rc_h, 0)
            self.assertIn(sct.AUDIT_ID, buf_human.getvalue())
            self.assertIn(cert1["certificate_sha256"], buf_human.getvalue())

        # Live repos check when running inside workspace next to ../repos
        live_repos = Path(__file__).resolve().parent.parent / "repos"
        if (live_repos / "score-centering" / "repo" / "losses.py").is_file():
            live_cert = sct.build_certificate(repos_dir=live_repos)
            self.assertEqual(live_cert["live_source_verification"]["mode"], "live_read_only")
            self.assertEqual(live_cert["live_source_verification"]["verified_files"], 7)
            self.assertEqual(live_cert["live_source_verification"]["verified_anchors"], 13)


if __name__ == "__main__":
    unittest.main()
