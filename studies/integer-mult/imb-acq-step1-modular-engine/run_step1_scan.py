#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Step 1 Stepped CLI Runner & Comprehensive Multi-Theorem Verification Suite.

Usage on any local `integer-mult-bounds` checkout (`WORD.json.gz` / `final.json.gz`):
  python3 run_step1_scan.py --self-test
  python3 run_step1_scan.py --word path/to/WORD.json.gz --stage all \
      --out STEP1-CANDIDATES.json --emit-word NEW-WORD.json.gz
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

from causal_dag_coalescer import scan_family_a_fusions, scan_flag_shear_coalitions
from joint_basis_abscission import (
    apply_joint_abscission_split,
    public_final_polynomials,
    scan_catalyst_abscission_splits,
)
from tariff_shadow_pricer import (
    certify_delta_moment_positive,
    pack_disjoint_splices,
    verify_full_word_and_grid,
)


def load_word(path: Path) -> dict:
    raw = path.read_bytes()
    if path.suffix == '.gz':
        raw = gzip.decompress(raw)
    return json.loads(raw)


def canonical_sha256(obj: dict) -> str:
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def run_pipeline(
    W: dict,
    stage: str = 'all',
    max_k: int = 3,
    max_window_events: int = 800,
    base_kappa: str = "0.003647081039689",
    caller_multiplier: int = 17,
) -> dict:
    t0 = time.time()
    report = {
        'input_word_canonical_sha256': canonical_sha256(W),
        'input_events': len(W['program']),
        'input_public': W['public'],
        'base_kappa': base_kappa,
        'caller_multiplier': caller_multiplier,
        'stages_executed': stage,
    }

    splices = []
    if stage in ('scan-a', 'all'):
        t_a = time.time()
        fam_a = scan_family_a_fusions(W)
        report['stage_1a_family_a'] = {
            'seconds': round(time.time() - t_a, 4),
            'count': len(fam_a),
            'candidates': fam_a[:25],
        }
        splices.extend(fam_a)

    if stage in ('scan-shear', 'all'):
        t_b = time.time()
        shears = scan_flag_shear_coalitions(W, max_k=max_k, max_window_events=max_window_events)
        priced_shears = []
        for s in shears:
            pr = certify_delta_moment_positive({}, s['paid_delta'], base_kappa, caller_multiplier)
            if pr['strictly_positive_proven']:
                priced_shears.append({**s, 'pricing': pr})
        priced_shears.sort(key=lambda x: x['pricing']['moment_gain_float'], reverse=True)
        report['stage_1b_flag_shears'] = {
            'seconds': round(time.time() - t_b, 4),
            'raw_algebraic_matches': len(shears),
            'strictly_positive_karamata_gains': len(priced_shears),
            'top_candidates': [
                {k: v for k, v in item.items() if k != 'new_window'}
                for item in priced_shears[:25]
            ],
        }
        splices.extend(shears)

    if stage in ('scan-abscission', 'all'):
        t_c = time.time()
        absc = scan_catalyst_abscission_splits(W, max_cohort_k=max_k)
        priced_single = []
        for c in absc['single_abscission_splits']:
            pr = certify_delta_moment_positive(c['productive_delta'], {}, base_kappa, caller_multiplier)
            if pr['strictly_positive_proven']:
                priced_single.append({**c, 'pricing': pr})
        priced_single.sort(key=lambda x: (x['nontrivial_both_halves'], x['pricing']['moment_gain_float']), reverse=True)

        priced_joint = []
        for c in absc['joint_basis_abscission_splits']:
            pr = certify_delta_moment_positive(c['productive_delta'], {}, base_kappa, caller_multiplier)
            if pr['strictly_positive_proven']:
                priced_joint.append({**c, 'pricing': pr})
        priced_joint.sort(key=lambda x: x['pricing']['moment_gain_float'], reverse=True)

        report['stage_1c_catalyst_abscission'] = {
            'seconds': round(time.time() - t_c, 4),
            'single_k1_count': len(priced_single),
            'joint_k2plus_count': len(priced_joint),
            'top_single_splits': priced_single[:20],
            'top_joint_basis_splits': priced_joint[:20],
        }

    if stage == 'all':
        t_d = time.time()
        packed = pack_disjoint_splices(W, splices, base_kappa, caller_multiplier)
        W_packed = packed['packed_word']
        audit = verify_full_word_and_grid(W_packed, W_ref=W)
        report['stage_1d_packed_verification'] = {
            'seconds': round(time.time() - t_d, 4),
            'disjoint_splices_packed': len(packed['selected']),
            'selected_kinds': [x['kind'] for x in packed['selected']],
            'cumulative_paid_delta': packed['cumulative_paid_delta'],
            'cumulative_pricing': packed['cumulative_pricing'],
            'packed_word_canonical_sha256': canonical_sha256(W_packed),
            'audit': audit,
        }
        report['_packed_word_obj'] = W_packed

    report['total_seconds'] = round(time.time() - t0, 4)
    return report


def run_comprehensive_self_test():
    print("=== RUNNING IMB ACQ STEP-1 MATHEMATICAL SUITE SELF-TEST ===")
    frames = [
        [],                                      # f=0 (dim 0)
        [1],                                     # f=1 (dim 1)
        [2, 4],                                  # f=2 (dim 2)
        [2, 4, 8, 16, 32],                       # f=3 (dim 5, step = 3)
        [2, 4, 8, 16, 32, 64, 128, 256],         # f=4 (dim 8, step = 3)
        [1, 2, 4, 8, 16, 32, 64, 128, 256],      # f=5 (dim 9, step = 1)
    ]
    n_pub = 125
    initial = [2] * n_pub
    final = [5] * n_pub
    initial[0] = 1; final[0] = 5
    initial[112] = 0; final[112] = 4

    prog = [
        ['MOVE', 0, 1, 5, False],
        ['MOVE', 112, 0, 4, False],
    ]

    # --- Block 1: PR #7481 pattern (`k=2` funded detour) across non-adjacent unrelated events! ---
    final[1] = 4; final[2] = 5
    initial[3] = 3; final[3] = 5
    initial[4] = 3; final[4] = 5
    prog.extend([
        ['MOVE', 1, 2, 3, False],
        ['SCALE', 5, '3/2', 2],           # Unrelated op bridged by Commuting-ADD DAG coalescer
        ['MOVE', 2, 2, 3, False],
        ['ADD', 3, 1, '-1', 3],
        ['ADD', 3, 2, '1/2', 3],
        ['ADD', 3, 4, '-1', 3],
        ['ADD', 1, 4, '1', 3],
        ['ADD', 2, 4, '1/2', 3],
        ['MOVE', 1, 3, 4, False],
        ['SCALE', 6, '1/2', 2],           # Unrelated op bridged by Commuting-ADD DAG coalescer
        ['MOVE', 2, 3, 5, False],
        ['MOVE', 3, 3, 5, False],
        ['MOVE', 4, 3, 5, False],
    ])

    # --- Block 2: `k=3` Rank-2 Non-Identity Block (`A_WW != I_3`, Corollary 1.1 single detour!) ---
    # Helper 10 skips f=3 (2->4), Carrier 11 co-terminates at f=4 (0 detour!), Carrier 12 detours 3->4->5!
    # All 6 `k=2` pairs are UNSAT (rank-2 external reads/writes), `k=3` achieves exact {1:+1, 3:-1, 4:-1, 6:+1}!
    final[10] = 4; final[11] = 4; final[12] = 5
    for r in (13, 14, 15, 16):
        initial[r] = 3; final[r] = 5
    prog.extend([
        ['MOVE', 10, 2, 3, False],
        ['MOVE', 11, 2, 3, False],
        ['MOVE', 12, 2, 3, False],
        ['ADD', 10, 11, '1/2', 3],        # Internal W-W interaction -> A_WW != I_3
        ['ADD', 13, 10, '1', 3],
        ['ADD', 13, 11, '1', 3],
        ['ADD', 14, 11, '1', 3],
        ['ADD', 14, 12, '1', 3],
        ['ADD', 10, 15, '1', 3],
        ['ADD', 11, 15, '1', 3],
        ['ADD', 11, 16, '1', 3],
        ['ADD', 12, 16, '2', 3],
        ['MOVE', 10, 3, 4, False],
        ['MOVE', 11, 3, 4, False],
        ['MOVE', 12, 3, 5, False],
        ['MOVE', 13, 3, 5, False],
        ['MOVE', 14, 3, 5, False],
        ['MOVE', 15, 3, 5, False],
        ['MOVE', 16, 3, 5, False],
    ])

    # --- Block 3: Family-A SCALE-commuting MOVE fusion on helper 20 (2 -> 3 -> 5) ---
    prog.extend([
        ['MOVE', 20, 2, 3, False],
        ['SCALE', 20, '3/4', 3],
        ['MOVE', 20, 3, 5, False],
    ])

    # --- Block 4: Coupled `k=2` Entangled Helper Catalyst Abscission (`30, 31`: 2 -> 3 -> 5) ---
    # At f=2, `32` receives `v_30 + 2*v_31` (so neither 30 nor 31 can k=1 split!).
    # At f=3, `33` reads `30` and `34` reads `31` (rank-2 read on 2 wires -> Stage 1B CANNOT bypass f=3!).
    # Yet right on arrival at f=3, `ker(L) = span([-2, 1])` has nullity 1, so Theorem 2's Joint-Basis
    # Abscission cleanly splits `30` into two independent helpers (ranks 3 + 4 instead of 7) at 0 paid cost!
    initial[33] = 3; final[33] = 5
    initial[34] = 3; final[34] = 5
    prog.extend([
        ['ADD', 32, 30, '1', 2],
        ['ADD', 32, 31, '2', 2],
        ['MOVE', 32, 2, 5, False],
        ['MOVE', 30, 2, 3, False],
        ['MOVE', 31, 2, 3, False],
        ['ADD', 33, 30, '1', 3],
        ['ADD', 34, 31, '1', 3],
        ['MOVE', 30, 3, 5, False],
        ['MOVE', 31, 3, 5, False],
        ['MOVE', 33, 3, 5, False],
        ['MOVE', 34, 3, 5, False],
    ])

    already_moved = {0, 112, 1, 2, 3, 4, 10, 11, 12, 13, 14, 15, 16, 20, 30, 31, 32, 33, 34}
    for r in range(n_pub):
        if r not in already_moved:
            prog.append(['MOVE', r, 2, 5, False])

    W_bench = {
        'public': n_pub,
        'owned_fields': 2,
        'frames': frames,
        'initial': initial,
        'final': final,
        'live': [0],
        'ports': [1],
        'hosted': {'Dports': [0], 'X2': [], 'Y2': []},
        'program': prog,
    }

    base_audit = verify_full_word_and_grid(W_bench)
    assert base_audit['status'] == 'PASS_EXACT_WORD_AND_GRID_AUDIT'

    rep = run_pipeline(W_bench, stage='all', max_k=3, base_kappa="0.003647081039689", caller_multiplier=17)
    s1a = rep['stage_1a_family_a']
    s1b = rep['stage_1b_flag_shears']
    s1c = rep['stage_1c_catalyst_abscission']
    s1d = rep['stage_1d_packed_verification']

    print(f"  [OK] Stage 1A Family-A fusions found : {s1a['count']}")
    print(f"  [OK] Stage 1B Flag-Shears (k=2,3)    : {s1b['strictly_positive_karamata_gains']} strictly positive")
    print(f"  [OK] Stage 1C Joint-Basis Abscission : {s1c['joint_k2plus_count']} coupled k>=2 splits")
    print(f"  [OK] Stage 1D Packed Disjoint Splices: {s1d['disjoint_splices_packed']} -> {s1d['selected_kinds']}")
    print(f"       Cumulative Paid Delta           : {s1d['cumulative_paid_delta']}")
    print(f"       Estimated Delta Kappa (17x)     : +{s1d['cumulative_pricing']['estimated_delta_kappa']}")

    assert 'k2_funded_detour_flag_shear' in s1d['selected_kinds']
    assert 'k3_funded_detour_flag_shear' in s1d['selected_kinds']
    assert 'family_a_move_fusion' in s1d['selected_kinds']
    assert s1d['disjoint_splices_packed'] == 3

    # Materialize Block 4's [30, 31] split on top of W_packed and check it against W_packed.
    W_packed = rep['_packed_word_obj']
    absc_on_packed = scan_catalyst_abscission_splits(W_packed, max_cohort_k=3)
    joint_30_31 = next(
        c for c in absc_on_packed['joint_basis_abscission_splits']
        if c['cohort'] == [30, 31] and c['f_cut'] == 3
    )
    W_split = apply_joint_abscission_split(W_packed, joint_30_31)
    polys_packed = public_final_polynomials(W_packed)
    polys_split = public_final_polynomials(W_split)
    changed = [r for r in range(W_packed['public']) if polys_split[r] != polys_packed[r]]
    assert not changed, f"split changed pre-split public finals {changed}"
    new_role = W_packed['public']
    assert polys_split[new_role] == {new_role: 1}
    assert all(new_role not in polys_split[r] for r in range(W_packed['public']))
    split_audit = verify_full_word_and_grid(W_split, W_ref=W_packed, odd_scale=1125, max_frac_bits=25)
    assert split_audit['jacobian_check'] == 'PASS_EXACT_WITH_ONE_SPLIT_HELPER'
    assert split_audit['public'] == W_packed['public'] + 1
    assert split_audit['helpers'].get(3, 0) == s1d['audit']['helpers'].get(3, 0) + 1
    assert split_audit['helpers'].get(4, 0) == s1d['audit']['helpers'].get(4, 0) + 1
    assert split_audit['helpers'].get(7, 0) == s1d['audit']['helpers'].get(7, 0) - 1
    assert split_audit['paid'] == s1d['audit']['paid']
    split_gain = certify_delta_moment_positive({7: -1, 3: 1, 4: 1}, {}, "0.003647081039689", 17)
    assert split_gain['strictly_positive_proven']
    print(f"  [OK] Split of helper 30 at f=3       : {W_packed['public']} pre-split public finals unchanged "
          f"(Jacobian check run against the packed word)")
    print(f"       Helpers delta {{7:-1, 3:+1, 4:+1}}, paid delta {{}}, est dk=+{split_gain['estimated_delta_kappa']} (fitted slope)")

    # Negative control: a word that reads the split role after it leaves f_cut must be refused.
    W_bad = {**W_packed, 'program': W_packed['program'] + [['ADD', 33, 30, '1', 5]]}
    try:
        apply_joint_abscission_split(W_bad, joint_30_31)
    except ValueError:
        pass
    else:
        raise AssertionError("split accepted a word that reads the split role after the cut")
    print("  [OK] Split refused when the split role is read after the cut")

    # Verify exact PR #7480 -> PR #7481 calibration (+3.03166854e-7):
    cal_7481 = certify_delta_moment_positive({}, {1: 1, 3: -1, 4: -1, 6: 1}, "0.003646777872835", 17)
    print(f"  [OK] PR #7481 Exact Calibration      : est_dk=+{cal_7481['estimated_delta_kappa']} (actual +3.031668540000e-7)")
    assert abs(cal_7481['estimated_delta_kappa_float'] - 3.03166854e-7) < 1e-13
    print("=== ALL 5 MATHEMATICAL & ADVERSARIAL SELF-TESTS PASSED ===")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--self-test', action='store_true', help='Run built-in 5-part mathematical & adversarial test suite')
    ap.add_argument('--word', type=Path, help='Path to WORD.json.gz or final.json.gz')
    ap.add_argument('--stage', choices=['scan-a', 'scan-shear', 'scan-abscission', 'all'], default='all')
    ap.add_argument('--max-k', type=int, default=3, help='Maximum coalition size k (default: 3)')
    ap.add_argument('--max-window', type=int, default=800, help='Maximum event span for DAG coalescing (default: 800)')
    ap.add_argument('--base-kappa', type=str, default='0.003647081039689', help='Rational/decimal base kappa (default: PR #7481)')
    ap.add_argument('--multiplier', type=int, default=17, help='Caller stage multiplier (17 for #7481, 18 for #7000)')
    ap.add_argument('--out', type=Path, help='Write JSON scan & verification receipt to path')
    ap.add_argument('--emit-word', type=Path, help='Write packed optimized word (.json or .json.gz) to path')
    args = ap.parse_args()

    if args.self_test or not args.word:
        run_comprehensive_self_test()
        if not args.word:
            return

    W = load_word(args.word)
    rep = run_pipeline(
        W,
        stage=args.stage,
        max_k=args.max_k,
        max_window_events=args.max_window,
        base_kappa=args.base_kappa,
        caller_multiplier=args.multiplier,
    )
    W_packed = rep.pop('_packed_word_obj', None)
    if args.emit_word and W_packed is not None:
        payload = json.dumps(W_packed, separators=(',', ':')).encode()
        if args.emit_word.suffix == '.gz':
            args.emit_word.write_bytes(gzip.compress(payload, mtime=0))
        else:
            args.emit_word.write_bytes(payload)
    out_json = json.dumps(rep, indent=2)
    if args.out:
        args.out.write_text(out_json + '\n')
    print(out_json)


if __name__ == '__main__':
    main()
