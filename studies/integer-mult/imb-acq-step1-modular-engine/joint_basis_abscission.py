# SPDX-License-Identifier: Apache-2.0
"""Module 2: Coupled k-Helper Nullspace Catalyst Abscission Solver.

Implements Theorem 2 (Joint-Basis Nullspace Catalyst Abscission over Z[1/30]):
Directly targets the open `p104-side-correction` frontier question:
  "Can joint helper bases and a legal causal split improve the complete P104
   productive/paid invoice?"

At any cut event where a cohort of public helpers H = [h_0, ..., h_{k-1}] with
identical (or flag-nested) endpoints (f_0, f_end) resides at an intermediate
frame f_cut (f_0 < f_cut < f_end):
  1. Single-helper abscission (k = 1): checks whether register h holds a pure
     smooth multiple c * v_h of its own public input variable v_h while EVERY
     other active register across all n_public variables has zero v_h coefficient.
  2. Coupled multi-helper joint-basis abscission (k >= 2): even when EVERY single
     helper in H has leaked into external/main registers (so all k = 1 splits fail!),
     let L in Q^{|E| x k} be the external leakage matrix of v_H across all other
     active registers E, and let B_H in Q^{k x k} be the internal matrix on H
     (after verifying zero main-input or outside-helper contamination on H).
     Whenever dim ker(L) >= 1, any smooth unimodular input basis rotation
     R_in in SL_k(Z[1/30]) at f_0 whose first column spans z in ker(L), paired
     with the disentangling shear R_cut = (B_H * R_in)^{-1} at f_cut, isolates
     transformed helper h_0 in state 1 * v_tilde_0 with ZERO external footprint!
     Splitting h_0 at f_cut replaces productive target (d_1 + d_2) with two
     independent productive targets (d_1, d_2), strictly increasing T(C)
     (since d_1^{1-C} + d_2^{1-C} > (d_1 + d_2)^{1-C}) at ZERO paid MOVE cost!
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as F
from bi_annihilator_flag_shear import (
    factor_glk_into_ops,
    is_scale_safe,
    mat_det_and_inv,
    mat_mul,
    normalize_to_slk_unit_pivots,
    rref_nullspace_right,
)


def span_mask(basis: list[int]) -> frozenset[int]:
    s = {0}
    for x in basis:
        s |= {v ^ x for v in s}
    return frozenset(s)


def scan_catalyst_abscission_splits(
    W: dict,
    max_cohort_k: int = 3,
    odd_scale: int = 1125,
    max_pow2: int = 16,
) -> dict:
    """Performs a single exact all-variable forward symbolic pass over `W['program']`
    to discover both single-helper (k=1) and coupled joint-basis (k>=2) abscission splits.
    """
    n = W['public']
    frames = [span_mask(b) for b in W['frames']]
    dim = [len(b) for b in W['frames']]
    main_roles = (
        set(W['live'])
        | {r + 112 for r in W['live']}
        | set(W['hosted']['X2'])
        | set(W['hosted']['Y2'])
    )
    helpers = {r for r in range(n) if r not in main_roles}
    prog = W['program']

    # Precompute first/last non-MOVE interaction of each helper so nontrivial splits rank first
    first_touch = {}
    last_touch = {}
    for idx, ev in enumerate(prog):
        if ev[0] in ('ADD', 'COPY'):
            for r in (ev[1], ev[2]):
                if r in helpers:
                    first_touch.setdefault(r, idx)
                    last_touch[r] = idx

    cur_frame = {r: W['initial'][r] for r in range(n)}
    val: dict[int, dict[int, F]] = {r: {r: F(1)} for r in range(n)}
    holders: dict[int, set[int]] = {v: {v} for v in range(n)}

    def set_coeff(reg: int, var: int, new_c: F):
        old_c = val[reg].get(var, F(0))
        if new_c == 0:
            if old_c != 0:
                del val[reg][var]
                holders[var].discard(reg)
        else:
            val[reg][var] = new_c
            holders[var].add(reg)

    single_splits = []
    joint_splits = []
    seen_single = set()
    seen_joint = set()

    def check_helper_single(r: int, cut_frame: int, idx: int, when: str):
        if (r, cut_frame) in seen_single:
            return
        f0, f_end = W['initial'][r], W['final'][r]
        if not (frames[f0] < frames[cut_frame] and frames[cut_frame] < frames[f_end]):
            return
        if holders[r] == {r} and len(val[r]) == 1 and r in val[r]:
            c_self = val[r][r]
            if c_self == 1 or (is_scale_safe(c_self, odd_scale, max_pow2) and is_scale_safe(F(1) / c_self, odd_scale, max_pow2)):
                seen_single.add((r, cut_frame))
                d1 = dim[cut_frame] - dim[f0]
                d2 = dim[f_end] - dim[cut_frame]
                nontrivial = (first_touch.get(r, 10**9) < idx < last_touch.get(r, -1))
                single_splits.append({
                    'kind': 'k1_single_abscission',
                    'role': r,
                    'event_idx': idx,
                    'when': when,
                    'f0': f0,
                    'f_cut': cut_frame,
                    'f_end': f_end,
                    'd_orig': d1 + d2,
                    'd1': d1,
                    'd2': d2,
                    'productive_delta': {d1 + d2: -1, d1: 1, d2: 1} if d1 != d2 else {d1 + d2: -1, d1: 2},
                    'scale': str(c_self),
                    'nontrivial_both_halves': nontrivial,
                })

    def check_joint_cohort_at_frame(cut_frame: int, trigger_role: int, idx: int, when: str):
        # Collect all helpers currently at `cut_frame` sharing `(f0, f_end)` with `trigger_role`
        # that are NOT already single-splittable (i.e. genuinely entangled / leaking!):
        f0, f_end = W['initial'][trigger_role], W['final'][trigger_role]
        if not (frames[f0] < frames[cut_frame] and frames[cut_frame] < frames[f_end]):
            return
        co = [
            h for h in sorted(helpers)
            if cur_frame.get(h) == cut_frame
            and W['initial'][h] == f0
            and W['final'][h] == f_end
            and not (holders[h] == {h} and len(val[h]) == 1 and h in val[h])
        ]
        if len(co) < 2:
            return
        co_sub = co[:max_cohort_k]
        co_set = set(co_sub)
        key = (tuple(co_sub), cut_frame)
        if key in seen_joint:
            return
        # Check that registers in `co_sub` ONLY depend on variables in `co_sub`
        # (zero main-variable or outside-helper contamination inside `co_sub`):
        if any(not set(val[h].keys()).issubset(co_set) for h in co_sub):
            return
        k = len(co_sub)
        B_H = [[val[co_sub[i]].get(co_sub[j], F(0)) for j in range(k)] for i in range(k)]
        det_B, _ = mat_det_and_inv(B_H)
        if det_B == 0:
            return

        # Build external leakage matrix L over all active registers outside `co_sub`:
        ext_holders = set()
        for h in co_sub:
            ext_holders |= (holders[h] - co_set)
        ext_list = sorted(ext_holders)
        L = [[val[e].get(co_sub[j], F(0)) for j in range(k)] for e in ext_list]
        z_basis = rref_nullspace_right(L, k)
        if not z_basis:
            return

        # Found a non-zero leakage-free mode z in ker(L)!
        # Construct R_in_inv whose row 0 creates the dual coordinate so column 0 of R_in is proportional to z!
        z = z_basis[0]
        # Build R_in^T by setting row 0 = z^T and completing to SL_k, then transposing so col 0 of R_in is z!
        # Wait: let's simply complete `z` as column 0 of `R_in`:
        # Nullspace of [[1, 0, ...]]? Even simpler: find k-1 independent rows annihilating z:
        ann_z = rref_nullspace_right([z], k)
        # Pick row 0 so row0 . z == 1 (choose first non-zero coord of z):
        nz = next(j for j in range(k) if z[j] != 0)
        r0 = [F(1) / z[nz] if j == nz else F(0) for j in range(k)]
        R_in_inv = normalize_to_slk_unit_pivots([r0] + ann_z)
        if R_in_inv is None:
            return
        _, R_in = mat_det_and_inv(R_in_inv)
        if R_in is None:
            return
        # Verify col 0 of R_in is in ker(L):
        col0 = [R_in[j][0] for j in range(k)]
        if any(sum(L[ei][j] * col0[j] for j in range(k)) != 0 for ei in range(len(ext_list))):
            return

        # Notice: original circuit expects `v_orig = R_in * v_new` at start frame `f0`!
        # And at `f_cut`, the registers `co_sub` currently hold `B_H * v_orig = (B_H * R_in) * v_new`!
        # So applying `R_cut = (B_H * R_in)^{-1}` at `f_cut` sets `co_sub` to `I_k * v_new`,
        # which puts `co_sub[0]` in pure state `1 * v_new[0]` with ZERO external leakage,
        # and then after splitting `co_sub[0]` (replacing `co_sub[0]` with fresh `v_split`!),
        # applying `R_restore = B_H * R_in` at `f_cut` restores the exact downstream trajectory
        # AND applying `R_in_inv` at `f_end` restores unmixed final helper basis on `co_sub[1:]` + `v_split`!
        BR = mat_mul(B_H, R_in)
        _, R_cut = mat_det_and_inv(BR)
        if R_cut is None:
            return

        ops_f0 = factor_glk_into_ops(R_in, co_sub, f0, odd_scale, max_pow2)
        ops_cut_pre = factor_glk_into_ops(R_cut, co_sub, cut_frame, odd_scale, max_pow2)
        ops_cut_post = factor_glk_into_ops(BR, co_sub, cut_frame, odd_scale, max_pow2)
        ops_fend = factor_glk_into_ops(R_in_inv, co_sub, f_end, odd_scale, max_pow2)
        if any(x is None for x in (ops_f0, ops_cut_pre, ops_cut_post, ops_fend)):
            return

        seen_joint.add(key)
        d1 = dim[cut_frame] - dim[f0]
        d2 = dim[f_end] - dim[cut_frame]
        joint_splits.append({
            'kind': f'k{k}_joint_basis_abscission',
            'cohort': co_sub,
            'split_role': co_sub[0],
            'event_idx': idx,
            'when': when,
            'f0': f0,
            'f_cut': cut_frame,
            'f_end': f_end,
            'd_orig': d1 + d2,
            'd1': d1,
            'd2': d2,
            'productive_delta': {d1 + d2: -1, d1: 1, d2: 1} if d1 != d2 else {d1 + d2: -1, d1: 2},
            'leakage_nullity': len(z_basis),
            'ops_f0': ops_f0,
            'ops_cut_pre': ops_cut_pre,
            'ops_cut_post': ops_cut_post,
            'ops_fend': ops_fend,
            'added_scalar_ops': len(ops_f0) + len(ops_cut_pre) + len(ops_cut_post) + len(ops_fend),
        })

    for idx, ev in enumerate(prog):
        op, r = ev[0], ev[1]
        if op == 'INIT':
            cur_frame[r] = ev[2]
            val[r] = {}
        elif op == 'CLEAR':
            for v in list(val[r].keys()):
                holders[v].discard(r)
            del val[r]
            del cur_frame[r]
        elif op == 'SCALE':
            q = F(ev[2])
            for v in list(val[r].keys()):
                val[r][v] *= q
        elif op == 'COPY':
            s, q = ev[2], F(ev[3])
            for v in list(val[r].keys()):
                holders[v].discard(r)
            val[r] = {v: c * q for v, c in val[s].items() if c * q != 0}
            for v in val[r]:
                holders[v].add(r)
        elif op == 'ADD':
            s, q = ev[2], F(ev[3])
            for v, cs in list(val[s].items()):
                set_coeff(r, v, val[r].get(v, F(0)) + q * cs)
        elif op == 'MOVE':
            _, _, fa, fb, owned = ev
            if not owned and r in helpers:
                check_helper_single(r, fa, idx, 'before')
                check_joint_cohort_at_frame(fa, r, idx, 'before')
            cur_frame[r] = fb
            if not owned and r in helpers:
                check_helper_single(r, fb, idx, 'after')
                check_joint_cohort_at_frame(fb, r, idx, 'after')

    return {
        'single_abscission_splits': single_splits,
        'joint_basis_abscission_splits': joint_splits,
    }


def apply_joint_abscission_split(W: dict, cand: dict) -> dict:
    """Materializes a word `W_new` with `public + 1` fields that splits the
    candidate's helper at `f_cut` and preserves the input polynomial of every
    pre-split public register.

    The new helper takes index `new_role = W['public']`, and owned register
    indices `>= W['public']` shift up by 1. The split role keeps every event up
    to its first MOVE out of `f_cut` at or after the candidate's event, so all
    of its reads and writes at `f_cut` still see the original value. That MOVE
    and every later MOVE of the split role are handed to the new helper, whose
    input variable is fresh and is never read. The split role then ends at
    `f_cut` holding the value it held there.

    This is only sound when the split role is not read or written after that
    MOVE. If it is, the split would change the linear map, so this raises
    ValueError instead of emitting a word. The candidate's basis-rotation ops
    (`ops_f0`, `ops_cut_*`, `ops_fend`) are not spliced in: placed as the scanner
    built them they change what other registers read (finals 32, 33 and 34 on
    the self-test's [30, 31] cohort), and the terminal cut above does not need
    them. Callers should still check the result with
    `verify_full_word_and_grid(W_new, W_ref=W)`; this function also asserts it.
    """
    n_old = W['public']
    new_helper = n_old

    def shift_reg(r: int) -> int:
        return r + 1 if r >= n_old else r

    def shift_ev(ev: list) -> list:
        ev = list(ev)
        ev[1] = shift_reg(ev[1])
        if ev[0] in ('ADD', 'COPY'):
            ev[2] = shift_reg(ev[2])
        return ev

    prog = [shift_ev(e) for e in W['program']]
    split_role = cand['role'] if cand['kind'] == 'k1_single_abscission' else cand['split_role']
    f_cut, f_end = cand['f_cut'], cand['f_end']
    if W['final'][split_role] != f_end:
        raise ValueError(f"split role {split_role} does not end at f_end={f_end}")

    start = cand['event_idx']
    depart = next(
        (i for i in range(start, len(prog))
         if prog[i][0] == 'MOVE' and prog[i][1] == split_role and prog[i][2] == f_cut),
        None,
    )
    if depart is None:
        raise ValueError(f"split role {split_role} never leaves f_cut={f_cut} after event {start}")

    def touches(ev: list, r: int) -> bool:
        return ev[1] == r or (ev[0] in ('ADD', 'COPY') and ev[2] == r)

    new_prog = list(prog[:depart])
    for ev in prog[depart:]:
        if touches(ev, split_role):
            if ev[0] != 'MOVE':
                raise ValueError(
                    f"split role {split_role} is used after leaving f_cut ({ev}); a split here would change the linear map"
                )
            ev = list(ev)
            ev[1] = new_helper
        new_prog.append(ev)

    new_initial = list(W['initial']) + [f_cut]
    new_final = list(W['final']) + [f_end]
    new_final[split_role] = f_cut

    W_new = {
        **W,
        'public': n_old + 1,
        'initial': new_initial,
        'final': new_final,
        'program': new_prog,
    }
    old_polys = public_final_polynomials(W)
    new_polys = public_final_polynomials(W_new)
    changed = [r for r in range(n_old) if new_polys[r] != old_polys[r]]
    if changed:
        raise AssertionError(f"split changed pre-split public finals {changed[:10]}")
    return W_new


def public_final_polynomials(W: dict) -> list[dict[int, F]]:
    """Forward exact evaluation: for each public register, its final value as a
    linear polynomial {input variable: coefficient} over the public inputs."""
    n = W['public']
    val: dict[int, dict[int, F]] = {r: {r: F(1)} for r in range(n)}
    for ev in W['program']:
        op, r = ev[0], ev[1]
        if op == 'INIT':
            val[r] = {}
        elif op == 'CLEAR':
            val.pop(r, None)
        elif op == 'SCALE':
            q = F(ev[2])
            val[r] = {v: c * q for v, c in val[r].items() if c * q != 0}
        elif op == 'COPY':
            q = F(ev[3])
            val[r] = {v: c * q for v, c in val[ev[2]].items() if c * q != 0}
        elif op == 'ADD':
            q = F(ev[3])
            acc = dict(val[r])
            for v, c in val[ev[2]].items():
                nv = acc.get(v, F(0)) + q * c
                if nv != 0:
                    acc[v] = nv
                else:
                    acc.pop(v, None)
            val[r] = acc
    return [val[r] for r in range(n)]
