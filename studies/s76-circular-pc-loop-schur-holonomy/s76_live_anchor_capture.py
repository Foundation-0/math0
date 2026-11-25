#!/usr/bin/env python3
"""Track S76 Live Real-Weight Anchor Capture on rel-int/CircularEP (CPU-only).

Reads the real shipped trained 2x256 tanh circular predictive-coding Sudoku model
(`demo/models/best.json` + `demo/puzzles.json`) from a read-only clone of
`rel-int/CircularEP` and writes a zero-float canonical JSON receipt
(`s76_circularep_live_anchor.json`, mode 0o600) encoding every live measurement
as exact decimal strings or exact integers so the downstream pure-Z/Q oracle and
auditor remain 100% stdlib and zero-float.
"""
from __future__ import annotations

import base64
from decimal import Decimal, ROUND_HALF_UP
import hashlib
import json
import math
import os
from pathlib import Path
import sys
from typing import Any

import numpy as np

_THIS_DIR = Path(__file__).resolve().parent
_DEFAULT_REPO = Path("/tmp/circularep_ro")
_OUT_PATH = _THIS_DIR / "s76_circularep_live_anchor.json"


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _dec_str(val: float, places: int) -> str:
    q = Decimal(10) ** (-places)
    d = Decimal(repr(float(val))).quantize(q, rounding=ROUND_HALF_UP)
    return format(d, f".{places}f")


def _sci_str(val: float, sig: int = 6) -> str:
    return f"{float(val):.{sig}e}"


def _dec_array(obj: dict[str, Any], dtype: Any = np.float64) -> np.ndarray:
    raw = base64.b64decode(obj["b64"])
    arr = np.frombuffer(raw, dtype="<f4").astype(dtype, copy=True)
    if "shape" in obj:
        arr = arr.reshape(obj["shape"])
    return arr


def main() -> int:
    repo = Path(sys.argv[1]) if len(sys.argv) > 1 else _DEFAULT_REPO
    best_path = repo / "demo" / "models" / "best.json"
    puzzles_path = repo / "demo" / "puzzles.json"
    model_js_path = repo / "demo" / "model.js"
    core_ep_path = repo / "core" / "ep.py"
    core_diag_path = repo / "core" / "diagnostics.py"

    best = json.loads(best_path.read_text(encoding="utf-8"))
    puzzles = json.loads(puzzles_path.read_text(encoding="utf-8"))["puzzles"]

    # Read HEAD commit sha from .git
    head_ref = (repo / ".git" / "HEAD").read_text(encoding="utf-8").strip()
    if head_ref.startswith("ref: "):
        commit_sha = (repo / ".git" / head_ref[5:]).read_text(encoding="utf-8").strip()
    else:
        commit_sha = head_ref

    Win32, bin32 = _dec_array(best["theta"]["Win"], np.float32), _dec_array(best["theta"]["bin"], np.float32)
    W1_32, b1_32 = _dec_array(best["theta"]["W1"], np.float32), _dec_array(best["theta"]["b1"], np.float32)
    W2_32, b2_32 = _dec_array(best["theta"]["W2"], np.float32), _dec_array(best["theta"]["b2"], np.float32)
    V32, c32 = _dec_array(best["psi"]["V"], np.float32), _dec_array(best["psi"]["c"], np.float32)

    Win, bin_ = Win32.astype(np.float64), bin32.astype(np.float64)
    W1, b1 = W1_32.astype(np.float64), b1_32.astype(np.float64)
    W2, b2 = W2_32.astype(np.float64), b2_32.astype(np.float64)
    V, c = V32.astype(np.float64), c32.astype(np.float64)
    I256 = np.eye(256, dtype=np.float64)

    sigma_w1 = float(np.linalg.svd(W1, compute_uv=False)[0])
    sigma_w2 = float(np.linalg.svd(W2, compute_uv=False)[0])

    def encode_puz(puz: list[int]) -> np.ndarray:
        x = np.zeros(80, dtype=np.float64)
        for i, val in enumerate(puz):
            x[i * 5 + val] = 1.0
        return x

    def embed_f32(puz: list[int]) -> np.ndarray:
        return (encode_puz(puz) @ Win + bin_).astype(np.float32)

    def embed_f64(puz: list[int]) -> np.ndarray:
        return encode_puz(puz) @ Win + bin_

    def jacobi_f64(u: np.ndarray, s: np.ndarray, x_inj: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
        u_hat = np.tanh(s.astype(np.float64) @ W1 + b1)
        s_hat = np.tanh(u.astype(np.float64) @ W2 + b2 + x_inj.astype(np.float64))
        return u_hat, s_hat

    def energy_f64(u: np.ndarray, s: np.ndarray, x_inj: np.ndarray) -> float:
        u_hat, s_hat = jacobi_f64(u, s, x_inj)
        eu = u.astype(np.float64) - u_hat
        es = s.astype(np.float64) - s_hat
        return 0.5 * float(np.dot(eu, eu) + np.dot(es, es))

    def grad_E_f64(u: np.ndarray, s: np.ndarray, x_inj: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
        u_hat, s_hat = jacobi_f64(u, s, x_inj)
        eu = u.astype(np.float64) - u_hat
        es = s.astype(np.float64) - s_hat
        du = eu * (1.0 - u_hat * u_hat)
        ds = es * (1.0 - s_hat * s_hat)
        return eu - ds @ W2.T, es - du @ W1.T

    def cost_and_gradC_f64(s: np.ndarray, label: np.ndarray) -> tuple[float, np.ndarray, np.ndarray]:
        logits = (s.astype(np.float64) @ V + c).reshape(16, 4)
        mx = logits.max(axis=1, keepdims=True)
        ex = np.exp(logits - mx)
        probs = ex / ex.sum(axis=1, keepdims=True)
        lse = mx[:, 0] + np.log(ex.sum(axis=1))
        C = float(np.mean(lse - logits[np.arange(16), label]))
        gl = probs.copy()
        gl[np.arange(16), label] -= 1.0
        gl /= 16.0
        return C, gl.reshape(64) @ V.T, logits.argmax(axis=1)

    def theta_grad_dict(puz: list[int], x_inj: np.ndarray, u: np.ndarray, s: np.ndarray) -> dict[str, np.ndarray]:
        x = encode_puz(puz)
        u_hat, s_hat = jacobi_f64(u, s, x_inj)
        du = (u.astype(np.float64) - u_hat) * (1.0 - u_hat * u_hat)
        ds = (s.astype(np.float64) - s_hat) * (1.0 - s_hat * s_hat)
        return {
            "Win": -np.outer(x, ds),
            "bin": -ds,
            "W1": -np.outer(s.astype(np.float64), du),
            "b1": -du,
            "W2": -np.outer(u.astype(np.float64), ds),
            "b2": -ds,
        }

    def theta_grad_flat(puz: list[int], x_inj: np.ndarray, u: np.ndarray, s: np.ndarray) -> np.ndarray:
        g = theta_grad_dict(puz, x_inj, u, s)
        return np.concatenate([g[k].ravel() for k in ("Win", "bin", "W1", "b1", "W2", "b2")])

    def run_free_f32(puz: list[int], eta: float, mom: float, T: int = 150, tol: float = 1e-6) -> tuple[np.ndarray, np.ndarray, np.ndarray, int, float]:
        x_inj = embed_f32(puz)
        u = np.tanh(b1).astype(np.float32)
        s = np.tanh(u.astype(np.float64) @ W2 + b2 + x_inj.astype(np.float64)).astype(np.float32)
        vu = np.zeros_like(u)
        vs = np.zeros_like(s)
        E = energy_f64(u, s, x_inj)
        it = 0
        while it < T and E >= tol:
            gu, gs = grad_E_f64(u, s, x_inj)
            vu = (mom * vu - eta * gu.astype(np.float32)).astype(np.float32)
            vs = (mom * vs - eta * gs.astype(np.float32)).astype(np.float32)
            u = (u + vu).astype(np.float32)
            s = (s + vs).astype(np.float32)
            it += 1
            E = energy_f64(u, s, x_inj)
        return x_inj, u, s, it, E

    def run_nudge_f32(x_inj: np.ndarray, u0: np.ndarray, s0: np.ndarray, label: np.ndarray, beta: float, eta: float, mom: float, T: int = 40) -> tuple[np.ndarray, np.ndarray]:
        u, s = u0.copy(), s0.copy()
        vu, vs = np.zeros_like(u), np.zeros_like(s)
        for _ in range(T):
            gu, gs = grad_E_f64(u, s, x_inj)
            _, gC, _ = cost_and_gradC_f64(s, label)
            gs_tot = (gs.astype(np.float32) + np.float32(beta) * gC.astype(np.float32)).astype(np.float32)
            vu = (mom * vu - eta * gu.astype(np.float32)).astype(np.float32)
            vs = (mom * vs - eta * gs_tot).astype(np.float32)
            u = (u + vu).astype(np.float32)
            s = (s + vs).astype(np.float32)
        return u, s

    def run_free_f64(puz: list[int], eta: float, mom: float, T: int = 150, tol: float = 1e-6) -> tuple[np.ndarray, np.ndarray, np.ndarray, int, float]:
        x_inj = embed_f64(puz)
        u = np.tanh(b1)
        s = np.tanh(u @ W2 + b2 + x_inj)
        vu, vs = np.zeros(256), np.zeros(256)
        E = energy_f64(u, s, x_inj)
        it = 0
        while it < T and E >= tol:
            gu, gs = grad_E_f64(u, s, x_inj)
            vu = mom * vu - eta * gu
            vs = mom * vs - eta * gs
            u = u + vu
            s = s + vs
            it += 1
            E = energy_f64(u, s, x_inj)
        return x_inj, u, s, it, E

    # 1. Exact float32 parity check against best.json["parity"] & ["parity_alt"]
    parity_receipts: dict[str, Any] = {}
    for pk, eta, mom in (("parity", 0.7, 0.7), ("parity_alt", 0.6, 0.0)):
        ref = best[pk]
        idx = int(ref["puzzle_index"])
        puz = puzzles[idx]["puzzle"]
        lbl = np.array(ref["label"], dtype=np.int32)
        x_inj, uf, sf, it, Ef = run_free_f32(puz, eta=eta, mom=mom, T=150, tol=1e-6)
        un, sn = run_nudge_f32(x_inj, uf, sf, lbl, beta=float(ref["nudge"]["beta"]), eta=eta, mom=mom, T=int(ref["nudge"]["T_nudge"]))
        Cn, _, _ = cost_and_gradC_f64(sn, lbl)
        En = energy_f64(un, sn, x_inj)
        du_ref = float(np.max(np.abs(uf - _dec_array(ref["free"]["u"], np.float32))))
        ds_ref = float(np.max(np.abs(sf - _dec_array(ref["free"]["s"], np.float32))))
        dun_ref = float(np.max(np.abs(un - _dec_array(ref["nudge"]["u"], np.float32))))
        dsn_ref = float(np.max(np.abs(sn - _dec_array(ref["nudge"]["s"], np.float32))))
        gp = theta_grad_dict(puz, x_inj, un, sn)
        gf = theta_grad_dict(puz, x_inj, uf, sf)
        beta_v = float(ref["nudge"]["beta"])
        max_gnorm_err = max(
            abs(float(np.linalg.norm((gp[k] - gf[k]) / beta_v)) - float(ref["ep_grad"]["norm"][k]))
            for k in gp
        )
        parity_receipts[pk] = {
            "mode": str(ref["mode"]),
            "puzzle_index": idx,
            "puzzle_id": str(ref["puzzle_id"]),
            "iters": it,
            "ref_iters": int(ref["free"]["iters"]),
            "E_free_sci": _sci_str(Ef),
            "ref_E_free_sci": _sci_str(float(ref["free"]["E"])),
            "max_abs_du_free_sci": _sci_str(du_ref),
            "max_abs_ds_free_sci": _sci_str(ds_ref),
            "max_abs_du_nudge_sci": _sci_str(dun_ref),
            "max_abs_ds_nudge_sci": _sci_str(dsn_ref),
            "E_nudge_dec6": _dec_str(En, 6),
            "ref_E_nudge_dec6": _dec_str(float(ref["nudge"]["E"]), 6),
            "C_nudge_dec6": _dec_str(Cn, 6),
            "ref_C_nudge_dec6": _dec_str(float(ref["nudge"]["C"]), 6),
            "max_ep_grad_norm_err_sci": _sci_str(max_gnorm_err),
        }

    # 2. Full 300-puzzle spectral, Loop-Schur, non-normality, curl, power-iter & GD cliff tomography
    rhos, sigmas, non_norms, curl_angles = [], [], [], []
    init_rhos, init_sigs = [], []
    schur_errs, h_lmins, h_lmaxs, s_lmins, g_lmaxs = [], [], [], [], []
    rho_128 = []
    solved_rhos, wrong_rhos, solved_nns, wrong_nns = [], [], [], []
    pi_err_real, pi_err_cx = [], []
    conv8_lmax, div8_lmax = [], []
    it_list, E_list = [], []
    solved_cnt = 0
    stalled_cnt = 0
    complex_dom_cnt = 0

    for idx, entry in enumerate(puzzles):
        puz = entry["puzzle"]
        sol = np.array(entry["solution"], dtype=np.int32) - 1
        x_inj64 = embed_f64(puz)
        u0 = np.tanh(b1)
        s0 = np.tanh(u0 @ W2 + b2 + x_inj64)
        uh0, sh0 = jacobi_f64(u0, s0, x_inj64)
        M0 = ((1.0 - sh0 * sh0)[:, None] * W2.T) @ ((1.0 - uh0 * uh0)[:, None] * W1.T)
        init_sigs.append(float(np.linalg.svd(M0, compute_uv=False)[0]))
        init_rhos.append(float(np.max(np.abs(np.linalg.eigvals(M0)))))

        x_inj32, uf, sf, it, Ef = run_free_f32(puz, eta=0.7, mom=0.7, T=150, tol=1e-6)
        _, _, pred = cost_and_gradC_f64(sf, sol)
        is_solved = bool(np.all(pred == sol))
        if Ef >= 1e-6:
            stalled_cnt += 1
        elif is_solved:
            solved_cnt += 1
        it_list.append(it)
        E_list.append(Ef)

        u_h, s_h = jacobi_f64(uf, sf, x_inj32)
        A = (1.0 - u_h * u_h)[:, None] * W1.T
        B = (1.0 - s_h * s_h)[:, None] * W2.T
        M = B @ A
        eigs = np.linalg.eigvals(M)
        lam0 = eigs[int(np.argmax(np.abs(eigs)))]
        rho = float(abs(lam0))
        sig = float(np.linalg.svd(M, compute_uv=False)[0])
        ang = float(abs(np.angle(lam0)))
        is_cx = abs(float(lam0.imag)) > 1e-10
        complex_dom_cnt += int(is_cx)
        rhos.append(rho)
        sigmas.append(sig)
        nn = sig / rho
        non_norms.append(nn)
        curl_angles.append(ang)
        if idx < 128 and entry["source"] == "test":
            rho_128.append(rho)
        if is_solved:
            solved_rhos.append(rho)
            solved_nns.append(nn)
        else:
            wrong_rhos.append(rho)
            wrong_nns.append(nn)

        # Full 512x512 Loop-Schur identity & Hessian spectrum on all 300 puzzles
        Huu = I256 + B.T @ B
        Hus = -(A + B.T)
        Hss = I256 + A.T @ A
        S_direct = Hss - Hus.T @ np.linalg.solve(Huu, Hus)
        G_loop = I256 + B @ B.T
        ImM = I256 - M
        S_formula = ImM.T @ np.linalg.solve(G_loop, ImM)
        schur_errs.append(float(np.max(np.abs(S_direct - S_formula))))
        J_R = np.block([[I256, -A], [-B, I256]])
        sv_jr = np.linalg.svd(J_R, compute_uv=False)
        lmin_h = float(sv_jr[-1] ** 2)
        lmax_h = float(sv_jr[0] ** 2)
        h_lmins.append(lmin_h)
        h_lmaxs.append(lmax_h)
        s_lmins.append(float(np.linalg.eigvalsh(S_direct)[0]))
        g_lmaxs.append(float(np.linalg.eigvalsh(G_loop)[-1]))

        # Real 60-step power iteration (exact core/diagnostics.py algorithm)
        rng = np.random.default_rng(1)
        v = rng.standard_normal(256)
        v /= np.linalg.norm(v)
        lam_pi = 0.0
        for _ in range(60):
            Jv = M @ v
            lam_pi = float(np.linalg.norm(Jv))
            v = Jv / (lam_pi + 1e-20)
        rel_pi = abs(lam_pi - rho) / rho
        if is_cx:
            pi_err_cx.append(rel_pi)
        else:
            pi_err_real.append(rel_pi)

        # Plain GD eta=0.8 stability cliff test
        _, _, _, _, E8 = run_free_f64(puz, eta=0.8, mom=0.0, T=150, tol=1e-6)
        if E8 < 1e-6:
            conv8_lmax.append(lmax_h)
        else:
            div8_lmax.append(lmax_h)

    # 3. Exact DEQ IFT vs Centered/One-Sided EP & Truncated-Free-Phase O(e*/beta) Sweep
    def solve_exact_free(puz: list[int]) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
        x_inj = embed_f64(puz)
        u = np.tanh(b1)
        s = np.tanh(u @ W2 + b2 + x_inj)
        for _ in range(300):
            un = np.tanh(s @ W1 + b1)
            sn = np.tanh(un @ W2 + b2 + x_inj)
            if np.linalg.norm(un - u) + np.linalg.norm(sn - s) < 1e-15:
                u, s = un, sn
                break
            u, s = un, sn
        return x_inj, u, s

    def solve_exact_nudge(x_inj: np.ndarray, u0: np.ndarray, s0: np.ndarray, lbl: np.ndarray, beta: float) -> tuple[np.ndarray, np.ndarray, float]:
        u, s = u0.copy(), s0.copy()
        vu, vs = np.zeros(256), np.zeros(256)
        for _ in range(1500):
            gu, gs = grad_E_f64(u, s, x_inj)
            _, gC, _ = cost_and_gradC_f64(s, lbl)
            gs_t = gs + beta * gC
            if np.linalg.norm(gu) + np.linalg.norm(gs_t) < 1e-13:
                break
            vu = 0.7 * vu - 0.6 * gu
            vs = 0.7 * vs - 0.6 * gs_t
            u, s = u + vu, s + vs
        gu, gs = grad_E_f64(u, s, x_inj)
        _, gC, _ = cost_and_gradC_f64(s, lbl)
        return u, s, float(np.linalg.norm(gu) + np.linalg.norm(gs + beta * gC))

    def exact_deq_ift(puz: list[int], x_inj: np.ndarray, u_st: np.ndarray, s_st: np.ndarray, lbl: np.ndarray) -> tuple[np.ndarray, float]:
        uh, sh = jacobi_f64(u_st, s_st, x_inj)
        du, ds = 1.0 - uh * uh, 1.0 - sh * sh
        A, B = du[:, None] * W1.T, ds[:, None] * W2.T
        M = B @ A
        _, gC, _ = cost_and_gradC_f64(s_st, lbl)
        e_s = -np.linalg.solve(I256 - M.T, gC)
        e_u = B.T @ e_s
        J_R = np.block([[I256, -A], [-B, I256]])
        dz = np.linalg.solve(J_R.T @ J_R, np.concatenate([np.zeros(256), -gC]))
        adj_err = float(np.max(np.abs(J_R @ dz - np.concatenate([e_u, e_s]))))
        x = encode_puz(puz)
        du_e, ds_e = e_u * du, e_s * ds
        g_ift = np.concatenate([
            (-np.outer(x, ds_e)).ravel(), -ds_e,
            (-np.outer(s_st, du_e)).ravel(), -du_e,
            (-np.outer(u_st, ds_e)).ravel(), -ds_e,
        ])
        return g_ift, adj_err

    ep_tomography: dict[str, Any] = {}
    for pidx in (16, 65):
        entry = puzzles[pidx]
        puz = entry["puzzle"]
        lbl = np.array(entry["solution"], dtype=np.int32) - 1
        x_inj, u_ex, s_ex = solve_exact_free(puz)
        g_ift, adj_err = exact_deq_ift(puz, x_inj, u_ex, s_ex, lbl)
        gnorm = float(np.linalg.norm(g_ift))

        exact_rows = []
        for beta_s in ("0.5", "0.2", "0.1", "0.05", "0.01", "0.002"):
            b = float(beta_s)
            up, sp, rp = solve_exact_nudge(x_inj, u_ex, s_ex, lbl, +b)
            um, sm, rm = solve_exact_nudge(x_inj, u_ex, s_ex, lbl, -b)
            gp = theta_grad_flat(puz, x_inj, up, sp)
            gm = theta_grad_flat(puz, x_inj, um, sm)
            g1 = gp / b
            gc = (gp - gm) / (2.0 * b)
            exact_rows.append({
                "beta": beta_s,
                "one_sided_rel_err_dec8": _dec_str(float(np.linalg.norm(g1 - g_ift) / gnorm), 8),
                "one_sided_cos_dec8": _dec_str(float(np.dot(g1, g_ift) / (np.linalg.norm(g1) * gnorm)), 8),
                "centered_rel_err_dec8": _dec_str(float(np.linalg.norm(gc - g_ift) / gnorm), 8),
                "centered_cos_dec8": _dec_str(float(np.dot(gc, g_ift) / (np.linalg.norm(gc) * gnorm)), 8),
                "max_nudge_res_sci": _sci_str(max(rp, rm)),
            })

        trunc_regimes = []
        for reg_name, T_f, tol_f in (("T10", 10, 0.0), ("T20", 20, 0.0), ("default_E_lt_1e6", 150, 1e-6)):
            _, uf, sf, it_f, Ef = run_free_f64(puz, eta=0.7, mom=0.7, T=T_f, tol=tol_f)
            gf = theta_grad_flat(puz, x_inj, uf, sf)
            e_norm = math.sqrt(2.0 * Ef)
            rows = []
            for beta_s in ("0.2", "0.05", "0.01", "0.002", "0.0005"):
                b = float(beta_s)
                def nudge40(bv: float) -> np.ndarray:
                    u, s = uf.copy(), sf.copy()
                    vu, vs = np.zeros(256), np.zeros(256)
                    for _ in range(40):
                        gu, gs = grad_E_f64(u, s, x_inj)
                        _, gC, _ = cost_and_gradC_f64(s, lbl)
                        vu = 0.7 * vu - 0.7 * gu
                        vs = 0.7 * vs - 0.7 * (gs + bv * gC)
                        u, s = u + vu, s + vs
                    return theta_grad_flat(puz, x_inj, u, s)
                gp40 = nudge40(+b)
                gm40 = nudge40(-b)
                g_nosub = gp40 / b
                g_sub = (gp40 - gf) / b
                g_cent = (gp40 - gm40) / (2.0 * b)
                rows.append({
                    "beta": beta_s,
                    "nosub_rel_err_dec6": _dec_str(float(np.linalg.norm(g_nosub - g_ift) / gnorm), 6),
                    "nosub_cos_dec6": _dec_str(float(np.dot(g_nosub, g_ift) / (np.linalg.norm(g_nosub) * gnorm)), 6),
                    "sub_rel_err_dec6": _dec_str(float(np.linalg.norm(g_sub - g_ift) / gnorm), 6),
                    "sub_cos_dec6": _dec_str(float(np.dot(g_sub, g_ift) / (np.linalg.norm(g_sub) * gnorm)), 6),
                    "centered_rel_err_dec6": _dec_str(float(np.linalg.norm(g_cent - g_ift) / gnorm), 6),
                    "centered_cos_dec6": _dec_str(float(np.dot(g_cent, g_ift) / (np.linalg.norm(g_cent) * gnorm)), 6),
                })
            trunc_regimes.append({
                "regime": reg_name,
                "free_iters": it_f,
                "E_free_sci": _sci_str(Ef),
                "residual_norm_dec6": _dec_str(e_norm, 6),
                "free_theta_grad_norm_dec6": _dec_str(float(np.linalg.norm(gf)), 6),
                "beta_rows": rows,
            })

        ep_tomography[entry["id"]] = {
            "puzzle_index": pidx,
            "exact_E_sci": _sci_str(energy_f64(u_ex, s_ex, x_inj)),
            "ift_grad_norm_dec6": _dec_str(gnorm, 6),
            "gloop_adjoint_cancel_max_abs_err_sci": _sci_str(adj_err),
            "exact_phase_beta_sweep": exact_rows,
            "truncated_free_phase_sweep": trunc_regimes,
        }

    receipt = {
        "schema_version": "aletheia.track_s76.circularep_live_anchor.v1",
        "track_id": "TRACK-S76-CIRCULAR-PC-LOOP-SCHUR-HOLONOMY",
        "upstream": {
            "repo": "rel-int/CircularEP",
            "arxiv_id": "2611.27610",
            "commit_sha": commit_sha,
            "best_json_sha256": _sha256_file(best_path),
            "puzzles_json_sha256": _sha256_file(puzzles_path),
            "model_js_sha256": _sha256_file(model_js_path),
            "core_ep_py_sha256": _sha256_file(core_ep_path),
            "core_diagnostics_py_sha256": _sha256_file(core_diag_path),
            "model_dims": {"N": 4, "P": 16, "din": 80, "H": 256, "n_classes": 64, "act": "tanh"},
            "sigma_W1_dec9": _dec_str(sigma_w1, 9),
            "sigma_W2_dec9": _dec_str(sigma_w2, 9),
            "ref_sigma_W1_dec9": _dec_str(float(best["meta"]["sigma"]["W1"]), 9),
            "ref_sigma_W2_dec9": _dec_str(float(best["meta"]["sigma"]["W2"]), 9),
        },
        "float32_parity": parity_receipts,
        "tomography_300_puzzles": {
            "n_puzzles": len(puzzles),
            "solved_count": solved_cnt,
            "converged_wrong_count": len(puzzles) - solved_cnt - stalled_cnt,
            "stalled_count": stalled_cnt,
            "ref_solved_count": int(best["meta"]["metrics"]["shipped"]["solved"]),
            "ref_converged_wrong_count": int(best["meta"]["metrics"]["shipped"]["converged_wrong"]),
            "median_free_iters_dec1": _dec_str(float(np.median(it_list)), 1),
            "max_E_free_sci": _sci_str(max(E_list)),
            "rho_first_128_test": {
                "n": len(rho_128),
                "median_dec6": _dec_str(float(np.median(rho_128)), 6),
                "p90_dec6": _dec_str(float(np.percentile(rho_128, 90)), 6),
                "max_dec6": _dec_str(max(rho_128), 6),
                "mean_dec6": _dec_str(float(np.mean(rho_128)), 6),
                "ref_median_dec6": _dec_str(float(best["meta"]["metrics"]["rho_J"]["median"]), 6),
                "ref_p90_dec6": _dec_str(float(best["meta"]["metrics"]["rho_J"]["p90"]), 6),
                "ref_max_dec6": _dec_str(float(best["meta"]["metrics"]["rho_J"]["max"]), 6),
                "ref_mean_dec6": _dec_str(float(best["meta"]["metrics"]["rho_J"]["mean"]), 6),
            },
            "init_ff_spectra": {
                "rho_min_dec6": _dec_str(min(init_rhos), 6),
                "rho_median_dec6": _dec_str(float(np.median(init_rhos)), 6),
                "rho_max_dec6": _dec_str(max(init_rhos), 6),
                "norm2_min_dec6": _dec_str(min(init_sigs), 6),
                "norm2_median_dec6": _dec_str(float(np.median(init_sigs)), 6),
                "norm2_max_dec6": _dec_str(max(init_sigs), 6),
            },
            "equilibrium_spectra": {
                "rho_min_dec6": _dec_str(min(rhos), 6),
                "rho_median_dec6": _dec_str(float(np.median(rhos)), 6),
                "rho_p90_dec6": _dec_str(float(np.percentile(rhos, 90)), 6),
                "rho_max_dec6": _dec_str(max(rhos), 6),
                "norm2_min_dec6": _dec_str(min(sigmas), 6),
                "norm2_median_dec6": _dec_str(float(np.median(sigmas)), 6),
                "norm2_p90_dec6": _dec_str(float(np.percentile(sigmas, 90)), 6),
                "norm2_max_dec6": _dec_str(max(sigmas), 6),
                "non_normality_min_dec6": _dec_str(min(non_norms), 6),
                "non_normality_median_dec6": _dec_str(float(np.median(non_norms)), 6),
                "non_normality_p90_dec6": _dec_str(float(np.percentile(non_norms, 90)), 6),
                "non_normality_max_dec6": _dec_str(max(non_norms), 6),
                "complex_dominant_count": complex_dom_cnt,
                "real_dominant_count": len(puzzles) - complex_dom_cnt,
                "max_abs_arg_rad_dec6": _dec_str(max(curl_angles), 6),
            },
            "solved_vs_wrong_separation": {
                "solved_median_rho_dec6": _dec_str(float(np.median(solved_rhos)), 6),
                "solved_mean_rho_dec6": _dec_str(float(np.mean(solved_rhos)), 6),
                "solved_median_nn_dec6": _dec_str(float(np.median(solved_nns)), 6),
                "wrong_median_rho_dec6": _dec_str(float(np.median(wrong_rhos)), 6),
                "wrong_mean_rho_dec6": _dec_str(float(np.mean(wrong_rhos)), 6),
                "wrong_median_nn_dec6": _dec_str(float(np.median(wrong_nns)), 6),
            },
            "loop_schur_and_hessian_512x512": {
                "n_verified": len(schur_errs),
                "max_schur_identity_abs_err_sci": _sci_str(max(schur_errs)),
                "h_pc_lambda_min_lo_dec6": _dec_str(min(h_lmins), 6),
                "h_pc_lambda_min_hi_dec6": _dec_str(max(h_lmins), 6),
                "h_pc_lambda_max_lo_dec6": _dec_str(min(h_lmaxs), 6),
                "h_pc_lambda_max_hi_dec6": _dec_str(max(h_lmaxs), 6),
                "schur_lambda_min_lo_dec6": _dec_str(min(s_lmins), 6),
                "schur_lambda_min_hi_dec6": _dec_str(max(s_lmins), 6),
                "g_loop_lambda_max_lo_dec6": _dec_str(min(g_lmaxs), 6),
                "g_loop_lambda_max_hi_dec6": _dec_str(max(g_lmaxs), 6),
            },
            "power_iter_60_curl_bias": {
                "real_dom_count": len(pi_err_real),
                "real_dom_median_rel_err_sci": _sci_str(float(np.median(pi_err_real))),
                "real_dom_max_rel_err_dec6": _dec_str(max(pi_err_real), 6),
                "complex_dom_count": len(pi_err_cx),
                "complex_dom_median_rel_err_dec6": _dec_str(float(np.median(pi_err_cx)), 6),
                "complex_dom_max_rel_err_dec6": _dec_str(max(pi_err_cx), 6),
            },
            "plain_gd_eta_0p8_cliff": {
                "eta": "0.8",
                "euler_crit_lambda_max": "2.500000",
                "converged_count": len(conv8_lmax),
                "diverged_count": len(div8_lmax),
                "converged_with_lmax_le_2p5": sum(1 for x in conv8_lmax if x <= 2.5),
                "diverged_with_lmax_gt_2p5": sum(1 for x in div8_lmax if x > 2.5),
                "converged_lmax_median_dec6": _dec_str(float(np.median(conv8_lmax)), 6),
                "converged_lmax_max_dec6": _dec_str(max(conv8_lmax), 6),
                "diverged_lmax_median_dec6": _dec_str(float(np.median(div8_lmax)), 6),
                "diverged_lmax_min_dec6": _dec_str(min(div8_lmax), 6),
            },
        },
        "ep_gradient_tomography": ep_tomography,
    }

    raw_bytes = (json.dumps(receipt, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode("ascii")
    fd = os.open(str(_OUT_PATH), os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    try:
        os.write(fd, raw_bytes)
        os.fsync(fd)
    finally:
        os.close(fd)
    os.chmod(_OUT_PATH, 0o600)
    print(f"WROTE {_OUT_PATH.name} bytes={len(raw_bytes)} sha256={hashlib.sha256(raw_bytes).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
