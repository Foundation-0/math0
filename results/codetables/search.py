"""Attack ~15 smallest-gap open codetables.de entries over GF(3)/GF(4)/GF(5).

Targets (TARGETS below) were picked from a live regeneration of the census
in data/codetables/ on 2026-10-18 (counts identical to the committed
census-2026-10-18.json).  Only these specific (q,n,k,lb,ub) entries are
committed here; Grassl's full tables are NOT (regenerate them locally with
data/codetables/census.py --csv).

Search families, per target:
  1. random generator matrices (random projective column multisets);
  2. greedy column augmentation + simulated-annealing column swaps,
     scored on the *exact* weight spectrum over all messages
     (the Spectrum class: for a column multiset C, the codeword weight
     for message u is #{c in C : u.c != 0}; the minimum over all
     normalised u is the exact minimum distance of that code, provided
     the columns span GF(q)^k, which is checked separately);
  3. cyclic and constacyclic codes: every monic generator polynomial
     g of degree n-k with g | x^n - lambda, when q^(n-k) is within budget;
  4. double-circulant codes [I | Circ(a)] when n = 2k (random a);
  5. shortening / puncturing / parity-extending the classical codes in
     gfq.codes, and (phase 2) the best codes found here for neighbouring
     parameters.

Every candidate that is *reported* (best per family and best overall per
target) is re-verified independently with gfq's exact checker
(gfq.min_distance, and the gfq CLI for the best overall).  The spectrum
score is used only to guide the search; no claim rests on it alone.

Usage:
    python3 results/codetables/search.py [--seconds 25] [--seed 20261018]
                                        [--only 5,16,5] [--quick]
Writes results.json (checkpointed after each target), best matrices and
gfq CLI certificates under results/codetables/.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import random
import subprocess
import sys
import time

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", ".."))

from gfq import GF, min_distance                      # noqa: E402
from gfq.codes import (hamming_generator, reed_solomon_generator,  # noqa: E402
                       repetition_generator, single_parity_generator,
                       ternary_golay_generator)
from gfq.matrix import combine, nullspace_basis, rank, rref  # noqa: E402

TABLE_DATE = "2026-10-18"
TABLE_SOURCE = "https://www.codetables.de/BKLC/ (Markus Grassl), Tables_color.php per field"

# (q, n, k, lower_bound, upper_bound) -- all gap 1 on TABLE_DATE, smallest n
# per field with k <= 10 so exact verification stays fast.  The GF(5)
# (18,9) entry is included (instead of (18,7)) so that the double-circulant
# family (n = 2k) is exercised on at least one target.
TARGETS = [
    (3, 22, 8, 9, 10), (3, 23, 8, 10, 11), (3, 23, 9, 9, 10),
    (3, 24, 9, 10, 11), (3, 24, 10, 9, 10),
    (4, 19, 8, 8, 9), (4, 20, 9, 8, 9), (4, 22, 6, 12, 13),
    (4, 23, 7, 12, 13), (4, 24, 8, 12, 13),
    (5, 16, 5, 9, 10), (5, 16, 6, 8, 9), (5, 17, 6, 9, 10),
    (5, 17, 7, 8, 9), (5, 18, 9, 7, 8),
]

HERE = os.path.dirname(os.path.abspath(__file__))


# --------------------------------------------------------------------------
# Exact weight spectrum over all messages (search scoring only)
# --------------------------------------------------------------------------
class Spectrum:
    def __init__(self, q: int, k: int):
        self.F = GF(q)
        self.q, self.k = q, k
        self.add = np.array(self.F._add, dtype=np.int64)
        self.mul = np.array(self.F._mul, dtype=np.int64)
        N = q ** k
        V = np.zeros((N, k), dtype=np.int16)
        tmp = np.arange(N, dtype=np.int64)
        for i in range(k):
            V[:, i] = tmp % q
            tmp //= q
        seen_nz = np.zeros(N, dtype=bool)
        first_is_one = np.ones(N, dtype=bool)
        for i in range(k):
            col = V[:, i]
            first_here = (~seen_nz) & (col != 0)
            first_is_one &= ~(first_here & (col != 1))
            seen_nz |= col != 0
        mask = seen_nz & first_is_one
        self.U = V[mask].astype(np.int64)  # one msg per scalar class
        self.P = self.U             # projective points (column reps)
        self.M = len(self.U)
        self._p_index = {tuple(r): i for i, r in enumerate(self.P.tolist())}

    def dot_nz(self, c) -> np.ndarray:
        acc = np.zeros(self.M, dtype=np.int64)
        for i in range(self.k):
            if c[i]:
                acc = self.add[acc, self.mul[self.U[:, i], int(c[i])]]
        return acc != 0

    def weights(self, cols) -> np.ndarray:
        W = np.zeros(self.M, dtype=np.int64)
        for c in cols:
            W += self.dot_nz(c)
        return W

    def normalize_col(self, c):
        """Projective representative (first nonzero entry scaled to 1)."""
        c = list(c)
        for i, a in enumerate(c):
            if a:
                inv = self.F.inv(a)
                return tuple(self.F.mul(inv, x) for x in c)
        return None                 # zero column: useless, dropped by caller


def penalty(W: np.ndarray, target: int) -> int:
    short = np.maximum(0, target - W)
    return int((short * short).sum())


def cols_to_matrix(cols, k: int):
    return [[int(cols[j][i]) for j in range(len(cols))] for i in range(k)]


def matrix_to_cols(G):
    k, n = len(G), len(G[0])
    return [tuple(G[i][j] for i in range(k)) for j in range(n)]


# --------------------------------------------------------------------------
# Random + greedy + anneal (all scored on the exact spectrum)
# --------------------------------------------------------------------------
def random_cols(sp: Spectrum, n: int, rng: random.Random):
    return [tuple(sp.P[rng.randrange(sp.M)].tolist()) for _ in range(n)]


def greedy_cols(sp: Spectrum, n: int, target: int, rng: random.Random,
                pool: int | None = None):
    if pool is None:                # ~2 s of dot products, any spectrum size
        pool = max(6, min(120, int(2.0 / (sp.M * 35e-9) / n)))
    cols, W = [], np.zeros(sp.M, dtype=np.int64)
    for _ in range(n):
        best_c, best_score = None, None
        for _ in range(pool):
            c = tuple(sp.P[rng.randrange(sp.M)].tolist())
            score = int(np.minimum(W + sp.dot_nz(c), target).sum())
            if best_score is None or score > best_score:
                best_c, best_score = c, score
        cols.append(best_c)
        W += sp.dot_nz(best_c)
    return cols


def anneal(sp: Spectrum, cols, target: int, seconds: float,
           rng: random.Random):
    """Simulated annealing on column swaps.  Returns (cols, stats)."""
    cols = list(cols)
    nz = [sp.dot_nz(c) for c in cols]
    W = np.zeros(sp.M, dtype=np.int64)
    for v in nz:
        W += v
    pen = penalty(W, target)
    best_cols, best_pen = list(cols), pen
    best_min = int(W.min())
    steps = accepted = 0
    t0 = time.time()
    temp = 2.0
    while time.time() - t0 < seconds:
        steps += 1
        j = rng.randrange(len(cols))
        if rng.random() < 0.5:
            # guided: pick a low-weight message, propose a column it sees
            low = np.flatnonzero(W <= W.min() + 1)
            u = sp.U[int(low[rng.randrange(len(low))])]
            for _ in range(20):
                c = tuple(sp.P[rng.randrange(sp.M)].tolist())
                acc = 0
                for i in range(sp.k):
                    acc = sp.F.add(acc, sp.F.mul(int(u[i]), c[i]))
                if acc != 0:
                    break
        else:
            c = tuple(sp.P[rng.randrange(sp.M)].tolist())
        new_nz = sp.dot_nz(c)
        W2 = W - nz[j] + new_nz
        pen2 = penalty(W2, target)
        if pen2 <= pen or rng.random() < math.exp(-(pen2 - pen) / temp):
            cols[j], nz[j], W, pen = c, new_nz, W2, pen2
            accepted += 1
            m = int(W.min())
            if pen < best_pen or (pen == best_pen and m > best_min):
                best_cols, best_pen, best_min = list(cols), pen, m
                if pen == 0:
                    break
        temp = max(0.05, temp * 0.9995)
        if steps % 4000 == 0:
            temp = 1.0              # periodic reheat
    return best_cols, {"steps": steps, "accepted": accepted,
                       "final_penalty": best_pen, "spectrum_min": best_min}


# --------------------------------------------------------------------------
# Cyclic / constacyclic exhaustive (budgeted), double-circulant random
# --------------------------------------------------------------------------
def _poly_divmod(a, mod, F: GF):
    """(quotient, remainder) of a / mod, polynomials low -> high."""
    a = list(a)
    dm = len(mod) - 1
    while dm > 0 and mod[dm] == 0:
        dm -= 1
    quot = [0] * max(1, len(a) - dm)
    d = len(a) - 1
    while d >= dm:
        if a[d]:
            c = F.div(a[d], mod[dm])
            quot[d - dm] = c
            for j in range(dm + 1):
                a[d - dm + j] = F.sub(a[d - dm + j], F.mul(c, mod[j]))
        d -= 1
    rem = a[:dm] if dm else [0]
    while len(quot) > 1 and quot[-1] == 0:
        quot.pop()
    return quot, rem


def cyclic_search(sp: Spectrum, n: int, k: int, budget: int = 600_000):
    """All cyclic/constacyclic [n,k] codes, via their check polynomials.

    Enumerates every monic h of degree k; h is the check polynomial of a
    (consta)cyclic code of dimension k iff h | x^n - lambda for some
    lambda != 0, in which case the generator polynomial is
    g = (x^n - lambda)/h.  One division per h suffices: with
    (x^n - 1) = h*g + r, we have h | x^n - lambda iff r is the constant
    polynomial lambda - 1 (and then the same g is the quotient).
    Exhaustive when q^k <= budget, else skipped with a stated reason.
    """
    F, q = sp.F, sp.q
    total = q ** k
    if total > budget:
        return None, {"skipped": f"q^k={total} > budget {budget}",
                      "polys_tested": 0, "divisors": 0}
    xn1 = [0] * (n + 1)
    xn1[0] = F.neg(1)
    xn1[n] = 1
    best, best_min, tested, divisors = None, -1, 0, 0
    for code in range(total):
        h, tmp = [], code
        for _ in range(k):
            h.append(tmp % q)
            tmp //= q
        h.append(1)
        tested += 1
        g, r = _poly_divmod(xn1, h, F)
        if any(r[1:]):
            continue                # no lambda makes h a divisor
        lam = F.add(r[0], 1) if r else 1
        if lam == 0:
            continue
        divisors += 1
        G = []
        for i in range(k):
            row = [0] * i + list(g) + [0] * (n - i - len(g))
            G.append(row[:n])
        cols = matrix_to_cols(G)
        d = int(sp.weights(cols).min())
        if d > best_min:
            best, best_min = cols, d
    return best, {"polys_tested": tested, "divisors": divisors,
                  "spectrum_min": best_min}


def double_circulant_search(sp: Spectrum, n: int, k: int,
                            rng: random.Random, samples: int = 3000):
    if n != 2 * k:
        return None, {"skipped": "needs n = 2k", "samples": 0}
    F, q = sp.F, sp.q
    best, best_min, done = None, -1, 0
    t0 = time.time()
    for _ in range(samples):
        if done and time.time() - t0 > 10.0:
            break
        done += 1
        a = [rng.randrange(q) for _ in range(k)]
        G = []
        for i in range(k):
            row = [1 if j == i else 0 for j in range(k)]
            row += [a[(j - i) % k] for j in range(k)]
            G.append(row)
        cols = matrix_to_cols(G)
        d = int(sp.weights(cols).min())
        if d > best_min:
            best, best_min = cols, d
    return best, {"samples": done, "spectrum_min": best_min}


# --------------------------------------------------------------------------
# Derivations: puncture / shorten / parity-extend
# --------------------------------------------------------------------------
def puncture(G, F: GF, drop):
    keep = [j for j in range(len(G[0])) if j not in set(drop)]
    rows, _ = rref([[row[j] for j in keep] for row in G], F)
    return rows


def shorten(G, F: GF, coords, basis=None):
    if basis is None:
        basis, _ = rref(G, F)
    k = len(basis)
    H = [[basis[j][s] for j in range(k)] for s in coords]   # |S| x k
    msgs = nullspace_basis(H, F)
    if not msgs:
        return []
    keep = [j for j in range(len(G[0])) if j not in set(coords)]
    rows = [[combine(basis, u, F)[j] for j in keep] for u in msgs]
    rows, _ = rref(rows, F)
    return rows


def extend_parity(G, F: GF):
    out = []
    for row in G:
        s = 0
        for a in row:
            s = F.add(s, a)
        out.append(list(row) + [F.neg(s)])
    return out


def derivations(G, F: GF):
    """Yield (label, matrix) for 1- and 2-coordinate derivations."""
    n = len(G[0])
    basis, _ = rref(G, F)
    yield "extend_parity", extend_parity(G, F)
    for a in range(n):
        yield f"puncture[{a}]", puncture(G, F, [a])
        s = shorten(G, F, [a], basis)
        if s:
            yield f"shorten[{a}]", s
    for a in range(n):
        for b in range(a + 1, n):
            yield f"puncture[{a},{b}]", puncture(G, F, [a, b])
            s = shorten(G, F, [a, b], basis)
            if s:
                yield f"shorten[{a},{b}]", s


def seed_codes(q: int):
    """Classical codes from gfq.codes over GF(q): (label, matrix)."""
    F = GF(q)
    out = []
    for r in (2, 3):
        try:
            out.append((f"hamming_r{r}", hamming_generator(F, r)))
        except ValueError:
            pass
    for n in range(2, q + 1):
        for k in range(1, n + 1):
            out.append((f"reed_solomon[{n},{k}]",
                        reed_solomon_generator(F, n, k)))
    if q == 3:
        out.append(("ternary_golay[11,6]", ternary_golay_generator(False)))
        out.append(("ternary_golay_ext[12,6]", ternary_golay_generator(True)))
    for n in range(2, 30):
        out.append((f"repetition[{n},1]", repetition_generator(F, n)))
        out.append((f"single_parity[{n},{n-1}]",
                    single_parity_generator(F, n)))
    return out


# --------------------------------------------------------------------------
# Independent verification with gfq (the only basis for reported d)
# --------------------------------------------------------------------------
def verify_with_gfq(G, q: int):
    F = GF(q)
    res = min_distance(G, F, method="auto")
    return {"n": res.n, "k": res.k, "d": res.d,
            "lower_bound": res.lower_bound, "upper_bound": res.upper_bound,
            "complete": res.complete, "method": res.method,
            "enumerated": res.enumerated,
            "codeword_certificate": res.codeword}


def write_matrix(path, G):
    with open(path, "w") as fh:
        for row in G:
            fh.write(" ".join(str(a) for a in row) + "\n")


def cli_certificate(G, q: int, stem: str):
    """Save matrix + `python3 -m gfq --json` output; return parsed JSON."""
    mpath = os.path.join(HERE, stem + ".txt")
    write_matrix(mpath, G)
    proc = subprocess.run(
        [sys.executable, "-m", "gfq", "--q", str(q), "--json", mpath],
        capture_output=True, text=True,
        cwd=os.path.join(HERE, "..", ".."))
    cert = {"command": f"python3 -m gfq --q {q} --json {stem}.txt",
            "exit_code": proc.returncode, "stdout": proc.stdout,
            "stderr": proc.stderr}
    with open(os.path.join(HERE, stem + ".gfq.json"), "w") as fh:
        json.dump(cert, fh, indent=1)
    try:
        cert["parsed"] = json.loads(proc.stdout)
    except json.JSONDecodeError:
        cert["parsed"] = None
    return cert


def consider(best: dict, family: str, G, q: int, k_want: int, stats: dict):
    """gfq-verify a family-best candidate; keep it if it beats `best`."""
    if G is None or not G or not G[0]:
        return best, None
    F = GF(q)
    if rank(G, F) != k_want:
        return best, {"family": family, "rejected": "rank != k",
                      "stats": stats}
    ver = verify_with_gfq(G, q)
    rec = {"family": family, "stats": stats, "gfq": ver,
           "generator": [[int(a) for a in row] for row in G]}
    if ver["complete"] and (best is None or ver["d"] > best["gfq"]["d"]):
        return rec, rec
    return best, rec


# --------------------------------------------------------------------------
# Per-target driver
# --------------------------------------------------------------------------
def run_target(t, seconds: float, rng: random.Random, derived_hits: dict):
    q, n, k, lb, ub = t
    target = lb + 1
    print(f"== GF({q}) [{n},{k}] table {lb}-{ub}, attacking d>={target}",
          flush=True)
    t0 = time.time()
    sp = Spectrum(q, k)
    families = []
    best = None

    # 1. random baseline (200 samples or ~3 s, whichever first)
    rbest, rbest_min, n_random = None, -1, 0
    rt0 = time.time()
    while n_random < 200 and (n_random == 0 or time.time() - rt0 < 3.0):
        n_random += 1
        cols = random_cols(sp, n, rng)
        d = int(sp.weights(cols).min())
        if d > rbest_min:
            rbest, rbest_min = cols, d
    families.append({"family": "random", "samples": n_random,
                     "spectrum_min_best": rbest_min})
    best, rec = consider(best, "random", cols_to_matrix(rbest, k), q, k,
                         families[-1])
    if rec and "gfq" in rec:
        families[-1]["gfq_d"] = rec["gfq"]["d"]

    # 2. greedy + anneal restarts within the time budget
    restarts = []
    deadline = time.time() + seconds
    r = 0
    while time.time() < deadline:
        r += 1
        seed_cols = (greedy_cols(sp, n, target, rng) if r % 2 == 1
                     else random_cols(sp, n, rng))
        slice_s = max(1.0, (deadline - time.time()) / 2)
        cols, stats = anneal(sp, seed_cols, target,
                             min(slice_s, max(1.0, seconds / 3)), rng)
        stats["seed"] = "greedy" if r % 2 == 1 else "random"
        restarts.append(stats)
        best, rec = consider(best, "greedy+anneal",
                             cols_to_matrix(cols, k), q, k, stats)
        if best and best["gfq"]["d"] >= target:
            break
        if r >= 6:
            break
    fam = {"family": "greedy+anneal", "restarts": restarts,
           "total_steps": sum(s["steps"] for s in restarts)}
    families.append(fam)

    # 3. cyclic / constacyclic
    cols, stats = cyclic_search(sp, n, k)
    fam = {"family": "cyclic+constacyclic", **stats}
    families.append(fam)
    if cols is not None:
        best, rec = consider(best, "cyclic+constacyclic",
                             cols_to_matrix(cols, k), q, k, stats)
        if rec and "gfq" in rec:
            fam["gfq_d"] = rec["gfq"]["d"]

    # 4. double-circulant (n = 2k only)
    cols, stats = double_circulant_search(sp, n, k, rng)
    fam = {"family": "double_circulant_QC", **stats}
    families.append(fam)
    if cols is not None:
        best, rec = consider(best, "double_circulant_QC",
                             cols_to_matrix(cols, k), q, k, stats)
        if rec and "gfq" in rec:
            fam["gfq_d"] = rec["gfq"]["d"]

    # 5a. derivations of gfq.codes seeds that land on this target
    hits = derived_hits.get((q, n, k), [])
    fam = {"family": "gfq.codes derivations",
           "candidates_matching_target": len(hits), "hits": []}
    for label, G in hits:
        best, rec = consider(best, f"derived:{label}", G, q, k, {})
        if rec and "gfq" in rec:
            fam["hits"].append({"derivation": label,
                                "gfq_d": rec["gfq"]["d"]})
    families.append(fam)

    result = {"q": q, "n": n, "k": k, "table_lower": lb, "table_upper": ub,
              "table_date": TABLE_DATE, "target_d": target,
              "families": families,
              "best_gfq_d": best["gfq"]["d"] if best else None,
              "best_family": best["family"] if best else None,
              "beats_table_lower": bool(best and best["gfq"]["complete"]
                                        and best["gfq"]["d"] > lb),
              "best_generator": best["generator"] if best else None,
              "best_gfq": best["gfq"] if best else None,
              "wall_seconds": round(time.time() - t0, 2)}
    print(f"   best gfq d = {result['best_gfq_d']} via "
          f"{result['best_family']} (table lb {lb}) "
          f"in {result['wall_seconds']}s", flush=True)
    return result


def second_pass(seconds: float, seed: int):
    """Longer annealing from each target's recorded best code, new seed.

    Updates results.json in place (checkpointed per target); a target's
    best code/certificate is replaced only on a gfq-verified improvement.
    """
    out_path = os.path.join(HERE, "results.json")
    out = json.load(open(out_path))
    rng = random.Random(seed)
    for r in out["targets"]:
        q, n, k, lb = r["q"], r["n"], r["k"], r["table_lower"]
        target = lb + 1
        sp = Spectrum(q, k)
        stats = {"seed": seed, "seconds_budget": seconds, "runs": []}
        starts = []
        if r["best_generator"]:
            cols = []
            for c in matrix_to_cols(r["best_generator"]):
                nc = sp.normalize_col(c)
                cols.append(nc if nc is not None
                            else tuple(sp.P[rng.randrange(sp.M)].tolist()))
            starts.append(("from_best", cols))
        starts.append(("greedy", greedy_cols(sp, n, target, rng)))
        best = {"gfq": r["best_gfq"], "generator": r["best_generator"],
                "family": r["best_family"]}
        for label, seed_cols in starts:
            cols, st = anneal(sp, seed_cols, target,
                              seconds / len(starts), rng)
            st["seed"] = label
            stats["runs"].append(st)
            best, _ = consider(best, f"second_pass:{label}",
                               cols_to_matrix(cols, k), q, k, st)
            if best["gfq"]["d"] >= target:
                break
        stats["best_gfq_d_after"] = best["gfq"]["d"]
        r.setdefault("second_passes", []).append(stats)
        if best["gfq"]["d"] > r["best_gfq_d"]:
            import glob
            for old in glob.glob(os.path.join(
                    HERE, "best", f"q{q}_n{n}_k{k}_d*")):
                os.remove(old)
            r["best_gfq_d"] = best["gfq"]["d"]
            r["best_family"] = best["family"]
            r["best_generator"] = best["generator"]
            r["best_gfq"] = best["gfq"]
            r["beats_table_lower"] = best["gfq"]["d"] > lb
            stem = f"best/q{q}_n{n}_k{k}_d{best['gfq']['d']}"
            cert = cli_certificate(best["generator"], q, stem)
            r["cli_certificate_file"] = stem + ".gfq.json"
            r["cli_certificate_ok"] = bool(
                cert["parsed"] and cert["parsed"].get("complete")
                and cert["parsed"].get("d") == best["gfq"]["d"]
                and cert["parsed"].get("certificate_checked"))
            if r["beats_table_lower"]:
                istem = f"improvements/q{q}_n{n}_k{k}_d{best['gfq']['d']}"
                cli_certificate(best["generator"], q, istem)
                r["improvement_certificate_file"] = istem + ".gfq.json"
        with open(out_path, "w") as fh:
            json.dump(out, fh, indent=1)
        print(f"second pass GF({q}) [{n},{k}]: best d = "
              f"{r['best_gfq_d']} (table lb {lb})", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seconds", type=float, default=25.0,
                    help="annealing budget per target")
    ap.add_argument("--seed", type=int, default=20261018)
    ap.add_argument("--only", help="single target as q,n,k")
    ap.add_argument("--quick", action="store_true",
                    help="tiny budgets, for a smoke test")
    ap.add_argument("--second-pass", action="store_true",
                    help="anneal longer from recorded best codes, then exit")
    args = ap.parse_args()
    if args.second_pass:
        second_pass(args.seconds, args.seed)
        return
    if args.quick:
        args.seconds = 2.0
    rng = random.Random(args.seed)
    targets = TARGETS
    if args.only:
        want = tuple(int(x) for x in args.only.split(","))
        targets = [t for t in TARGETS if t[:3] == want]
        assert targets, f"no target {want}"

    # Phase 0: gfq.codes derivations toward targets.  A seed [n0,k0] can
    # only reach (n0+1,k0), (n0-1,k0/k0-1), (n0-2,k0/k0-1/k0-2) by the
    # derivations above, so seeds outside that parameter reach of every
    # target are excluded by parameter arithmetic alone (counted, not
    # silently dropped); reachable seeds get full matrix derivations.
    derived_hits = {}
    derived_total = {}
    target_keys = {(t[0], t[1], t[2]) for t in TARGETS}
    for q in sorted({t[0] for t in targets}):
        F = GF(q)
        seeds = seed_codes(q)
        generated = reachable = 0
        for label, G in seeds:
            n0, k0 = len(G[0]), rank(G, F)
            reach = {(q, n0 + 1, k0), (q, n0 - 1, k0), (q, n0 - 1, k0 - 1),
                     (q, n0 - 2, k0), (q, n0 - 2, k0 - 1),
                     (q, n0 - 2, k0 - 2), (q, n0, k0)}
            if not (reach & target_keys):
                continue
            reachable += 1
            for dlabel, D in derivations(G, F):
                if not D or not D[0]:
                    continue
                generated += 1
                key = (q, len(D[0]), rank(D, F))
                if key in target_keys:
                    derived_hits.setdefault(key, []).append(
                        (f"{label} -> {dlabel}", D))
        derived_total[str(q)] = {
            "seeds_examined": len(seeds),
            "seeds_within_derivation_reach_of_a_target": reachable,
            "derived_matrices_generated": generated}
        print(f"GF({q}): {len(seeds)} seeds, {reachable} within reach, "
              f"{generated} derivations, "
              f"{sum(len(v) for kk, v in derived_hits.items() if kk[0] == q)}"
              " match a target", flush=True)

    out_path = os.path.join(HERE, "results.json")
    out = {"table_date": TABLE_DATE, "table_source": TABLE_SOURCE,
           "seed": args.seed, "seconds_per_target": args.seconds,
           "derived_seed_matrices_generated": derived_total,
           "targets": []}
    if os.path.exists(out_path) and not args.only:
        pass                        # fresh run overwrites; see git history
    for t in targets:
        out["targets"].append(run_target(t, args.seconds, rng,
                                          derived_hits))
        with open(out_path, "w") as fh:     # checkpoint per target
            json.dump(out, fh, indent=1)

    # Phase 2: derive from best-found codes toward neighbouring targets,
    # gfq-verify, keep genuine improvements over phase-1 best.
    by_key = {(r["q"], r["n"], r["k"]): r for r in out["targets"]}
    phase2 = []
    for r in list(out["targets"]):
        if not r["best_generator"]:
            continue
        F = GF(r["q"])
        for dlabel, D in derivations(r["best_generator"], F):
            if not D or not D[0]:
                continue
            key = (r["q"], len(D[0]), rank(D, F))
            tgt = by_key.get(key)
            if tgt is None or tgt is r:
                continue
            ver = verify_with_gfq(D, r["q"])
            phase2.append({"from": [r["q"], r["n"], r["k"]],
                           "derivation": dlabel, "to": list(key),
                           "gfq_d": ver["d"], "complete": ver["complete"],
                           "previous_best": tgt["best_gfq_d"]})
            if ver["complete"] and ver["d"] > (tgt["best_gfq_d"] or -1):
                tgt["best_gfq_d"] = ver["d"]
                tgt["best_family"] = (f"phase2 derived:{dlabel} from "
                                      f"[{r['n']},{r['k']}]")
                tgt["best_generator"] = D
                tgt["best_gfq"] = ver
                tgt["beats_table_lower"] = ver["d"] > tgt["table_lower"]
    out["phase2_cross_derivations"] = phase2
    print(f"phase 2: {len(phase2)} cross-derivations gfq-verified",
          flush=True)

    # Certificates: CLI output for the best code of every target.
    os.makedirs(os.path.join(HERE, "best"), exist_ok=True)
    os.makedirs(os.path.join(HERE, "improvements"), exist_ok=True)
    for r in out["targets"]:
        if not r["best_generator"]:
            continue
        stem = f"best/q{r['q']}_n{r['n']}_k{r['k']}_d{r['best_gfq_d']}"
        cert = cli_certificate(r["best_generator"], r["q"], stem)
        r["cli_certificate_file"] = stem + ".gfq.json"
        r["cli_certificate_ok"] = bool(
            cert["parsed"] and cert["parsed"].get("complete")
            and cert["parsed"].get("d") == r["best_gfq_d"]
            and cert["parsed"].get("certificate_checked"))
        if r["beats_table_lower"]:
            istem = (f"improvements/q{r['q']}_n{r['n']}_k{r['k']}"
                     f"_d{r['best_gfq_d']}")
            cli_certificate(r["best_generator"], r["q"], istem)
            r["improvement_certificate_file"] = istem + ".gfq.json"
    with open(out_path, "w") as fh:
        json.dump(out, fh, indent=1)
    beat = [r for r in out["targets"] if r["beats_table_lower"]]
    print(f"DONE: {len(beat)} target(s) beat the table lower bound")
    for r in out["targets"]:
        print(f" GF({r['q']}) [{r['n']},{r['k']}] table "
              f"{r['table_lower']}-{r['table_upper']}  best found "
              f"d={r['best_gfq_d']} ({r['best_family']})")


if __name__ == "__main__":
    main()
