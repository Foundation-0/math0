# Zenodo `23644664` (*Proyecto RNS / P-NP*) Exact Mathematical Tomography (`AUDIT-070R`)

- **Audit Status:** `AUDIT-070R VERIFIED` (`N1`, `0` unresolved defects; `51/51` `100.0%` `aletheia v1.4.0 mutate` killed; `aletheia v1.4.0 audit-check --strict-ancestors PASS`; `4/4` isolated `-I` bit-identical R4 determinism).
- **Target Record (Strictly Read-Only, `0` External Writes):** Manuel Romero, *Proyecto RNS / P-NP* (V00–V03), DOI `10.5281/zenodo.23644664` (`12` published `.md`/`.zip` files MD5-verified against `record_23644664.json`, `sha256:6198464c...`). No third-party Zenodo archives are vendored here; all exact mathematical refutations execute live in standalone pure Python 3 stdlib (`int` / `fractions.Fraction`, **zero floats**).

## Files in This Study

| File | SHA-256 / Role |
|---|---|
| [zenodo_rns_pnp_audit.py](zenodo_rns_pnp_audit.py) | `67d57d73148b32e151e8a3931c7319478e8875d3c2ef4cd92761a433e885bb72` — Zero-float pure-$\mathbb{Q}$ oracle refuting `V03 Anexo` Theorems `2.1`, `3.2`, `4.1`, `5.1`, and `6.1` (`--standalone` requires no external files) |
| [test_r5_zenodo_rns_pnp.py](test_r5_zenodo_rns_pnp.py) | `aa14e0299fc3d13fc448cc5177d8e26cc22c82d5bc60a55fd431bfc1c3ab9030` — R1–R5 invariant & refusal-site test suite (`51/51` `100.0%` mutation kill) |
| [zenodo_rns_pnp_certificate.json](zenodo_rns_pnp_certificate.json) | `eae51ad62e4252a65d5962fad6b7ed7917f505a34b5a37275c46a6d3c7391e73` — Sealed `AUDIT-070R` live-anchored zero-float certificate (`certificate_sha256 = 878f2500fedd58acaeb8eed564315fb743640f261ce161f3bd1498b3fe03c6be`) |
| [REPORT_R7_3_ZENODO_RNS_PNP.md](REPORT_R7_3_ZENODO_RNS_PNP.md) | Full forensic report, Law-2 steelman reproduction receipts, minimal counterexamples, and Law-4 `N0` prior-art quarantine |

## Quickstart (Zero External Dependencies)

From `studies/zenodo-rns-pnp-tomography/`:

```bash
# 1. Run exact pure-Q mathematical refutations in standalone isolated mode
#    4/4 isolated -I modes (-I -B, -I -O -B, -I -B -W error, -I -O -B -W error)
#    produce bit-identical stdout SHA-256:
#      d2fed613467f9bcafa36a89c1f3eed7151bf7bba91a9e6fc0e0552b63015be41
#    (certificate_sha256 = 8de3e04f49c799d1093edd65283a7b026f2cd3ff03d03f35805d8badd35bd7a2)
python3 -I -B zenodo_rns_pnp_audit.py --standalone | sha256sum

# 2. Run the full R5 invariant and refusal-site test suite
python3 -I -O -B -W error test_r5_zenodo_rns_pnp.py
```

With [`Foundation-0/aletheia`](https://github.com/Foundation-0/aletheia) v1.4.0 installed or on `PYTHONPATH`:

```bash
python3 -B -W error -m aletheia audit-check . \
  --strict-ancestors --scripts zenodo_rns_pnp_audit.py test_r5_zenodo_rns_pnp.py --json
python3 -B -W error -m aletheia mutate zenodo_rns_pnp_audit.py \
  --work-root . --add-cwd --test-cmd "python3 -I -O -B -W error test_r5_zenodo_rns_pnp.py" --json
```

## Summary of Verified Results (`N1`)

- **Live Code Forensics (`RNS-EMP-01..04`):** Author's own unmodified `Code V01/V02` scripts yield `26643` (`+4.07%`, worse than 2-opt's `26400`), `18` vs `3` backtracks (`+500%`, despite hardcoded `"(Reduccion notable)"`), `>30s` timeout at `N=3000` (`22,123,500` `distance_euc` calls in `patch_tours`), and a `SyntaxError` at `rns_benchmark_suite.py:195`.
- **Exact Zero-Float Counterexamples to Theorems `2.1`, `3.2`, `4.1`, `5.1`, `6.1`:** Tseitin($K_4, b$) exact Gramian blindness (`W_SAT == W_UNSAT == 8*I_6`); self-loop squaring spectral inversion (`M = (A_0 + I)^2` maps `-3 -> 9`); infinite planar TSP partition counterexample family ($\sigma_0 \to \infty$, optimality gap `1 + (R - M) > +1`); Subset-Sum (`249/250`), 0-1 Knapsack (`23/100`), and Scheduling (`5/71`, `4/71`) local-optima witnesses; symmetric regular deposit non-collapse ($K_4$) and triangle-free Mycielski $M_4$ ($\omega = 2, \chi = 4$).
- **Law-2 Steelman & Law-4 Quarantine:** Narrow heuristic gains (`LPT 13/100 -> 68/100`, `232947/232947`, `queen5_5` `8 -> 5`, L1 tiling locality) are verified honestly and mapped to classical `N0` prior art (Sherman–Morrison, Jeroslow–Wang, Karp 1977, Croes 1958, Graham 1969, Brélaz 1979, Mycielski 1955).
