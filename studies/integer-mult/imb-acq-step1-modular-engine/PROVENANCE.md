# Provenance and status: imb-acq-step1-modular-engine

**Status: claimed, pending review.** No maintainer of math0 or of CrocSwap/integer-mult-bounds has reviewed this
package. No kappa is claimed here, and nothing has been submitted upstream.

## What it is

A pure-standard-library Python package (Python 3.12+) for searching rewrites of integer-multiplication circuit words
in [CrocSwap/integer-mult-bounds](https://github.com/CrocSwap/integer-mult-bounds). Its README states three theorems
(a k-wire flag-shear bypass, coupled-helper abscission, and commuting-ADD window coalescing) and a staged command line
that scans a `WORD.json.gz` circuit word for candidate splices. The files other than this one are as received.

## Source

| Item | Value |
|---|---|
| Drive file | `2026-11-13_imb-acq-step1-modular-engine.zip`, id `11H71gQfrlG4RzTHmqVzxJDIfFXKtCCpu` |
| Drive created and modified | 2026-11-13T21:06:56Z |
| Zip size and SHA-256 | 28,186 bytes, `b4ad92b475e7e47245881dc1375702480792165b8ed6ba46e9a2f6c1dc9af6e4` |
| Zip contents | `imb_acq_step1/` (7 files), copied here without that top folder |
| Inner manifest | `SHA256SUMS` from the zip; `sha256sum -c SHA256SUMS` passes on all 6 listed files |
| Author | An AI agent working for Ahraz Arifuddin (Aska Digital), per the Drive owner and the README |

## What was run

On Linux x86_64, Python 3.13.5, 14 November 2026:

```
$ python3 -B run_step1_scan.py --self-test
=== RUNNING IMB ACQ STEP-1 MATHEMATICAL SUITE SELF-TEST ===
  [OK] Stage 1A Family-A fusions found : 1
  [OK] Stage 1B Flag-Shears (k=2,3)    : 10 strictly positive
  [OK] Stage 1C Joint-Basis Abscission : 1 coupled k>=2 splits
  [OK] Stage 1D Packed Disjoint Splices: 3 -> ['k2_funded_detour_flag_shear', 'k3_funded_detour_flag_shear', 'family_a_move_fusion']
       Cumulative Paid Delta           : {1: 2, 3: -3, 4: -3, 6: 2, 7: 1}
       Estimated Delta Kappa (17x)     : +1.366766446839e-6
  [OK] Coupled k=2 Abscission Verified : helpers delta={7:-1, 3:+1, 4:+1}, paid delta={}, est dk=+7.603827685338e-7
  [OK] PR #7481 Exact Calibration      : est_dk=+3.031668277822e-7 (actual +3.031668540000e-7)
=== ALL 5 MATHEMATICAL & ADVERSARIAL SELF-TESTS PASSED ===
```

Exit status 0, about 0.1 s. All five modules also pass `python3 -m py_compile`.

The scan stages (`--word ... --stage ...`) were not run: they need a circuit word from an integer-mult-bounds
checkout, and none is included.

## Claims that are not yet checked

- **The three theorems.** Stated in the README with proof sketches only. Nobody has checked them.
- **Self-test results.** The self-test builds small synthetic words in code. Its positive candidates and the
  `+1.37e-6` kappa estimate are for those synthetic words, not for any real circuit.
- **The #7481 calibration.** The pricing slope in `tariff_shadow_pricer.py` is fitted from the #7480 to #7481 gain,
  and the self-test then checks the estimate against that same gain. It shows the arithmetic is consistent, not that
  the estimator predicts other candidates.
- **Upstream state.** As of 14 November 2026, CrocSwap/integer-mult-bounds #7000 is merged; #7480, #7481 and #7497
  are open. The README's description of those pull requests and of the "fifteen follow-up audits" is the author's
  and has not been checked here.
- **The self-test uses `assert`** (12 in `run_step1_scan.py`), so `python3 -O` skips its checks.

## Next steps

Run stage 1D on the #7481 word from a CrocSwap checkout and replay any packed splice through the upstream verifier.
Whether this belongs here, in a CrocSwap pull request, or in its own Foundation-0 repository is open.
