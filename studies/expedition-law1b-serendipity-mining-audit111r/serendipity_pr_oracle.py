"""
`serendipity_pr_oracle`: Pure-Z/Q Zero-Float Executable Oracle for Law-1b Unmerged-PR Mining (Track S12).

Zero external dependencies (Python 3 stdlib only: `int`, `fractions.Fraction`).
Zero floats on trust paths or serialized outputs. Zero bare `assert` statements.

Implements six exact, non-metaphorical mathematical/algorithmic/security operators and
negative controls distilled verbatim from open and closed-unmerged PRs across 8 portals:
  - M1 (`NandhaKishorM/laya#1465` [open]): Micro-batch item-count weighted loss accumulation
       vs. CS-10 unweighted micro-batch mean collapse.
  - M2 (`NandhaKishorM/laya#698` [closed_unmerged]): Exact nearest-rank rational quantile
       index `ceil(p*n) - 1` vs. `min(n-1, floor(p*n))` +1 rank overshoot whenever `q_den | q_num*n`.
  - M3 (`NandhaKishorM/laya#693`, `#683` [closed_unmerged]): Affine bare-score range projection
       preserving lower bound `minimum` vs. self-cancelling `idx = round(s) - minimum`.
  - M4 (`NandhaKishorM/vegaml#57` [open]): Exact Q-vector equivalence between sparse scatter-add
       (`index_add` + `bincount`) and direct contiguous span slicing.
  - M5 (`Moissanite-Labs/exo#490`, `#911`, `#1136`, `#402`, `#428`, `#1192`): Deterministic
       lexer/getopt/operand/pinned-key/wake-budget witnesses for `aletheia.safety` v2.1 & harness gates.
  - M6 (`certify_law1b_serendipity_mining`): Fail-closed Law-1b (Exhaustive Serendipity &
       Unmerged-PR Portal Mining) pure-Z/Q governance gate (`G-1b.1`..`G-1b.4`).

Declared-record scope: M6 certifies that a caller-supplied Law-1b mining record is
well-formed and satisfies guards `G-1b.1`..`G-1b.4`. Live disk SHA-256 provenance of
fetched GitHub snapshots is verified separately in `serendipity_pr_certifier.py --live`.
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import json
import math
from typing import Any


class SerendipityError(ValueError):
    """Structured fail-closed exception carrying an exact error code."""

    def __init__(self, code: str, detail: str = "") -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}" if detail else code)


MECHANISM_CLASSES = frozenset(
    {
        "DENOMINATOR_OR_WEIGHT_BIAS",
        "QUANTILE_OR_INDEX_BOUNDARY",
        "AFFINE_OR_RANGE_PROJECTION",
        "ALGEBRAIC_KERNEL_EQUIVALENCE",
        "LEXER_OR_PARSER_SECURITY_BYPASS",
        "CRYPTO_PIN_OR_STATE_MACHINE",
        "EMPIRICAL_REFUTATION_OR_FREEZE",
        "INTERNAL_STEERING_OR_ARCHITECTURE",
        "EXACT_CERTIFIER_OR_DOMAIN_TOOL",
    }
)

PR_STATUSES = frozenset({"open", "closed_unmerged"})
EVIDENCE_STANDINGS = frozenset({"EXECUTED_EXACT_WITNESS", "CATALOGED_LEAD"})
NOVELTY_LABELS = frozenset({"N0", "N1", "N2"})

REPO_ROW_KEYS = frozenset({"repo", "fetched", "open", "closed_unmerged", "merged", "prs_json_sha256"})
MINED_ENTRY_KEYS = frozenset(
    {
        "repo",
        "number",
        "status",
        "head_sha",
        "snapshot_sha256",
        "mechanism_class",
        "evidence_standing",
        "honest_novelty",
        "operator_summary",
    }
)
MINING_SPEC_KEYS = frozenset(
    {
        "spec_version",
        "external_writes",
        "repos",
        "mined_entries",
    }
)

XARGS_OPT_WITH_ARG_SHORT = frozenset({"I", "n", "P", "L", "s", "d", "E", "a", "J", "R", "S"})
XARGS_OPT_NO_ARG_SHORT = frozenset({"0", "o", "p", "r", "t", "x"})
XARGS_LONG_WITH_ARG_PREFIXES = (
    "--arg-file",
    "--delimiter",
    "--eof",
    "--max-args",
    "--max-chars",
    "--max-lines",
    "--max-procs",
    "--replace",
)

GH_OPTS_TAKING_VALUE = frozenset({"-R", "--repo", "--body", "-b", "--title", "-t", "--duplicate-of", "--comment", "--reason"})


def is_strict_int(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def is_clean_ascii(value: object) -> bool:
    return (
        isinstance(value, str)
        and len(value) > 0
        and value == value.strip()
        and all(32 <= ord(ch) <= 126 for ch in value)
    )


def is_nonuniform_lower_hex(value: object, expected_len: int) -> bool:
    return (
        isinstance(value, str)
        and len(value) == expected_len
        and all(ch in "0123456789abcdef" for ch in value)
        and len(set(value)) > 1
    )


def verify_exact_json_value(obj: object) -> None:
    """Reject floats, complex, bytes, sets, and non-str dict keys recursively."""
    if obj is None or isinstance(obj, (bool, str)):
        return
    if isinstance(obj, int):
        return
    if isinstance(obj, float):
        raise SerendipityError("FLOAT_FORBIDDEN", repr(obj))
    if isinstance(obj, dict):
        for k, v in obj.items():
            if not isinstance(k, str):
                raise SerendipityError("NON_STR_DICT_KEY", type(k).__name__)
            verify_exact_json_value(v)
        return
    if isinstance(obj, list):
        for item in obj:
            verify_exact_json_value(item)
        return
    raise SerendipityError("UNSUPPORTED_EXACT_TYPE", type(obj).__name__)


def strict_typed_equal(left: object, right: object) -> bool:
    """Recursive equality requiring identical runtime types (`1 != True`)."""
    if type(left) is not type(right):
        return False
    if isinstance(left, dict):
        if set(left.keys()) != set(right.keys()):
            return False
        return all(strict_typed_equal(left[k], right[k]) for k in left)
    if isinstance(left, list):
        return len(left) == len(right) and all(strict_typed_equal(x, y) for x, y in zip(left, right))
    return left == right


def parse_exact_rational(value: object) -> Fraction:
    if isinstance(value, Fraction):
        return value
    if is_strict_int(value):
        return Fraction(value, 1)
    if not is_clean_ascii(value):
        raise SerendipityError("RATIONAL_INVALID_SYNTAX", repr(value))
    if len(value) > 128:
        raise SerendipityError("RATIONAL_TOO_LONG", str(len(value)))
    parts = value.split("/")
    if len(parts) > 2:
        raise SerendipityError("RATIONAL_TOO_MANY_SLASHES", value)
    num_s = parts[0]
    neg = num_s.startswith("-")
    digits = num_s[1:] if neg else num_s
    if not digits.isdigit():
        raise SerendipityError("RATIONAL_INVALID_NUMERATOR", value)
    if len(digits) > 1 and digits.startswith("0"):
        raise SerendipityError("RATIONAL_NONCANONICAL_LEADING_ZERO", value)
    num = -int(digits) if neg else int(digits)
    if neg and num == 0:
        raise SerendipityError("RATIONAL_NEGATIVE_ZERO", value)
    if len(parts) == 1:
        return Fraction(num, 1)
    den_s = parts[1]
    if not den_s.isdigit():
        raise SerendipityError("RATIONAL_INVALID_DENOMINATOR", value)
    if len(den_s) > 1 and den_s.startswith("0"):
        raise SerendipityError("RATIONAL_NONCANONICAL_LEADING_ZERO", value)
    den = int(den_s)
    if den <= 0:
        raise SerendipityError("RATIONAL_NONPOSITIVE_DENOMINATOR", value)
    if math.gcd(abs(num), den) != 1:
        raise SerendipityError("RATIONAL_UNREDUCED_FRACTION", value)
    return Fraction(num, den)


def fmt_q(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}" if value.denominator != 1 else str(value.numerator)


def canonical_json_bytes(obj: Any) -> bytes:
    verify_exact_json_value(obj)
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode("utf-8")


def canonical_sha256(obj: Any) -> str:
    return hashlib.sha256(canonical_json_bytes(obj)).hexdigest()


# ---------------------------------------------------------------------------
# M1: Micro-Batch Item-Count Weighted Loss Accumulation (laya#1465 / CS-10)
# ---------------------------------------------------------------------------


def certify_m1_microbatch_weighting(
    item_losses: list[Any],
    micro_batch_sizes: list[int],
) -> dict[str, Any]:
    """Verify exact equivalence between item-weighted micro-batch accumulation and full-batch mean,
    and quantify the CS-10 unweighted micro-batch distortion on uneven windows."""
    if not isinstance(item_losses, list) or len(item_losses) == 0:
        raise SerendipityError("M1_EMPTY_ITEM_LOSSES")
    if not isinstance(micro_batch_sizes, list) or len(micro_batch_sizes) == 0:
        raise SerendipityError("M1_EMPTY_MICROBATCH_SIZES")

    losses_q = [parse_exact_rational(x) for x in item_losses]
    for sz in micro_batch_sizes:
        if not is_strict_int(sz) or sz <= 0:
            raise SerendipityError("M1_INVALID_MICROBATCH_SIZE")
    if sum(micro_batch_sizes) != len(losses_q):
        raise SerendipityError("M1_PARTITION_SUM_MISMATCH")

    total_items = len(losses_q)
    true_full_mean = sum(losses_q, Fraction(0, 1)) / Fraction(total_items, 1)

    batch_means: list[Fraction] = []
    pos = 0
    for sz in micro_batch_sizes:
        chunk = losses_q[pos : pos + sz]
        pos += sz
        batch_means.append(sum(chunk, Fraction(0, 1)) / Fraction(sz, 1))

    weighted_accum = sum(
        (bm * Fraction(sz, total_items) for bm, sz in zip(batch_means, micro_batch_sizes)),
        Fraction(0, 1),
    )
    unweighted_buggy = sum(batch_means, Fraction(0, 1)) / Fraction(len(micro_batch_sizes), 1)
    weighted_residual = weighted_accum - true_full_mean
    unweighted_distortion = unweighted_buggy - true_full_mean

    return {
        "source_pr": "NandhaKishorM/laya#1465",
        "pr_status": "open",
        "total_items": total_items,
        "micro_batch_sizes": list(micro_batch_sizes),
        "true_full_mean": fmt_q(true_full_mean),
        "weighted_accum_mean": fmt_q(weighted_accum),
        "unweighted_buggy_mean": fmt_q(unweighted_buggy),
        "weighted_residual": fmt_q(weighted_residual),
        "unweighted_distortion": fmt_q(unweighted_distortion),
        "exact_match": weighted_residual == Fraction(0, 1),
        "uneven_bias_detected": unweighted_distortion != Fraction(0, 1),
    }


# ---------------------------------------------------------------------------
# M2: Exact Nearest-Rank Rational Quantile Indexing (laya#698)
# ---------------------------------------------------------------------------


def certify_m2_nearest_rank_quantile(
    sample_sizes: list[int],
    quantile: Any = "19/20",
) -> dict[str, Any]:
    """Compare exact nearest-rank index ceil(p*n)-1 against buggy min(n-1, floor(p*n))
    on 1..n ordered values across sample sizes."""
    q = parse_exact_rational(quantile)
    if q <= Fraction(0, 1) or q > Fraction(1, 1):
        raise SerendipityError("M2_QUANTILE_OUT_OF_RANGE")
    if not isinstance(sample_sizes, list) or len(sample_sizes) == 0:
        raise SerendipityError("M2_EMPTY_SAMPLE_SIZES")

    checked: list[int] = []
    overshoot_sizes: list[int] = []
    expected_divisible: list[int] = []
    for n in sample_sizes:
        if not is_strict_int(n) or n <= 0:
            raise SerendipityError("M2_INVALID_SAMPLE_SIZE")
        checked.append(n)
        num = q.numerator * n
        den = q.denominator
        exact_idx = (num + den - 1) // den - 1
        buggy_idx = min(n - 1, num // den)
        if buggy_idx != exact_idx:
            overshoot_sizes.append(n)
        if num % den == 0 and exact_idx < n - 1:
            expected_divisible.append(n)

    return {
        "source_pr": "NandhaKishorM/laya#698",
        "pr_status": "closed_unmerged",
        "quantile": fmt_q(q),
        "sizes_checked_count": len(checked),
        "overshoot_sizes": overshoot_sizes,
        "overshoot_count": len(overshoot_sizes),
        "exact_divisibility_match": overshoot_sizes == expected_divisible,
    }


# ---------------------------------------------------------------------------
# M3: Affine Score-to-Range Projection Offset Preservation (laya#693, #683)
# ---------------------------------------------------------------------------


def _half_away_from_zero_round(x: Fraction) -> int:
    if x >= 0:
        return (2 * x.numerator + x.denominator) // (2 * x.denominator)
    return -((2 * (-x.numerator) + x.denominator) // (2 * x.denominator))


def certify_m3_affine_score_projection(
    minimum: int,
    maximum: int,
    raw_score: Any,
) -> dict[str, Any]:
    """Verify exact integer score projection preserving `minimum` offset vs. the
    self-cancelling `minimum + (round(score) - minimum)` bug in laya#693/#683."""
    if not is_strict_int(minimum) or not is_strict_int(maximum) or maximum <= minimum:
        raise SerendipityError("M3_INVALID_RANGE")
    score_q = parse_exact_rational(raw_score)
    span = maximum - minimum
    if score_q < Fraction(0, 1) or score_q > Fraction(span, 1):
        raise SerendipityError("M3_SCORE_OUT_OF_LEVEL_SPAN")

    level_idx = _half_away_from_zero_round(score_q)
    fixed_val = minimum + level_idx
    buggy_val = minimum + (level_idx - minimum)
    offset_drop = fixed_val - buggy_val

    return {
        "source_pr": "NandhaKishorM/laya#693",
        "pr_status": "closed_unmerged",
        "minimum": minimum,
        "maximum": maximum,
        "raw_score": fmt_q(score_q),
        "fixed_projected": fixed_val,
        "buggy_projected": buggy_val,
        "offset_drop": offset_drop,
        "fixed_in_range": minimum <= fixed_val <= maximum,
        "buggy_out_of_range": not (minimum <= buggy_val <= maximum),
    }


# ---------------------------------------------------------------------------
# M4: Direct Contiguous Span Pooling vs. Scatter-Add Equivalence (vegaml#57)
# ---------------------------------------------------------------------------


def certify_m4_span_pooling_equivalence(
    hidden_rows: list[list[Any]],
    spans: list[list[int]],
) -> dict[str, Any]:
    """Prove exact Q-matrix equality between scatter-add/bincount pooling and
    direct contiguous slice pooling over disjoint token spans."""
    if not isinstance(hidden_rows, list) or len(hidden_rows) == 0:
        raise SerendipityError("M4_EMPTY_HIDDEN_ROWS")
    if not isinstance(hidden_rows[0], list) or len(hidden_rows[0]) == 0:
        raise SerendipityError("M4_EMPTY_HIDDEN_DIM")
    seq_len = len(hidden_rows)
    dim = len(hidden_rows[0])
    mat_q: list[list[Fraction]] = []
    for row in hidden_rows:
        if not isinstance(row, list) or len(row) != dim:
            raise SerendipityError("M4_RAGGED_HIDDEN_MATRIX")
        mat_q.append([parse_exact_rational(v) for v in row])

    if not isinstance(spans, list) or len(spans) == 0:
        raise SerendipityError("M4_EMPTY_SPANS")

    occupied = [False] * seq_len
    parsed_spans: list[tuple[int, int]] = []
    for sp in spans:
        if not isinstance(sp, list) or len(sp) != 2:
            raise SerendipityError("M4_INVALID_SPAN_PAIR")
        lo, hi = sp[0], sp[1]
        if not is_strict_int(lo) or not is_strict_int(hi) or lo < 0 or hi <= lo or hi > seq_len:
            raise SerendipityError("M4_SPAN_OUT_OF_BOUNDS")
        for idx in range(lo, hi):
            if occupied[idx]:
                raise SerendipityError("M4_OVERLAPPING_SPANS")
            occupied[idx] = True
        parsed_spans.append((lo, hi))

    # Method A: scatter-add with dummy segment 0 for unspanned positions + bincount
    num_spans = len(parsed_spans)
    seg_ids = [0] * seq_len
    for sid, (lo, hi) in enumerate(parsed_spans, start=1):
        for idx in range(lo, hi):
            seg_ids[idx] = sid
    scatter_sums = [[Fraction(0, 1)] * dim for _ in range(num_spans + 1)]
    bincounts = [0] * (num_spans + 1)
    for t, sid in enumerate(seg_ids):
        bincounts[sid] += 1
        for j in range(dim):
            scatter_sums[sid][j] += mat_q[t][j]
    pooled_scatter = [
        [scatter_sums[sid][j] / Fraction(bincounts[sid], 1) for j in range(dim)]
        for sid in range(1, num_spans + 1)
    ]

    # Method B: direct contiguous span slicing (vegaml#57)
    pooled_direct = [
        [
            sum((mat_q[t][j] for t in range(lo, hi)), Fraction(0, 1)) / Fraction(hi - lo, 1)
            for j in range(dim)
        ]
        for lo, hi in parsed_spans
    ]

    max_abs_diff = Fraction(0, 1)
    for row_a, row_b in zip(pooled_scatter, pooled_direct):
        for a, b in zip(row_a, row_b):
            diff = abs(a - b)
            if diff > max_abs_diff:
                max_abs_diff = diff

    return {
        "source_pr": "NandhaKishorM/vegaml#57",
        "pr_status": "open",
        "seq_len": seq_len,
        "hidden_dim": dim,
        "span_count": num_spans,
        "max_abs_residual": fmt_q(max_abs_diff),
        "exact_equivalence": max_abs_diff == Fraction(0, 1),
        "pooled_direct": [[fmt_q(v) for v in row] for row in pooled_direct],
    }


# ---------------------------------------------------------------------------
# M5: Shell-Lexer, Getopt, Operand, Pinned-Key & Wake-Budget Witnesses (exo)
# ---------------------------------------------------------------------------


def collapse_backtick_line_continuations(body: str) -> str:
    """exo#490: Bash drops unescaped backslash-newline inside backticks before parsing."""
    if not isinstance(body, str):
        raise SerendipityError("M5_BODY_NOT_STR")
    out: list[str] = []
    i = 0
    n = len(body)
    while i < n:
        if body[i] == "\\":
            j = i
            while j < n and body[j] == "\\":
                j += 1
            bs_count = j - i
            if j < n and body[j] == "\n":
                # Even backslashes -> half as many literal backslashes + kept newline.
                # Odd backslashes -> (bs_count - 1)//2 literal backslashes + dropped \<NL>.
                out.append("\\" * (bs_count // 2))
                if bs_count % 2 == 0:
                    out.append("\n")
                i = j + 1
                continue
            out.append(body[i:j])
            i = j
            continue
        out.append(body[i])
        i += 1
    return "".join(out)


def match_heredoc_logical_terminator(
    physical_lines: list[str],
    delimiter: str,
    *,
    quoted_delimiter: bool,
    strip_leading_tabs: bool,
) -> int:
    """exo#911: Return 0-based index of the closing physical line, or -1 if unterminated.

    Unquoted delimiters join physical lines ending in an odd backslash run; `<<-` strips
    leading tabs from the joined logical line, NOT from subsequent continuation lines.
    """
    if not isinstance(physical_lines, list) or any(not isinstance(ln, str) for ln in physical_lines):
        raise SerendipityError("M5_HEREDOC_LINES_INVALID")
    if not is_clean_ascii(delimiter):
        raise SerendipityError("M5_HEREDOC_DELIM_INVALID")
    if not isinstance(quoted_delimiter, bool) or not isinstance(strip_leading_tabs, bool):
        raise SerendipityError("M5_HEREDOC_FLAG_INVALID")

    buf = ""
    for idx, raw in enumerate(physical_lines):
        if quoted_delimiter:
            cand = raw.lstrip("\t") if strip_leading_tabs else raw
            if cand == delimiter:
                return idx
            continue
        bs = 0
        for ch in reversed(raw):
            if ch == "\\":
                bs += 1
            else:
                break
        if bs % 2 == 1:
            buf += raw[:-1]
            continue
        logical = buf + raw
        buf = ""
        cand = logical.lstrip("\t") if strip_leading_tabs else logical
        if cand == delimiter:
            return idx
    return -1


def parse_xargs_command_token(argv: list[str]) -> str | None:
    """exo#1136: Parse GNU/BSD xargs getopt options to locate the actual invoked command."""
    if not isinstance(argv, list) or len(argv) == 0 or any(not isinstance(a, str) for a in argv):
        raise SerendipityError("M5_XARGS_ARGV_INVALID")
    if argv[0] != "xargs":
        raise SerendipityError("M5_XARGS_FIRST_TOKEN")

    i = 1
    n = len(argv)
    while i < n:
        tok = argv[i]
        if tok == "--":
            return argv[i + 1] if i + 1 < n else None
        if tok.startswith("--"):
            if "=" in tok:
                i += 1
                continue
            if any(p.startswith(tok) for p in XARGS_LONG_WITH_ARG_PREFIXES) and len(tok) >= 4:
                i += 2
                continue
            i += 1
            continue
        if tok.startswith("-") and len(tok) > 1:
            letters = tok[1:]
            consumes_next = False
            for pos, ch in enumerate(letters):
                if ch in XARGS_OPT_WITH_ARG_SHORT:
                    if pos == len(letters) - 1:
                        consumes_next = True
                    break
                if ch in XARGS_OPT_NO_ARG_SHORT:
                    continue
                break
            i += 2 if consumes_next else 1
            continue
        return tok
    return None


def resolve_gh_target_repo(argv: list[str]) -> str | None:
    """exo#402: Extract gh target strictly from `-R`/`--repo` or positional URL operands,
    never from option values like `--body` or `--duplicate-of`."""
    if not isinstance(argv, list) or len(argv) == 0 or any(not isinstance(a, str) for a in argv):
        raise SerendipityError("M5_GH_ARGV_INVALID")
    if argv[0] != "gh":
        raise SerendipityError("M5_GH_FIRST_TOKEN")

    explicit_repo: str | None = None
    operand_url: str | None = None
    i = 1
    n = len(argv)
    after_dd = False
    while i < n:
        tok = argv[i]
        if not after_dd and tok == "--":
            after_dd = True
            i += 1
            continue
        if not after_dd and tok in ("-R", "--repo"):
            if i + 1 >= n:
                raise SerendipityError("M5_GH_MISSING_REPO_VALUE")
            explicit_repo = argv[i + 1]
            i += 2
            continue
        if not after_dd and tok.startswith("--repo="):
            explicit_repo = tok.split("=", 1)[1]
            i += 1
            continue
        if not after_dd and tok.startswith("-R") and len(tok) > 2:
            explicit_repo = tok[2:]
            i += 1
            continue
        if not after_dd and tok in GH_OPTS_TAKING_VALUE:
            i += 2
            continue
        if not after_dd and tok.startswith("-") and "=" in tok:
            i += 1
            continue
        if not after_dd and tok.startswith("-"):
            i += 1
            continue
        if operand_url is None and tok.startswith("https://github.com/"):
            operand_url = tok
        i += 1
    return explicit_repo if explicit_repo is not None else operand_url


def verify_pinned_peer_envelope(
    seat: str,
    envelope_signer_key: str,
    presence_file_key: str,
    pinned_keys: dict[str, str],
) -> dict[str, Any]:
    """exo#428: Verify peer envelope strictly against pinned seat key, never presence file."""
    if not is_clean_ascii(seat):
        raise SerendipityError("M5_INVALID_SEAT")
    if not is_clean_ascii(envelope_signer_key) or not is_clean_ascii(presence_file_key):
        raise SerendipityError("M5_INVALID_KEY")
    if not isinstance(pinned_keys, dict):
        raise SerendipityError("M5_PINNED_KEYS_NOT_DICT")

    pinned = pinned_keys.get(seat)
    if pinned is None:
        return {"trusted": False, "decision": "HOLD_UNPINNED_SEAT", "presence_matched": envelope_signer_key == presence_file_key}
    if not is_clean_ascii(pinned):
        raise SerendipityError("M5_INVALID_PINNED_VALUE")
    trusted = envelope_signer_key == pinned
    return {
        "trusted": trusted,
        "decision": "VERIFIED_PINNED_KEY" if trusted else "REJECT_KEY_MISMATCH",
        "presence_matched": envelope_signer_key == presence_file_key,
    }


def simulate_wake_budget_fsm(events: list[str], max_wakes: int = 5) -> dict[str, Any]:
    """exo#1192: Only a `principal` turn resets the wake budget; `peer`/`bus`/`job`/`stop`
    never renew it, and `steer`/`undo`/`stop` drop pending wakes."""
    if not is_strict_int(max_wakes) or max_wakes <= 0:
        raise SerendipityError("M5_INVALID_MAX_WAKES")
    if not isinstance(events, list) or len(events) == 0:
        raise SerendipityError("M5_EMPTY_WAKE_EVENTS")
    valid_events = frozenset({"schedule_wake", "wake_turn", "principal_turn", "peer_turn", "bus_turn", "job_turn", "steer", "undo", "stop"})

    wakes_used = 0
    pending_wake = False
    denied_wakes = 0
    for ev in events:
        if not isinstance(ev, str) or ev not in valid_events:
            raise SerendipityError("M5_UNKNOWN_WAKE_EVENT", repr(ev))
        if ev == "schedule_wake":
            if wakes_used < max_wakes:
                pending_wake = True
            else:
                denied_wakes += 1
        elif ev == "wake_turn":
            if pending_wake and wakes_used < max_wakes:
                wakes_used += 1
                pending_wake = False
            else:
                denied_wakes += 1
        elif ev == "principal_turn":
            wakes_used = 0
            pending_wake = False
        elif ev in ("peer_turn", "bus_turn", "job_turn"):
            pending_wake = False
        elif ev in ("steer", "undo", "stop"):
            pending_wake = False

    return {
        "max_wakes": max_wakes,
        "wakes_used": wakes_used,
        "pending_wake": pending_wake,
        "denied_wakes": denied_wakes,
        "budget_conserved": wakes_used <= max_wakes,
    }


# ---------------------------------------------------------------------------
# M6: Law-1b Serendipity-Mining Governance Gate (`aletheia v2.1` Proposal)
# ---------------------------------------------------------------------------


def certify_law1b_serendipity_mining(spec: dict[str, Any]) -> dict[str, Any]:
    """Fail-closed pure-Z/Q Law-1b gate (Exhaustive Serendipity & Unmerged-PR Portal Mining).

    Enforces:
      - G-1b.1 (Anti-Merged-Only Blind Spot): must mine unmerged PRs, and whenever any
        scanned repository has closed-unmerged PRs, closed-unmerged coverage must be non-zero.
      - G-1b.2 (Exact Provenance Pinning): every repo row and mined entry has valid counts,
        non-uniform lowercase hex commit/snapshot digests, and closed-taxonomy mechanism class.
      - G-1b.3 (Non-Metaphorical Operator Discipline): requires >=1 `EXECUTED_EXACT_WITNESS`
        entry alongside any `CATALOGED_LEAD` entries; forbids duplicate `(repo, number)` keys.
      - G-1b.4 (Zero-Write Portal Integrity): `external_writes == 0` required fail-closed.

    Declared-record scope: validates record structure, provenance formatting, and Law-1b
    invariants over the caller-supplied spec; live disk SHA-256 verification against frozen
    intake JSON files is executed separately by `serendipity_pr_certifier.py --live`.
    """
    verify_exact_json_value(spec)
    if not isinstance(spec, dict) or frozenset(spec.keys()) != MINING_SPEC_KEYS:
        raise SerendipityError("L1B_SCHEMA_MISMATCH")
    if spec["spec_version"] != "aletheia.law1b.v1":
        raise SerendipityError("L1B_INVALID_SPEC_VERSION")
    ext_writes = spec["external_writes"]
    if not is_strict_int(ext_writes) or ext_writes != 0:
        raise SerendipityError("L1B_NONZERO_EXTERNAL_WRITES")

    repos = spec["repos"]
    if not isinstance(repos, list) or len(repos) == 0:
        raise SerendipityError("L1B_EMPTY_REPOS")

    seen_repos: set[str] = set()
    repo_stats: dict[str, dict[str, int]] = {}
    total_fetched = 0
    total_open = 0
    total_closed_unmerged = 0
    total_merged = 0
    for row in repos:
        if not isinstance(row, dict) or frozenset(row.keys()) != REPO_ROW_KEYS:
            raise SerendipityError("L1B_REPO_ROW_SCHEMA_MISMATCH")
        rname = row["repo"]
        if not is_clean_ascii(rname) or "/" not in rname:
            raise SerendipityError("L1B_INVALID_REPO_NAME")
        rlow = rname.lower()
        if rlow in seen_repos:
            raise SerendipityError("L1B_DUPLICATE_REPO")
        seen_repos.add(rlow)

        fetched = row["fetched"]
        n_open = row["open"]
        n_cu = row["closed_unmerged"]
        n_merged = row["merged"]
        if (
            not is_strict_int(fetched)
            or not is_strict_int(n_open)
            or not is_strict_int(n_cu)
            or not is_strict_int(n_merged)
        ):
            raise SerendipityError("L1B_REPO_COUNT_NOT_INT")
        if fetched <= 0 or n_open < 0 or n_cu < 0 or n_merged < 0:
            raise SerendipityError("L1B_REPO_COUNT_NEGATIVE")
        if n_open + n_cu + n_merged != fetched:
            raise SerendipityError("L1B_REPO_COUNT_SUM_MISMATCH")
        if not is_nonuniform_lower_hex(row["prs_json_sha256"], 64):
            raise SerendipityError("L1B_INVALID_REPO_SHA256")

        repo_stats[rlow] = {"open": n_open, "closed_unmerged": n_cu}
        total_fetched += fetched
        total_open += n_open
        total_closed_unmerged += n_cu
        total_merged += n_merged

    entries = spec["mined_entries"]
    if not isinstance(entries, list) or len(entries) == 0:
        raise SerendipityError("L1B_EMPTY_MINED_ENTRIES")

    seen_prs: set[tuple[str, int]] = set()
    mined_open_by_repo: dict[str, int] = {}
    mined_cu_by_repo: dict[str, int] = {}
    open_mined = 0
    cu_mined = 0
    witness_count = 0
    lead_count = 0
    class_counts: dict[str, int] = {}

    for ent in entries:
        if not isinstance(ent, dict) or frozenset(ent.keys()) != MINED_ENTRY_KEYS:
            raise SerendipityError("L1B_ENTRY_SCHEMA_MISMATCH")
        rname = ent["repo"]
        if not is_clean_ascii(rname) or rname.lower() not in repo_stats:
            raise SerendipityError("L1B_ENTRY_UNKNOWN_REPO")
        rlow = rname.lower()
        num = ent["number"]
        if not is_strict_int(num) or num <= 0:
            raise SerendipityError("L1B_ENTRY_INVALID_PR_NUMBER")
        pr_key = (rlow, num)
        if pr_key in seen_prs:
            raise SerendipityError("L1B_DUPLICATE_MINED_PR")
        seen_prs.add(pr_key)

        status = ent["status"]
        if status not in PR_STATUSES:
            raise SerendipityError("L1B_ENTRY_INVALID_STATUS")
        if not is_nonuniform_lower_hex(ent["head_sha"], 40):
            raise SerendipityError("L1B_ENTRY_INVALID_HEAD_SHA")
        if not is_nonuniform_lower_hex(ent["snapshot_sha256"], 64):
            raise SerendipityError("L1B_ENTRY_INVALID_SNAPSHOT_SHA")
        mcls = ent["mechanism_class"]
        if mcls not in MECHANISM_CLASSES:
            raise SerendipityError("L1B_ENTRY_INVALID_MECHANISM_CLASS")
        standing = ent["evidence_standing"]
        if standing not in EVIDENCE_STANDINGS:
            raise SerendipityError("L1B_ENTRY_INVALID_STANDING")
        novelty = ent["honest_novelty"]
        if novelty not in NOVELTY_LABELS:
            raise SerendipityError("L1B_ENTRY_INVALID_NOVELTY")
        if standing == "CATALOGED_LEAD" and novelty != "N0":
            raise SerendipityError("L1B_LEAD_CANNOT_CLAIM_ABOVE_N0")
        if not is_clean_ascii(ent["operator_summary"]):
            raise SerendipityError("L1B_ENTRY_EMPTY_SUMMARY")

        if status == "open":
            open_mined += 1
            mined_open_by_repo[rlow] = mined_open_by_repo.get(rlow, 0) + 1
            if mined_open_by_repo[rlow] > repo_stats[rlow]["open"]:
                raise SerendipityError("L1B_REPO_OPEN_COUNT_EXCEEDED", rname)
        else:
            cu_mined += 1
            mined_cu_by_repo[rlow] = mined_cu_by_repo.get(rlow, 0) + 1
            if mined_cu_by_repo[rlow] > repo_stats[rlow]["closed_unmerged"]:
                raise SerendipityError("L1B_REPO_CLOSED_UNMERGED_COUNT_EXCEEDED", rname)
        if standing == "EXECUTED_EXACT_WITNESS":
            witness_count += 1
        else:
            lead_count += 1
        class_counts[mcls] = class_counts.get(mcls, 0) + 1

    # G-1b.1: Anti-merged-only & anti-open-only blind spot
    if total_closed_unmerged > 0 and cu_mined == 0:
        raise SerendipityError("L1B_CLOSED_UNMERGED_BLIND_SPOT")
    if total_open > 0 and open_mined == 0:
        raise SerendipityError("L1B_OPEN_PR_BLIND_SPOT")
    if witness_count == 0:
        raise SerendipityError("L1B_ZERO_EXECUTED_WITNESSES")

    total_unmerged = total_open + total_closed_unmerged
    return {
        "certified": True,
        "verdict": "LAW1B_MINING_CERTIFIED",
        "repos_scanned": len(repos),
        "total_prs_fetched": total_fetched,
        "total_open_prs": total_open,
        "total_closed_unmerged_prs": total_closed_unmerged,
        "total_unmerged_prs": total_unmerged,
        "total_merged_prs": total_merged,
        "unmerged_fraction": fmt_q(Fraction(total_unmerged, total_fetched)),
        "mined_entries_count": len(entries),
        "open_mined": open_mined,
        "closed_unmerged_mined": cu_mined,
        "executed_exact_witnesses": witness_count,
        "cataloged_leads": lead_count,
        "mechanism_class_counts": dict(sorted(class_counts.items())),
    }
