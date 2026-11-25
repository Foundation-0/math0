"""Exact Pure-Z/Q Coupled Multi-Entity Farkas Dual Cuts & Deadlock Certifier (Track S20e).

Pure Python 3 standard library (`int` and `fractions.Fraction` only; zero floats,
zero bare asserts, zero external dependencies, Zone-B fail-closed boundaries).

Attacks the 3 open Heroes of Sokoban Part III Frontier rooms (`III-14`, `III-20`,
`III-21`) with:
  1. Exact rational action-class cost-partitioned multi-quotient Farkas LP solver
     (`primal == dual` exact in Q, globally 1-step consistent `h(s) - h(s') <= 1`),
  2. Exact non-separable multi-entity Farkas deadlock-infeasibility cut-set certifier
     (finite 1-entity projections vs exact coupled infinity / strict coupling gap),
  3. Standalone Part III concrete engine verified on all 3 catalog reference routes
     (`48`, `84`, `316` keys) and off-route random transitions (`0` Bellman violations),
  4. Explicit Law-2b falsification controls (naive unpartitioned sum `must_fail`
     control + residual gap diagnostics below global search floors).
"""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import heapq
import hmac
import json
import math
from pathlib import Path
import random
import stat
from typing import Any, Callable, Dict, List, Optional, Sequence, Set, Tuple

MAX_INT_BITS = 2048
MAX_INT_DIGITS = 616
MAX_JSON_DEPTH = 64
MAX_JSON_BYTES = 16 * 1024 * 1024
_HEX_LOWER = frozenset("0123456789abcdef")
_EXACT_PATH_TYPE = type(Path("."))

ACTIVE_HEROES = frozenset({"F", "T", "W", "P", "B", "D"})
INACTIVE_HEROES = frozenset({"1", "2", "3", "4", "5", "6"})
TO_INACTIVE: Dict[str, str] = {"F": "1", "T": "2", "W": "3", "P": "4", "B": "5", "D": "6"}
TO_ACTIVE: Dict[str, str] = {"1": "F", "2": "T", "3": "W", "4": "P", "5": "B", "6": "D"}
CYCLE_ORDER: Tuple[str, ...] = ("1", "2", "3", "4", "5", "6")
DIRS: Dict[str, Tuple[int, int]] = {"U": (0, -1), "D": (0, 1), "L": (-1, 0), "R": (1, 0)}
DIR_DELTAS: Tuple[Tuple[int, int], ...] = ((0, -1), (0, 1), (-1, 0), (1, 0))


class AletheiaError(ValueError):
    """Fail-closed Zone-B validation error with structured machine-readable code."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _require_utf8_str(val: Any, label: str) -> str:
    if type(val) is not str:
        raise AletheiaError("INVALID_STR_TYPE", f"{label} must be strict str")
    try:
        val.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise AletheiaError("INVALID_UTF8", f"{label} contains unpaired surrogate") from exc
    return val


def require_int(
    val: Any,
    label: str = "int",
    *,
    lo: Optional[int] = None,
    hi: Optional[int] = None,
) -> int:
    if type(val) is not int:
        raise AletheiaError("INVALID_INT_TYPE", f"{label} must be strict int")
    blen = val.bit_length()
    if blen > MAX_INT_BITS:
        raise AletheiaError("INT_BIT_LIMIT", f"{label} bit_length={blen} exceeds {MAX_INT_BITS}")
    if lo is not None:
        if type(lo) is not int:
            raise AletheiaError("INVALID_BOUND_TYPE", f"{label}.lo must be strict int")
        if val < lo:
            raise AletheiaError("INT_BELOW_MIN", f"{label} bit_length={blen} below minimum")
    if hi is not None:
        if type(hi) is not int:
            raise AletheiaError("INVALID_BOUND_TYPE", f"{label}.hi must be strict int")
        if val > hi:
            raise AletheiaError("INT_ABOVE_MAX", f"{label} bit_length={blen} above maximum")
    return val


def require_hex64_ascii(val: Any, label: str = "sha256") -> str:
    if type(val) is not str:
        raise AletheiaError("INVALID_DIGEST_TYPE", f"{label} must be strict str")
    if len(val) != 64:
        raise AletheiaError("INVALID_DIGEST_LEN", f"{label} must have length 64")
    for ch in val:
        if ch not in _HEX_LOWER:
            raise AletheiaError("INVALID_DIGEST_HEX", f"{label} must be lowercase ASCII hex")
    return val


def constant_time_hex64_equal(left: Any, right: Any, label: str = "sha256") -> bool:
    a = require_hex64_ascii(left, f"{label}.left")
    b = require_hex64_ascii(right, f"{label}.right")
    return hmac.compare_digest(a, b)


def fmt_q(q: Fraction) -> str:
    if type(q) is not Fraction:
        raise AletheiaError("INVALID_FRACTION_TYPE", "q must be strict Fraction")
    nb = q.numerator.bit_length()
    db = q.denominator.bit_length()
    if nb > MAX_INT_BITS or db > MAX_INT_BITS:
        raise AletheiaError("FRACTION_BIT_LIMIT", f"fraction bit_lengths=({nb},{db}) exceed {MAX_INT_BITS}")
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def parse_q(val: Any, label: str = "q") -> Fraction:
    if type(val) is int:
        return Fraction(require_int(val, label))
    if type(val) is Fraction:
        nb = val.numerator.bit_length()
        db = val.denominator.bit_length()
        if nb > MAX_INT_BITS or db > MAX_INT_BITS:
            raise AletheiaError("FRACTION_BIT_LIMIT", f"{label} bit_lengths=({nb},{db}) exceed {MAX_INT_BITS}")
        return val
    if type(val) is str:
        s = _require_utf8_str(val, label)
        if "/" in s:
            parts = s.split("/")
            if len(parts) != 2:
                raise AletheiaError("INVALID_RATIONAL_STR", f"{label} malformed rational")
            num_s, den_s = parts
            n = _parse_int_str(num_s, f"{label}.num")
            d = _parse_int_str(den_s, f"{label}.den")
            if d <= 1 or math.gcd(abs(n), d) != 1:
                raise AletheiaError("INVALID_RATIONAL_CANON", f"{label} must be reduced with denominator > 1")
            return Fraction(n, d)
        return Fraction(_parse_int_str(s, label))
    raise AletheiaError("INVALID_RATIONAL_TYPE", f"{label} must be strict int, Fraction, or str")


def _parse_int_str(tok: str, label: str) -> int:
    if not tok:
        raise AletheiaError("INVALID_INT_STR", f"{label} empty integer token")
    body = tok[1:] if tok[0] == "-" else tok
    if not body or not body.isascii() or not body.isdigit():
        raise AletheiaError("INVALID_INT_STR", f"{label} invalid integer syntax")
    if tok == "-0" or (len(body) > 1 and body[0] == "0"):
        raise AletheiaError("NON_CANONICAL_INT_STR", f"{label} non-canonical integer string")
    if len(body) > MAX_INT_DIGITS:
        raise AletheiaError("INT_DIGIT_LIMIT", f"{label} exceeds {MAX_INT_DIGITS} digits")
    return require_int(int(tok), label)


def ceil_q(q: Fraction) -> int:
    fq = parse_q(q, "ceil_q")
    return -((-fq.numerator) // fq.denominator)


def validate_json_value(obj: Any, *, max_depth: int = MAX_JSON_DEPTH) -> None:
    limit = require_int(max_depth, "max_depth", lo=1, hi=128)
    stack: List[Tuple[Any, int]] = [(obj, 0)]
    while stack:
        cur, depth = stack.pop()
        if depth > limit:
            raise AletheiaError("MAX_DEPTH_EXCEEDED", f"JSON nesting exceeds {limit}")
        t = type(cur)
        if t is dict:
            for k, v in cur.items():
                if type(k) is not str:
                    raise AletheiaError("NON_STR_KEY", "JSON object keys must be strict str")
                _require_utf8_str(k, "json_key")
                stack.append((v, depth + 1))
        elif t is list:
            for item in cur:
                stack.append((item, depth + 1))
        elif t is int:
            require_int(cur, "json_int")
        elif t is str:
            _require_utf8_str(cur, "json_str")
        elif t is bool or cur is None:
            continue
        elif t is float:
            raise AletheiaError("FLOAT_FORBIDDEN", "float values are forbidden in exact JSON")
        else:
            raise AletheiaError("UNSUPPORTED_JSON_TYPE", f"unsupported JSON type {t.__name__}")


def _reject_float(tok: str) -> Any:
    raise AletheiaError("JSON_FLOAT_FORBIDDEN", f"float literal forbidden: {tok!r}")


def _reject_const(tok: str) -> Any:
    raise AletheiaError("JSON_CONSTANT_FORBIDDEN", f"non-RFC8259 constant forbidden: {tok!r}")


def _parse_json_int(tok: str) -> int:
    return _parse_int_str(tok, "json_int")


def _reject_dupes(pairs: List[Tuple[str, Any]]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise AletheiaError("JSON_DUPLICATE_KEY", f"duplicate JSON key: {k!r}")
        out[k] = v
    return out


def parse_strict_json_text(
    raw_text: str,
    *,
    require_object: bool = True,
    max_depth: int = MAX_JSON_DEPTH,
) -> Any:
    if type(require_object) is not bool:
        raise AletheiaError("INVALID_BOOL_TYPE", "require_object must be strict bool")
    text = _require_utf8_str(raw_text, "raw_text")
    raw_bytes = text.encode("utf-8")
    if len(raw_bytes) > MAX_JSON_BYTES:
        raise AletheiaError("JSON_TOO_LARGE", f"JSON exceeds {MAX_JSON_BYTES} bytes")
    if not text.strip():
        raise AletheiaError("EMPTY_JSON_INPUT", "JSON text must be non-empty")
    try:
        obj = json.loads(
            text,
            parse_float=_reject_float,
            parse_constant=_reject_const,
            parse_int=_parse_json_int,
            object_pairs_hook=_reject_dupes,
        )
    except AletheiaError:
        raise
    except (json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise AletheiaError("JSON_SYNTAX_ERROR", str(exc)) from exc
    validate_json_value(obj, max_depth=max_depth)
    if require_object and type(obj) is not dict:
        raise AletheiaError("JSON_ROOT_NOT_OBJECT", "top-level JSON payload must be an object")
    return obj


def canonical_json_bytes(obj: Any) -> bytes:
    validate_json_value(obj)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def canonical_sha256(obj: Any) -> str:
    return hashlib.sha256(canonical_json_bytes(obj)).hexdigest()


def require_no_symlink_path(path: Path) -> None:
    if type(path) is not _EXACT_PATH_TYPE:
        raise AletheiaError("INVALID_PATH_TYPE", "path must be exact pathlib.Path")
    raw_s = _require_utf8_str(str(path), "path")
    if "\x00" in raw_s:
        raise AletheiaError("INVALID_PATH_NUL", "NUL byte forbidden in path")
    try:
        if path.is_symlink():
            raise AletheiaError("SYMLINK_FORBIDDEN", "symlink target path forbidden")
        cur = Path("/") if path.is_absolute() else Path.cwd()
        ancestors: List[Path] = list(cur.parents) + [cur]
        for part in path.parts:
            if part not in ("", "/"):
                cur = cur / part
                ancestors.append(cur)
        if any(p.is_symlink() for p in ancestors):
            raise AletheiaError("SYMLINK_ANCESTOR_FORBIDDEN", "symlink ancestor forbidden")
    except OSError as exc:
        raise AletheiaError("PATH_OS_ERROR", f"path access error: {type(exc).__name__}") from exc


def read_strict_utf8_file(path: Path) -> Tuple[bytes, str]:
    require_no_symlink_path(path)
    try:
        st = path.lstat()
    except OSError as exc:
        raise AletheiaError("FILE_NOT_FOUND", f"cannot stat file: {type(exc).__name__}") from exc
    if not stat.S_ISREG(st.st_mode):
        raise AletheiaError("NOT_REGULAR_FILE", "target path is not a regular file")
    if st.st_size > MAX_JSON_BYTES:
        raise AletheiaError("FILE_TOO_LARGE", f"file exceeds {MAX_JSON_BYTES} bytes")
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise AletheiaError("FILE_READ_ERROR", f"cannot read file: {type(exc).__name__}") from exc
    if b"\r" in raw:
        raise AletheiaError("CR_LINE_ENDINGS_FORBIDDEN", "CR/CRLF line endings forbidden")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise AletheiaError("INVALID_UTF8", "invalid UTF-8 file bytes") from exc
    return raw, text


# =============================================================================
# Catalog Frontier Rooms (`III-14`, `III-20`, `III-21`)
# =============================================================================

FRONTIER_CATALOG: Dict[str, Dict[str, Any]] = {
    "III-14": {
        "width": 15,
        "height": 7,
        "proven_floor": 44,
        "shortest_known": 48,
        "prior_1box_bounds": {
            "single_hero_max_manhattan": 10,
            "cardinal_bottleneck_h_dir": 11,
            "vault_disjoint_h_vault": 21,
        },
        "reference_route": "LLULULULRURURURURUAUDRRDDAUARRDLRAULDLDRARURDUUR",
        "grid": (
            "###############",
            "#.............#",
            "#.5.}}}.]]]]].#",
            "#...}}}.]G.G].#",
            "#.D.}}}.]]]]].#",
            "#.............#",
            "###############",
        ),
    },
    "III-20": {
        "width": 15,
        "height": 9,
        "proven_floor": 77,
        "shortest_known": 84,
        "prior_1box_bounds": {
            "soko53_c2_h_oc_rational": "14/5",
            "soko53_c2_h_oc_ceil": 3,
            "solo_min_sum": 39,
        },
        "reference_route": "ADDDRRADAAADRULARADAAADDLLALAAAARRRRUULAAUALLRADRRRRADRULRURRRRRARRUURURAURRRDDRAUUR",
        "grid": (
            "###############",
            "#....#O.O#...G#",
            "#..##W...1##..#",
            "#..#O..O..O#.G#",
            "#4.#..OGO..#..#",
            "#..#O..O..O#.G#",
            "#..##2...6##..#",
            "#....#O.O#...G#",
            "###############",
        ),
    },
    "III-21": {
        "width": 23,
        "height": 13,
        "proven_floor": 270,
        "shortest_known": 316,
        "prior_1box_bounds": {
            "soko53_c2_h_oc_rational": "21",
            "soko53_c2_h_oc_ceil": 21,
            "solo_min_sum": 60,
        },
        "reference_route": (
            "RRRDRRDRRRURRDRRUURRRRRLLLLDDAUAADLLULLLLLDDAAALLLULDDDRDLULDDLLUUAAAULLULAAUAD"
            "LLLLLAAADLAAALDADRAAAALLDAULAALARUAAARRRRRAUAARDRAAARRDRRUADDRRDDRLAAUAAAULLRRU"
            "RURDDAURULDDRRRRLLLLAAUUAAARDDRRRDRRRRRAAAAAULLULULULLLDUURLDLLUALLLUUAAAALLLLL"
            "DLLLDULLULLLLLLLADDRDALDDAUAAALDURADDUUAAAUAARRRRRRRRUUURUUADRDDDAAAUUURDDDAUUL"
        ),
        "grid": (
            "#######################",
            "#.F.*....#G.G#....*.4.#",
            "#...#....#...#....#...#",
            "#######.........#######",
            "#####.#####O#####.#####",
            "#..##O#..#...#..#O##..#",
            "#.2.*....#G.G#....*.5.#",
            "#..##O#..*...#..#O##..#",
            "#####.####...####.#####",
            "#######..#..*O.*#######",
            "#...###.#######...#...#",
            "#.3.###.##G.G##...#.6.#",
            "#######################",
        ),
    },
}


# =============================================================================
# Standalone Part III Concrete Engine
# =============================================================================

class Part3Oracle:
    """Exact standalone interpreter for Heroes of Sokoban Part III mechanics."""

    def __init__(self, rows: Sequence[str]) -> None:
        if type(rows) not in (list, tuple) or not rows or any(type(r) is not str for r in rows) or not rows[0]:
            raise AletheiaError("INVALID_GRID", "grid must be non-empty list/tuple of str")
        self.h = len(rows)
        self.w = len(rows[0])
        if any(len(r) != self.w for r in rows):
            raise AletheiaError("INVALID_GRID", "grid rows must have equal width")
        self.floor: List[List[Optional[str]]] = [[None] * self.w for _ in range(self.h)]
        self.obj: List[List[Optional[str]]] = [[None] * self.w for _ in range(self.h)]
        self.notes: Set[Tuple[int, int]] = set()
        for y, row in enumerate(rows):
            for x, ch in enumerate(row):
                if ch == ".":
                    continue
                if ch in ("G", "}"):
                    self.floor[y][x] = ch
                elif ch in ("#", "*", "O", "]") or ch in ACTIVE_HEROES or ch in INACTIVE_HEROES:
                    self.obj[y][x] = ch
                else:
                    raise AletheiaError("INVALID_GRID_SYMBOL", f"unrecognized symbol {ch!r}")
        self._run_late()

    def clone(self) -> "Part3Oracle":
        cp = Part3Oracle.__new__(Part3Oracle)
        cp.h = self.h
        cp.w = self.w
        cp.floor = [r[:] for r in self.floor]
        cp.obj = [r[:] for r in self.obj]
        cp.notes = set(self.notes)
        return cp

    def signature(self) -> Tuple[Any, ...]:
        return (
            tuple(tuple(r) for r in self.obj),
            tuple(tuple(r) for r in self.floor),
            frozenset(self.notes),
        )

    @staticmethod
    def is_hero(o: Optional[str]) -> bool:
        return (o in ACTIVE_HEROES) or (o in INACTIVE_HEROES)

    @staticmethod
    def is_healer(o: Optional[str]) -> bool:
        return o in ("P", "4")

    @staticmethod
    def is_moveable(o: Optional[str]) -> bool:
        return o == "*" or (o in INACTIVE_HEROES) or o == "O"

    @staticmethod
    def is_static(o: Optional[str]) -> bool:
        return o in ("#", "]")

    @classmethod
    def is_weighing(cls, o: Optional[str]) -> bool:
        return o in ("*", "#", "O") or cls.is_hero(o)

    def find_active(self) -> Optional[Tuple[int, int, str]]:
        for y in range(self.h):
            for x in range(self.w):
                o = self.obj[y][x]
                if o in ACTIVE_HEROES:
                    return (x, y, o)
        return None

    def extract_heroes(self) -> Tuple[Dict[str, Tuple[int, int]], Optional[str]]:
        heroes: Dict[str, Tuple[int, int]] = {}
        active: Optional[str] = None
        for y in range(self.h):
            for x in range(self.w):
                o = self.obj[y][x]
                if o in ACTIVE_HEROES:
                    slot = TO_INACTIVE[o]
                    heroes[slot] = (x, y)
                    active = slot
                elif o in INACTIVE_HEROES:
                    heroes[o] = (x, y)
        return heroes, active

    def check_win(self) -> bool:
        for y in range(self.h):
            for x in range(self.w):
                if self.is_hero(self.obj[y][x]) != (self.floor[y][x] == "G"):
                    return False
        return True

    def _compute_notes(self) -> None:
        self.notes.clear()
        bard = next(((x, y) for y in range(self.h) for x in range(self.w) if self.obj[y][x] == "B"), None)
        if bard is None:
            return
        bx, by = bard
        for ny in range(max(0, by - 2), min(self.h, by + 3)):
            for nx in range(max(0, bx - 2), min(self.w, bx + 3)):
                if (nx, ny) != (bx, by) and self.is_moveable(self.obj[ny][nx]):
                    self.notes.add((nx, ny))

    def _run_late(self) -> bool:
        self._compute_notes()
        dying: Set[Tuple[int, int]] = set()
        for y in range(self.h):
            for x in range(self.w):
                if self.obj[y][x] == "O":
                    for dx, dy in DIR_DELTAS:
                        nx, ny = x + dx, y + dy
                        if 0 <= nx < self.w and 0 <= ny < self.h:
                            vo = self.obj[ny][nx]
                            if vo == "O" or self.is_hero(vo):
                                dying.add((nx, ny))
        for x, y in list(dying):
            if self.is_healer(self.obj[y][x]):
                dying.remove((x, y))
        for y in range(self.h):
            for x in range(self.w):
                if self.is_healer(self.obj[y][x]):
                    for dx, dy in DIR_DELTAS:
                        nx, ny = x + dx, y + dy
                        if (nx, ny) in dying and self.is_hero(self.obj[ny][nx]):
                            dying.remove((nx, ny))
        corpse = False
        for x, y in dying:
            if self.obj[y][x] == "O":
                self.obj[y][x] = None
            elif self.is_hero(self.obj[y][x]):
                self.obj[y][x] = "CORPSE"
                corpse = True

        sw = [(x, y) for y in range(self.h) for x in range(self.w) if self.floor[y][x] == "}"]
        if sw:
            any_w = any(self.is_weighing(self.obj[y][x]) for x, y in sw)
            any_u = any(not self.is_weighing(self.obj[y][x]) for x, y in sw)
            if any_w and not any_u:
                for y in range(self.h):
                    for x in range(self.w):
                        if self.obj[y][x] == "]":
                            self.obj[y][x] = None
                            self.floor[y][x] = "PO"
            elif any_u:
                for y in range(self.h):
                    for x in range(self.w):
                        if self.floor[y][x] == "PO":
                            if self.is_hero(self.obj[y][x]):
                                corpse = True
                            self.floor[y][x] = None
                            self.obj[y][x] = "]"

        self.notes = {(x, y) for (x, y) in self.notes if self.is_moveable(self.obj[y][x])}
        return corpse

    def step(self, key: str) -> Tuple[bool, bool]:
        if key not in ("U", "D", "L", "R", "A"):
            raise AletheiaError("INVALID_KEY", f"invalid key {key!r}")
        act = self.find_active()
        if act is None:
            return False, False
        ax, ay, ah = act

        if key == "A":
            self.notes.clear()
            cur_inact = TO_INACTIVE[ah]
            cur_pos = CYCLE_ORDER.index(cur_inact)
            for offset in range(1, 6):
                target_inact = CYCLE_ORDER[(cur_pos + offset) % 6]
                found = None
                for x in range(self.w):
                    for y in range(self.h):
                        if self.obj[y][x] == target_inact:
                            found = (x, y)
                            break
                    if found is not None:
                        break
                if found is not None:
                    fx, fy = found
                    self.obj[ay][ax] = cur_inact
                    self.obj[fy][fx] = TO_ACTIVE[target_inact]
                    break
            corpse = self._run_late()
            return (not corpse), self.check_win()

        dx, dy = DIRS[key]
        nx, ny = ax + dx, ay + dy

        if ah == "F":
            self.notes.clear()
            cx, cy = nx, ny
            while 0 <= cx < self.w and 0 <= cy < self.h and self.is_moveable(self.obj[cy][cx]):
                cx += dx
                cy += dy
            if 0 <= cx < self.w and 0 <= cy < self.h and self.obj[cy][cx] is None:
                while (cx, cy) != (ax, ay):
                    px, py = cx - dx, cy - dy
                    self.obj[cy][cx] = self.obj[py][px]
                    cx, cy = px, py
                self.obj[ay][ax] = None
        elif ah == "T":
            self.notes.clear()
            if 0 <= nx < self.w and 0 <= ny < self.h and self.obj[ny][nx] is None:
                bx, by = ax - dx, ay - dy
                self.obj[ny][nx] = "T"
                if 0 <= bx < self.w and 0 <= by < self.h and self.is_moveable(self.obj[by][bx]):
                    self.obj[ay][ax] = self.obj[by][bx]
                    self.obj[by][bx] = None
                else:
                    self.obj[ay][ax] = None
        elif ah == "W":
            self.notes.clear()
            wx, wy = ax, ay
            while True:
                tx, ty = wx + dx, wy + dy
                if not (0 <= tx < self.w and 0 <= ty < self.h):
                    if 0 <= nx < self.w and 0 <= ny < self.h and self.obj[ny][nx] is None:
                        self.obj[ny][nx] = "W"
                        self.obj[ay][ax] = None
                    break
                tobj = self.obj[ty][tx]
                if tobj is None:
                    wx, wy = tx, ty
                elif self.is_static(tobj):
                    if self.obj[ny][nx] is None:
                        self.obj[ny][nx] = "W"
                        self.obj[ay][ax] = None
                    break
                else:
                    self.obj[ty][tx] = "W"
                    self.obj[ay][ax] = tobj
                    break
        elif ah == "P":
            self.notes.clear()
            if 0 <= nx < self.w and 0 <= ny < self.h and self.obj[ny][nx] is None:
                self.obj[ny][nx] = "P"
                self.obj[ay][ax] = None
        elif ah == "D":
            self.notes.clear()
            if 0 <= nx < self.w and 0 <= ny < self.h:
                tobj = self.obj[ny][nx]
                if tobj is None:
                    self.obj[ny][nx] = "D"
                    self.obj[ay][ax] = None
                elif tobj in ("*", "O"):
                    self.obj[ny][nx] = "#"
                elif tobj == "#":
                    self.obj[ny][nx] = "*"
                elif not self.is_healer(tobj) and self.is_hero(tobj):
                    adj_h = any(
                        0 <= nx + hx < self.w and 0 <= ny + hy < self.h and self.is_healer(self.obj[ny + hy][nx + hx])
                        for hx, hy in DIR_DELTAS
                    )
                    if not adj_h:
                        self.obj[ny][nx] = "#"
        else:  # ah == "B"
            snap_obj = [r[:] for r in self.obj]
            snap_floor = [r[:] for r in self.floor]
            snap_notes = set(self.notes)
            bard_pos = (ax, ay)
            bard_moved = False
            charmed = set(self.notes)
            changed = True
            while changed:
                changed = False
                for cx, cy in list(charmed):
                    tx, ty = cx + dx, cy + dy
                    if 0 <= tx < self.w and 0 <= ty < self.h and self.obj[ty][tx] is None:
                        self.obj[ty][tx] = self.obj[cy][cx]
                        self.obj[cy][cx] = None
                        charmed.remove((cx, cy))
                        changed = True
                if not bard_moved:
                    tx, ty = bard_pos[0] + dx, bard_pos[1] + dy
                    if 0 <= tx < self.w and 0 <= ty < self.h and self.obj[ty][tx] is None:
                        self.obj[ty][tx] = "B"
                        self.obj[bard_pos[1]][bard_pos[0]] = None
                        bard_pos = (tx, ty)
                        bard_moved = True
                        changed = True
            if not bard_moved:
                self.obj = snap_obj
                self.floor = snap_floor
                self.notes = snap_notes
                return True, self.check_win()
            self.notes.clear()

        corpse = self._run_late()
        return (not corpse), self.check_win()


# =============================================================================
# Pillar 1: Exact Pure-Q Coupled Multi-Quotient Farkas LP & Deadlock Engine
# =============================================================================

@dataclass(frozen=True)
class QuotientGraph:
    name: str
    num_vertices: int
    start: int
    goals: Tuple[int, ...]
    edges: Tuple[Tuple[int, int, str], ...]  # (u, v, action_class)


def solve_coupled_farkas_lp(
    *,
    instance_id: str,
    action_classes: Sequence[str],
    quotients: Sequence[QuotientGraph],
    cost_partition: Sequence[Dict[str, Fraction]],
) -> Dict[str, Any]:
    """Solve the exact rational action-class cost-partitioned multi-quotient LP and
    construct its exact Farkas dual flow `(y_{m,e}, lambda_a)` with zero duality gap.
    """
    if (
        type(instance_id) is not str
        or type(action_classes) not in (list, tuple)
        or type(quotients) not in (list, tuple)
        or type(cost_partition) not in (list, tuple)
        or not action_classes
        or not quotients
        or len(quotients) != len(cost_partition)
    ):
        raise AletheiaError("INVALID_FARKAS_INPUT", "non-empty action_classes and aligned quotients required")
    act_list = [_require_utf8_str(a, "action_class") for a in action_classes]
    act_set = set(act_list)
    if len(act_set) != len(act_list):
        raise AletheiaError("DUPLICATE_ACTION_CLASS", "action_classes must be unique")

    # Validate exact cost partition: w_{m,a} >= 0 and sum_m w_{m,a} <= 1
    weights_norm: List[Dict[str, Fraction]] = []
    act_sums: Dict[str, Fraction] = {a: Fraction(0) for a in act_list}
    for m, wmap in enumerate(cost_partition):
        if type(wmap) is not dict:
            raise AletheiaError("INVALID_FARKAS_INPUT", f"cost_partition[{m}] must be strict dict")
        norm_m: Dict[str, Fraction] = {}
        for a in act_list:
            w = parse_q(wmap.get(a, Fraction(0)), f"w[{m}][{a}]")
            if w < 0:
                raise AletheiaError("NEGATIVE_WEIGHT", f"negative cost partition weight on {a}")
            norm_m[a] = w
            act_sums[a] += w
        weights_norm.append(norm_m)
    for a, total_w in act_sums.items():
        if total_w > 1:
            raise AletheiaError("COST_PARTITION_EXCEEDS_ONE", f"sum_m w_m[{a}] > 1")

    q_certs: List[Dict[str, Any]] = []
    primal_total = Fraction(0)
    lambda_dual: Dict[str, Fraction] = {a: Fraction(0) for a in act_list}

    for m, qg in enumerate(quotients):
        if type(qg) is not QuotientGraph:
            raise AletheiaError("INVALID_QUOTIENT", f"quotients[{m}] must be QuotientGraph")
        n = require_int(qg.num_vertices, f"{qg.name}.num_vertices", lo=1)
        s0 = require_int(qg.start, f"{qg.name}.start", lo=0, hi=n - 1)
        goals = tuple(sorted(set(require_int(g, f"{qg.name}.goal", lo=0, hi=n - 1) for g in qg.goals)))
        if not goals:
            raise AletheiaError("EMPTY_GOALS", f"{qg.name} requires >= 1 goal")
        wmap = weights_norm[m]
        rev_adj: List[List[Tuple[int, Fraction, int]]] = [[] for _ in range(n)]
        edge_list: List[List[Any]] = []
        for e_idx, (u, v, a) in enumerate(qg.edges):
            ui = require_int(u, f"{qg.name}.e.u", lo=0, hi=n - 1)
            vi = require_int(v, f"{qg.name}.e.v", lo=0, hi=n - 1)
            if a not in act_set:
                raise AletheiaError("UNKNOWN_ACTION_CLASS", f"unknown action class {a!r}")
            rev_adj[vi].append((ui, wmap[a], e_idx))
            edge_list.append([ui, vi, a])

        # Exact shortest-path primal potentials h_m(u) via Dijkstra (all w >= 0)
        h: List[Optional[Fraction]] = [None] * n
        parent_edge: List[int] = [-1] * n
        pq: List[Tuple[Fraction, int]] = []
        for g in goals:
            h[g] = Fraction(0)
            heapq.heappush(pq, (Fraction(0), g))
        while pq:
            dv, v = heapq.heappop(pq)
            if h[v] is None or dv != h[v]:
                continue
            for u, w, e_idx in rev_adj[v]:
                cand = dv + w
                hu = h[u]
                if hu is None or cand < hu:
                    h[u] = cand
                    parent_edge[u] = e_idx
                    heapq.heappush(pq, (cand, u))

        if h[s0] is None:
            raise AletheiaError("QUOTIENT_UNREACHABLE", f"{qg.name} start vertex unreachable from goals")
        # Assign unreachable non-start vertices 0? No: keep only reachable or fail if unreachable
        if any(x is None for x in h):
            raise AletheiaError("QUOTIENT_PARTIAL_UNREACHABLE", f"{qg.name} has unreachable vertices")
        h_exact: List[Fraction] = [x if x is not None else Fraction(0) for x in h]
        h_s0 = h_exact[s0]
        primal_total += h_s0

        # Trace exact unit Farkas dual flow y_{m,e} along tight shortest-path from s0 to a goal
        dual_y: Dict[int, Fraction] = {}
        goal_set = set(goals)
        cur = s0
        while cur not in goal_set:
            pe = parent_edge[cur]
            dual_y[pe] = Fraction(1)
            cur = edge_list[pe][1]

        action_flow_m: Dict[str, Fraction] = {a: Fraction(0) for a in act_list}
        for e_idx, flow_val in dual_y.items():
            a_lbl = edge_list[e_idx][2]
            action_flow_m[a_lbl] += flow_val
        for a in act_list:
            if action_flow_m[a] > lambda_dual[a]:
                lambda_dual[a] = action_flow_m[a]

        q_certs.append({
            "name": qg.name,
            "num_vertices": n,
            "start": s0,
            "goals": list(goals),
            "edges": edge_list,
            "weights": {a: fmt_q(wmap[a]) for a in act_list},
            "primal_h": [fmt_q(x) for x in h_exact],
            "primal_start_q": fmt_q(h_s0),
            "dual_flow_edges": [[e_idx, fmt_q(dual_y[e_idx])] for e_idx in sorted(dual_y)],
        })

    dual_total = sum(lambda_dual.values(), Fraction(0))
    if primal_total != dual_total:
        raise AletheiaError("NONZERO_DUALITY_GAP", "cost partition is not tight on the chosen dual path")

    return {
        "instance_id": instance_id,
        "action_classes": act_list,
        "quotients": q_certs,
        "dual_lambda": {a: fmt_q(lambda_dual[a]) for a in act_list},
        "primal_objective_q": fmt_q(primal_total),
        "dual_objective_q": fmt_q(dual_total),
        "ceil_integer_bound": ceil_q(primal_total),
        "strong_duality_exact": True,
    }


def independent_bfs_distance(
    num_vertices: int,
    start: int,
    goals: Sequence[int],
    edges: Sequence[Tuple[int, int]],
) -> Optional[int]:
    """Independent unweighted exact BFS distance oracle (returns None if unreachable)."""
    n = require_int(num_vertices, "num_vertices", lo=1)
    s0 = require_int(start, "start", lo=0, hi=n - 1)
    if type(goals) not in (list, tuple) or type(edges) not in (list, tuple):
        raise AletheiaError("INVALID_GRAPH_CONTAINER", "goals and edges must be list or tuple")
    goal_set = {require_int(g, "goal", lo=0, hi=n - 1) for g in goals}
    adj: List[List[int]] = [[] for _ in range(n)]
    for e in edges:
        if type(e) not in (list, tuple) or len(e) != 2:
            raise AletheiaError("INVALID_EDGE", "edge must be length-2 list or tuple")
        adj[require_int(e[0], "u", lo=0, hi=n - 1)].append(require_int(e[1], "v", lo=0, hi=n - 1))
    dist: List[int] = [-1] * n
    dist[s0] = 0
    q: deque[int] = deque([s0])
    while q:
        u = q.popleft()
        if u in goal_set:
            return dist[u]
        for v in adj[u]:
            if dist[v] < 0:
                dist[v] = dist[u] + 1
                q.append(v)
    return None


def certify_farkas_deadlock(
    *,
    witness_id: str,
    num_vertices: int,
    start: int,
    goals: Sequence[int],
    edges: Sequence[Tuple[int, int]],
    one_entity_projections: Sequence[Dict[str, Any]],
) -> Dict[str, Any]:
    """Construct an exact Farkas infeasibility cut-set witness proving `d*(start) = +inf`
    while independently certifying finite distance on every 1-entity projection.
    """
    _require_utf8_str(witness_id, "witness_id")
    n = require_int(num_vertices, "num_vertices", lo=1)
    s0 = require_int(start, "start", lo=0, hi=n - 1)
    if (
        type(goals) not in (list, tuple)
        or type(edges) not in (list, tuple)
        or type(one_entity_projections) not in (list, tuple)
    ):
        raise AletheiaError("INVALID_DEADLOCK_INPUT", "goals, edges, and projections must be list/tuple")
    goal_set = sorted({require_int(g, "goal", lo=0, hi=n - 1) for g in goals})
    adj: List[List[int]] = [[] for _ in range(n)]
    edge_pairs: List[List[int]] = []
    for e in edges:
        if type(e) not in (list, tuple) or len(e) != 2:
            raise AletheiaError("INVALID_EDGE", "edge must be length-2 list or tuple")
        ui = require_int(e[0], "u", lo=0, hi=n - 1)
        vi = require_int(e[1], "v", lo=0, hi=n - 1)
        adj[ui].append(vi)
        edge_pairs.append([ui, vi])

    reach: Set[int] = {s0}
    q: deque[int] = deque([s0])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v not in reach:
                reach.add(v)
                q.append(v)

    if any(g in reach for g in goal_set):
        raise AletheiaError("NOT_DEADLOCK", f"{witness_id} reaches a goal state")

    proj_results: List[Dict[str, Any]] = []
    for proj in one_entity_projections:
        d1 = independent_bfs_distance(
            proj["num_vertices"],
            proj["start"],
            proj["goals"],
            [(e[0], e[1]) for e in proj["edges"]],
        )
        if d1 is None:
            raise AletheiaError("PROJECTION_NOT_FINITE", f"1-entity projection {proj['name']} is not finite")
        proj_results.append({
            "name": proj["name"],
            "finite_distance": d1,
            "num_vertices": proj["num_vertices"],
        })

    return {
        "witness_id": witness_id,
        "num_vertices": n,
        "start": s0,
        "goals": goal_set,
        "edges": edge_pairs,
        "reachable_cut_set": sorted(reach),
        "reachable_cut_size": len(reach),
        "coupled_infeasible": True,
        "one_entity_projections": proj_results,
    }


# =============================================================================
# Topology Helpers & Globally 1-Step-Consistent Coupled Potentials
# =============================================================================

def _nonwall_component(ps: Part3Oracle, sx: int, sy: int) -> Set[Tuple[int, int]]:
    vis: Set[Tuple[int, int]] = {(sx, sy)}
    q: deque[Tuple[int, int]] = deque([(sx, sy)])
    while q:
        x, y = q.popleft()
        for dx, dy in DIR_DELTAS:
            nx, ny = x + dx, y + dy
            if 1 <= nx < ps.w - 1 and 1 <= ny < ps.h - 1 and ps.obj[ny][nx] != "#" and (nx, ny) not in vis:
                vis.add((nx, ny))
                q.append((nx, ny))
    return vis


def _wall_boundary(ps: Part3Oracle, comp: Set[Tuple[int, int]]) -> Set[Tuple[int, int]]:
    out: Set[Tuple[int, int]] = set()
    for x, y in comp:
        for dx, dy in DIR_DELTAS:
            nx, ny = x + dx, y + dy
            if 1 <= nx < ps.w - 1 and 1 <= ny < ps.h - 1 and ps.obj[ny][nx] == "#":
                out.add((nx, ny))
    return out


def _min_walls_exit(
    ps: Part3Oracle,
    seeds: Sequence[Tuple[int, int]],
    region: Set[Tuple[int, int]],
) -> int:
    dist: Dict[Tuple[int, int], int] = {}
    dq: deque[Tuple[int, int, int]] = deque()
    for sx, sy in seeds:
        dist[(sx, sy)] = 0
        dq.appendleft((0, sx, sy))
    while dq:
        d, x, y = dq.popleft()
        if d > dist[(x, y)]:
            continue
        if (x, y) not in region:
            return d
        for dx, dy in DIR_DELTAS:
            nx, ny = x + dx, y + dy
            if 1 <= nx < ps.w - 1 and 1 <= ny < ps.h - 1:
                c = 1 if ps.obj[ny][nx] == "#" else 0
                nd = d + c
                if nd < dist.get((nx, ny), 999):
                    dist[(nx, ny)] = nd
                    if c == 0:
                        dq.appendleft((nd, nx, ny))
                    else:
                        dq.append((nd, nx, ny))
    return 999


# ---- Precomputed room topologies (derived directly from FRONTIER_CATALOG) ----

def _build_topologies() -> Dict[str, Any]:
    ps14 = Part3Oracle(FRONTIER_CATALOG["III-14"]["grid"])
    s9 = tuple((x, y) for x in (4, 5, 6) for y in (2, 3, 4))
    perim14 = frozenset((x, y) for y in range(ps14.h) for x in range(ps14.w) if x in (0, 14) or y in (0, 6))

    ps20 = Part3Oracle(FRONTIER_CATALOG["III-20"]["grid"])
    c20_l = frozenset(_nonwall_component(ps20, 1, 4))
    c20_r = frozenset(_nonwall_component(ps20, 13, 1))
    b20_l = frozenset(_wall_boundary(ps20, set(c20_l)))
    b20_r = frozenset(_wall_boundary(ps20, set(c20_r)))
    g20_r = ((13, 1), (13, 3), (13, 5), (13, 7))
    g20_all = frozenset(((13, 1), (13, 3), (7, 4), (13, 5), (13, 7)))

    ps21 = Part3Oracle(FRONTIER_CATALOG["III-21"]["grid"])
    c21_dru = frozenset(_nonwall_component(ps21, 20, 11))
    c21_bard = frozenset(_nonwall_component(ps21, 20, 6))
    c21_bg = frozenset(_nonwall_component(ps21, 10, 11))
    c21_wiz = frozenset(_nonwall_component(ps21, 2, 11))
    b21_dru = frozenset(_wall_boundary(ps21, set(c21_dru)))
    b21_bard = frozenset(_wall_boundary(ps21, set(c21_bard)))
    b21_bg = frozenset(_wall_boundary(ps21, set(c21_bg)))
    b21_wiz = frozenset(_wall_boundary(ps21, set(c21_wiz)))
    r21_wiz = frozenset((x, y) for y in range(8, 12) for x in range(1, 7))
    b21_wiz_adj = frozenset(
        set(c21_wiz)
        | set(b21_wiz)
        | {
            (x + dx, y + dy)
            for x, y in b21_wiz
            for dx, dy in DIR_DELTAS
            if 1 <= x + dx < ps21.w - 1 and 1 <= y + dy < ps21.h - 1
        }
    )
    r21_wiz_adj = frozenset(
        set(r21_wiz)
        | {
            (x + dx, y + dy)
            for x, y in r21_wiz
            for dx, dy in DIR_DELTAS
            if 1 <= x + dx < ps21.w - 1 and 1 <= y + dy < ps21.h - 1
        }
    )
    g21_all = frozenset(((10, 1), (12, 1), (10, 6), (12, 6), (10, 11), (12, 11)))

    return {
        "s9": s9,
        "s9_set": frozenset(s9),
        "perim14": perim14,
        "c20_l": c20_l,
        "c20_r": c20_r,
        "b20_l": b20_l,
        "b20_r": b20_r,
        "g20_r": g20_r,
        "g20_all": g20_all,
        "c21_dru": c21_dru,
        "c21_bard": c21_bard,
        "c21_bg": c21_bg,
        "c21_wiz": c21_wiz,
        "b21_dru": b21_dru,
        "b21_bard": b21_bard,
        "b21_bg": b21_bg,
        "b21_wiz": b21_wiz,
        "r21_wiz": r21_wiz,
        "b21_wiz_adj": b21_wiz_adj,
        "r21_wiz_adj": r21_wiz_adj,
        "g21_all": g21_all,
    }


TOPO = _build_topologies()


def _max_match_9(adj: List[List[int]]) -> int:
    match_r = [-1] * 9

    def dfs(u: int, vis: List[bool]) -> bool:
        for v in adj[u]:
            if not vis[v]:
                vis[v] = True
                if match_r[v] == -1 or dfs(match_r[v], vis):
                    match_r[v] = u
                    return True
        return False

    cnt = 0
    for u in range(len(adj)):
        if dfs(u, [False] * 9):
            cnt += 1
            if cnt == 9:
                return 9
    return cnt


def eval_iii14_coupled(ps: Part3Oracle) -> Tuple[int, Dict[str, int]]:
    """Globally 1-step-consistent coupled Farkas potential on `III-14` (`h0 = 24`)."""
    if type(ps) is not Part3Oracle:
        raise AletheiaError("INVALID_ORACLE_STATE", "ps must be Part3Oracle")
    if ps.check_win():
        return 0, {"w2c": 0, "a_sw": 0, "bard_druid_move": 0}
    s9 = TOPO["s9"]
    s9_set = TOPO["s9_set"]
    perim14 = TOPO["perim14"]

    b_pos: Optional[Tuple[int, int]] = None
    d_pos: Optional[Tuple[int, int]] = None
    active: Optional[str] = None
    supply: List[Tuple[int, int]] = []
    n_cr = 0
    weighed_nonhero = 0
    for y in range(ps.h):
        for x in range(ps.w):
            o = ps.obj[y][x]
            if o == "B":
                b_pos, active = (x, y), "B"
            elif o == "5":
                b_pos = (x, y)
            elif o == "D":
                d_pos, active = (x, y), "D"
            elif o == "6":
                d_pos = (x, y)
            elif o == "*":
                n_cr += 1
                supply.append((x, y))
                if (x, y) in s9_set:
                    weighed_nonhero += 1
            elif o == "#":
                supply.append((x, y))
                if (x, y) not in perim14:
                    n_cr += 1
                    if (x, y) in s9_set:
                        weighed_nonhero += 1

    if b_pos is None or d_pos is None or active is None:
        return 0, {"w2c": 0, "a_sw": 0, "bard_druid_move": 0}

    need_w2c = max(0, 9 - n_cr)
    if need_w2c >= 1 and weighed_nonhero < 9:
        a_need = 1 if active == "D" else 2
    elif need_w2c >= 1:
        a_need = 0 if active == "D" else 1
    elif weighed_nonhero < 9:
        a_need = 1 if active == "D" else 0
    else:
        a_need = 0

    candidates: List[Tuple[int, int, int, int, int]] = []
    for g_b, g_d in (((9, 3), (11, 3)), ((11, 3), (9, 3))):
        b_l0 = max(0, b_pos[0] - g_b[0])
        b_r0 = max(0, g_b[0] - b_pos[0])
        b_u0 = max(0, b_pos[1] - g_b[1])
        b_d0 = max(0, g_b[1] - b_pos[1])
        for kx in range(0, 12):
            b_l, b_r = b_l0 + kx, b_r0 + kx
            dx_extra = max(0, d_pos[0] - g_d[0] - b_l) + max(0, g_d[0] - d_pos[0] - b_r)
            for ky in range(0, 8):
                b_u, b_d = b_u0 + ky, b_d0 + ky
                dy_extra = max(0, d_pos[1] - g_d[1] - b_u) + max(0, g_d[1] - d_pos[1] - b_d)
                tot = b_l + b_r + b_u + b_d + dx_extra + dy_extra
                candidates.append((tot, b_l, b_r, b_u, b_d))
    candidates.sort()
    best_move = 999
    for tot, b_l, b_r, b_u, b_d in candidates:
        if tot >= best_move:
            break
        adj: List[List[int]] = []
        cover_mask = 0
        for sx0, sy0 in supply:
            reach: List[int] = []
            for j, (tx, ty) in enumerate(s9):
                if (sx0 - tx <= b_l) and (tx - sx0 <= b_r) and (sy0 - ty <= b_u) and (ty - sy0 <= b_d):
                    reach.append(j)
                    cover_mask |= 1 << j
            if reach:
                adj.append(reach)
        if cover_mask == 511 and len(adj) >= 9 and _max_match_9(adj) == 9:
            best_move = tot
            break

    total = need_w2c + a_need + best_move
    return total, {"w2c": need_w2c, "a_sw": a_need, "bard_druid_move": best_move}


def _h_dir_pts(cand_pts: Sequence[Tuple[int, int]], goals: Sequence[Tuple[int, int]]) -> int:
    best = 16
    for n_l in range(0, best):
        for n_r in range(0, best - n_l):
            for n_u in range(0, best - n_l - n_r):
                need_d = 0
                ok = True
                for gx, gy in goals:
                    best_g = 999
                    for x, y in cand_pts:
                        if x - gx <= n_l and gx - x <= n_r and y - gy <= n_u:
                            d = gy - y if gy > y else 0
                            if d < best_g:
                                best_g = d
                    if best_g == 999:
                        ok = False
                        break
                    if best_g > need_d:
                        need_d = best_g
                if ok and n_l + n_r + n_u + need_d < best:
                    best = n_l + n_r + n_u + need_d
    return best


def eval_iii20_coupled(ps: Part3Oracle) -> Tuple[int, Dict[str, int]]:
    """Globally 1-step-consistent coupled Farkas potential on `III-20` (`h0 = 9`)."""
    if type(ps) is not Part3Oracle:
        raise AletheiaError("INVALID_ORACLE_STATE", "ps must be Part3Oracle")
    if ps.check_win():
        return 0, {"cut_l": 0, "cut_r": 0, "a_sw": 0, "occ_frontier": 0}
    heroes, active = ps.extract_heroes()
    if "6" not in heroes or active is None:
        return 0, {"cut_l": 0, "cut_r": 0, "a_sw": 0, "occ_frontier": 0}

    c20_l = TOPO["c20_l"]
    c20_r = TOPO["c20_r"]
    b20_l = TOPO["b20_l"]
    b20_r = TOPO["b20_r"]
    g20_r = TOPO["g20_r"]
    g20_all = TOPO["g20_all"]

    left_heroes = sum(1 for x, y in c20_l if ps.is_hero(ps.obj[y][x]))
    cut_l = 1 if (left_heroes > 0 and all(ps.obj[y][x] == "#" for x, y in b20_l)) else 0
    right_heroes = sum(1 for x, y in c20_r if ps.is_hero(ps.obj[y][x]))
    cut_r = 1 if (right_heroes < 4 and all(ps.obj[y][x] == "#" for x, y in b20_r)) else 0

    slots = sorted(heroes.keys())
    act_i = slots.index(active)
    dru_i = slots.index("6")
    non_d_off_goal = any(pos not in g20_all for sl, pos in heroes.items() if sl != "6")
    non_d_trapped_l = any(sl != "6" and pos in c20_l for sl, pos in heroes.items()) and cut_l >= 1
    sealed_r_needs_other = (right_heroes < 3) and cut_r >= 1

    if non_d_trapped_l or sealed_r_needs_other:
        a_tax = ((dru_i - act_i) % len(slots)) + 1
    elif cut_l + cut_r >= 1:
        a_tax = (dru_i - act_i) % len(slots)
    elif active == "6" and non_d_off_goal:
        a_tax = 1
    else:
        a_tax = 0

    m_with_r: List[Tuple[int, int]] = []
    for y in range(ps.h):
        for x in range(ps.w):
            o = ps.obj[y][x]
            if ps.is_hero(o) or o in ("*", "O") or (o == "#" and ((x, y) in b20_l or (x, y) in b20_r)):
                m_with_r.append((x, y))
    occ_r = _h_dir_pts(m_with_r, g20_r)

    total = cut_l + cut_r + a_tax + occ_r
    return total, {"cut_l": cut_l, "cut_r": cut_r, "a_sw": a_tax, "occ_frontier": occ_r}


def eval_iii21_coupled(ps: Part3Oracle) -> Tuple[int, Dict[str, int]]:
    """Globally 1-step-consistent coupled Farkas potential on `III-21` (`h0 = 30`)."""
    if type(ps) is not Part3Oracle:
        raise AletheiaError("INVALID_ORACLE_STATE", "ps must be Part3Oracle")
    if ps.check_win():
        return 0, {
            "cut_dru": 0,
            "cut_bard": 0,
            "cut_bg": 0,
            "cut_wiz": 0,
            "a_sw": 0,
            "pre_maze": 0,
            "wiz_post": 0,
        }
    heroes, active = ps.extract_heroes()
    if "6" not in heroes or active is None:
        return 0, {
            "cut_dru": 0,
            "cut_bard": 0,
            "cut_bg": 0,
            "cut_wiz": 0,
            "a_sw": 0,
            "pre_maze": 0,
            "wiz_post": 0,
        }

    c21_dru = TOPO["c21_dru"]
    c21_bard = TOPO["c21_bard"]
    c21_bg = TOPO["c21_bg"]
    c21_wiz = TOPO["c21_wiz"]
    b21_dru = TOPO["b21_dru"]
    b21_bard = TOPO["b21_bard"]
    b21_bg = TOPO["b21_bg"]
    b21_wiz = TOPO["b21_wiz"]
    r21_wiz = TOPO["r21_wiz"]
    g21_all = TOPO["g21_all"]

    dru_in = [p for p in c21_dru if ps.is_hero(ps.obj[p[1]][p[0]])]
    cut_dru = 1 if (dru_in and all(ps.obj[y][x] == "#" for x, y in b21_dru)) else 0

    bard_in = [p for p in c21_bard if ps.is_hero(ps.obj[p[1]][p[0]])]
    cut_bard = 1 if (bard_in and all(ps.obj[y][x] == "#" for x, y in b21_bard)) else 0

    bg_heroes = sum(1 for x, y in c21_bg if ps.is_hero(ps.obj[y][x]))
    cut_bg = 1 if (bg_heroes < 2 and all(ps.obj[y][x] == "#" for x, y in b21_bg)) else 0

    wiz_in = [p for p in c21_wiz if ps.is_hero(ps.obj[p[1]][p[0]])]
    cut_wiz = _min_walls_exit(ps, wiz_in, set(r21_wiz)) if wiz_in else 0
    total_cuts = cut_dru + cut_bard + cut_bg + cut_wiz

    slots = sorted(heroes.keys())
    act_i = slots.index(active)
    dru_i = slots.index("6")
    non_d_off_goal = any(pos not in g21_all for sl, pos in heroes.items() if sl != "6")
    wiz_non_d_trapped = any(sl != "6" and pos in c21_wiz for sl, pos in heroes.items()) and cut_wiz >= 1
    bard_non_d_trapped = any(sl != "6" and pos in c21_bard for sl, pos in heroes.items()) and cut_bard >= 1

    if wiz_non_d_trapped or bard_non_d_trapped:
        a_tax = ((dru_i - act_i) % len(slots)) + 1
    elif total_cuts >= 1:
        a_tax = (dru_i - act_i) % len(slots)
    elif active == "6" and non_d_off_goal:
        a_tax = 1
    else:
        a_tax = 0

    wiz_pos = heroes.get("3")
    wiz_sealed = (wiz_pos in c21_wiz) and (cut_wiz >= 1)
    dru_pos = heroes["6"]
    pre_move = 0
    if wiz_sealed:
        b_wiz_intact = all(ps.obj[y][x] == "#" for x, y in b21_wiz)
        target_set = TOPO["b21_wiz_adj"] if b_wiz_intact else TOPO["r21_wiz_adj"]
        s0 = (dru_pos[0], dru_pos[1], cut_dru, cut_bard, cut_bg)
        dist: Dict[Tuple[int, int, int, int, int], int] = {s0: 0}
        pq: List[Tuple[int, Tuple[int, int, int, int, int]]] = [(0, s0)]
        while pq:
            d, st = heapq.heappop(pq)
            if d != dist[st]:
                continue
            x, y, fd, fb, fg = st
            if (x, y) in target_set:
                pre_move = d
                break
            for dx, dy in DIR_DELTAS:
                nx, ny = x + dx, y + dy
                if 1 <= nx < ps.w - 1 and 1 <= ny < ps.h - 1:
                    nfd, nfb, nfg = fd, fb, fg
                    if ps.obj[ny][nx] != "#" or (nx, ny) in r21_wiz:
                        c = 1
                    elif (nx, ny) in b21_dru and fd > 0:
                        c = 1
                        nfd = 0
                    elif (nx, ny) in b21_bard and fb > 0:
                        c = 1
                        nfb = 0
                    elif (nx, ny) in b21_bg and fg > 0:
                        c = 1
                        nfg = 0
                    else:
                        c = 2
                    nst = (nx, ny, nfd, nfb, nfg)
                    if d + c < dist.get(nst, 999):
                        dist[nst] = d + c
                        heapq.heappush(pq, (d + c, nst))

    wiz_post = 1 if (wiz_pos is not None and wiz_pos not in g21_all) else 0
    total = total_cuts + a_tax + pre_move + wiz_post
    return total, {
        "cut_dru": cut_dru,
        "cut_bard": cut_bard,
        "cut_bg": cut_bg,
        "cut_wiz": cut_wiz,
        "a_sw": a_tax,
        "pre_maze": pre_move,
        "wiz_post": wiz_post,
    }


def eval_naive_unpartitioned_iii21(ps: Part3Oracle) -> int:
    """Deliberately unsound unpartitioned 6-hero L1 sum (`must_fail` negative control)."""
    if type(ps) is not Part3Oracle:
        raise AletheiaError("INVALID_ORACLE_STATE", "ps must be Part3Oracle")
    if ps.check_win():
        return 0
    heroes, _ = ps.extract_heroes()
    goals = sorted(TOPO["g21_all"])
    return sum(min(abs(hx - gx) + abs(hy - gy) for gx, gy in goals) for hx, hy in heroes.values())


# =============================================================================
# Explicit Board-Derived Coupled Quotient Builders (Farkas Primal == Dual in Q)
# =============================================================================

def _chain_quotient(name: str, length: int, action: str) -> QuotientGraph:
    edges = tuple((i, i - 1, action) for i in range(length, 0, -1))
    return QuotientGraph(name=name, num_vertices=length + 1, start=length, goals=(0,), edges=edges)


def _cyclic_post_breach_switch_quotient(
    name: str,
    slots: Sequence[str],
    active: str,
    druid_slot: str,
    action: str,
) -> QuotientGraph:
    """Build the actual `k+1`-state cyclic hero switch automaton (`slot -> next_slot` on `'A'`,
    plus post-breach exit state `k` reached from `druid_slot` on `'A'`), directly from board heroes.
    """
    k = len(slots)
    start_idx = slots.index(active)
    druid_idx = slots.index(druid_slot)
    edges: List[Tuple[int, int, str]] = []
    for i in range(k):
        nxt = (i + 1) % k
        edges.append((i, nxt, action))
        if i == druid_idx:
            edges.append((i, k, action))
    return QuotientGraph(name=name, num_vertices=k + 1, start=start_idx, goals=(k,), edges=tuple(edges))


def _build_iii21_concrete_maze_quotient(ps: Part3Oracle, cut_bg: int) -> QuotientGraph:
    """Build the full-board `III-21` pre-release Druid maze quotient directly from `ps.obj`
    with states `(x, y, free_bg_rem)` over all interior cells plus wall-breach intermediates.
    """
    b21_dru = TOPO["b21_dru"]
    b21_bard = TOPO["b21_bard"]
    b21_bg = TOPO["b21_bg"]
    r21_wiz = TOPO["r21_wiz"]
    goals_xy = TOPO["b21_wiz_adj"]
    heroes, _ = ps.extract_heroes()
    dru_pos = heroes["6"]

    # Map every interior cell (x, y) x fg in {0, 1} to a vertex id
    vid: Dict[Tuple[int, int, int], int] = {}
    for y in range(1, ps.h - 1):
        for x in range(1, ps.w - 1):
            for fg in (0, 1):
                vid[(x, y, fg)] = len(vid)

    # Intermediate wall-breach vertex for each (nx, ny, nfg) when crossing a non-exempt '#' costs 2
    breach_vid: Dict[Tuple[int, int, int], int] = {}
    edges: List[Tuple[int, int, str]] = []
    goals: List[int] = []
    for (x, y, fg), u in list(vid.items()):
        if (x, y) in goals_xy:
            goals.append(u)
            continue
        for dx, dy in DIR_DELTAS:
            nx, ny = x + dx, y + dy
            if 1 <= nx < ps.w - 1 and 1 <= ny < ps.h - 1:
                is_wall = ps.obj[ny][nx] == "#"
                if (not is_wall) or ((nx, ny) in r21_wiz) or ((nx, ny) in b21_dru) or ((nx, ny) in b21_bard):
                    edges.append((u, vid[(nx, ny, fg)], "DRU_PRE_MAZE"))
                elif (nx, ny) in b21_bg and fg > 0:
                    edges.append((u, vid[(nx, ny, 0)], "DRU_PRE_MAZE"))
                else:
                    bkey = (nx, ny, fg)
                    bv = breach_vid.get(bkey)
                    if bv is None:
                        bv = len(vid) + len(breach_vid)
                        breach_vid[bkey] = bv
                        edges.append((bv, vid[(nx, ny, fg)], "DRU_PRE_MAZE"))
                    edges.append((u, bv, "D_W2C_OTHER"))

    return QuotientGraph(
        name="iii21_concrete_23x13_pre_release_druid_maze",
        num_vertices=len(vid) + len(breach_vid),
        start=vid[(dru_pos[0], dru_pos[1], cut_bg)],
        goals=tuple(sorted(goals)),
        edges=tuple(edges),
    )


def build_iii14_farkas_certificate() -> Dict[str, Any]:
    """Build board-derived coupled action-class Farkas LP certificate for `III-14` (`primal == dual == 24`)."""
    ps0 = Part3Oracle(FRONTIER_CATALOG["III-14"]["grid"])
    _, comp = eval_iii14_coupled(ps0)
    actions = ("D_W2C", "A_SW", "MOVE_BD")
    q_supply = _chain_quotient("iii14_perimeter_w2c_supply", comp["w2c"], "D_W2C")
    q_switch = _chain_quotient("iii14_active_switch_parity", comp["a_sw"], "A_SW")
    q_move = _chain_quotient("iii14_bard_conservation_9switch_tour", comp["bard_druid_move"], "MOVE_BD")
    weights = [
        {"D_W2C": Fraction(1), "A_SW": Fraction(0), "MOVE_BD": Fraction(0)},
        {"D_W2C": Fraction(0), "A_SW": Fraction(1), "MOVE_BD": Fraction(0)},
        {"D_W2C": Fraction(0), "A_SW": Fraction(0), "MOVE_BD": Fraction(1)},
    ]
    return solve_coupled_farkas_lp(
        instance_id="III-14_coupled_bard_conservation_farkas",
        action_classes=actions,
        quotients=(q_supply, q_switch, q_move),
        cost_partition=weights,
    )


def _require_active_slot(ps: Part3Oracle) -> Tuple[Dict[str, Tuple[int, int]], str]:
    heroes, active = ps.extract_heroes()
    if active is None:
        raise AletheiaError("MISSING_ACTIVE_HERO", "board missing active hero")
    return heroes, active


def require_pairwise_disjoint(sets: Sequence[Any]) -> None:
    for i in range(len(sets)):
        for j in range(i + 1, len(sets)):
            if sets[i] & sets[j]:
                raise AletheiaError("BARRIERS_NOT_DISJOINT", "barrier regions overlap")


def build_iii20_farkas_certificate() -> Dict[str, Any]:
    """Build board-derived coupled action-class Farkas LP certificate for `III-20` (`primal == dual == 9`)."""
    ps0 = Part3Oracle(FRONTIER_CATALOG["III-20"]["grid"])
    _, comp = eval_iii20_coupled(ps0)
    heroes, active = _require_active_slot(ps0)
    actions = ("D_W2C_L", "D_W2C_R", "A_SW", "M_OCC_MOVE")
    q_l = _chain_quotient("iii20_left_priest_cut", comp["cut_l"], "D_W2C_L")
    q_r = _chain_quotient("iii20_right_4goal_cut", comp["cut_r"], "D_W2C_R")
    q_a = _cyclic_post_breach_switch_quotient(
        "iii20_cyclic_5hero_post_breach_switch",
        sorted(heroes.keys()),
        active,
        "6",
        "A_SW",
    )
    q_m = _chain_quotient("iii20_wizard_invariant_occ_frontier", comp["occ_frontier"], "M_OCC_MOVE")
    weights = [
        {"D_W2C_L": Fraction(1), "D_W2C_R": Fraction(0), "A_SW": Fraction(0), "M_OCC_MOVE": Fraction(0)},
        {"D_W2C_L": Fraction(0), "D_W2C_R": Fraction(1), "A_SW": Fraction(0), "M_OCC_MOVE": Fraction(0)},
        {"D_W2C_L": Fraction(0), "D_W2C_R": Fraction(0), "A_SW": Fraction(1), "M_OCC_MOVE": Fraction(0)},
        {"D_W2C_L": Fraction(0), "D_W2C_R": Fraction(0), "A_SW": Fraction(0), "M_OCC_MOVE": Fraction(1)},
    ]
    return solve_coupled_farkas_lp(
        instance_id="III-20_coupled_barrier_occupancy_farkas",
        action_classes=actions,
        quotients=(q_l, q_r, q_a, q_m),
        cost_partition=weights,
    )


def build_iii21_farkas_certificate() -> Dict[str, Any]:
    """Build board-derived coupled action-class Farkas LP certificate for `III-21` (`primal == dual == 30`),
    including the full-board `23x13` pre-release Druid maze quotient and `7`-state cyclic switch automaton.
    """
    ps0 = Part3Oracle(FRONTIER_CATALOG["III-21"]["grid"])
    _, comp = eval_iii21_coupled(ps0)
    heroes, active = _require_active_slot(ps0)
    require_pairwise_disjoint((TOPO["b21_dru"], TOPO["b21_bard"], TOPO["b21_bg"], TOPO["r21_wiz"]))

    actions = (
        "D_W2C_DRU",
        "D_W2C_BARD",
        "D_W2C_BG",
        "D_W2C_WIZ",
        "A_SW",
        "DRU_PRE_MAZE",
        "D_W2C_OTHER",
        "WIZ_POST_GOAL",
    )
    q_dru = _chain_quotient("iii21_druid_alcove_cut", comp["cut_dru"], "D_W2C_DRU")
    q_bard = _chain_quotient("iii21_bard_chamber_cut", comp["cut_bard"], "D_W2C_BARD")
    q_bg = _chain_quotient("iii21_bottom_2goal_cut", comp["cut_bg"], "D_W2C_BG")
    q_wiz = _chain_quotient("iii21_wizard_2thick_alcove_cut", comp["cut_wiz"], "D_W2C_WIZ")
    q_a = _cyclic_post_breach_switch_quotient(
        "iii21_cyclic_6hero_post_breach_switch",
        sorted(heroes.keys()),
        active,
        "6",
        "A_SW",
    )
    q_maze = _build_iii21_concrete_maze_quotient(ps0, comp["cut_bg"])
    q_post = _chain_quotient("iii21_post_release_wizard_goal_step", comp["wiz_post"], "WIZ_POST_GOAL")

    def _w(owned: Sequence[str]) -> Dict[str, Fraction]:
        oset = set(owned)
        return {a: (Fraction(1) if a in oset else Fraction(0)) for a in actions}

    quotients = (q_dru, q_bard, q_bg, q_wiz, q_a, q_maze, q_post)
    weights = [
        _w(("D_W2C_DRU",)),
        _w(("D_W2C_BARD",)),
        _w(("D_W2C_BG",)),
        _w(("D_W2C_WIZ",)),
        _w(("A_SW",)),
        _w(("DRU_PRE_MAZE", "D_W2C_OTHER")),
        _w(("WIZ_POST_GOAL",)),
    ]
    return solve_coupled_farkas_lp(
        instance_id="III-21_coupled_4barrier_maze_farkas",
        action_classes=actions,
        quotients=quotients,
        cost_partition=weights,
    )


def build_fractional_shared_action_certificate() -> Dict[str, Any]:
    """Build a strictly fractional Q\\Z cost-partitioned coupled Farkas LP witness
    (`h_1 = 5/3`, `h_2 = 7/3`, exact strong duality `5/3 + 7/3 == 4 == lambda(SHARED=2, PRIV_1=1, PRIV_2=1)`).
    """
    actions = ("SHARED", "PRIV_1", "PRIV_2")
    q1 = QuotientGraph(
        name="coupled_bard_agent1_shared_carry",
        num_vertices=4,
        start=3,
        goals=(0,),
        edges=((3, 2, "SHARED"), (2, 1, "SHARED"), (1, 0, "PRIV_1")),
    )
    q2 = QuotientGraph(
        name="coupled_bard_agent2_shared_carry",
        num_vertices=4,
        start=3,
        goals=(0,),
        edges=((3, 2, "SHARED"), (2, 1, "SHARED"), (1, 0, "PRIV_2")),
    )
    weights = [
        {"SHARED": Fraction(1, 3), "PRIV_1": Fraction(1), "PRIV_2": Fraction(0)},
        {"SHARED": Fraction(2, 3), "PRIV_1": Fraction(0), "PRIV_2": Fraction(1)},
    ]
    return solve_coupled_farkas_lp(
        instance_id="FRAC_coupled_shared_action_partition",
        action_classes=actions,
        quotients=(q1, q2),
        cost_partition=weights,
    )


# =============================================================================
# Non-Separable Multi-Entity Deadlock & Coupling Obstruction Witnesses
# =============================================================================

def _build_concrete_subproblem_graph(
    grid: Sequence[str],
    *,
    max_states: int = 2000,
) -> Tuple[int, int, List[int], List[Tuple[int, int]]]:
    """Explore exact concrete reachable graph of a Part III subproblem under `{U,D,L,R,A}`."""
    p0 = Part3Oracle(grid)
    sig0 = p0.signature()
    idx_of: Dict[Tuple[Any, ...], int] = {sig0: 0}
    states: List[Part3Oracle] = [p0]
    goals: List[int] = [0] if p0.check_win() else []
    edges: Set[Tuple[int, int]] = set()
    q: deque[int] = deque([0])
    while q:
        u = q.popleft()
        st = states[u]
        if st.check_win():
            continue
        for key in ("U", "D", "L", "R", "A"):
            nxt = st.clone()
            alive, won = nxt.step(key)
            if not alive:
                continue
            sig = nxt.signature()
            v = idx_of.get(sig)
            if v is None:
                if len(states) >= max_states:
                    raise AletheiaError("SUBPROBLEM_STATE_CAP", "subproblem exceeded state cap")
                v = len(states)
                idx_of[sig] = v
                states.append(nxt)
                if won:
                    goals.append(v)
                q.append(v)
            if v != u:
                edges.add((u, v))
    return len(states), 0, sorted(goals), sorted(edges)


def _concrete_bfs_shortest_win(
    grid: Sequence[str],
    *,
    max_states: int = 3000,
) -> Tuple[int, str]:
    """Exact unweighted BFS returning `(min_steps, witness_route)` for a solvable Part III slice."""
    p0 = Part3Oracle(grid)
    if p0.check_win():
        return 0, ""
    visited: Set[Tuple[Any, ...]] = {p0.signature()}
    q: deque[Tuple[Part3Oracle, str]] = deque([(p0, "")])
    while q:
        st, route = q.popleft()
        for key in ("U", "D", "L", "R", "A"):
            nxt = st.clone()
            alive, won = nxt.step(key)
            if not alive:
                continue
            nroute = route + key
            if won:
                return len(nroute), nroute
            sig = nxt.signature()
            if sig not in visited:
                if len(visited) >= max_states:
                    raise AletheiaError("BFS_STATE_CAP", "BFS exceeded state cap")
                visited.add(sig)
                q.append((nxt, nroute))
    raise AletheiaError("SLICE_UNSOLVABLE", "concrete slice has no winning path")


def build_deadlock_and_coupling_witnesses() -> Dict[str, Any]:
    """Construct and certify 3 concrete non-separable multi-entity obstruction witnesses
    grounded directly in `III-14`, `III-20`, and `III-21`.
    """
    # 1. III-20 Center 4-Goblin Ring Escort Deadlock (exact 7x5 center slice of III-20):
    #    Without Priest, Fighter F cannot reach goal G surrounded by 4 Goblins (Farkas-infeasible, 5-state cut!).
    #    In the 1-entity Goblin-blind projection, F reaches G in 3 steps.
    #    Coupling Priest P restores exact feasibility in 9 steps (shielded Goblin push -> mutual destruction!).
    iii20_no_priest_grid = (
        "#######",
        "#...O.#",
        "#F.OGO#",
        "#...O.#",
        "#######",
    )
    n20, s20, g20, e20 = _build_concrete_subproblem_graph(iii20_no_priest_grid)
    iii20_1ent_grid = (
        "#######",
        "#.....#",
        "#F..G.#",
        "#.....#",
        "#######",
    )
    n20_1, s20_1, g20_1, e20_1 = _build_concrete_subproblem_graph(iii20_1ent_grid)
    dl_iii20 = certify_farkas_deadlock(
        witness_id="III-20_goblin_ring_no_priest_deadlock",
        num_vertices=n20,
        start=s20,
        goals=g20,
        edges=e20,
        one_entity_projections=[{
            "name": "fighter_goblin_blind_1entity",
            "num_vertices": n20_1,
            "start": s20_1,
            "goals": g20_1,
            "edges": [[u, v] for u, v in e20_1],
        }],
    )
    iii20_with_priest_grid = (
        "#######",
        "#4..O.#",
        "#F.OGO#",
        "#G..O.#",
        "#######",
    )
    dist20_with_priest, route20_with_priest = _concrete_bfs_shortest_win(iii20_with_priest_grid)

    # 2. III-21 Bottom-Left Sealed Wizard Alcove Deadlock (exact 9x5 slice of III-21 without Druid):
    #    Wizard W is sealed behind the exact 2-thick '#' barrier while goal G is outside;
    #    1-entity wall-blind projection reaches G in finite steps, whereas coupled alcove is Farkas-infeasible!
    iii21_alcove_grid = (
        "#########",
        "#...#...#",
        "#####...#",
        "#.W.###G#",
        "#########",
    )
    n21, s21, g21, e21 = _build_concrete_subproblem_graph(iii21_alcove_grid)
    iii21_1ent_grid = (
        "#########",
        "#.......#",
        "#.......#",
        "#.W....G#",
        "#########",
    )
    n21_1, s21_1, g21_1, e21_1 = _build_concrete_subproblem_graph(iii21_1ent_grid)
    dl_iii21 = certify_farkas_deadlock(
        witness_id="III-21_wizard_sealed_alcove_deadlock",
        num_vertices=n21,
        start=s21,
        goals=g21,
        edges=e21,
        one_entity_projections=[{
            "name": "wizard_wall_blind_1entity",
            "num_vertices": n21_1,
            "start": s21_1,
            "goals": g21_1,
            "edges": [[u, v] for u, v in e21_1],
        }],
    )

    # 3. III-14 Coupled 2-Crate Bard 5x5 Rigid-Aura Blow-Off Deadlock (exact 7x7 chamber slice without Druid):
    #    Each 1-crate projection reaches its switch & opens G in exactly 8 steps, yet the coupled 2-crate state
    #    is 100% Farkas-infeasible (43-state closed cut-set disjoint from goals)!
    iii14_rigid_2crate_grid = (
        "#######",
        "#.#####",
        "#..}###",
        "#B**]G#",
        "#..}###",
        "#.#####",
        "#######",
    )
    n14, s14, g14, e14 = _build_concrete_subproblem_graph(iii14_rigid_2crate_grid)
    iii14_1c_a_grid = (
        "#######",
        "#.#####",
        "#..}###",
        "#B*.]G#",
        "#...###",
        "#.#####",
        "#######",
    )
    n14_a, s14_a, g14_a, e14_a = _build_concrete_subproblem_graph(iii14_1c_a_grid)
    iii14_1c_b_grid = (
        "#######",
        "#.#####",
        "#...###",
        "#B.*]G#",
        "#..}###",
        "#.#####",
        "#######",
    )
    n14_b, s14_b, g14_b, e14_b = _build_concrete_subproblem_graph(iii14_1c_b_grid)
    dl_iii14 = certify_farkas_deadlock(
        witness_id="III-14_bard_5x5_rigid_2crate_blowoff_deadlock",
        num_vertices=n14,
        start=s14,
        goals=g14,
        edges=e14,
        one_entity_projections=[
            {
                "name": "crate1_to_top_switch_1box",
                "num_vertices": n14_a,
                "start": s14_a,
                "goals": g14_a,
                "edges": [[u, v] for u, v in e14_a],
            },
            {
                "name": "crate2_to_bot_switch_1box",
                "num_vertices": n14_b,
                "start": s14_b,
                "goals": g14_b,
                "edges": [[u, v] for u, v in e14_b],
            },
        ],
    )

    return {
        "iii14_bard_2crate_deadlock": dl_iii14,
        "iii20_goblin_ring_deadlock": dl_iii20,
        "iii20_priest_escort_restoration_distance": dist20_with_priest,
        "iii20_priest_escort_witness_route": route20_with_priest,
        "iii21_wizard_alcove_deadlock": dl_iii21,
    }


# =============================================================================
# Concrete Route & Off-Route Bellman 1-Step Consistency Verifier
# =============================================================================

def verify_concrete_room_bound(
    room_id: str,
    eval_fn: Callable[[Part3Oracle], Tuple[int, Dict[str, int]]],
    *,
    random_walks: int = 16,
    walk_len: int = 16,
    seed: int = 20261122,
) -> Dict[str, Any]:
    """Verify exact route replay, admissibility (`h(s) <= remaining`), and 1-step Bellman
    consistency (`h(s) - h(s') <= 1`) across the entire catalog route and off-route random walks.
    """
    if type(room_id) is not str or room_id not in FRONTIER_CATALOG:
        raise AletheiaError("UNKNOWN_ROOM", "room_id must be in FRONTIER_CATALOG")
    if not callable(eval_fn):
        raise AletheiaError("INVALID_EVAL_FN", "eval_fn must be callable")
    spec = FRONTIER_CATALOG[room_id]
    grid = spec["grid"]
    route: str = spec["reference_route"]
    ps = Part3Oracle(grid)
    h0, comp0 = eval_fn(ps)

    route_states: List[Tuple[Part3Oracle, int]] = [(ps.clone(), h0)]
    max_drop = 0
    admissibility_violations = 0
    hu = h0
    for t, key in enumerate(route):
        if hu > len(route) - t:
            admissibility_violations += 1
        alive, _ = ps.step(key)
        if not alive:
            raise AletheiaError("ROUTE_DIED", f"{room_id} route died at step {t}")
        hv, _ = eval_fn(ps)
        if hu - hv > max_drop:
            max_drop = hu - hv
        hu = hv
        route_states.append((ps.clone(), hu))

    won = ps.check_win()
    h_end = hu
    if not won or h_end != 0:
        raise AletheiaError("ROUTE_NOT_WIN", f"{room_id} reference route failed terminal check")

    # Seeded random off-route transitions
    rng = random.Random(seed)
    n_goals = sum(1 for y in range(ps.h) for x in range(ps.w) if ps.floor[y][x] == "G")
    offroute_edges = 0
    for _ in range(random_walks):
        base_st, hu = rng.choice(route_states)
        cur = base_st.clone()
        for _step in range(walk_len):
            if cur.check_win():
                break
            key = rng.choice("UDLRA")
            nxt = cur.clone()
            alive, _ = nxt.step(key)
            if not alive:
                continue
            n_heroes = sum(1 for y in range(nxt.h) for x in range(nxt.w) if nxt.is_hero(nxt.obj[y][x]))
            if n_heroes < n_goals:
                continue
            hv, _ = eval_fn(nxt)
            offroute_edges += 1
            if hu - hv > max_drop:
                max_drop = hu - hv
            cur = nxt
            hu = hv

    return {
        "room_id": room_id,
        "root_coupled_bound": h0,
        "root_components": comp0,
        "prior_1box_bounds": spec["prior_1box_bounds"],
        "proven_floor": spec["proven_floor"],
        "shortest_known": spec["shortest_known"],
        "residual_gap_to_floor": spec["proven_floor"] - h0,
        "residual_gap_to_known": spec["shortest_known"] - h0,
        "route_length": len(route),
        "route_exact_win": won,
        "terminal_h": h_end,
        "route_edges_checked": len(route),
        "offroute_edges_checked": offroute_edges,
        "total_edges_checked": len(route) + offroute_edges,
        "admissibility_violations": admissibility_violations,
        "max_1step_drop": max_drop,
        "bellman_1step_consistent": (max_drop <= 1) and (admissibility_violations == 0) and (h_end == 0),
    }


def verify_naive_must_fail_control() -> Dict[str, Any]:
    """Negative Law-2b `must_fail` control: prove naive unpartitioned 6-hero L1 sum on `III-21`
    violates 1-step Bellman consistency under Bard multi-hero carries and Wizard ray swaps.
    """
    spec = FRONTIER_CATALOG["III-21"]
    ps = Part3Oracle(spec["grid"])
    route: str = spec["reference_route"]
    h0 = eval_naive_unpartitioned_iii21(ps)
    violations: List[Dict[str, Any]] = []
    max_drop = 0
    for t, key in enumerate(route):
        act = ps.find_active()
        ah = act[2] if act is not None else "?"
        hu = eval_naive_unpartitioned_iii21(ps)
        ps.step(key)
        hv = eval_naive_unpartitioned_iii21(ps)
        drop = hu - hv
        if drop > max_drop:
            max_drop = drop
        if drop > 1:
            violations.append({"step": t, "hero": ah, "key": key, "h_before": hu, "h_after": hv, "drop": drop})
    return {
        "control_id": "III-21_naive_unpartitioned_l1_sum",
        "root_naive_sum": h0,
        "bellman_violation_count": len(violations),
        "max_1step_drop": max_drop,
        "first_3_violations": violations[:3],
        "correctly_falsified": (len(violations) > 0) and (max_drop > 1),
    }
