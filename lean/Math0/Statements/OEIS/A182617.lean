/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A182617: toothpicks in the toothpick spiral around `n` hexagonal cells

Source: https://oeis.org/A182617, Vincenzo Librandi, Sep 20 2017 (FORMULA section of the entry
by Omar E. Pol, Dec 13 2010). Verbatim:
> Conjecture: a(n) = 2*n + ceiling(sqrt(12*n - 3)), for n > 0. - _Vincenzo Librandi_, Sep 20 2017

The sequence (offset `0`) is "Number of toothpicks in a toothpick spiral around n cells on
hexagonal net." The comments explain: a hexagonal cell is "ON" when all 6 of its vertices are
covered by toothpicks; the toothpicks form a self-avoiding walk on the edges of the net that
first goes round a central hexagon (5 edges) and then winds round the successive rings of
hexagons; the count of toothpicks is read off each time one more hexagon becomes ON. The
examples give `a(0) = 0`, `a(1) = 5`, `a(2) = 9`, `a(3) = 12`.

## Encoding

* **The net.** Vertices of the hexagonal net are `Pt = ℤ × ℤ` in brick-wall coordinates: `(x, y)`
  is joined to `(x ± 1, y)`, and to `(x, y + 1)` if `x + y` is even, to `(x, y - 1)` if `x + y` is
  odd. This is a planar straight-line drawing of the hexagonal net in which every face is a
  `2 × 1` brick. The cells are these bricks: for every `c = (x, y)` with `x + y` even, the cell
  `c` has the six vertices `(x, y), (x+1, y), (x+2, y), (x, y+1), (x+1, y+1), (x+2, y+1)`
  (`cellVerts`).
* **The spiral.** `nbrs v` lists the neighbours of `v` counterclockwise; arriving at `v` from the
  neighbour `p`, the left turn leads to the neighbour two places after `p` in this cyclic order,
  the right turn to the one just after `p` (`turns`). The walk starts at `(0, 0)` with its first
  toothpick going to `(1, 0)`; afterwards it turns left whenever the vertex there has not been
  visited yet, and otherwise turns right (if both are visited it would stop, which never happens:
  the walk winds outward forever). Thus it goes round the central hexagon with 5 toothpicks,
  then steps out and goes once round the next ring until self-avoidance forces it outward, and so
  on, exactly as described in the comments. `walk t` is the list of vertices covered by the first
  `t` toothpicks (most recent first). Since the net is vertex-transitive under rotations, the
  starting vertex and direction do not matter, and the mirror-image spiral gives the same counts.
* **Cells ON and `a(n)`.** `onCells w` is the set of cells all six of whose vertices are covered
  (every such cell has its corner `c` among the covered vertices), and `onCount t` is the number
  of ON cells after `t` toothpicks. `a n` is the number of toothpicks at the first moment at which
  `n` cells are ON, i.e. the least `t` with `n ≤ onCount t`; so `a 0 = 0`. To keep `a` computable
  the search runs over `t ≤ 6 * n` and returns `6 * n + 1` if no such `t` is found. The cap is
  harmless: `a_eq_iff_isLeast` shows `a n` is the least such `t` whenever that is at most `6n`,
  and `statement_iff` restates the conjecture with no cap at all (the conjectured value is at
  most `6n` for `n ≥ 1`).
* **Data.** `a_data` checks all 40 listed terms `a(0), …, a(39)` in the kernel.
* **The conjecture** is stated for `n > 0`, as in the entry. `ceiling(sqrt(12*n - 3))` is
  `⌈Real.sqrt (12 * n - 3)⌉₊`; for `n ≥ 1` the radicand is positive, so this is the usual ceiling
  of the real square root.
-/

namespace Math0.Statements.A182617

/-- Vertices of the hexagonal net, in brick-wall coordinates. -/
abbrev Pt := ℤ × ℤ

/-- The three neighbours of a vertex of the hexagonal net, listed counterclockwise: for `x + y`
even they are right, up, left; for `x + y` odd they are right, left, down. -/
def nbrs (v : Pt) : Pt × Pt × Pt :=
  if (v.1 + v.2) % 2 = 0 then ((v.1 + 1, v.2), (v.1, v.2 + 1), (v.1 - 1, v.2))
  else ((v.1 + 1, v.2), (v.1 - 1, v.2), (v.1, v.2 - 1))

/-- `turns p v = (l, r)`: arriving at `v` from its neighbour `p`, the left turn leads to `l` and
the right turn leads to `r`. -/
def turns (p v : Pt) : Pt × Pt :=
  let (n0, n1, n2) := nbrs v
  if p = n0 then (n2, n1) else if p = n1 then (n0, n2) else (n1, n0)

/-- One more toothpick of the spiral. The list `w` holds the covered vertices, most recent first;
the walk turns left if that vertex is still uncovered, and otherwise right (it would stop if both
were covered). -/
def step : List Pt → List Pt
  | v :: p :: rest =>
    let w := v :: p :: rest
    let (l, r) := turns p v
    if l ∉ w then l :: w else if r ∉ w then r :: w else w
  | w => w

/-- The vertices covered by the first `t` toothpicks of the spiral (most recent first). It starts
at `(0, 0)`, and the first toothpick joins `(0, 0)` to `(1, 0)`. -/
def walk : ℕ → List Pt
  | 0 => [(0, 0)]
  | t + 1 => step^[t] [(1, 0), (0, 0)]

/-- The six vertices of the hexagonal cell with lower-left corner `c` (for `c.1 + c.2` even). -/
def cellVerts (c : Pt) : List Pt :=
  [(c.1, c.2), (c.1 + 1, c.2), (c.1 + 2, c.2),
    (c.1, c.2 + 1), (c.1 + 1, c.2 + 1), (c.1 + 2, c.2 + 1)]

/-- The cells that are "ON" once the vertices in `w` are covered: the cells all six of whose
vertices are covered, each represented by its lower-left corner. -/
def onCells (w : List Pt) : Finset Pt :=
  w.toFinset.filter (fun c => (c.1 + c.2) % 2 = 0 ∧ ∀ u ∈ cellVerts c, u ∈ w)

/-- The number of ON cells after `t` toothpicks of the spiral. -/
def onCount (t : ℕ) : ℕ := (onCells (walk t)).card

/-- A182617: the number of toothpicks in the toothpick spiral at the first moment when it
surrounds `n` cells (has `n` cells ON), i.e. the least `t` with `n ≤ onCount t`. The search is
capped at `6 * n` (returning `6 * n + 1` beyond it); see `a_eq_iff_isLeast`. -/
def a (n : ℕ) : ℕ :=
  ((List.range (6 * n + 1)).find? (fun t => n ≤ onCount t)).getD (6 * n + 1)

/-- The definition reproduces all 40 terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 40).map (fun i => a (i + 0)) =
    [0, 5, 9, 12, 15, 18, 21, 23, 26, 29, 31, 34, 36, 39, 41, 44, 46, 49, 51, 53,
      56, 58, 61, 63, 65, 68, 70, 72, 75, 77, 79, 82, 84, 86, 89, 91, 93, 95, 98, 100] := by
  decide +kernel

/-- The cap in the definition of `a` does not matter: for `t ≤ 6n`, `a n = t` exactly when `t` is
the least number of toothpicks at which `n` cells are ON. -/
theorem a_eq_iff_isLeast {n t : ℕ} (ht : t ≤ 6 * n) :
    a n = t ↔ IsLeast {s | n ≤ onCount s} t := by
  constructor
  · intro h
    unfold a at h
    cases hf : (List.range (6 * n + 1)).find? (fun t => n ≤ onCount t) with
    | none => rw [hf] at h; simp at h; omega
    | some i =>
      rw [hf] at h
      simp only [Option.getD_some] at h
      subst h
      rw [List.find?_range_eq_some] at hf
      obtain ⟨h1, -, h3⟩ := hf
      refine ⟨by simpa using h1, fun s hs => ?_⟩
      by_contra hlt
      have := h3 s (by omega)
      simp only [Set.mem_ofPred_eq] at hs
      simp [hs] at this
  · rintro ⟨h1, h2⟩
    have hf : (List.range (6 * n + 1)).find? (fun t => n ≤ onCount t) = some t := by
      rw [List.find?_range_eq_some]
      refine ⟨by simpa using h1, by simp; omega, fun j hj => ?_⟩
      have : ¬ n ≤ onCount j := fun hj' => absurd (h2 hj') (by omega)
      simpa using this
    unfold a
    rw [hf]
    rfl

/-- Librandi's conjecture: for `n > 0`, `a(n) = 2n + ⌈√(12n - 3)⌉`. -/
def statement : Prop :=
  ∀ n : ℕ, 0 < n → a n = 2 * n + ⌈Real.sqrt (12 * (n : ℝ) - 3)⌉₊

/-- The conjecture says exactly that, for every `n > 0`, the least number of toothpicks of the
spiral at which `n` cells are ON is `2n + ⌈√(12n - 3)⌉` (no cap on the search). -/
theorem statement_iff : statement ↔
    ∀ n : ℕ, 0 < n →
      IsLeast {t | n ≤ onCount t} (2 * n + ⌈Real.sqrt (12 * (n : ℝ) - 3)⌉₊) := by
  have hb : ∀ n : ℕ, 0 < n → 2 * n + ⌈Real.sqrt (12 * (n : ℝ) - 3)⌉₊ ≤ 6 * n := by
    intro n hn
    have hc : ⌈Real.sqrt (12 * (n : ℝ) - 3)⌉₊ ≤ 4 * n := by
      rw [Nat.ceil_le, Real.sqrt_le_left (by positivity)]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast
      nlinarith
    omega
  exact forall₂_congr fun n hn => a_eq_iff_isLeast (hb n hn)

end Math0.Statements.A182617
