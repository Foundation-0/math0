/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A121750: columns of even length in deco polyominoes (Mathar's recurrence)

Source: https://oeis.org/A121750, _R. J. Mathar_, Jul 26 2022 (FORMULA section). Verbatim:
> Conjecture D-finite with recurrence a(n) +(-n-2)*a(n-1) +(-n^2+4*n-2)*a(n-2)
> +(n^3-3*n^2-4*n+11)*a(n-3) -(n-1)*(n^2-11*n+26)*a(n-4) +(-n^3+5*n^2+7*n-43)*a(n-5)
> +(n-3)*(n-5)^2*a(n-6)=0. - _R. J. Mathar_, Jul 26 2022

The entry (Emeric Deutsch, Aug 20 2006, offset `1`) is "Number of columns of even length in all
deco polyominoes of height n. A deco polyomino is a directed column-convex polyomino in which the
height, measured along the diagonal, is attained only in the last column."

## Encoding

* *Directed column-convex polyominoes as column lists.* Cells are `(x, y)`, `x` the column.
  A polyomino is counted up to translation. In a directed column-convex polyomino every column is
  a vertical segment of cells, and every cell is reached from the source cell by a path of north
  and east unit steps inside the polyomino; the source is the bottom cell of the first column.
  Translating the source to `(0, 0)`, the polyomino is determined by its list of columns
  `[(b₀, t₀), …, (b_k, t_k)]`: column `i` is the set of cells `(i, y)` with `bᵢ ≤ y ≤ tᵢ`. The
  constraints are `bᵢ ≤ tᵢ` (nonempty column), `b₀ = 0` (source at the origin), and the
  directedness condition `bᵢ ≤ bᵢ₊₁ ≤ tᵢ`: the bottom cell `(i+1, bᵢ₊₁)` of a column can only be
  entered from the west, so `(i, bᵢ₊₁)` must be a cell of column `i`; conversely, under these
  conditions every cell is reached by climbing column `0`, stepping east, climbing, and so on.
  Distinct lists give distinct polyominoes. (`IsDeco` writes these conditions with list indices.)
* *Height along the diagonal.* The height measured along the diagonal is the number of diagonals
  `x + y = const` met by the polyomino, `max (x + y) - min (x + y) + 1`. The minimum is `0`, at
  the source, and the largest value of `x + y` in column `i` is `i + tᵢ` (its top cell). So the
  height is `n` iff `i + tᵢ + 1 ≤ n` for all `i`, with equality for some `i`; a column attains the
  height iff `i + tᵢ + 1 = n`, and "attained only in the last column" says that this forces
  `i = k`. There is no deco polyomino of height `0` (`isDeco_zero`), so `a 0 = 0` (not a term).
* *The sequence.* A column `(b, t)` has length `t - b + 1`. `a n` is the sum, over the deco
  polyominoes of height `n`, of their number of columns of even length (`evenCols`). The deco
  polyominoes of height `n` are enumerated by the list `decos n` (built column by column by
  `tails`), and `mem_decos`, `nodup_decos` prove that `decos n` lists exactly the column lists
  satisfying `IsDeco n`, each once. So `a n = Σ_{P deco of height n} evenCols P`, literally the
  OEIS definition.
  For example, the deco polyominoes of height `2` are the vertical domino `[(0, 1)]` (one column
  of even length) and the horizontal domino `[(0, 0), (1, 0)]` (none), so `a 2 = 1`, as in the
  entry's example. The translation from cell sets to column lists above is the standard one and is
  argued here in prose only; the checks below test the encoding against the OEIS data.
* *Checks.* Directly from the enumeration (kernel): `a 1, …, a 6` (`a_data_direct`), the numbers
  of deco polyominoes of heights `1, …, 6` are `1!, …, 6!` (`decos_length_data_direct`; these
  are the row sums of A121748, a well-known property of deco polyominoes), and rows `1..6` of the
  triangle A121748 ("number of deco polyominoes of height n having k columns of even length"),
  `triangle_data`. For speed,
  `tab` computes the pair (number of completions, total number of even columns) for each state of
  the column-by-column construction by dynamic programming; `tab_getD` proves it correct for all
  arguments, so `a = aDP` (`a_eq_aDP`), and `a_data` checks all 19 listed terms `a 1, …, a 19`;
  `decos_length_data` checks that there are `n!` deco polyominoes of height `n` for
  `n = 1, …, 19`.
* *The conjecture.* No range of `n` is given. The recurrence involves `a(n-6)`, and the sequence
  starts at `a(1)` (offset `1`), so it is stated for every `n ≥ 7`, in `ℤ`, with no other
  hypothesis. `recurrence_data` checks the transcription on the listed terms (`7 ≤ n ≤ 19`).
-/

namespace Math0.Statements.A121750

/-! ### Deco polyominoes -/

/-- `IsDeco n cs`: the column list `cs = [(b₀, t₀), …, (b_k, t_k)]` describes a deco polyomino of
height `n`, with source cell `(0, 0)`; column `i` consists of the cells `(i, y)`,
`bᵢ ≤ y ≤ tᵢ`. -/
def IsDeco (n : ℕ) (cs : List (ℕ × ℕ)) : Prop :=
  -- at least one column, and every column is a nonempty vertical segment
  cs ≠ [] ∧
  (∀ c ∈ cs, c.1 ≤ c.2) ∧
  -- the source `(0, 0)` is the bottom cell of the first column
  (∀ c ∈ cs.head?, c.1 = 0) ∧
  -- directed: the bottom cell of column `i + 1` has its west neighbour in column `i`
  (∀ i (h : i + 1 < cs.length), cs[i].1 ≤ cs[i + 1].1 ∧ cs[i + 1].1 ≤ cs[i].2) ∧
  -- height `n` along the diagonal: `max (x + y) + 1 = n` over the cells (`min (x + y) = 0`)
  (∀ i (h : i < cs.length), i + cs[i].2 + 1 ≤ n) ∧
  (∃ i, ∃ h : i < cs.length, i + cs[i].2 + 1 = n) ∧
  -- the height is attained only in the last column
  (∀ i (h : i < cs.length), i + cs[i].2 + 1 = n → i + 1 = cs.length)

/-- `tails r b`: the column lists `[(b, t₀), (b₁, t₁), …]` whose first column has bottom `b`,
with nonempty columns and the directedness condition, such that `i + tᵢ ≤ r` for every column
`i`, with equality exactly for the last column (`mem_tails`). The first column `(b, t)` is either
the last one (`t = r`), or `b ≤ t < r` and the remaining columns form a list in `tails (r - 1) b'`
with `b ≤ b' ≤ t`. -/
def tails : ℕ → ℕ → List (List (ℕ × ℕ))
  | 0, b => if b = 0 then [[(b, 0)]] else []
  | r + 1, b => (if b ≤ r + 1 then [[(b, r + 1)]] else []) ++
      (List.range' b (r + 1 - b)).flatMap fun t =>
        ((List.range' b (t + 1 - b)).flatMap (tails r)).map ((b, t) :: ·)

/-- All deco polyominoes of height `n` (as column lists), each listed once (`mem_decos`,
`nodup_decos`). -/
def decos : ℕ → List (List (ℕ × ℕ))
  | 0 => []
  | n + 1 => tails n 0

/-- The number of columns of even length (`t - b + 1`) of a polyomino. -/
def evenCols (cs : List (ℕ × ℕ)) : ℕ :=
  cs.countP fun c => (c.2 + 1 - c.1) % 2 == 0

/-- A121750: the number of columns of even length in all deco polyominoes of height `n`. -/
def a (n : ℕ) : ℕ := ((decos n).map evenCols).sum

/-- The definition, evaluated directly by enumerating the polyominoes, reproduces the first 6
listed terms (kernel-checked). All 19 listed terms are checked in `a_data` below. -/
theorem a_data_direct : (List.range 6).map (fun i => a (i + 1)) =
    [0, 1, 5, 26, 184, 1338] := by
  decide +kernel

/-- There are `n!` deco polyominoes of height `n` (the row sums of A121748), `n = 1, …, 6`,
counted directly. -/
theorem decos_length_data_direct : (List.range 6).map (fun i => (decos (i + 1)).length) =
    [1, 2, 6, 24, 120, 720] := by
  decide +kernel

/-- Rows `1..6` of A121748: the number of deco polyominoes of height `n` with `k` columns of
even length, `0 ≤ k < n`, counted directly. -/
theorem triangle_data : (List.range 6).map (fun i =>
      (List.range (i + 1)).map fun k => ((decos (i + 1)).filter fun P => evenCols P == k).length) =
    [[1], [1, 1], [2, 3, 1], [6, 11, 6, 1], [16, 44, 42, 16, 2], [66, 209, 254, 147, 40, 4]] := by
  decide +kernel

/-! ### `decos n` lists exactly the deco polyominoes of height `n`, each once -/

/-- The conditions satisfied by the members of `tails r b`. -/
def IsTail (r b : ℕ) (cs : List (ℕ × ℕ)) : Prop :=
  cs ≠ [] ∧
  (∀ c ∈ cs, c.1 ≤ c.2) ∧
  (∀ c ∈ cs.head?, c.1 = b) ∧
  (∀ i (h : i + 1 < cs.length), cs[i].1 ≤ cs[i + 1].1 ∧ cs[i + 1].1 ≤ cs[i].2) ∧
  (∀ i (h : i < cs.length), i + cs[i].2 ≤ r) ∧
  (∀ i (h : i < cs.length), i + cs[i].2 = r ↔ i + 1 = cs.length)

theorem isTail_zero (b : ℕ) (cs : List (ℕ × ℕ)) :
    IsTail 0 b cs ↔ b = 0 ∧ cs = [(b, 0)] := by
  constructor
  · rintro ⟨hne, hle, hhd, -, hdiag, hlast⟩
    rcases cs with _ | ⟨c, l⟩
    · exact absurd rfl hne
    · have h0 := hdiag 0 (by simp)
      have h1 := (hlast 0 (by simp)).1 (by simp at h0 ⊢; omega)
      have hb := hhd c (by simp)
      have hc := hle c (by simp)
      simp at h0 h1
      obtain ⟨c1, c2⟩ := c
      simp at h0 hb hc
      subst h1
      refine ⟨by omega, ?_⟩
      simp only [List.cons.injEq, Prod.mk.injEq, and_true]
      omega
  · rintro ⟨rfl, rfl⟩
    refine ⟨by simp, by simp, by simp, ?_, ?_, ?_⟩
    · intro i hi; simp at hi
    · intro i hi; simp at hi; subst hi; simp
    · intro i hi; simp at hi; subst hi; simp

theorem isTail_cons_succ (r b : ℕ) (c : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    IsTail (r + 1) b (c :: l) ↔ c.1 = b ∧ c.1 ≤ c.2 ∧
      ((l = [] ∧ c.2 = r + 1) ∨ (c.2 < r + 1 ∧ ∃ b', c.1 ≤ b' ∧ b' ≤ c.2 ∧ IsTail r b' l)) := by
  constructor
  · rintro ⟨-, hle, hhd, hdir, hdiag, hlast⟩
    have hb : c.1 = b := hhd c (by simp)
    have hc : c.1 ≤ c.2 := hle c (by simp)
    refine ⟨hb, hc, ?_⟩
    rcases l with _ | ⟨d, l⟩
    · left
      have := (hlast 0 (by simp)).2 (by simp)
      simpa using this
    · right
      have h0 := hdiag 0 (by simp)
      have h0' := hlast 0 (by simp)
      have hd := hdir 0 (by simp)
      simp at h0 h0' hd
      refine ⟨by omega, d.1, hd.1, hd.2, ?_⟩
      refine ⟨by simp, fun x hx => hle x (by simp [hx]), by simp, ?_, ?_, ?_⟩
      · intro i hi
        have := hdir (i + 1) (by simp at hi ⊢; omega)
        simpa using this
      · intro i hi
        have := hdiag (i + 1) (by simp at hi ⊢; omega)
        simp at this ⊢; omega
      · intro i hi
        have := hlast (i + 1) (by simp at hi ⊢; omega)
        simp at this ⊢; omega
  · rintro ⟨hb, hc, ⟨rfl, h2⟩ | ⟨hlt, b', h1, h2, hne, hle, hhd, hdir, hdiag, hlast⟩⟩
    · refine ⟨by simp, by simpa using hc, by simpa using hb, ?_, ?_, ?_⟩
      · intro i hi; simp at hi
      · intro i hi; simp at hi; subst hi; simp; omega
      · intro i hi; simp at hi; subst hi; simp; omega
    · rcases l with _ | ⟨d, l⟩
      · exact absurd rfl hne
      have hd : d.1 = b' := hhd d (by simp)
      refine ⟨by simp, ?_, by simpa using hb, ?_, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hc
        · exact hle x (by simp [hx])
      · intro i hi
        rcases i with _ | i
        · simp; omega
        · have := hdir i (by simp at hi ⊢; omega)
          simpa using this
      · intro i hi
        rcases i with _ | i
        · simp; omega
        · have := hdiag i (by simp at hi ⊢; omega)
          simp at this ⊢; omega
      · intro i hi
        rcases i with _ | i
        · simp; omega
        · have := hlast i (by simp at hi ⊢; omega)
          simp at this ⊢; omega

theorem nil_not_isTail (r b : ℕ) : ¬ IsTail r b [] := fun h => h.1 rfl

theorem mem_tails (r b : ℕ) (cs : List (ℕ × ℕ)) : cs ∈ tails r b ↔ IsTail r b cs := by
  induction r generalizing b cs with
  | zero =>
    rw [isTail_zero, tails]
    split_ifs with h <;> simp [h]
  | succ r ih =>
    rcases cs with _ | ⟨c, l⟩
    · simp only [tails, List.mem_append, List.mem_flatMap, List.mem_map]
      refine iff_of_false ?_ (nil_not_isTail _ _)
      rintro (h | ⟨t, -, x, -, hx⟩)
      · split_ifs at h <;> simp at h
      · exact List.cons_ne_nil _ _ hx
    · rw [isTail_cons_succ]
      simp only [tails, List.mem_append, List.mem_flatMap, List.mem_map, ih, List.mem_range'_1]
      obtain ⟨c1, c2⟩ := c
      constructor
      · rintro (h | ⟨t, ht, x, ⟨b', hb', hx⟩, hxe⟩)
        · split_ifs at h with hb
          · simp at h
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
            exact ⟨rfl, hb, Or.inl ⟨rfl, rfl⟩⟩
          · simp at h
        · simp only [List.cons.injEq, Prod.mk.injEq] at hxe
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hxe
          refine ⟨rfl, by omega, Or.inr ⟨by omega, b', by omega, by omega, hx⟩⟩
      · rintro ⟨rfl, hc, ⟨rfl, rfl⟩ | ⟨hlt, b', h1, h2, hx⟩⟩
        · left
          simp only at hc
          rw [if_pos hc]
          simp
        · right
          exact ⟨c2, ⟨by simpa using h1.trans h2, by simp at hlt ⊢; omega⟩, l,
            ⟨b', ⟨by simpa using h1, by simp at h2 ⊢; omega⟩, hx⟩, rfl⟩

theorem isDeco_zero (cs : List (ℕ × ℕ)) : ¬ IsDeco 0 cs := by
  rintro ⟨-, -, -, -, -, ⟨i, hi, h⟩, -⟩
  omega

theorem isDeco_succ (r : ℕ) (cs : List (ℕ × ℕ)) : IsDeco (r + 1) cs ↔ IsTail r 0 cs := by
  constructor
  · rintro ⟨hne, hle, hhd, hdir, hdiag, ⟨j, hj, hjn⟩, hlast⟩
    refine ⟨hne, hle, hhd, hdir, fun i hi => by have := hdiag i hi; omega, ?_⟩
    intro i hi
    refine ⟨fun h => hlast i hi (by omega), fun h => ?_⟩
    have := hlast j hj hjn
    obtain rfl : i = j := by omega
    omega
  · rintro ⟨hne, hle, hhd, hdir, hdiag, hlast⟩
    refine ⟨hne, hle, hhd, hdir, fun i hi => by have := hdiag i hi; omega, ?_,
      fun i hi h => (hlast i hi).1 (by omega)⟩
    refine ⟨cs.length - 1, by have := List.length_pos_iff.2 hne; omega, ?_⟩
    have := (hlast (cs.length - 1) (by have := List.length_pos_iff.2 hne; omega)).2
      (by have := List.length_pos_iff.2 hne; omega)
    omega

/-- `decos n` consists exactly of the deco polyominoes of height `n`. -/
theorem mem_decos (n : ℕ) (cs : List (ℕ × ℕ)) : cs ∈ decos n ↔ IsDeco n cs := by
  cases n with
  | zero => simp [decos, isDeco_zero]
  | succ r => rw [decos, mem_tails, isDeco_succ]

theorem head_of_mem_tails {r b : ℕ} {x : List (ℕ × ℕ)} (h : x ∈ tails r b) :
    ∃ t l, x = (b, t) :: l := by
  rw [mem_tails] at h
  obtain ⟨hne, -, hhd, -⟩ := h
  rcases x with _ | ⟨⟨c1, c2⟩, l⟩
  · exact absurd rfl hne
  · have := hhd (c1, c2) (by simp)
    simp at this
    exact ⟨c2, l, by rw [this]⟩

theorem nodup_tails (r b : ℕ) : (tails r b).Nodup := by
  induction r generalizing b with
  | zero => rw [tails]; split_ifs <;> simp
  | succ r ih =>
    rw [tails, List.nodup_append]
    refine ⟨by split_ifs <;> simp, ?_, ?_⟩
    · refine List.nodup_flatMap.2 ⟨fun t _ => ?_, ?_⟩
      · refine List.Nodup.map List.cons_injective (List.nodup_flatMap.2 ⟨fun b' _ => ih b', ?_⟩)
        refine (List.nodup_range' (s := b) (n := t + 1 - b)).imp fun {b₁ b₂} hne => ?_
        refine List.disjoint_left.2 fun x h₁ h₂ => hne ?_
        obtain ⟨t₁, l₁, rfl⟩ := head_of_mem_tails h₁
        obtain ⟨t₂, l₂, h⟩ := head_of_mem_tails h₂
        simp only [List.cons.injEq, Prod.mk.injEq] at h
        exact h.1.1
      · refine (List.nodup_range' (s := b) (n := r + 1 - b)).imp fun {t₁ t₂} hne => ?_
        refine List.disjoint_left.2 fun x h₁ h₂ => hne ?_
        simp only [List.mem_map] at h₁ h₂
        obtain ⟨y₁, -, rfl⟩ := h₁
        obtain ⟨y₂, -, h⟩ := h₂
        simp only [List.cons.injEq, Prod.mk.injEq] at h
        exact h.1.2.symm
    · intro x hx y hy hxy
      subst hxy
      split_ifs at hx
      · simp only [List.mem_singleton] at hx
        subst hx
        simp only [List.mem_flatMap, List.mem_map, List.mem_range'_1] at hy
        obtain ⟨t, ht, z, -, hz⟩ := hy
        simp only [List.cons.injEq, Prod.mk.injEq] at hz
        omega
      · simp at hx

/-- `decos n` lists every deco polyomino of height `n` only once. -/
theorem nodup_decos (n : ℕ) : (decos n).Nodup := by
  cases n with
  | zero => simp [decos]
  | succ r => exact nodup_tails r 0

/-! ### Fast evaluation by dynamic programming -/

/-- `1` if the column `(b, t)` has even length, else `0`. -/
def eo (b t : ℕ) : ℕ := if (t + 1 - b) % 2 = 0 then 1 else 0

/-- From the row `T` for budget `r` (entry `b'`: number of lists in `tails r b'` and their total
number of even columns), the row for budget `r + 1`, following the recursion of `tails`. -/
def nextRow (r : ℕ) (T : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (List.range (r + 2)).map fun b =>
    (1 + ((List.range' b (r + 1 - b)).map fun t =>
          ((List.range' b (t + 1 - b)).map fun b' => (T.getD b' (0, 0)).1).sum).sum,
     eo b (r + 1) + ((List.range' b (r + 1 - b)).map fun t =>
          eo b t * ((List.range' b (t + 1 - b)).map fun b' => (T.getD b' (0, 0)).1).sum +
          ((List.range' b (t + 1 - b)).map fun b' => (T.getD b' (0, 0)).2).sum).sum)

/-- `(tab r).getD b (0, 0) = ((tails r b).length, total even columns over tails r b)`
(`tab_getD`). -/
def tab : ℕ → List (ℕ × ℕ)
  | 0 => [(1, 0)]
  | r + 1 => nextRow r (tab r)

/-- `a`, computed by dynamic programming (`a_eq_aDP`). -/
def aDP : ℕ → ℕ
  | 0 => 0
  | n + 1 => ((tab n).getD 0 (0, 0)).2

theorem evenCols_cons (b t : ℕ) (x : List (ℕ × ℕ)) :
    evenCols ((b, t) :: x) = eo b t + evenCols x := by
  simp only [evenCols, List.countP_cons, eo]
  split_ifs with h1 h2 h2 <;> simp_all; omega

theorem sum_evenCols_map_cons (b t : ℕ) (X : List (List (ℕ × ℕ))) :
    ((X.map ((b, t) :: ·)).map evenCols).sum = eo b t * X.length + (X.map evenCols).sum := by
  induction X with
  | nil => simp
  | cons x X ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, evenCols_cons] at ih ⊢
    rw [ih]; ring

theorem sum_map_flatMap {α β : Type*} (l : List α) (f : α → List β) (g : β → ℕ) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem evenCols_nil : evenCols [] = 0 := rfl

theorem tab_getD (r b : ℕ) :
    (tab r).getD b (0, 0) = ((tails r b).length, ((tails r b).map evenCols).sum) := by
  induction r generalizing b with
  | zero =>
    rcases b with _ | b
    · decide
    · simp [tab, tails]
  | succ r ih =>
    rw [tab, nextRow, List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hb : b < r + 2
    · rw [List.getElem?_range hb]
      simp only [Option.map_some, Option.getD_some, ih]
      rw [tails, if_pos (by omega)]
      simp only [List.length_append, List.length_singleton, List.length_flatMap,
        List.length_map, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, sum_map_flatMap, sum_evenCols_map_cons, evenCols_cons,
        evenCols_nil]
      refine Prod.ext ?_ ?_
      · simp only
      · simp only; ring
    · rw [List.getElem?_eq_none_iff.2 (by simp; omega)]
      rw [tails, if_neg (by omega), show r + 1 - b = 0 by omega]
      simp

theorem a_eq_aDP (n : ℕ) : a n = aDP n := by
  cases n with
  | zero => rfl
  | succ r => rw [a, decos, aDP, tab_getD]

/-- The number of lists in `tails r b`, read off the table. -/
theorem length_tails (r b : ℕ) : (tails r b).length = ((tab r).getD b (0, 0)).1 := by
  rw [tab_getD]

/-- The definition reproduces all 19 terms listed in OEIS, `a 1, …, a 19` (kernel-checked, through
the proven-equal `aDP`). -/
theorem a_data : (List.range 19).map (fun i => a (i + 1)) =
    [0, 1, 5, 26, 184, 1338, 11652, 108210, 1140336, 12849714, 159858900, 2117522754,
      30442090248, 463511103426, 7569181895436, 130254363597330, 2383020441932256,
      45738553437874962, 927010880040945924] := by
  simp only [a_eq_aDP]
  decide +kernel

/-- There are `n!` deco polyominoes of height `n`, for `n = 1, …, 19` (kernel-checked). -/
theorem decos_length_data : (List.range 19).map (fun i => (decos (i + 1)).length) =
    (List.range 19).map (fun i => (i + 1).factorial) := by
  simp only [decos, length_tails]
  decide +kernel

/-- Mathar's conjectured recurrence: for every `n ≥ 7`,
`a(n) - (n+2)·a(n-1) + (-n²+4n-2)·a(n-2) + (n³-3n²-4n+11)·a(n-3) - (n-1)(n²-11n+26)·a(n-4)
+ (-n³+5n²+7n-43)·a(n-5) + (n-3)(n-5)²·a(n-6) = 0` (computed in `ℤ`). -/
def statement : Prop :=
  ∀ n : ℕ, 7 ≤ n →
    (a n : ℤ) + (-(n : ℤ) - 2) * a (n - 1) + (-(n : ℤ) ^ 2 + 4 * n - 2) * a (n - 2) +
      ((n : ℤ) ^ 3 - 3 * n ^ 2 - 4 * n + 11) * a (n - 3) -
      ((n : ℤ) - 1) * ((n : ℤ) ^ 2 - 11 * n + 26) * a (n - 4) +
      (-(n : ℤ) ^ 3 + 5 * n ^ 2 + 7 * n - 43) * a (n - 5) +
      ((n : ℤ) - 3) * ((n : ℤ) - 5) ^ 2 * a (n - 6) = 0

/-- Sanity check of the transcription: the recurrence of `statement` holds on the listed terms,
`7 ≤ n ≤ 19` (kernel-checked; this says nothing about larger `n`). -/
theorem recurrence_data : ∀ n ∈ List.range' 7 13,
    (a n : ℤ) + (-(n : ℤ) - 2) * a (n - 1) + (-(n : ℤ) ^ 2 + 4 * n - 2) * a (n - 2) +
      ((n : ℤ) ^ 3 - 3 * n ^ 2 - 4 * n + 11) * a (n - 3) -
      ((n : ℤ) - 1) * ((n : ℤ) ^ 2 - 11 * n + 26) * a (n - 4) +
      (-(n : ℤ) ^ 3 + 5 * n ^ 2 + 7 * n - 43) * a (n - 5) +
      ((n : ℤ) - 3) * ((n : ℤ) - 5) ^ 2 * a (n - 6) = 0 := by
  simp only [a_eq_aDP]
  decide +kernel

end Math0.Statements.A121750
