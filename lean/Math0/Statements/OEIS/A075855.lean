/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A075855: longest path on the black squares of an even chessboard

Source: https://oeis.org/A075855, Jon Perry, Oct 15 2002 (edited by Dean Hickerson,
Oct 25 2002; FORMULA section). Verbatim:
> For n odd, a(n)=(n-1)^2/2+1. For n even, it is conjectured that a(n)=(n^2-n+2)/2 (it is easy
> to show this is a lower bound).

The entry's definition (offset 1): "Maximum number of black squares on an n X n chessboard (with
a black square in at least one corner) that can be covered by a single path, traveling only to
adjacent black squares." The conjecture is the even case; the odd case is stated as a fact and
is not part of `statement`.

## Encoding

* *Board.* The square in row `i` and column `j` (`0`-indexed, `i, j < n`) is the pair `(i, j)`.
  It is black iff `i + j` is even (`IsBlack`), so the corner `(0, 0)` is black. For even `n` the
  two colourings of the board are mirror images of each other, so the choice of colouring does
  not matter there; for odd `n` it is fixed by "with a black square in at least one corner".
* *Adjacency.* Two squares are adjacent iff they are distinct and touch, i.e. both coordinates
  differ by at most `1` (`Adj`). Two black squares never share an edge, so for black squares
  this means sharing a corner, i.e. being diagonal neighbours (`adj_iff_of_isBlack`). This is the
  only reading under which a path can have more than one square, and it gives the listed values
  (e.g. `a(2) = 2` uses the step `(0,0) → (1,1)`).
* *Paths.* A path is a list of black squares, consecutive squares adjacent, that does not visit a
  square twice (`IsBoardPath`). The number of squares covered is its length. (If squares could be
  revisited, every black square could be covered, e.g. `5` for `n = 3`, but the entry lists
  `a(3) = 3`.) The empty path is allowed; it only matters for `n = 0`, outside the offset.
* *The sequence.* `a n` is computed by an exhaustive depth-first search over all paths (`dfs`,
  with the visited squares kept as a bit mask), started from every black square. `a_spec` proves
  that `a n` is exactly the maximum length of a path: it is the greatest element of
  `{k | ∃ l, IsBoardPath n l ∧ l.length = k}`. So `a` is the entry's sequence, with no reliance on
  the correctness of the search beyond what is proved here.
* *Data.* `a_data` kernel-checks the listed terms `a(1), …, a(6)` = `1, 2, 3, 7, 9, 16`. The
  search visits every path, and the number of paths grows fast (`17932` directed paths for
  `n = 6`, `295501` for `n = 7`), so `a(7), a(8), a(9)` = `19, 29, 33` are out of reach of the
  kernel. `a_data_lower` kernel-checks explicit paths of `19`, `29` and `33` squares, so
  `a(7) ≥ 19`, `a(8) ≥ 29`, `a(9) ≥ 33`. (An independent exhaustive search outside Lean, over all
  `10181048` resp. `441446761` directed paths for `n = 8, 9`, gives the listed values
  `a(7) = 19`, `a(8) = 29`, `a(9) = 33`; that check is not part of this file.)
* *Reading of the conjecture.* For every even `n` in the range of the entry (`n ≥ 1`, i.e.
  `n ≥ 2`), `a n = (n ^ 2 - n + 2) / 2`. Here `n ^ 2 - n + 2 = n (n - 1) + 2` is even, so the
  division in `ℕ` is exact, and the subtraction does not truncate since `n ≤ n ^ 2`.
  Equivalently `a (2 m) = 2 m ^ 2 - m + 1` for `m ≥ 1`.
-/

namespace Math0.Statements.A075855

/-! ### Board, adjacency and paths -/

/-- The square `c = (i, j)` (row `i`, column `j`, `0`-indexed) of the `n × n` board is black:
`i < n`, `j < n` and `i + j` is even (the corner `(0, 0)` is black). -/
def IsBlack (n : ℕ) (c : ℕ × ℕ) : Prop := c.1 < n ∧ c.2 < n ∧ (c.1 + c.2) % 2 = 0

/-- Two squares are adjacent: they are distinct and touch (each coordinate differs by at most
`1`). For black squares this means sharing a corner (`adj_iff_of_isBlack`). -/
def Adj (c d : ℕ × ℕ) : Prop :=
  c ≠ d ∧ c.1 ≤ d.1 + 1 ∧ d.1 ≤ c.1 + 1 ∧ c.2 ≤ d.2 + 1 ∧ d.2 ≤ c.2 + 1

/-- A path on the black squares of the `n × n` board: a list of black squares, pairwise distinct
(no square is visited twice), with consecutive squares adjacent. The number of squares it covers
is its length. -/
def IsBoardPath (n : ℕ) (l : List (ℕ × ℕ)) : Prop :=
  (∀ c ∈ l, IsBlack n c) ∧ l.Nodup ∧ l.IsChain Adj

/-- Black squares are adjacent iff they are diagonal neighbours (black squares never share an
edge). -/
theorem adj_iff_of_isBlack {n : ℕ} {c d : ℕ × ℕ} (hc : IsBlack n c) (hd : IsBlack n d) :
    Adj c d ↔ (c.1 + 1 = d.1 ∨ d.1 + 1 = c.1) ∧ (c.2 + 1 = d.2 ∨ d.2 + 1 = c.2) := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨d1, d2⟩ := d
  simp only [IsBlack, Adj, ne_eq, Prod.mk.injEq] at hc hd ⊢
  omega

/-! ### The computable sequence -/

/-- `max` written with `Nat.ble`, which the kernel evaluates quickly. -/
def nmax (x y : ℕ) : ℕ := bif Nat.ble x y then y else x

/-- The maximum of `f` over the list `l` (`0` for the empty list). -/
def lmax {α : Type} (l : List α) (f : α → ℕ) : ℕ := l.foldr (fun x best => nmax best (f x)) 0

/-- The bit used for the square `c` in the mask of visited squares. -/
def idx (n : ℕ) (c : ℕ × ℕ) : ℕ := c.1 * n + c.2

/-- The diagonal neighbours of the square `d` that lie on the `n × n` board. -/
def nbrs (n : ℕ) (d : ℕ × ℕ) : List (ℕ × ℕ) :=
  (bif Nat.blt (d.1 + 1) n && Nat.blt (d.2 + 1) n then [(d.1 + 1, d.2 + 1)] else []) ++
  (bif Nat.blt (d.1 + 1) n && Nat.blt 0 d.2 then [(d.1 + 1, d.2 - 1)] else []) ++
  (bif Nat.blt 0 d.1 && Nat.blt (d.2 + 1) n then [(d.1 - 1, d.2 + 1)] else []) ++
  (bif Nat.blt 0 d.1 && Nat.blt 0 d.2 then [(d.1 - 1, d.2 - 1)] else [])

/-- Depth-first search: `dfs n fuel d mask` is the largest number of squares (at most `fuel`) by
which a path ending at the square `d`, whose visited squares are the set bits of `mask`, can be
continued. (Written with `Nat.rec` on the fuel, which the kernel evaluates faster than the
compiled structural recursion; `dfs_zero` and `dfs_succ` are the defining equations.) -/
def dfs (n : ℕ) (fuel : ℕ) : ℕ × ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ × ℕ → ℕ → ℕ) (fun _ _ => 0)
    (fun _ ih d mask => lmax ((nbrs n d).filter fun c => !mask.testBit (idx n c))
      fun c => ih c (mask ||| 1 <<< idx n c) + 1) fuel

theorem dfs_zero (n : ℕ) (d : ℕ × ℕ) (mask : ℕ) : dfs n 0 d mask = 0 := rfl

theorem dfs_succ (n fuel : ℕ) (d : ℕ × ℕ) (mask : ℕ) :
    dfs n (fuel + 1) d mask = lmax ((nbrs n d).filter fun c => !mask.testBit (idx n c))
      fun c => dfs n fuel c (mask ||| 1 <<< idx n c) + 1 := rfl

/-- The black squares of the `n × n` board. -/
def cells (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n ×ˢ List.range n).filter fun c => (c.1 + c.2) % 2 == 0

/-- A075855: the maximum number of black squares of the `n × n` board (corner `(0, 0)` black)
covered by a single path through adjacent black squares, found by an exhaustive search from
every black square (see `a_spec`). -/
def a (n : ℕ) : ℕ := lmax (cells n) fun c => dfs n (n * n) c (1 <<< idx n c) + 1

/-- The definition reproduces the first terms listed in OEIS, `a(1), …, a(6)`
(kernel-checked). -/
theorem a_data : (List.range 6).map (fun i => a (i + 1)) = [1, 2, 3, 7, 9, 16] := by
  decide +kernel

/-! ### `a n` is the maximum length of a path -/

theorem nmax_eq (x y : ℕ) : nmax x y = max x y := by
  unfold nmax
  cases h : Nat.ble x y
  · have : ¬ x ≤ y := fun hle => by simp [Nat.ble_eq_true_of_le hle] at h
    simp only [cond_false]; omega
  · have : x ≤ y := Nat.le_of_ble_eq_true h
    simp only [cond_true]; omega

theorem le_lmax {α : Type} {l : List α} {f : α → ℕ} {x : α} (hx : x ∈ l) : f x ≤ lmax l f := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    simp only [lmax, List.foldr_cons, nmax_eq] at ih ⊢
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_max_right _ _
    · exact (ih hx).trans (le_max_left _ _)

theorem lmax_cases {α : Type} (l : List α) (f : α → ℕ) :
    lmax l f = 0 ∨ ∃ x ∈ l, lmax l f = f x := by
  induction l with
  | nil => simp [lmax]
  | cons y l ih =>
    simp only [lmax, List.foldr_cons, nmax_eq] at ih ⊢
    rcases le_total (List.foldr (fun x best => max best (f x)) 0 l) (f y) with h | h
    · exact Or.inr ⟨y, List.mem_cons_self, max_eq_right h⟩
    · rw [max_eq_left h]
      rcases ih with ih | ⟨x, hx, hx'⟩
      · exact Or.inl ih
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hx'⟩

theorem mem_cells {n : ℕ} {c : ℕ × ℕ} : c ∈ cells n ↔ IsBlack n c := by
  obtain ⟨x, y⟩ := c
  simp [cells, IsBlack, List.mem_filter, List.mem_product, List.mem_range, and_assoc]

theorem idx_inj {n : ℕ} {c d : ℕ × ℕ} (hc : c.2 < n) (hd : d.2 < n) (h : idx n c = idx n d) :
    c = d := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨d1, d2⟩ := d
  simp only [idx] at h hc hd
  have h1 : c1 = d1 := by
    rcases lt_trichotomy c1 d1 with h' | h' | h'
    · have : (c1 + 1) * n ≤ d1 * n := Nat.mul_le_mul_right n h'
      nlinarith
    · exact h'
    · have : (d1 + 1) * n ≤ c1 * n := Nat.mul_le_mul_right n h'
      nlinarith
  subst h1
  have : c2 = d2 := by omega
  rw [this]

theorem testBit_or_one_shiftLeft (m k j : ℕ) :
    (m ||| 1 <<< k).testBit j = (m.testBit j || decide (k = j)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_one_shiftLeft (k j : ℕ) : (1 <<< k).testBit j = decide (k = j) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem mem_nbrs {n : ℕ} {c d : ℕ × ℕ} (hd1 : d.1 < n) (hd2 : d.2 < n) :
    c ∈ nbrs n d ↔ c.1 < n ∧ c.2 < n ∧
      (d.1 + 1 = c.1 ∨ c.1 + 1 = d.1) ∧ (d.2 + 1 = c.2 ∨ c.2 + 1 = d.2) := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨d1, d2⟩ := d
  simp only at hd1 hd2 ⊢
  simp only [nbrs, List.mem_append, Bool.cond_eq_ite, Bool.and_eq_true, Nat.blt_eq]
  split_ifs <;> simp only [List.mem_singleton, List.not_mem_nil, Prod.mk.injEq, or_false,
    false_or]
  all_goals first | omega | (rw [false_iff]; omega)

theorem isBoardPath_nil (n : ℕ) : IsBoardPath n [] := by simp [IsBoardPath]

theorem isBoardPath_singleton {n : ℕ} {c : ℕ × ℕ} (hc : IsBlack n c) : IsBoardPath n [c] := by
  simp [IsBoardPath, hc]

theorem isBoardPath_cons_cons {n : ℕ} {c d : ℕ × ℕ} {p : List (ℕ × ℕ)} :
    IsBoardPath n (c :: d :: p) ↔
      IsBlack n c ∧ c ∉ d :: p ∧ Adj c d ∧ IsBoardPath n (d :: p) := by
  simp only [IsBoardPath, List.mem_cons, forall_eq_or_imp, List.nodup_cons,
    List.isChain_cons_cons]
  tauto

theorem IsBoardPath.of_append {n : ℕ} {q p : List (ℕ × ℕ)} (h : IsBoardPath n (q ++ p)) :
    IsBoardPath n p :=
  ⟨fun c hc => h.1 c (List.mem_append_right q hc), h.2.1.of_append_right,
    (List.isChain_append.1 h.2.2).2.1⟩

theorem IsBoardPath.length_le {n : ℕ} {l : List (ℕ × ℕ)} (h : IsBoardPath n l) :
    l.length ≤ n * n := by
  rw [← List.toFinset_card_of_nodup h.2.1]
  have hsub : l.toFinset ⊆ Finset.range n ×ˢ Finset.range n := by
    intro c hc
    have := h.1 c (List.mem_toFinset.1 hc)
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨this.1, this.2.1⟩
  simpa using Finset.card_le_card hsub

/-- Correctness of the search: for a path `d :: p` (most recent square `d` first) whose squares
are the set bits of `mask`, `dfs n fuel d mask` is the largest length of a continuation `q` of at
most `fuel` squares such that `q ++ d :: p` is a path. -/
theorem dfs_spec (n : ℕ) : ∀ (fuel : ℕ) (d : ℕ × ℕ) (p : List (ℕ × ℕ)) (mask : ℕ),
    IsBoardPath n (d :: p) →
    (∀ e : ℕ × ℕ, e.1 < n → e.2 < n → (mask.testBit (idx n e) = true ↔ e ∈ d :: p)) →
    (∀ q, IsBoardPath n (q ++ d :: p) → q.length ≤ fuel → q.length ≤ dfs n fuel d mask) ∧
    (∃ q, IsBoardPath n (q ++ d :: p) ∧ q.length = dfs n fuel d mask) := by
  intro fuel
  induction fuel with
  | zero =>
    intro d p mask hP _
    refine ⟨fun q _ hq => by rw [dfs_zero]; exact hq, ⟨[], by simpa using hP, rfl⟩⟩
  | succ fuel ih =>
    intro d p mask hP hmask
    have hd : IsBlack n d := hP.1 d List.mem_cons_self
    -- the squares by which the path can be continued
    have hC : ∀ c, c ∈ (nbrs n d).filter (fun c => !mask.testBit (idx n c)) ↔
        IsBoardPath n (c :: d :: p) := by
      intro c
      rw [List.mem_filter, mem_nbrs hd.1 hd.2.1, isBoardPath_cons_cons]
      constructor
      · rintro ⟨⟨hc1, hc2, hadj⟩, hbit⟩
        have hcb : IsBlack n c := by
          refine ⟨hc1, hc2, ?_⟩
          have := hd.2.2
          omega
        refine ⟨hcb, ?_, ?_, hP⟩
        · intro hmem
          have := (hmask c hc1 hc2).2 hmem
          simp [this] at hbit
        · rw [adj_iff_of_isBlack hcb hd]
          omega
      · rintro ⟨hcb, hnot, hadj, -⟩
        rw [adj_iff_of_isBlack hcb hd] at hadj
        refine ⟨⟨hcb.1, hcb.2.1, by omega⟩, ?_⟩
        cases hb : mask.testBit (idx n c)
        · rfl
        · exact absurd ((hmask c hcb.1 hcb.2.1).1 hb) hnot
    -- the mask after visiting `c`
    have hmask' : ∀ c, IsBoardPath n (c :: d :: p) → ∀ e : ℕ × ℕ, e.1 < n → e.2 < n →
        ((mask ||| 1 <<< idx n c).testBit (idx n e) = true ↔ e ∈ c :: d :: p) := by
      intro c hc e he1 he2
      have hcb : IsBlack n c := hc.1 c List.mem_cons_self
      rw [testBit_or_one_shiftLeft, Bool.or_eq_true, hmask e he1 he2, decide_eq_true_iff,
        List.mem_cons (a := e) (b := c)]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl (idx_inj he2 hcb.2.1 h.symm)
      · rintro (h | h)
        · exact Or.inr (by rw [h])
        · exact Or.inl h
    rw [dfs_succ]
    constructor
    · intro q hq hlen
      rcases List.eq_nil_or_concat q with rfl | ⟨q', c, rfl⟩
      · simp
      · simp only [List.concat_eq_append, List.append_assoc, List.cons_append,
          List.nil_append] at hq
        have hcP : IsBoardPath n (c :: d :: p) := hq.of_append
        have hcC := (hC c).2 hcP
        have := (ih c (d :: p) _ hcP (hmask' c hcP)).1 q' hq
          (by simp only [List.concat_eq_append, List.length_append, List.length_singleton]
                at hlen; omega)
        refine le_trans ?_ (le_lmax hcC)
        simp only [List.concat_eq_append, List.length_append, List.length_singleton]
        omega
    · rcases lmax_cases ((nbrs n d).filter fun c => !mask.testBit (idx n c))
          (fun c => dfs n fuel c (mask ||| 1 <<< idx n c) + 1) with h | ⟨c, hcC, h⟩
      · exact ⟨[], by simpa using hP, by rw [h]; rfl⟩
      · have hcP := (hC c).1 hcC
        obtain ⟨q', hq', hlen⟩ := (ih c (d :: p) _ hcP (hmask' c hcP)).2
        refine ⟨q' ++ [c], ?_, ?_⟩
        · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hq'
        · rw [h, List.length_append, List.length_singleton, hlen]

/-- `a n` is the maximum number of black squares of the `n × n` board covered by a single path
through adjacent black squares: some path has `a n` squares and no path has more. -/
theorem a_spec (n : ℕ) : IsGreatest {k | ∃ l, IsBoardPath n l ∧ l.length = k} (a n) := by
  have hstart : ∀ c, IsBlack n c → ∀ e : ℕ × ℕ, e.1 < n → e.2 < n →
      ((1 <<< idx n c).testBit (idx n e) = true ↔ e ∈ [c]) := by
    intro c hc e he1 he2
    rw [testBit_one_shiftLeft, decide_eq_true_iff, List.mem_singleton]
    exact ⟨fun h => idx_inj he2 hc.2.1 h.symm, fun h => by rw [h]⟩
  constructor
  · rcases lmax_cases (cells n) (fun c => dfs n (n * n) c (1 <<< idx n c) + 1) with
      h | ⟨c, hc, h⟩
    · exact ⟨[], isBoardPath_nil n, by rw [a, h]; rfl⟩
    · have hcb := mem_cells.1 hc
      obtain ⟨q, hq, hlen⟩ :=
        (dfs_spec n (n * n) c [] _ (isBoardPath_singleton hcb) (hstart c hcb)).2
      exact ⟨q ++ [c], hq, by rw [a, h, List.length_append, List.length_singleton, hlen]⟩
  · rintro k ⟨l, hl, rfl⟩
    rcases List.eq_nil_or_concat l with rfl | ⟨q, c, rfl⟩
    · simp
    · simp only [List.concat_eq_append] at hl ⊢
      have hcb : IsBlack n c := (hl.of_append).1 c List.mem_cons_self
      have hlen := hl.length_le
      have := (dfs_spec n (n * n) c [] _ (isBoardPath_singleton hcb) (hstart c hcb)).1 q hl
        (by simp only [List.length_append, List.length_singleton] at hlen; omega)
      refine le_trans ?_ (le_lmax (f := fun c => dfs n (n * n) c (1 <<< idx n c) + 1)
        (mem_cells.2 hcb))
      simp only [List.length_append, List.length_singleton]
      omega

/-- The remaining listed terms `a(7), a(8), a(9)` = `19, 29, 33` are lower bounds: explicit paths
covering that many squares (found by a computer search) are kernel-checked. -/
theorem a_data_lower : 19 ≤ a 7 ∧ 29 ≤ a 8 ∧ 33 ≤ a 9 := by
  refine ⟨(a_spec 7).2 ⟨[(0, 0), (1, 1), (0, 2), (1, 3), (0, 4), (1, 5), (2, 4), (3, 3), (2, 2),
      (3, 1), (4, 0), (5, 1), (4, 2), (5, 3), (4, 4), (3, 5), (4, 6), (5, 5), (6, 4)], ?_, rfl⟩,
    (a_spec 8).2 ⟨[(0, 0), (1, 1), (0, 2), (1, 3), (0, 4), (1, 5), (0, 6), (1, 7), (2, 6), (3, 5),
      (2, 4), (3, 3), (2, 2), (3, 1), (4, 0), (5, 1), (4, 2), (5, 3), (4, 4), (5, 5), (4, 6), (5, 7),
      (6, 6), (7, 5), (6, 4), (7, 3), (6, 2), (7, 1), (6, 0)], ?_, rfl⟩,
    (a_spec 9).2 ⟨[(0, 0), (1, 1), (0, 2), (1, 3), (0, 4), (1, 5), (0, 6), (1, 7), (2, 6), (3, 5),
      (2, 4), (3, 3), (2, 2), (3, 1), (4, 0), (5, 1), (4, 2), (5, 3), (4, 4), (5, 5), (4, 6), (3, 7),
      (4, 8), (5, 7), (6, 6), (7, 7), (8, 6), (7, 5), (6, 4), (7, 3), (6, 2), (7, 1), (6, 0)], ?_,
      rfl⟩⟩ <;>
  · unfold IsBoardPath IsBlack Adj
    decide +kernel

/-! ### The conjecture -/

/-- For even `n ≥ 2` (the entry's range `n ≥ 1`, restricted to even `n`), the maximum number of
black squares of the `n × n` chessboard that a single path through adjacent black squares can
cover is `(n ^ 2 - n + 2) / 2`. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → Even n → a n = (n ^ 2 - n + 2) / 2

end Math0.Statements.A075855
