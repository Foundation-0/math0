/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A075855
import Math0.Audit

/-!
# The longest path on the black squares of an even chessboard (A075855)

We prove the conjecture in OEIS A075855: for even `n = 2m ≥ 2`, the longest path through
diagonally adjacent black squares of the `n × n` board covers `(n^2 - n + 2)/2 = 2m^2 - m + 1`
squares.

**Upper bound (weights).** Give the black square `(i, j)` weight `-1` if
`i + j < n` and `i` is odd, or `i + j ≥ n` and `i` is even (`mi`), and weight `+1` otherwise.
Diagonal neighbours lie in rows of different parity, so two adjacent squares on the same side of
the anti-diagonal `i + j = n` have opposite weights. Hence two adjacent `+1` squares are the ends
of one of the `m` "useful" edges `(i, j) — (i+1, j+1)` with `i + j = n - 2`, `i` even (`us`
marks their lower ends; `plus_plus`). Walking along a path `h :: l` from its far end, `key`
shows `|h :: l| + [h is useful and its partner is not on the path] ≤
2·#(-1 squares) + #(useful squares) + [h has weight +1]`: a step onto a `+1` square from a `+1`
square uses a useful edge whose lower end is either the new square or the previous square,
which then still had its credit. So a path has at most `2·m(m-1) + m + 1` squares, because the
board has `m (m-1)` squares of weight `-1` and `m` useful squares (`count_mi`, `count_us`,
via injections into `range m ×ˢ range (m-1)` and `range m`).

**Lower bound (construction).** Cut the board into `m` strips of two rows. Snake upwards:
strip `2k` left to right in full (`2m` squares), strip `2k+1` right to left without its two
end squares (`2m - 2` squares); `blk` is one such pair of strips. For odd `m` finish with a full
strip, for even `m` with the corner `(n - 2, 0)`. This misses exactly `m - 1` squares.
-/

namespace Math0.Frontier.A075855
open Math0.Statements.A075855

/-! ### Upper bound -/

/-- The cells of weight `-1` on the board of side `n` (`n` even): below the anti-diagonal
`i + j = n` in odd rows, and on or above it in even rows. -/
private def mi (n : ℕ) (c : ℕ × ℕ) : Bool :=
  decide ((c.1 + c.2 < n ∧ c.1 % 2 = 1) ∨ (n ≤ c.1 + c.2 ∧ c.1 % 2 = 0))

/-- The lower ends `(i, j)` (`i + j = n - 2`, `i` even) of the `n / 2` "useful" edges
`(i, j) — (i + 1, j + 1)`, the only edges joining two cells of weight `+1`. -/
private def us (n : ℕ) (c : ℕ × ℕ) : Bool := decide (c.1 + c.2 + 2 = n ∧ c.1 % 2 = 0)

/-- Two adjacent black cells of weight `+1` are the two ends of a useful edge. -/
private lemma plus_plus {n : ℕ} {c d : ℕ × ℕ} (hn : n % 2 = 0) (hc : IsBlack n c)
    (hd : IsBlack n d) (hadj : Adj c d) (h1 : mi n c = false) (h2 : mi n d = false) :
    (us n c = true ∧ d = (c.1 + 1, c.2 + 1)) ∨ (us n d = true ∧ c = (d.1 + 1, d.2 + 1)) := by
  rw [adj_iff_of_isBlack hc hd] at hadj
  obtain ⟨a, b⟩ := c
  obtain ⟨e, f⟩ := d
  simp only [IsBlack, mi, us, decide_eq_true_eq, decide_eq_false_iff_not, Prod.mk.injEq] at *
  omega

/-- The main inequality, by induction along the path (from its far end): for a path `h :: l`,
`|h :: l| + [h is useful and its partner is not on the path]
  ≤ 2 · #(weight -1 cells) + #(useful cells) + [h has weight +1]`. -/
private lemma key (n : ℕ) (hn : n % 2 = 0) : ∀ (l : List (ℕ × ℕ)) (h : ℕ × ℕ),
    IsBoardPath n (h :: l) →
    (h :: l).length + (if us n h = true ∧ (h.1 + 1, h.2 + 1) ∉ l then 1 else 0) ≤
      2 * (h :: l).countP (mi n) + (h :: l).countP (us n) + (if mi n h = true then 0 else 1) := by
  intro l
  induction l with
  | nil =>
    intro h _
    simp only [List.countP_cons, List.countP_nil, List.length_cons, List.length_nil]
    split_ifs <;> simp_all
  | cons d l ih =>
    intro h hP
    rw [isBoardPath_cons_cons] at hP
    obtain ⟨hh, hnot, hadj, hP'⟩ := hP
    have ih' := ih d hP'
    have hd : IsBlack n d := hP'.1 d List.mem_cons_self
    have key2 : mi n h = false → mi n d = false →
        ((us n h = true ∧ (h.1 + 1, h.2 + 1) ∈ d :: l) ∨
          (us n d = true ∧ (d.1 + 1, d.2 + 1) ∉ l)) := by
      intro h1 h2
      rcases plus_plus hn hh hd hadj h1 h2 with ⟨hu, he⟩ | ⟨hu, he⟩
      · exact Or.inl ⟨hu, by rw [← he]; exact List.mem_cons_self⟩
      · exact Or.inr ⟨hu, by rw [← he]; exact fun hm => hnot (List.mem_cons_of_mem _ hm)⟩
    have e2 : (if us n h = true ∧ (h.1 + 1, h.2 + 1) ∉ d :: l then 1 else 0) ≤
        (if us n h = true then 1 else 0) := by
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd h1.1 h2
      · exact Nat.zero_le _
      · exact le_rfl
    have e3 : mi n h = false → mi n d = false →
        (if us n h = true ∧ (h.1 + 1, h.2 + 1) ∉ d :: l then 1 else 0) + 1 ≤
          (if us n h = true then 1 else 0) +
            (if us n d = true ∧ (d.1 + 1, d.2 + 1) ∉ l then 1 else 0) := by
      intro h1 h2
      rcases key2 h1 h2 with ⟨hu, hm⟩ | ⟨hu, hm⟩
      · rw [if_neg (fun hh => hh.2 hm), if_pos hu]
        exact Nat.le_add_right _ _
      · rw [if_pos (show us n d = true ∧ (d.1 + 1, d.2 + 1) ∉ l from ⟨hu, hm⟩)]
        omega
    simp only [List.countP_cons, List.length_cons] at ih' ⊢
    by_cases hmh : mi n h = true <;> by_cases hmd : mi n d = true
    · simp only [hmh, hmd, ↓reduceIte] at ih' ⊢
      omega
    · simp only [hmh, hmd, ↓reduceIte, Bool.false_eq_true] at ih' ⊢
      omega
    · simp only [hmh, hmd, ↓reduceIte, Bool.false_eq_true] at ih' ⊢
      omega
    · have e4 := e3 (by simpa using hmh) (by simpa using hmd)
      simp only [hmh, hmd, ↓reduceIte, Bool.false_eq_true] at ih' ⊢
      omega

/-- A list that `f` maps injectively into `s` has length at most `s.card`. -/
private lemma len_le_of_inj {α β : Type} [DecidableEq β] (l : List α) (hl : l.Nodup)
    (f : α → β) (s : Finset β) (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y)
    (hs : ∀ x ∈ l, f x ∈ s) : l.length ≤ s.card := by
  have h1 : (l.map f).Nodup := hl.map_on hinj
  calc l.length = (l.map f).length := by simp
    _ = (l.map f).toFinset.card := (List.toFinset_card_of_nodup h1).symm
    _ ≤ s.card := Finset.card_le_card (by
        intro y hy
        simp only [List.mem_toFinset, List.mem_map] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact hs x hx)

/-- A path on the board of side `2m` contains at most `m` useful cells. -/
private lemma count_us (m : ℕ) (l : List (ℕ × ℕ)) (hl : IsBoardPath (2 * m) l) :
    l.countP (us (2 * m)) ≤ m := by
  rw [List.countP_eq_length_filter]
  have := len_le_of_inj (l.filter (us (2 * m))) (hl.2.1.filter _) (fun c => c.1 / 2)
    (Finset.range m) ?_ ?_
  · simpa using this
  · intro x hx y hy hxy
    simp only [List.mem_filter, us, decide_eq_true_eq] at hx hy
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    simp only [Prod.mk.injEq] at hxy hx hy ⊢
    omega
  · intro x hx
    simp only [List.mem_filter, us, decide_eq_true_eq] at hx
    simp only [Finset.mem_range]
    omega

/-- A path on the board of side `2m` contains at most `m (m - 1)` cells of weight `-1`. -/
private lemma count_mi (m : ℕ) (l : List (ℕ × ℕ)) (hl : IsBoardPath (2 * m) l) :
    l.countP (mi (2 * m)) ≤ m * (m - 1) := by
  rw [List.countP_eq_length_filter]
  have := len_le_of_inj (l.filter (mi (2 * m))) (hl.2.1.filter _)
    (fun c => (c.1 / 2, if c.1 % 2 = 1 then c.2 / 2 else c.2 / 2 - 1))
    (Finset.range m ×ˢ Finset.range (m - 1)) ?_ ?_
  · simpa using this
  · intro x hx y hy hxy
    simp only [List.mem_filter, mi, decide_eq_true_eq] at hx hy
    have hbx := hl.1 x hx.1
    have hby := hl.1 y hy.1
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    simp only [IsBlack] at hbx hby
    simp only [Prod.mk.injEq] at hxy hx hy ⊢
    split_ifs at hxy <;> omega
  · intro x hx
    simp only [List.mem_filter, mi, decide_eq_true_eq] at hx
    have hbx := hl.1 x hx.1
    obtain ⟨x1, x2⟩ := x
    simp only [IsBlack] at hbx
    simp only [Finset.mem_product, Finset.mem_range]
    split_ifs <;> omega

/-- Upper bound: a path on the board of side `2m` has at most `2 m^2 - m + 1` cells. -/
private lemma upper (m : ℕ) (l : List (ℕ × ℕ)) (hl : IsBoardPath (2 * m) l) :
    l.length + m ≤ 2 * (m * m) + 1 := by
  cases l with
  | nil => simp; exact Nat.le_mul_self m |>.trans (by omega)
  | cons h l =>
    have h1 := key (2 * m) (by omega) l h hl
    have h2 := count_us m _ hl
    have h3 := count_mi m _ hl
    have h4 : m * (m - 1) = m * m - m := Nat.mul_sub_one m m
    have h5 := Nat.le_mul_self m
    split_ifs at h1 <;> omega

/-! ### Lower bound -/

/-- Gluing two paths: disjoint, with the last square of the first adjacent to the first square
of the second. -/
private lemma isBoardPath_append {n : ℕ} {l₁ l₂ : List (ℕ × ℕ)} (h₁ : IsBoardPath n l₁)
    (h₂ : IsBoardPath n l₂) (hd : ∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b)
    (hc : ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, Adj x y) : IsBoardPath n (l₁ ++ l₂) :=
  ⟨fun c hc => (List.mem_append.1 hc).elim (h₁.1 c) (h₂.1 c),
    List.nodup_append.2 ⟨h₁.2.1, h₂.2.1, hd⟩, List.isChain_append.2 ⟨h₁.2.2, h₂.2.2, hc⟩⟩

/-- The zigzag through rows `4k, 4k+1` from left to right (`2m` squares), then back through
rows `4k+2, 4k+3` from right to left, leaving out the two end squares (`2m - 2` squares). -/
private def blk (m k : ℕ) : List (ℕ × ℕ) :=
  (List.range (4 * m - 2)).map fun t =>
    if t < 2 * m then (4 * k + t % 2, t) else (4 * k + 2 + t % 2, 4 * m - 2 - t)

/-- The first `q` blocks, one after the other. -/
private def blks (m : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | q + 1 => blks m q ++ blk m q

/-- The left-to-right zigzag through rows `r, r+1` (`2m` squares). -/
private def strip (m r : ℕ) : List (ℕ × ℕ) :=
  (List.range (2 * m)).map fun t => (r + t % 2, t)

/-- A block is a path in rows `4k, …, 4k+3`; its only square in column `0` is `(4k, 0)`; it
runs from `(4k, 0)` to `(4k+3, 1)` and has `4m - 2` squares. -/
private lemma blk_props (m k : ℕ) (hk : 4 * k + 4 ≤ 2 * m) :
    IsBoardPath (2 * m) (blk m k) ∧
      (∀ c ∈ blk m k, 4 * k ≤ c.1 ∧ c.1 < 4 * k + 4 ∧ (c.2 = 0 → c.1 % 4 = 0)) ∧
      (blk m k).head? = some (4 * k, 0) ∧ (blk m k).getLast? = some (4 * k + 3, 1) ∧
      (blk m k).length = 4 * m - 2 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [blk, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    simp only [IsBlack]
    split_ifs <;> simp only <;> omega
  · refine List.Nodup.map_on ?_ List.nodup_range
    intro x hx y hy hxy
    simp only [List.mem_range] at hx hy
    split_ifs at hxy <;> simp only [Prod.mk.injEq] at hxy <;> omega
  · rw [blk, List.isChain_map, List.isChain_range]
    intro t ht
    simp only [Adj, ne_eq, Prod.ext_iff, Nat.succ_eq_add_one]
    split_ifs <;> simp only <;> omega
  · intro c hc
    simp only [blk, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    split_ifs <;> simp only <;> omega
  · simp only [blk, List.head?_map, List.head?_range]
    rw [if_neg (by omega)]
    simp only [Option.map_some, Option.some.injEq]
    rw [if_pos (by omega)]
    simp
  · simp only [blk, List.getLast?_map, List.getLast?_range]
    rw [if_neg (by omega)]
    simp only [Option.map_some, Option.some.injEq]
    rw [if_neg (by omega)]
    simp only [Prod.mk.injEq]
    omega
  · simp [blk]

/-- The first `q` blocks form a path in rows `< 4q` whose squares in column `0` lie in rows
divisible by `4`; it ends at `(4q - 1, 1)` and has `q (4m - 2)` squares. -/
private lemma blks_props (m : ℕ) : ∀ q, 4 * q ≤ 2 * m →
    IsBoardPath (2 * m) (blks m q) ∧
      (∀ c ∈ blks m q, c.1 < 4 * q ∧ (c.2 = 0 → c.1 % 4 = 0)) ∧
      (∀ x ∈ (blks m q).getLast?, x = (4 * q - 1, 1)) ∧
      (blks m q).length = q * (4 * m - 2) := by
  intro q
  induction q with
  | zero => intro _; simp [blks, isBoardPath_nil]
  | succ q ih =>
    intro hq
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    obtain ⟨b1, b2, b3, b4, b5⟩ := blk_props m q (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine isBoardPath_append h1 b1 ?_ ?_
      · intro a ha b hb hab
        have := (h2 a ha).1
        have := (b2 b hb).1
        subst hab
        omega
      · intro x hx y hy
        rw [h3 x hx]
        rw [b3, Option.mem_some_iff] at hy
        subst hy
        cases q with
        | zero => simp [blks] at hx
        | succ q =>
          simp only [Adj, ne_eq, Prod.ext_iff]
          omega
    · intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · have := h2 c hc
        omega
      · have := b2 c hc
        omega
    · intro x hx
      simp only [blks, List.getLast?_append, b4, Option.some_or, Option.mem_some_iff] at hx
      subst hx
      rw [show 4 * (q + 1) - 1 = 4 * q + 3 by omega]
    · simp only [blks, List.length_append, h4, b5]
      ring

/-- A path with `2 m^2 - m + 1` squares on the board of side `2m`, `m ≥ 1`. -/
private lemma lower (m : ℕ) (hm : 1 ≤ m) :
    ∃ l, IsBoardPath (2 * m) l ∧ l.length + m = 2 * (m * m) + 1 := by
  obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' m
  · -- `m = 2 (q' + 1)`: all blocks, then the corner `(4 q' + 2, 0)`
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    obtain ⟨h1, h2, h3, h4⟩ := blks_props (2 * (q' + 1)) (q' + 1) (by omega)
    refine ⟨blks (2 * (q' + 1)) (q' + 1) ++ [(4 * q' + 2, 0)], ?_, ?_⟩
    · refine isBoardPath_append h1 (isBoardPath_singleton ⟨by omega, by omega, by simp; omega⟩)
        ?_ ?_
      · intro a ha b hb hab
        rw [List.mem_singleton] at hb
        subst hb
        subst hab
        have := (h2 _ ha).2 rfl
        omega
      · intro x hx y hy
        rw [h3 x hx]
        simp only [List.head?_cons, Option.mem_some_iff] at hy
        subst hy
        simp only [Adj, ne_eq, Prod.ext_iff]
        omega
    · rw [List.length_append, h4, List.length_singleton]
      have : 4 * (2 * (q' + 1)) - 2 = 8 * q' + 6 := by omega
      rw [this]
      ring
  · -- `m = 2 q + 1`: the first `q` blocks, then the top strip
    obtain ⟨h1, h2, h3, h4⟩ := blks_props (2 * q + 1) q (by omega)
    have s1 : IsBoardPath (2 * (2 * q + 1)) (strip (2 * q + 1) (4 * q)) := by
      refine ⟨?_, ?_, ?_⟩
      · intro c hc
        simp only [strip, List.mem_map, List.mem_range] at hc
        obtain ⟨t, ht, rfl⟩ := hc
        simp only [IsBlack]
        omega
      · refine List.Nodup.map_on ?_ List.nodup_range
        intro x hx y hy hxy
        simp only [Prod.mk.injEq] at hxy
        exact hxy.2
      · rw [strip, List.isChain_map, List.isChain_range]
        intro t ht
        simp only [Adj, ne_eq, Prod.ext_iff, Nat.succ_eq_add_one]
        omega
    refine ⟨blks (2 * q + 1) q ++ strip (2 * q + 1) (4 * q), isBoardPath_append h1 s1 ?_ ?_, ?_⟩
    · intro a ha b hb hab
      simp only [strip, List.mem_map, List.mem_range] at hb
      obtain ⟨t, ht, rfl⟩ := hb
      have := (h2 a ha).1
      subst hab
      simp only at this
      omega
    · intro x hx y hy
      rw [h3 x hx]
      simp only [strip, List.head?_map, List.head?_range] at hy
      rw [if_neg (by omega)] at hy
      simp only [Option.map_some, Option.mem_some_iff] at hy
      subst hy
      cases q with
      | zero => simp [blks] at hx
      | succ q =>
        simp only [Adj, ne_eq, Prod.ext_iff]
        omega
    · rw [List.length_append, h4]
      simp only [strip, List.length_map, List.length_range]
      have : 4 * (2 * q + 1) - 2 = 8 * q + 2 := by omega
      rw [this]
      ring

/-- **A075855, even case.** For even `n ≥ 2`, the longest path on the black squares of the
`n × n` chessboard covers exactly `(n^2 - n + 2) / 2` squares. -/
theorem result : statement := by
  intro n hn hev
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := by
    obtain ⟨k, hk⟩ := hev
    exact ⟨k, by omega⟩
  have hm : 1 ≤ m := by omega
  have hv : ((2 * m) ^ 2 - 2 * m + 2) / 2 = 2 * (m * m) - m + 1 := by
    have h1 : (2 * m) ^ 2 = 4 * (m * m) := by ring
    have h2 := Nat.le_mul_self m
    rw [h1]
    omega
  rw [hv]
  have h2 := Nat.le_mul_self m
  obtain ⟨l, hl, hlen⟩ := lower m hm
  apply le_antisymm
  · obtain ⟨l', hl', hlen'⟩ := (a_spec (2 * m)).1
    have := upper m l' hl'
    omega
  · have := (a_spec (2 * m)).2 (show l.length ∈ {k | ∃ l, IsBoardPath (2 * m) l ∧ l.length = k}
      from ⟨l, hl, rfl⟩)
    omega

end Math0.Frontier.A075855

#math0_settles Math0.Frontier.A075855.result Math0.Statements.A075855.statement
