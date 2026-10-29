/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A182617
import Math0.Audit

/-!
# The toothpick spiral around `n` hexagonal cells (A182617): `a(n) = 2n + ⌈√(12n - 3)⌉`

We prove Librandi's conjecture: for `n ≥ 1`, the first time at which the toothpick spiral has
`n` cells ON is `2n + ⌈√(12n - 3)⌉`.

**The spiral in closed form.** In the brick-wall coordinates of the statement, the walk visits
"vertex ring" `m ≥ 0` during the times `bs m, …, bs m + 12 m + 7` with `bs m = 6 m² + 2 m`. The
`k`-th vertex of ring `m` is `pos m k`, a piecewise-linear function with six sides (two
horizontal rows and four staircases). Conversely `rg` and `off` (piecewise linear, with `max`
and halving) compute the ring and the offset of any vertex, so every vertex `v` gets an explicit
visit time `Q v = bs (rg v) + off v`, and `Q` is injective. A case analysis over the sides of
a ring (`LL`) shows the local rule of the spiral: arriving at `pos m k` from its predecessor,
either the left turn is the successor, or the left turn is an already visited vertex (on ring
`m - 1`, or the start for `m = 0`) and the right turn is the successor. By induction on `t`
(`inv`, `mem_walk`) the walk after `t` toothpicks covers exactly the vertices with `Q ≤ t`.

**Cells.** Cells are enumerated ring by ring: `cpos j s` is cell `s ∈ [1, 6 j]` of cell ring
`j` (and `cpos 0 0` is the centre); this is a bijection onto all cells. For each cell, an
explicit vertex is visited last, at time `Tz j s = 6 j² - 1 + 2 s + cc j s`, where
`cc j s ∈ {1, …, 6}` is one more than the number of corners of the cell ring passed so far
(`cell_complete`). With `n = 3 j (j - 1) + 1 + s` one has
`12 n - 3 = (6 j - 3)² + 12 s`, and squeezing between consecutive squares gives
`⌈√(12 n - 3)⌉ = 6 j - 3 + cc j s`, i.e. `Tz j s = 2 n + ⌈√(12 n - 3)⌉` (`TT_eq`). Since
this is strictly increasing in `n`, the cells ON after `t` toothpicks are exactly the cells
with index `n` satisfying `2 n + ⌈√(12 n - 3)⌉ ≤ t`, and the count follows.
-/

namespace Math0.Frontier.A182617
open Math0.Statements.A182617

/-- The ring index of a vertex: the spiral visits the vertices of ring `m` at times `bs m, …, bs m +
12 m + 7`. -/
private def rg (v : Pt) : ℤ :=
  if v.2 ≤ 0 then max (max (-v.2) ((1 - v.1 - v.2) / 2)) ((v.1 - v.2 - 1) / 2)
  else max (max (v.2 - 1) ((v.1 + v.2 - 2) / 2)) ((v.2 - v.1 - 2) / 2)

/-- The offset of the vertex `v` inside ring `m` (six sides `A`–`F` of the ring). -/
private def offm (m : ℤ) (v : Pt) : ℤ :=
  if v.2 ≤ 0 then
    (if v.1 + v.2 ≤ 1 - 2 * m then v.1 + 2 * m - v.2
     else if v.2 = -m then 3 * m + v.1 else 4 * m + v.1 + v.2)
  else
    (if v.1 + v.2 ≥ 2 * m + 2 then 8 * m + 4 - v.1 + v.2
     else if v.2 = m + 1 then 9 * m + 5 - v.1 else 10 * m + 6 - v.1 - v.2)

/-- The offset of a vertex inside its ring. -/
private def off (v : Pt) : ℤ := offm (rg v) v

/-- The vertex of ring `m` with offset `k` (for `0 ≤ k ≤ 12 m + 7`). -/
private def pos (m k : ℤ) : Pt :=
  if k ≤ 2 * m then (-2 * m + (k + 1) / 2, -(k / 2))
  else if k ≤ 4 * m + 2 then (k - 3 * m, -m)
  else if k ≤ 6 * m + 2 then (m + 2 + (k - 4 * m - 2) / 2, -m + (k - 4 * m - 1) / 2)
  else if k ≤ 8 * m + 3 then (2 * m + 2 - (k - 6 * m - 2) / 2, (k - 6 * m - 1) / 2)
  else if k ≤ 10 * m + 7 then (9 * m + 5 - k, m + 1)
  else (-m - 2 - (k - 10 * m - 7) / 2, m + 1 - (k - 10 * m - 6) / 2)

/-- `rg` and `off` invert `pos` on valid ring/offset pairs. -/
private lemma D2 (m k : ℤ) (hm : 0 ≤ m) (hk : 0 ≤ k) (hk' : k ≤ 12 * m + 7) :
    rg (pos m k) = m ∧ off (pos m k) = k := by
  have hr : rg (pos m k) = m := by
    unfold pos
    split_ifs <;> (unfold rg; omega)
  refine ⟨hr, ?_⟩
  unfold off; rw [hr]
  unfold pos
  split_ifs <;> (unfold offm; omega)

/-- Ring indices are nonnegative. -/
private lemma rg_nonneg (v : Pt) : 0 ≤ rg v := by unfold rg; omega

/-- Every vertex is `pos (rg v) (off v)`, with a valid offset. -/
private lemma D1 (v : Pt) : 0 ≤ off v ∧ off v ≤ 12 * rg v + 7 ∧ pos (rg v) (off v) = v := by
  obtain ⟨x, y⟩ := v
  unfold off
  have h0 := rg_nonneg (x, y)
  generalize hm : rg (x, y) = m at h0 ⊢
  unfold rg at hm
  simp only at hm
  unfold offm
  simp only
  split_ifs with h1 h2 h3 h4 h5 <;>
  (unfold pos; split_ifs <;> simp only [Prod.mk.injEq] <;> omega)

/-- The time at which ring `m` starts: `6 m² + 2 m`. -/
private def bs (m : ℤ) : ℤ := 6 * m * m + 2 * m

/-- The visit time of a vertex in the spiral (proved to be correct in `mem_walk`). -/
private def Q (v : Pt) : ℤ := bs (rg v) + off v

/-- Ring `m` has `12 m + 8` vertices. -/
private lemma bs_succ (m : ℤ) : bs (m + 1) = bs m + 12 * m + 8 := by unfold bs; ring

/-- Later rings start after earlier rings end. -/
private lemma bs_mono {a b : ℤ} (ha : 0 ≤ a) (hab : a < b) : bs a + 12 * a + 8 ≤ bs b := by
  unfold bs; nlinarith

/-- Ring start times are nonnegative. -/
private lemma bs_nonneg {a : ℤ} (ha : 0 ≤ a) : 0 ≤ bs a := by unfold bs; nlinarith

/-- The visit time of `pos m k`. -/
private lemma Q_pos (m k : ℤ) (hm : 0 ≤ m) (hk : 0 ≤ k) (hk' : k ≤ 12 * m + 7) :
    Q (pos m k) = bs m + k := by
  obtain ⟨h1, h2⟩ := D2 m k hm hk hk'
  unfold Q; rw [h1, h2]

/-- Visit times are nonnegative. -/
private lemma Q_nonneg (v : Pt) : 0 ≤ Q v := by
  have := D1 v; have := rg_nonneg v; have := bs_nonneg (rg_nonneg v); unfold Q; omega

/-- Different vertices have different visit times. -/
private lemma Q_inj {u v : Pt} (h : Q u = Q v) : u = v := by
  have hu := D1 u; have hv := D1 v
  have h0u := rg_nonneg u; have h0v := rg_nonneg v
  unfold Q at h
  have hr : rg u = rg v := by
    rcases lt_trichotomy (rg u) (rg v) with h1 | h1 | h1
    · have := bs_mono h0u h1; omega
    · exact h1
    · have := bs_mono h0v h1; omega
  have ho : off u = off v := by rw [hr] at h; omega
  rw [← hu.2.2, ← hv.2.2, hr, ho]

/-- `pos` on side `A` of a ring (extended range). -/
private lemma pos_A (m k : ℤ) (_hm : 0 ≤ m) (h0 : 0 ≤ k) (h1 : k ≤ 2 * m + 1) :
    pos m k = (-2 * m + (k + 1) / 2, -(k / 2)) := by
  unfold pos; split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/-- `pos` on side `B` of a ring. -/
private lemma pos_B (m k : ℤ) (_hm : 0 ≤ m) (h0 : 2 * m ≤ k) (h1 : k ≤ 4 * m + 2) :
    pos m k = (k - 3 * m, -m) := by
  unfold pos; split_ifs <;> rw [Prod.mk.injEq] <;> omega

/-- `pos` on side `C` of a ring (extended range). -/
private lemma pos_C (m k : ℤ) (hm : 0 ≤ m) (h0 : 4 * m + 1 ≤ k) (h1 : k ≤ 6 * m + 3) :
    pos m k = (m + 2 + (k - 4 * m - 2) / 2, -m + (k - 4 * m - 1) / 2) := by
  unfold pos; split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/-- `pos` on side `D` of a ring (extended range). -/
private lemma pos_D (m k : ℤ) (hm : 0 ≤ m) (h0 : 6 * m + 2 ≤ k) (h1 : k ≤ 8 * m + 4) :
    pos m k = (2 * m + 2 - (k - 6 * m - 2) / 2, (k - 6 * m - 1) / 2) := by
  unfold pos; split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/-- `pos` on side `E` of a ring. -/
private lemma pos_E (m k : ℤ) (hm : 0 ≤ m) (h0 : 8 * m + 3 ≤ k) (h1 : k ≤ 10 * m + 7) :
    pos m k = (9 * m + 5 - k, m + 1) := by
  unfold pos; split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/-- `pos` on side `F` of a ring (and beyond). -/
private lemma pos_F (m k : ℤ) (hm : 0 ≤ m) (h0 : 10 * m + 6 ≤ k) :
    pos m k = (-m - 2 - (k - 10 * m - 7) / 2, m + 1 - (k - 10 * m - 6) / 2) := by
  unfold pos; split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/-- `turns` in explicit coordinates. -/
private lemma turns_eq (p : Pt) (x y : ℤ) : turns p (x, y) =
    if (x + y) % 2 = 0 then
      (if p = (x + 1, y) then ((x - 1, y), (x, y + 1))
       else if p = (x, y + 1) then ((x + 1, y), (x - 1, y)) else ((x, y + 1), (x + 1, y)))
    else
      (if p = (x + 1, y) then ((x, y - 1), (x - 1, y))
       else if p = (x - 1, y) then ((x + 1, y), (x, y - 1)) else ((x - 1, y), (x + 1, y))) := by
  simp only [turns, nbrs]
  split_ifs <;> rfl

/-- The local step property at `v`, coming from `p`, with intended next vertex `n`: either the left
turn is `n`, or the left turn is an earlier vertex and the right turn is `n`. -/
private def LLgoal (p v n : Pt) (m k : ℤ) : Prop :=
  (turns p v).1 = n ∨ ((turns p v).2 = n ∧ ∃ m' k', 0 ≤ m' ∧ 0 ≤ k' ∧ k' ≤ 12 * m' + 7 ∧
    (m' < m ∨ (m' = m ∧ k' < k)) ∧ (turns p v).1 = pos m' k')

set_option maxHeartbeats 4000000 in
/-- The local step property for a generic vertex of ring `m ≥ 1`. -/
private lemma LL_gen (m k : ℤ) (hm : 1 ≤ m) (hk1 : 1 ≤ k) (hk2 : k ≤ 12 * m + 6) :
    LLgoal (pos m (k - 1)) (pos m k) (pos m (k + 1)) m k := by
  unfold LLgoal
  rcases (by omega : k ≤ 2 * m ∨ (2 * m + 1 ≤ k ∧ k ≤ 4 * m + 1) ∨ k = 4 * m + 2 ∨
      (4 * m + 3 ≤ k ∧ k ≤ 6 * m + 2) ∨ (6 * m + 3 ≤ k ∧ k ≤ 8 * m + 3) ∨
      (8 * m + 4 ≤ k ∧ k ≤ 10 * m + 6) ∨ k = 10 * m + 7 ∨ 10 * m + 8 ≤ k) with
    h | h | h | h | h | h | h | h
  · rw [pos_A m k (by omega) (by omega) (by omega), pos_A m (k - 1) (by omega) (by omega) (by omega),
      pos_A m (k + 1) (by omega) (by omega) (by omega), turns_eq]
    simp only [Prod.mk.injEq]
    split_ifs <;> simp only [Prod.mk.injEq] <;> first
      | omega
      | (left; omega)
      | (right; refine ⟨by omega, m - 1, k - 1, by omega, by omega, by omega, by omega, ?_⟩
         rw [pos_A (m - 1) (k - 1) (by omega) (by omega) (by omega)]; simp only [Prod.mk.injEq]; omega)
  · rw [pos_B m k (by omega) (by omega) (by omega), pos_B m (k - 1) (by omega) (by omega) (by omega),
      pos_B m (k + 1) (by omega) (by omega) (by omega), turns_eq]
    simp only [Prod.mk.injEq, and_true]
    split_ifs <;> simp only [Prod.mk.injEq, and_true] <;> first
      | omega
      | (left; omega)
      | (right; refine ⟨by omega, m - 1, k - 3, by omega, by omega, by omega, by omega, ?_⟩
         rw [pos_B (m - 1) (k - 3) (by omega) (by omega) (by omega)]; simp only [Prod.mk.injEq]; omega)
  · rw [pos_B m k (by omega) (by omega) (by omega), pos_B m (k - 1) (by omega) (by omega) (by omega),
      pos_C m (k + 1) (by omega) (by omega) (by omega), turns_eq]
    simp only [Prod.mk.injEq, and_true]
    split_ifs <;> simp only [Prod.mk.injEq] <;> first
      | omega
  · rw [pos_C m k (by omega) (by omega) (by omega), pos_C m (k - 1) (by omega) (by omega) (by omega),
      pos_C m (k + 1) (by omega) (by omega) (by omega), turns_eq]
    simp only [Prod.mk.injEq]
    split_ifs <;> simp only [Prod.mk.injEq] <;> first
      | omega
      | (left; omega)
      | (right; refine ⟨by omega, m - 1, k - 5, by omega, by omega, by omega, by omega, ?_⟩
         rw [pos_C (m - 1) (k - 5) (by omega) (by omega) (by omega)]; simp only [Prod.mk.injEq]; omega)
  · rw [pos_D m k (by omega) (by omega) (by omega), pos_D m (k - 1) (by omega) (by omega) (by omega),
      pos_D m (k + 1) (by omega) (by omega) (by omega), turns_eq]
    simp only [Prod.mk.injEq]
    split_ifs <;> simp only [Prod.mk.injEq] <;> first
      | omega
      | (left; omega)
      | (right; refine ⟨by omega, m - 1, k - 7, by omega, by omega, by omega, by omega, ?_⟩
         rw [pos_D (m - 1) (k - 7) (by omega) (by omega) (by omega)]; simp only [Prod.mk.injEq]; omega)
  · rw [pos_E m k (by omega) (by omega) (by omega), pos_E m (k - 1) (by omega) (by omega) (by omega),
      pos_E m (k + 1) (by omega) (by omega) (by omega), turns_eq]
    simp only [Prod.mk.injEq, and_true]
    split_ifs <;> simp only [Prod.mk.injEq, and_true] <;> first
      | omega
      | (left; omega)
      | (right; refine ⟨by omega, m - 1, k - 9, by omega, by omega, by omega, by omega, ?_⟩
         rw [pos_E (m - 1) (k - 9) (by omega) (by omega) (by omega)]; simp only [Prod.mk.injEq]; omega)
  · rw [pos_E m k (by omega) (by omega) (by omega), pos_E m (k - 1) (by omega) (by omega) (by omega),
      pos_F m (k + 1) (by omega) (by omega), turns_eq]
    simp only [Prod.mk.injEq, and_true]
    split_ifs <;> simp only [Prod.mk.injEq] <;> first
      | omega
  · rw [pos_F m k (by omega) (by omega), pos_F m (k - 1) (by omega) (by omega),
      pos_F m (k + 1) (by omega) (by omega), turns_eq]
    simp only [Prod.mk.injEq]
    split_ifs <;> simp only [Prod.mk.injEq] <;> first
      | omega
      | (left; omega)
      | (right; refine ⟨by omega, m - 1, k - 11, by omega, by omega, by omega, by omega, ?_⟩
         rw [pos_F (m - 1) (k - 11) (by omega) (by omega)]; simp only [Prod.mk.injEq]; omega)

/-- The local step property at the first vertex of a ring. -/
private lemma LL_start (m : ℤ) (hm : 1 ≤ m) :
    LLgoal (pos (m - 1) (12 * m - 5)) (pos m 0) (pos m 1) m 0 := by
  unfold LLgoal
  rw [pos_F (m - 1) (12 * m - 5) (by omega) (by omega), pos_A m 0 (by omega) (by omega) (by omega),
    pos_A m 1 (by omega) (by omega) (by omega), turns_eq]
  simp only [Prod.mk.injEq]
  split_ifs <;> simp only [Prod.mk.injEq] <;> first
      | omega

/-- The local step property at the last vertex of a ring. -/
private lemma LL_end (m : ℤ) (hm : 0 ≤ m) :
    LLgoal (pos m (12 * m + 6)) (pos m (12 * m + 7)) (pos (m + 1) 0) m (12 * m + 7) := by
  unfold LLgoal
  rw [pos_F m (12 * m + 6) (by omega) (by omega), pos_F m (12 * m + 7) (by omega) (by omega),
    pos_A (m + 1) 0 (by omega) (by omega) (by omega), turns_eq]
  simp only [Prod.mk.injEq]
  split_ifs <;> simp only [Prod.mk.injEq] <;> first
      | omega

/-- The local step property in ring `0`. -/
private lemma LL_zero (k : ℤ) (hk1 : 1 ≤ k) (hk2 : k ≤ 6) :
    LLgoal (pos 0 (k - 1)) (pos 0 k) (pos 0 (k + 1)) 0 k := by
  unfold LLgoal
  interval_cases k
  · rw [show pos 0 (1 - 1) = (0, 0) by decide, show pos 0 1 = (1, 0) by decide,
      show pos 0 (1 + 1) = (2, 0) by decide, turns_eq]
    norm_num
  · rw [show pos 0 (2 - 1) = (1, 0) by decide, show pos 0 2 = (2, 0) by decide,
      show pos 0 (2 + 1) = (2, 1) by decide, turns_eq]
    norm_num
  · rw [show pos 0 (3 - 1) = (2, 0) by decide, show pos 0 3 = (2, 1) by decide,
      show pos 0 (3 + 1) = (1, 1) by decide, turns_eq]
    norm_num
  · rw [show pos 0 (4 - 1) = (2, 1) by decide, show pos 0 4 = (1, 1) by decide,
      show pos 0 (4 + 1) = (0, 1) by decide, turns_eq]
    norm_num
  · rw [show pos 0 (5 - 1) = (1, 1) by decide, show pos 0 5 = (0, 1) by decide,
      show pos 0 (5 + 1) = (-1, 1) by decide, turns_eq]
    norm_num
    exact ⟨0, le_rfl, 0, le_rfl, by norm_num, by norm_num, by decide⟩
  · rw [show pos 0 (6 - 1) = (0, 1) by decide, show pos 0 6 = (-1, 1) by decide,
      show pos 0 (6 + 1) = (-2, 1) by decide, turns_eq]
    norm_num

/-- The ring/offset pair visited just before `(m, k)`. -/
private def prv (m k : ℤ) : ℤ × ℤ := if k = 0 then (m - 1, 12 * m - 5) else (m, k - 1)

/-- The ring/offset pair visited just after `(m, k)`. -/
private def nxt (m k : ℤ) : ℤ × ℤ := if k = 12 * m + 7 then (m + 1, 0) else (m, k + 1)

/-- The local step property at every vertex other than the start. -/
private lemma LL (m k : ℤ) (hm : 0 ≤ m) (hk : 0 ≤ k) (hk' : k ≤ 12 * m + 7) (h0 : 0 < m ∨ 0 < k) :
    LLgoal (pos (prv m k).1 (prv m k).2) (pos m k) (pos (nxt m k).1 (nxt m k).2) m k := by
  by_cases hk0 : k = 0
  · subst hk0
    have : nxt m 0 = (m, 0 + 1) := by unfold nxt; rw [if_neg (by omega)]
    rw [this]; unfold prv; simp only [if_true]
    exact LL_start m (by omega)
  · have hp : prv m k = (m, k - 1) := by unfold prv; rw [if_neg hk0]
    rw [hp]
    by_cases hk7 : k = 12 * m + 7
    · subst hk7
      have : nxt m (12 * m + 7) = (m + 1, 0) := by unfold nxt; simp
      rw [this]
      have e : 12 * m + 7 - 1 = 12 * m + 6 := by ring
      simp only; rw [e]
      exact LL_end m hm
    · have : nxt m k = (m, k + 1) := by unfold nxt; rw [if_neg hk7]
      rw [this]
      rcases (by omega : m = 0 ∨ 1 ≤ m) with h | h
      · subst h; exact LL_zero k (by omega) (by omega)
      · exact LL_gen m k h (by omega) (by omega)

/-- `step` on a list with at least two entries. -/
private lemma step_cons (v p : Pt) (rest : List Pt) :
    step (v :: p :: rest) =
      if (turns p v).1 ∉ v :: p :: rest then (turns p v).1 :: v :: p :: rest
      else if (turns p v).2 ∉ v :: p :: rest then (turns p v).2 :: v :: p :: rest
      else v :: p :: rest := rfl

/-- One more toothpick is one more `step`. -/
private lemma walk_succ (t : ℕ) (ht : 1 ≤ t) : walk (t + 1) = step (walk t) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [walk]
  exact Function.iterate_succ_apply' step s _

/-- Lexicographic order on ring/offset pairs gives the order of visit times. -/
private lemma Q_lex {m k m' k' : ℤ} (hm' : 0 ≤ m') (hk' : k' ≤ 12 * m' + 7) (hk : 0 ≤ k)
    (h : m' < m ∨ (m' = m ∧ k' < k)) : bs m' + k' < bs m + k := by
  rcases h with h | ⟨rfl, h⟩
  · have := bs_mono hm' h; omega
  · omega

/-- The predecessor is visited one step earlier. -/
private lemma Q_prv (m k : ℤ) (hm : 0 ≤ m) (hk : 0 ≤ k) (hk' : k ≤ 12 * m + 7) (h0 : 0 < m ∨ 0 < k) :
    Q (pos (prv m k).1 (prv m k).2) + 1 = bs m + k := by
  unfold prv; split_ifs with h
  · simp only
    rw [Q_pos (m - 1) (12 * m - 5) (by omega) (by omega) (by omega)]
    have := bs_succ (m - 1); rw [sub_add_cancel] at this; omega
  · simp only
    rw [Q_pos m (k - 1) (by omega) (by omega) (by omega)]; ring

/-- The successor is visited one step later. -/
private lemma Q_nxt (m k : ℤ) (hm : 0 ≤ m) (hk : 0 ≤ k) (hk' : k ≤ 12 * m + 7) :
    Q (pos (nxt m k).1 (nxt m k).2) = bs m + k + 1 := by
  unfold nxt; split_ifs with h
  · simp only
    rw [Q_pos (m + 1) 0 (by omega) (by omega) (by omega), bs_succ]; omega
  · simp only
    rw [Q_pos m (k + 1) (by omega) (by omega) (by omega)]; ring

/-- `(1, 0)` is visited at time `1`. -/
private lemma Q10 : Q (1, 0) = 1 := by
  have := Q_pos 0 1 (by norm_num) (by norm_num) (by norm_num)
  rw [show pos 0 1 = (1, 0) by decide] at this
  rw [this]; norm_num [bs]

/-- `(0, 0)` is visited at time `0`. -/
private lemma Q00 : Q (0, 0) = 0 := by
  have := Q_pos 0 0 (by norm_num) (by norm_num) (by norm_num)
  rw [show pos 0 0 = (0, 0) by decide] at this
  rw [this]; norm_num [bs]

/-- The walk invariant: after `t ≥ 1` toothpicks the walk ends at the vertices with visit times `t`
and `t - 1`, and covers exactly the vertices with visit time at most `t`. -/
private lemma inv (t : ℕ) (ht : 1 ≤ t) : ∃ v p rest, walk t = v :: p :: rest ∧ Q v = t ∧ Q p + 1 = t ∧
    ∀ u, u ∈ walk t ↔ Q u ≤ t := by
  induction t, ht using Nat.le_induction with
  | base =>
    refine ⟨(1, 0), (0, 0), [], rfl, by rw [Q10]; norm_num, by rw [Q00]; norm_num, ?_⟩
    intro u
    constructor
    · intro h
      change u ∈ [(1, 0), (0, 0)] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · rw [Q10]; norm_num
      · rw [Q00]; norm_num
    · intro h
      have h0 := Q_nonneg u
      change u ∈ [(1, 0), (0, 0)]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases (by have := Q10; have := Q00; push_cast at h; omega : Q u = Q (1, 0) ∨ Q u = Q (0, 0)) with h1 | h1
      · exact Or.inl (Q_inj h1)
      · exact Or.inr (Q_inj h1)
  | succ t ht ih =>
    obtain ⟨v, p, rest, hw, hv, hp, hmem⟩ := ih
    obtain ⟨hk0, hk1, hpos⟩ := D1 v
    have hm0 := rg_nonneg v
    have hQv : Q v = bs (rg v) + off v := rfl
    have h0 : 0 < rg v ∨ 0 < off v := by
      by_contra hc
      have e1 : rg v = 0 := by omega
      have e2 : off v = 0 := by omega
      rw [e1, e2] at hQv; norm_num [bs] at hQv; omega
    have hpp : pos (prv (rg v) (off v)).1 (prv (rg v) (off v)).2 = p := by
      apply Q_inj
      have := Q_prv (rg v) (off v) hm0 hk0 hk1 h0
      omega
    have hQn := Q_nxt (rg v) (off v) hm0 hk0 hk1
    have hL := LL (rg v) (off v) hm0 hk0 hk1 h0
    rw [hpp, hpos] at hL
    set n := pos (nxt (rg v) (off v)).1 (nxt (rg v) (off v)).2 with hn
    have hnmem : n ∉ walk t := by
      rw [hmem]; omega
    rw [walk_succ t ht, hw, step_cons]
    rw [hw] at hnmem hmem
    have key : ∀ u, u ∈ n :: v :: p :: rest ↔ Q u ≤ ((t + 1 : ℕ) : ℤ) := by
      intro u
      rw [List.mem_cons, hmem]
      push_cast
      constructor
      · rintro (rfl | h)
        · omega
        · omega
      · intro h
        by_cases h' : Q u ≤ t
        · exact Or.inr h'
        · left; apply Q_inj; omega
    rcases hL with hL | ⟨hR, m', k', hm', hk', hk'', hlex, hl⟩
    · rw [hL, if_pos hnmem]
      exact ⟨n, v, p :: rest, rfl, by push_cast; omega, by push_cast; omega, key⟩
    · have hlm : (turns p v).1 ∈ v :: p :: rest := by
        rw [hmem, hl, Q_pos m' k' hm' hk' hk'']
        have := Q_lex hm' hk'' hk0 hlex
        omega
      rw [if_neg (not_not.mpr hlm), hR, if_pos hnmem]
      exact ⟨n, v, p :: rest, rfl, by push_cast; omega, by push_cast; omega, key⟩

/-- The vertices covered after `t` toothpicks are exactly those with visit time at most `t`. -/
private lemma mem_walk (t : ℕ) (u : Pt) : u ∈ walk t ↔ Q u ≤ t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp only [walk, List.mem_cons, List.not_mem_nil, or_false, Nat.cast_zero]
    constructor
    · rintro rfl; rw [Q00]
    · intro h; have := Q_nonneg u; apply Q_inj; rw [Q00]; omega
  · obtain ⟨_, _, _, _, _, _, h⟩ := inv t ht
    exact h u

/-- The lower-left corner of cell number `s` (`1 ≤ s ≤ 6 j`) of cell ring `j`; `cpos 0 0` is the
central cell. -/
private def cpos (j s : ℤ) : Pt :=
  if s ≤ j then (-j - s, j - s)
  else if s ≤ 2 * j then (s - 3 * j, j - s)
  else if s ≤ 3 * j then (2 * s - 5 * j, -j)
  else if s ≤ 4 * j then (s - 2 * j, s - 4 * j)
  else if s ≤ 5 * j then (6 * j - s, s - 4 * j)
  else (11 * j - 2 * s, j)

/-- Valid cell ring/index pairs. -/
private def validC (j s : ℤ) : Prop := (j = 0 ∧ s = 0) ∨ (1 ≤ j ∧ 1 ≤ s ∧ s ≤ 6 * j)

/-- `cpos` gives cell corners. -/
private lemma cpos_even (j s : ℤ) : ((cpos j s).1 + (cpos j s).2) % 2 = 0 := by
  unfold cpos; split_ifs <;> omega

set_option maxHeartbeats 4000000 in
/-- Every cell is some `cpos j s`. -/
private lemma cpos_surj (c : Pt) (hc : (c.1 + c.2) % 2 = 0) : ∃ j s, validC j s ∧ cpos j s = c := by
  obtain ⟨x, y⟩ := c
  simp only at hc
  unfold validC
  obtain ⟨q, hq⟩ : ∃ q, x = 2 * q + y := ⟨(x - y) / 2, by omega⟩
  subst hq
  rcases (by omega : (q = 0 ∧ y = 0) ∨ (q < 0 ∧ 0 ≤ y ∧ y < -q) ∨ (y ≤ 0 ∧ q ≤ 0 ∧ q + y < 0) ∨
      (y < 0 ∧ 0 ≤ q ∧ q ≤ -y) ∨ (0 < q ∧ -q ≤ y ∧ y ≤ 0) ∨ (0 ≤ y ∧ 0 ≤ q ∧ 0 < q + y) ∨
      (0 < y ∧ -y ≤ q ∧ q ≤ 0)) with h | h | h | h | h | h | h
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, 0, by omega, by decide⟩
  · exact ⟨-q, -q - y, by omega, by unfold cpos; split_ifs <;> simp only [Prod.mk.injEq] <;> omega⟩
  · exact ⟨-q - y, -q - 2 * y, by omega, by unfold cpos; split_ifs <;> simp only [Prod.mk.injEq] <;> omega⟩
  · exact ⟨-y, q - 2 * y, by omega, by unfold cpos; split_ifs <;> simp only [Prod.mk.injEq] <;> omega⟩
  · exact ⟨q, y + 4 * q, by omega, by unfold cpos; split_ifs <;> simp only [Prod.mk.injEq] <;> omega⟩
  · exact ⟨q + y, 4 * q + 5 * y, by omega, by unfold cpos; split_ifs <;> simp only [Prod.mk.injEq] <;> omega⟩
  · exact ⟨y, 5 * y - q, by omega, by unfold cpos; split_ifs <;> simp only [Prod.mk.injEq, and_true] <;> omega⟩

set_option maxHeartbeats 4000000 in
/-- `cpos` is injective on valid pairs. -/
private lemma cpos_inj {j s j' s' : ℤ} (h : validC j s) (h' : validC j' s') (e : cpos j s = cpos j' s') :
    j = j' ∧ s = s' := by
  unfold validC at h h'
  unfold cpos at e
  split_ifs at e <;> simp only [Prod.mk.injEq] at e <;> omega

/-- One more than the number of corners of the cell ring passed by cell `s` of ring `j`. -/
private def cc (j s : ℤ) : ℤ :=
  if s < j then 1 else if s < 2 * j then 2 else if s < 3 * j then 3
  else if s < 4 * j then 4 else if s < 5 * j then 5 else 6

/-- The time at which cell `s` of cell ring `j` becomes ON. -/
private def Tz (j s : ℤ) : ℤ := 6 * j * j - 1 + 2 * s + cc j s

/-- Comparison of visit times through ring and offset. -/
private lemma Q_le_lex (u : Pt) (mw kw : ℤ) (_hmw : 0 ≤ mw) (hkw : 0 ≤ kw)
    (h : rg u < mw ∨ (rg u = mw ∧ off u ≤ kw)) : Q u ≤ bs mw + kw := by
  have hu := D1 u; have h0 := rg_nonneg u
  unfold Q
  rcases h with h | ⟨h1, h2⟩
  · have := bs_mono h0 h; omega
  · rw [h1]; omega

/-- The vertices of the central cell are visited by time `5`. -/
private lemma cv00 : ∀ u ∈ cellVerts (0, 0), rg u < 0 ∨ (rg u = 0 ∧ off u ≤ 5) := by decide

set_option maxHeartbeats 4000000 in
/-- Vertex comparison for cells on side 0 of a cell ring. -/
private lemma cv0 (j s : ℤ) (hj : 1 ≤ j) (h1 : 1 ≤ s) (h2 : s ≤ j - 1) :
    ∀ u ∈ cellVerts (-j - s, j - s),
      rg u < j - 1 ∨ (rg u = j - 1 ∧ off u ≤ 10 * j + 2 * s - 4) := by
  intro u hu
  simp only [cellVerts, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> (unfold off offm rg; simp only; omega)

set_option maxHeartbeats 4000000 in
/-- Vertex comparison for cells on side 1 of a cell ring. -/
private lemma cv1 (j s : ℤ) (hj : 1 ≤ j) (h1 : j ≤ s) (h2 : s ≤ 2 * j - 1) :
    ∀ u ∈ cellVerts (s - 3 * j, j - s), rg u < j ∨ (rg u = j ∧ off u ≤ 2 * s - 2 * j + 1) := by
  intro u hu
  simp only [cellVerts, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> (unfold off offm rg; simp only; omega)

set_option maxHeartbeats 4000000 in
/-- Vertex comparison for cells on side 2 of a cell ring. -/
private lemma cv2 (j s : ℤ) (hj : 1 ≤ j) (h1 : 2 * j ≤ s) (h2 : s ≤ 3 * j - 1) :
    ∀ u ∈ cellVerts (2 * s - 5 * j, -j), rg u < j ∨ (rg u = j ∧ off u ≤ 2 * s - 2 * j + 2) := by
  intro u hu
  simp only [cellVerts, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> (unfold off offm rg; simp only; omega)

set_option maxHeartbeats 4000000 in
/-- Vertex comparison for cells on side 3 of a cell ring. -/
private lemma cv3 (j s : ℤ) (hj : 1 ≤ j) (h1 : 3 * j ≤ s) (h2 : s ≤ 4 * j - 1) :
    ∀ u ∈ cellVerts (s - 2 * j, s - 4 * j), rg u < j ∨ (rg u = j ∧ off u ≤ 2 * s - 2 * j + 3) := by
  intro u hu
  simp only [cellVerts, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> (unfold off offm rg; simp only; omega)

set_option maxHeartbeats 4000000 in
/-- Vertex comparison for cells on side 4 of a cell ring. -/
private lemma cv4 (j s : ℤ) (hj : 1 ≤ j) (h1 : 4 * j ≤ s) (h2 : s ≤ 5 * j - 1) :
    ∀ u ∈ cellVerts (6 * j - s, s - 4 * j), rg u < j ∨ (rg u = j ∧ off u ≤ 2 * s - 2 * j + 4) := by
  intro u hu
  simp only [cellVerts, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> (unfold off offm rg; simp only; omega)

set_option maxHeartbeats 4000000 in
/-- Vertex comparison for cells on side 5 of a cell ring. -/
private lemma cv5 (j s : ℤ) (hj : 1 ≤ j) (h1 : 5 * j ≤ s) (h2 : s ≤ 6 * j) :
    ∀ u ∈ cellVerts (11 * j - 2 * s, j), rg u < j ∨ (rg u = j ∧ off u ≤ 2 * s - 2 * j + 5) := by
  intro u hu
  simp only [cellVerts, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> (unfold off offm rg; simp only; omega)

/-- All six vertices of cell `(j, s)` are covered by time `Tz j s`, and one of them exactly then. -/
private lemma cell_complete (j s : ℤ) (hv : validC j s) :
    (∀ u ∈ cellVerts (cpos j s), Q u ≤ Tz j s) ∧ (∃ u ∈ cellVerts (cpos j s), Q u = Tz j s) := by
  unfold validC at hv
  rcases hv with ⟨rfl, rfl⟩ | ⟨hj, hs1, hs2⟩
  · have e : cpos 0 0 = (0, 0) := by decide
    have hT : Tz 0 0 = bs 0 + 5 := by decide
    rw [e, hT]
    refine ⟨fun u hu => Q_le_lex u 0 5 le_rfl (by norm_num) (cv00 u hu), (0, 1),
      by simp [cellVerts], ?_⟩
    rw [show ((0 : ℤ), (1 : ℤ)) = pos 0 5 by decide, Q_pos 0 5 (by norm_num) (by norm_num) (by norm_num)]
  · rcases (by omega : s ≤ j - 1 ∨ (j ≤ s ∧ s ≤ 2 * j - 1) ∨ (2 * j ≤ s ∧ s ≤ 3 * j - 1) ∨
        (3 * j ≤ s ∧ s ≤ 4 * j - 1) ∨ (4 * j ≤ s ∧ s ≤ 5 * j - 1) ∨ 5 * j ≤ s) with h | h | h | h | h | h
    · have e : cpos j s = (-j - s, j - s) := by unfold cpos; rw [if_pos (by omega)]
      have hT : Tz j s = bs (j - 1) + (10 * j + 2 * s - 4) := by
        unfold Tz cc bs; rw [if_pos (by omega)]; ring
      have hw : pos (j - 1) (10 * j + 2 * s - 4) = (-j - s, j - s) := by
        rw [pos_F _ _ (by omega) (by omega)]; simp only [Prod.mk.injEq]; omega
      rw [e, hT]
      refine ⟨fun u hu => Q_le_lex u _ _ (by omega) (by omega) (cv0 j s hj hs1 h u hu),
        (-j - s, j - s), by simp [cellVerts], ?_⟩
      rw [← hw, Q_pos _ _ (by omega) (by omega) (by omega)]
    · have e : cpos j s = (s - 3 * j, j - s) := by
        unfold cpos; split_ifs <;> simp only [Prod.mk.injEq, and_true] <;> omega
      have hT : Tz j s = bs j + (2 * s - 2 * j + 1) := by
        unfold Tz cc bs; rw [if_neg (by omega), if_pos (by omega)]; ring
      have hw : pos j (2 * s - 2 * j + 1) = (s - 3 * j + 1, j - s) := by
        rw [pos_A _ _ (by omega) (by omega) (by omega)]; simp only [Prod.mk.injEq]; omega
      rw [e, hT]
      refine ⟨fun u hu => Q_le_lex u _ _ (by omega) (by omega) (cv1 j s hj h.1 h.2 u hu),
        (s - 3 * j + 1, j - s), by simp [cellVerts], ?_⟩
      rw [← hw, Q_pos _ _ (by omega) (by omega) (by omega)]
    · have e : cpos j s = (2 * s - 5 * j, -j) := by
        unfold cpos; split_ifs <;> simp only [Prod.mk.injEq] <;> omega
      have hT : Tz j s = bs j + (2 * s - 2 * j + 2) := by
        unfold Tz cc bs; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; ring
      have hw : pos j (2 * s - 2 * j + 2) = (2 * s - 5 * j + 2, -j) := by
        rw [pos_B _ _ (by omega) (by omega) (by omega)]; simp only [Prod.mk.injEq, and_true]; omega
      rw [e, hT]
      refine ⟨fun u hu => Q_le_lex u _ _ (by omega) (by omega) (cv2 j s hj h.1 h.2 u hu),
        (2 * s - 5 * j + 2, -j), by simp [cellVerts], ?_⟩
      rw [← hw, Q_pos _ _ (by omega) (by omega) (by omega)]
    · have e : cpos j s = (s - 2 * j, s - 4 * j) := by
        unfold cpos; split_ifs <;> simp only [Prod.mk.injEq, and_true] <;> omega
      have hT : Tz j s = bs j + (2 * s - 2 * j + 3) := by
        unfold Tz cc bs
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; ring
      have hw : pos j (2 * s - 2 * j + 3) = (s - 2 * j + 2, s - 4 * j + 1) := by
        rw [pos_C _ _ (by omega) (by omega) (by omega)]; simp only [Prod.mk.injEq]; omega
      rw [e, hT]
      refine ⟨fun u hu => Q_le_lex u _ _ (by omega) (by omega) (cv3 j s hj h.1 h.2 u hu),
        (s - 2 * j + 2, s - 4 * j + 1), by simp [cellVerts], ?_⟩
      rw [← hw, Q_pos _ _ (by omega) (by omega) (by omega)]
    · have e : cpos j s = (6 * j - s, s - 4 * j) := by
        unfold cpos; split_ifs <;> simp only [Prod.mk.injEq, and_true] <;> omega
      have hT : Tz j s = bs j + (2 * s - 2 * j + 4) := by
        unfold Tz cc bs
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos (by omega)]; ring
      have hw : pos j (2 * s - 2 * j + 4) = (6 * j - s + 1, s - 4 * j + 1) := by
        rw [pos_D _ _ (by omega) (by omega) (by omega)]; simp only [Prod.mk.injEq]; omega
      rw [e, hT]
      refine ⟨fun u hu => Q_le_lex u _ _ (by omega) (by omega) (cv4 j s hj h.1 h.2 u hu),
        (6 * j - s + 1, s - 4 * j + 1), by simp [cellVerts], ?_⟩
      rw [← hw, Q_pos _ _ (by omega) (by omega) (by omega)]
    · have e : cpos j s = (11 * j - 2 * s, j) := by
        unfold cpos; split_ifs <;> simp only [Prod.mk.injEq] <;> omega
      have hT : Tz j s = bs j + (2 * s - 2 * j + 5) := by
        unfold Tz cc bs
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega)]; ring
      have hw : pos j (2 * s - 2 * j + 5) = (11 * j - 2 * s, j + 1) := by
        rw [pos_E _ _ (by omega) (by omega) (by omega)]; simp only [Prod.mk.injEq, and_true]; omega
      rw [e, hT]
      refine ⟨fun u hu => Q_le_lex u _ _ (by omega) (by omega) (cv5 j s hj h hs2 u hu),
        (11 * j - 2 * s, j + 1), by simp [cellVerts], ?_⟩
      rw [← hw, Q_pos _ _ (by omega) (by omega) (by omega)]

/-- The integer squeeze behind `⌈√(12 n - 3)⌉ = 6 j - 3 + cc j s`. -/
private lemma cc_bounds (j s : ℤ) (hv : validC j s) :
    (6 * j - 4 + cc j s) ^ 2 < 36 * j * j - 36 * j + 9 + 12 * s ∧
    36 * j * j - 36 * j + 9 + 12 * s ≤ (6 * j - 3 + cc j s) ^ 2 ∧ 1 ≤ 6 * j - 4 + cc j s := by
  unfold validC at hv
  rcases hv with ⟨rfl, rfl⟩ | ⟨hj, hs1, hs2⟩
  · decide
  · unfold cc
    split_ifs with h1 h2 h3 h4 h5
    · refine ⟨by nlinarith, by nlinarith, by omega⟩
    · refine ⟨by nlinarith, by nlinarith, by omega⟩
    · refine ⟨by nlinarith, by nlinarith, by omega⟩
    · refine ⟨by nlinarith, by nlinarith, by omega⟩
    · refine ⟨by nlinarith, by nlinarith, by omega⟩
    · refine ⟨by nlinarith, by nlinarith, by omega⟩

/-- The conjectured value `2 n + ⌈√(12 n - 3)⌉`. -/
private noncomputable def TT (n : ℕ) : ℕ := 2 * n + ⌈Real.sqrt (12 * (n : ℝ) - 3)⌉₊

/-- The conjectured value at the index of cell `(j, s)` is the time `Tz j s` at which that cell
turns ON. -/
private lemma TT_eq (j s : ℤ) (hv : validC j s) (n : ℕ) (hn : (n : ℤ) = 3 * j * (j - 1) + 1 + s) :
    (TT n : ℤ) = Tz j s := by
  obtain ⟨h1, h2, h3⟩ := cc_bounds j s hv
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = 6 * j - 4 + cc j s := ⟨(6 * j - 4 + cc j s).toNat, by omega⟩
  have hX : (36 * j * j - 36 * j + 9 + 12 * s : ℤ) = 12 * (n : ℤ) - 3 := by rw [hn]; ring
  rw [hX, ← hM] at h1
  rw [hX, show 6 * j - 3 + cc j s = (M : ℤ) + 1 by omega] at h2
  have r1 : ((M : ℝ)) ^ 2 < 12 * (n : ℝ) - 3 := by exact_mod_cast h1
  have r2 : 12 * (n : ℝ) - 3 ≤ ((M : ℝ) + 1) ^ 2 := by exact_mod_cast h2
  have hc : ⌈Real.sqrt (12 * (n : ℝ) - 3)⌉₊ = M + 1 := by
    apply le_antisymm
    · rw [Nat.ceil_le, Real.sqrt_le_left (by positivity)]
      push_cast; exact r2
    · rw [Nat.succ_le_iff, Nat.lt_ceil, Real.lt_sqrt (by positivity)]
      exact r1
  unfold TT Tz
  rw [hc]; push_cast
  rw [hn, hM]; ring

/-- The conjectured value is strictly increasing. -/
private lemma TT_mono {a b : ℕ} (h : a < b) : TT a < TT b := by
  unfold TT
  have : ⌈Real.sqrt (12 * (a : ℝ) - 3)⌉₊ ≤ ⌈Real.sqrt (12 * (b : ℝ) - 3)⌉₊ := by
    apply Nat.ceil_mono
    apply Real.sqrt_le_sqrt
    have : (a : ℝ) ≤ b := by exact_mod_cast h.le
    linarith
  omega

/-- The conjectured value is an order embedding. -/
private lemma TT_le_iff {a b : ℕ} : TT a ≤ TT b ↔ a ≤ b := by
  constructor
  · intro h; by_contra h'; have := TT_mono (not_le.mp h'); omega
  · intro h; rcases h.lt_or_eq with h | rfl
    · exact (TT_mono h).le
    · exact le_rfl

/-- The cell ring/index pair of the `n`-th cell of the spiral. -/
private def dec : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | 1 => (0, 0)
  | n + 2 => if (dec (n + 1)).2 = 6 * (dec (n + 1)).1 then ((dec (n + 1)).1 + 1, 1)
      else ((dec (n + 1)).1, (dec (n + 1)).2 + 1)

/-- `dec n` is valid and has index `n`. -/
private lemma dec_spec (a : ℕ) (ha : 1 ≤ a) :
    validC (dec a).1 (dec a).2 ∧ 3 * (dec a).1 * ((dec a).1 - 1) + 1 + (dec a).2 = a := by
  induction a, ha using Nat.le_induction with
  | base => refine ⟨Or.inl ⟨rfl, rfl⟩, by simp [dec]⟩
  | succ b hb ih =>
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    obtain ⟨hv, he⟩ := ih
    have hd : dec (c + 1 + 1) = if (dec (c + 1)).2 = 6 * (dec (c + 1)).1 then ((dec (c + 1)).1 + 1, 1)
      else ((dec (c + 1)).1, (dec (c + 1)).2 + 1) := rfl
    rw [hd]
    unfold validC at hv ⊢
    generalize dec (c + 1) = p at hv he ⊢
    obtain ⟨x, y⟩ := p
    simp only at hv he ⊢
    split_ifs with h
    · refine ⟨Or.inr ⟨by omega, le_rfl, by omega⟩, ?_⟩
      push_cast at he ⊢; linear_combination he - h
    · refine ⟨Or.inr ⟨by omega, by omega, by omega⟩, ?_⟩
      push_cast at he ⊢; linear_combination he

/-- Cell indices are positive. -/
private lemma Nidx_pos {j s : ℤ} (h : validC j s) : 1 ≤ 3 * j * (j - 1) + 1 + s := by
  unfold validC at h
  rcases h with ⟨rfl, rfl⟩ | ⟨h1, h2, _⟩
  · norm_num
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ j by omega) (show (0 : ℤ) ≤ j - 1 by omega)]

/-- The cell index is injective on valid pairs. -/
private lemma Nidx_inj {j s j' s' : ℤ} (h : validC j s) (h' : validC j' s')
    (e : 3 * j * (j - 1) + 1 + s = 3 * j' * (j' - 1) + 1 + s') : j = j' ∧ s = s' := by
  unfold validC at h h'
  have key : ∀ a b a' b' : ℤ, ((a = 0 ∧ b = 0) ∨ (1 ≤ a ∧ 1 ≤ b ∧ b ≤ 6 * a)) →
      ((a' = 0 ∧ b' = 0) ∨ (1 ≤ a' ∧ 1 ≤ b' ∧ b' ≤ 6 * a')) → a < a' →
      3 * a * (a - 1) + 1 + b < 3 * a' * (a' - 1) + 1 + b' := by
    intro a b a' b' ha ha' hlt
    have h0 : 0 ≤ a := by omega
    have := mul_nonneg (show (0 : ℤ) ≤ a' - a - 1 by omega) (show (0 : ℤ) ≤ a' + a by omega)
    rcases ha with ⟨rfl, rfl⟩ | ⟨_, _, hb⟩ <;> rcases ha' with ⟨rfl, rfl⟩ | ⟨_, hb', _⟩ <;> nlinarith
  rcases lt_trichotomy j j' with hl | rfl | hl
  · have := key _ _ _ _ h h' hl; omega
  · omega
  · have := key _ _ _ _ h' h hl; omega

/-- `dec` inverts the cell index. -/
private lemma dec_unique (j s : ℤ) (hv : validC j s) (a : ℕ) (ha : (a : ℤ) = 3 * j * (j - 1) + 1 + s) :
    dec a = (j, s) := by
  have ha1 : 1 ≤ a := by have := Nidx_pos hv; omega
  obtain ⟨hv', he'⟩ := dec_spec a ha1
  obtain ⟨e1, e2⟩ := Nidx_inj hv' hv (by rw [he', ha])
  exact Prod.ext e1 e2

/-- The ON cells after `t` toothpicks are the cells whose ON time is at most `t`. -/
private lemma mem_onCells (t : ℕ) (c : Pt) :
    c ∈ onCells (walk t) ↔ ∃ j s, validC j s ∧ cpos j s = c ∧ Tz j s ≤ t := by
  unfold onCells
  rw [Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨_, heven, hall⟩
    obtain ⟨j, s, hv, rfl⟩ := cpos_surj c heven
    obtain ⟨_, u, hu, hQ⟩ := cell_complete j s hv
    refine ⟨j, s, hv, rfl, ?_⟩
    rw [← hQ, ← mem_walk]
    exact hall u hu
  · rintro ⟨j, s, hv, rfl, hT⟩
    obtain ⟨hle, _⟩ := cell_complete j s hv
    refine ⟨?_, cpos_even j s, fun u hu => ?_⟩
    · rw [mem_walk]
      exact (hle _ (by simp [cellVerts])).trans hT
    · rw [mem_walk]
      exact (hle u hu).trans hT

/-- The ON time of the `a`-th cell is the conjectured value at `a`. -/
private lemma Tz_dec (a : ℕ) (ha : 1 ≤ a) : Tz (dec a).1 (dec a).2 = TT a :=
  (TT_eq _ _ (dec_spec a ha).1 a (dec_spec a ha).2.symm).symm

/-- Before the conjectured time, fewer than `n` cells are ON. -/
private lemma upper (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (ht : t < TT n) : onCount t ≤ n - 1 := by
  unfold onCount
  have hsub : onCells (walk t) ⊆ (Finset.Icc 1 (n - 1)).image (fun a => cpos (dec a).1 (dec a).2) := by
    intro c hc
    rw [mem_onCells] at hc
    obtain ⟨j, s, hv, rfl, hT⟩ := hc
    have hpos := Nidx_pos hv
    obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = 3 * j * (j - 1) + 1 + s :=
      ⟨(3 * j * (j - 1) + 1 + s).toNat, by omega⟩
    have hd := dec_unique j s hv a ha
    have hTa := TT_eq j s hv a ha
    have ha1 : 1 ≤ a := by omega
    have hlt : TT a < TT n := by omega
    have han : a < n := by
      by_contra h'; have := TT_le_iff.mpr (not_lt.mp h'); omega
    rw [Finset.mem_image]
    exact ⟨a, Finset.mem_Icc.mpr ⟨ha1, by omega⟩, by rw [hd]⟩
  calc (onCells (walk t)).card ≤ ((Finset.Icc 1 (n - 1)).image _).card := Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_image_le
    _ = n - 1 := by simp

/-- At the conjectured time, at least `n` cells are ON. -/
private lemma lower (n : ℕ) (_hn : 1 ≤ n) : n ≤ onCount (TT n) := by
  unfold onCount
  have hsub : (Finset.Icc 1 n).image (fun a => cpos (dec a).1 (dec a).2) ⊆ onCells (walk (TT n)) := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    rw [Finset.mem_Icc] at ha
    rw [mem_onCells]
    refine ⟨_, _, (dec_spec a ha.1).1, rfl, ?_⟩
    rw [Tz_dec a ha.1]
    exact_mod_cast TT_le_iff.mpr ha.2
  have hinj : Set.InjOn (fun a => cpos (dec a).1 (dec a).2) (Finset.Icc 1 n : Set ℕ) := by
    intro a ha b hb e
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    obtain ⟨hva, hea⟩ := dec_spec a ha.1
    obtain ⟨hvb, heb⟩ := dec_spec b hb.1
    obtain ⟨e1, e2⟩ := cpos_inj hva hvb e
    have : (a : ℤ) = b := by rw [← hea, ← heb, e1, e2]
    exact_mod_cast this
  calc n = (Finset.Icc 1 n).card := by simp
    _ = ((Finset.Icc 1 n).image _).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Librandi's conjecture holds: for every `n > 0`, `a(n) = 2n + ⌈√(12n - 3)⌉`. -/
theorem result : statement := by
  rw [statement_iff]
  intro n hn
  refine ⟨lower n hn, fun t ht => ?_⟩
  by_contra h
  have := upper n hn t (not_le.mp h)
  have ht' : n ≤ onCount t := ht
  omega

end Math0.Frontier.A182617

#math0_settles Math0.Frontier.A182617.result Math0.Statements.A182617.statement
