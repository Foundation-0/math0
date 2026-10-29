/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A300789
import Math0.Audit

/-!
# Domino-tileable Young diagrams are exactly the colour-balanced ones (A300789)

We prove Wiseman's conjecture from OEIS A300789: the Heinz numbers of partitions whose Young
diagram can be tiled by dominoes are exactly the Heinz numbers of partitions whose odd parts
occur as often in even as in odd positions. Hence `a n = b n` for all `n ≥ 1`.

Colour the cell `(i, j)` with the weight `(-1)^(i+j)`. A row `i` of length `y_i` has total
weight `(-1)^i [y_i odd]`, so the parity condition says that the diagram has total weight zero
(the "imbalance" `∑ (-1)^i [y_i odd]` vanishes).

* (tileable → balanced) Every domino covers two cells of opposite colour. We run this along the
  verified search `tileL` of the statement file: each step removes a cell and a neighbour.
* (balanced → tileable) Strong induction on the number of cells, with the row lengths as an
  antitone function `Y : ℕ → ℕ`. If some row has `Y i ≥ Y (i+1) + 2`, remove the horizontal
  domino at its end. If `Y i = Y (i+1) > Y (i+2)`, remove the vertical domino at the ends of
  rows `i, i+1`. Both moves keep the shape a partition and keep the imbalance. If neither move
  applies, the shape is a staircase `Y r = k - r`. All its odd rows have the same sign
  `(-1)^(k+1)`, so its imbalance is nonzero unless `k = 0`, the empty diagram.
-/

namespace Math0.Frontier.A300789
open Math0.Statements.A300789

/-- The chessboard weight `(-1)^(i+j)` of a cell `(i, j)`. -/
private def wt (c : ℕ × ℕ) : ℤ := (-1) ^ (c.1 + c.2)

/-- A list of cells accepted by `tileL` has total chessboard weight zero: each domino covers one
cell of each colour. -/
private theorem sum_wt_of_tileL : ∀ (fuel : ℕ) (l : List (ℕ × ℕ)), tileL fuel l = true →
    (l.map wt).sum = 0
  | _, [], _ => by simp
  | 0, _ :: _, h => by simp [tileL] at h
  | fuel + 1, c :: rest, h => by
    simp only [tileL, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨hx, ht⟩ | ⟨hx, ht⟩
    · have ih := sum_wt_of_tileL fuel _ ht
      have hp := ((List.perm_cons_erase hx).map wt).sum_eq
      simp only [List.map_cons, List.sum_cons] at hp ⊢
      rw [hp, ih, wt, wt]
      ring
    · have ih := sum_wt_of_tileL fuel _ ht
      have hp := ((List.perm_cons_erase hx).map wt).sum_eq
      simp only [List.map_cons, List.sum_cons] at hp ⊢
      rw [hp, ih, wt, wt]
      ring

/-- The weight of a row of length `n` in row `i`. -/
private theorem sum_row (i n : ℕ) :
    (((List.range n).map fun j => (i, j)).map wt).sum = (-1) ^ i * ((n % 2 : ℕ) : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wt, add_zero, pow_add]
    rcases Nat.even_or_odd n with hn | hn
    · have h := Nat.even_iff.1 hn
      rw [hn.neg_one_pow, h, show (n + 1) % 2 = 1 by omega]
      push_cast; ring
    · have h := Nat.odd_iff.1 hn
      rw [hn.neg_one_pow, h, show (n + 1) % 2 = 0 by omega]
      push_cast; ring

/-- The imbalance `∑_{i < N} (-1)^i [Y i odd]` of the rows `Y 0, …, Y (N-1)`. -/
private def imb (Y : ℕ → ℕ) (N : ℕ) : ℤ := ∑ i ∈ Finset.range N, (-1) ^ i * ((Y i % 2 : ℕ) : ℤ)

/-- The total weight of the Young diagram of `y` is its imbalance. -/
private theorem sum_cellsList (y : List ℕ) :
    ((cellsList y).map wt).sum = imb (fun i => y.getD i 0) y.length := by
  unfold cellsList imb
  generalize y.length = m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ, List.flatMap_cons, List.flatMap_nil, List.append_nil, sum_row]

/-- The sign of a row: `(-1)^i [v odd]` as a difference of two indicators. -/
private theorem term_eq (i v : ℕ) : (-1 : ℤ) ^ i * ((v % 2 : ℕ) : ℤ) =
    (if Odd (i + 1) ∧ Odd v then 1 else 0) - (if Even (i + 1) ∧ Odd v then 1 else 0) := by
  rcases Nat.even_or_odd i with hi | hi <;> rcases Nat.even_or_odd v with hy | hy
  · have h1 : ¬ Odd v := Nat.not_odd_iff_even.2 hy
    rw [Nat.even_iff.1 hy]; simp [h1]
  · have h1 : Odd (i + 1) := hi.add_one
    have h2 : ¬ Even (i + 1) := Nat.not_even_iff_odd.2 h1
    rw [Nat.odd_iff.1 hy, hi.neg_one_pow]; simp [h1, h2, hy]
  · have h1 : ¬ Odd v := Nat.not_odd_iff_even.2 hy
    rw [Nat.even_iff.1 hy]; simp [h1]
  · have h1 : Even (i + 1) := hi.add_one
    have h2 : ¬ Odd (i + 1) := Nat.not_odd_iff_even.2 h1
    rw [Nat.odd_iff.1 hy, hi.neg_one_pow]; simp [h1, h2, hy]

/-- The parity condition of the conjecture is the vanishing of the imbalance. -/
private theorem balanced_iff (y : List ℕ) :
    OddPartsBalanced y ↔ imb (fun i => y.getD i 0) y.length = 0 := by
  unfold OddPartsBalanced imb
  simp only [term_eq, Finset.sum_sub_distrib, Finset.sum_boole]
  rw [sub_eq_zero, Nat.cast_inj, eq_comm]

/-- The diagram `{(i, j) | j < Y i}` of a row-length function `Y`. -/
private def shape (Y : ℕ → ℕ) : Set (ℕ × ℕ) := {c | c.2 < Y c.1}

/-- A nonempty staircase `Y r = k - r` has nonzero imbalance: every odd row has the sign
`(-1)^(k+1)`. -/
private theorem imb_staircase_ne (Y : ℕ → ℕ) (N : ℕ) (hN : ∀ i, N ≤ i → Y i = 0)
    (hst : ∀ r, Y r = Y 0 - r) (h0 : 0 < Y 0) : imb Y N ≠ 0 := by
  have hkN : Y 0 ≤ N := by have := hN N le_rfl; rw [hst N] at this; omega
  have hterm : ∀ i ∈ Finset.range N, (-1 : ℤ) ^ i * ((Y i % 2 : ℕ) : ℤ) =
      (-1) ^ (Y 0 + 1) * ((Y i % 2 : ℕ) : ℤ) := by
    intro i _
    rcases Nat.mod_two_eq_zero_or_one (Y i) with h | h
    · rw [h]; simp
    · obtain ⟨m, hm⟩ : ∃ m, Y 0 + 1 = i + 2 * m := ⟨(Y 0 + 1 - i) / 2, by rw [hst i] at h; omega⟩
      rw [hm, pow_add, pow_mul]; simp
  unfold imb
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
  have h1 : Y (Y 0 - 1) % 2 = 1 := by rw [hst (Y 0 - 1)]; omega
  apply ne_of_gt
  calc (0 : ℤ) < 1 := one_pos
    _ = ((Y (Y 0 - 1) % 2 : ℕ) : ℤ) := by rw [h1]; norm_num
    _ ≤ _ := Finset.single_le_sum (f := fun i => ((Y i % 2 : ℕ) : ℤ))
          (fun i _ => by positivity) (Finset.mem_range.2 (by omega))

/-- The main lemma: an antitone row-length function with zero imbalance has a domino-tileable
diagram. By strong induction on the number of cells, removing a rim domino. -/
private theorem tileable_shape (N : ℕ) : ∀ (s : ℕ) (Y : ℕ → ℕ), ∑ i ∈ Finset.range N, Y i = s →
    Antitone Y → (∀ i, N ≤ i → Y i = 0) → imb Y N = 0 → DominoTileable (shape Y) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro Y hs hY hN himb
  by_cases h0 : Y 0 = 0
  · have : shape Y = ∅ := by
      ext ⟨r, c⟩
      simp only [shape, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have := hY (Nat.zero_le r); omega
    rw [this]; exact tileable_empty
  by_cases hh : ∃ i, Y (i + 1) + 2 ≤ Y i
  · -- a horizontal rim domino at the end of row `i`
    obtain ⟨i, hi⟩ := hh
    have hiN : i < N := by
      by_contra h
      have := hN i (by omega); omega
    have hdom : IsDomino {(i, Y i - 2), (i, Y i - 2 + 1)} := ⟨i, Y i - 2, Or.inr rfl⟩
    have hsub : ({(i, Y i - 2), (i, Y i - 2 + 1)} : Set (ℕ × ℕ)) ⊆ shape Y := by
      intro c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl <;> simp only [shape, Set.mem_ofPred_eq] <;> omega
    have hdiff : shape Y \ {(i, Y i - 2), (i, Y i - 2 + 1)} =
        shape (fun r => if r = i then Y r - 2 else Y r) := by
      ext ⟨r, c⟩
      simp only [shape, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff, Prod.mk.injEq]
      split_ifs with h
      · subst h; omega
      · omega
    refine tileable_of_diff hdom hsub ?_
    rw [hdiff]
    refine ih _ ?_ _ rfl ?_ ?_ ?_
    · rw [← hs]
      apply Finset.sum_lt_sum
      · intro r _; split_ifs <;> omega
      · refine ⟨i, Finset.mem_range.2 hiN, ?_⟩
        show (if i = i then Y i - 2 else Y i) < Y i
        rw [if_pos rfl]; omega
    · intro a b hab
      have h1 := hY hab
      have h2 : Y b ≤ Y (i + 1) ∨ b ≤ i := by
        rcases Nat.lt_or_ge i b with h | h
        · exact Or.inl (hY h)
        · exact Or.inr h
      simp only
      split_ifs with ha hb hb <;> subst_vars <;> omega
    · intro r hr
      have := hN r hr
      split_ifs <;> omega
    · rw [← himb]; unfold imb
      apply Finset.sum_congr rfl
      intro r _
      beta_reduce
      split_ifs with h
      · subst h
        rw [show (Y r - 2) % 2 = Y r % 2 by omega]
      · rfl
  by_cases hv : ∃ i, Y (i + 1) = Y i ∧ Y (i + 2) < Y (i + 1)
  · -- a vertical rim domino at the ends of rows `i` and `i + 1`
    obtain ⟨i, heq, hlt⟩ := hv
    have hiN : i + 1 < N := by
      by_contra h
      have := hN (i + 1) (by omega); omega
    have hdom : IsDomino {(i, Y i - 1), (i + 1, Y i - 1)} := ⟨i, Y i - 1, Or.inl rfl⟩
    have hsub : ({(i, Y i - 1), (i + 1, Y i - 1)} : Set (ℕ × ℕ)) ⊆ shape Y := by
      intro c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl <;> simp only [shape, Set.mem_ofPred_eq] <;> omega
    have hdiff : shape Y \ {(i, Y i - 1), (i + 1, Y i - 1)} =
        shape (fun r => if r = i ∨ r = i + 1 then Y r - 1 else Y r) := by
      ext ⟨r, c⟩
      simp only [shape, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff, Prod.mk.injEq]
      split_ifs with h
      · rcases h with rfl | rfl <;> omega
      · omega
    refine tileable_of_diff hdom hsub ?_
    rw [hdiff]
    refine ih _ ?_ _ rfl ?_ ?_ ?_
    · rw [← hs]
      apply Finset.sum_lt_sum
      · intro r _; split_ifs <;> omega
      · exact ⟨i, Finset.mem_range.2 (by omega), by simp only [true_or, if_true]; omega⟩
    · intro a b hab
      have h1 := hY hab
      have h2 : Y b ≤ Y (i + 2) ∨ b ≤ i + 1 := by
        rcases Nat.lt_or_ge (i + 1) b with h | h
        · exact Or.inl (hY h)
        · exact Or.inr h
      have h3 : Y (i + 1) ≤ Y a ∨ i + 1 < a := by
        rcases Nat.lt_or_ge (i + 1) a with h | h
        · exact Or.inr h
        · exact Or.inl (hY h)
      simp only
      split_ifs with ha hb hb <;> omega
    · intro r hr
      have := hN r hr
      split_ifs <;> omega
    · rw [← himb]; unfold imb
      obtain ⟨t, rfl⟩ : ∃ t, N = i + 1 + 1 + t := ⟨N - (i + 2), by omega⟩
      simp only
      rw [Finset.sum_range_add _ (i + 1 + 1) t, Finset.sum_range_add _ (i + 1 + 1) t,
        Finset.sum_range_succ _ (i + 1), Finset.sum_range_succ _ (i + 1),
        Finset.sum_range_succ _ i, Finset.sum_range_succ _ i]
      have hA : ∑ x ∈ Finset.range i, (-1 : ℤ) ^ x *
          (((if x = i ∨ x = i + 1 then Y x - 1 else Y x) % 2 : ℕ) : ℤ) =
          ∑ x ∈ Finset.range i, (-1 : ℤ) ^ x * ((Y x % 2 : ℕ) : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have := Finset.mem_range.1 hx
        rw [if_neg (by omega)]
      have hB : ∑ x ∈ Finset.range t, (-1 : ℤ) ^ (i + 1 + 1 + x) *
          (((if i + 1 + 1 + x = i ∨ i + 1 + 1 + x = i + 1 then Y (i + 1 + 1 + x) - 1
            else Y (i + 1 + 1 + x)) % 2 : ℕ) : ℤ) =
          ∑ x ∈ Finset.range t, (-1 : ℤ) ^ (i + 1 + 1 + x) * ((Y (i + 1 + 1 + x) % 2 : ℕ) : ℤ) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [if_neg (by omega)]
      rw [hA, hB, if_pos (Or.inl rfl), if_pos (Or.inr rfl), heq, pow_succ]
      ring
  · -- no rim domino: the diagram is a staircase, which has nonzero imbalance
    push Not at hh hv
    have hflat : ∀ r, Y (r + 1) = Y r → Y r = 0 := by
      intro r hr
      have hc1 : ∀ t, Y (r + t + 1) = Y (r + t) := by
        intro t
        induction t with
        | zero => simpa using hr
        | succ t iht =>
          have h1 := hv (r + t) iht
          have h2 := hY (show r + t + 1 ≤ r + t + 2 by omega)
          rw [show r + (t + 1) + 1 = r + t + 2 by omega, show r + (t + 1) = r + t + 1 by omega]
          omega
      have hc : ∀ t, Y (r + t) = Y r := by
        intro t
        induction t with
        | zero => rfl
        | succ t iht => rw [← add_assoc, hc1 t, iht]
      rw [← hc N]
      exact hN _ (by omega)
    have hst : ∀ r, Y r = Y 0 - r := by
      intro r
      induction r with
      | zero => simp
      | succ r ihr =>
        have h1 := hY (show r ≤ r + 1 by omega)
        have h2 := hh r
        by_cases he : Y (r + 1) = Y r
        · have := hflat r he; omega
        · omega
    exact absurd himb (imb_staircase_ne Y N hN hst (Nat.pos_of_ne_zero h0))

/-- `y.getD · 0` is antitone for a weakly decreasing list `y`. -/
private theorem antitone_getD {l : List ℕ} (hl : l.Pairwise (· ≥ ·)) :
    Antitone (fun i => l.getD i 0) := by
  intro a b hab
  simp only
  by_cases hb : b < l.length
  · rw [List.getD_eq_getElem _ _ hb, List.getD_eq_getElem _ _ (show a < l.length by omega)]
    rcases Nat.lt_or_eq_of_le hab with h | rfl
    · exact List.pairwise_iff_getElem.1 hl a b (by omega) hb h
    · exact le_refl _
  · rw [List.getD_eq_default _ _ (show l.length ≤ b by omega)]; exact Nat.zero_le _

/-- The parts of `k` are weakly decreasing. -/
private theorem parts_pairwise (k : ℕ) : (parts k).Pairwise (· ≥ ·) := by
  unfold parts
  rw [List.pairwise_reverse]
  exact (Nat.primeFactorsList_sorted k).pairwise.map _ (fun a b h => Nat.monotone_primeCounting h)

/-- The Young diagram of `y` is the diagram of its row-length function. -/
private theorem youngDiagram_eq (y : List ℕ) : youngDiagram y = shape (fun i => y.getD i 0) := by
  ext ⟨r, c⟩
  simp only [youngDiagram, shape, Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    by_contra hr
    rw [List.getD_eq_default _ _ (show y.length ≤ r by omega)] at h
    omega

/-- Domino tileability is exactly the conjectured parity condition. -/
private theorem isTerm_iff (k : ℕ) : IsTerm k ↔ IsConjTerm k := by
  unfold IsTerm IsConjTerm
  refine and_congr_right fun _ => ?_
  rw [balanced_iff]
  constructor
  · intro h
    have ht := (tileL_iff _ _ (pairwise_cellsList (parts k)) le_rfl).2
      (by rw [setOf_mem_cellsList]; exact h)
    have := sum_wt_of_tileL _ _ ht
    rwa [sum_cellsList] at this
  · intro h
    rw [youngDiagram_eq]
    exact tileable_shape _ _ _ rfl (antitone_getD (parts_pairwise k))
      (fun i hi => List.getD_eq_default _ _ hi) h

/-- Wiseman's conjecture holds: `a n = b n` for all `n ≥ 1`. -/
theorem result : statement := by
  intro n _
  have h : IsTerm = IsConjTerm := funext fun k => propext (isTerm_iff k)
  simp only [a, b, h]

end Math0.Frontier.A300789

#math0_settles Math0.Frontier.A300789.result Math0.Statements.A300789.statement
