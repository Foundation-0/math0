/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A332010
import Math0.Audit

/-!
# A332010: the one-descent derangements and their average first letter

We prove Kagey's conjecture `T(n, 1) = 2^(n-2)` for every `n ≥ 2`: the average first letter of
the derangements of `{1, …, n}` with exactly one descent has reduced denominator `2^(n-2)`.

**Structure.** Write `n = m + 2`. A word with distinct letters and exactly one descent is the
concatenation `P ++ Q` of two increasing runs (`split_of_desB`). For a permutation of
`{1, …, n}`, an increasing run `P` at positions `1, 2, …` has `P[i] ≥ i + 1`, with a fixed point
iff its first letter is `1`; an increasing run `Q` ending at position `n` has a fixed point iff it
contains `n` (`lower_of_derB`, `upper_of_derB`). So for a derangement, `1` is in the second run
and `n` in the first: the word is `s ++ [n] ++ [1] ++ (the rest of {2, …, n-1}, increasing)`
where `s` is an increasing list from `{2, …, n-1}`, i.e. a sublist of `[2, …, n-1]`.
Conversely each such word is a one-descent derangement (`word_mem_ders`), and distinct `s` give
distinct words. Hence the one-descent derangements are a permutation of the `2^m` words
`word m s`, `s` a sublist of `[2, …, m+1]` (`ders_perm_words`).

**Counting.** The first letter of `word m s` is the head of `s`, or `m + 2` when `s = []`.
Summing over the sublists of `[a, …, a+k-1]` with default `a + k` gives `(a+1)·2^k - 1`
(`sum_heads`, by induction using `sublists'_cons`), so the sum of first letters is
`N = 3·2^m - 1`. The average is `N / 2^m`, and `N` is coprime to `2^m` (it is odd when `m ≥ 1`),
so its reduced denominator is `2^m = 2^(n-2)`.
-/

namespace Math0.Frontier.A332010
open Math0.Statements.A332010

/-! ### The derangement test on pieces -/

/-- `derB` of a concatenation. -/
private theorem derB_append (l₁ l₂ : List ℕ) (i : ℕ) :
    derB (l₁ ++ l₂) i = (derB l₁ i && derB l₂ (i + l₁.length)) := by
  induction l₁ generalizing i with
  | nil => simp [derB]
  | cons x xs ih =>
    simp only [List.cons_append, derB, ih, List.length_cons, Bool.and_assoc]
    rw [show i + 1 + xs.length = i + (xs.length + 1) by omega]

/-- An increasing list whose letters all exceed `i` passes `derB _ i`. -/
private theorem derB_of_lower : ∀ (l : List ℕ) (i : ℕ), l.Pairwise (· < ·) →
    (∀ x ∈ l, i < x) → derB l i = true
  | [], _, _, _ => rfl
  | x :: xs, i, hp, hb => by
    rw [List.pairwise_cons] at hp
    simp only [derB, Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨by have := hb x (by simp); omega, derB_of_lower xs (i + 1) hp.2 fun y hy => ?_⟩
    have h1 := hp.1 y hy
    have h2 := hb x (by simp)
    omega

/-- In an increasing list `x :: xs` bounded by `B`, the head satisfies `x + |xs| < B`. -/
private theorem head_add_length_lt : ∀ (x : ℕ) (xs : List ℕ) (B : ℕ),
    (x :: xs).Pairwise (· < ·) → (∀ y ∈ x :: xs, y < B) → x + xs.length < B
  | x, [], B, _, hb => by simpa using hb x (by simp)
  | x, z :: zs, B, hp, hb => by
    have h1 := head_add_length_lt z zs B (List.pairwise_cons.mp hp).2
      (fun y hy => hb y (List.mem_cons_of_mem _ hy))
    have h2 := (List.pairwise_cons.mp hp).1 z (by simp)
    simp only [List.length_cons]
    omega

/-- An increasing list placed at positions `i, i+1, …` whose letters all lie below its last
position passes `derB _ i`. -/
private theorem derB_of_upper : ∀ (l : List ℕ) (i : ℕ), l.Pairwise (· < ·) →
    (∀ x ∈ l, x + 1 < i + l.length) → derB l i = true
  | [], _, _, _ => rfl
  | x :: xs, i, hp, hb => by
    have h1 := head_add_length_lt x xs (i + xs.length) hp
      (fun y hy => by have := hb y hy; simp only [List.length_cons] at this; omega)
    rw [List.pairwise_cons] at hp
    simp only [derB, Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨by omega, derB_of_upper xs (i + 1) hp.2 fun y hy => ?_⟩
    have := hb y (List.mem_cons_of_mem _ hy)
    simp only [List.length_cons] at this
    omega

/-- Converse direction at the start: an increasing list with letters `≥ i` passing `derB _ i`
has all letters `> i`. -/
private theorem lower_of_derB : ∀ (l : List ℕ) (i : ℕ), l.Pairwise (· < ·) →
    (∀ x ∈ l, i ≤ x) → derB l i = true → ∀ x ∈ l, i < x
  | [], _, _, _, _ => by simp
  | x :: xs, i, hp, hb, hd => by
    simp only [derB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hd
    rw [List.pairwise_cons] at hp
    have hx : i < x := by have := hb x (by simp); omega
    have ih := lower_of_derB xs (i + 1) hp.2 (fun y hy => by have := hp.1 y hy; omega) hd.2
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · have := ih y hy; omega

/-- Converse direction at the end: an increasing list at positions `i, i+1, …` with letters
below `i + |l|` passing `derB _ i` has all letters below its last position. -/
private theorem upper_of_derB : ∀ (l : List ℕ) (i : ℕ), l.Pairwise (· < ·) →
    (∀ x ∈ l, x < i + l.length) → derB l i = true → ∀ x ∈ l, x + 1 < i + l.length
  | [], _, _, _, _ => by simp
  | x :: xs, i, hp, hb, hd => by
    simp only [derB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hd
    rw [List.pairwise_cons] at hp
    have ih := upper_of_derB xs (i + 1) hp.2 (fun y hy => by
      have := hb y (List.mem_cons_of_mem _ hy); simp only [List.length_cons] at this; omega) hd.2
    intro y hy
    simp only [List.length_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · cases xs with
      | nil => have := hb y (by simp); simp at this; omega
      | cons z zs =>
        have h1 := hp.1 z (by simp)
        have h2 := ih z (by simp)
        simp only [List.length_cons] at h2 ⊢
        omega
    · have := ih y hy; omega

/-! ### The descent count on pieces -/

/-- One unfolding step of `desB`. -/
private theorem desB_cons_cons (x y : ℕ) (l : List ℕ) :
    desB (x :: y :: l) = (if y < x then 1 else 0) + desB (y :: l) := by
  rw [desB]

/-- An increasing word has no descent. -/
private theorem desB_of_pairwise : ∀ l : List ℕ, l.Pairwise (· < ·) → desB l = 0
  | [], _ => rfl
  | [_], _ => rfl
  | x :: y :: l, hp => by
    rw [desB_cons_cons, desB_of_pairwise (y :: l) (List.pairwise_cons.mp hp).2]
    have := (List.pairwise_cons.mp hp).1 y (by simp)
    rw [if_neg (by omega)]

/-- A word with distinct letters and no descent is increasing. -/
private theorem pairwise_of_desB : ∀ l : List ℕ, l.Nodup → desB l = 0 → l.Pairwise (· < ·)
  | [], _, _ => List.Pairwise.nil
  | [_], _, _ => List.pairwise_singleton _ _
  | x :: y :: l, hn, hd => by
    rw [desB_cons_cons] at hd
    have hyx : ¬ y < x := by intro h; rw [if_pos h] at hd; omega
    rw [if_neg hyx, Nat.zero_add] at hd
    have ih := pairwise_of_desB (y :: l) (List.nodup_cons.mp hn).2 hd
    have hxy : x ≠ y := fun h => (List.nodup_cons.mp hn).1 (h ▸ List.mem_cons_self ..)
    refine List.Pairwise.cons (fun z hz => ?_) ih
    rcases List.mem_cons.mp hz with rfl | hz
    · omega
    · have := (List.pairwise_cons.mp ih).1 z hz; omega

/-- Descents of `l ++ a :: b :: m`, split at the step `a, b`. -/
private theorem desB_split : ∀ (l : List ℕ) (a b : ℕ) (m : List ℕ),
    desB (l ++ a :: b :: m) = desB (l ++ [a]) + (if b < a then 1 else 0) + desB (b :: m)
  | [], a, b, m => by simp [desB_cons_cons, desB]
  | [x], a, b, m => by simp [desB_cons_cons, desB]; omega
  | x :: y :: l, a, b, m => by
    have ih := desB_split (y :: l) a b m
    simp only [List.cons_append] at ih ⊢
    rw [desB_cons_cons, ih, desB_cons_cons]
    omega

/-- A word with distinct letters and exactly one descent is the concatenation of two increasing
runs. -/
private theorem split_of_desB : ∀ l : List ℕ, l.Nodup → desB l = 1 →
    ∃ u a b v, l = u ++ a :: b :: v ∧ (u ++ [a]).Pairwise (· < ·) ∧ (b :: v).Pairwise (· < ·)
  | [], _, h => by simp [desB] at h
  | [_], _, h => by simp [desB] at h
  | x :: y :: l, hn, hd => by
    rw [desB_cons_cons] at hd
    by_cases hyx : y < x
    · rw [if_pos hyx] at hd
      exact ⟨[], x, y, l, rfl, by simp,
        pairwise_of_desB (y :: l) (List.nodup_cons.mp hn).2 (by omega)⟩
    · rw [if_neg hyx] at hd
      obtain ⟨u, a, b, v, he, hu, hv⟩ :=
        split_of_desB (y :: l) (List.nodup_cons.mp hn).2 (by omega)
      have hxy : x ≠ y := fun h => (List.nodup_cons.mp hn).1 (h ▸ List.mem_cons_self ..)
      refine ⟨x :: u, a, b, v, by rw [he]; rfl, ?_, hv⟩
      rw [List.cons_append, List.pairwise_cons]
      refine ⟨fun z hz => ?_, hu⟩
      have hy : ∀ z ∈ u ++ [a], y ≤ z := by
        cases u with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at he
          simp [he.1]
        | cons c u' =>
          simp only [List.cons_append, List.cons.injEq] at he
          obtain ⟨rfl, -⟩ := he
          intro z hz
          rw [List.cons_append] at hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact le_refl _
          · exact le_of_lt ((List.pairwise_cons.mp hu).1 z hz)
      have := hy z hz
      omega

/-! ### The explicit list of one-descent derangements -/

/-- The word attached to an increasing list `s` of letters from `{2, …, m+1}`: the first run is
`s` followed by `m+2`, the second run is `1` followed by the remaining letters of
`{2, …, m+1}`. -/
private def word (m : ℕ) (s : List ℕ) : List ℕ :=
  s ++ (m + 2) :: 1 :: (List.range' 2 m).filter (fun x => decide (x ∉ s))

/-- All the words `word m s`, for `s` running over the sublists of `[2, …, m+1]`. -/
private def words (m : ℕ) : List (List ℕ) := (List.range' 2 m).sublists'.map (word m)


/-- Membership in `range' a k`. -/
private theorem mem_range'_iff {x a k : ℕ} : x ∈ List.range' a k ↔ a ≤ x ∧ x < a + k :=
  List.mem_range'_1

/-- Every word `word m s` (with `s` a sublist of `[2, …, m+1]`) is a derangement of
`{1, …, m+2}` with exactly one descent. -/
private theorem word_mem_ders {m : ℕ} {s : List ℕ} (hsub : s.Sublist (List.range' 2 m)) :
    word m s ∈ ders (m + 2) 1 := by
  have hs : s.Pairwise (· < ·) := List.Pairwise.sublist hsub List.pairwise_lt_range'
  have hsn : s.Nodup := List.Nodup.sublist hsub List.nodup_range'
  have hsm : ∀ x ∈ s, 2 ≤ x ∧ x < 2 + m := fun x hx => mem_range'_iff.mp (hsub.subset hx)
  have hslen : s.length ≤ m := by simpa using hsub.length_le
  set v := (List.range' 2 m).filter (fun x => decide (x ∉ s)) with hvdef
  have hv : v.Pairwise (· < ·) := List.Pairwise.filter _ List.pairwise_lt_range'
  have hvn : v.Nodup := List.Nodup.filter _ List.nodup_range'
  have memv : ∀ x, x ∈ v ↔ (2 ≤ x ∧ x < 2 + m) ∧ x ∉ s := by
    intro x; simp [hvdef, List.mem_filter]
  have hw : word m s = s ++ (m + 2) :: 1 :: v := rfl
  have hnod : (word m s).Nodup := by
    rw [hw, List.nodup_append, List.nodup_cons, List.nodup_cons]
    refine ⟨hsn, ⟨?_, ?_, hvn⟩, ?_⟩
    · simp only [List.mem_cons, not_or]
      refine ⟨by omega, fun h => ?_⟩
      have := ((memv _).mp h).1; omega
    · intro h; have := ((memv _).mp h).1; omega
    · intro x hx y hy
      have hx' := hsm x hx
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · omega
      · omega
      · rintro rfl; exact ((memv _).mp hy).2 hx
  have hperm : (word m s).Perm (List.range' 1 (m + 2)) := by
    rw [List.perm_ext_iff_of_nodup hnod List.nodup_range']
    intro x
    rw [hw, mem_range'_iff]
    simp only [List.mem_append, List.mem_cons, memv]
    constructor
    · rintro (h | rfl | rfl | ⟨h, -⟩)
      · have := hsm x h; omega
      · omega
      · omega
      · omega
    · intro h
      by_cases hxs : x ∈ s
      · exact Or.inl hxs
      · right
        by_cases h1 : x = m + 2
        · exact Or.inl h1
        · right
          by_cases h2 : x = 1
          · exact Or.inl h2
          · exact Or.inr ⟨by omega, hxs⟩
  have hlen : s.length + v.length = m := by
    have := hperm.length_eq
    rw [hw] at this
    simp only [List.length_append, List.length_cons, List.length_range'] at this
    omega
  rw [mem_ders]
  refine ⟨hperm, ?_, ?_⟩
  · have hder : derB (word m s) 1 = true := by
      rw [hw, derB_append]
      simp only [derB, Bool.and_eq_true, bne_iff_ne, ne_eq]
      refine ⟨derB_of_lower s 1 hs (fun x hx => by have := hsm x hx; omega), by omega, by omega,
        derB_of_upper v _ hv (fun x hx => ?_)⟩
      have := ((memv x).mp hx).1
      omega
    rw [derB_one] at hder
    exact of_decide_eq_true hder
  · rw [← desB_eq, hw, desB_split, desB_of_pairwise (s ++ [m + 2]), desB_of_pairwise (1 :: v),
      if_pos (by omega)]
    · rw [List.pairwise_cons]
      exact ⟨fun x hx => by have := ((memv x).mp hx).1; omega, hv⟩
    · rw [List.pairwise_append]
      refine ⟨hs, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
      have := hsm x hx
      simp only [List.mem_singleton] at hy
      omega

/-- Every derangement of `{1, …, m+2}` with exactly one descent is a word `word m s`. -/
private theorem mem_words_of_mem_ders {m : ℕ} {w : List ℕ} (h : w ∈ ders (m + 2) 1) :
    w ∈ words m := by
  rw [mem_ders] at h
  obtain ⟨hp, hd, hdes⟩ := h
  have hn : w.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hmem : ∀ x, x ∈ w ↔ 1 ≤ x ∧ x < 1 + (m + 2) := fun x => hp.mem_iff.trans mem_range'_iff
  have hlen : w.length = m + 2 := hp.length_eq.trans List.length_range'
  have hD : derB w 1 = true := by rw [derB_one]; simpa using hd
  obtain ⟨u, a, b, v, rfl, hP, hQ⟩ := split_of_desB w hn (by rw [desB_eq]; exact hdes)
  have hsplit : u ++ a :: b :: v = (u ++ [a]) ++ (b :: v) := by simp
  rw [hsplit] at hD hmem hlen hn
  rw [derB_append, Bool.and_eq_true] at hD
  have hlo := lower_of_derB _ 1 hP (fun x hx => ((hmem x).mp (List.mem_append_left _ hx)).1) hD.1
  have hup := upper_of_derB _ _ hQ (fun x hx => by
      have := ((hmem x).mp (List.mem_append_right _ hx)).2
      rw [List.length_append] at hlen; omega) hD.2
  rw [List.length_append] at hlen
  replace hup : ∀ x ∈ b :: v, x + 1 < 1 + (m + 2) := fun x hx => by have := hup x hx; omega
  -- `1` lies in the second run, so `b = 1`
  have hb : b = 1 := by
    have h1 : 1 ∈ (u ++ [a]) ++ (b :: v) := (hmem 1).mpr (by omega)
    rcases List.mem_append.mp h1 with h1 | h1
    · have := hlo 1 h1; omega
    · have hb1 := ((hmem b).mp (List.mem_append_right _ (List.mem_cons_self ..))).1
      rcases List.mem_cons.mp h1 with h1 | h1
      · exact h1.symm
      · have := (List.pairwise_cons.mp hQ).1 1 h1; omega
  -- `m + 2` lies in the first run, so `a = m + 2`
  have hPa : ∀ x ∈ u, x < a := fun x hx =>
    (List.pairwise_append.mp hP).2.2 x hx a (List.mem_singleton_self _)
  have ha : a = m + 2 := by
    have h1 : m + 2 ∈ (u ++ [a]) ++ (b :: v) := (hmem _).mpr (by omega)
    have ha2 := ((hmem a).mp (List.mem_append_left _ (by simp))).2
    rcases List.mem_append.mp h1 with h1 | h1
    · rcases List.mem_append.mp h1 with h1 | h1
      · have := hPa _ h1; omega
      · simp only [List.mem_singleton] at h1; omega
    · have := hup _ h1; omega
  subst hb ha
  have hun : u.Nodup := (List.nodup_append.mp (List.nodup_append.mp hn).1).1
  have hu : u.Pairwise (· < ·) := (List.pairwise_append.mp hP).1
  have hv : v.Pairwise (· < ·) := (List.pairwise_cons.mp hQ).2
  have hv1 : ∀ x ∈ v, 1 < x := (List.pairwise_cons.mp hQ).1
  have hdisj : ∀ x ∈ u, x ∉ v := by
    intro x hx hxv
    have := (List.nodup_append.mp hn).2.2 x (List.mem_append_left _ hx) x
      (List.mem_cons_of_mem _ hxv)
    exact this rfl
  have husub : u ⊆ List.range' 2 m := by
    intro x hx
    rw [mem_range'_iff]
    have h1 := hlo x (List.mem_append_left _ hx)
    have h2 := hPa x hx
    omega
  have hsub : u.Sublist (List.range' 2 m) :=
    List.sublist_of_subperm_of_pairwise (List.subperm_of_subset hun husub) hu
      List.pairwise_lt_range'
  have hveq : v = (List.range' 2 m).filter (fun x => decide (x ∉ u)) := by
    apply List.Pairwise.eq_of_mem_iff hv (List.Pairwise.filter _ List.pairwise_lt_range')
    intro x
    simp only [List.mem_filter, mem_range'_iff, decide_eq_true_eq]
    constructor
    · intro hx
      have h1 := hv1 x hx
      have h2 := hup x (List.mem_cons_of_mem _ hx)
      exact ⟨⟨by omega, by omega⟩, fun hu' => hdisj x hu' hx⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hx := (hmem x).mpr (by omega)
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact absurd hx h3
        · simp only [List.mem_singleton] at hx; omega
      · rcases List.mem_cons.mp hx with hx | hx
        · omega
        · exact hx
  rw [words, List.mem_map]
  refine ⟨u, List.mem_sublists'.mpr hsub, ?_⟩
  rw [word, ← hveq]

/-- The words `word m s` are pairwise distinct. -/
private theorem words_nodup (m : ℕ) : (words m).Nodup := by
  refine List.Nodup.map_on ?_ (List.nodup_sublists'.mpr List.nodup_range')
  intro s hs t ht hst
  have hs' := List.mem_sublists'.mp hs
  have ht' := List.mem_sublists'.mp ht
  have hns : m + 2 ∉ s := fun h => by have := mem_range'_iff.mp (hs'.subset h); omega
  have hnz : m + 2 ∉ 1 :: (List.range' 2 m).filter (fun x => decide (x ∉ s)) := by
    simp only [List.mem_cons, List.mem_filter, mem_range'_iff, not_or]
    omega
  exact ((List.append_cons_inj_of_notMem hns hnz).mp hst).1

/-- The one-descent derangements of `{1, …, m+2}` are, up to order, the words `word m s`. -/
private theorem ders_perm_words (m : ℕ) : (ders (m + 2) 1).Perm (words m) := by
  rw [List.perm_ext_iff_of_nodup (nodup_ders _ _) (words_nodup m)]
  intro w
  constructor
  · exact mem_words_of_mem_ders
  · intro h
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    exact word_mem_ders (List.mem_sublists'.mp hs)

/-- The sum, over the sublists `s` of `[a, …, a+k-1]`, of the first letter of `s` (or `a + k`
for the empty sublist) is `(a + 1) 2^k - 1`. -/
private theorem sum_heads : ∀ k a : ℕ,
    ((List.range' a k).sublists'.map fun s => s.headD (a + k)).sum + 1 = (a + 1) * 2 ^ k
  | 0, a => by simp
  | k + 1, a => by
    have ih := sum_heads k (a + 1)
    rw [show a + 1 + k = a + (k + 1) by omega] at ih
    rw [List.range'_succ, List.sublists'_cons, List.map_append, List.sum_append, List.map_map]
    have h2 : ((List.range' (a + 1) k).sublists'.map
        ((fun s => s.headD (a + (k + 1))) ∘ List.cons a)).sum = a * 2 ^ k := by
      simp [Function.comp_def, List.length_sublists', Nat.mul_comm]
    rw [h2, pow_succ]
    nlinarith

/-- Kagey's conjecture: `T(n, 1) = 2^(n-2)` for every `n ≥ 2`. -/
theorem result : statement := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hlen : (words m).length = 2 ^ m := by
    simp [words, List.length_sublists']
  have hsum : ((words m).map fun w => w.headD 0).sum + 1 = 3 * 2 ^ m := by
    have h := sum_heads m 2
    rw [show 2 + m = m + 2 by omega] at h
    have : ((words m).map fun w => w.headD 0) =
        (List.range' 2 m).sublists'.map fun s => s.headD (m + 2) := by
      rw [words, List.map_map]
      congr 1
      funext s
      cases s <;> rfl
    rw [this, h]
  rw [T, avgFirst, avgFirstLetter_perm (ders_perm_words m), avgFirstLetter, hlen,
    Nat.add_sub_cancel]
  set N := ((words m).map fun w => w.headD 0).sum
  have hcop : Nat.Coprime N (2 ^ m) := by
    rcases m with _ | k
    · simp
    · apply Nat.Coprime.pow_right
      rw [Nat.coprime_two_right]
      rw [pow_succ] at hsum
      exact ⟨3 * 2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  have key := Rat.den_div_eq_of_coprime (a := (N : ℤ)) (b := ((2 ^ m : ℕ) : ℤ))
    (by positivity) (by simpa using hcop)
  rw [Int.cast_natCast, Int.cast_natCast] at key
  exact_mod_cast key

end Math0.Frontier.A332010

#math0_settles Math0.Frontier.A332010.result Math0.Statements.A332010.statement
