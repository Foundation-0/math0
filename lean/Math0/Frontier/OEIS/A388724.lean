/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A388724
import Math0.Audit

/-!
# Column sums of strictly superdiagonal reversed partitions are A000245

We prove Gus Wiseman's conjecture for A388724: for every `k ≥ 1`, the number of strictly
superdiagonal reversed partitions (of any size) with maximum `k` is `A000245(k-1)`.

**Idea.** Summing `T(n,k)` over `n` just counts the lists `y = (y_1 ≤ … ≤ y_m)` with `y_i > i`
and maximum `k` (`colSum_card`). Let `N k lo` count the weakly increasing lists with `y_i > i`
and all entries in `[lo, k]` (empty list included). Splitting off the first entry `j` and
subtracting `1` from the remaining entries gives `N (k+1) lo = 1 + ∑_{j = max lo 2}^{k+1} N k (j-1)`
(this is the enumeration `enum`, shown complete and duplicate-free in `mem_enum`, `nodup_enum`),
hence the Pascal-type recursion `N (k+1) lo = N (k+1) (lo+1) + N k (lo-1)` for `2 ≤ lo ≤ k+1`,
together with `N (k+1) lo = 1` for `lo ≥ k+2` and `N k 0 = N k 1 = N k 2`. In the indexing
`A k s = N k (k+1-s)` this is the Catalan triangle, and induction gives the ballot formula
`A n (m+1) = C(n+m+1, m+1) - C(n+m+1, m)` for `m < n` (`A_closed`; on the diagonal one uses
`A (n+1) (n+1) = A (n+1) n` and `C(2m+1, m+1) = C(2m+1, m)`).

The lists with maximum `k + 1` are the lists with entries `≤ k + 1` minus those with entries
`≤ k`, so the column sum is `N (K+1) 0 - N K 0 = N (K+1) 3 = A (K+1) (K-1)` (`K = k - 1 ≥ 1`;
the column `k = 1` is empty). For `K = j + 2` this is `C(2j+4, j+1) - C(2j+4, j)`, and multiplying
by `(j+4)! (j+1)!` gives `(j+4)·(2j+4)! - (j+1)·(2j+4)! = 3·(2j+4)!`, which is the defining
formula `A000245(K) = 3 (2K)! / ((K+2)! (K-1)!)`; `K = 1` gives `1 = A000245(1)`.
-/

namespace Math0.Frontier.A388724
open Math0.Statements.A388724 Finset

/-- `SD c y`: the `i`-th entry (0-indexed) of `y` exceeds `i + c`. -/
private def SD : ℕ → List ℕ → Prop
  | _, [] => True
  | c, x :: t => c < x ∧ SD (c + 1) t

/-- `SD c y` in terms of indices. -/
private theorem SD_iff : ∀ (c : ℕ) (y : List ℕ), SD c y ↔ ∀ i (h : i < y.length), i + c < y[i]
  | c, [] => by simp [SD]
  | c, x :: t => by
    rw [SD, SD_iff (c + 1) t]
    constructor
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => simpa using h0
      | succ i =>
        have := h1 i (by simpa using hi)
        simp only [List.getElem_cons_succ]
        omega
    · intro h
      have h0 := h 0 (by simp)
      rw [List.getElem_cons_zero] at h0
      refine ⟨by omega, fun i hi => ?_⟩
      have := h (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      omega

/-- Shifting all entries up by one shifts the bound up by one. -/
private theorem SD_map : ∀ (c : ℕ) (t : List ℕ), SD (c + 1) (t.map (· + 1)) ↔ SD c t
  | c, [] => by simp [SD]
  | c, x :: t => by
    simp only [List.map_cons, SD]
    exact and_congr (by omega) (SD_map (c + 1) t)

/-- `Good lo k y`: `y` is weakly increasing, strictly superdiagonal, with entries in `[lo, k]`. -/
private def Good (lo k : ℕ) (y : List ℕ) : Prop :=
  y.Pairwise (· ≤ ·) ∧ SD 1 y ∧ ∀ x ∈ y, lo ≤ x ∧ x ≤ k

/-- Enumeration of the lists `y` with `Good lo k y`: either `y = []`, or `y = j :: (t + 1)` with
`max lo 2 ≤ j ≤ k` and `Good (j - 1) (k - 1) t`. -/
private def enum : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | k + 1, lo => [] :: (List.range' (max lo 2) (k + 2 - max lo 2)).flatMap
      fun j => (enum k (j - 1)).map fun t => j :: t.map (· + 1)

/-- Subtracting then adding one is the identity on lists of positive numbers. -/
private theorem map_sub_add : ∀ s : List ℕ, (∀ a ∈ s, 1 ≤ a) → (s.map (· - 1)).map (· + 1) = s
  | [], _ => rfl
  | a :: s, h => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨by have := h a List.mem_cons_self; omega,
      map_sub_add s fun b hb => h b (List.mem_cons_of_mem a hb)⟩

/-- `enum k lo` lists exactly the lists `y` with `Good lo k y`. -/
private theorem mem_enum : ∀ (k lo : ℕ) (y : List ℕ), y ∈ enum k lo ↔ Good lo k y
  | 0, lo, y => by
    simp only [enum, List.mem_singleton]
    constructor
    · rintro rfl
      simp [Good, SD]
    · rintro ⟨-, hsd, hb⟩
      cases y with
      | nil => rfl
      | cons x t =>
        have := (hb x List.mem_cons_self).2
        simp only [SD] at hsd
        omega
  | k + 1, lo, y => by
    cases y with
    | nil => simp [enum, Good, SD]
    | cons x s =>
      simp only [enum, List.mem_cons, reduceCtorEq, false_or, List.mem_flatMap,
        List.mem_range'_1, List.mem_map, List.cons.injEq]
      constructor
      · rintro ⟨j, ⟨hj1, hj2⟩, t, ht, rfl, rfl⟩
        rw [mem_enum k (j - 1) t] at ht
        obtain ⟨ht1, ht2, ht3⟩ := ht
        refine ⟨?_, ?_, ?_⟩
        · rw [List.pairwise_cons, List.pairwise_map]
          refine ⟨?_, ht1.imp fun h => by omega⟩
          intro a ha
          rw [List.mem_map] at ha
          obtain ⟨b, hb, rfl⟩ := ha
          have := (ht3 b hb).1
          omega
        · exact ⟨by omega, (SD_map 1 t).2 ht2⟩
        · intro a ha
          rw [List.mem_cons, List.mem_map] at ha
          rcases ha with rfl | ⟨b, hb, rfl⟩
          · omega
          · have := ht3 b hb
            omega
      · rintro ⟨hp, hsd, hb⟩
        rw [List.pairwise_cons] at hp
        simp only [SD] at hsd
        have hx := hb x List.mem_cons_self
        have hs1 : ∀ a ∈ s, 1 ≤ a := fun a ha => by have := hp.1 a ha; omega
        refine ⟨x, ⟨by omega, by omega⟩, s.map (· - 1), ?_, rfl, map_sub_add s hs1⟩
        rw [mem_enum k (x - 1)]
        refine ⟨?_, ?_, ?_⟩
        · rw [List.pairwise_map]
          exact hp.2.imp fun h => by omega
        · rw [← SD_map 1, map_sub_add s hs1]
          exact hsd.2
        · intro a ha
          rw [List.mem_map] at ha
          obtain ⟨b, hb', rfl⟩ := ha
          have h1 := hp.1 b hb'
          have h2 := hb b (List.mem_cons_of_mem x hb')
          omega

/-- `enum k lo` has no repetitions. -/
private theorem nodup_enum : ∀ (k lo : ℕ), (enum k lo).Nodup
  | 0, lo => by simp [enum]
  | k + 1, lo => by
    rw [enum, List.nodup_cons]
    refine ⟨by simp, ?_⟩
    rw [List.nodup_flatMap]
    refine ⟨fun j _ => (nodup_enum k (j - 1)).map ?_, ?_⟩
    · intro t1 t2 h
      simp only [List.cons.injEq, true_and] at h
      exact (List.map_injective_iff.2 (add_left_injective 1)) h
    · refine (List.nodup_range' (s := max lo 2) (n := k + 2 - max lo 2)).imp fun {i j} hij => ?_
      intro y hy1 hy2
      simp only [List.mem_map] at hy1 hy2
      obtain ⟨t, -, rfl⟩ := hy1
      obtain ⟨t', -, h⟩ := hy2
      exact hij (List.cons.inj h).1.symm

/-- The number of lists `y` with `Good lo k y`. -/
private def N (k lo : ℕ) : ℕ := (enum k lo).length

/-- The defining recursion of `N`, from the shape of `enum`. -/
private theorem N_succ (k lo : ℕ) : N (k + 1) lo =
    1 + ((List.range' (max lo 2) (k + 2 - max lo 2)).map fun j => N k (j - 1)).sum := by
  simp only [N, enum, List.length_cons, List.length_flatMap, List.length_map]
  omega

/-- Lower bounds `lo ≤ 2` are all equivalent (the first entry is at least `2` anyway). -/
private theorem N_low (k lo : ℕ) (h : lo ≤ 2) : N (k + 1) lo = N (k + 1) 2 := by
  rw [N_succ, N_succ, max_eq_right h, max_self]

/-- `N k 1 = N k 0`. -/
private theorem N_one (k : ℕ) : N k 1 = N k 0 := by
  cases k with
  | zero => rfl
  | succ k => rw [N_low k 1 (by norm_num), N_low k 0 (by norm_num)]

/-- With lower bound above the upper bound only the empty list remains. -/
private theorem N_top (k lo : ℕ) (h : k + 2 ≤ lo) : N (k + 1) lo = 1 := by
  rw [N_succ, show k + 2 - max lo 2 = 0 by omega]
  simp

/-- Pascal-type recursion: either the first entry is `lo`, or all entries are `≥ lo + 1`. -/
private theorem N_rec (k lo : ℕ) (h1 : 2 ≤ lo) (h2 : lo ≤ k + 1) :
    N (k + 1) lo = N (k + 1) (lo + 1) + N k (lo - 1) := by
  rw [N_succ, N_succ, max_eq_left h1, max_eq_left (by omega : 2 ≤ lo + 1),
    show k + 2 - lo = (k + 2 - (lo + 1)) + 1 by omega, List.range'_succ]
  simp only [List.map_cons, List.sum_cons]
  omega

/-- The Catalan-triangle indexing `A k s = N k (k + 1 - s)`. -/
private def A (k s : ℕ) : ℕ := N k (k + 1 - s)

/-- The first column of the triangle is `1`. -/
private theorem A_zero (k : ℕ) : A k 0 = 1 := by
  cases k with
  | zero => rfl
  | succ k => exact N_top k _ (by omega)

/-- Pascal recursion of the Catalan triangle. -/
private theorem A_rec (k s : ℕ) (h : s + 1 ≤ k) :
    A (k + 1) (s + 1) = A (k + 1) s + A k (s + 1) := by
  have := N_rec k (k + 1 - s) (by omega) (by omega)
  rw [show k + 1 - s + 1 = k + 1 + 1 - s by omega, show k + 1 - s - 1 = k + 1 - (s + 1) by omega]
    at this
  simpa [A, show k + 1 + 1 - (s + 1) = k + 1 - s by omega] using this

/-- The diagonal equals the subdiagonal. -/
private theorem A_diag (k : ℕ) : A (k + 1) (k + 1) = A (k + 1) k := by
  simp only [A, show k + 1 + 1 - (k + 1) = 1 by omega, show k + 1 + 1 - k = 2 by omega]
  exact N_low k 1 (by norm_num)

/-- Closed form of the Catalan triangle: `A n (m+1) = C(n+m+1, m+1) - C(n+m+1, m)`. -/
private theorem A_closed (n : ℕ) :
    ∀ m, m + 1 ≤ n → A n (m + 1) + (n + m + 1).choose m = (n + m + 1).choose (m + 1) := by
  induction n with
  | zero => intro m h; omega
  | succ n ih =>
    intro m
    induction m with
    | zero =>
      intro _
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [A_diag 0, A_zero]
        simp
      · rw [A_rec n 0 (by omega), A_zero]
        have := ih 0 (by omega)
        simp only [Nat.add_zero, Nat.zero_add, Nat.choose_zero_right, Nat.choose_one_right]
          at this ⊢
        omega
    | succ m ihm =>
      intro hm
      rcases Nat.lt_or_ge (m + 1) n with hlt | hge
      · have e1 : A (n + 1) (m + 1) + (n + m + 2).choose m = (n + m + 2).choose (m + 1) := by
          have := ihm (by omega)
          rwa [show n + 1 + m + 1 = n + m + 2 by ring] at this
        have e2 : A n (m + 1 + 1) + (n + m + 2).choose (m + 1) =
            (n + m + 2).choose (m + 1 + 1) := by
          have := ih (m + 1) (by omega)
          rwa [show n + (m + 1) + 1 = n + m + 2 by ring] at this
        rw [A_rec n (m + 1) (by omega), show n + 1 + (m + 1) + 1 = n + m + 2 + 1 by ring,
          Nat.choose_succ_succ' (n + m + 2) (m + 1), Nat.choose_succ_succ' (n + m + 2) m]
        omega
      · obtain rfl : n = m + 1 := by omega
        have e1 : A (m + 1 + 1) (m + 1) + (2 * (m + 1) + 1).choose m =
            (2 * (m + 1) + 1).choose (m + 1) := by
          have := ihm (by omega)
          rwa [show m + 1 + 1 + m + 1 = 2 * (m + 1) + 1 by ring] at this
        rw [A_diag (m + 1), show m + 1 + 1 + (m + 1) + 1 = 2 * (m + 1) + 1 + 1 by ring,
          Nat.choose_succ_succ' (2 * (m + 1) + 1) (m + 1),
          Nat.choose_succ_succ' (2 * (m + 1) + 1) m, Nat.choose_symm_half (m + 1)]
        omega

/-- `A000245 (j+2)` as a difference of binomials. -/
private theorem A000245_eq (j x : ℕ)
    (hx : x + (2 * j + 4).choose j = (2 * j + 4).choose (j + 1)) :
    A000245 (j + 2) = x := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (n := 2 * j + 4) (k := j + 1) (by omega)
  have h0 := Nat.choose_mul_factorial_mul_factorial (n := 2 * j + 4) (k := j) (by omega)
  rw [show 2 * j + 4 - (j + 1) = j + 3 by omega] at h1
  rw [show 2 * j + 4 - j = j + 4 by omega] at h0
  have key : 3 * (2 * (j + 2)).factorial = x * ((j + 2 + 2).factorial * (j + 2 - 1).factorial) := by
    rw [show 2 * (j + 2) = 2 * j + 4 by ring, show j + 2 + 2 = (j + 3) + 1 by ring,
      show j + 2 - 1 = j + 1 by omega, Nat.factorial_succ (j + 3), Nat.factorial_succ j]
    rw [show j + 4 = (j + 3) + 1 by ring, Nat.factorial_succ (j + 3)] at h0
    rw [Nat.factorial_succ j] at h1
    have hx' : (x : ℤ) = ((2 * j + 4).choose (j + 1) : ℤ) - ((2 * j + 4).choose j : ℤ) := by
      rw [← hx]; push_cast; ring
    have h1' : ((2 * j + 4).choose (j + 1) : ℤ) * ((j + 1) * j.factorial) * (j + 3).factorial =
        (2 * j + 4).factorial := by exact_mod_cast h1
    have h0' : ((2 * j + 4).choose j : ℤ) * j.factorial * ((j + 3 + 1) * (j + 3).factorial) =
        (2 * j + 4).factorial := by exact_mod_cast h0
    have : (3 * (2 * j + 4).factorial : ℤ) =
        x * ((j + 3 + 1) * (j + 3).factorial * ((j + 1) * j.factorial)) := by
      rw [hx']
      linear_combination (j + 1 : ℤ) * h0' - (j + 4 : ℤ) * h1'
    exact_mod_cast this
  rw [A000245, if_neg (by omega), key, Nat.mul_div_cancel _ (by positivity)]

/-- The column sum, as the number of good lists with maximum `k`. -/
private theorem colSum_card (k : ℕ) :
    ∑ᶠ n, T n k = #{y ∈ (enum k 0).toFinset | k ∈ y} := by
  have hT : ∀ n, T n k = #{y ∈ {y ∈ (enum k 0).toFinset | k ∈ y} | y.sum = n} := by
    intro n
    rw [T, ← Set.ncard_coe_finset]
    congr 1
    ext y
    rw [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_filter,
      List.mem_toFinset, mem_enum]
    simp only [Good, IsRevPartition, StrictlySuperdiagonal, List.max?_eq_some_iff, ← SD_iff 1 y]
    constructor
    · rintro ⟨⟨-, hp, hs⟩, hsd, hk, hle⟩
      exact ⟨⟨⟨hp, hsd, fun x hx => ⟨Nat.zero_le _, hle x hx⟩⟩, hk⟩, hs⟩
    · rintro ⟨⟨⟨hp, hsd, hb⟩, hk⟩, hs⟩
      refine ⟨⟨fun x hx => ?_, hp, hs⟩, hsd, hk, fun x hx => (hb x hx).2⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
      have := (SD_iff 1 y).1 hsd i hi
      omega
  simp_rw [hT]
  rw [finsum_eq_sum_of_support_subset (s := {y ∈ (enum k 0).toFinset | k ∈ y}.image List.sum),
    ← card_eq_sum_card_image]
  intro n hn
  rw [Function.mem_support] at hn
  obtain ⟨y, hy⟩ := Finset.card_ne_zero.1 hn
  rw [mem_filter] at hy
  simp only [coe_image, Set.mem_image, mem_coe]
  exact ⟨y, hy.1, hy.2⟩

/-- The good lists with maximum `k + 1` and those with maximum at most `k` make up all good
lists with entries at most `k + 1`. -/
private theorem card_split (k : ℕ) :
    #{y ∈ (enum (k + 1) 0).toFinset | k + 1 ∈ y} + N k 0 = N (k + 1) 0 := by
  have hN : ∀ k, N k 0 = #(enum k 0).toFinset := fun k =>
    (List.toFinset_card_of_nodup (nodup_enum k 0)).symm
  have hc : {y ∈ (enum (k + 1) 0).toFinset | ¬ (k + 1 ∈ y)} = (enum k 0).toFinset := by
    ext y
    simp only [mem_filter, List.mem_toFinset, mem_enum, Good]
    constructor
    · rintro ⟨⟨hp, hsd, hb⟩, hk⟩
      refine ⟨hp, hsd, fun x hx => ⟨Nat.zero_le _, ?_⟩⟩
      have := (hb x hx).2
      have : x ≠ k + 1 := fun h => hk (h ▸ hx)
      omega
    · rintro ⟨hp, hsd, hb⟩
      refine ⟨⟨hp, hsd, fun x hx => ⟨Nat.zero_le _, by have := (hb x hx).2; omega⟩⟩, fun hk => ?_⟩
      have := (hb _ hk).2
      omega
  rw [hN, hN, ← hc, card_filter_add_card_filter_not]

/-- The theorem: column sums of A388724 are A000245. -/
theorem result : statement := by
  intro k hk
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  rw [colSum_card, Nat.add_sub_cancel]
  have hs := card_split K
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · have : N (0 + 1) 0 = 1 := rfl
    have h0 : N 0 0 = 1 := rfl
    rw [A000245, if_pos rfl]
    omega
  · rw [N_low K 0 (by norm_num), N_rec K 2 le_rfl (by omega), ← N_one,
      show (2 : ℕ) - 1 = 1 from rfl]
      at hs
    have h3 : #{y ∈ (enum (K + 1) 0).toFinset | K + 1 ∈ y} = A (K + 1) (K - 1) := by
      rw [A, show K + 1 + 1 - (K - 1) = 2 + 1 by omega]
      omega
    rw [h3]
    obtain ⟨j, rfl⟩ | rfl : (∃ j, K = j + 2) ∨ K = 1 := by
      rcases K with _ | _ | j
      · omega
      · exact Or.inr rfl
      · exact Or.inl ⟨j, by ring⟩
    · rw [show j + 2 - 1 = j + 1 by omega]
      refine (A000245_eq j _ ?_).symm
      have := A_closed (j + 2 + 1) j (by omega)
      rwa [show j + 2 + 1 + j + 1 = 2 * j + 4 by ring] at this
    · rw [show 1 - 1 = 0 by rfl, A_zero]
      decide

end Math0.Frontier.A388724

#math0_settles Math0.Frontier.A388724.result Math0.Statements.A388724.statement
