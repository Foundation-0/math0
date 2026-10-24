/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# OEIS A201060: repdigits whose digital product is a repdigit

Source: https://oeis.org/A201060, Jaroslav Krizek, Nov 26 2011 (COMMENTS section). Verbatim:
> Conjecture: a(n) is repunit for n >= 16.

The entry's name is "Repdigit numbers with repdigit digital product." (offset `1`). Data:
`0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 22, 33, 111, 222, 1111, 11111, …, 1111111111111111111`
(31 terms, `n = 1, …, 31`).

## Encoding

* *Repdigits* (A010785, which starts with `0`): `IsRepdigit m` says that all decimal digits of
  `m` (`Nat.digits 10 m`) are equal. `Nat.digits 10 0 = []`, so `0` is a repdigit, as in
  A010785 and in this entry (`a(1) = 0`).
* *Digital product* (A007954): `digitProd m` is the product of the decimal digits of `m`, with
  `digitProd 0 = 0` as in A007954 (the empty product would give `1`; both are repdigits, so
  this choice does not affect the sequence).
* *The sequence.* `IsTerm m := IsRepdigit m ∧ IsRepdigit (digitProd m)`, and
  `a n = Nat.nth IsTerm (n - 1)`: the `n`-th smallest term (offset `1`, so `a 1 = 0`). The set of
  terms is infinite (every repunit is a term, `infinite_isTerm`), so `a` is strictly increasing
  and lists all terms. `a` is noncomputable as written (`Nat.nth`).
* *Data check.* `rep d k = Nat.ofDigits 10 (replicate k d)` is the `k`-digit repdigit with digit
  `d`. We prove that the repdigits below `10 ^ L` are exactly `0` and the `rep d k` with
  `1 ≤ d ≤ 9`, `1 ≤ k ≤ L` (`isRepdigit_iff_mem_repList`). Filtering this explicit list for
  `L = 19` gives the 31 listed terms (kernel-checked), and `map_nth_eq_of_filter` transfers this
  to `Nat.nth`. All 31 listed terms are checked (`a_data`).
* *Repunits* (A002275): `IsRepunit m` says that all decimal digits of `m` are `1`, i.e.
  `m = (10^k - 1)/9` for some `k ≥ 0` (A002275 includes `R_0 = 0`; this is irrelevant here since
  `a n ≥ a 16 = 1111` for `n ≥ 16`).
* *The conjecture.* "a(n) is repunit for n >= 16" is `∀ n ≥ 16, IsRepunit (a n)`, with the
  entry's offset `1` (`a 16 = 1111`).
-/

namespace Math0.Statements.A201060

/-! ### Definitions -/

/-- `m` is a repdigit (A010785): all its decimal digits are equal (`0` counts). -/
def IsRepdigit (m : ℕ) : Prop := ∀ x ∈ Nat.digits 10 m, ∀ y ∈ Nat.digits 10 m, x = y

instance : DecidablePred IsRepdigit := fun m => by unfold IsRepdigit; infer_instance

/-- The digital product of `m` (A007954): the product of its decimal digits, `0` for `m = 0`. -/
def digitProd (m : ℕ) : ℕ := if m = 0 then 0 else (Nat.digits 10 m).prod

/-- `m` is a repdigit whose digital product is a repdigit. -/
def IsTerm (m : ℕ) : Prop := IsRepdigit m ∧ IsRepdigit (digitProd m)

instance : DecidablePred IsTerm := fun m => by unfold IsTerm; infer_instance

/-- A201060: the `n`-th repdigit number with repdigit digital product, in increasing order
(offset `1`, `a 1 = 0`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- `m` is a repunit (A002275): all its decimal digits are `1`. -/
def IsRepunit (m : ℕ) : Prop := ∀ d ∈ Nat.digits 10 m, d = 1

/-! ### The repdigits, explicitly -/

/-- The repdigit with `k` decimal digits, all equal to `d`. -/
def rep (d k : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate k d)

theorem digits_rep {d : ℕ} (hd1 : 1 ≤ d) (hd9 : d ≤ 9) (k : ℕ) :
    Nat.digits 10 (rep d k) = List.replicate k d := by
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro x hx
    rw [List.eq_of_mem_replicate hx]
    omega
  · intro h
    have := List.getLast_mem h
    rw [List.eq_of_mem_replicate this]
    omega

/-- `0` and the repdigits `rep d k` with `1 ≤ d ≤ 9`, `1 ≤ k ≤ L`. -/
def repList (L : ℕ) : List ℕ :=
  0 :: (List.range L).flatMap fun k => (List.range 9).map fun d => rep (d + 1) (k + 1)

theorem mem_repList {L m : ℕ} :
    m ∈ repList L ↔ m = 0 ∨ ∃ k < L, ∃ d < 9, rep (d + 1) (k + 1) = m := by
  simp only [repList, List.mem_cons, List.mem_flatMap, List.mem_range, List.mem_map]

/-- The repdigits below `10 ^ L` are exactly the elements of `repList L`. -/
theorem isRepdigit_iff_mem_repList {L m : ℕ} (hm : m < 10 ^ L) :
    IsRepdigit m ↔ m ∈ repList L := by
  rw [mem_repList]
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact Or.inl rfl
    right
    have hne : Nat.digits 10 m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 hpos.ne'
    obtain ⟨d, l', hdl⟩ := List.exists_cons_of_ne_nil hne
    have hdmem : d ∈ Nat.digits 10 m := by rw [hdl]; exact List.mem_cons_self
    have hrep : Nat.digits 10 m = List.replicate (Nat.digits 10 m).length d :=
      List.eq_replicate_iff.2 ⟨rfl, fun b hb => h b hb d hdmem⟩
    have hd10 : d < 10 := Nat.digits_lt_base (by norm_num) hdmem
    have hd0 : d ≠ 0 := by
      have h1 := Nat.getLast_digit_ne_zero 10 hpos.ne'
      rwa [h _ (List.getLast_mem _) d hdmem] at h1
    have hlen : (Nat.digits 10 m).length ≤ L := (Nat.digits_length_le_iff (by norm_num) m).2 hm
    have hlen1 : 1 ≤ (Nat.digits 10 m).length := by rw [hdl]; simp
    refine ⟨(Nat.digits 10 m).length - 1, by omega, d - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel hlen1, Nat.sub_add_cancel (by omega), rep, ← hrep,
      Nat.ofDigits_digits]
  · rintro (rfl | ⟨k, -, d, hd, rfl⟩)
    · simp [IsRepdigit]
    · intro x hx y hy
      rw [digits_rep (by omega) (by omega)] at hx hy
      rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]

/-- Every repunit `rep 1 k` is a term (its digital product is `1` or `0`). -/
theorem isTerm_rep_one (k : ℕ) : IsTerm (rep 1 k) := by
  have hd := digits_rep (d := 1) le_rfl (by norm_num) k
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    rw [hd] at hx hy
    rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
  · unfold digitProd
    split_ifs
    · simp [IsRepdigit]
    · rw [hd, List.prod_replicate, one_pow]
      simp [IsRepdigit]

/-- The sequence is infinite: it contains every repunit. -/
theorem infinite_isTerm : (Set.ofPred IsTerm).Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨B, hB⟩ => ?_
  have h1 : B < rep 1 (B + 1) := by
    have h2 : 10 ^ B ≤ rep 1 (B + 1) := by
      rw [← Nat.lt_digits_length_iff (by norm_num), digits_rep le_rfl (by norm_num),
        List.length_replicate]
      omega
    have h3 : B < 10 ^ B := Nat.lt_pow_self (by norm_num)
    omega
  have := hB (isTerm_rep_one (B + 1))
  omega

/-! ### Sanity checks -/

/-- The elements `< N` satisfying `p`, in increasing order, are `nth p 0, nth p 1, …`. -/
theorem filter_range_eq (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    (List.range N).filter (fun k => decide (p k)) =
      (List.range (Nat.count p N)).map (Nat.nth p) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, ih, Nat.count_succ]
    by_cases h : p N
    · simp [h, List.range_succ, Nat.nth_count h]
    · simp [h]

theorem map_nth_eq_of_filter {p : ℕ → Prop} [DecidablePred p] {N K : ℕ} {L : List ℕ}
    (h : (List.range N).filter (fun k => decide (p k)) = L) (hK : L.length = K) :
    (List.range K).map (Nat.nth p) = L := by
  rw [filter_range_eq] at h
  subst h
  simp only [List.length_map, List.length_range] at hK
  rw [hK]

/-- The 31 terms listed in OEIS. -/
def listed : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 22, 33, 111, 222, 1111, 11111, 111111, 1111111, 11111111,
    111111111, 1111111111, 11111111111, 111111111111, 1111111111111, 11111111111111,
    111111111111111, 1111111111111111, 11111111111111111, 111111111111111111,
    1111111111111111111]

/-- Filtering the repdigits with at most 19 digits gives the listed terms (kernel-checked). -/
theorem filter_repList :
    (repList 19).filter (fun m => decide (IsRepdigit (digitProd m))) = listed := by
  decide +kernel

theorem repList_lt : ∀ m ∈ repList 19, m < 10 ^ 19 := by
  decide +kernel

theorem listed_pairwise : listed.Pairwise (· < ·) := by
  decide +kernel

/-- The terms below `10 ^ 19`, in increasing order, are the listed terms. -/
theorem filter_range_isTerm :
    (List.range (10 ^ 19)).filter (fun k => decide (IsTerm k)) = listed := by
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) (List.pairwise_lt_range.filter _)
    listed_pairwise fun m => ?_
  rw [← filter_repList, List.mem_filter, List.mem_filter, List.mem_range, decide_eq_true_iff,
    decide_eq_true_iff, IsTerm]
  constructor
  · rintro ⟨hm, h1, h2⟩
    exact ⟨(isRepdigit_iff_mem_repList hm).1 h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hm := repList_lt m h1
    exact ⟨hm, (isRepdigit_iff_mem_repList hm).2 h1, h2⟩

/-- The definition reproduces all 31 terms listed in OEIS (kernel-checked). -/
theorem a_data : (List.range 31).map (fun i => a (i + 1)) =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 22, 33, 111, 222, 1111, 11111, 111111, 1111111, 11111111,
      111111111, 1111111111, 11111111111, 111111111111, 1111111111111, 11111111111111,
      111111111111111, 1111111111111111, 11111111111111111, 111111111111111111,
      1111111111111111111] := by
  have : (fun i => a (i + 1)) = Nat.nth IsTerm := funext fun i => by simp [a]
  rw [this]
  exact map_nth_eq_of_filter filter_range_isTerm rfl

/-! ### The conjecture -/

/-- Conjecture (Krizek, A201060): `a(n)` is a repunit for every `n ≥ 16`. -/
def statement : Prop := ∀ n : ℕ, 16 ≤ n → IsRepunit (a n)

end Math0.Statements.A201060
