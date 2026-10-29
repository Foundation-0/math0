/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A334592
import Math0.Audit

/-!
# Records of the XOR-triangle zero count A334592 are exactly the powers of two

We prove Peter Kagey's conjecture: `n ≥ 1` is a record position of `a` (the number of zeros in
the XOR-triangle of the binary expansion of `n`) if and only if `n` is a power of two.

**Ones bound.** Let `ones r` be the number of `true` entries in the XOR-triangle with top row
`r`. For every split `r = p ++ true :: s` we show
`count true p + |s| + 1 ≤ ones r`, by induction on `|s|` (generalizing `p`):
* `s = []`: the top row alone has `count true p + 1` ones;
* `s = true :: s'`: apply the induction hypothesis to the split `(p ++ [true]) ++ true :: s'`;
* `s = false :: s'`: the next row is `q ++ true :: xorRow (false :: s')` (as `true ⊕ false = true`),
  with `|xorRow (false :: s')| = |s'|`; the induction hypothesis bounds the ones below the top row
  by `|s'| + 1`, and the top row has at least `count true p + 1` ones.
With `p = []`: a top row of length `L` starting with `true` gives at least `L` ones.

**Zeros.** The triangle of a row of length `L` has `tri L = L(L+1)/2` entries, so
`a n + L ≤ tri L`, i.e. `a n ≤ tri (L - 1)`, where `L` is the bit length of `n ≥ 1` (the leading
bit is `1`). For `n = 2^k` the rows are `10…0` of lengths `k+1, k, …, 1`, so `a (2^k) = tri k`.

**Records.** If `1 ≤ m < 2^k` then `m` has bit length `L ≤ k`, so `a m ≤ tri (L-1) < tri k`.
If `n ≥ 1` is not a power of two, with bit length `k + 1`, then `2^k < n` and
`a n ≤ tri k = a (2^k)`, so `n` is not a record.
-/

namespace Math0.Frontier.A334592
open Math0.Statements.A334592

/-- Number of `true` entries in the XOR-triangle with top row `r`. -/
private def ones (r : List Bool) : ℕ := ((xorTriangle r).map (List.count true)).sum

/-- Number of `false` entries in the XOR-triangle with top row `r`. -/
private def zeros (r : List Bool) : ℕ := ((xorTriangle r).map (List.count false)).sum

/-- Triangular numbers: `tri k = 0 + 1 + ⋯ + k`. -/
private def tri : ℕ → ℕ
  | 0 => 0
  | k + 1 => tri k + (k + 1)

/-- `tri` is strictly increasing. -/
private lemma tri_lt {a b : ℕ} (h : a < b) : tri a < tri b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | rfl
    · have := ih h'
      simp only [tri]
      omega
    · simp only [tri]
      omega

/-- The next row is one shorter. -/
private lemma xorRow_length (r : List Bool) : (xorRow r).length = r.length - 1 := by
  simp [xorRow]

/-- `xorRow` on a list with two leading entries. -/
private lemma xorRow_cons_cons (a b : Bool) (s : List Bool) :
    xorRow (a :: b :: s) = (a ^^ b) :: xorRow (b :: s) := rfl

/-- The XOR-triangle of a nonempty row: the row followed by the triangle of the next row. -/
private lemma xorTriangle_cons (x : Bool) (s : List Bool) :
    xorTriangle (x :: s) = (x :: s) :: xorTriangle (xorRow (x :: s)) := by
  have h : (xorRow (x :: s)).length = s.length := by
    rw [xorRow_length]
    simp
  show rows (s.length + 1) (x :: s) = (x :: s) :: rows (xorRow (x :: s)).length (xorRow (x :: s))
  rw [h]
  rfl

/-- Recursion for `ones` on a nonempty row. -/
private lemma ones_of_ne_nil (r : List Bool) (hr : r ≠ []) :
    ones r = r.count true + ones (xorRow r) := by
  obtain ⟨x, s, rfl⟩ := List.exists_cons_of_ne_nil hr
  simp only [ones, xorTriangle_cons, List.map_cons, List.sum_cons]

/-- Recursion for `zeros` on a nonempty row. -/
private lemma zeros_of_ne_nil (r : List Bool) (hr : r ≠ []) :
    zeros r = r.count false + zeros (xorRow r) := by
  obtain ⟨x, s, rfl⟩ := List.exists_cons_of_ne_nil hr
  simp only [zeros, xorTriangle_cons, List.map_cons, List.sum_cons]

/-- The triangle of a row of length `n` has `tri n` entries. -/
private lemma zeros_add_ones : ∀ (n : ℕ) (r : List Bool), r.length = n →
    zeros r + ones r = tri n
  | 0, r, h => by
    have : r = [] := List.eq_nil_of_length_eq_zero h
    subst this
    rfl
  | n + 1, r, h => by
    have hr : r ≠ [] := by
      intro h'
      subst h'
      simp at h
    have ih := zeros_add_ones n (xorRow r) (by rw [xorRow_length]; omega)
    rw [zeros_of_ne_nil r hr, ones_of_ne_nil r hr]
    have := List.count_false_add_count_true r
    simp only [tri]
    omega

/-- Prepending a prefix to a nonempty row changes only a prefix of the next row. -/
private lemma xorRow_append (p l : List Bool) (hl : l ≠ []) :
    ∃ q, xorRow (p ++ l) = q ++ xorRow l := by
  induction p with
  | nil => exact ⟨[], rfl⟩
  | cons a p ih =>
    obtain ⟨q, hq⟩ := ih
    obtain ⟨b, t, hbt⟩ : ∃ b t, p ++ l = b :: t := by
      cases p with
      | nil =>
        obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil hl
        exact ⟨b, t, rfl⟩
      | cons b t => exact ⟨b, t ++ l, rfl⟩
    refine ⟨(a ^^ b) :: q, ?_⟩
    rw [List.cons_append, hbt, xorRow_cons_cons, ← hbt, hq]
    rfl

/-- The key bound: for a top row `p ++ true :: s` the triangle has at least
`count true p + |s| + 1` ones (one on each antidiagonal from that `true` onward). -/
private lemma ones_ge : ∀ (n : ℕ) (p s : List Bool), s.length = n →
    p.count true + s.length + 1 ≤ ones (p ++ true :: s)
  | 0, p, s, h => by
    have : s = [] := List.eq_nil_of_length_eq_zero h
    subst this
    rw [ones_of_ne_nil _ (by simp)]
    simp only [List.count_append, List.count_singleton_self, List.length_nil]
    omega
  | n + 1, p, s, h => by
    obtain ⟨b, s', rfl⟩ := List.exists_cons_of_length_eq_add_one h
    have hs' : s'.length = n := by simpa using h
    cases b with
    | true =>
      have ih := ones_ge n (p ++ [true]) s' hs'
      have e : p ++ [true] ++ true :: s' = p ++ true :: true :: s' := by simp
      rw [e, List.count_append] at ih
      simp only [List.count_singleton_self, List.length_cons] at ih ⊢
      omega
    | false =>
      obtain ⟨q, hq⟩ := xorRow_append p (true :: false :: s') (by simp)
      have e : xorRow (true :: false :: s') = true :: xorRow (false :: s') := rfl
      have hl : (xorRow (false :: s')).length = n := by
        rw [xorRow_length]
        simp [hs']
      have ih := ones_ge n q (xorRow (false :: s')) hl
      rw [ones_of_ne_nil _ (by simp), hq, e]
      have hc : p.count true + 1 ≤ (p ++ true :: false :: s').count true := by
        simp [List.count_append]
      simp only [List.length_cons, hs']
      omega

/-- A row of length `L` starting with `true` has at least `L` ones in its triangle. -/
private lemma ones_ge_length (s : List Bool) : (true :: s).length ≤ ones (true :: s) := by
  have := ones_ge s.length [] s rfl
  simpa using this

/-- `xorRow` of an all-zero row. -/
private lemma xorRow_replicate_false (k : ℕ) :
    xorRow (List.replicate k false) = List.replicate (k - 1) false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [List.replicate_succ, List.replicate_succ, xorRow_cons_cons, ← List.replicate_succ, ih]
      simp [List.replicate_succ]

/-- The triangle of `10…0` (with `k` zeros) has `tri k` zeros. -/
private lemma zeros_pow (k : ℕ) : zeros (true :: List.replicate k false) = tri k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [zeros_of_ne_nil _ (by simp), List.replicate_succ, xorRow_cons_cons,
      ← List.replicate_succ, xorRow_replicate_false]
    simp only [Bool.true_xor, Bool.not_false, Nat.add_sub_cancel] at ih ⊢
    rw [ih]
    simp only [tri, List.count_cons_of_ne (by decide : true ≠ false), List.count_replicate_self]
    omega

/-- The binary expansion of a positive number starts with `1`. -/
private lemma binary_cons (n : ℕ) (hn : n ≠ 0) : ∃ s, binary n = true :: s := by
  rw [binary_eq_digits]
  have hne : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  obtain ⟨L, d, hLd⟩ := (List.eq_nil_or_concat (Nat.digits 2 n)).resolve_left hne
  have hlast := Nat.getLast_digit_ne_zero 2 hn
  have hd : (Nat.digits 2 n).getLast hne = d := by simp [hLd]
  have hmem : d ∈ Nat.digits 2 n := by rw [hLd]; simp
  have hlt : d < 2 := Nat.digits_lt_base (by norm_num) hmem
  have h1 : d = 1 := by omega
  rw [hLd, h1]
  simp

/-- The length of the binary expansion is the number of base-2 digits. -/
private lemma binary_length (n : ℕ) : (binary n).length = (Nat.digits 2 n).length := by
  simp [binary_eq_digits]

/-- The binary expansion of `2^k` is `10…0`. -/
private lemma binary_pow (k : ℕ) : binary (2 ^ k) = true :: List.replicate k false := by
  rw [binary_eq_digits]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.digits_def' (by norm_num) (by positivity)]
    have h1 : 2 ^ (k + 1) % 2 = 0 := by simp [Nat.pow_succ]
    have h2 : 2 ^ (k + 1) / 2 = 2 ^ k := by simp [Nat.pow_succ]
    rw [h1, h2, List.map_cons, List.reverse_cons, ih, List.replicate_succ']
    rfl

/-- `a (2^k) = tri k`. -/
private lemma a_pow (k : ℕ) : a (2 ^ k) = tri k := by
  show zeros (binary (2 ^ k)) = tri k
  rw [binary_pow, zeros_pow]

/-- For `n ≥ 1` with `L` binary digits, `a n ≤ tri (L - 1)`. -/
private lemma a_le (n : ℕ) (hn : n ≠ 0) : a n ≤ tri ((Nat.digits 2 n).length - 1) := by
  obtain ⟨s, hs⟩ := binary_cons n hn
  have hlen := binary_length n
  rw [hs] at hlen
  have h1 := ones_ge_length s
  have h2 := zeros_add_ones _ (true :: s) rfl
  have ha : a n = zeros (true :: s) := by
    show zeros (binary n) = _
    rw [hs]
  rw [ha, ← hlen]
  simp only [List.length_cons, Nat.add_sub_cancel] at h1 h2 ⊢
  simp only [tri] at h2
  omega

/-- Kagey's conjecture: the record positions of A334592 are exactly the powers of two. -/
theorem result : statement := by
  intro n
  constructor
  · rintro ⟨hn1, hrec⟩
    by_contra hne
    simp only [not_exists] at hne
    have hn0 : n ≠ 0 := by omega
    have hpos : 0 < (Nat.digits 2 n).length :=
      List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr hn0)
    have hL : 2 ^ ((Nat.digits 2 n).length - 1) ≤ n :=
      (Nat.lt_digits_length_iff (by norm_num) n).1 (by omega)
    have hlt : 2 ^ ((Nat.digits 2 n).length - 1) < n :=
      lt_of_le_of_ne hL (fun h => hne _ h.symm)
    have h1 := hrec _ Nat.one_le_two_pow hlt
    have h2 := a_le n hn0
    rw [a_pow] at h1
    omega
  · rintro ⟨k, rfl⟩
    refine ⟨Nat.one_le_two_pow, fun m hm1 hmk => ?_⟩
    have hm0 : m ≠ 0 := by omega
    have hLk : (Nat.digits 2 m).length ≤ k := (Nat.digits_length_le_iff (by norm_num) m).2 hmk
    have hpos : 0 < (Nat.digits 2 m).length :=
      List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr hm0)
    have h1 := a_le m hm0
    have h2 : tri ((Nat.digits 2 m).length - 1) < tri k := tri_lt (by omega)
    rw [a_pow]
    omega

end Math0.Frontier.A334592

#math0_settles Math0.Frontier.A334592.result Math0.Statements.A334592.statement
