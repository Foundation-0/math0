/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A308121
import Math0.Audit

/-!
# A308121: for odd `n`, row `2n` is row `n` with its halves swapped

We prove Charlie Neder's conjecture (2019) on the irregular triangle
`T(n,k) = A109395(n)·k - A076512(n)·r_k`, where `r_1 < ⋯ < r_φ(n)` are the totatives of `n`
and `A076512(n)/A109395(n)` is `φ(n)/n` in lowest terms.

Let `n = 2t+1 ≥ 3`, `m = φ(n) = 2h`, and `φ(n)/n = a/b` in lowest terms.

* **Totatives.** By the reflection `r ↦ n - r`, exactly `h` totatives of `n` lie in `[1, t]`
  (list `L`) and `h` in `[t+1, 2t]` (list `H`); `totatives n = L ++ H`. The totatives of `2n`
  are the odd numbers coprime to `n`: those below `n` are `2r - n` for `r ∈ H`, those above `n`
  are `n + 2r` for `r ∈ L`, so `totatives (2n) = H.map (2·-n) ++ L.map (n+2·)`.
* **Fractions.** `φ(2n) = φ(n)`, so `φ(2n)/(2n) = (a/b)/2`. From `a n = b m` with `m` even
  and `n` odd, `a` is even, so `(a/2)/b` is already in lowest terms: `A109395(2n) = b`,
  `A076512(2n) = a/2`.
* **Algebra.** For `k ≤ h`: `T(2n,k) = b k - (a/2)(2 H_k - n) = b(k+h) - a H_k = T(n, k+h)`, using
  `(a/2) n = b h`. For `k > h`: `T(2n,k) = b k - (a/2)(n + 2 L_{k-h}) = T(n, k-h)`.
-/

namespace Math0.Frontier.A308121
open Math0.Statements.A308121

/-- Among `a, a+1, …, a+2k-1` with `a` odd, the numbers coprime to `2n` are exactly the odd
ones `a, a+2, …, a+2k-2` that are coprime to `n`. -/
private lemma filter_pair (n : ℕ) : ∀ (k a : ℕ), Odd a →
    (List.range' a (2 * k)).filter (fun s => Nat.Coprime s (2 * n)) =
      (List.range' a k 2).filter (fun s => Nat.Coprime s n) := by
  intro k
  induction k with
  | zero => intro a _; simp
  | succ k ih =>
    intro a ha
    have h2 : 2 * (k + 1) = (2 * k) + 1 + 1 := by ring
    have c1 : Nat.Coprime a (2 * n) ↔ Nat.Coprime a n := by
      rw [Nat.coprime_mul_iff_right]; simp [ha]
    have c2 : ¬ Nat.Coprime (a + 1) (2 * n) := by
      intro h
      have := Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 n) h)
      rw [Nat.odd_add_one] at this
      exact this ha
    have ha2 : Odd (a + 1 + 1) := by rw [Nat.odd_add_one, Nat.odd_add_one, not_not]; exact ha
    rw [h2, List.range'_succ, List.range'_succ, List.range'_succ, List.filter_cons,
      List.filter_cons, List.filter_cons, ih _ ha2]
    simp [c1, c2]

/-- An arithmetic progression of step `2` is the image of a step-`1` range under any `f` that
increases by `2` at each step. -/
private lemma range'_two_eq_map (f : ℕ → ℕ) : ∀ (k r0 : ℕ),
    (∀ r, r0 ≤ r → f (r + 1) = f r + 2) →
    List.range' (f r0) k 2 = (List.range' r0 k).map f := by
  intro k
  induction k with
  | zero => intro r0 _; simp
  | succ k ih =>
    intro r0 hf
    rw [List.range'_succ, List.range'_succ, List.map_cons, ← hf r0 le_rfl,
      ih (r0 + 1) (fun r hr => hf r (by omega))]

/-- Reflection `r ↦ N - r` sends `[1, t]` onto `[N - t, N - 1]`, reversed. -/
private lemma map_sub_range' (N : ℕ) : ∀ t, t < N →
    (List.range' 1 t).map (fun r => N - r) = (List.range' (N - t) t).reverse := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    rw [List.range'_concat, List.map_append, ih (by omega)]
    have : N - (t + 1) + 1 = N - t := by omega
    rw [List.range'_succ, this]
    simp
    omega

/-- `totatives n` has `φ(n)` elements. -/
private lemma len_tot (n : ℕ) : (totatives n).length = Nat.totient n := by
  rw [← Nat.filter_coprime_Ico_eq_totient n 1, Nat.Ico_eq_range']
  simp [totatives, Finset.card, Finset.filter, Nat.coprime_comm]

/-- For odd `n` and `2r ≥ n`: `2r - n` is coprime to `n` iff `r` is. -/
private lemma cop_hi {n r : ℕ} (hn : Odd n) (hr : n ≤ 2 * r) :
    Nat.Coprime (2 * r - n) n ↔ Nat.Coprime r n := by
  rw [Nat.coprime_sub_self_left hr, Nat.coprime_mul_iff_left]; simp [hn]

/-- For odd `n`: `n + 2r` is coprime to `n` iff `r` is. -/
private lemma cop_lo {n r : ℕ} (hn : Odd n) :
    Nat.Coprime (n + 2 * r) n ↔ Nat.Coprime r n := by
  rw [add_comm, Nat.coprime_add_self_left, Nat.coprime_mul_iff_left]; simp [hn]

/-- The totatives of `n = 2t+1` are those in `[1, t]` followed by those in `[t+1, 2t]`. -/
private lemma tot_split (t : ℕ) (ht : 1 ≤ t) :
    totatives (2 * t + 1) =
      (List.range' 1 t).filter (fun r => Nat.Coprime r (2 * t + 1)) ++
      (List.range' (t + 1) t).filter (fun r => Nat.Coprime r (2 * t + 1)) := by
  have e : List.range' 1 (2 * t + 1) =
      List.range' 1 t ++ List.range' (t + 1) t ++ [2 * t + 1] := by
    rw [show [2 * t + 1] = List.range' (1 + (t + t)) 1 by simp; omega,
      show t + 1 = 1 + t by omega, List.range'_append_1, List.range'_append_1]
    congr 1; omega
  have hc : ¬ Nat.Coprime (2 * t + 1) (2 * t + 1) := by
    rw [Nat.coprime_self]; omega
  rw [totatives, e, List.filter_append, List.filter_append]
  simp [hc]

/-- The totatives of `2n`, `n = 2t+1`: first `2r - n` for the totatives `r > n/2` of `n`, then
`n + 2r` for the totatives `r < n/2`, each in increasing order. -/
private lemma tot2_split (t : ℕ) (ht : 1 ≤ t) :
    totatives (2 * (2 * t + 1)) =
      ((List.range' (t + 1) t).filter (fun r => Nat.Coprime r (2 * t + 1))).map
          (fun r => 2 * r - (2 * t + 1)) ++
      ((List.range' 1 t).filter (fun r => Nat.Coprime r (2 * t + 1))).map
          (fun r => (2 * t + 1) + 2 * r) := by
  have hn : Odd (2 * t + 1) := odd_two_mul_add_one t
  have e : List.range' 1 (2 * (2 * t + 1)) =
      List.range' 1 (2 * t) ++ List.range' (2 * t + 1) 2 ++ List.range' (2 * t + 3) (2 * t) := by
    rw [show 2 * t + 1 = 1 + 2 * t by omega, List.range'_append_1,
      show 2 * t + 3 = 1 + (2 * t + 2) by omega, List.range'_append_1]
    congr 1; omega
  have hmid : (List.range' (2 * t + 1) 2).filter
      (fun s => Nat.Coprime s (2 * (2 * t + 1))) = [] := by
    have c1 : ¬ Nat.Coprime (2 * t + 1) (2 * (2 * t + 1)) := by
      intro h
      have := Nat.Coprime.coprime_dvd_right (dvd_mul_left (2 * t + 1) 2) h
      rw [Nat.coprime_self] at this; omega
    have c2 : ¬ Nat.Coprime (2 * t + 1 + 1) (2 * (2 * t + 1)) := by
      intro h
      have := Nat.coprime_two_right.mp
        (Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 (2 * t + 1)) h)
      rw [Nat.odd_add_one] at this
      exact this hn
    simp [List.range'_succ, c1, c2]
  rw [totatives, e, List.filter_append, List.filter_append, hmid, List.append_nil,
    filter_pair _ t 1 (by simp), filter_pair _ t (2 * t + 3) (by
      rw [show 2 * t + 3 = 2 * (t + 1) + 1 by ring]; exact odd_two_mul_add_one _)]
  have m1 : List.range' 1 t 2 = (List.range' (t + 1) t).map (fun r => 2 * r - (2 * t + 1)) := by
    have := range'_two_eq_map (fun r => 2 * r - (2 * t + 1)) t (t + 1)
      (fun r hr => by omega)
    convert this using 2; omega
  have m2 : List.range' (2 * t + 3) t 2 = (List.range' 1 t).map (fun r => (2 * t + 1) + 2 * r) := by
    have := range'_two_eq_map (fun r => (2 * t + 1) + 2 * r) t 1
      (fun r hr => by omega)
    convert this using 2
  rw [m1, m2, List.filter_map, List.filter_map]
  congr 2
  · apply List.filter_congr
    intro x hx
    simp only [List.mem_range'_1] at hx
    simp only [Function.comp, decide_eq_decide]
    exact cop_hi hn (by omega)
  · apply List.filter_congr
    intro x hx
    simp only [Function.comp, decide_eq_decide]
    exact cop_lo hn

/-- The reflection `r ↦ n - r` shows that equally many totatives of `n = 2t+1` lie below and
above `n/2`. -/
private lemma len_eq (t : ℕ) :
    ((List.range' 1 t).filter (fun r => Nat.Coprime r (2 * t + 1))).length =
      ((List.range' (t + 1) t).filter (fun r => Nat.Coprime r (2 * t + 1))).length := by
  have hm := map_sub_range' (2 * t + 1) t (by omega)
  rw [show 2 * t + 1 - t = t + 1 by omega] at hm
  rw [← List.length_reverse (as := List.filter _ (List.range' (t + 1) t)),
    ← List.filter_reverse, ← hm, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro x hx
  simp only [List.mem_range'_1] at hx
  simp only [Function.comp, decide_eq_decide]
  exact (Nat.coprime_self_sub_left (by omega)).symm

/-- For odd `n > 1`, writing `φ(n)/n = a/b` in lowest terms: `φ(2n)/(2n) = (a/2)/b` in lowest
terms (since `a` is even), and `a n = b φ(n)`. -/
private lemma rat_facts (n : ℕ) (hn : Odd n) (h1 : 1 < n) :
    A109395 (2 * n) = A109395 n ∧ A076512 (2 * n) * 2 = A076512 n ∧
      A076512 n * n = A109395 n * Nat.totient n := by
  set q : ℚ := (Nat.totient n : ℚ) / n with hqdef
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hq2 : (Nat.totient (2 * n) : ℚ) / ((2 * n : ℕ) : ℚ) = q / 2 := by
    rw [Nat.totient_mul (Nat.coprime_two_left.mpr hn), Nat.totient_two, hqdef]
    push_cast; ring
  have key : (q.num : ℚ) * n = q.den * Nat.totient n := by
    rw [← Rat.mul_den_eq_num q, hqdef]; field_simp
  have keyZ : q.num * n = q.den * Nat.totient n := by exact_mod_cast key
  have hev : Even q.num := by
    have h2 : Even ((q.den : ℤ) * Nat.totient n) := by
      apply Even.mul_left
      exact_mod_cast Nat.totient_even (n := n) (by obtain ⟨k, hk⟩ := hn; omega)
    rw [← keyZ, Int.even_mul] at h2
    rcases h2 with h2 | h2
    · exact h2
    · exact absurd (by exact_mod_cast h2 : Even n) (Nat.not_even_iff_odd.mpr hn)
  obtain ⟨c, hc⟩ := hev
  have hcop : Nat.Coprime c.natAbs (q.den : ℤ).natAbs := by
    have := q.reduced
    rw [hc, show c + c = 2 * c by ring, Int.natAbs_mul] at this
    simpa using Nat.Coprime.coprime_mul_left this
  have hdpos : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
  have hq2' : q / 2 = (c : ℚ) / ((q.den : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q, hc]
    push_cast; ring
  have hden := Rat.den_div_eq_of_coprime hdpos hcop
  have hnum := Rat.num_div_eq_of_coprime hdpos hcop
  rw [← hq2', ← hq2] at hden hnum
  refine ⟨?_, ?_, keyZ⟩
  · show ((Nat.totient (2 * n) : ℚ) / ((2 * n : ℕ) : ℚ)).den = q.den
    exact_mod_cast hden
  · show ((Nat.totient (2 * n) : ℚ) / ((2 * n : ℕ) : ℚ)).num * 2 = q.num
    rw [hnum, hc]; ring

/-- `getD` at a valid index is `getElem`. -/
private lemma getD_lt {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- If `φ(n) = h + h`, row `n` is the concatenation of its first `h` and last `h` entries. -/
private lemma row_split (n h : ℕ) (hφ : Nat.totient n = h + h) :
    row n = (List.range h).map (fun i => T n (i + 1)) ++
      (List.range h).map (fun i => T n (h + i + 1)) := by
  rw [row, hφ, List.range_add, List.map_append, List.map_map]
  rfl

/-- Charlie Neder's conjecture on A308121 holds: for odd `n > 1`, row `2n` is row `n` with its
two halves interchanged. -/
theorem result : statement := by
  intro n hn h1
  obtain ⟨t, rfl⟩ := hn
  have ht : 1 ≤ t := by omega
  have hNodd : Odd (2 * t + 1) := odd_two_mul_add_one t
  have htot := tot_split t ht
  have htot2 := tot2_split t ht
  have hlen := len_eq t
  set N := 2 * t + 1 with hN
  set L := (List.range' 1 t).filter (fun r => Nat.Coprime r N) with hL
  set H := (List.range' (t + 1) t).filter (fun r => Nat.Coprime r N) with hH
  set h := L.length with hh
  have hφ : Nat.totient N = h + h := by
    rw [← len_tot, htot, List.length_append]; omega
  have hφ2 : Nat.totient (2 * N) = h + h := by
    rw [← len_tot, htot2, List.length_append, List.length_map, List.length_map]; omega
  obtain ⟨e1, e2, e3⟩ := rat_facts N hNodd (by omega)
  rw [hφ] at e3
  have key : A076512 (2 * N) * N = (A109395 N : ℤ) * h := by
    have : 2 * (A076512 (2 * N) * N) = 2 * ((A109395 N : ℤ) * h) := by
      push_cast at e3
      linear_combination (N : ℤ) * e2 + e3
    exact Int.eq_of_mul_eq_mul_left (by norm_num) this
  refine ⟨_, _, row_split N h hφ, by simp, ?_⟩
  rw [row_split (2 * N) h hφ2]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    have hiH : i < H.length := by omega
    have hmem : H[i] ∈ List.range' (t + 1) t := List.mem_of_mem_filter (List.getElem_mem hiH)
    rw [List.mem_range'_1] at hmem
    simp only [T, Nat.add_sub_cancel]
    rw [htot2, htot, getD_lt (by simp; omega), getD_lt (by simp; omega),
      List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega),
      List.getElem_map, e1]
    have hsub : h + i - L.length = i := by omega
    simp only [hsub]
    push_cast [Nat.cast_sub (show N ≤ 2 * H[i] by omega)]
    linear_combination (-(H[i] : ℤ)) * e2 + key
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [T, Nat.add_sub_cancel]
    rw [htot2, htot, getD_lt (by simp; omega), getD_lt (by simp; omega),
      List.getElem_append_right (by simp; omega), List.getElem_append_left (by omega),
      List.getElem_map, e1]
    have hsub : h + i - (List.map (fun r => 2 * r - N) H).length = i := by
      rw [List.length_map]; omega
    simp only [hsub]
    push_cast
    linear_combination (-(L[i] : ℤ)) * e2 - key

end Math0.Frontier.A308121

#math0_settles Math0.Frontier.A308121.result Math0.Statements.A308121.statement
