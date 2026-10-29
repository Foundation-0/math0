/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A123710
import Math0.Audit

/-!
# A123710: the rows of `inv(⌊n/k⌋)` with four nonzero entries are `6` and the proper prime powers

We prove Hasler's conjecture `a(n) = A025475(n)` for `n > 2`.

**Closed form of the inverse.** Let `g n k = μ(n/k)` if `k ∣ n` and `0` otherwise. Then row `n`
of the inverse of `A(n,k) = ⌊n/k⌋` is `T(n,k) = g n k - g n (k+1)` (`T_eq_F`). Indeed, by Abel
summation and `⌊k/j⌋ - ⌊(k-1)/j⌋ = [j ∣ k]`,
`∑_k (g n k - g n (k+1)) ⌊k/j⌋ = ∑_{j ∣ k ∣ n} μ(n/k) = ∑_{d ∣ n/j} μ(d) = [j = n]` (`key`), so
these rows form a left inverse of every truncation, which must be the matrix inverse.

**Counting.** Hence `A123709 n` is the number of `k ∈ [1, n]` with `g n k ≠ g n (k+1)`
(`A123709_eq_card`); every such `k` has `g n k ≠ 0` or `g n (k+1) ≠ 0`.
* For `n = p^a`, `a ≥ 2`, `g n` is supported on `{p^(a-1), p^a}` with values `-1, 1`, and the
  change points are exactly `p^(a-1) - 1, p^(a-1), p^a - 1, p^a` (`card_C_pp`).
* For `n = p` prime the change points lie in `{1, p - 1, p}` (`card_C_prime`).
* If `p < q` are primes dividing `n ≠ 6`, then with `A = n/p`: `A - 1, A, n - 1, n` are change
  points (`A ± 1` cannot divide `n`, since consecutive divisors `d, d+1` of `n` give
  `d(d+1) ∣ n`), and since `g n (n/q) = -1 ≠ 0 = g n (A - 1)` with `n/q < A - 1`, there is one
  more change point in `[n/q, A - 1)` (`card_C_two`). So there are at least `5`.
Together with `A123709 1 = 1`, `A123709 6 = 4` this gives
`IsTerm n ↔ n = 6 ∨ n` is a proper prime power (`isTerm_iff`).

**Indexing.** Both predicates agree from `7` on and have exactly two elements below `7`, so their
`nth` elements agree from index `2` on (`nth_shift`).
-/

namespace Math0.Frontier.A123710
open Math0.Statements.A123710
open Finset

/-! ### The closed form of the inverse -/

/-- `g n k = μ(n / k)` if `k ∣ n`, and `0` otherwise. -/
private def g (n k : ℕ) : ℤ := if k ∣ n then ArithmeticFunction.moebius (n / k) else 0

/-- The closed form of row `n` of the inverse: `F n k = g n k - g n (k + 1)`. -/
private def F (n k : ℕ) : ℤ := g n k - g n (k + 1)

/-- `g n k = 0` when `k ∤ n`. -/
private lemma g_eq_zero {n k : ℕ} (h : ¬ k ∣ n) : g n k = 0 := by simp [g, h]

/-- `g n k = 0` when `0 < n < k`. -/
private lemma g_of_gt {n k : ℕ} (hn : 1 ≤ n) (h : n < k) : g n k = 0 :=
  g_eq_zero fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)

/-- `g n n = μ 1 = 1`. -/
private lemma g_self {n : ℕ} (hn : 1 ≤ n) : g n n = 1 := by
  rw [g, if_pos dvd_rfl, Nat.div_self (by omega), ArithmeticFunction.moebius_apply_one]

/-- `g n (n / q) = μ q = -1` for a prime `q ∣ n`. -/
private lemma g_div_prime {n q : ℕ} (hn : 1 ≤ n) (hq : q.Prime) (hqn : q ∣ n) :
    g n (n / q) = -1 := by
  rw [g, if_pos (Nat.div_dvd_of_dvd hqn), Nat.div_div_self hqn (by omega),
    ArithmeticFunction.moebius_apply_prime hq]

/-- `F n k = 0` when `0 < n < k`. -/
private lemma F_of_gt {n k : ℕ} (hn : 1 ≤ n) (h : n < k) : F n k = 0 := by
  rw [F, g_of_gt hn h, g_of_gt hn (by omega), sub_zero]

/-- Abel summation. -/
private lemma abel (u v : ℕ → ℤ) (N : ℕ) :
    ∑ l ∈ range N, (u (l + 1) - u (l + 1 + 1)) * v (l + 1) =
      ∑ l ∈ range N, u (l + 1) * (v (l + 1) - v l) - u (N + 1) * v N + u 1 * v 0 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih, sum_range_succ]; ring

/-- `∑_{d ∣ m} μ d = [m = 1]`. -/
private lemma sum_moebius_divisors (m : ℕ) :
    ∑ d ∈ m.divisors, ArithmeticFunction.moebius d = if m = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
    ArithmeticFunction.one_apply]

/-- `∑_{d ∣ n, j ∣ d} μ(n/d) = [j = n]`. -/
private lemma sum_divisors_dvd {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    ∑ d ∈ n.divisors, (if j ∣ d then ArithmeticFunction.moebius (n / d) else 0) =
      if j = n then 1 else 0 := by
  have h1 : ∑ d ∈ n.divisors, (if j ∣ d then ArithmeticFunction.moebius (n / d) else 0) =
      ∑ d ∈ n.divisors, (if j ∣ n / d then ArithmeticFunction.moebius d else 0) := by
    rw [← Nat.sum_div_divisors n (fun d => if j ∣ n / d then ArithmeticFunction.moebius d else 0)]
    refine sum_congr rfl fun d hd => ?_
    rw [Nat.mem_divisors] at hd
    rw [Nat.div_div_self hd.1 hd.2]
  rw [h1]
  by_cases hjn : j ∣ n
  · obtain ⟨m, rfl⟩ := hjn
    have hm : m ≠ 0 := by rintro rfl; simp at hn
    have h2 : ∀ d ∈ (j * m).divisors,
        (if j ∣ j * m / d then ArithmeticFunction.moebius d else 0) =
          if d ∣ m then ArithmeticFunction.moebius d else 0 := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      have : j ∣ j * m / d ↔ d ∣ m := by
        rw [Nat.dvd_div_iff_mul_dvd hd.1, mul_comm d j]
        exact Nat.mul_dvd_mul_iff_left (by omega)
      simp only [this]
    rw [sum_congr rfl h2]
    rw [← sum_subset (Nat.divisors_subset_of_dvd (by omega) (Dvd.intro_left j rfl))]
    · rw [sum_congr rfl (fun d hd => if_pos (Nat.dvd_of_mem_divisors hd)), sum_moebius_divisors]
      by_cases hm1 : m = 1
      · subst hm1; simp
      · rw [if_neg hm1, if_neg]
        intro h
        apply hm1
        exact (Nat.eq_of_mul_eq_mul_left (by omega : 0 < j) (by rw [mul_one]; exact h)).symm
    · intro d _ hd
      rw [if_neg]
      exact fun h => hd (Nat.mem_divisors.2 ⟨h, hm⟩)
  · rw [if_neg (fun h : j = n => hjn (by rw [h]))]
    exact sum_eq_zero fun d hd =>
      if_neg fun h => hjn (h.trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))

/-- Row `n` of `F · A = I`: `∑_{k=1}^{n} F(n,k) ⌊k/j⌋ = [j = n]`. -/
private lemma key {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    ∑ l ∈ range n, F n (l + 1) * (((l + 1) / j : ℕ) : ℤ) = if j = n then 1 else 0 := by
  have e1 := abel (g n) (fun l => ((l / j : ℕ) : ℤ)) n
  simp only [Nat.zero_div, Nat.cast_zero, mul_zero, add_zero] at e1
  rw [g_of_gt hn (by omega : n < n + 1), zero_mul, sub_zero] at e1
  simp only [F]
  rw [e1, ← sum_divisors_dvd hn hj]
  have e2 : ∀ l, (((l + 1) / j : ℕ) : ℤ) - ((l / j : ℕ) : ℤ) = if j ∣ l + 1 then 1 else 0 := by
    intro l
    rw [Nat.succ_div]
    split_ifs <;> push_cast <;> ring
  simp only [e2]
  rw [Nat.divisors, sum_filter, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine sum_congr rfl fun l _ => ?_
  rw [add_comm 1 l, g]
  split_ifs <;> simp

/-- The `N × N` truncation of `F`. -/
private def Fmat (N : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  Matrix.of fun i j => F ((i : ℕ) + 1) ((j : ℕ) + 1)

/-- `F` is a left inverse of every truncation of `⌊n/k⌋`. -/
private lemma Fmat_mul_floorMat (N : ℕ) : Fmat N * floorMat N = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Fmat, floorMat, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun l => F ((i : ℕ) + 1) (l + 1) * (((l + 1) / ((j : ℕ) + 1) : ℕ) : ℤ)) N]
  have hi := i.isLt
  have hN : range N = range (((i : ℕ) + 1) + (N - ((i : ℕ) + 1))) := by congr 1; omega
  rw [hN, Finset.sum_range_add, key (by omega) (by omega)]
  rw [Finset.sum_eq_zero (s := range (N - ((i : ℕ) + 1))) fun x _ => by
    rw [F_of_gt (by omega) (by omega), zero_mul], add_zero]
  by_cases e : i = j
  · subst e; simp
  · rw [if_neg e, if_neg]
    intro e'
    exact e (Fin.ext (by omega))

/-- The closed form of the inverse: `T n k = g n k - g n (k + 1)` for `1 ≤ k ≤ n`. -/
private lemma T_eq_F {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : T n k = F n k := by
  have h : Tmat n = Fmat n := by rw [Tmat_eq_inv, Matrix.inv_eq_left_inv (Fmat_mul_floorMat n)]
  have := congrFun (congrFun h ⟨n - 1, by omega⟩) ⟨k - 1, by omega⟩
  simp only [Tmat, Fmat, Matrix.of_apply] at this
  rwa [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.sub_add_cancel hk] at this

/-! ### Counting the change points -/

/-- The change points of `g n` in `[1, n]`: the nonzero entries of row `n`. -/
private def C (n : ℕ) : Finset ℕ := {k ∈ Icc 1 n | F n k ≠ 0}

private lemma A123709_eq_card (n : ℕ) : A123709 n = #(C n) := by
  rw [A123709, C]
  congr 1
  refine filter_congr fun k hk => ?_
  rw [mem_Icc] at hk
  rw [A123706_eq_T, T_eq_F hk.1 hk.2]

private lemma mem_C {n k : ℕ} : k ∈ C n ↔ 1 ≤ k ∧ k ≤ n ∧ g n k ≠ g n (k + 1) := by
  simp only [C, mem_filter, mem_Icc, F, ne_eq, sub_eq_zero, and_assoc]

private lemma ne_zero_of_ne {x y : ℤ} (h : x ≠ y) : x ≠ 0 ∨ y ≠ 0 := by
  by_cases hx : x = 0
  · exact Or.inr fun hy => h (hx.trans hy.symm)
  · exact Or.inl hx

/-- Two consecutive divisors `d, d + 1` of `n` satisfy `d (d + 1) ∣ n`. -/
private lemma consec {d n : ℕ} (h1 : d ∣ n) (h2 : d + 1 ∣ n) : d * (d + 1) ∣ n :=
  (Nat.coprime_self_add_right.2 (Nat.coprime_one_right d)).mul_dvd_of_dvd_of_dvd h1 h2

/-- `g n (n - 1) = 0` for `n ≥ 3`. -/
private lemma g_pred {n : ℕ} (hn : 3 ≤ n) : g n (n - 1) = 0 := by
  apply g_eq_zero
  intro hd
  obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hd
  have := (Nat.coprime_self_add_right.2 (Nat.coprime_one_right c)).eq_one_of_dvd hd
  omega

/-- A discrete intermediate value statement: if `u a ≠ u (a + d)`, `u` changes somewhere in
`[a, a + d)`. -/
private lemma ivt (u : ℕ → ℤ) (a : ℕ) :
    ∀ d, u a ≠ u (a + d) → ∃ j, a ≤ j ∧ j < a + d ∧ u j ≠ u (j + 1)
  | 0, h => absurd rfl h
  | d + 1, h => by
    by_cases h' : u a = u (a + d)
    · exact ⟨a + d, by omega, by omega, fun e => h (h'.trans e)⟩
    · obtain ⟨j, h1, h2, h3⟩ := ivt u a d h'
      exact ⟨j, h1, by omega, h3⟩

/-- For a proper prime power `p ^ a` there are exactly four change points. -/
private lemma card_C_pp {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) : #(C (p ^ a)) = 4 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  have hp2 := hp.two_le
  have hB2 : 2 ≤ p ^ (b + 1) := le_trans hp2 (Nat.le_self_pow (by omega) p)
  have hnB : 2 * p ^ (b + 1) ≤ p ^ (b + 2) := by
    rw [pow_succ p (b + 1), mul_comm]; exact Nat.mul_le_mul_left _ hp2
  have hn1 : 1 ≤ p ^ (b + 2) := by omega
  have hdiv : p ^ (b + 2) / p = p ^ (b + 1) := by
    rw [pow_succ p (b + 1), Nat.mul_div_cancel _ hp.pos]
  have supp : ∀ k, g (p ^ (b + 2)) k ≠ 0 → k = p ^ (b + 1) ∨ k = p ^ (b + 2) := by
    intro k hk
    by_cases hkd : k ∣ p ^ (b + 2)
    · obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 hkd
      rw [g, if_pos hkd, Nat.pow_div hi hp.pos] at hk
      by_cases h0 : b + 2 - i = 0
      · right; congr 1; omega
      · rw [ArithmeticFunction.moebius_apply_prime_pow hp h0] at hk
        split_ifs at hk with h1
        · left; congr 1; omega
        · exact absurd rfl hk
    · exact absurd (g_eq_zero hkd) hk
  have gz : ∀ k, k ≠ p ^ (b + 1) → k ≠ p ^ (b + 2) → g (p ^ (b + 2)) k = 0 := fun k h1 h2 => by
    by_contra h
    rcases supp k h with h' | h' <;> contradiction
  have gB : g (p ^ (b + 2)) (p ^ (b + 1)) = -1 := by
    rw [← hdiv]; exact g_div_prime hn1 hp (dvd_pow_self p (by omega))
  have gN : g (p ^ (b + 2)) (p ^ (b + 2)) = 1 := g_self hn1
  generalize p ^ (b + 2) = N at *
  generalize p ^ (b + 1) = B at *
  have hC : C N = {B - 1, B, N - 1, N} := by
    ext k
    rw [mem_C]
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases ne_zero_of_ne h3 with h | h
      · rcases supp _ h with h | h <;> omega
      · rcases supp _ h with h | h <;> omega
    · rintro (rfl | rfl | rfl | rfl)
      · refine ⟨by omega, by omega, ?_⟩
        rw [gz _ (by omega) (by omega), show B - 1 + 1 = B by omega, gB]; norm_num
      · refine ⟨by omega, by omega, ?_⟩
        rw [gB, gz _ (by omega) (by omega)]; norm_num
      · refine ⟨by omega, by omega, ?_⟩
        rw [gz _ (by omega) (by omega), show N - 1 + 1 = N by omega, gN]; norm_num
      · refine ⟨by omega, le_rfl, ?_⟩
        rw [gN, gz _ (by omega) (by omega)]; norm_num
  rw [hC, card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; omega),
    card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; omega),
    card_insert_of_notMem (by simp only [mem_singleton]; omega), card_singleton]

/-- For a prime `p` there are at most three change points. -/
private lemma card_C_prime {p : ℕ} (hp : p.Prime) : #(C p) ≤ 3 := by
  have supp : ∀ k, g p k ≠ 0 → k = 1 ∨ k = p := fun k hk => by
    by_cases hkd : k ∣ p
    · exact hp.eq_one_or_self_of_dvd k hkd
    · exact absurd (g_eq_zero hkd) hk
  have hsub : C p ⊆ {1, p - 1, p} := by
    intro k hk
    rw [mem_C] at hk
    obtain ⟨h1, h2, h3⟩ := hk
    simp only [mem_insert, mem_singleton]
    rcases ne_zero_of_ne h3 with h | h
    · rcases supp _ h with h | h <;> omega
    · rcases supp _ h with h | h <;> omega
  exact (card_le_card hsub).trans card_le_three

/-- If `p` and `p + 1` are both prime, then `p = 2`. -/
private lemma eq_two_of_succ {p : ℕ} (hp : p.Prime) (hq : (p + 1).Prime) : p = 2 := by
  rcases hp.eq_two_or_odd' with h | ⟨r, hr⟩
  · exact h
  · have h2 := hp.two_le
    rcases hq.eq_one_or_self_of_dvd 2 ⟨r + 1, by omega⟩ with h | h <;> omega

/-- If two primes `p < q` divide `n ≠ 6`, there are at least five change points. -/
private lemma card_C_two {n p q : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpn : p ∣ n) (hqn : q ∣ n) (h6 : n ≠ 6) : 5 ≤ #(C n) := by
  have hp2 := hp.two_le
  have hq3 : 3 ≤ q := by omega
  obtain ⟨m, hnm⟩ : p * q ∣ n :=
    ((Nat.coprime_primes hp hq).2 hpq.ne).mul_dvd_of_dvd_of_dvd hpn hqn
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hnm; omega
    · exact h
  have hA : n / p = q * m := by rw [hnm, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  have hB : n / q = p * m := by
    rw [hnm, mul_comm p q, mul_assoc, Nat.mul_div_cancel_left _ hq.pos]
  have hnA : n = q * m * p := by rw [hnm]; ring
  have gN := g_self hn
  have gA : g n (q * m) = -1 := hA ▸ g_div_prime hn hp hpn
  have gB : g n (p * m) = -1 := hB ▸ g_div_prime hn hq hqn
  have hnot : ¬ (m = 1 ∧ q = p + 1) := by
    rintro ⟨rfl, rfl⟩
    have := eq_two_of_succ hp hq
    subst this
    exact h6 (by rw [hnm])
  have hA3 : 3 ≤ q * m := le_trans hq3 (Nat.le_mul_of_pos_right q hm)
  have hnA2 : 2 * (q * m) ≤ n := by rw [hnA, mul_comm _ p]; exact Nat.mul_le_mul_right _ hp2
  have hBA : p * m + 2 ≤ q * m := by
    rcases Nat.eq_or_lt_of_le hm with h | h
    · subst h
      have : q ≠ p + 1 := fun e => hnot ⟨rfl, e⟩
      rw [mul_one, mul_one]
      omega
    · nlinarith
  have hB1 : 2 ≤ p * m := le_trans hp2 (Nat.le_mul_of_pos_right p hm)
  have gA1 : g n (q * m + 1) = 0 := by
    apply g_eq_zero
    intro hd
    have h1 := consec (⟨p, hnA⟩ : q * m ∣ n) hd
    rw [hnA] at h1
    have h2 := Nat.le_of_dvd hp.pos (Nat.dvd_of_mul_dvd_mul_left (by omega) h1)
    have : q ≤ q * m := Nat.le_mul_of_pos_right q hm
    omega
  have gAm : g n (q * m - 1) = 0 := by
    apply g_eq_zero
    intro hd
    obtain ⟨c, hc⟩ : ∃ c, q * m = c + 1 := ⟨q * m - 1, by omega⟩
    rw [hc, Nat.add_sub_cancel] at hd
    have h1 := consec hd (⟨p, hc ▸ hnA⟩ : c + 1 ∣ n)
    rw [hnA, hc, mul_comm c] at h1
    have h2 := Nat.dvd_of_mul_dvd_mul_left (by omega) h1
    rcases hp.eq_one_or_self_of_dvd c h2 with h3 | h3
    · omega
    · apply hnot
      have hm1 : m = 1 := by
        by_contra hm1
        have : 2 ≤ m := by omega
        nlinarith
      subst hm1
      omega
  have gn1 : g n (n - 1) = 0 := g_pred (by omega)
  have gnp : g n (n + 1) = 0 := g_of_gt hn (by omega)
  clear hA hB hnot hnA hnm
  generalize q * m = A at *
  generalize p * m = B at *
  obtain ⟨j, hj1, hj2, hj3⟩ := ivt (g n) B (A - 1 - B) (by
    rw [show B + (A - 1 - B) = A - 1 by omega, gB, gAm]; norm_num)
  have hsub : ({j, A - 1, A, n - 1, n} : Finset ℕ) ⊆ C n := by
    intro k hk
    simp only [mem_insert, mem_singleton] at hk
    rw [mem_C]
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, by omega, hj3⟩
    · refine ⟨by omega, by omega, ?_⟩
      rw [show A - 1 + 1 = A by omega, gAm, gA]; norm_num
    · refine ⟨by omega, by omega, ?_⟩
      rw [gA, gA1]; norm_num
    · refine ⟨by omega, by omega, ?_⟩
      rw [show n - 1 + 1 = n by omega, gn1, gN]; norm_num
    · refine ⟨by omega, le_rfl, ?_⟩
      rw [gN, gnp]; norm_num
  have hcard : #({j, A - 1, A, n - 1, n} : Finset ℕ) = 5 := by
    rw [card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; omega),
      card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; omega),
      card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; omega),
      card_insert_of_notMem (by simp only [mem_singleton]; omega), card_singleton]
  exact hcard ▸ card_le_card hsub

/-! ### The terms of A123710 -/

/-- `n` is a term of A123710 iff `n = 6` or `n` is a proper prime power. -/
private lemma isTerm_iff (n : ℕ) : IsTerm n ↔ n = 6 ∨ ∃ p k, p.Prime ∧ 2 ≤ k ∧ n = p ^ k := by
  rw [IsTerm]
  constructor
  · intro h
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · rw [A123709_eq_Rf] at h; exact absurd h (by decide +kernel)
      · rw [A123709_eq_Rf] at h; exact absurd h (by decide +kernel)
    · rw [A123709_eq_card] at h
      obtain ⟨p, hpdef⟩ : ∃ p, p = n.minFac := ⟨_, rfl⟩
      have hp : p.Prime := hpdef ▸ Nat.minFac_prime (by omega)
      have hpn : p ∣ n := hpdef ▸ Nat.minFac_dvd n
      have hmin : ∀ q, q.Prime → q ∣ n → p ≤ q := fun q hq hqn =>
        hpdef ▸ Nat.minFac_le_of_dvd hq.two_le hqn
      clear hpdef
      by_cases hall : ∀ d, d.Prime → d ∣ n → d = p
      · obtain ⟨e, he⟩ : ∃ e, n = p ^ e :=
          ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (fun hd hdn => hall _ hd hdn)⟩
        rcases e with _ | _ | e
        · rw [pow_zero] at he; omega
        · rw [pow_one] at he
          subst he
          have := card_C_prime hp
          omega
        · exact Or.inr ⟨p, e + 2, hp, by omega, he⟩
      · push Not at hall
        obtain ⟨q, hq, hqn, hqp⟩ := hall
        have hpq : p < q := lt_of_le_of_ne (hmin q hq hqn) (Ne.symm hqp)
        by_cases h6 : n = 6
        · exact Or.inl h6
        · have := card_C_two (by omega) hp hq hpq hpn hqn h6
          omega
  · rintro (rfl | ⟨p, k, hp, hk, rfl⟩)
    · rw [A123709_eq_Rf]; decide +kernel
    · rw [A123709_eq_card, card_C_pp hp hk]

/-- Two predicates that agree from `K` on and have the same count below `K` have the same counts
from `K` on. -/
private lemma count_shift {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] {K : ℕ}
    (hpq : ∀ x, K ≤ x → (p x ↔ q x)) (hc : Nat.count p K = Nat.count q K) :
    ∀ b, Nat.count p (K + b) = Nat.count q (K + b)
  | 0 => hc
  | b + 1 => by
    rw [← add_assoc, Nat.count_succ, Nat.count_succ, count_shift hpq hc b]
    by_cases h : p (K + b)
    · rw [if_pos h, if_pos ((hpq _ (by omega)).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((hpq _ (by omega)).2 h'))]

/-- Two predicates that agree from `K` on and have the same count `c` below `K` (the second one
holding infinitely often) have the same `nth` elements from index `c` on. -/
private lemma nth_shift {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] {K : ℕ}
    (hpq : ∀ x, K ≤ x → (p x ↔ q x)) (hc : Nat.count p K = Nat.count q K)
    (hq : (Set.ofPred q).Infinite) (i : ℕ) :
    Nat.nth p (Nat.count q K + i) = Nat.nth q (Nat.count q K + i) := by
  obtain ⟨x, hx⟩ : ∃ x, x = Nat.nth q (Nat.count q K + i) := ⟨_, rfl⟩
  have hqx : q x := hx ▸ Nat.nth_mem_of_infinite hq _
  have hcx : Nat.count q x = Nat.count q K + i := hx ▸ Nat.count_nth_of_infinite hq _
  have hKx : K ≤ x := by
    by_contra hlt
    have h1 := Nat.count_monotone q (show x + 1 ≤ K by omega)
    rw [Nat.count_succ, if_pos hqx] at h1
    omega
  have hpx : p x := (hpq x hKx).2 hqx
  have hcp : Nat.count p x = Nat.count q x := by
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hKx
    rw [hb]
    exact count_shift hpq hc b
  rw [← hx, ← hcx, ← hcp, Nat.nth_count hpx]

/-- Hasler's conjecture: from the third term on, A123710 lists the proper prime powers, i.e.
`a n = A025475 n` for `n > 2`. -/
theorem result : statement := by
  intro n hn
  have hT : ∀ x, 7 ≤ x → (IsTerm x ↔ IsA025475 x) := by
    intro x hx
    rw [isTerm_iff, IsA025475]
    constructor
    · rintro (h | h)
      · omega
      · exact Or.inr h
    · rintro (h | h)
      · omega
      · exact Or.inr h
  have c1 : Nat.count IsTerm 7 = 2 := by decide +kernel
  have c2 : Nat.count IsA025475 7 = 2 := by decide +kernel
  have hinf : (Set.ofPred IsA025475).Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 ^ (k + 2))
      (fun a b h => by
        have := Nat.pow_right_injective (le_refl 2) h
        simpa using this)
      (fun k => Or.inr ⟨2, k + 2, Nat.prime_two, by omega, rfl⟩)
  have := nth_shift hT (c1.trans c2.symm) hinf (n - 3)
  rw [c2] at this
  rw [a, A025475, show n - 1 = 2 + (n - 3) by omega]
  exact this

end Math0.Frontier.A123710

#math0_settles Math0.Frontier.A123710.result Math0.Statements.A123710.statement
