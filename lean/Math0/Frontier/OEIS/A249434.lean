/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A249434
import Math0.Audit

/-!
# `A249151(k) = k` exactly when `k + 1` is prime

We prove Karttunen's conjecture (A249434 / A249151): for every `k`, `k` is the largest `m` with
`m ! ∣ rowProd k` (the product of row `k` of Pascal's triangle) iff `k + 1` is prime.

**Reduction.** The set `{m | m ! ∣ P}` is downward closed, so the claim is
`k ! ∣ P(k) ∧ ¬ (k+1)! ∣ P(k) ↔ (k+1).Prime`. Fix a prime `q`, put `n = k + 1`,
`g(m) = v_q(P(m))`, `L(m) = v_q(m!)`. From `P(n) n! = P(n-1) n^n` we get
`g(k) - L(k) = D := g(n) - (n-1) v_q(n)`, so `k ! ∣ P(k)` iff `D_q ≥ 0` for all `q`, and
`(k+1)! ∣ P(k)` iff `D_q ≥ v_q(n)` for all `q`.

**Recursions.** By induction from the recurrence, `g(q m + r) = q g(m) + (q-1-r)(m + L(m))` for
`r < q`, and Legendre gives `L(q m + r) = m + L(m)`. Iterating, for `n = q^e u` with `q ∤ u` and
`S = u - (q-1) L(u)` (the base-`q` digit sum of `u`, `S ≥ 1`):
`(q-1) D = q^e ((q-1) g(u) - S) + S + (q-1) e`.

**Key inequality.** If `g(u) ≥ 1` then `(q-1)(g(u) + L(u)) ≥ u`, i.e. `(q-1) g(u) ≥ S`
(strong induction on `u` via the recursion). Hence `D > e` when `g(u) ≥ 1`. When `g(u) = 0`,
`(q-1) D = (q-1) e - (q^e - 1) S < 0` unless `e = 1` and `S = 1`, i.e. `n = q`.

**Conclusion.** If `n` is prime, `D_q ≥ 0` for all `q` and `D_n = 0 < 1 = v_n(n)`. If `n` is not
prime, every `q ∣ n` has `q ≠ n`, so `D_q < 0` or `D_q ≥ v_q(n)`; thus `k ! ∣ P(k)` forces
`(k+1)! ∣ P(k)`.
-/

namespace Math0.Frontier.A249434
open Math0.Statements.A249434
open Nat

/-- The `q`-adic valuation of the row product `rowProd n`. -/
private def g (q n : ℕ) : ℕ := padicValNat q (rowProd n)

/-- The `q`-adic valuation of `n !`. -/
private def L (q n : ℕ) : ℕ := padicValNat q (n !)

/-- `rowProd 0 = 1`. -/
private lemma g_zero (q : ℕ) : g q 0 = 0 := by simp [g, rowProd]

/-- `rowProd 1 = 1`. -/
private lemma g_one (q : ℕ) : g q 1 = 0 := by simp [g, rowProd, Finset.prod_range_succ]

/-- `0 ! = 1`. -/
private lemma L_zero (q : ℕ) : L q 0 = 0 := by simp [L]

/-- `1 ! = 1`. -/
private lemma L_one (q : ℕ) : L q 1 = 0 := by simp [L]

/-- `q ∤ q m + r` for `0 < r < q`. -/
private lemma v_eq_zero (q m r : ℕ) (h0 : 0 < r) (h : r < q) :
    padicValNat q (q * m + r) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  rw [Nat.dvd_add_right (dvd_mul_right q m)]
  exact Nat.not_dvd_of_pos_of_lt h0 h

section Val

variable (q : ℕ) [hq : Fact q.Prime]

/-- Valuation form of `rowProd (n+1) * (n+1)! = rowProd n * (n+1)^(n+1)`. -/
private lemma rec_val (n : ℕ) :
    g q (n + 1) + L q (n + 1) = g q n + (n + 1) * padicValNat q (n + 1) := by
  have h := congrArg (padicValNat q) (rowProd_succ_mul n)
  rw [padicValNat.mul (rowProd_pos _).ne' (factorial_ne_zero _),
    padicValNat.mul (rowProd_pos _).ne' (pow_ne_zero _ (succ_ne_zero n)), padicValNat.pow] at h
  exact h

/-- Legendre recursion: `v_q((q m + r)!) = m + v_q(m!)` for `r < q`. -/
private lemma L_mul_add (m r : ℕ) (hr : r < q) : L q (q * m + r) = m + L q m := by
  unfold L
  rw [padicValNat_factorial_mul_add m hr, padicValNat_factorial_mul, add_comm]

/-- `v_q((q m)!) = m + v_q(m!)`. -/
private lemma L_mul (m : ℕ) : L q (q * m) = m + L q m := by
  simpa using L_mul_add q m 0 hq.out.pos

/-- `v_q(q m) = 1 + v_q(m)`. -/
private lemma v_mul (m : ℕ) (hm : m ≠ 0) : padicValNat q (q * m) = 1 + padicValNat q m := by
  rw [padicValNat.mul hq.out.ne_zero hm, padicValNat_self]

/-- One step inside a block `q m, …, q m + q - 1`. -/
private lemma step_inner (m r : ℕ) (h : r + 1 < q) :
    (g q (q * m + (r + 1)) : ℤ) = g q (q * m + r) - (m + L q m) := by
  have h1 := rec_val q (q * m + r)
  rw [add_assoc, v_eq_zero q m (r + 1) (succ_pos r) h, L_mul_add q m (r + 1) h] at h1
  have h2 : ((g q (q * m + (r + 1)) + (m + L q m) : ℕ) : ℤ) = (g q (q * m + r) : ℕ) := by
    rw [h1]; simp
  push_cast at h2
  linarith

/-- Inside a block: `g(q m + r) = g(q m) - r (m + L m)`. -/
private lemma block (m r : ℕ) (h : r < q) :
    (g q (q * m + r) : ℤ) = g q (q * m) - r * (m + L q m) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [step_inner q m r h, ih (by omega)]
    push_cast
    ring

/-- The basic recursion `g(q m) = q g(m) + (q - 1)(m + L m)`. -/
private lemma g_mul (m : ℕ) :
    (g q (q * m) : ℤ) = q * g q m + (q - 1) * (m + L q m) := by
  have hq1 := hq.out.one_lt
  induction m with
  | zero => simp [g_zero q, L_zero q]
  | succ m ih =>
    have e1 : q * m + (q - 1) + 1 = q * (m + 1) := by
      rw [Nat.mul_succ]; omega
    have hA := rec_val q (q * m + (q - 1))
    rw [e1, v_mul q (m + 1) (succ_ne_zero m), L_mul] at hA
    have hB := block q m (q - 1) (by omega)
    rw [ih] at hB
    have hE := rec_val q m
    have hc : (((q - 1 : ℕ)) : ℤ) = (q : ℤ) - 1 := by
      rw [Nat.cast_sub hq1.le, Nat.cast_one]
    rw [hc] at hB
    have hA' : ((g q (q * (m + 1)) + (m + 1 + L q (m + 1)) : ℕ) : ℤ) =
        ((g q (q * m + (q - 1)) + q * (m + 1) * (1 + padicValNat q (m + 1)) : ℕ) : ℤ) := by
      rw [hA]
    have hE' : ((g q (m + 1) + L q (m + 1) : ℕ) : ℤ) =
        ((g q m + (m + 1) * padicValNat q (m + 1) : ℕ) : ℤ) := by
      rw [hE]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hA' hE'
    simp only [Nat.cast_add, Nat.cast_one]
    linear_combination hA' + hB - q * hE'

/-- `g(q m + r) = q g(m) + (q - 1 - r)(m + L m)` for `r < q`. -/
private lemma g_mul_add (m r : ℕ) (hr : r < q) :
    (g q (q * m + r) : ℤ) = q * g q m + (q - 1 - r) * (m + L q m) := by
  rw [block q m r hr, g_mul]
  ring

/-- `(q - 1) v_q(u!) < u` for `u ≠ 0`. -/
private lemma S_pos (u : ℕ) (hu : u ≠ 0) : ((q : ℤ) - 1) * L q u + 1 ≤ u := by
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero q hu
  have hc : (((q - 1 : ℕ)) : ℤ) = (q : ℤ) - 1 := by
    rw [Nat.cast_sub hq.out.one_lt.le, Nat.cast_one]
  have h' : (((q - 1) * padicValNat q u ! : ℕ) : ℤ) < (u : ℤ) := by exact_mod_cast h
  rw [Nat.cast_mul, hc] at h'
  unfold L
  linarith

/-- The base-`q` digit sum `u - (q - 1) v_q(u!)` of `u ≥ 2` with `q ∤ u` is at least `2`. -/
private lemma S_two (u : ℕ) (hu : 2 ≤ u) (hqu : ¬ q ∣ u) : ((q : ℤ) - 1) * L q u + 2 ≤ u := by
  have hq0 := hq.out.pos
  have hu' : u = q * (u / q) + u % q := (Nat.div_add_mod u q).symm
  have hr : u % q < q := Nat.mod_lt _ hq0
  have hr0 : 0 < u % q := by
    rcases Nat.eq_zero_or_pos (u % q) with h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) hqu
    · exact h
  have hL := L_mul_add q (u / q) (u % q) hr
  rw [← hu'] at hL
  rcases Nat.eq_zero_or_pos (u / q) with hm | hm
  · rw [hm, L_zero q] at hL
    rw [hL]; push_cast; linarith
  · have h1 := S_pos q (u / q) hm.ne'
    have hu'' : (u : ℤ) = q * (u / q : ℕ) + (u % q : ℕ) := by exact_mod_cast hu'
    rw [hL, hu'']
    push_cast
    have : (1 : ℤ) ≤ ((u % q : ℕ) : ℤ) := by exact_mod_cast hr0
    nlinarith

/-- Key lemma: if `g(u) ≥ 1` then `(q - 1)(g(u) + L(u)) ≥ u`. -/
private lemma key_ineq (u : ℕ) (hg : 1 ≤ g q u) :
    (u : ℤ) ≤ ((q : ℤ) - 1) * (g q u + L q u) := by
  have hq1 := hq.out.one_lt
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    have hu' : u = q * (u / q) + u % q := (Nat.div_add_mod u q).symm
    have hr : u % q < q := Nat.mod_lt _ (by omega)
    have hg' := g_mul_add q (u / q) (u % q) hr
    have hL := L_mul_add q (u / q) (u % q) hr
    rw [← hu'] at hg' hL
    have hu'' : (u : ℤ) = q * (u / q : ℕ) + (u % q : ℕ) := by exact_mod_cast hu'
    set m := u / q with hm
    set r := u % q with hrdef
    have hgm : (0 : ℤ) ≤ g q m := by positivity
    have hLm : (0 : ℤ) ≤ L q m := by positivity
    have hr0 : (0 : ℤ) ≤ r := by positivity
    have hgu : (1 : ℤ) ≤ g q u := by exact_mod_cast hg
    have hqZ : (2 : ℤ) ≤ q := by exact_mod_cast hq1
    rw [hL, hu'']
    push_cast
    rcases Nat.lt_or_ge (r + 1) q with hrq | hrq
    · -- `r ≤ q - 2`
      have hrqZ : (r : ℤ) + 2 ≤ q := by exact_mod_cast hrq
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · rw [hm0, g_zero q, L_zero q] at hg'
        push_cast at hg'
        linarith
      · have hmZ : (1 : ℤ) ≤ m := by exact_mod_cast hm0
        rw [hg']
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ m) (by linarith : (0:ℤ) ≤ q))
          (by linarith : (0:ℤ) ≤ q - r - 2), mul_nonneg hr0 (by linarith : (0:ℤ) ≤ m - 1),
          mul_nonneg (by linarith : (0:ℤ) ≤ q - 1) hgm,
          mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ q - 1) (by linarith : (0:ℤ) ≤ q)) hgm,
          mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ q - 1) (by linarith : (0:ℤ) ≤ q - r))
            hLm]
    · -- `r = q - 1`
      have hrq' : r + 1 = q := by omega
      have hrZ : (r : ℤ) = q - 1 := by
        have : ((r + 1 : ℕ) : ℤ) = q := by exact_mod_cast hrq'
        push_cast at this; linarith
      rw [hrZ] at hg'
      have hg'' : (g q u : ℤ) = q * g q m := by rw [hg']; ring
      have hgm1 : 1 ≤ g q m := by
        by_contra hcon
        have : g q m = 0 := by omega
        rw [this] at hg''
        push_cast at hg''
        linarith
      have hu0 : u ≠ 0 := by
        rintro rfl
        rw [g_zero q] at hg
        omega
      have hmu : m < u := Nat.div_lt_self (Nat.pos_of_ne_zero hu0) hq1
      have ih' := ih m hmu hgm1
      rw [hg'', hrZ]
      have hgm1Z : (1 : ℤ) ≤ g q m := by exact_mod_cast hgm1
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ q - 1)
          (by linarith : (0:ℤ) ≤ q - 1)) (by linarith : (0:ℤ) ≤ g q m - 1),
        mul_nonneg (by linarith : (0:ℤ) ≤ q - 2) (by linarith : (0:ℤ) ≤ q - 1)]

/-- `(q - 1) L(q^e u) = (q - 1) L(u) + (q^e - 1) u`. -/
private lemma L_pow (e u : ℕ) :
    ((q : ℤ) - 1) * L q (q ^ e * u) = (q - 1) * L q u + ((q : ℤ) ^ e - 1) * u := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h1 : q ^ (e + 1) * u = q * (q ^ e * u) := by ring
    rw [h1, L_mul]
    push_cast
    linear_combination ih

/-- Closed form of `g(q^e u)`, multiplied by `q - 1`. -/
private lemma g_pow (e u : ℕ) :
    ((q : ℤ) - 1) * g q (q ^ e * u) = (q : ℤ) ^ e * ((q - 1) * g q u - (u - (q - 1) * L q u))
      + (q - 1) * e * q ^ e * u + (u - (q - 1) * L q u) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h1 : q ^ (e + 1) * u = q * (q ^ e * u) := by ring
    rw [h1, g_mul]
    have hL := L_pow q e u
    push_cast
    linear_combination q * ih + (q - 1) * hL

/-- For `e ≥ 2`, `q^e - 1 > (q - 1) e`. -/
private lemma pow_gt (e : ℕ) : ((q : ℤ) - 1) * (e + 2) + 1 < (q : ℤ) ^ (e + 2) := by
  have hqZ : (2 : ℤ) ≤ q := by exact_mod_cast hq.out.one_lt
  induction e with
  | zero => push_cast; nlinarith
  | succ e ih =>
    push_cast at ih ⊢
    rw [pow_succ]
    have ih' : ((q : ℤ) - 1) * (e + 2) + 2 ≤ (q : ℤ) ^ (e + 2) := by linarith
    have he : (0 : ℤ) ≤ e := by positivity
    nlinarith [mul_le_mul_of_nonneg_right ih' (by linarith : (0 : ℤ) ≤ q),
      mul_nonneg (by linarith : (0 : ℤ) ≤ q - 1)
        (by nlinarith : (0 : ℤ) ≤ (e + 2) * (q - 1) + 1)]

/-- `v_q(rowProd k) - v_q(k!) = g(k+1) - k v_q(k+1)`. -/
private lemma key_rel (k : ℕ) :
    (g q k : ℤ) - L q k = g q (k + 1) - k * padicValNat q (k + 1) := by
  have h1 := rec_val q k
  have h2 : L q (k + 1) = L q k + padicValNat q (k + 1) := by
    unfold L
    rw [factorial_succ, padicValNat.mul (succ_ne_zero k) (factorial_ne_zero k), add_comm]
  have h1' : ((g q (k + 1) + L q (k + 1) : ℕ) : ℤ) =
      ((g q k + (k + 1) * padicValNat q (k + 1) : ℕ) : ℤ) := by rw [h1]
  have h2' : ((L q (k + 1) : ℕ) : ℤ) = ((L q k + padicValNat q (k + 1) : ℕ) : ℤ) := by rw [h2]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h1' h2'
  linear_combination h2' - h1'

/-- `q`-part of `k ! ∣ rowProd k`. -/
private lemma val_fact_iff (k : ℕ) :
    padicValNat q (k !) ≤ padicValNat q (rowProd k) ↔
      (0 : ℤ) ≤ g q (k + 1) - k * padicValNat q (k + 1) := by
  rw [← key_rel q k]
  change L q k ≤ g q k ↔ _
  constructor
  · intro h
    have : (L q k : ℤ) ≤ g q k := by exact_mod_cast h
    linarith
  · intro h
    have : (L q k : ℤ) ≤ g q k := by linarith
    exact_mod_cast this

/-- `q`-part of `(k + 1)! ∣ rowProd k`. -/
private lemma val_fact_succ_iff (k : ℕ) :
    padicValNat q ((k + 1)!) ≤ padicValNat q (rowProd k) ↔
      (padicValNat q (k + 1) : ℤ) ≤ g q (k + 1) - k * padicValNat q (k + 1) := by
  rw [← key_rel q k, factorial_succ, padicValNat.mul (succ_ne_zero k) (factorial_ne_zero k)]
  change padicValNat q (k + 1) + L q k ≤ g q k ↔ _
  constructor
  · intro h
    have : ((padicValNat q (k + 1) + L q k : ℕ) : ℤ) ≤ g q k := by exact_mod_cast h
    rw [Nat.cast_add] at this
    linarith
  · intro h
    have : ((padicValNat q (k + 1) + L q k : ℕ) : ℤ) ≤ g q k := by
      rw [Nat.cast_add]; linarith
    exact_mod_cast this

/-- `g(q) = q - 1`. -/
private lemma g_self : (g q q : ℤ) = q - 1 := by
  have h := g_mul q 1
  rw [mul_one, g_one q, L_one q] at h
  rw [h]
  push_cast
  ring

/-- The dichotomy: if `q ∣ n` and `n ≠ q`, then with `D = g(n) - (n - 1) v_q(n)`, either
`D < 0` or `D ≥ v_q(n)`. -/
private lemma dichotomy (n : ℕ) (hn : n ≠ 0) (hdvd : q ∣ n) (hne : n ≠ q) :
    (g q n : ℤ) - ((n : ℤ) - 1) * padicValNat q n < 0 ∨
      (padicValNat q n : ℤ) ≤ (g q n : ℤ) - ((n : ℤ) - 1) * padicValNat q n := by
  obtain ⟨e, u, hqu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q hq.out.ne_one
  have hu0 : u ≠ 0 := by rintro rfl; simp at hn
  have hv : padicValNat q (q ^ e * u) = e := by
    rw [padicValNat.mul (pow_ne_zero _ hq.out.ne_zero) hu0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hqu, add_zero]
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      rw [pow_zero, one_mul] at hdvd
      exact absurd hdvd hqu
    · exact h
  rw [hv]
  have hG := g_pow q e u
  have hS1 := S_pos q u hu0
  have hqZ : (2 : ℤ) ≤ q := by exact_mod_cast hq.out.one_lt
  have hcast : ((q ^ e * u : ℕ) : ℤ) = (q : ℤ) ^ e * u := by push_cast; ring
  rw [hcast]
  have hqe : (1 : ℤ) ≤ (q : ℤ) ^ e := one_le_pow₀ (by linarith)
  set D := (g q (q ^ e * u) : ℤ) - ((q : ℤ) ^ e * u - 1) * e with hD
  set S := (u : ℤ) - (q - 1) * L q u with hS
  rcases Nat.eq_zero_or_pos (g q u) with hg0 | hg1
  · left
    rw [hg0] at hG
    have key : ((q : ℤ) - 1) * D = -(((q : ℤ) ^ e - 1) * S) + (q - 1) * e := by
      rw [hD]; push_cast at hG; linear_combination hG
    have hneg : ((q : ℤ) - 1) * D < 0 := by
      rw [key]
      rcases Nat.lt_or_ge e 2 with he2 | he2
      · have he1 : e = 1 := by omega
        subst he1
        have hu2 : 2 ≤ u := by
          rcases Nat.lt_or_ge u 2 with h | h
          · have : u = 1 := by omega
            subst this
            simp at hne
          · exact h
        have hS2 := S_two q u hu2 hqu
        push_cast
        nlinarith
      · obtain ⟨d, rfl⟩ : ∃ d, e = d + 2 := ⟨e - 2, by omega⟩
        have hpg := pow_gt q d
        push_cast at hpg ⊢
        nlinarith [mul_le_mul_of_nonneg_left (by linarith : (1 : ℤ) ≤ S)
          (by linarith : (0 : ℤ) ≤ (q : ℤ) ^ (d + 2) - 1)]
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ q - 1) hcon]
  · right
    have hK := key_ineq q u hg1
    have hK' : (0 : ℤ) ≤ (q - 1) * g q u - S := by rw [hS]; linarith
    have key : ((q : ℤ) - 1) * D = (q : ℤ) ^ e * ((q - 1) * g q u - S) + S + (q - 1) * e := by
      rw [hD, hS]; rw [hS] at hK'; linear_combination hG
    have hpos : ((q : ℤ) - 1) * (D - e) ≥ 1 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ (q : ℤ) ^ e) hK']
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ q - 1) (by linarith : (0 : ℤ) ≤ e - D)]

end Val

/-- `IsGreatest` reduces to `k ! ∣ P ∧ ¬ (k + 1)! ∣ P`, since the set is downward closed. -/
private lemma isGreatest_iff (k P : ℕ) :
    IsGreatest {m : ℕ | m ! ∣ P} k ↔ k ! ∣ P ∧ ¬ (k + 1)! ∣ P := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => absurd (h2 h) (by omega)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun m hm => ?_⟩
    by_contra hlt
    exact h2 ((factorial_dvd_factorial (by omega)).trans hm)

/-- Divisibility of `rowProd k` via `p`-adic valuations. -/
private lemma dvd_rowProd_iff (k d : ℕ) (hd : d ≠ 0) :
    d ∣ rowProd k ↔ ∀ q, q.Prime → padicValNat q d ≤ padicValNat q (rowProd k) := by
  rw [← Nat.factorization_prime_le_iff_dvd hd (rowProd_pos k).ne']
  refine forall_congr' fun q => forall_congr' fun hq => ?_
  rw [Nat.factorization_def _ hq, Nat.factorization_def _ hq]

/-- Karttunen's conjecture: `A249151(k) = k` iff `k + 1` is prime. -/
theorem result : statement := by
  intro k
  rw [isGreatest_iff]
  by_cases hp : (k + 1).Prime
  · simp only [hp, iff_true]
    constructor
    · refine (dvd_rowProd_iff k _ (factorial_ne_zero k)).2 fun q hq => ?_
      have := Fact.mk hq
      rw [val_fact_iff]
      by_cases hqn : q ∣ k + 1
      · have hqe : q = k + 1 := (Nat.prime_dvd_prime_iff_eq hq hp).1 hqn
        have hg := g_self q
        rw [← hqe, padicValNat_self, hg, hqe]
        push_cast
        linarith
      · rw [padicValNat.eq_zero_of_not_dvd hqn]
        push_cast
        linarith [(Nat.cast_nonneg (g q (k + 1)) : (0 : ℤ) ≤ _)]
    · intro h
      have h' := (dvd_rowProd_iff k _ (factorial_ne_zero _)).1 h (k + 1) hp
      have := Fact.mk hp
      rw [val_fact_succ_iff, padicValNat_self, g_self] at h'
      push_cast at h'
      linarith
  · simp only [hp, iff_false, not_and, not_not]
    intro h1
    refine (dvd_rowProd_iff k _ (factorial_ne_zero _)).2 fun q hq => ?_
    have h1q := (dvd_rowProd_iff k _ (factorial_ne_zero k)).1 h1 q hq
    have := Fact.mk hq
    rw [val_fact_iff] at h1q
    rw [val_fact_succ_iff]
    by_cases hqn : q ∣ k + 1
    · have hne : k + 1 ≠ q := fun h => hp (h ▸ hq)
      have hd := dichotomy q (k + 1) (succ_ne_zero k) hqn hne
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hd
      rcases hd with hd | hd
      · linarith
      · exact hd
    · rw [padicValNat.eq_zero_of_not_dvd hqn] at h1q ⊢
      push_cast at h1q ⊢
      linarith

end Math0.Frontier.A249434

#math0_settles Math0.Frontier.A249434.result Math0.Statements.A249434.statement
