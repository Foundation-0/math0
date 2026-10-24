/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A119936
import Math0.Audit

/-!
# The row-LCM of denominators of the cube of the mean matrix is `n · lcm(1..n)²`

We prove Wolfdieter Lang's conjecture (A119936): `a(n)/n³ = A002944(n)²`, i.e.
`a(n) = n · L²` with `L = lcm(1, …, n)`.

Write `D = n · L²` and `N(m) = ∑_{m ≤ l ≤ k ≤ n} L²/(k l)` (each summand is a natural number since
`k, l ∣ L`). Then `N(m) = D · r(n,m)` by `r_eq_explicit`. Writing `r = num/den` in lowest terms,
`|num| · D = N(m) · den`, so:

* `den ∣ D` for every `m` (as `den` is coprime to `num`), hence `a(n) ∣ D`;
* if `p ∤ N(m)` then every prime power `p^k ∣ D` divides `den`.

For a prime `p` let `e = ⌊log_p n⌋` (so `v_p(L) = e`) and `m = ⌊n/p^e⌋ · p^e`. The only
multiple of `p^e` in `[m, n]` is `m` itself, so for every pair `(k, l) ≠ (m, m)` one of `k, l`
has `v_p < e`, the other `v_p ≤ e`, hence `p ∣ L²/(k l)`; while `p ∤ L²/m²` because
`v_p(L²) = 2e ≤ v_p(m²)`. Thus `p ∤ N(m)`, and every prime power dividing `D` divides `a(n)`,
so `D ∣ a(n)`.
-/

namespace Math0.Frontier.A119936
open Math0.Statements.A119936

/-- Every `k ∈ [1, n]` divides `lcm(1, …, n)`. -/
private lemma dvd_lcmUpTo {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) : k ∣ lcmUpTo n :=
  Finset.dvd_lcm (s := Finset.Icc 1 n) (f := id) (Finset.mem_Icc.2 ⟨hk1, hkn⟩)

/-- `lcm(1, …, n) ≠ 0`. -/
private lemma lcmUpTo_ne_zero (n : ℕ) : lcmUpTo n ≠ 0 := Nat.lcmUpto_ne_zero n

/-- The `p`-adic valuation of `lcm(1, …, n)` is `⌊log_p n⌋`. -/
private lemma factorization_lcmUpTo (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (lcmUpTo n).factorization p = Nat.log p n := Nat.factorization_lcmUpto n hp

/-- `k l ∣ L²` for `k, l ∈ [1, n]`. -/
private lemma mul_dvd_sq {n k l : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hl : 1 ≤ l) (hln : l ≤ n) :
    k * l ∣ lcmUpTo n ^ 2 := by
  rw [sq]
  exact mul_dvd_mul (dvd_lcmUpTo hk hkn) (dvd_lcmUpTo hl hln)

/-- The row entry scaled by `n · L²`: `N n m = ∑_{m ≤ l ≤ k ≤ n} L²/(k l)`. -/
private def N (n m : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc m n, ∑ l ∈ Finset.Icc m k, lcmUpTo n ^ 2 / (k * l)

/-- `N n m = n · L² · r(n, m)`. -/
private lemma N_cast {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ((N n m : ℕ) : ℚ) = ((n * lcmUpTo n ^ 2 : ℕ) : ℚ) * r n m := by
  rw [r_eq_explicit hm hmn, N]
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h1 : ((n * lcmUpTo n ^ 2 : ℕ) : ℚ) *
      (1 / (n : ℚ) * ∑ k ∈ Finset.Icc m n, ∑ l ∈ Finset.Icc m k, 1 / ((k : ℚ) * l)) =
      ((lcmUpTo n : ℚ) ^ 2) * ∑ k ∈ Finset.Icc m n, ∑ l ∈ Finset.Icc m k, 1 / ((k : ℚ) * l) := by
    push_cast
    field_simp
  rw [h1, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mem_Icc] at hk hl
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast (show l ≠ 0 by omega)
  rw [Nat.cast_div (mul_dvd_sq (by omega) hk.2 (by omega) (by omega)) (by push_cast; positivity)]
  push_cast
  field_simp

/-- If `M = D · q` with `M, D` natural, then `|num q| · D = M · den q`. -/
private lemma num_mul_eq {q : ℚ} {D M : ℕ} (h : (M : ℚ) = (D : ℚ) * q) :
    q.num.natAbs * D = M * q.den := by
  have hq : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
  have h2 : (q.num * D : ℤ) = (M * q.den : ℤ) := by
    have : ((q.num * D : ℤ) : ℚ) = ((M * q.den : ℤ) : ℚ) := by
      push_cast
      rw [hq, h]
      ring
    exact_mod_cast this
  have h3 := congrArg Int.natAbs h2
  simpa [Int.natAbs_mul] using h3

/-- If `M = D · q` with `M, D` natural, then `den q ∣ D`. -/
private lemma den_dvd_of {q : ℚ} {D M : ℕ} (h : (M : ℚ) = (D : ℚ) * q) : q.den ∣ D := by
  have := num_mul_eq h
  refine Nat.Coprime.dvd_of_dvd_mul_left q.reduced.symm ⟨M, ?_⟩
  rw [this, Nat.mul_comm]

/-- If `M = D · q` with `M, D` natural and the prime `p` does not divide `M`, then every power
`p^k ∣ D` divides `den q`. -/
private lemma pow_dvd_den {q : ℚ} {D M p k : ℕ} (h : (M : ℚ) = (D : ℚ) * q) (hp : p.Prime)
    (hM : ¬ p ∣ M) (hk : p ^ k ∣ D) : p ^ k ∣ q.den := by
  have := num_mul_eq h
  have hc : Nat.Coprime (p ^ k) M :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hM)
  refine hc.dvd_of_dvd_mul_left ?_
  rw [← this]
  exact Dvd.dvd.mul_left hk _

/-- For `1 ≤ k ≤ n`, `v_p(k) ≤ ⌊log_p n⌋`. -/
private lemma factorization_le_log {p n k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkn : k ≤ n) :
    k.factorization p ≤ Nat.log p n :=
  Nat.le_log_of_pow_le hp.one_lt
    ((Nat.le_of_dvd (by omega) (Nat.ordProj_dvd k p)).trans hkn)

/-- If not both `k` and `l` are multiples of `p^e` (`e = ⌊log_p n⌋`), then `p ∣ L²/(k l)`. -/
private lemma p_dvd_term {p n k l : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkn : k ≤ n) (hl : 1 ≤ l)
    (hln : l ≤ n) (h : ¬ (p ^ Nat.log p n ∣ k ∧ p ^ Nat.log p n ∣ l)) :
    p ∣ lcmUpTo n ^ 2 / (k * l) := by
  have hq : lcmUpTo n ^ 2 / (k * l) * (k * l) = lcmUpTo n ^ 2 :=
    Nat.div_mul_cancel (mul_dvd_sq hk hkn hl hln)
  by_contra hnd
  have hpL : p ^ Nat.log p n ∣ lcmUpTo n :=
    (hp.pow_dvd_iff_le_factorization (lcmUpTo_ne_zero n)).2
      (factorization_lcmUpTo n hp).ge
  have hpe : p ^ (2 * Nat.log p n) ∣ lcmUpTo n ^ 2 := by
    rw [pow_mul']
    exact pow_dvd_pow_of_dvd hpL 2
  have hc : Nat.Coprime (p ^ (2 * Nat.log p n)) (lcmUpTo n ^ 2 / (k * l)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
  have hkl : p ^ (2 * Nat.log p n) ∣ k * l := by
    refine hc.dvd_of_dvd_mul_left ?_
    rw [hq]
    exact hpe
  rw [hp.pow_dvd_iff_le_factorization (by positivity),
    Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply] at hkl
  have hke := factorization_le_log hp hk hkn
  have hle := factorization_le_log hp hl hln
  apply h
  rw [hp.pow_dvd_iff_le_factorization (by omega), hp.pow_dvd_iff_le_factorization (by omega)]
  omega

/-- For a multiple `m ≥ 1` of `p^e` (`e = ⌊log_p n⌋`), `p ∤ L²/(m m)`. -/
private lemma not_p_dvd_term {p n m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hpm : p ^ Nat.log p n ∣ m) : ¬ p ∣ lcmUpTo n ^ 2 / (m * m) := by
  have hq : lcmUpTo n ^ 2 / (m * m) * (m * m) = lcmUpTo n ^ 2 :=
    Nat.div_mul_cancel (mul_dvd_sq hm hmn hm hmn)
  intro hd
  have h1 : p ^ (2 * Nat.log p n + 1) ∣ lcmUpTo n ^ 2 := by
    rw [← hq, pow_succ, mul_comm, two_mul, pow_add]
    exact mul_dvd_mul hd (mul_dvd_mul hpm hpm)
  rw [hp.pow_dvd_iff_le_factorization (pow_ne_zero 2 (lcmUpTo_ne_zero n)),
    Nat.factorization_pow, Finsupp.smul_apply, factorization_lcmUpTo n hp, smul_eq_mul] at h1
  omega

/-- For every prime `p` there is a column `m` with `p ∤ N n m`. -/
private lemma exists_good {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) :
    ∃ m, 1 ≤ m ∧ m ≤ n ∧ ¬ p ∣ N n m := by
  set e := Nat.log p n with he
  have hpe : p ^ e ≤ n := Nat.pow_log_le_self p (by omega)
  have hpe0 : 0 < p ^ e := pow_pos hp.pos e
  set c := n / p ^ e with hc
  have hc1 : 1 ≤ c := Nat.div_pos hpe hpe0
  have hlt : n < p ^ e * (c + 1) := Nat.lt_mul_div_succ n hpe0
  refine ⟨c * p ^ e, ?_, Nat.div_mul_le_self n (p ^ e), ?_⟩
  · nlinarith
  have hmn : c * p ^ e ≤ n := Nat.div_mul_le_self n (p ^ e)
  have hm1 : 1 ≤ c * p ^ e := by nlinarith
  have hmem : c * p ^ e ∈ Finset.Icc (c * p ^ e) n := Finset.mem_Icc.2 ⟨le_rfl, hmn⟩
  rw [N, ← Finset.add_sum_erase _ _ hmem, Finset.Icc_self, Finset.sum_singleton]
  have hrest : p ∣ ∑ k ∈ (Finset.Icc (c * p ^ e) n).erase (c * p ^ e),
      ∑ l ∈ Finset.Icc (c * p ^ e) k, lcmUpTo n ^ 2 / (k * l) := by
    refine Finset.dvd_sum fun k hk => Finset.dvd_sum fun l hl => ?_
    rw [Finset.mem_erase, Finset.mem_Icc] at hk
    rw [Finset.mem_Icc] at hl
    refine p_dvd_term hp (by omega) hk.2.2 (by omega) (by omega) ?_
    rintro ⟨⟨j, hj⟩, -⟩
    rw [← he] at hj
    have h1 : c * p ^ e < p ^ e * j := by omega
    have h2 : p ^ e * j < p ^ e * (c + 1) := by omega
    have h3 : c < j := by nlinarith
    have h4 : j < c + 1 := Nat.lt_of_mul_lt_mul_left h2
    omega
  intro hd
  exact not_p_dvd_term hp hm1 hmn (dvd_mul_left _ _) ((Nat.dvd_add_left hrest).1 hd)

/-- The integer form: `a(n) = n · lcm(1, …, n)²` for `n ≥ 1`. -/
private lemma a_eq {n : ℕ} (hn : 1 ≤ n) : a n = n * lcmUpTo n ^ 2 := by
  apply Nat.dvd_antisymm
  · refine Finset.lcm_dvd fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    exact den_dvd_of (N_cast hm.1 hm.2)
  · rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    obtain ⟨m, hm1, hmn, hpN⟩ := exists_good hp hn
    exact (pow_dvd_den (N_cast hm1 hmn) hp hpN hpk).trans
      (Finset.dvd_lcm (Finset.mem_Icc.2 ⟨hm1, hmn⟩))

/-- Lang's conjecture: `a(n)/n³ = A002944(n)²` for all `n ≥ 1`. -/
theorem result : statement :=
  statement_iff.2 fun _ hn => a_eq hn

end Math0.Frontier.A119936

#math0_settles Math0.Frontier.A119936.result Math0.Statements.A119936.statement
