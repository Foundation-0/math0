/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A129455
import Math0.Audit

/-!
# The triple-gcd Pascal triangle A129455: integrality and sixth powers

We prove Peter Bala's conjecture: writing `G(m) = A129454(m+1) = ∏_{i,j,k ∈ [1,m]} gcd(i,j,k)`,
for all `0 ≤ k ≤ n` the quotient `T(n,k) = G(n)/(G(k) G(n-k))` is an integer, `C(n,k) ∣ T(n,k)`,
and `T(n,k)/C(n,k)` is a perfect sixth power.

**Idea.** Let `L(d) = p` if `d = p^t` is a prime power and `L(d) = 1` otherwise (so
`log L = Λ`, the von Mangoldt function). Since `∑_{d ∣ g} Λ(d) = log g`, every `g ≥ 1` satisfies
`g = ∏_{d ∣ g} L(d)`. Applying this to every `gcd(i,j,k)` and to every factor of `m!`, and
counting multiples of `d` in `[1,m]`, we get for `m ≤ N`
`G(m) = ∏_{d=1}^N L(d)^{⌊m/d⌋^3}` and `m! = ∏_{d=1}^N L(d)^{⌊m/d⌋}`.
Fix `d ≥ 1` and put `F = ⌊n/d⌋`, `A = ⌊k/d⌋`, `B = ⌊(n-k)/d⌋`; then `F = A + B + c` with
`c ∈ {0,1}`. Hence `C(n,k) = n!/(k!(n-k)!) = ∏ L(d)^c`, and
`F^3 = A^3 + B^3 + c + 3(AB(A+B) + c(A+B)(A+B+1))`, where `AB(A+B)` and `(A+B)(A+B+1)` are
even. So `G(n) = G(k) G(n-k) C(n,k) M^6` with `M = ∏ L(d)^{e_d}`,
`e_d = (AB(A+B) + c(A+B)(A+B+1))/2`, which gives all three claims at once.
-/

namespace Math0.Frontier.A129455
open Math0.Statements.A129455

/-- `L d = p` when `d` is a power `p ^ t` (`t ≥ 1`) of a prime `p`, and `1` otherwise; its
logarithm is the von Mangoldt function. -/
private def L (d : ℕ) : ℕ := if IsPrimePow d then d.minFac else 1

/-- `L` is positive. -/
private lemma L_pos (d : ℕ) : 0 < L d := by
  unfold L
  split_ifs
  · exact Nat.minFac_pos _
  · exact one_pos

/-- `log (L d) = Λ d`. -/
private lemma log_L (d : ℕ) : Real.log (L d : ℝ) = ArithmeticFunction.vonMangoldt d := by
  rw [ArithmeticFunction.vonMangoldt_apply]
  unfold L
  split_ifs <;> simp

/-- Every positive `g` is the product of `L d` over the divisors `d` of `g`. -/
private lemma prod_divisors_L (g : ℕ) (hg : 0 < g) : ∏ d ∈ g.divisors, L d = g := by
  have h1 : (0 : ℝ) < ((∏ d ∈ g.divisors, L d : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun d _ => L_pos d
  have h2 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have h3 : Real.log ((∏ d ∈ g.divisors, L d : ℕ) : ℝ) = Real.log g := by
    rw [Nat.cast_prod, Real.log_prod (fun d _ => by exact_mod_cast (L_pos d).ne'),
      ← ArithmeticFunction.vonMangoldt_sum]
    exact Finset.sum_congr rfl fun d _ => log_L d
  exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.2 h1) (Set.mem_Ioi.2 h2) h3

/-- For `1 ≤ g ≤ N`, `g = ∏_{d=1}^N L(d)^{[d ∣ g]}`. -/
private lemma decomp (N g : ℕ) (hg : 0 < g) (hgN : g ≤ N) :
    g = ∏ d ∈ Finset.Icc 1 N, L d ^ (if d ∣ g then 1 else 0) := by
  have hfilt : (Finset.Icc 1 N).filter (· ∣ g) = g.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨h, hg.ne'⟩
    · rintro ⟨h, _⟩
      have := Nat.le_of_dvd hg h
      have : 0 < d := Nat.pos_of_dvd_of_pos h hg
      exact ⟨⟨this, by omega⟩, h⟩
  simp only [pow_ite, pow_one, pow_zero]
  rw [← Finset.prod_filter, hfilt, prod_divisors_L g hg]

/-- The number of multiples of `d` in `[1, m]` is `m / d`. -/
private lemma count_mult (d m : ℕ) :
    ∑ i ∈ Finset.Icc 1 m, (if d ∣ i then 1 else 0) = m / d := by
  rw [Finset.sum_boole]
  have : Finset.Icc 1 m = Finset.Ioc 0 m := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [this]
  exact_mod_cast Nat.Ioc_filter_dvd_card_eq_div m d

/-- `m! = ∏_{d=1}^N L(d)^{⌊m/d⌋}` for `m ≤ N`. -/
private lemma factorial_eq (N m : ℕ) (hm : m ≤ N) :
    m.factorial = ∏ d ∈ Finset.Icc 1 N, L d ^ (m / d) := by
  have h1 : m.factorial = ∏ i ∈ Finset.Icc 1 m, i := by
    rw [← Finset.prod_Ico_id_eq_factorial]
    rfl
  rw [h1]
  calc ∏ i ∈ Finset.Icc 1 m, i
      = ∏ i ∈ Finset.Icc 1 m, ∏ d ∈ Finset.Icc 1 N, L d ^ (if d ∣ i then 1 else 0) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [Finset.mem_Icc] at hi
        exact decomp N i (by omega) (by omega)
    _ = ∏ d ∈ Finset.Icc 1 N, ∏ i ∈ Finset.Icc 1 m, L d ^ (if d ∣ i then 1 else 0) :=
        Finset.prod_comm
    _ = ∏ d ∈ Finset.Icc 1 N, L d ^ (m / d) := by
        refine Finset.prod_congr rfl fun d _ => ?_
        rw [Finset.prod_pow_eq_pow_sum, count_mult]

/-- `A129454 (m+1) = ∏_{d=1}^N L(d)^{⌊m/d⌋^3}` for `m ≤ N`. -/
private lemma G_eq (N m : ℕ) (hm : m ≤ N) :
    A129454 (m + 1) = ∏ d ∈ Finset.Icc 1 N, L d ^ ((m / d) ^ 3) := by
  unfold A129454
  rw [Nat.add_sub_cancel]
  calc ∏ i ∈ Finset.Icc 1 m, ∏ j ∈ Finset.Icc 1 m, ∏ k ∈ Finset.Icc 1 m,
        Nat.gcd (Nat.gcd i j) k
      = ∏ i ∈ Finset.Icc 1 m, ∏ j ∈ Finset.Icc 1 m, ∏ k ∈ Finset.Icc 1 m,
          ∏ d ∈ Finset.Icc 1 N, L d ^ (if d ∣ Nat.gcd (Nat.gcd i j) k then 1 else 0) := by
        refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ =>
          Finset.prod_congr rfl fun k hk => ?_
        rw [Finset.mem_Icc] at hk
        exact decomp N _ (Nat.gcd_pos_of_pos_right _ (by omega))
          (le_trans (Nat.gcd_le_right _ (by omega)) (by omega))
    _ = ∏ i ∈ Finset.Icc 1 m, ∏ j ∈ Finset.Icc 1 m, ∏ d ∈ Finset.Icc 1 N,
          ∏ k ∈ Finset.Icc 1 m, L d ^ (if d ∣ Nat.gcd (Nat.gcd i j) k then 1 else 0) :=
        Finset.prod_congr rfl fun _ _ => Finset.prod_congr rfl fun _ _ => Finset.prod_comm
    _ = ∏ i ∈ Finset.Icc 1 m, ∏ d ∈ Finset.Icc 1 N, ∏ j ∈ Finset.Icc 1 m,
          ∏ k ∈ Finset.Icc 1 m, L d ^ (if d ∣ Nat.gcd (Nat.gcd i j) k then 1 else 0) :=
        Finset.prod_congr rfl fun _ _ => Finset.prod_comm
    _ = ∏ d ∈ Finset.Icc 1 N, ∏ i ∈ Finset.Icc 1 m, ∏ j ∈ Finset.Icc 1 m,
          ∏ k ∈ Finset.Icc 1 m, L d ^ (if d ∣ Nat.gcd (Nat.gcd i j) k then 1 else 0) :=
        Finset.prod_comm
    _ = ∏ d ∈ Finset.Icc 1 N, L d ^ ((m / d) ^ 3) := by
        refine Finset.prod_congr rfl fun d _ => ?_
        simp only [Finset.prod_pow_eq_pow_sum]
        congr 1
        have hsplit : ∀ i j k : ℕ, (if d ∣ Nat.gcd (Nat.gcd i j) k then 1 else 0) =
            (if d ∣ i then 1 else 0) * (if d ∣ j then 1 else 0) * (if d ∣ k then 1 else 0) := by
          intro i j k
          simp only [Nat.dvd_gcd_iff]
          by_cases hi : d ∣ i <;> by_cases hj : d ∣ j <;> by_cases hk : d ∣ k <;> simp [hi, hj, hk]
        simp only [hsplit, ← Finset.mul_sum, ← Finset.sum_mul, count_mult]
        ring

/-- Parity: `AB(A+B) + c(A+B)(A+B+1)` is even. -/
private lemma two_dvd (A B c : ℕ) : 2 ∣ A * B * (A + B) + c * (A + B) * (A + B + 1) := by
  rw [← even_iff_two_dvd]
  have h1 : Even (A * B * (A + B)) := by
    rcases Nat.even_or_odd A with hA | hA
    · exact (hA.mul_right B).mul_right _
    · rcases Nat.even_or_odd B with hB | hB
      · exact (hB.mul_left A).mul_right _
      · exact (hA.add_odd hB).mul_left _
  have h2 : Even (c * (A + B) * (A + B + 1)) := by
    rw [mul_assoc]
    exact (Nat.even_mul_succ_self (A + B)).mul_left c
  exact h1.add h2

/-- The cubic identity behind the sixth powers. -/
private lemma cube_identity (A B c : ℕ) (hc : c = 0 ∨ c = 1) :
    (A + B + c) ^ 3 =
      A ^ 3 + B ^ 3 + c + 6 * ((A * B * (A + B) + c * (A + B) * (A + B + 1)) / 2) := by
  obtain ⟨q, hq⟩ := two_dvd A B c
  rw [hq, Nat.mul_div_cancel_left q (by norm_num)]
  rcases hc with rfl | rfl
  · nlinarith [hq]
  · nlinarith [hq]

/-- The main identity: `G(n) = G(n-k) G(k) (C(n,k) M^6)`. -/
private lemma main_identity (n k : ℕ) (hk : k ≤ n) :
    ∃ M : ℕ, A129454 (n + 1) = A129454 (n - k + 1) * A129454 (k + 1) * (n.choose k * M ^ 6) := by
  set c : ℕ → ℕ := fun d => if d ≤ k % d + (n - k) % d then 1 else 0 with hc_def
  have hF : ∀ d ∈ Finset.Icc 1 n, n / d = k / d + (n - k) / d + c d := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have := Nat.add_div (a := k) (b := n - k) (c := d) (by omega)
    rw [Nat.add_sub_cancel' hk] at this
    exact this
  have hc01 : ∀ d, c d = 0 ∨ c d = 1 := by
    intro d
    simp only [hc_def]
    split_ifs <;> simp
  set e : ℕ → ℕ := fun d =>
    ((k / d) * ((n - k) / d) * (k / d + (n - k) / d) +
      c d * (k / d + (n - k) / d) * (k / d + (n - k) / d + 1)) / 2 with he_def
  refine ⟨∏ d ∈ Finset.Icc 1 n, L d ^ e d, ?_⟩
  -- binomial coefficient
  have hchoose : n.choose k = ∏ d ∈ Finset.Icc 1 n, L d ^ c d := by
    have h1 := Nat.choose_mul_factorial_mul_factorial hk
    rw [factorial_eq n n le_rfl, factorial_eq n k hk, factorial_eq n (n - k) (Nat.sub_le n k)]
      at h1
    have h2 : ∏ d ∈ Finset.Icc 1 n, L d ^ (n / d) =
        (∏ d ∈ Finset.Icc 1 n, L d ^ c d) *
          ((∏ d ∈ Finset.Icc 1 n, L d ^ (k / d)) *
            ∏ d ∈ Finset.Icc 1 n, L d ^ ((n - k) / d)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun d hd => ?_
      rw [hF d hd, ← pow_add, ← pow_add]
      ring_nf
    rw [h2, mul_assoc] at h1
    have hpos : 0 < (∏ d ∈ Finset.Icc 1 n, L d ^ (k / d)) *
        ∏ d ∈ Finset.Icc 1 n, L d ^ ((n - k) / d) := by
      apply Nat.mul_pos <;> exact Finset.prod_pos fun d _ => pow_pos (L_pos d) _
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  rw [G_eq n n le_rfl, G_eq n (n - k) (Nat.sub_le n k), G_eq n k hk, hchoose,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun d hd => ?_
  have hcube :
      (k / d + (n - k) / d + c d) ^ 3 = (k / d) ^ 3 + ((n - k) / d) ^ 3 + c d + 6 * e d :=
    cube_identity (k / d) ((n - k) / d) (c d) (hc01 d)
  rw [hF d hd, hcube]
  ring

/-- A129454 is positive. -/
private lemma A129454_pos (m : ℕ) : 0 < A129454 m := by
  unfold A129454
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => Finset.prod_pos fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  exact Nat.gcd_pos_of_pos_right _ (by omega)

/-- Bala's conjecture on A129455 holds: `T(n,k)` is an integer, `C(n,k) ∣ T(n,k)`, and
`T(n,k)/C(n,k)` is a perfect sixth power. -/
theorem result : statement := by
  intro n k hk
  obtain ⟨M, hM⟩ := main_identity n k hk
  have hpos : 0 < A129454 (n - k + 1) * A129454 (k + 1) :=
    Nat.mul_pos (A129454_pos _) (A129454_pos _)
  have hT : T n k = n.choose k * M ^ 6 := by
    unfold T
    rw [hM, Nat.mul_div_cancel_left _ hpos]
  refine ⟨Dvd.intro _ hM.symm, ?_, M, ?_⟩
  · rw [hT]
    exact dvd_mul_right _ _
  · rw [hT, Nat.mul_div_cancel_left _ (Nat.choose_pos hk)]

end Math0.Frontier.A129455

#math0_settles Math0.Frontier.A129455.result Math0.Statements.A129455.statement
