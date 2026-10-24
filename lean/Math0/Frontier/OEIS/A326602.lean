/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A326602
import Math0.Audit

/-!
# A326602: `a n` is odd iff `n` is a square

We prove Hanna's conjecture: the coefficient `a n` of `x^(2n)` in
`∑_{n ≥ 0} (x^(2n-1) + 1)^n x^n / (1 + x^(2n+1))^(n+1)` is odd iff `n` is a perfect square.

Idea. Write `p = x`, `s = x^(2n)`, so the `n`-th summand is `(p + s)^n / (1 + p s)^(n+1)`.
Expanding, the coefficient of `x^N` in the `n`-th summand is the sum, over `i ≤ n` and `j ≥ 0`
with `n + (2n-1) i + (2n+1) j = N`, of `(-1)^j C(n,i) C(n+j,j)`. Put `m = i + j`: the exponent
becomes `n + m + 2nm - 2i` and (up to sign) the weight becomes the trinomial coefficient
`T n m i = C(n+m-i, i) C(n+m-2i, n-i) = (n+m-i)! / (i! (n-i)! (m-i)!)`. Both are symmetric in
`n, m`. Hence, mod 2, `coeff N A` is the sum of `T n m i` over the finite set of triples
`(n, i, m)` with `i ≤ n`, `i ≤ m`, `n + m + 2nm = N + 2i`, and the involution `n ↔ m` cancels all
off-diagonal triples. On the diagonal `n = m`, `T n n i = C(2n-i, i) C(2(n-i), n-i)` is even
unless `i = n` (central binomial coefficients are even), and the triple `(n, n, n)` has exponent
`2n²` and weight `1`. So `A ≡ ∑_k x^(2k²) (mod 2)`.
-/

namespace Math0.Frontier.A326602
open Math0.Statements.A326602

/-- The symmetric weight `T n m i = C(n+m-i, i) C(n+m-2i, n-i)`. -/
private def T (n m i : ℕ) : ℕ := (n + m - i).choose i * (n + m - 2 * i).choose (n - i)

/-- `T` is symmetric in its first two arguments. -/
private theorem T_symm {n m i : ℕ} (hn : i ≤ n) (hm : i ≤ m) : T n m i = T m n i := by
  unfold T
  rw [add_comm m n]
  congr 1
  exact Nat.choose_symm_of_eq_add (by omega)

/-- `C(n,i) C(n+j,j) = T n (i+j) i`. -/
private theorem T_eq {n i j : ℕ} (hi : i ≤ n) :
    n.choose i * (n + j).choose j = T n (i + j) i := by
  unfold T
  have h1 : n + (i + j) - i = n + j := by omega
  have h2 : n + (i + j) - 2 * i = n + j - i := by omega
  rw [h1, h2, ← Nat.choose_mul (n := n + j) hi, ← Nat.choose_symm_add, Nat.mul_comm]

/-- The exponent identity `((2n-1) i + n) + (2n+1) j + 2i = n + m + 2nm` with `m = i + j`. -/
private theorem key_arith {n i j : ℕ} (hi : i ≤ n) :
    (2 * n - 1) * i + n + (2 * n + 1) * j + 2 * i = n + (i + j) + 2 * (n * (i + j)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : i = 0 := by omega
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
    ring

/-- `m ↦ n + m + 2nm` is injective. -/
private theorem inj_aux {n m m' : ℕ} (h : n + m + 2 * (n * m) = n + m' + 2 * (n * m')) :
    m = m' := by
  have e1 : (2 * n + 1) * m = m + 2 * (n * m) := by ring
  have e2 : (2 * n + 1) * m' = m' + 2 * (n * m') := by ring
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * n + 1) (by omega)

/-- `-1 = 1` in `ZMod 2`. -/
private theorem neg_one_zmod2 : (-1 : ZMod 2) = 1 := by decide

/-- Mod 2, `term N n i` (for `i ≤ n`) is the sum of `T n m i` over the (at most one) `m` with
`i ≤ m` and `n + m + 2nm = N + 2i`. -/
private theorem term_cast {N n i : ℕ} (hi : i ≤ n) :
    ((term N n i : ℤ) : ZMod 2) = ∑ m ∈ Finset.range (N + 1),
      if i ≤ m ∧ n + m + 2 * (n * m) = N + 2 * i then (T n m i : ZMod 2) else 0 := by
  unfold term
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have hNq : N = (2 * n - 1) * i + n +
        (2 * n + 1) * ((N - ((2 * n - 1) * i + n)) / (2 * n + 1)) := by
      have := Nat.div_add_mod (N - ((2 * n - 1) * i + n)) (2 * n + 1)
      rw [h2] at this
      omega
    generalize (N - ((2 * n - 1) * i + n)) / (2 * n + 1) = q at hNq ⊢
    have hk := key_arith (j := q) hi
    have hq' : q ≤ (2 * n + 1) * q := Nat.le_mul_of_pos_left q (by omega)
    rw [Finset.sum_eq_single (i + q)]
    · rw [if_pos ⟨by omega, by omega⟩]
      push_cast
      rw [neg_one_zmod2, one_pow, one_mul, binom_eq_choose, binom_eq_choose, ← Nat.cast_mul,
        T_eq hi]
    · intro m _ hne
      rw [if_neg]
      rintro ⟨_, heq⟩
      exact hne (inj_aux (n := n) (by omega)).symm
    · intro hmem
      exfalso
      apply hmem
      rw [Finset.mem_range]
      omega
  · symm
    apply Finset.sum_eq_zero
    intro m _
    rw [if_neg]
    rintro ⟨him, heq⟩
    apply h
    obtain ⟨j, rfl⟩ : ∃ j, m = i + j := ⟨m - i, by omega⟩
    have := key_arith (j := j) hi
    refine ⟨by omega, ?_⟩
    have : N - ((2 * n - 1) * i + n) = (2 * n + 1) * j := by omega
    rw [this, Nat.mul_mod_right]

/-- The finite set of triples `(n, i, m)` with `i ≤ n`, `i ≤ m` and `n + m + 2nm = N + 2i`
(all coordinates are automatically `≤ N`). -/
private def S (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
    fun x => x.2.1 ≤ x.1 ∧ x.2.1 ≤ x.2.2 ∧ x.1 + x.2.2 + 2 * (x.1 * x.2.2) = N + 2 * x.2.1

/-- The contribution of the `n`-th summand, mod 2. -/
private theorem summand_cast {N n : ℕ} (hn : n ≤ N) :
    ∑ i ∈ Finset.range (n + 1), ((term N n i : ℤ) : ZMod 2) =
      ∑ i ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
        if i ≤ n ∧ i ≤ m ∧ n + m + 2 * (n * m) = N + 2 * i then (T n m i : ZMod 2) else 0 := by
  rw [← Finset.sum_subset (s₁ := Finset.range (n + 1)) (s₂ := Finset.range (N + 1))
    (Finset.range_subset_range.2 (by omega))]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := by rw [Finset.mem_range] at hi; omega
    rw [term_cast hi']
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hi', true_and]
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro m _
    rw [if_neg]
    rintro ⟨h, -⟩
    rw [Finset.mem_range] at hi
    omega

/-- `coeffA N` mod 2 is the sum of `T` over `S N`. -/
private theorem coeffA_cast (N : ℕ) :
    ((coeffA N : ℤ) : ZMod 2) = ∑ x ∈ S N, (T x.1 x.2.2 x.2.1 : ZMod 2) := by
  rw [coeffA_eq, Int.cast_sum, S, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Int.cast_sum, Finset.sum_product, summand_cast (by rw [Finset.mem_range] at hn; omega)]

/-- The off-diagonal triples cancel mod 2 (involution `n ↔ m`). -/
private theorem sum_S_eq_diag (N : ℕ) :
    ∑ x ∈ S N, (T x.1 x.2.2 x.2.1 : ZMod 2) =
      ∑ x ∈ (S N).filter (fun x => x.1 = x.2.2), (T x.1 x.2.2 x.2.1 : ZMod 2) := by
  rw [← Finset.sum_filter_add_sum_filter_not (S N) (fun x => x.1 = x.2.2), add_eq_left]
  refine Finset.sum_involution (fun x _ => (x.2.2, x.2.1, x.1)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    rw [T_symm hx.1.2.1 hx.1.2.2.1, CharTwo.add_self_eq_zero]
  · rintro ⟨n, i, m⟩ hx _ h
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    apply hx.2
    simp only [Prod.mk.injEq] at h
    omega
  · rintro ⟨n, i, m⟩ hx
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx ⊢
    obtain ⟨⟨⟨h1, h2, h3⟩, h4, h5, h6⟩, h7⟩ := hx
    refine ⟨⟨⟨h3, h2, h1⟩, h5, h4, ?_⟩, fun h => h7 h.symm⟩
    have := Nat.mul_comm m n
    omega
  · intro x _
    rfl

/-- On the diagonal, `T n n i` is even unless `i = n`. -/
private theorem T_diag_even {n i : ℕ} (h : i < n) : ((T n n i : ℕ) : ZMod 2) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  unfold T
  apply Dvd.dvd.mul_left
  have : n + n - 2 * i = 2 * (n - i) := by omega
  rw [this, ← Nat.centralBinom_eq_two_mul_choose]
  exact Nat.two_dvd_centralBinom_of_one_le (by omega)

/-- On a diagonal triple `(n, i, n)` of `S N`, `T n n i` is `0` mod 2 unless `i = n`, in which case
`N = 2 n²`. -/
private theorem diag_cases {N n i : ℕ} (h6 : n + n + 2 * (n * n) = N + 2 * i) (h4 : i ≤ n) :
    ((T n n i : ℕ) : ZMod 2) = 0 ∨ (i = n ∧ N = 2 * (n * n)) := by
  rcases Nat.lt_or_ge i n with h | h
  · exact Or.inl (T_diag_even h)
  · exact Or.inr ⟨by omega, by omega⟩

/-- `a K` mod 2 is `1` if `K` is a square and `0` otherwise. -/
private theorem a_cast (K : ℕ) : ((a K : ℤ) : ZMod 2) = if IsSquare K then 1 else 0 := by
  rw [a, coeffA_cast, sum_S_eq_diag]
  split_ifs with hK
  · obtain ⟨k, rfl⟩ := hK
    rw [Finset.sum_eq_single (k, k, k)]
    · simp [T]
    · rintro ⟨n, i, m⟩ hx hne
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
      obtain ⟨⟨⟨-, -, -⟩, h4, -, h6⟩, hnm⟩ := hx
      dsimp only
      rw [← hnm] at h6 ⊢
      rcases diag_cases h6 h4 with h | ⟨hin, hN⟩
      · exact h
      · exfalso
        apply hne
        have hsq : n * n = k * k := by omega
        have hnk : n = k := Nat.mul_self_inj.1 hsq
        rw [← hnm, hin, hnk]
    · intro hmem
      exfalso
      apply hmem
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      have : k ≤ k * k := Nat.le_mul_self k
      refine ⟨⟨⟨by omega, by omega, by omega⟩, le_rfl, le_rfl, by omega⟩, trivial⟩
  · apply Finset.sum_eq_zero
    rintro ⟨n, i, m⟩ hx
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    obtain ⟨⟨⟨-, -, -⟩, h4, -, h6⟩, hnm⟩ := hx
    dsimp only
    rw [← hnm] at h6 ⊢
    rcases diag_cases h6 h4 with h | ⟨-, hN⟩
    · exact h
    · exact absurd ⟨n, by omega⟩ hK

/-- Hanna's conjecture A326602: `a n` is odd iff `n` is a square. -/
theorem result : statement := by
  intro n
  rw [← ZMod.intCast_eq_one_iff_odd, a_cast]
  split_ifs with h
  · simp [h]
  · simp [h]

end Math0.Frontier.A326602

#math0_settles Math0.Frontier.A326602.result Math0.Statements.A326602.statement
