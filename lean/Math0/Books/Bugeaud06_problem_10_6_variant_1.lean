/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_6
import Math0.Audit

/-!
# A sequence with ratio floor `1 + c / log n`, dense mod one for all irrationals (Bugeaud 10.6)

Bugeaud (*Distribution modulo one and Diophantine approximation*, Problem 10.6) asks for a
"very rapidly increasing" sequence `(m_n)` of positive integers such that `({ξ m_n})` is dense
modulo one for every irrational `ξ`. We prove exactly the formal statement
`Bugeaud06.problem_10_6_variant_1`, which reads "very rapidly increasing" as: `m` is strictly
increasing and `m (n+1) / m n ≥ 1 + c / log n` eventually, for some `c > 0`.
The witness enumerates the set of all powers of two together with blocks
`B_k = {A + r W + (D + r) j : r, j < K}` with `K = 2^k`, `D = 2^(2^(4^k))`, `W = 2 D K`,
`A = K W` (a power of two). Inside `[A, 2A)` all gaps are `≥ D = A / (2 K^2)`, and because the
powers of two are in the set, an element `≥ A` has index `≥ log₂ A ≥ 2^(4^k)`, so
`D / (2A) = 1 / (4 · 4^k)` beats `(1/8) / log n`. Density: by Dirichlet and a stepping
argument we pick `r < K` with `ξ (D + r) ≡ s (mod 1)`, `s ∈ [η/2, η]`; then the `K` points
`ξ (A + r W) + j s` walk around the circle with steps `s ≤ η` and hit any interval of length `η`.
-/

namespace Math0.Bugeaud06

open Filter

/-- The exponent `M k = 2 ^ (4 ^ k)` fixing the scale of block `k`. -/
def bM (k : ℕ) : ℕ := 2 ^ (4 ^ k)

/-- The side length `K k = 2 ^ k` of block `k`. -/
def bK (k : ℕ) : ℕ := 2 ^ k

/-- The base difference `D k = 2 ^ M k` of block `k`. -/
def bD (k : ℕ) : ℕ := 2 ^ bM k

/-- The spacing `W k = 2 D K` between the sub-progressions of block `k`. -/
def bW (k : ℕ) : ℕ := 2 * bD k * bK k

/-- The starting point `A k = K W` of block `k`. -/
def bA (k : ℕ) : ℕ := bK k * bW k

/-- The dyadic level of block `k`: `A k = 2 ^ L k`. -/
def bL (k : ℕ) : ℕ := bM k + 2 * k + 1

/-- The element of block `k` with parameters `r, j`. -/
def elt (k r j : ℕ) : ℕ := bA k + r * bW k + (bD k + r) * j

/-- The set: all powers of two, together with all block elements. -/
def S : Set ℕ :=
  {x | (∃ i, x = 2 ^ i) ∨ ∃ k r j, r < bK k ∧ j < bK k ∧ x = elt k r j}

/-- The sequence enumerating `S` increasingly. -/
noncomputable def seq : ℕ → ℕ := Nat.nth (· ∈ S)

/-- The side length is at most the base difference: `K k ≤ D k`. -/
lemma bK_le_bD (k : ℕ) : bK k ≤ bD k := by
  unfold bK bD bM
  refine Nat.pow_le_pow_right (by norm_num) ?_
  calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
    _ ≤ 2 ^ (4 ^ k) := Nat.pow_le_pow_right (by norm_num)
        ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by norm_num : 2 ≤ 4) k))

/-- The base difference is positive. -/
lemma bD_pos (k : ℕ) : 0 < bD k := by unfold bD; positivity

/-- The side length is positive. -/
lemma bK_pos (k : ℕ) : 0 < bK k := by unfold bK; positivity

/-- The starting point of block `k` is the power of two `2 ^ L k`. -/
lemma bA_eq (k : ℕ) : bA k = 2 ^ bL k := by
  unfold bA bW bD bK bL; ring

/-- `2 A = 4 D · 4^k`, i.e. `D / (2 A) = 1 / (4 · 4^k)`. -/
lemma bA_eq' (k : ℕ) : 2 * bA k = 4 * bD k * 4 ^ k := by
  unfold bA bW bK
  have : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
  rw [this]; ring

/-- The key inequality `(D + r) j + D ≤ W` for `r, j < K`: a sub-progression plus one gap
fits below the next sub-progression. -/
lemma key_bound {k r j : ℕ} (hr : r < bK k) (hj : j < bK k) :
    (bD k + r) * j + bD k ≤ bW k := by
  have h1 := bK_le_bD k
  have h2 : (bD k + r) * (j + 1) ≤ (bD k + bK k) * bK k :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : (bD k + bK k) * bK k ≤ 2 * bD k * bK k := by
    nlinarith
  unfold bW
  nlinarith

/-- Every element of block `k` is at least its starting point `A k`. -/
lemma elt_ge {k r j : ℕ} : bA k ≤ elt k r j := by
  unfold elt; omega

/-- Every element of block `k` stays at distance `≥ D` below `2 A`. -/
lemma elt_add_le {k r j : ℕ} (hr : r < bK k) (hj : j < bK k) :
    elt k r j + bD k ≤ 2 * bA k := by
  have h := key_bound hr hj
  have h2 : (r + 1) * bW k ≤ bK k * bW k := Nat.mul_le_mul_right _ hr
  unfold elt bA
  nlinarith

/-- Two elements of the same block differ by at least `D`. -/
lemma within_gap {k r j r' j' : ℕ} (hr : r < bK k) (hj : j < bK k) (hr' : r' < bK k)
    (hj' : j' < bK k) (h : elt k r j < elt k r' j') : elt k r j + bD k ≤ elt k r' j' := by
  have key := key_bound hr hj
  have key' := key_bound hr' hj'
  have hD := bD_pos k
  unfold elt at *
  rcases lt_trichotomy r r' with h1 | rfl | h1
  · have : (r + 1) * bW k ≤ r' * bW k := Nat.mul_le_mul_right _ h1
    nlinarith
  · have h2 : j < j' := by
      by_contra h3
      have : (bD k + r) * j' ≤ (bD k + r) * j := Nat.mul_le_mul_left _ (by omega)
      omega
    have : (bD k + r) * (j + 1) ≤ (bD k + r) * j' := Nat.mul_le_mul_left _ h2
    nlinarith
  · have : (r' + 1) * bW k ≤ r * bW k := Nat.mul_le_mul_right _ h1
    nlinarith

/-- The dyadic levels of distinct blocks are separated: `L k + 1 ≤ L k'` for `k < k'`. -/
lemma bL_lt {k k' : ℕ} (h : k < k') : bL k + 1 ≤ bL k' := by
  have : bM k ≤ bM k' := by
    unfold bM
    exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) h.le)
  unfold bL
  omega

/-- `2 A k = 2 ^ (L k + 1)`. -/
lemma two_mul_bA (k : ℕ) : 2 * bA k = 2 ^ (bL k + 1) := by
  rw [bA_eq, pow_succ]; ring

/-- Gap after a block element. -/
lemma gap_block {k r j y : ℕ} (hr : r < bK k) (hj : j < bK k) (hy : y ∈ S)
    (h : elt k r j < y) : elt k r j + bD k ≤ y := by
  have hge := @elt_ge k r j
  have hle := elt_add_le hr hj
  rcases hy with ⟨i, rfl⟩ | ⟨k', r', j', hr', hj', rfl⟩
  · rcases Nat.lt_or_ge (bL k) i with hi | hi
    · have : 2 ^ (bL k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
      rw [two_mul_bA] at hle
      omega
    · have : 2 ^ i ≤ 2 ^ bL k := Nat.pow_le_pow_right (by norm_num) hi
      rw [bA_eq] at hge
      omega
  · have hge' := @elt_ge k' r' j'
    have hle' := elt_add_le hr' hj'
    rcases lt_trichotomy k k' with hk | rfl | hk
    · have := bL_lt hk
      have : 2 ^ (bL k + 1) ≤ 2 ^ bL k' := Nat.pow_le_pow_right (by norm_num) this
      rw [two_mul_bA] at hle
      rw [bA_eq] at hge'
      omega
    · exact within_gap hr hj hr' hj' h
    · have := bL_lt hk
      have : 2 ^ (bL k' + 1) ≤ 2 ^ bL k := Nat.pow_le_pow_right (by norm_num) this
      rw [two_mul_bA] at hle'
      rw [bA_eq] at hge
      omega

/-- Gap after a power of two that is not the start of a block. -/
lemma gap_filler {i y : ℕ} (hi : ∀ k, i ≠ bL k) (hy : y ∈ S) (h : 2 ^ i < y) :
    2 * 2 ^ i ≤ y := by
  rcases hy with ⟨i', rfl⟩ | ⟨k, r, j, hr, hj, rfl⟩
  · have : i < i' := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h
    have : 2 ^ (i + 1) ≤ 2 ^ i' := Nat.pow_le_pow_right (by norm_num) this
    rw [pow_succ] at this
    omega
  · have hge := @elt_ge k r j
    have hle := elt_add_le hr hj
    rw [two_mul_bA] at hle
    have h1 : 2 ^ i < 2 ^ (bL k + 1) := by omega
    have h2 : i < bL k + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
    have h3 : i + 1 ≤ bL k := by have := hi k; omega
    have : 2 ^ (i + 1) ≤ 2 ^ bL k := Nat.pow_le_pow_right (by norm_num) h3
    rw [pow_succ, ← bA_eq] at this
    omega

/-- Every element of `S` is a block element, or a power of two not at a block level. -/
lemma S_cases {x : ℕ} (hx : x ∈ S) :
    (∃ k r j, r < bK k ∧ j < bK k ∧ x = elt k r j) ∨ (∃ i, x = 2 ^ i ∧ ∀ k, i ≠ bL k) := by
  rcases hx with ⟨i, rfl⟩ | h
  · by_cases hi : ∃ k, i = bL k
    · obtain ⟨k, rfl⟩ := hi
      left
      refine ⟨k, 0, 0, bK_pos k, bK_pos k, ?_⟩
      simp [elt, bA_eq]
    · push Not at hi
      exact Or.inr ⟨i, rfl, hi⟩
  · exact Or.inl h

/-- `S` is infinite, since it contains every power of two. -/
lemma S_infinite : (Set.ofPred (· ∈ S)).Infinite := by
  have : Set.range (fun i : ℕ => 2 ^ i) ⊆ Set.ofPred (· ∈ S) := by
    rintro _ ⟨i, rfl⟩
    exact Or.inl ⟨i, rfl⟩
  exact Set.Infinite.mono this
    (Set.infinite_range_of_injective (Nat.pow_right_injective le_rfl))

/-- The enumeration of `S` is strictly increasing. -/
lemma seq_strictMono : StrictMono seq := Nat.nth_strictMono S_infinite

/-- Every term of the enumeration lies in `S`. -/
lemma seq_mem (n : ℕ) : seq n ∈ S := Nat.nth_mem_of_infinite S_infinite n

/-- The range of the enumeration is exactly `S`. -/
lemma range_seq : Set.range seq = S := Nat.range_nth_of_infinite S_infinite

/-- Index bound: `seq n ≤ 2 ^ n`, because `1, 2, ..., 2 ^ n` are `n + 1` elements of `S`. -/
lemma seq_le_pow (n : ℕ) : seq n ≤ 2 ^ n := by
  have hmem : ∀ i, 2 ^ i ∈ Set.range seq := fun i => by
    rw [range_seq]; exact Or.inl ⟨i, rfl⟩
  choose f hf using hmem
  have hfm : StrictMono f := fun i i' h => by
    rw [← seq_strictMono.lt_iff_lt, hf, hf]
    exact Nat.pow_lt_pow_right (by norm_num) h
  calc seq n ≤ seq (f n) := seq_strictMono.monotone (hfm.id_le n)
    _ = 2 ^ n := hf n

/-- All terms are positive. -/
lemma seq_pos (n : ℕ) : 0 < seq n := by
  rcases seq_mem n with ⟨i, h⟩ | ⟨k, r, j, -, -, h⟩
  · rw [h]; positivity
  · rw [h]; have := @elt_ge k r j; rw [bA_eq] at this
    have : 0 < 2 ^ bL k := by positivity
    omega

/-- The ratio floor: `seq (n+1) / seq n ≥ 1 + (1/8) / log n` for all `n ≥ 2`. -/
lemma sublacunary : _root_.Bugeaud06.IsGenuinelySublacunary seq := by
  refine ⟨1 / 8, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hxy : seq n < seq (n + 1) := seq_strictMono (Nat.lt_succ_self n)
  have hy := seq_mem (n + 1)
  have hxpos : (0 : ℝ) < seq n := by exact_mod_cast seq_pos n
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 := Real.log_two_gt_d9
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  have hlpos : 0 < Real.log n := by linarith
  rw [le_div_iff₀ hxpos]
  rcases S_cases (seq_mem n) with ⟨k, r, j, hr, hj, hx⟩ | ⟨i, hx, hi⟩
  · have hgap := gap_block hr hj hy (hx ▸ hxy)
    rw [← hx] at hgap
    have hle := elt_add_le hr hj
    rw [← hx, bA_eq'] at hle
    have hge := @elt_ge k r j
    rw [← hx, bA_eq] at hge
    -- index bound
    have hL : bL k ≤ n := by
      have := hge.trans (seq_le_pow n)
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    have hM : 2 ^ (4 ^ k) ≤ n := by
      have : bM k ≤ bL k := by unfold bL; omega
      unfold bM at this
      omega
    have hMR : (2 : ℝ) ^ (4 ^ k) ≤ n := by exact_mod_cast hM
    have hlog : (4 : ℝ) ^ k * Real.log 2 ≤ Real.log n := by
      have := Real.log_le_log (by positivity) hMR
      rw [Real.log_pow] at this
      push_cast at this
      exact this
    have hgapR : (seq n : ℝ) + bD k ≤ seq (n + 1) := by exact_mod_cast hgap
    have hleR : (seq n : ℝ) + bD k ≤ 4 * bD k * 4 ^ k := by exact_mod_cast hle
    have hDpos : (0 : ℝ) < bD k := by exact_mod_cast bD_pos k
    have h4 : (0 : ℝ) < 4 ^ k := by positivity
    have hlog' : (4 : ℝ) ^ k / 2 ≤ Real.log n := by nlinarith
    have hkey : 1 / 8 / Real.log n * seq n ≤ bD k := by
      rw [div_div, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hlog' hDpos.le]
    nlinarith
  · have hgap := gap_filler hi hy (hx ▸ hxy)
    rw [← hx] at hgap
    have hgapR : 2 * (seq n : ℝ) ≤ seq (n + 1) := by exact_mod_cast hgap
    have : 1 / 8 / Real.log n ≤ 1 := by
      rw [div_le_one hlpos]; linarith
    nlinarith

/-- Stepping lemma, positive step. -/
lemma step_pos {δ η u a : ℝ} (hδ : 0 < δ) (hδη : δ ≤ η) {N : ℕ} (hN : 1 ≤ N * δ) :
    ∃ j : ℕ, j ≤ N ∧ ∃ z : ℤ, a ≤ u + j * δ + z ∧ u + j * δ + z ≤ a + η := by
  have hw0 : 0 ≤ Int.fract (a - u) := Int.fract_nonneg _
  have hw1 : Int.fract (a - u) < 1 := Int.fract_lt_one _
  have hfl := Int.floor_add_fract (a - u)
  refine ⟨⌈Int.fract (a - u) / δ⌉₊, ?_, ⌊a - u⌋, ?_, ?_⟩
  · apply Nat.ceil_le.2
    rw [div_le_iff₀ hδ]
    linarith
  · have h1 := Nat.le_ceil (Int.fract (a - u) / δ)
    rw [div_le_iff₀ hδ] at h1
    linarith
  · have h2 := Nat.ceil_lt_add_one (div_nonneg hw0 hδ.le)
    have h3 := mul_lt_mul_of_pos_right h2 hδ
    rw [add_mul, div_mul_cancel₀ _ hδ.ne'] at h3
    linarith

/-- Stepping lemma, step of either sign. -/
lemma step_any {δ η u a : ℝ} (hδ : δ ≠ 0) (hδη : |δ| ≤ η) {N : ℕ} (hN : 1 ≤ N * |δ|) :
    ∃ j : ℕ, j ≤ N ∧ ∃ z : ℤ, a ≤ u + j * δ + z ∧ u + j * δ + z ≤ a + η := by
  rcases lt_or_gt_of_ne hδ with h | h
  · rw [abs_of_neg h] at hδη hN
    obtain ⟨j, hj, z, h1, h2⟩ :=
      step_pos (u := -u) (a := -a - η) (neg_pos.2 h) hδη hN
    refine ⟨j, hj, -z, ?_, ?_⟩ <;> push_cast <;> linarith
  · rw [abs_of_pos h] at hδη hN
    exact step_pos h hδη hN

/-- For irrational `ξ`, every open interval `(a, b)` contains some `ξ x + z` with `x ∈ S`, `z ∈ ℤ`. -/
lemma dense_aux (ξ : ℝ) (hξ : Irrational ξ) (a b : ℝ) (hab : a < b) :
    ∃ x ∈ S, ∃ z : ℤ, a < ξ * x + z ∧ ξ * x + z < b := by
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (b - a) / 2 := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; linarith
  -- Dirichlet's theorem gives a small nonzero `δ = q ξ - round (q ξ)`.
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℕ, n0 = ⌈2 / η⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨q, hq0, -, hq⟩ := Real.exists_nat_abs_mul_sub_round_le ξ (n := n0) (by omega)
  obtain ⟨R, hR⟩ : ∃ R : ℤ, R = round ((q : ℝ) * ξ) := ⟨_, rfl⟩
  rw [← hR] at hq
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (q : ℝ) * ξ - R := ⟨_, rfl⟩
  rw [← hδ] at hq
  have hδ0 : δ ≠ 0 := by
    have hirr : Irrational ((q : ℝ) * ξ) := hξ.natCast_mul (by omega)
    have := hirr.ne_int R
    intro h; apply this; rw [hδ] at h; linarith
  have hδη : |δ| ≤ η / 2 := by
    refine hq.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have h1 := Nat.le_ceil (2 / η)
    have h2 : (n0 : ℝ) = ⌈2 / η⌉₊ + 1 := by rw [hn0]; push_cast; ring
    rw [h2]
    have h3 : 2 / η * (η / 2) = 1 := by field_simp
    nlinarith
  have hδpos : 0 < |δ| := abs_pos.2 hδ0
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, N1 = ⌈1 / |δ|⌉₊ := ⟨_, rfl⟩
  have hN1' : 1 ≤ (N1 : ℝ) * |δ| := by
    have := Nat.le_ceil (1 / |δ|)
    rw [div_le_iff₀ hδpos, ← hN1] at this
    exact this
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, N2 = ⌈2 / η⌉₊ := ⟨_, rfl⟩
  -- the block we use
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = N1 * q + N2 := ⟨_, rfl⟩
  have hKk : k < bK k := Nat.lt_two_pow_self
  -- first step: choose `r` with `ξ (D + r)` close to a small positive number mod 1
  obtain ⟨j1, hj1, z1, h1a, h1b⟩ :=
    step_any (u := ξ * (bD k : ℝ)) (a := η / 2) hδ0 hδη hN1'
  have hrK : j1 * q < bK k := by
    have : j1 * q ≤ N1 * q := Nat.mul_le_mul_right _ hj1
    omega
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ξ * (bD k : ℝ) + j1 * δ + z1 := ⟨_, rfl⟩
  rw [← hs] at h1a h1b
  have hspos : 0 < s := by linarith
  have hsη : s ≤ η := by linarith
  have hN2s : 1 ≤ (N2 : ℝ) * s := by
    have h1 := Nat.le_ceil (2 / η)
    rw [← hN2] at h1
    have h2 : 2 / η * (η / 2) = 1 := by field_simp
    nlinarith
  -- second step: walk along the progression with difference `D + r`
  obtain ⟨j2, hj2, z2, h2a, h2b⟩ :=
    step_pos (u := ξ * ((bA k : ℝ) + (j1 * q : ℕ) * bW k)) (a := a + η / 2) hspos hsη hN2s
  have hjK : j2 < bK k := by omega
  have hid : ξ * (elt k (j1 * q) j2 : ℝ) + ((z2 + j2 * (z1 - j1 * R) : ℤ) : ℝ) =
      ξ * ((bA k : ℝ) + (j1 * q : ℕ) * bW k) + j2 * s + z2 := by
    rw [hs, hδ]; simp only [elt]; push_cast; ring
  refine ⟨elt k (j1 * q) j2, Or.inr ⟨k, j1 * q, j2, hrK, hjK, rfl⟩,
    z2 + j2 * (z1 - j1 * R), ?_, ?_⟩
  · rw [hid]; linarith
  · rw [hid]; linarith

/-- For irrational `ξ`, the points `ξ · seq n` are dense in `ℝ / ℤ`. -/
lemma dense_seq (ξ : ℝ) (hξ : Irrational ξ) :
    Dense (Set.range fun n => (↑(ξ * seq n) : AddCircle (1 : ℝ))) := by
  have hT : Dense {t : ℝ | ∃ x ∈ S, ∃ z : ℤ, t = ξ * x + z} := by
    rw [dense_iff_exists_between]
    intro a b hab
    obtain ⟨x, hx, z, h1, h2⟩ := dense_aux ξ hξ a b hab
    exact ⟨_, ⟨x, hx, z, rfl⟩, h1, h2⟩
  have hsurj : Function.Surjective (fun t : ℝ => (t : AddCircle (1 : ℝ))) :=
    QuotientAddGroup.mk_surjective
  have hcont : Continuous (fun t : ℝ => (t : AddCircle (1 : ℝ))) := AddCircle.continuous_mk' 1
  refine (hsurj.denseRange.dense_image hcont hT).mono ?_
  rintro _ ⟨t, ⟨x, hx, z, rfl⟩, rfl⟩
  rw [← range_seq] at hx
  obtain ⟨n, rfl⟩ := hx
  refine ⟨n, ?_⟩
  apply QuotientAddGroup.eq.2
  rw [AddSubgroup.mem_zmultiples_iff]
  exact ⟨z, by simp⟩

/-- There is a strictly increasing sequence with consecutive ratios at least `1 + c / log n`
which is dense modulo one for every irrational dilation. -/
theorem problem_10_6_variant_1 : type_of% @Bugeaud06.problem_10_6_variant_1 :=
  ⟨seq, seq_strictMono, sublacunary, dense_seq⟩

end Math0.Bugeaud06

#math0_proves Math0.Bugeaud06.problem_10_6_variant_1 Bugeaud06.problem_10_6_variant_1
