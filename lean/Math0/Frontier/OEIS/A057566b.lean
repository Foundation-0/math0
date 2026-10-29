/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A057566b
import Math0.Audit

/-!
# The corrected floor formula for collinear triples in a `3 × n` grid

We prove the corrected conjecture (Layman, corrected by Ferudun, Oct 2026) for every `n ≥ 0`:
`a(n) = 5*floor((2n^3 - 3n^2 - 2n + 3)/24) + floor((2(n-1)^3 - 3(n-1)^2 - 2(n-1) + 3)/24) + n`,
where `a(n)` is the number of 3-element collinear subsets of the grid `{0, 1, 2} × {0, …, n - 1}`.

**Counting.** A collinear 3-subset either lies in one row (`3 * C(n, 3)` of them), or has one
point in each row, in columns `x, y, z` with `x + z = 2y` (two points in one row and the third
in another row are never collinear). The transversal triples are parametrized by `(k, l)` with
`(x, z) = (2k, 2l)` or `(2k + 1, 2l + 1)`, giving `⌈n/2⌉^2 + ⌊n/2⌋^2` of them. Formally,
`a n = 3 * C(n, 3) + ⌈n/2⌉^2 + ⌊n/2⌋^2` is proved by an explicit bijection `g` from a disjoint
sum `dom n` onto the set of collinear triples (`Finset.card_nbij`).

**Floor identity.** With `N(m) = 2m^3 - 3m^2 - 2m + 3` one has the polynomial identity
`5 N(n) + N(n - 1) = 12n^3 - 24n^2 + 15`, while `24 a(n) = 12n^3 - 24n^2 + 24n + 12 (n mod 2)`.
So the formula is equivalent to `5 (N(n) mod 24) + (N(n - 1) mod 24) = 15 - 12 (n mod 2)`,
which depends only on `n mod 24` and is checked for the 24 residues.
-/

namespace Math0.Frontier.A057566b
open Math0.Statements.A057566b

/-- The embedding of the column index `j` into row `i` of the grid. -/
private def rowEmb (i : ℕ) : ℕ ↪ ℕ × ℕ :=
  ⟨fun j => (i, j), fun a b h => by simpa using h⟩

/-- `rowEmb i j = (i, j)`. -/
private theorem rowEmb_apply (i j : ℕ) : rowEmb i j = (i, j) := rfl

/-- The parameter set: a row `i < 3` with a 3-subset of the columns, or a pair `(k, l)` of
half-columns for an even transversal triple, or a pair `(k, l)` for an odd one. -/
private def dom (n : ℕ) : Finset ((ℕ × Finset ℕ) ⊕ ((ℕ × ℕ) ⊕ (ℕ × ℕ))) :=
  (Finset.range 3 ×ˢ (Finset.range n).powersetCard 3).disjSum
    ((Finset.range ((n + 1) / 2) ×ˢ Finset.range ((n + 1) / 2)).disjSum
      (Finset.range (n / 2) ×ˢ Finset.range (n / 2)))

/-- The parametrization of the collinear triples: a 3-subset of one row, or the transversal
triple in columns `(2k, k + l, 2l)`, or in columns `(2k + 1, k + l + 1, 2l + 1)`. -/
private def g : (ℕ × Finset ℕ) ⊕ ((ℕ × ℕ) ⊕ (ℕ × ℕ)) → Finset (ℕ × ℕ)
  | Sum.inl (i, t) => t.map (rowEmb i)
  | Sum.inr (Sum.inl (x, z)) => {(0, 2 * x), (1, x + z), (2, 2 * z)}
  | Sum.inr (Sum.inr (x, z)) => {(0, 2 * x + 1), (1, x + z + 1), (2, 2 * z + 1)}

/-- The size of the parameter set. -/
private theorem card_dom (n : ℕ) :
    (dom n).card = 3 * n.choose 3 + (n + 1) / 2 * ((n + 1) / 2) + n / 2 * (n / 2) := by
  simp [dom, Finset.card_disjSum, Finset.card_product, Finset.card_powersetCard]
  ring

/-- Every 3-subset of a single row is in the image of `g`. -/
private theorem surj_row (n i : ℕ) (hi : i < 3) (x y z : ℕ) (hx : x < n) (hy : y < n)
    (hz : z < n) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ a ∈ dom n, g a = {(i, x), (i, y), (i, z)} := by
  refine ⟨Sum.inl (i, {x, y, z}), ?_, ?_⟩
  · simp only [dom, Finset.inl_mem_disjSum, Finset.mem_product, Finset.mem_range,
      Finset.mem_powersetCard]
    refine ⟨hi, ?_, ?_⟩
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_range]
      omega
    · rw [Finset.card_eq_three]
      exact ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  · simp [g, rowEmb_apply]

/-- Every transversal triple `{(0, x), (1, y), (2, z)}` with `x + z = 2y` is in the image of
`g`. -/
private theorem surj_trans (n x y z : ℕ) (hx : x < n) (hz : z < n) (h : x + z = 2 * y)
    (s : Finset (ℕ × ℕ)) (hs : s = {(0, x), (1, y), (2, z)}) :
    ∃ a ∈ dom n, g a = s := by
  subst hs
  rcases Nat.even_or_odd' x with ⟨k, rfl | rfl⟩
  · obtain ⟨l, rfl⟩ : ∃ l, z = 2 * l := ⟨z / 2, by omega⟩
    obtain rfl : y = k + l := by omega
    refine ⟨Sum.inr (Sum.inl (k, l)), ?_, rfl⟩
    simp only [dom, Finset.inr_mem_disjSum, Finset.inl_mem_disjSum, Finset.mem_product,
      Finset.mem_range]
    omega
  · obtain ⟨l, rfl⟩ : ∃ l, z = 2 * l + 1 := ⟨z / 2, by omega⟩
    obtain rfl : y = k + l + 1 := by omega
    refine ⟨Sum.inr (Sum.inr (k, l)), ?_, rfl⟩
    simp only [dom, Finset.inr_mem_disjSum, Finset.mem_product, Finset.mem_range]
    omega

/-- The closed form `a n = 3 * C(n, 3) + ⌈n/2⌉^2 + ⌊n/2⌋^2`, via the bijection `g`. -/
private theorem a_eq (n : ℕ) :
    a n = 3 * n.choose 3 + (n + 1) / 2 * ((n + 1) / 2) + n / 2 * (n / 2) := by
  rw [← card_dom, a]
  symm
  apply Finset.card_nbij g
  · rintro (⟨i, t⟩ | ⟨x, z⟩ | ⟨x, z⟩) hx
    · simp only [Finset.mem_coe, dom, Finset.inl_mem_disjSum, Finset.mem_product,
        Finset.mem_range, Finset.mem_powersetCard] at hx
      obtain ⟨hi, ht, htc⟩ := hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro w hw
        simp only [g, Finset.mem_map, rowEmb_apply] at hw
        obtain ⟨j, hj, rfl⟩ := hw
        have := ht hj
        simp only [Finset.mem_range] at this
        simp [grid, hi, this]
      · simp [g, htc]
      · intro p hp q hq r hr
        simp only [g, Finset.mem_map, rowEmb_apply] at hp hq hr
        obtain ⟨_, _, rfl⟩ := hp
        obtain ⟨_, _, rfl⟩ := hq
        obtain ⟨_, _, rfl⟩ := hr
        simp [cross]
    · simp only [Finset.mem_coe, dom, Finset.inr_mem_disjSum, Finset.inl_mem_disjSum,
        Finset.mem_product, Finset.mem_range] at hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard, g]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> simp [grid] <;> omega
      · rw [Finset.card_eq_three]
        exact ⟨_, _, _, by simp, by simp, by simp, rfl⟩
      · rw [isCollinear_triple]
        simp only [cross]
        push_cast
        ring
    · simp only [Finset.mem_coe, dom, Finset.inr_mem_disjSum,
        Finset.mem_product, Finset.mem_range] at hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard, g]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> simp [grid] <;> omega
      · rw [Finset.card_eq_three]
        exact ⟨_, _, _, by simp, by simp, by simp, rfl⟩
      · rw [isCollinear_triple]
        simp only [cross]
        push_cast
        ring
  · rintro (⟨i, t⟩ | ⟨x, z⟩ | ⟨x, z⟩) hx (⟨i', t'⟩ | ⟨x', z'⟩ | ⟨x', z'⟩) hx' h
    · simp only [Finset.mem_coe, dom, Finset.inl_mem_disjSum, Finset.mem_product,
        Finset.mem_range, Finset.mem_powersetCard] at hx hx'
      simp only [g] at h
      obtain ⟨j, hj⟩ : t.Nonempty := Finset.card_pos.1 (by omega)
      have hm : (i, j) ∈ t'.map (rowEmb i') := by rw [← h]; exact Finset.mem_map_of_mem _ hj
      simp only [Finset.mem_map, rowEmb_apply, Prod.mk.injEq] at hm
      obtain ⟨_, _, rfl, rfl⟩ := hm
      rw [Finset.map_inj] at h
      rw [h]
    · have h0 : (0, 2 * x') ∈ g (Sum.inl (i, t)) := by rw [h]; simp [g]
      have h1 : (1, x' + z') ∈ g (Sum.inl (i, t)) := by rw [h]; simp [g]
      simp only [g, Finset.mem_map, rowEmb_apply, Prod.mk.injEq] at h0 h1
      omega
    · have h0 : (0, 2 * x' + 1) ∈ g (Sum.inl (i, t)) := by rw [h]; simp [g]
      have h1 : (1, x' + z' + 1) ∈ g (Sum.inl (i, t)) := by rw [h]; simp [g]
      simp only [g, Finset.mem_map, rowEmb_apply, Prod.mk.injEq] at h0 h1
      omega
    · have h0 : (0, 2 * x) ∈ g (Sum.inl (i', t')) := by rw [← h]; simp [g]
      have h1 : (1, x + z) ∈ g (Sum.inl (i', t')) := by rw [← h]; simp [g]
      simp only [g, Finset.mem_map, rowEmb_apply, Prod.mk.injEq] at h0 h1
      omega
    · have h0 : (0, 2 * x) ∈ g (Sum.inr (Sum.inl (x', z'))) := by rw [← h]; simp [g]
      have h2 : (2, 2 * z) ∈ g (Sum.inr (Sum.inl (x', z'))) := by rw [← h]; simp [g]
      simp [g] at h0 h2
      simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq]
      omega
    · have h0 : (0, 2 * x) ∈ g (Sum.inr (Sum.inr (x', z'))) := by rw [← h]; simp [g]
      simp [g] at h0
      omega
    · have h0 : (0, 2 * x + 1) ∈ g (Sum.inl (i', t')) := by rw [← h]; simp [g]
      have h1 : (1, x + z + 1) ∈ g (Sum.inl (i', t')) := by rw [← h]; simp [g]
      simp only [g, Finset.mem_map, rowEmb_apply, Prod.mk.injEq] at h0 h1
      omega
    · have h0 : (0, 2 * x + 1) ∈ g (Sum.inr (Sum.inl (x', z'))) := by rw [← h]; simp [g]
      simp [g] at h0
      omega
    · have h0 : (0, 2 * x + 1) ∈ g (Sum.inr (Sum.inr (x', z'))) := by rw [← h]; simp [g]
      have h2 : (2, 2 * z + 1) ∈ g (Sum.inr (Sum.inr (x', z'))) := by rw [← h]; simp [g]
      simp [g] at h0 h2
      simp only [Sum.inr.injEq, Prod.mk.injEq]
      omega
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hs
    obtain ⟨⟨hsub, hcard⟩, hcol⟩ := hs
    obtain ⟨⟨p1, p2⟩, ⟨q1, q2⟩, ⟨r1, r2⟩, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.1 hcard
    rw [isCollinear_triple] at hcol
    have hp := hsub (by simp : (p1, p2) ∈ ({(p1, p2), (q1, q2), (r1, r2)} : Finset (ℕ × ℕ)))
    have hq := hsub (by simp : (q1, q2) ∈ ({(p1, p2), (q1, q2), (r1, r2)} : Finset (ℕ × ℕ)))
    have hr := hsub (by simp : (r1, r2) ∈ ({(p1, p2), (q1, q2), (r1, r2)} : Finset (ℕ × ℕ)))
    simp only [grid, Finset.mem_product, Finset.mem_range] at hp hq hr
    simp only [ne_eq, Prod.mk.injEq] at hpq hpr hqr
    simp only [cross] at hcol
    rw [Set.mem_image]
    simp only [Finset.mem_coe]
    by_cases hrow : p1 = q1 ∧ q1 = r1
    · obtain ⟨rfl, rfl⟩ := hrow
      exact surj_row n p1 hp.1 p2 q2 r2 hp.2 hq.2 hr.2 (by omega) (by omega) (by omega)
    · rcases (show p1 = 0 ∨ p1 = 1 ∨ p1 = 2 by omega) with rfl | rfl | rfl <;>
      rcases (show q1 = 0 ∨ q1 = 1 ∨ q1 = 2 by omega) with rfl | rfl | rfl <;>
      rcases (show r1 = 0 ∨ r1 = 1 ∨ r1 = 2 by omega) with rfl | rfl | rfl <;>
      push_cast at hcol <;> (try ring_nf at hcol) <;>
      first
        | omega
        | (refine surj_trans n p2 q2 r2 ?_ ?_ ?_ _ ?_ <;>
            first
              | omega
              | rfl
              | (ext ⟨u, v⟩; simp only [Finset.mem_insert, Finset.mem_singleton,
                  Prod.mk.injEq]; omega))
        | (refine surj_trans n p2 r2 q2 ?_ ?_ ?_ _ ?_ <;>
            first
              | omega
              | rfl
              | (ext ⟨u, v⟩; simp only [Finset.mem_insert, Finset.mem_singleton,
                  Prod.mk.injEq]; omega))
        | (refine surj_trans n q2 p2 r2 ?_ ?_ ?_ _ ?_ <;>
            first
              | omega
              | rfl
              | (ext ⟨u, v⟩; simp only [Finset.mem_insert, Finset.mem_singleton,
                  Prod.mk.injEq]; omega))
        | (refine surj_trans n q2 r2 p2 ?_ ?_ ?_ _ ?_ <;>
            first
              | omega
              | rfl
              | (ext ⟨u, v⟩; simp only [Finset.mem_insert, Finset.mem_singleton,
                  Prod.mk.injEq]; omega))
        | (refine surj_trans n r2 p2 q2 ?_ ?_ ?_ _ ?_ <;>
            first
              | omega
              | rfl
              | (ext ⟨u, v⟩; simp only [Finset.mem_insert, Finset.mem_singleton,
                  Prod.mk.injEq]; omega))
        | (refine surj_trans n r2 q2 p2 ?_ ?_ ?_ _ ?_ <;>
            first
              | omega
              | rfl
              | (ext ⟨u, v⟩; simp only [Finset.mem_insert, Finset.mem_singleton,
                  Prod.mk.injEq]; omega))

/-- `6 * C(n, 3) = n (n - 1) (n - 2)` and `2 * C(n, 2) = n (n - 1)` over `ℤ`. -/
private theorem choose_three (n : ℕ) :
    (6 * n.choose 3 : ℤ) = n * (n - 1) * (n - 2) ∧ (2 * n.choose 2 : ℤ) = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    constructor
    · linear_combination 3 * ih.2 + ih.1
    · linear_combination ih.2

/-- The residues of the two numerators modulo `24`, for a residue `r` of `n` modulo `24`:
`5 * (N(r) mod 24) + (N(r - 1) mod 24) = 15 - 12 * (r mod 2)`, where
`N(m) = 2m^3 - 3m^2 - 2m + 3` (a finite check). -/
private theorem resid (r : ℤ) (h0 : 0 ≤ r) (h1 : r < 24) :
    5 * ((2 * r ^ 3 - 3 * r ^ 2 - 2 * r + 3) % 24)
      + (2 * (r - 1) ^ 3 - 3 * (r - 1) ^ 2 - 2 * (r - 1) + 3) % 24 = 15 - 12 * (r % 2) := by
  interval_cases r <;> norm_num

/-- `2 * (⌈n/2⌉^2 + ⌊n/2⌋^2) = n^2 + (n mod 2)`. -/
private theorem sq_half (n : ℕ) :
    (((n + 1) / 2 * ((n + 1) / 2) + n / 2 * (n / 2) : ℕ) : ℤ) * 2 =
      (n : ℤ) ^ 2 + (n : ℤ) % 2 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show (2 * k + 1) / 2 = k by omega, show 2 * k / 2 = k by omega]
    push_cast
    rw [show (2 * (k : ℤ)) % 2 = 0 by omega]
    ring
  · rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega]
    push_cast
    rw [show (2 * (k : ℤ) + 1) % 2 = 1 by omega]
    ring

/-- The corrected floor formula holds for every `n ≥ 0`. -/
theorem result : statement := by
  rw [statement_iff_ediv]
  intro n
  have h3 := (choose_three n).1
  have hS := sq_half n
  rw [a_eq]
  rw [show ((3 * n.choose 3 + (n + 1) / 2 * ((n + 1) / 2) + n / 2 * (n / 2) : ℕ) : ℤ) =
      3 * (n.choose 3 : ℤ) + (((n + 1) / 2 * ((n + 1) / 2) + n / 2 * (n / 2) : ℕ) : ℤ) by
    push_cast; ring]
  generalize (((n + 1) / 2 * ((n + 1) / 2) + n / 2 * (n / 2) : ℕ) : ℤ) = S at hS ⊢
  generalize (n.choose 3 : ℤ) = C at h3 ⊢
  generalize (n : ℤ) = m at h3 hS ⊢
  have hN1 : (2 * m ^ 3 - 3 * m ^ 2 - 2 * m + 3) % 24
      = (2 * (m % 24) ^ 3 - 3 * (m % 24) ^ 2 - 2 * (m % 24) + 3) % 24 := by
    have hmr : m ≡ m % 24 [ZMOD 24] := (Int.mod_modEq m 24).symm
    have : 2 * m ^ 3 - 3 * m ^ 2 - 2 * m + 3 ≡
        2 * (m % 24) ^ 3 - 3 * (m % 24) ^ 2 - 2 * (m % 24) + 3 [ZMOD 24] := by gcongr
    exact this
  have hN2 : (2 * (m - 1) ^ 3 - 3 * (m - 1) ^ 2 - 2 * (m - 1) + 3) % 24
      = (2 * (m % 24 - 1) ^ 3 - 3 * (m % 24 - 1) ^ 2 - 2 * (m % 24 - 1) + 3) % 24 := by
    have hmr : m ≡ m % 24 [ZMOD 24] := (Int.mod_modEq m 24).symm
    have : 2 * (m - 1) ^ 3 - 3 * (m - 1) ^ 2 - 2 * (m - 1) + 3 ≡
        2 * (m % 24 - 1) ^ 3 - 3 * (m % 24 - 1) ^ 2 - 2 * (m % 24 - 1) + 3 [ZMOD 24] := by
      gcongr
    exact this
  have hpar : m % 24 % 2 = m % 2 := Int.emod_emod_of_dvd m (by norm_num)
  have hρ := resid (m % 24) (Int.emod_nonneg m (by norm_num)) (Int.emod_lt_of_pos m (by norm_num))
  have hu := Int.mul_ediv_add_emod (2 * m ^ 3 - 3 * m ^ 2 - 2 * m + 3) 24
  have hw := Int.mul_ediv_add_emod (2 * (m - 1) ^ 3 - 3 * (m - 1) ^ 2 - 2 * (m - 1) + 3) 24
  rw [hN1] at hu
  rw [hN2] at hw
  rw [hpar] at hρ
  have key : 24 * (3 * C + S - (5 * ((2 * m ^ 3 - 3 * m ^ 2 - 2 * m + 3) / 24)
      + ((2 * (m - 1) ^ 3 - 3 * (m - 1) ^ 2 - 2 * (m - 1) + 3) / 24) + m)) = 0 := by
    linear_combination 12 * h3 + 12 * hS - 5 * hu - hw + hρ
  omega

end Math0.Frontier.A057566b

#math0_settles Math0.Frontier.A057566b.result Math0.Statements.A057566b.statement
