/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A357583
import Math0.Audit

/-!
# Kurkov's recursion for the row polynomials of convolution triangles holds

We prove both parts of Mikhail Kurkov's conjecture: for every integer sequence `s` and every
`n > 0`, the row polynomial `E(n) = ∑_k T_s(n,k) x^k` of the convolution triangle of `s` equals
`x * R(n,1)`, where `R(1,k) = s(k)` and `R(n,k) = R(n-1,k+1) + x R(n-1,1) R(1,k)`; the Bell case
(A357583) is the instance `s = Bell`, after casting the natural-number triangle to `ℤ`.

**Row-polynomial recursion.** Since `T_s(n,k) = 0` for `k > n` and `T_s(n,0) = [n = 0]`,
the column recursion `T_s(n+1,k+1) = ∑_{j=0}^{n} s(j+1) T_s(n-j,k)` gives
`E(0) = 1` and `E(n+1) = x ∑_{j=0}^{n} s(j+1) E(n-j)` (i.e. `E = 1/(1 - x A(z))`).

**Closed form.** By induction on `m`, `R(m+1,k) = ∑_{j=0}^{m} s(k+j) E(m-j)`: the step splits off
the `j = 0` term `s(k) E(m+1)`, and `E(m+1) = x R(m+1,1)` by the recursion above and the
induction hypothesis at `k = 1`, while the remaining terms are `R(m+1,k+1)`.

**Conclusion.** `x R(m+1,1) = x ∑_{j=0}^{m} s(j+1) E(m-j) = E(m+1)`.
-/

namespace Math0.Frontier.A357583
open Math0.Statements.A357583
open Polynomial

/-- Entries above the diagonal of a convolution triangle vanish. -/
private lemma convT_eq_zero (s : ℕ → ℤ) : ∀ k n : ℕ, n < k → convT s n k = 0
  | 0, n, h => absurd h (Nat.not_lt_zero n)
  | k + 1, n, h => by
    rw [convT]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rcases Nat.eq_zero_or_pos p.1 with h1 | h1
    · simp [pad, h1]
    · rw [convT_eq_zero s k p.2 (by omega), mul_zero]

/-- Extending the range of the row polynomial sum by vanishing terms. -/
private lemma rowPoly_eq_sum (s : ℕ → ℤ) (m : ℕ) : ∀ M : ℕ, m + 1 ≤ M →
    ∑ k ∈ Finset.range M, C (convT s m k) * X ^ k = rowPoly s m
  | 0, h => absurd h (by omega)
  | M + 1, h => by
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · rw [← h']; rfl
    · rw [Finset.sum_range_succ, rowPoly_eq_sum s m M (by omega),
        convT_eq_zero s M m (by omega)]
      simp

/-- `rowPoly s 0 = 1`. -/
private lemma rowPoly_zero (s : ℕ → ℤ) : rowPoly s 0 = 1 := by
  simp [rowPoly, convT]

/-- The column recursion, with the antidiagonal written as a range sum (the term `pad s 0`
vanishes). -/
private lemma convT_succ_succ (s : ℕ → ℤ) (n k : ℕ) :
    convT s (n + 1) (k + 1) = ∑ j ∈ Finset.range (n + 1), s (j + 1) * convT s (n - j) k := by
  rw [convT, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => pad s (i + 1) * convT s j k) n]
  simp [pad]

/-- The recursion `E(n+1) = x * ∑_{j=0}^{n} s(j+1) E(n-j)` for the row polynomials. -/
private lemma rowPoly_succ (s : ℕ → ℤ) (n : ℕ) :
    rowPoly s (n + 1) =
      X * ∑ j ∈ Finset.range (n + 1), C (s (j + 1)) * rowPoly s (n - j) := by
  calc rowPoly s (n + 1)
      = ∑ k ∈ Finset.range (n + 1), C (convT s (n + 1) (k + 1)) * X ^ (k + 1) := by
        unfold rowPoly
        rw [Finset.sum_range_succ']
        simp [convT]
    _ = ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          X * (C (s (j + 1)) * (C (convT s (n - j) k) * X ^ k)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [convT_succ_succ, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
        ring
    _ = X * ∑ j ∈ Finset.range (n + 1),
          C (s (j + 1)) * ∑ k ∈ Finset.range (n + 1), C (convT s (n - j) k) * X ^ k := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ = X * ∑ j ∈ Finset.range (n + 1), C (s (j + 1)) * rowPoly s (n - j) := by
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [rowPoly_eq_sum s (n - j) (n + 1) (by omega)]

/-- Closed form of Kurkov's polynomials:
`R(m+1, k) = ∑_{j=0}^{m} s(k+j) E(m-j)` with `E` the row polynomials. -/
private lemma R_closed (s : ℕ → ℤ) : ∀ m k : ℕ,
    R s (m + 1) k = ∑ j ∈ Finset.range (m + 1), C (s (k + j)) * rowPoly s (m - j)
  | 0, k => by simp [R, rowPoly_zero]
  | m + 1, k => by
    rw [R, R_closed s m (k + 1), R_closed s m 1, Finset.sum_range_succ' _ (m + 1)]
    have hE : X * ∑ j ∈ Finset.range (m + 1), C (s (1 + j)) * rowPoly s (m - j) =
        rowPoly s (m + 1) := by
      rw [rowPoly_succ]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.add_comm 1 j]
    rw [hE, R]
    simp only [Nat.add_zero, Nat.sub_zero]
    rw [mul_comm (rowPoly s (m + 1))]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.add_sub_add_right, show k + 1 + j = k + (j + 1) by omega]

/-- Part (2) of the conjecture, for every sequence `s`. -/
private lemma part_two (s : ℕ → ℤ) (n : ℕ) (hn : 0 < n) : rowPoly s n = X * R s n 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [R_closed, rowPoly_succ]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.add_comm 1 j]

/-- Casting the convolution triangle along a ring homomorphism. -/
private lemma map_convT {S₁ S₂ : Type*} [CommSemiring S₁] [CommSemiring S₂] (f : S₁ →+* S₂)
    (s : ℕ → S₁) : ∀ k n : ℕ, f (convT s n k) = convT (fun j => f (s j)) n k
  | 0, n => by
    simp only [convT]
    split_ifs <;> simp
  | k + 1, n => by
    simp only [convT, map_sum, map_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_convT f s k p.2]
    congr 1
    unfold pad
    split_ifs <;> simp

/-- Kurkov's conjecture holds: the row polynomials of every integer convolution triangle, and in
particular of A357583, are `x * R(n, 1)`. -/
theorem result : statement := by
  refine ⟨fun n hn => ?_, part_two⟩
  rw [← part_two bellZ n hn]
  unfold rowPoly
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  exact map_convT (Nat.castRingHom ℤ) Nat.bell k n

end Math0.Frontier.A357583

#math0_settles Math0.Frontier.A357583.result Math0.Statements.A357583.statement
