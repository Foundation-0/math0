/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A060693
import Math0.Audit

/-!
# Schulte's alternating quadratic sum over the Schröder-peaks triangle

We prove Werner Schulte's conjecture for A060693: for every `n ≥ 0`,
`∑_{k=0}^{n} (-1)^k · T(n,k) · (n+1-k)^2 = 1 + n + n^2`,
where `T(n,k)` counts Schröder paths of semilength `n` with `k` peaks.

**Idea.** Write `(n+1-k)^2 = (n+1)^2 - (2n+1)·k + k(k-1)`, so the sum is
`(n+1)^2 S₀ - (2n+1) S₁ + S₂` with `S_r = ∑_k (-1)^k k^{(r)} T(n,k)` (falling factorials
`1, k, k(k-1)`). We compute these three alternating moments for the generalized counts
`cnt m h b k` of the statement file (paths of width `m` from height `h`, an initial `D` counting
as a peak when `b`), using the three-term recursion `cnt_step`. With `m = h + 2s` the moments are
* `S₀ = [s = 0]·(b ∧ h ≠ 0 ? -1 : 1)`,
* `S₁ = [s = 0]·(b ∧ h ≠ 0 ? -1 : 0) + [s ≥ 1]·(b ? h - 1 : -(h+1))`,
* `S₂ = [s ≥ 1]·((h+1)(s-1)(s+h) + (b ? 2h - 2h(s-1)(s+h-1) : 0))`,

proved by strong induction on `m` (an initial `D` after a `U` shifts the peak index, which turns
the weight `(-1)^k k^{(r)}` into a combination of lower moments). Combinatorially these are the
coefficients of `t^0, t^1, t^2` after substituting `x = t - 1` for the peak variable, i.e.
counts of Dyck paths with `0`, `1`, `2` peaks (each `H` is a peak `UD` that was "flattened").
Finally peaks number at most `n` (`2·peaks + h ≤ width + 2b`), so for `h = 0`, `b = false`,
`s = n` we get `S₀ = [n = 0]`, `S₁ = -[n ≥ 1]`, `S₂ = n(n-1)`, and the sum is
`2n + 1 + n(n-1) = n^2 + n + 1` for `n ≥ 1` and `1` for `n = 0`.
-/

namespace Math0.Frontier.A060693
open Math0.Statements.A060693
open Math0.Statements.A060693.Step

/-! ### A bound on the number of peaks -/

/-- Each peak uses up a `U` and a `D` (except a leading `D` when `b`), so
`2·peaks + h ≤ width + 2b` for a valid walk from height `h`. -/
private theorem peaks_bound : ∀ (p : List Step) (h : ℕ) (b : Bool), valid h p = true →
    2 * peaksFrom b p + h ≤ width p + 2 * b.toNat
  | [], h, b => by simp [valid, peaksFrom]; intro h0; omega
  | U :: p, h, b => by
    intro hv
    have := peaks_bound p (h + 1) true hv
    simp only [peaksFrom, width_cons, Step.dx, Bool.toNat_true] at this ⊢
    omega
  | D :: p, 0, b => by simp [valid]
  | D :: p, h + 1, b => by
    intro hv
    have := peaks_bound p h false hv
    simp only [peaksFrom, width_cons, Step.dx, Bool.toNat_false] at this ⊢
    cases b <;> simp <;> omega
  | H :: p, h, b => by
    intro hv
    have := peaks_bound p h false hv
    simp only [peaksFrom, width_cons, Step.dx, Bool.toNat_false] at this ⊢
    omega

/-- A Schröder path of width `m` has at most `m / 2` peaks. -/
private theorem cnt_peaks (m k : ℕ) (hk : m < 2 * k) : cnt m 0 false k = 0 := by
  rw [cnt, List.countP_eq_zero]
  intro w hw
  rw [mem_words] at hw
  simp only [Bool.and_eq_true, beq_iff_eq, not_and]
  intro hv hpk
  have := peaks_bound w 0 false hv
  simp at this
  omega

/-! ### Weighted sums and their recursion -/

/-- The weighted count `∑_k w(k) · cnt m h b k`. -/
private def W (w : ℕ → ℤ) (m h : ℕ) (b : Bool) : ℤ :=
  ∑ k ∈ Finset.range (m + 1), w k * (cnt m h b k : ℤ)

/-- The range of summation may be enlarged. -/
private theorem W_eq_range (w : ℕ → ℤ) (m h : ℕ) (b : Bool) (N : ℕ) (hN : m + 1 ≤ N) :
    ∑ k ∈ Finset.range N, w k * (cnt m h b k : ℤ) = W w m h b := by
  unfold W
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk'
    simp only [Finset.mem_range, not_lt] at hk hk'
    rw [cnt_eq_zero m h b k (by omega)]
    simp

/-- `W` vanishes below the diagonal. -/
private theorem W_zero_lt (w : ℕ → ℤ) (m h : ℕ) (b : Bool) (hm : m < h) : W w m h b = 0 := by
  unfold W
  apply Finset.sum_eq_zero
  intro k _
  rw [cnt_eq_zero m h b k (Or.inl hm)]
  simp

/-- `W` is linear in the weight. -/
private theorem W_lin (w u v : ℕ → ℤ) (a c : ℤ) (hw : ∀ k, w k = a * u k + c * v k)
    (m h : ℕ) (b : Bool) : W w m h b = a * W u m h b + c * W v m h b := by
  unfold W
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [hw]
  ring

/-- The contribution of an initial `D` step. -/
private def Dpart (w : ℕ → ℤ) (m : ℕ) : ℕ → Bool → ℤ
  | 0, _ => 0
  | h + 1, false => W w (m + 1) h false
  | h + 1, true => W (fun k => w (k + 1)) (m + 1) h false

/-- The recursion for `W`, from `cnt_step`. -/
private theorem W_step (w : ℕ → ℤ) (m h : ℕ) (b : Bool) :
    W w (m + 2) h b = W w (m + 1) (h + 1) true + W w m h false + Dpart w m h b := by
  have e : W w (m + 2) h b = ∑ k ∈ Finset.range (m + 3),
      (w k * (cnt (m + 1) (h + 1) true k : ℤ) + w k * (cnt m h false k : ℤ) +
        w k * (dTerm (cnt (m + 1)) h b k : ℤ)) := by
    unfold W
    apply Finset.sum_congr rfl
    intro k _
    rw [cnt_step, step]
    push_cast
    ring
  rw [e, Finset.sum_add_distrib, Finset.sum_add_distrib, W_eq_range _ _ _ _ _ (by omega),
    W_eq_range _ _ _ _ _ (by omega)]
  congr 1
  rcases h with _ | h
  · simp [dTerm, Dpart]
  · cases b
    · simp only [dTerm, Dpart]
      exact W_eq_range _ _ _ _ _ (by omega)
    · rw [Finset.sum_range_succ']
      simp only [dTerm, Dpart, Nat.cast_zero, mul_zero, add_zero]
      exact W_eq_range _ _ _ _ _ (by omega)

private theorem cnt00 (b : Bool) (k : ℕ) : cnt 0 0 b k = if k = 0 then 1 else 0 := by
  rcases k with _ | k <;> cases b <;> simp [cnt, words, valid, peaksFrom]

private theorem W_base0 (w : ℕ → ℤ) (b : Bool) : W w 0 0 b = w 0 := by
  simp [W, cnt00]

private theorem W_base1f (w : ℕ → ℤ) : W w 1 1 false = w 0 := by
  simp [W, cnt, words, valid, peaksFrom]

private theorem W_base1t (w : ℕ → ℤ) : W w 1 1 true = w 1 := by
  simp [W, cnt, words, valid, peaksFrom]

/-- A generic closed-form principle: if `F` matches the base cases and satisfies the recursion
(with the initial-`D` shift expressed through `L`), then `W w m h b = F h s b` for `m = h + 2s`. -/
private theorem closed_gen (w : ℕ → ℤ) (F : ℕ → ℕ → Bool → ℤ) (L : ℕ → ℕ → ℤ)
    (h0 : ∀ b, F 0 0 b = w 0) (h1f : F 1 0 false = w 0) (h1t : F 1 0 true = w 1)
    (hsh : ∀ m h s, h + 2 * s = m + 1 →
      W (fun k => w (k + 1)) (m + 1) h false = -W w (m + 1) h false + L h s)
    (hrec : ∀ h s b, 2 ≤ h + 2 * s → F h s b =
      (if s = 0 then 0 else F (h + 1) (s - 1) true + F h (s - 1) false) +
      (if h = 0 then 0 else if b then -F (h - 1) s false + L (h - 1) s else F (h - 1) s false)) :
    ∀ m h s b, h + 2 * s = m → W w m h b = F h s b := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro h s b hm
  match m, ih, hm with
  | 0, _, hm =>
    obtain ⟨rfl, rfl⟩ : h = 0 ∧ s = 0 := by omega
    rw [W_base0, h0]
  | 1, _, hm =>
    obtain ⟨rfl, rfl⟩ : h = 1 ∧ s = 0 := by omega
    cases b
    · rw [W_base1f, h1f]
    · rw [W_base1t, h1t]
  | m + 2, ih, hm =>
    rw [hrec h s b (by omega), W_step]
    have hA : W w (m + 1) (h + 1) true + W w m h false =
        (if s = 0 then 0 else F (h + 1) (s - 1) true + F h (s - 1) false) := by
      rcases s with _ | s
      · rw [W_zero_lt _ _ _ _ (by omega), W_zero_lt _ _ _ _ (by omega)]
        simp
      · rw [ih (m + 1) (by omega) (h + 1) s true (by omega), ih m (by omega) h s false (by omega)]
        simp
    have hC : Dpart w m h b =
        (if h = 0 then 0 else if b then -F (h - 1) s false + L (h - 1) s
          else F (h - 1) s false) := by
      rcases h with _ | h
      · simp [Dpart]
      · cases b
        · simp only [Dpart, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
            Bool.false_eq_true]
          exact ih (m + 1) (by omega) h s false (by omega)
        · simp only [Dpart, Nat.add_one_ne_zero, if_false, if_true, Nat.add_sub_cancel]
          rw [hsh m h s (by omega), ih (m + 1) (by omega) h s false (by omega)]
    rw [hA, hC]

/-! ### The three moments -/

/-- Weight `(-1)^k`. -/
private def w0 (k : ℕ) : ℤ := (-1) ^ k

/-- Weight `(-1)^k · k`. -/
private def w1 (k : ℕ) : ℤ := (-1) ^ k * k

/-- Weight `(-1)^k · k(k-1)`. -/
private def w2 (k : ℕ) : ℤ := (-1) ^ k * ((k : ℤ) * ((k : ℤ) - 1))

/-- Closed form of the zeroth moment. -/
private def F0 (h s : ℕ) (b : Bool) : ℤ :=
  if s = 0 then (if b = true ∧ h ≠ 0 then -1 else 1) else 0

/-- Closed form of the first moment. -/
private def F1 (h s : ℕ) (b : Bool) : ℤ :=
  if s = 0 then (if b = true ∧ h ≠ 0 then -1 else 0)
  else (if b then (h : ℤ) - 1 else -((h : ℤ) + 1))

/-- Closed form of the second moment. -/
private def F2 (h s : ℕ) (b : Bool) : ℤ :=
  if s = 0 then 0
  else ((h : ℤ) + 1) * ((s : ℤ) - 1) * ((s : ℤ) + h) +
    (if b then 2 * (h : ℤ) - 2 * (h : ℤ) * ((s : ℤ) - 1) * ((s : ℤ) + h - 1) else 0)

private theorem W0_closed : ∀ m h s b, h + 2 * s = m → W w0 m h b = F0 h s b := by
  apply closed_gen w0 F0 (fun _ _ => 0)
  · intro b; cases b <;> simp [F0, w0]
  · simp [F0, w0]
  · simp [F0, w0]
  · intro m h s _
    rw [W_lin (fun k => w0 (k + 1)) w0 w0 (-1) 0 (fun k => by simp [w0, pow_succ])]
    ring
  · intro h s b hs
    rcases s with _ | _ | s <;> rcases h with _ | _ | h <;> cases b <;> simp [F0] <;> omega

private theorem W1_closed : ∀ m h s b, h + 2 * s = m → W w1 m h b = F1 h s b := by
  apply closed_gen w1 F1 (fun h s => -F0 h s false)
  · intro b; cases b <;> simp [F1, w1]
  · simp [F1, w1]
  · simp [F1, w1]
  · intro m h s hs
    rw [W_lin (fun k => w1 (k + 1)) w1 w0 (-1) (-1) (fun k => by simp [w1, w0, pow_succ]; ring),
      W0_closed (m + 1) h s false hs]
    ring
  · intro h s b hs
    rcases s with _ | _ | s <;> rcases h with _ | _ | h <;> cases b <;> simp [F0, F1]

private theorem W2_closed : ∀ m h s b, h + 2 * s = m → W w2 m h b = F2 h s b := by
  apply closed_gen w2 F2 (fun h s => -2 * F1 h s false)
  · intro b; cases b <;> simp [F2, w2]
  · simp [F2, w2]
  · simp [F2, w2]
  · intro m h s hs
    rw [W_lin (fun k => w2 (k + 1)) w2 w1 (-1) (-2) (fun k => by simp [w2, w1, pow_succ]; ring),
      W1_closed (m + 1) h s false hs]
    ring
  · intro h s b hs
    rcases s with _ | _ | s <;> rcases h with _ | _ | h <;> cases b <;> simp [F1, F2] <;>
      ring_nf

/-! ### The identity -/

/-- Schulte's conjecture holds: `∑_{k=0}^{n} (-1)^k T(n,k) (n+1-k)^2 = 1 + n + n^2`. -/
theorem result : statement := by
  intro n
  have hT : ∀ k, (T n k : ℤ) = (cnt (2 * n) 0 false k : ℤ) := fun k => by rw [T_eq_cnt]
  simp_rw [hT]
  have hext : ∑ k ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ k * (cnt (2 * n) 0 false k : ℤ) * ((n : ℤ) + 1 - k) ^ 2 =
      ∑ k ∈ Finset.range (2 * n + 1),
      (-1 : ℤ) ^ k * (cnt (2 * n) 0 false k : ℤ) * ((n : ℤ) + 1 - k) ^ 2 := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    · intro k hk hk'
      simp only [Finset.mem_range, not_lt] at hk hk'
      rw [cnt_peaks (2 * n) k (by omega)]
      simp
  rw [hext]
  have hsplit : ∑ k ∈ Finset.range (2 * n + 1),
      (-1 : ℤ) ^ k * (cnt (2 * n) 0 false k : ℤ) * ((n : ℤ) + 1 - k) ^ 2 =
      ((n : ℤ) + 1) ^ 2 * W w0 (2 * n) 0 false - (2 * (n : ℤ) + 1) * W w1 (2 * n) 0 false +
        W w2 (2 * n) 0 false := by
    simp only [W, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [w0, w1, w2]
    ring
  rw [hsplit, W0_closed (2 * n) 0 n false (by omega), W1_closed (2 * n) 0 n false (by omega),
    W2_closed (2 * n) 0 n false (by omega)]
  rcases n with _ | n
  · simp [F0, F1, F2]
  · simp [F0, F1, F2]
    ring

end Math0.Frontier.A060693

#math0_settles Math0.Frontier.A060693.result Math0.Statements.A060693.statement
