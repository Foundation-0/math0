/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Math0.Statements.OEIS.A338885
import Math0.Audit

/-!
# A338885: the smallest number in row 655 is not A228286(655)

Kagey's conjecture says that the smallest `k` for which a diagonal lattice rectangle touches all
four sides of an `n X k` box is `A228286 n`. It fails at `n = 655`.

* `104` is in row `655`: the rectangle with vertices `(4, 0)`, `(655, 42)`, `(651, 104)`,
  `(0, 62)` has side vectors `u = (651, 42)` and `v = (-4, 62)`, which are perpendicular since
  `651 * (-4) + 42 * 62 = -2604 + 2604 = 0`; it lies in `[0, 655] × [0, 104]`, touches all four
  sides, and has no horizontal side.
* Every value `x + y * z` with `x, y, z ≥ 1` and `x * y + z = 655` is at least `105` (in fact
  the minimum `A228286 655` is `115`). If `x + y * z ≤ 104` then `x ≤ 104` and
  `y ≤ y * z ≤ 104`, and a kernel-checked search over the `104 × 104` pairs `(x, y)` (with
  `z = 655 - x * y`) shows that this never happens.

Hence `A228286 655 ≥ 105 > 104`, so `A228286 655` is not a lower bound of row `655`.
-/

namespace Math0.Frontier.A338885
open Math0.Statements.A338885

/-- Finite search: for `1 ≤ x, y ≤ 104` with `x * y < 655`, the value
`x + y * (655 - x * y)` is at least `105` (kernel-checked). -/
private theorem search : ∀ x < 105, ∀ y < 105, 0 < x → 0 < y → x * y < 655 →
    105 ≤ x + y * (655 - x * y) := by
  decide +kernel

/-- Every element of `A228286Set 655` is at least `105`. -/
private theorem ge_of_mem {m : ℕ} (hm : m ∈ A228286Set 655) : 105 ≤ m := by
  obtain ⟨x, y, z, hx, hy, hz, hsum, rfl⟩ := hm
  by_contra hlt
  have hyz : y ≤ y * z := Nat.le_mul_of_pos_right y hz
  have hz' : z = 655 - x * y := by omega
  have h := search x (by omega) y (by omega) hx hy (by omega)
  rw [← hz'] at h
  omega

/-- The explicit diagonal lattice rectangle with vertices `(4, 0)`, `(655, 42)`, `(651, 104)`,
`(0, 62)` shows that `104` is in row `655`. -/
private theorem inRow_655_104 : InRow 655 104 := by
  refine ⟨4, 0, 651, 42, -4, 62, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [vertices, InBox, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    norm_num
  · exact ⟨(0, 62), by simp [vertices], by norm_num⟩
  · exact ⟨(655, 42), by simp [vertices], by norm_num⟩
  · exact ⟨(4, 0), by simp [vertices], by norm_num⟩
  · exact ⟨(651, 104), by simp [vertices], by norm_num⟩

/-- Kagey's conjecture fails at `n = 655`: `104` is in row `655` but `A228286 655 ≥ 105`. -/
theorem result : ¬ statement := by
  intro h
  have hle : A228286 655 ≤ 104 := (h 655 (by norm_num)).2 inRow_655_104
  have hge : 105 ≤ A228286 655 := ge_of_mem (isLeast_A228286 (by norm_num)).1
  omega

end Math0.Frontier.A338885

#math0_settles Math0.Frontier.A338885.result Math0.Statements.A338885.statement
