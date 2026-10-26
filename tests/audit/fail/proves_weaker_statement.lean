-- expect: math0 statement check failed
import Math0.Audit
-- Upstream statements are theorems proved by `sorry`; only their types matter.
theorem upstream : ∀ n : Nat, n < 2 * n + 1 := sorry
theorem ours : ∀ n : Nat, n ≤ 2 * n + 1 := fun n => by omega
#math0_proves ours upstream
