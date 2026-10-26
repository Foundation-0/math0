-- expect: math0 audit failed
import Math0.Audit
theorem upstream : ∀ n : Nat, n + 0 = n := sorry
theorem ours : ∀ n : Nat, n + 0 = n := sorry
#math0_proves ours upstream
