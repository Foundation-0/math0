-- expect: math0 statement check failed
import Math0.Audit
theorem upstream : ∀ n : Nat, n + 0 = n := sorry
theorem ours : ∀ n : Nat, n + 0 = n := fun _ => rfl
#math0_refutes ours upstream
