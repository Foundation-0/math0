-- expect: math0 statement check failed
import Math0.Audit
-- Definitionally equal but not syntactically equal types are rejected: no unfolding.
def double (n : Nat) : Nat := 2 * n
theorem upstream : ∀ n : Nat, double n = 2 * n := sorry
theorem ours : ∀ n : Nat, 2 * n = 2 * n := fun _ => rfl
#math0_proves ours upstream
