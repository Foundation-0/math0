-- expect: math0 statement check failed
import Math0.Audit
def statement : Prop := ∀ n : Nat, n + 0 = n
-- Proving the unfolded body is not accepted: the type must be exactly `statement` or `¬ statement`.
theorem result : ∀ n : Nat, n + 0 = n := fun _ => rfl
#math0_settles result statement
