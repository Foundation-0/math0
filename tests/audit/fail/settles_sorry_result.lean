-- expect: math0 audit failed
import Math0.Audit
def statement : Prop := ∀ n : Nat, n + 0 = n
theorem result : statement := sorry
#math0_settles result statement
