-- expect: math0 audit failed
import Math0.Audit
-- A statement that hides a `sorry` is rejected even if the result itself is sorry-free.
def statement : Prop := sorry
theorem result : statement := sorry
#math0_settles result statement
