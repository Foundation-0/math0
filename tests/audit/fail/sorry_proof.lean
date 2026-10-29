-- expect: math0 audit failed
import Math0.Audit
theorem t : 1 + 1 = 2 := sorry
#math0_audit t
