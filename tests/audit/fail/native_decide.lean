-- expect: math0 audit failed
import Math0.Audit
theorem t : 2 + 2 = 4 := by native_decide
#math0_audit t
