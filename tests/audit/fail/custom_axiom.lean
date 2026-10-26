-- expect: math0 audit failed
import Math0.Audit
axiom cheat : False
theorem t : 1 = 2 := cheat.elim
#math0_audit t
