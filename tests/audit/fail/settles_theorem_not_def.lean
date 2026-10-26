-- expect: math0 statement check failed
import Math0.Audit
theorem statement : True := trivial
theorem result : True := trivial
#math0_settles result statement
