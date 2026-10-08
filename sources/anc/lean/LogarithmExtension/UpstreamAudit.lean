import OAI.NumberTheory.PiExponent.Main

/-!
# Verification of the reference endpoint

This is the upstream pi theorem, not a theorem about logarithms. The source
checkout is pinned to adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

#check @OAI.PiExponent.pi_irrationalityExponent_eq_two
#print axioms OAI.PiExponent.pi_eventual_lower_bound
#print axioms OAI.PiExponent.pi_irrationalityExponent_eq_two
#print axioms OAI.PiExponent.main
