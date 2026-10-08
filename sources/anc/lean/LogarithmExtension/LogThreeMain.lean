import LogarithmExtension.Endpoint
import LogarithmExtension.LogThreeGeometry
import LogarithmExtension.LogThreeAnalyticAggregate

/-!
# The irrationality exponent of log(3)

The endpoint below has no approximation, interpolation, determinant, or
analytic-estimate hypotheses. Both determinant inputs are supplied by the
checked logarithm-specific developments.
-/

namespace LogarithmExtension

/-- No rational approximation exponent greater than two persists at arbitrarily
large denominators for the natural logarithm of three. -/
theorem logThree_eventual_lower_bound :
    EventualLowerBound (Real.log 3) 2 :=
  LogThree.DeterminantContradiction.eventualLowerBound_of_interpolation_and_analytic_aggregate
    LogThree.Geometry.globalInterpolation LogThree.LiteralAnalytic.analyticAggregate

theorem logThree_irrational : Irrational (Real.log 3) :=
  irrational_of_eventualLowerBound logThree_eventual_lower_bound

/-- Unconditional endpoint, using the standard rational-approximation exponent
defined in the reference development. -/
theorem logThree_irrationalityExponent_eq_two :
    OAI.PiExponent.irrationalityExponent (Real.log 3) = 2 :=
  irrationalityExponent_eq_two logThree_eventual_lower_bound

theorem logThree_target : LogThreeTarget :=
  ⟨logThree_irrational, logThree_eventual_lower_bound⟩

/-- The exponent-two approximation estimate in epsilon notation. -/
theorem logThree_approximation_bound (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-(2 + epsilon)) ≤ |Real.log 3 - (p : ℝ) / (q : ℝ)| :=
  logThree_eventual_lower_bound (2 + epsilon) (by linarith)

#print axioms logThree_eventual_lower_bound
#print axioms logThree_irrational
#print axioms logThree_irrationalityExponent_eq_two
#print axioms logThree_target

end LogarithmExtension

