import LogarithmExtension.GeneralExponent
import LogarithmExtension.AlgebraicLogGeometry
import LogarithmExtension.AlgebraicLogAllEmbeddings

/-!
# Irrationality bounds for logarithms of positive algebraic numbers

For a positive real algebraic number other than one, the approximation
exponent is at most twice its degree. Both determinant inputs are constructed
in the imported developments. No rank or analytic-estimate hypotheses remain.
This bound does not assert exponent two for an arbitrary algebraic base.
-/

namespace LogarithmExtension

theorem algebraicBase_eventual_lower_bound (base : AlgebraicLog.Base) :
    EventualLowerBound base.logValue (2 * base.degree) :=
  AlgebraicLog.DeterminantContradiction.eventualLowerBound_of_interpolation_and_analytic_aggregate
    (AlgebraicLog.Geometry.globalInterpolation base)
    (AlgebraicLog.AllEmbeddings.analyticAggregate base)

theorem algebraicLog_eventual_lower_bound (α : ℝ) (hα : IsAlgebraic ℚ α)
    (hpos : 0 < α) (hne : α ≠ 1) :
    EventualLowerBound (Real.log α) (2 * ((minpoly ℚ α).natDegree : ℝ)) := by
  have h := algebraicBase_eventual_lower_bound (AlgebraicLog.Base.ofAlgebraic α hα hpos hne)
  change EventualLowerBound (Real.log α)
    (2 * (Module.finrank ℚ (IntermediateField.adjoin ℚ ({α} : Set ℝ)) : ℝ)) at h
  rwa [IntermediateField.adjoin.finrank hα.isIntegral] at h

theorem algebraicLog_irrational (α : ℝ) (hα : IsAlgebraic ℚ α)
    (hpos : 0 < α) (hne : α ≠ 1) : Irrational (Real.log α) :=
  irrational_of_eventualLowerBound (algebraicLog_eventual_lower_bound α hα hpos hne)

theorem algebraicLog_irrationalityExponent_le (α : ℝ) (hα : IsAlgebraic ℚ α)
    (hpos : 0 < α) (hne : α ≠ 1) :
    OAI.PiExponent.irrationalityExponent (Real.log α) ≤ 2 * ((minpoly ℚ α).natDegree : ℝ) :=
  irrationalityExponent_le_of_eventualLowerBound
    (algebraicLog_eventual_lower_bound α hα hpos hne)

theorem algebraicLog_irrationalityExponent_bounds (α : ℝ) (hα : IsAlgebraic ℚ α)
    (hpos : 0 < α) (hne : α ≠ 1) :
    2 ≤ OAI.PiExponent.irrationalityExponent (Real.log α) ∧
      OAI.PiExponent.irrationalityExponent (Real.log α) ≤ 2 * ((minpoly ℚ α).natDegree : ℝ) :=
  ⟨two_le_irrationalityExponent_of_eventualLowerBound
      (algebraicLog_eventual_lower_bound α hα hpos hne),
    algebraicLog_irrationalityExponent_le α hα hpos hne⟩

theorem algebraicLog_approximation_bound (α : ℝ) (hα : IsAlgebraic ℚ α)
    (hpos : 0 < α) (hne : α ≠ 1) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-(2 * ((minpoly ℚ α).natDegree : ℝ) + epsilon)) ≤
        |Real.log α - (p : ℝ) / (q : ℝ)| :=
  algebraicLog_eventual_lower_bound α hα hpos hne
    (2 * ((minpoly ℚ α).natDegree : ℝ) + epsilon) (by linarith)

theorem algebraicLogarithm_target : AlgebraicLogarithmTarget := by
  intro α hα hpos hne
  exact ⟨algebraicLog_irrational α hα hpos hne,
    algebraicLog_eventual_lower_bound α hα hpos hne⟩

#print axioms algebraicLogarithm_target
#print axioms algebraicLog_irrationalityExponent_bounds

end LogarithmExtension
