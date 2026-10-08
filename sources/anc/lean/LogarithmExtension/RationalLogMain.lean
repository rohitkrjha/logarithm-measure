import LogarithmExtension.Endpoint
import LogarithmExtension.RationalLogGeometry
import LogarithmExtension.RationalLogAnalyticAggregate

/-! Optimal irrationality exponents of every nonzero real logarithm of a
positive rational number. No interpolation or determinant assumptions remain. -/

namespace LogarithmExtension

theorem rationalBase_eventual_lower_bound (base : RationalLog.Base) :
    EventualLowerBound base.logValue 2 :=
  RationalLog.DeterminantContradiction.eventualLowerBound_of_interpolation_and_analytic_aggregate
    (RationalLog.Geometry.globalInterpolation base) (RationalLog.LiteralAnalytic.analyticAggregate base)

theorem log_nat_div_nat_eventual_lower_bound (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    EventualLowerBound (Real.log ((a : ℝ) / (b : ℝ))) 2 :=
  rationalBase_eventual_lower_bound ⟨a, b, ha, hb, hab⟩

theorem rationalLogarithm_target : RationalLogarithmTarget := by
  intro a b ha hb hab
  have h := log_nat_div_nat_eventual_lower_bound a b ha hb hab
  exact ⟨irrational_of_eventualLowerBound h, h⟩

theorem rationalLog_eventual_lower_bound (r : ℚ) (hr : 0 < r) (hr1 : r ≠ 1) :
    EventualLowerBound (Real.log (r : ℝ)) 2 := by
  have hn : 0 < r.num := Rat.num_pos.mpr hr
  have hnum : (r.num.toNat : ℝ) = (r.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn.le
  have hval : (r.num.toNat : ℝ) / (r.den : ℝ) = (r : ℝ) := by
    rw [hnum, Rat.cast_def]
  have hne : r.num.toNat ≠ r.den := by
    intro he
    have hd : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    have hrval : (r : ℝ) = 1 := by rw [← hval, he, div_self hd]
    exact hr1 (by exact_mod_cast hrval)
  have h := log_nat_div_nat_eventual_lower_bound r.num.toNat r.den
    (by omega) r.pos hne
  simpa only [hval] using h

theorem rationalLog_irrational (r : ℚ) (hr : 0 < r) (hr1 : r ≠ 1) :
    Irrational (Real.log (r : ℝ)) :=
  irrational_of_eventualLowerBound (rationalLog_eventual_lower_bound r hr hr1)

theorem rationalLog_irrationalityExponent_eq_two (r : ℚ) (hr : 0 < r) (hr1 : r ≠ 1) :
    OAI.PiExponent.irrationalityExponent (Real.log (r : ℝ)) = 2 :=
  irrationalityExponent_eq_two (rationalLog_eventual_lower_bound r hr hr1)

theorem rationalLog_approximation_bound (r : ℚ) (hr : 0 < r) (hr1 : r ≠ 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-(2 + epsilon)) ≤ |Real.log (r : ℝ) - (p : ℝ) / (q : ℝ)| :=
  rationalLog_eventual_lower_bound r hr hr1 (2 + epsilon) (by linarith)

#print axioms rationalLogarithm_target
#print axioms rationalLog_irrationalityExponent_eq_two

end LogarithmExtension
