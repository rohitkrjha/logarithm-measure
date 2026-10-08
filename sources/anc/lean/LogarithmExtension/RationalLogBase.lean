import Mathlib
import LogarithmExtension.AnalyticTranslation

/-! Positive rational bases different from one, with all fixed analytic and
arithmetic costs explicit. -/

noncomputable section
namespace LogarithmExtension.RationalLog

structure Base where
  numerator : ℕ
  denominator : ℕ
  numerator_pos : 0 < numerator
  denominator_pos : 0 < denominator
  numerator_ne_denominator : numerator ≠ denominator

namespace Base
variable (r : Base)

def value : ℝ := (r.numerator : ℝ) / (r.denominator : ℝ)
def complexValue : ℂ := (r.numerator : ℂ) / (r.denominator : ℂ)
def logValue : ℝ := Real.log r.value
def radius : ℝ := 100 * (1 + |r.logValue|)
def denominatorCost : ℝ := Real.log (r.denominator : ℝ)

theorem value_pos : 0 < r.value := by
  exact div_pos (by exact_mod_cast r.numerator_pos) (by exact_mod_cast r.denominator_pos)

theorem value_ne_one : r.value ≠ 1 := by
  intro h
  have hd : (r.denominator : ℝ) ≠ 0 := by exact_mod_cast r.denominator_pos.ne'
  have he : (r.numerator : ℝ) = r.denominator := by
    simpa only [one_mul] using (div_eq_iff hd).mp h
  exact r.numerator_ne_denominator (by exact_mod_cast he)

theorem logValue_ne_zero : r.logValue ≠ 0 := by
  intro h
  exact r.value_ne_one (Real.eq_one_of_pos_of_log_eq_zero r.value_pos h)

theorem complexValue_eq : r.complexValue = (r.value : ℂ) := by
  simp only [complexValue, value, Complex.ofReal_div, Complex.ofReal_natCast]

theorem complexValue_ne_zero : r.complexValue ≠ 0 := by
  rw [complexValue_eq]
  exact_mod_cast r.value_pos.ne'

theorem exp_logValue : Complex.exp (r.logValue : ℂ) = r.complexValue := by
  rw [← Complex.ofReal_exp, logValue, Real.exp_log r.value_pos, complexValue_eq]

theorem radius_ge : 100 ≤ r.radius := by
  unfold radius
  nlinarith [abs_nonneg r.logValue]

theorem radius_pos : 0 < r.radius := lt_of_lt_of_le (by norm_num) r.radius_ge

theorem denominatorCost_nonneg : 0 ≤ r.denominatorCost := by
  apply Real.log_nonneg
  exact_mod_cast r.denominator_pos

theorem radius_eq : AnalyticTranslation.radiusFactor (r.logValue : ℂ) = r.radius := by
  simp only [AnalyticTranslation.radiusFactor, radius, Complex.norm_real, Real.norm_eq_abs]

end Base
end LogarithmExtension.RationalLog

