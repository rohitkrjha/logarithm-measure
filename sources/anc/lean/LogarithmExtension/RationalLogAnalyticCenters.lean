import LogarithmExtension.RationalLogMatrixArithmetic
import OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds

/-! Approximation errors and analytic-radius accounting for rational logarithms. -/
noncomputable section
namespace LogarithmExtension.RationalLog

open OAI OAI.PiExponent

variable (base : Base)

def logarithmicPeriod (base : Base) : ℂ := (base.logValue : ℂ)

theorem exp_logarithmicPeriod : Complex.exp (logarithmicPeriod base) = base.complexValue := base.exp_logValue

theorem norm_period_error (p : ℤ) (q : ℕ) :
    ‖(p : ℂ) / (q : ℂ) - (logarithmicPeriod base)‖ = |base.logValue - (p : ℝ) / q| := by
  have he : (p : ℂ) / (q : ℂ) - (logarithmicPeriod base) =
      (((p : ℝ) / q - base.logValue : ℝ) : ℂ) := by
    simp only [logarithmicPeriod, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_intCast, Complex.ofReal_natCast]
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]

theorem norm_center_error_le (nu : ℝ) {p : ℤ} {q j K : ℕ}
    (hj : j ≤ K)
    (happrox : |base.logValue - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ‖(j : ℂ) * ((p : ℂ) / q - (logarithmicPeriod base))‖ ≤
      2 * K * (q : ℝ) ^ (-nu) := by
  rw [norm_mul, norm_period_error base, Complex.norm_natCast]
  have hjR : (j : ℝ) ≤ K := by exact_mod_cast hj
  have hqpow : 0 ≤ (q : ℝ) ^ (-nu) := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ (K : ℝ) * (q : ℝ) ^ (-nu) :=
      mul_le_mul hjR happrox (abs_nonneg _) (Nat.cast_nonneg _)
    _ ≤ _ := by nlinarith [mul_nonneg (Nat.cast_nonneg K) hqpow]

theorem actual_error_exp {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ)
    (j K : ℕ) (nu : ℝ) (hK : 1 ≤ K) (hj : j ≤ K) (hnu : 0 ≤ nu)
    (hq : ∀ i, 1 ≤ q i)
    (happrox : ∀ i, |base.logValue - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-nu)) :
    ∀ i, ‖(j : ℂ) * (MatrixArithmetic.rationalCenters p q i - (logarithmicPeriod base))‖ ≤
      Real.exp ((Real.log (2 * (K : ℝ)) + nu) - nu * MatrixArithmetic.logWeights q i) := by
  intro i
  have hKpos : (0 : ℝ) < 2 * K := by exact_mod_cast (by omega : 0 < 2 * K)
  calc
    _ ≤ 2 * K * (q i : ℝ) ^ (-nu) := norm_center_error_le base nu hj (happrox i)
    _ ≤ 2 * K * (Real.exp nu * Real.exp (-nu * (⌈Real.log (q i)⌉₊ : ℝ))) :=
      mul_le_mul_of_nonneg_left (rpow_neg_le_exp_ceil_log nu hnu (hq i)) (by positivity)
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log hKpos]
      simp only [MatrixArithmetic.logWeights, neg_mul, mul_assoc]

theorem radiusFactor_eq : AnalyticTranslation.radiusFactor (logarithmicPeriod base) = base.radius :=
  base.radius_eq

theorem holomorphicError_eq (K : ℕ) (w0 v0 wstar : ℝ) :
    AnalyticTranslation.holomorphicError (logarithmicPeriod base) K w0 v0 wstar =
      base.radius * K / w0 + Real.log 2 / v0 + Real.log (2 * base.radius * K) / wstar := by
  rw [AnalyticTranslation.holomorphicError, radiusFactor_eq]

end LogarithmExtension.RationalLog
