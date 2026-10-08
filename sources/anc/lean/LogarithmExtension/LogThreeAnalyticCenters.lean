import LogarithmExtension.LogThreeMatrixArithmetic
import OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds

/-! Approximation errors and analytic-radius accounting for log(3). -/
noncomputable section
namespace LogarithmExtension.LogThree

open OAI OAI.PiExponent

def logarithmicPeriod : ℂ := (Real.log 3 : ℂ)

theorem exp_logarithmicPeriod : Complex.exp logarithmicPeriod = 3 := by
  rw [logarithmicPeriod, ← Complex.ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  norm_num

theorem norm_period_error (p : ℤ) (q : ℕ) :
    ‖(p : ℂ) / (q : ℂ) - logarithmicPeriod‖ = |Real.log 3 - (p : ℝ) / q| := by
  have he : (p : ℂ) / (q : ℂ) - logarithmicPeriod =
      (((p : ℝ) / q - Real.log 3 : ℝ) : ℂ) := by
    simp only [logarithmicPeriod, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_intCast, Complex.ofReal_natCast]
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]

theorem norm_center_error_le (nu : ℝ) {p : ℤ} {q j K : ℕ}
    (hj : j ≤ K)
    (happrox : |Real.log 3 - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ‖(j : ℂ) * ((p : ℂ) / q - logarithmicPeriod)‖ ≤
      2 * K * (q : ℝ) ^ (-nu) := by
  rw [norm_mul, norm_period_error, Complex.norm_natCast]
  have hjR : (j : ℝ) ≤ K := by exact_mod_cast hj
  have hqpow : 0 ≤ (q : ℝ) ^ (-nu) := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ (K : ℝ) * (q : ℝ) ^ (-nu) :=
      mul_le_mul hjR happrox (abs_nonneg _) (Nat.cast_nonneg _)
    _ ≤ _ := by nlinarith [mul_nonneg (Nat.cast_nonneg K) hqpow]

theorem actual_error_exp {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ)
    (j K : ℕ) (nu : ℝ) (hK : 1 ≤ K) (hj : j ≤ K) (hnu : 0 ≤ nu)
    (hq : ∀ i, 1 ≤ q i)
    (happrox : ∀ i, |Real.log 3 - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-nu)) :
    ∀ i, ‖(j : ℂ) * (MatrixArithmetic.rationalCenters p q i - logarithmicPeriod)‖ ≤
      Real.exp ((Real.log (2 * (K : ℝ)) + nu) - nu * MatrixArithmetic.logWeights q i) := by
  intro i
  have hKpos : (0 : ℝ) < 2 * K := by exact_mod_cast (by omega : 0 < 2 * K)
  calc
    _ ≤ 2 * K * (q i : ℝ) ^ (-nu) := norm_center_error_le nu hj (happrox i)
    _ ≤ 2 * K * (Real.exp nu * Real.exp (-nu * (⌈Real.log (q i)⌉₊ : ℝ))) :=
      mul_le_mul_of_nonneg_left (rpow_neg_le_exp_ceil_log nu hnu (hq i)) (by positivity)
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log hKpos]
      simp only [MatrixArithmetic.logWeights, neg_mul, mul_assoc]

theorem radiusFactor_le : AnalyticTranslation.radiusFactor logarithmicPeriod ≤ 300 := by
  have hpos : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlt : Real.log 3 < 2 := Real.log_three_lt_d9.trans (by norm_num)
  simp only [AnalyticTranslation.radiusFactor, logarithmicPeriod,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
  linarith

theorem holomorphicError_le (K : ℕ) (w0 v0 wstar : ℝ)
    (hK : 0 < K) (hw0 : 0 < w0) (hws : 0 < wstar) :
    AnalyticTranslation.holomorphicError logarithmicPeriod K w0 v0 wstar ≤
      300 * K / w0 + Real.log 2 / v0 + Real.log (600 * K) / wstar := by
  have hrad : 0 < AnalyticTranslation.radiusFactor logarithmicPeriod :=
    lt_of_lt_of_le (by norm_num) (AnalyticTranslation.radiusFactor_ge _)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hfirst := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right radiusFactor_le hKpos.le) hw0.le
  have hlog : Real.log (2 * AnalyticTranslation.radiusFactor logarithmicPeriod * K) ≤
      Real.log (600 * K) := by
    apply Real.log_le_log (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right radiusFactor_le hKpos.le]
  have hlast := div_le_div_of_nonneg_right hlog hws.le
  unfold AnalyticTranslation.holomorphicError
  linarith

end LogarithmExtension.LogThree
