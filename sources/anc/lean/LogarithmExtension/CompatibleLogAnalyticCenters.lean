import LogarithmExtension.CompatibleLogMatrixArithmetic
import OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds

/-! Approximation errors and a uniform analytic radius for all compatible
embeddings, with the algebraic slope retained in every matrix center. -/

noncomputable section
namespace LogarithmExtension.CompatibleLog

open OAI OAI.PiExponent

variable (base : Base) (σ : base.carrier →ₐ[ℚ] ℂ)

theorem norm_period_error (p : ℤ) (q : ℕ) :
    ‖σ base.slope * (p : ℂ) / (q : ℂ) - base.period σ‖ =
      ‖σ base.slope‖ * |base.value - (p : ℝ) / q| := by
  have he : σ base.slope * (p : ℂ) / (q : ℂ) - base.period σ =
      σ base.slope * ((((p : ℝ) / q - base.value : ℝ) : ℂ)) := by
    simp only [Base.period, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_intCast, Complex.ofReal_natCast]
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]

theorem norm_center_error_le (nu : ℝ) {p : ℤ} {q j K : ℕ}
    (hj : j ≤ K)
    (happrox : |base.value - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ‖(j : ℂ) * (σ base.slope * (p : ℂ) / q - base.period σ)‖ ≤
      2 * K * base.gammaSize * (q : ℝ) ^ (-nu) := by
  rw [norm_mul, norm_period_error base σ, Complex.norm_natCast]
  have hjR : (j : ℝ) ≤ K := by exact_mod_cast hj
  have hqpow : 0 ≤ (q : ℝ) ^ (-nu) := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ (K : ℝ) * (base.gammaSize * (q : ℝ) ^ (-nu)) :=
      mul_le_mul hjR
        (mul_le_mul (base.norm_slope_le_gammaSize σ) happrox (abs_nonneg _)
          base.gammaSize_pos.le)
        (mul_nonneg (norm_nonneg _) (abs_nonneg _)) (Nat.cast_nonneg _)
    _ ≤ _ := by
      have hs := mul_nonneg (Nat.cast_nonneg K) (mul_nonneg base.gammaSize_pos.le hqpow)
      nlinarith

theorem actual_error_exp {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ)
    (j K : ℕ) (nu : ℝ) (hK : 1 ≤ K) (hj : j ≤ K) (hnu : 0 ≤ nu)
    (hq : ∀ i, 1 ≤ q i)
    (happrox : ∀ i, |base.value - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-nu)) :
    ∀ i, ‖(j : ℂ) * (MatrixArithmetic.scaledCenters base σ p q i - base.period σ)‖ ≤
      Real.exp ((Real.log (2 * (K : ℝ) * base.gammaSize) + nu) -
        nu * MatrixArithmetic.logWeights q i) := by
  intro i
  have hKr : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hKpos : (0 : ℝ) < 2 * K * base.gammaSize :=
    mul_pos (mul_pos (by norm_num) hKr) base.gammaSize_pos
  calc
    _ ≤ 2 * K * base.gammaSize * (q i : ℝ) ^ (-nu) :=
      norm_center_error_le base σ nu hj (happrox i)
    _ ≤ (2 * K * base.gammaSize) *
        (Real.exp nu * Real.exp (-nu * (⌈Real.log (q i)⌉₊ : ℝ))) :=
      mul_le_mul_of_nonneg_left (rpow_neg_le_exp_ceil_log nu hnu (hq i)) hKpos.le
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log hKpos]
      simp only [MatrixArithmetic.logWeights, neg_mul, mul_assoc]

theorem holomorphicError_le (K : ℕ) (w0 v0 wstar : ℝ)
    (hK : 0 < K) (hw0 : 0 < w0) (hwstar : 0 < wstar) :
    AnalyticTranslation.holomorphicError (base.period σ) K w0 v0 wstar ≤
      base.radius * K / w0 + Real.log 2 / v0 +
        Real.log (2 * base.radius * K) / wstar := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hR : 0 < AnalyticTranslation.radiusFactor (base.period σ) :=
    lt_of_lt_of_le (by norm_num) (AnalyticTranslation.radiusFactor_ge _)
  have hfirst := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (base.radiusFactor_le σ) hKr.le) hw0.le
  have hlog : Real.log (2 * AnalyticTranslation.radiusFactor (base.period σ) * K) ≤
      Real.log (2 * base.radius * K) := by
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (base.radiusFactor_le σ) (by norm_num)) hKr.le
  have hlast := div_le_div_of_nonneg_right hlog hwstar.le
  unfold AnalyticTranslation.holomorphicError
  linarith

#print axioms actual_error_exp
#print axioms holomorphicError_le

end LogarithmExtension.CompatibleLog
