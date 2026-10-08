import LogarithmExtension.RationalLogMain
import LogarithmExtension.RationalAffine

/-! Exponent two for all positive real numbers with a nontrivial rational
positive integer power, not just for rational bases themselves. -/
namespace LogarithmExtension

theorem rationalPowerLog_eventual_lower_bound
    (x : ℝ) (_hx : 0 < x) (n : ℕ) (hn : 0 < n)
    (r : ℚ) (hr : 0 < r) (hr1 : r ≠ 1) (hpower : x ^ n = (r : ℝ)) :
    EventualLowerBound (Real.log x) 2 := by
  have hlog : Real.log (r : ℝ) = (n : ℝ) * Real.log x := by
    rw [← hpower, Real.log_pow]
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hb := (rationalLog_eventual_lower_bound r hr hr1).rat_mul
    ((n : ℚ)⁻¹) (inv_ne_zero hnQ)
  have heq : (((n : ℚ)⁻¹ : ℚ) : ℝ) * Real.log (r : ℝ) = Real.log x := by
    rw [Rat.cast_inv, Rat.cast_natCast, hlog, ← mul_assoc, inv_mul_cancel₀ hnR, one_mul]
  rwa [heq] at hb

theorem rationalPowerLog_irrationalityExponent_eq_two
    (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 0 < n)
    (r : ℚ) (hr : 0 < r) (hr1 : r ≠ 1) (hpower : x ^ n = (r : ℝ)) :
    OAI.PiExponent.irrationalityExponent (Real.log x) = 2 :=
  irrationalityExponent_eq_two
    (rationalPowerLog_eventual_lower_bound x hx n hn r hr hr1 hpower)

theorem log_sqrt_two_irrationalityExponent_eq_two :
    OAI.PiExponent.irrationalityExponent (Real.log (Real.sqrt 2)) = 2 := by
  apply rationalPowerLog_irrationalityExponent_eq_two (Real.sqrt 2)
    (Real.sqrt_pos.mpr (by norm_num)) 2 (by norm_num) 2 (by norm_num) (by norm_num)
  norm_num [Real.sq_sqrt]

#print axioms rationalPowerLog_irrationalityExponent_eq_two

end LogarithmExtension

