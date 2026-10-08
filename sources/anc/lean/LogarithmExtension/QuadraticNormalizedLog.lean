import LogarithmExtension.CompatibleLogMain

/-! Quadratic norm-one logarithms, normalized by the square-root slope.
This proves exponent two for log(a+b*sqrt(D))/sqrt(D), not for the
unnormalized logarithm. The field and all compatible embeddings are built. -/

noncomputable section
namespace LogarithmExtension

theorem quadraticNormalizedLog_irrationalityExponent_eq_two
    (a b D : ℚ) (hD : 0 < D) (hnorm : a ^ 2 - b ^ 2 * D = 1)
    (halpha : 1 < (a : ℝ) + (b : ℝ) * Real.sqrt (D : ℝ)) :
    OAI.PiExponent.irrationalityExponent
      (Real.log ((a : ℝ) + (b : ℝ) * Real.sqrt (D : ℝ)) / Real.sqrt (D : ℝ)) = 2 := by
  let delta : ℝ := Real.sqrt (D : ℝ)
  let alpha : ℝ := (a : ℝ) + (b : ℝ) * delta
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hdelta : 0 < delta := Real.sqrt_pos.mpr hDreal
  have hdelta_sq : delta ^ 2 = (D : ℝ) := Real.sq_sqrt hDreal.le
  have hdelta_integral : IsIntegral ℚ delta := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hdelta_sq]
    exact isIntegral_algebraMap
  let K := IntermediateField.adjoin ℚ ({delta} : Set ℝ)
  let : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hdelta_integral
  let : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  let gamma : K := IntermediateField.AdjoinSimple.gen ℚ delta
  have hgamma_sq : gamma ^ 2 = (D : K) := by
    apply Subtype.ext
    exact hdelta_sq
  have hgamma : gamma ≠ 0 := by
    intro h
    exact hdelta.ne' (congrArg (fun z : K => (z : ℝ)) h)
  have halpha_pos : 0 < alpha := zero_lt_one.trans halpha
  have hx : Real.log alpha / delta ≠ 0 :=
    div_ne_zero (Real.log_pos halpha).ne' hdelta.ne'
  have hinverse : (alpha : ℂ)⁻¹ = (a : ℂ) - (b : ℂ) * (delta : ℂ) := by
    apply inv_eq_of_mul_eq_one_right
    have hn : (a : ℝ) ^ 2 - (b : ℝ) ^ 2 * (D : ℝ) = 1 := by exact_mod_cast hnorm
    have hr : alpha * ((a : ℝ) - (b : ℝ) * delta) = 1 := by
      dsimp only [alpha]
      nlinarith [hdelta_sq]
    exact_mod_cast hr
  have hexp : Complex.exp ((delta : ℂ) * ((Real.log alpha / delta : ℝ) : ℂ)) =
      (alpha : ℂ) := by
    have he : (delta : ℂ) * ((Real.log alpha / delta : ℝ) : ℂ) =
        (Real.log alpha : ℂ) := by
      have hdc : (delta : ℂ) ≠ 0 := by exact_mod_cast hdelta.ne'
      push_cast
      field_simp
    rw [he, ← Complex.ofReal_exp, Real.exp_log halpha_pos]
  have hexp_neg : Complex.exp (-(delta : ℂ) * ((Real.log alpha / delta : ℝ) : ℂ)) =
      (a : ℂ) - (b : ℂ) * (delta : ℂ) := by
    rw [neg_mul, Complex.exp_neg, hexp, hinverse]
  apply CompatibleLog.all_embeddings_irrationalityExponent_eq_two K gamma
    ((a : K) + (b : K) * gamma) (Real.log alpha / delta) hgamma hx
  intro sigma
  have hsquare : (sigma gamma) ^ 2 = (delta : ℂ) ^ 2 := by
    rw [← map_pow, hgamma_sq, map_ratCast]
    exact_mod_cast hdelta_sq.symm
  rcases eq_or_eq_neg_of_sq_eq_sq (sigma gamma) (delta : ℂ) hsquare with hs | hs
  · simpa only [map_add, map_mul, map_ratCast, hs, alpha, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_ratCast] using hexp
  · simpa only [map_add, map_mul, map_ratCast, hs, mul_neg, ← sub_eq_add_neg]
      using hexp_neg

theorem log_three_add_two_sqrt_two_normalized_irrationalityExponent_eq_two :
    OAI.PiExponent.irrationalityExponent
      (Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2) = 2 := by
  have h := quadraticNormalizedLog_irrationalityExponent_eq_two 3 2 2
    (by norm_num) (by norm_num) (by norm_num; nlinarith [Real.sqrt_nonneg (2 : ℝ)])
  simpa using h

#print axioms quadraticNormalizedLog_irrationalityExponent_eq_two
#print axioms log_three_add_two_sqrt_two_normalized_irrationalityExponent_eq_two

end LogarithmExtension
