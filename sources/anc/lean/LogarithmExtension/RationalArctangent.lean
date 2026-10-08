import LogarithmExtension.CompatibleLogMain
import Mathlib.Analysis.Complex.IsIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-! Exponent two for every nonzero rational arctangent, using the full
compatible-embedding theorem over Q(i), including root-of-unity values. -/

noncomputable section
namespace LogarithmExtension

theorem exp_twice_I_arctan (r : ℝ) :
    Complex.exp (2 * Complex.I * (Real.arctan r : ℂ)) =
      (1 + Complex.I * (r : ℂ)) / (1 - Complex.I * (r : ℂ)) := by
  have hplus : (1 : ℂ) + (r : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
  have hminus : (1 : ℂ) - (r : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
  rw [Complex.ofReal_arctan, Complex.arctan]
  have he (z : ℂ) : 2 * Complex.I * (-Complex.I / 2 * z) = z := by
    calc
      _ = -(Complex.I * Complex.I) * z := by ring
      _ = z := by rw [Complex.I_mul_I]; ring
  rw [he, Complex.exp_log (div_ne_zero hplus hminus)]
  congr 2 <;> ring

theorem exp_neg_twice_I_arctan (r : ℝ) :
    Complex.exp (2 * (-Complex.I) * (Real.arctan r : ℂ)) =
      (1 + (-Complex.I) * (r : ℂ)) / (1 - (-Complex.I) * (r : ℂ)) := by
  have h := congrArg (starRingEnd ℂ) (exp_twice_I_arctan r)
  simpa only [← Complex.exp_conj, map_mul, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal, map_div₀, map_add, map_one, map_sub] using h

theorem rationalArctan_irrationalityExponent_eq_two (r : ℚ) (hr : r ≠ 0) :
    OAI.PiExponent.irrationalityExponent (Real.arctan (r : ℝ)) = 2 := by
  let K := IntermediateField.adjoin ℚ ({Complex.I} : Set ℂ)
  let : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Complex.isIntegral_I ℚ)
  let : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  let ii : K := IntermediateField.AdjoinSimple.gen ℚ Complex.I
  have hii : ii ^ 2 = -1 := by
    apply Subtype.ext
    exact Complex.I_sq
  have hiine : ii ≠ 0 := by
    intro h
    have hI : Complex.I = 0 := congrArg (fun z : K => (z : ℂ)) h
    exact Complex.I_ne_zero hI
  have hx : Real.arctan (r : ℝ) ≠ 0 := by
    intro h
    exact hr (by exact_mod_cast Real.arctan_eq_zero_iff.mp h)
  apply CompatibleLog.all_embeddings_irrationalityExponent_eq_two K
    (2 * ii) ((1 + ii * (r : K)) / (1 - ii * (r : K))) (Real.arctan (r : ℝ))
    (mul_ne_zero (by norm_num) hiine) hx
  intro sigma
  have hsquare : (sigma ii) ^ 2 = Complex.I ^ 2 := by
    rw [← map_pow, hii, map_neg, map_one, Complex.I_sq]
  rcases eq_or_eq_neg_of_sq_eq_sq (sigma ii) Complex.I hsquare with hs | hs
  · simpa only [map_mul, map_ofNat, map_div₀, map_add, map_one, map_sub,
      map_ratCast, hs, Complex.ofReal_ratCast] using exp_twice_I_arctan (r : ℝ)
  · simpa only [map_mul, map_ofNat, map_div₀, map_add, map_one, map_sub,
      map_ratCast, hs, Complex.ofReal_ratCast] using exp_neg_twice_I_arctan (r : ℝ)

/-- This specialization exercises the root-of-unity branch (xi=i). -/
theorem arctan_one_irrationalityExponent_eq_two :
    OAI.PiExponent.irrationalityExponent (Real.arctan 1) = 2 := by
  simpa using rationalArctan_irrationalityExponent_eq_two 1 one_ne_zero

#print axioms rationalArctan_irrationalityExponent_eq_two
#print axioms arctan_one_irrationalityExponent_eq_two

end LogarithmExtension
