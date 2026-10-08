import Mathlib

/-!
# Number-field norm accounting for logarithmic determinants

All complex embeddings are included, with conjugate embeddings counted
separately. In particular, clearing a positive rational denominator has a
cost multiplied by the degree of the number field.
-/

noncomputable section
namespace LogarithmExtension.NumberFieldArithmetic

open scoped BigOperators NumberField

variable {F : Type*} [Field F] [NumberField F]

theorem prod_embedding_norm (z : F) :
    (∏ σ : F →ₐ[ℚ] ℂ, ‖σ z‖) = |(Algebra.norm ℚ z : ℝ)| := by
  have h := congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ z)
  simpa only [norm_prod, eq_ratCast, Complex.norm_ratCast] using h.symm

theorem one_le_prod_embedding_norm {z : F} (hz : IsIntegral ℤ z) (hne : z ≠ 0) :
    1 ≤ ∏ σ : F →ₐ[ℚ] ℂ, ‖σ z‖ := by
  rw [prod_embedding_norm]
  let a : 𝓞 F := ⟨z, hz⟩
  have ha : a ≠ 0 := by
    intro h
    exact hne (congrArg (fun a : 𝓞 F => (a : F)) h)
  change (1 : ℝ) ≤ |(Algebra.norm ℚ (a : F) : ℝ)|
  rw [← Algebra.coe_norm_int, Rat.cast_intCast, ← Int.cast_abs, ← Int.cast_one,
    Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)

theorem sum_log_embedding_norm_nonneg {z : F} (hz : IsIntegral ℤ z) (hne : z ≠ 0) :
    0 ≤ ∑ σ : F →ₐ[ℚ] ℂ, Real.log ‖σ z‖ := by
  have h := Real.log_nonneg (one_le_prod_embedding_norm hz hne)
  rw [Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hne))] at h
  exact h

/-- The full degree factor is retained in the denominator-clearing cost. -/
theorem cleared_element_log_bound (z : F) (S : ℚ) (hS : 0 < S) (hz : z ≠ 0)
    (hintegral : IsIntegral ℤ ((S : F) * z)) :
    -(Module.finrank ℚ F : ℝ) * Real.log (S : ℝ) ≤
      ∑ σ : F →ₐ[ℚ] ℂ, Real.log ‖σ z‖ := by
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have hSF : (S : F) ≠ 0 := by exact_mod_cast hS.ne'
  have h := sum_log_embedding_norm_nonneg hintegral (mul_ne_zero hSF hz)
  have he (σ : F →ₐ[ℚ] ℂ) :
      Real.log ‖σ ((S : F) * z)‖ = Real.log (S : ℝ) + Real.log ‖σ z‖ := by
    rw [map_mul, map_ratCast, norm_mul, Complex.norm_ratCast, abs_of_pos hSR,
      Real.log_mul hSR.ne' (norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hz))]
  simp only [he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at h
  have hcard : Fintype.card (F →ₐ[ℚ] ℂ) = Module.finrank ℚ F := by simp
  rw [hcard] at h
  linarith

theorem exists_positive_integral_denominator (z : F) :
    ∃ D : ℕ, 0 < D ∧ IsIntegral ℤ ((D : F) * z) := by
  refine ⟨Algebra.natDenominator z, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (IsAlgebraic.natDenominator_ne_zero
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (.of_finite ℚ z)))
  · simpa only [nsmul_eq_mul] using Algebra.isIntegral_natDenominator_smul z

/-- A nonzero determinant with integral row/column-scaled entries gives a
lower bound for the sum over *all* embeddings. -/
theorem cleared_matrix_log_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F) (r c : ι → ℚ) (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hentries : ∀ i j, IsIntegral ℤ ((r i : F) * ((c j : F) * A i j))) :
    -(Module.finrank ℚ F : ℝ) *
        ((∑ i, Real.log (r i : ℝ)) + ∑ j, Real.log (c j : ℝ)) ≤
      ∑ σ : F →ₐ[ℚ] ℂ, Real.log ‖σ A.det‖ := by
  classical
  let S : ℚ := (∏ i, r i) * ∏ j, c j
  have hS : 0 < S :=
    mul_pos (Finset.prod_pos (fun i _ => hr i)) (Finset.prod_pos (fun j _ => hc j))
  have hint := IsIntegral.det hentries
  change IsIntegral ℤ (Matrix.det (Matrix.of fun i j =>
    (r i : F) * ((c j : F) * A i j))) at hint
  erw [Matrix.det_mul_column (fun i => (r i : F))
    (Matrix.of fun i j => (c j : F) * A i j),
    Matrix.det_mul_row (fun j => (c j : F)) A] at hint
  have hscale : IsIntegral ℤ ((S : F) * A.det) := by
    simpa only [S, Rat.cast_mul, Rat.cast_prod, mul_assoc] using hint
  have h := cleared_element_log_bound A.det S hS hA hscale
  have hrR : ∀ i, (0 : ℝ) < r i := fun i => by exact_mod_cast hr i
  have hcR : ∀ i, (0 : ℝ) < c i := fun i => by exact_mod_cast hc i
  have hlog : Real.log (S : ℝ) =
      (∑ i, Real.log (r i : ℝ)) + ∑ j, Real.log (c j : ℝ) := by
    dsimp only [S]
    rw [Rat.cast_mul, Rat.cast_prod, Rat.cast_prod,
      Real.log_mul (Finset.prod_ne_zero_iff.mpr (fun i _ => (hrR i).ne'))
        (Finset.prod_ne_zero_iff.mpr (fun j _ => (hcR j).ne')),
      Real.log_prod (fun i _ => (hrR i).ne'), Real.log_prod (fun j _ => (hcR j).ne')]
  rwa [hlog] at h

theorem cleared_matrix_log_bound_with_denominator {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F) (r c : ι → ℚ) (D : ℚ)
    (hD : 0 < D) (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i) (hA : A.det ≠ 0)
    (hentries : ∀ i j, IsIntegral ℤ ((D : F) * (r i : F) * ((c j : F) * A i j))) :
    -(Module.finrank ℚ F : ℝ) *
        ((Fintype.card ι : ℝ) * Real.log (D : ℝ) +
          (∑ i, Real.log (r i : ℝ)) + ∑ j, Real.log (c j : ℝ)) ≤
      ∑ σ : F →ₐ[ℚ] ℂ, Real.log ‖σ A.det‖ := by
  have h := cleared_matrix_log_bound A (fun i => D * r i) c
    (fun i => mul_pos hD (hr i)) hc hA (by simpa using hentries)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hrR : ∀ i, (0 : ℝ) < r i := fun i => by exact_mod_cast hr i
  simp only [Rat.cast_mul, Real.log_mul hDR.ne' (hrR _).ne',
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  exact h

/-- Numerical normalization of the genuine number-field norm estimate. -/
theorem normalized_arithmetic_bound
    (d M H b E δ logD columnCost rowCost logAbsNorm : ℝ)
    (hd : 0 ≤ d) (hM : 0 < M) (hH : 0 < H)
    (hclear : -d * (M * logD + columnCost - rowCost) ≤ logAbsNorm)
    (hden : logD ≤ H * E) (hcol : columnCost ≤ M * H)
    (hrow : M * H * b - M * H * δ ≤ rowCost) :
    -d * (1 - b) - d * (E + δ) ≤ logAbsNorm / (M * H) := by
  apply (le_div_iff₀ (mul_pos hM hH)).mpr
  have hdD := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hden hM.le) hd
  have hdC := mul_le_mul_of_nonneg_left hcol hd
  have hdR := mul_le_mul_of_nonneg_left hrow hd
  nlinarith only [hclear, hdD, hdC, hdR]

#print axioms cleared_element_log_bound
#print axioms cleared_matrix_log_bound_with_denominator

end LogarithmExtension.NumberFieldArithmetic
