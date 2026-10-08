import LogarithmExtension.NumberFieldNorm
import LogarithmExtension.Basic
import OAI.NumberTheory.PiExponent.Approximation.Parameters

/-! Exact norm averaging over a chosen set of compatible embeddings. The
analytic inequalities remain explicit inputs here; this module does not
claim the final logarithm theorem. -/

noncomputable section
namespace LogarithmExtension.NumberFieldArithmetic

open scoped BigOperators NumberField

variable {F : Type*} [Field F] [NumberField F]

local instance : DecidableEq (F →ₐ[ℚ] ℂ) := Classical.decEq _

theorem norm_averaging_over_embeddings (z : F) (hz : z ≠ 0)
    (D : ℚ) (hD : 0 < D) (hintegral : IsIntegral ℤ ((D : F) * z))
    (M H cost good : ℝ) (hM : 0 < M) (hH : 0 < H)
    (hcost : Real.log (D : ℝ) / (M * H) ≤ cost)
    (S : Finset (F →ₐ[ℚ] ℂ)) (hS : S.Nonempty)
    (other : (F →ₐ[ℚ] ℂ) → ℝ)
    (hgood : ∀ σ ∈ S, Real.log ‖σ z‖ / (M * H) ≤ good)
    (hother : ∀ σ ∉ S, Real.log ‖σ z‖ / (M * H) ≤ other σ) :
    -((Module.finrank ℚ F : ℝ) / (S.card : ℝ)) * cost ≤
      good + (∑ σ ∈ Sᶜ, other σ) / (S.card : ℝ) := by
  classical
  have hMH := mul_pos hM hH
  have hdegree : (0 : ℝ) ≤ Module.finrank ℚ F := Nat.cast_nonneg _
  have hl := div_le_div_of_nonneg_right (cleared_element_log_bound z D hD hz hintegral) hMH.le
  have hlow : -(Module.finrank ℚ F : ℝ) * cost ≤
      ∑ σ : F →ₐ[ℚ] ℂ, Real.log ‖σ z‖ / (M * H) := by
    have hc := mul_le_mul_of_nonpos_left hcost (neg_nonpos.mpr hdegree)
    rw [Finset.sum_div] at hl
    have he : -(Module.finrank ℚ F : ℝ) * (Real.log (D : ℝ) / (M * H)) =
        (-(Module.finrank ℚ F : ℝ) * Real.log (D : ℝ)) / (M * H) := by ring
    rw [he] at hc
    exact hc.trans hl
  have hu : (∑ σ : F →ₐ[ℚ] ℂ, Real.log ‖σ z‖ / (M * H)) ≤
      (S.card : ℝ) * good + ∑ σ ∈ Sᶜ, other σ := by
    rw [← Finset.sum_add_sum_compl S (fun σ => Real.log ‖σ z‖ / (M * H))]
    apply add_le_add
    · simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hgood
    · apply Finset.sum_le_sum
      intro σ hσ
      exact hother σ (Finset.mem_compl.mp hσ)
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have h := div_le_div_of_nonneg_right (hlow.trans hu) hcard.le
  convert h using 1 <;> field_simp

/-- Dividing the approximation exponent by d/s is the exact numerical
translation of the norm cost; it is not an assumed irrationality bound. -/
theorem exists_parameters_above_twice_ratio (κ ν : ℝ) (hκ : 0 < κ) (hν : 2 * κ < ν) :
    ∃ P : OAI.PiExponent.Parameters (ν / κ),
      0 < ν * ((P.A : ℝ) * (1 - P.eta) - P.theta) - κ * (1 - P.theta) := by
  have hquot : 2 < ν / κ := (lt_div_iff₀ hκ).mpr hν
  obtain ⟨P⟩ := OAI.PiExponent.exists_parameters (ν / κ) hquot
  refine ⟨P, ?_⟩
  have h := mul_pos hκ P.gap_pos
  have he : κ * ((ν / κ) * ((P.A : ℝ) * (1 - P.eta) - P.theta) - (1 - P.theta)) =
      ν * ((P.A : ℝ) * (1 - P.eta) - P.theta) - κ * (1 - P.theta) := by
    field_simp
  rwa [he] at h

#print axioms norm_averaging_over_embeddings
#print axioms exists_parameters_above_twice_ratio

end LogarithmExtension.NumberFieldArithmetic
