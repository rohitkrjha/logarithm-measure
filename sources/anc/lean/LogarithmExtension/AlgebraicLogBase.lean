import LogarithmExtension.NumberFieldNorm
import LogarithmExtension.AnalyticTranslation

/-! A positive real algebraic base presented in a number field, with the
degree, integral denominator, and conjugate growth constants explicit.
No irrationality-exponent conclusion is assumed by this data structure. -/

noncomputable section
namespace LogarithmExtension.AlgebraicLog

structure Base where
  carrier : Type
  [field : Field carrier]
  [numberField : NumberField carrier]
  element : carrier
  embedding : carrier →ₐ[ℚ] ℂ
  value : ℝ
  embedding_eq_value : embedding element = (value : ℂ)
  value_pos : 0 < value
  value_ne_one : value ≠ 1

attribute [instance] Base.field Base.numberField

namespace Base
variable (r : Base)

def complexValue : ℂ := r.embedding r.element
def logValue : ℝ := Real.log r.value
def degreeNat : ℕ := Module.finrank ℚ r.carrier
def degree : ℝ := r.degreeNat
def radius : ℝ := 100 * (1 + |r.logValue|)
def denominator : ℕ :=
  (NumberFieldArithmetic.exists_positive_integral_denominator r.element).choose
def denominatorCost : ℝ := Real.log (r.denominator : ℝ)
def conjugateSize : ℝ := max 1 (NumberField.house r.element)
def conjugateCost : ℝ := Real.log r.conjugateSize
def slopeSize : ℝ := |r.logValue| + 1

theorem complexValue_eq : r.complexValue = (r.value : ℂ) := r.embedding_eq_value

theorem complexValue_ne_zero : r.complexValue ≠ 0 := by
  rw [r.complexValue_eq]
  exact_mod_cast r.value_pos.ne'

theorem logValue_ne_zero : r.logValue ≠ 0 := by
  intro h
  exact r.value_ne_one (Real.eq_one_of_pos_of_log_eq_zero r.value_pos h)

theorem exp_logValue : Complex.exp (r.logValue : ℂ) = r.complexValue := by
  rw [← Complex.ofReal_exp, logValue, Real.exp_log r.value_pos, r.complexValue_eq]

theorem degreeNat_pos : 0 < r.degreeNat := Module.finrank_pos

theorem degree_ge_one : 1 ≤ r.degree := by
  change (1 : ℝ) ≤ (r.degreeNat : ℝ)
  exact_mod_cast r.degreeNat_pos

theorem degree_pos : 0 < r.degree := lt_of_lt_of_le zero_lt_one r.degree_ge_one

theorem radius_ge : 100 ≤ r.radius := by
  unfold radius
  nlinarith [abs_nonneg r.logValue]

theorem radius_pos : 0 < r.radius := lt_of_lt_of_le (by norm_num) r.radius_ge

theorem radius_eq : AnalyticTranslation.radiusFactor (r.logValue : ℂ) = r.radius := by
  simp only [AnalyticTranslation.radiusFactor, radius, Complex.norm_real, Real.norm_eq_abs]

theorem denominator_pos : 0 < r.denominator :=
  (NumberFieldArithmetic.exists_positive_integral_denominator r.element).choose_spec.1

theorem denominator_integral : IsIntegral ℤ ((r.denominator : r.carrier) * r.element) :=
  (NumberFieldArithmetic.exists_positive_integral_denominator r.element).choose_spec.2

theorem denominatorCost_nonneg : 0 ≤ r.denominatorCost := by
  apply Real.log_nonneg
  exact_mod_cast r.denominator_pos

theorem conjugateSize_ge_one : 1 ≤ r.conjugateSize := le_max_left _ _

theorem norm_embedding_le_conjugateSize (σ : r.carrier →ₐ[ℚ] ℂ) :
    ‖σ r.element‖ ≤ r.conjugateSize :=
  (NumberField.norm_embedding_le_house r.element σ.toRingHom).trans (le_max_right _ _)

theorem conjugateCost_nonneg : 0 ≤ r.conjugateCost := Real.log_nonneg r.conjugateSize_ge_one

theorem slopeSize_ge_one : 1 ≤ r.slopeSize := by
  unfold slopeSize
  linarith [abs_nonneg r.logValue]

/-- Every positive real algebraic base other than one has such a model. -/
def ofAlgebraic (α : ℝ) (hα : IsAlgebraic ℚ α) (hpos : 0 < α) (hne : α ≠ 1) : Base := by
  let K := IntermediateField.adjoin ℚ ({α} : Set ℝ)
  letI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hα.isIntegral
  letI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  exact {
    carrier := K
    element := IntermediateField.AdjoinSimple.gen ℚ α
    embedding := Complex.ofRealHom.toRatAlgHom.comp (IntermediateField.val K)
    value := α
    embedding_eq_value := rfl
    value_pos := hpos
    value_ne_one := hne
  }

@[simp] theorem ofAlgebraic_value (α : ℝ) (hα : IsAlgebraic ℚ α) (hpos : 0 < α) (hne : α ≠ 1) :
    (ofAlgebraic α hα hpos hne).value = α := rfl

end Base
end LogarithmExtension.AlgebraicLog
