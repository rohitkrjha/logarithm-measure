import LogarithmExtension.AlgebraicLogBase

/-!
# Data for the full compatible-embedding generalization

The real target is any nonzero x for which exp(sigma(gamma) * x) = sigma(xi)
at a nonempty set of embeddings of a number field containing gamma and xi.
This structure contains no approximation, rank, or determinant hypothesis.
The degree/count ratio and every fixed growth/denominator constant are explicit.
-/

noncomputable section
namespace LogarithmExtension.CompatibleLog

structure Base where
  carrier : Type
  [field : Field carrier]
  [numberField : NumberField carrier]
  element : carrier
  slope : carrier
  slope_ne_zero : slope ≠ 0
  value : ℝ
  value_ne_zero : value ≠ 0
  good : Finset (carrier →ₐ[ℚ] ℂ)
  good_nonempty : good.Nonempty
  compatible : ∀ σ ∈ good, Complex.exp (σ slope * (value : ℂ)) = σ element

attribute [instance] Base.field Base.numberField

namespace Base
variable (r : Base)

def degreeNat : ℕ := Module.finrank ℚ r.carrier
def degree : ℝ := r.degreeNat
def goodCount : ℝ := r.good.card
def ratio : ℝ := r.degree / r.goodCount
def embedding : r.carrier →ₐ[ℚ] ℂ := r.good_nonempty.choose
def period (σ : r.carrier →ₐ[ℚ] ℂ) : ℂ := σ r.slope * (r.value : ℂ)
def denominator : ℕ :=
  (NumberFieldArithmetic.exists_positive_integral_denominator r.element).choose
def slopeDenominator : ℕ :=
  (NumberFieldArithmetic.exists_positive_integral_denominator r.slope).choose
def denominatorCost : ℝ := Real.log r.denominator
def slopeDenominatorCost : ℝ := Real.log r.slopeDenominator
def conjugateSize : ℝ := max 1 (NumberField.house r.element)
def conjugateCost : ℝ := Real.log r.conjugateSize
def gammaSize : ℝ := max 1 (NumberField.house r.slope)
def radius : ℝ := 100 * (1 + r.gammaSize * |r.value|)
def slopeSize : ℝ := r.gammaSize * (|r.value| + 1)

theorem embedding_mem : r.embedding ∈ r.good := r.good_nonempty.choose_spec

theorem element_ne_zero : r.element ≠ 0 := by
  intro h
  have he := r.compatible r.embedding r.embedding_mem
  rw [h, map_zero] at he
  exact Complex.exp_ne_zero _ he

theorem degree_pos : 0 < r.degree := by
  change (0 : ℝ) < (Module.finrank ℚ r.carrier : ℝ)
  exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ r.carrier)

theorem goodCount_pos : 0 < r.goodCount := by
  change (0 : ℝ) < (r.good.card : ℝ)
  exact_mod_cast r.good_nonempty.card_pos

theorem goodCount_le_degree : r.goodCount ≤ r.degree := by
  have h := Finset.card_le_univ r.good
  simpa [goodCount, degree, degreeNat] using (show (r.good.card : ℝ) ≤
    (Fintype.card (r.carrier →ₐ[ℚ] ℂ) : ℝ) by exact_mod_cast h)

theorem ratio_ge_one : 1 ≤ r.ratio :=
  (one_le_div r.goodCount_pos).mpr r.goodCount_le_degree

theorem ratio_pos : 0 < r.ratio := lt_of_lt_of_le zero_lt_one r.ratio_ge_one

theorem denominator_pos : 0 < r.denominator :=
  (NumberFieldArithmetic.exists_positive_integral_denominator r.element).choose_spec.1

theorem denominator_integral : IsIntegral ℤ ((r.denominator : r.carrier) * r.element) :=
  (NumberFieldArithmetic.exists_positive_integral_denominator r.element).choose_spec.2

theorem slopeDenominator_pos : 0 < r.slopeDenominator :=
  (NumberFieldArithmetic.exists_positive_integral_denominator r.slope).choose_spec.1

theorem slopeDenominator_integral :
    IsIntegral ℤ ((r.slopeDenominator : r.carrier) * r.slope) :=
  (NumberFieldArithmetic.exists_positive_integral_denominator r.slope).choose_spec.2

theorem denominatorCost_nonneg : 0 ≤ r.denominatorCost :=
  Real.log_nonneg (by exact_mod_cast r.denominator_pos)

theorem slopeDenominatorCost_nonneg : 0 ≤ r.slopeDenominatorCost :=
  Real.log_nonneg (by exact_mod_cast r.slopeDenominator_pos)

theorem conjugateSize_ge_one : 1 ≤ r.conjugateSize := le_max_left _ _

theorem norm_embedding_le_conjugateSize (σ : r.carrier →ₐ[ℚ] ℂ) :
    ‖σ r.element‖ ≤ r.conjugateSize :=
  (NumberField.norm_embedding_le_house r.element σ.toRingHom).trans (le_max_right _ _)

theorem conjugateCost_nonneg : 0 ≤ r.conjugateCost := Real.log_nonneg r.conjugateSize_ge_one

theorem gammaSize_ge_one : 1 ≤ r.gammaSize := le_max_left _ _

theorem gammaSize_pos : 0 < r.gammaSize := lt_of_lt_of_le zero_lt_one r.gammaSize_ge_one

theorem norm_slope_le_gammaSize (σ : r.carrier →ₐ[ℚ] ℂ) : ‖σ r.slope‖ ≤ r.gammaSize :=
  (NumberField.norm_embedding_le_house r.slope σ.toRingHom).trans (le_max_right _ _)

theorem norm_period_le (σ : r.carrier →ₐ[ℚ] ℂ) : ‖r.period σ‖ ≤ r.gammaSize * |r.value| := by
  rw [period, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (r.norm_slope_le_gammaSize σ) (abs_nonneg _)

theorem radius_ge : 100 ≤ r.radius := by
  unfold radius
  nlinarith [mul_nonneg r.gammaSize_pos.le (abs_nonneg r.value)]

theorem radius_pos : 0 < r.radius := lt_of_lt_of_le (by norm_num) r.radius_ge

theorem radiusFactor_le (σ : r.carrier →ₐ[ℚ] ℂ) :
    AnalyticTranslation.radiusFactor (r.period σ) ≤ r.radius := by
  unfold AnalyticTranslation.radiusFactor radius
  linarith [r.norm_period_le σ]

theorem slopeSize_ge_one : 1 ≤ r.slopeSize := by
  unfold slopeSize
  nlinarith [r.gammaSize_ge_one,
    mul_nonneg r.gammaSize_pos.le (abs_nonneg r.value)]

theorem period_ne_zero (σ : r.carrier →ₐ[ℚ] ℂ) : r.period σ ≠ 0 :=
  mul_ne_zero ((map_ne_zero σ).mpr r.slope_ne_zero)
    (by exact_mod_cast r.value_ne_zero)

theorem exp_period (σ : r.carrier →ₐ[ℚ] ℂ) (hσ : σ ∈ r.good) :
    Complex.exp (r.period σ) = σ r.element := r.compatible σ hσ

/-- Multiplying the slope and exponentiating the algebraic value preserves
every compatible embedding, and leaves x, d, s, and d/s unchanged. -/
def raiseExponent (n : ℕ) (hn : 0 < n) : Base where
  carrier := r.carrier
  element := r.element ^ n
  slope := (n : r.carrier) * r.slope
  slope_ne_zero := mul_ne_zero (by exact_mod_cast hn.ne') r.slope_ne_zero
  value := r.value
  value_ne_zero := r.value_ne_zero
  good := r.good
  good_nonempty := r.good_nonempty
  compatible := by
    intro σ hσ
    rw [map_mul, map_natCast, map_pow, mul_assoc, Complex.exp_nat_mul,
      r.compatible σ hσ]

@[simp] theorem raiseExponent_value (n : ℕ) (hn : 0 < n) :
    (r.raiseExponent n hn).value = r.value := rfl

@[simp] theorem raiseExponent_ratio (n : ℕ) (hn : 0 < n) :
    (r.raiseExponent n hn).ratio = r.ratio := rfl

theorem powers_injective_of_no_root
    (hroot : ¬ ∃ n : ℕ, 0 < n ∧ r.element ^ n = 1) :
    Function.Injective (fun n : ℕ => r.element ^ n) := by
  intro m n he
  change r.element ^ m = r.element ^ n at he
  wlog hle : m ≤ n generalizing m n
  · exact (this he.symm (by omega)).symm
  by_contra hne
  have hn : 0 < n - m := by omega
  apply hroot
  refine ⟨n - m, hn, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero m r.element_ne_zero)
  rw [← pow_add, Nat.add_sub_of_le hle, mul_one]
  exact he.symm

theorem embedding_powers_injective (hinj : Function.Injective (fun n : ℕ => r.element ^ n))
    (σ : r.carrier →ₐ[ℚ] ℂ) : Function.Injective (fun n : ℕ => (σ r.element) ^ n) := by
  intro m n he
  apply hinj
  apply σ.injective
  rw [map_pow, map_pow]
  exact he

/-- The root-of-unity reduction is unconditional. It reduces the full target
to distinct multiplicative centers or to the common fiber xi=1, not just to
the non-root-of-unity case. It does not assume either interpolation theorem. -/
theorem exists_normalized : ∃ b : Base, b.value = r.value ∧ b.ratio = r.ratio ∧
    (b.element = 1 ∨ Function.Injective (fun n : ℕ => b.element ^ n)) := by
  by_cases hroot : ∃ n : ℕ, 0 < n ∧ r.element ^ n = 1
  · obtain ⟨n, hn, he⟩ := hroot
    exact ⟨r.raiseExponent n hn, rfl, rfl, Or.inl he⟩
  · exact ⟨r, rfl, rfl, Or.inr (r.powers_injective_of_no_root hroot)⟩

end Base

#print axioms Base.exists_normalized
#print axioms Base.radiusFactor_le

end LogarithmExtension.CompatibleLog
