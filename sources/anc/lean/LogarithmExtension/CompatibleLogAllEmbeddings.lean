import LogarithmExtension.CompatibleLogAnalyticAggregate
import LogarithmExtension.ConjugateAnalyticBound

/-! Sum of the compatible analytic estimate and the direct estimates at
every other embedding, for the same selected number-field determinant. -/

noncomputable section
namespace LogarithmExtension.CompatibleLog.AllEmbeddings

open OAI OAI.PiExponent Filter
open scoped BigOperators Topology
open DeterminantContradiction LiteralAnalytic

variable {base : Base} {nu : ℝ}

def directError (d : FixedData base nu) : ℝ :=
  (base.conjugateCost + Real.log (3 / 2)) * (d.K : ℝ) / (d.w0 : ℝ) +
    Real.log (2 * ((d.K : ℝ) * base.slopeSize + 2)) / d.wstar + Real.log 2 / (d.v0 : ℝ)

theorem directError_nonneg (d : FixedData base nu) : 0 ≤ directError d := by
  have hl : 0 ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hs : 0 ≤ base.slopeSize := zero_le_one.trans base.slopeSize_ge_one
  have hb : 0 ≤ Real.log (2 * ((d.K : ℝ) * base.slopeSize + 2)) := by
    apply Real.log_nonneg
    nlinarith [mul_nonneg (Nat.cast_nonneg d.K) hs]
  unfold directError
  exact add_nonneg (add_nonneg
    (div_nonneg (mul_nonneg (add_nonneg base.conjugateCost_nonneg hl) (Nat.cast_nonneg _)) d.w0_pos.le)
    (div_nonneg hb d.wstar_pos.le)) (div_nonneg h2 d.v0_pos.le)

theorem scaledCenter_norm_le (d : FixedData base nu) (hnu : 0 ≤ nu)
    (σ : base.carrier →ₐ[ℚ] ℂ) (i : Fin d.m) :
    ‖MatrixArithmetic.scaledCenters base σ (finiteNumerators d) (finiteDenominators d) i‖ ≤
      base.slopeSize := by
  have hq : 1 ≤ (finiteDenominators d i : ℝ) := by
    exact_mod_cast (show 1 ≤ finiteDenominators d i from (by decide : 1 ≤ 2).trans
      (finiteDenominators_two_le d i))
  have he : |base.value - (finiteNumerators d i : ℝ) / (finiteDenominators d i : ℝ)| ≤ 1 :=
    (d.approximations i.val).2.2.trans
      (Real.rpow_le_one_of_one_le_of_nonpos hq (neg_nonpos.mpr hnu))
  have hr : |(finiteNumerators d i : ℝ) / (finiteDenominators d i : ℝ)| ≤ |base.value| + 1 := by
    calc
      _ = |base.value - (base.value -
          (finiteNumerators d i : ℝ) / (finiteDenominators d i : ℝ))| := by congr 1; ring
      _ ≤ |base.value| + |base.value -
          (finiteNumerators d i : ℝ) / (finiteDenominators d i : ℝ)| := abs_sub _ _
      _ ≤ _ := by linarith
  have hc : MatrixArithmetic.scaledCenters base σ (finiteNumerators d) (finiteDenominators d) i =
      σ base.slope * (((finiteNumerators d i : ℝ) / (finiteDenominators d i : ℝ) : ℝ) : ℂ) := by
    simp only [MatrixArithmetic.scaledCenters, Complex.ofReal_div,
      Complex.ofReal_intCast, Complex.ofReal_natCast, mul_div_assoc]
  rw [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (base.norm_slope_le_gammaSize σ) hr (abs_nonneg _) base.gammaSize_pos.le

theorem conjugateError_le_directError (d : FixedData base nu) (σ : base.carrier →ₐ[ℚ] ℂ) :
    ConjugateAnalytic.conjugateError (σ base.element) base.slopeSize d.K d.w0 d.wstar d.v0 ≤
      directError d := by
  have hnorm : max 1 ‖σ base.element‖ ≤ base.conjugateSize :=
    max_le base.conjugateSize_ge_one (base.norm_embedding_le_conjugateSize σ)
  have hl : Real.log (max 1 ‖σ base.element‖) ≤ base.conjugateCost :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hnorm
  have hK : (1 : ℝ) ≤ d.K := by exact_mod_cast d.K_pos
  have hlog : 0 ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
  have he : (d.K : ℝ) * Real.log (max 1 ‖σ base.element‖) + Real.log (3 / 2) ≤
      (base.conjugateCost + Real.log (3 / 2)) * (d.K : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg d.K),
      mul_le_mul_of_nonneg_right hK hlog]
  unfold ConjugateAnalytic.conjugateError directError
  linarith [div_le_div_of_nonneg_right he d.w0_pos.le]

theorem norm_conjugate_entry_le (d : FixedData base nu) (hnu : 0 ≤ nu)
    (σ : base.carrier →ₐ[ℚ] ℂ) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (ρ τ : Row d H) :
    ‖MatrixArithmetic.selectedMinorAt base σ d.K d.w0 d.v0 d.base.theta d.F0 H
        (finiteNumerators d) (finiteDenominators d) selection ρ τ‖ ≤
      Real.exp (H * directError d) := by
  have hh := ConjugateAnalytic.norm_matrixEntry_exp_le (σ base.element)
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (MatrixArithmetic.scaledCenters base σ (finiteNumerators d) (finiteDenominators d))
    base.slopeSize (scaledCenter_norm_le d hnu σ)
    (zero_le_one.trans base.slopeSize_ge_one) ρ.1.isLt.le
    (ρ.2.1 0) ((selection τ).1 0) (fun i => (selection τ).1 i.succ)
    (fun i => ρ.2.1 i.succ) (fixedWeights d) H d.w0 d.wstar d.v0
    d.w0_pos d.wstar_pos (fixedWeights_lower d)
    (InterpolationMatrix.column_weight_le d.w0_pos (fixedWeights_pos d) (selection τ)) (rowOrder_le d ρ)
  exact hh.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (conjugateError_le_directError d σ) hH.le))

theorem conjugate_normalized_log_bound (d : FixedData base nu) (hnu : 0 ≤ nu)
    (σ : base.carrier →ₐ[ℚ] ℂ) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (hne : (actualMinor d H selection).det ≠ 0) :
    Real.log ‖σ (fieldMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H) ≤
      directError d + Real.log (actualRowCount d H : ℝ) / H := by
  have he := MatrixArithmetic.map_fieldSelectedMinor_det base σ d.K d.w0 d.v0 d.base.theta d.F0 H
    (finiteNumerators d) (finiteDenominators d) selection
  have hdet : (MatrixArithmetic.selectedMinorAt base σ d.K d.w0 d.v0 d.base.theta d.F0 H
      (finiteNumerators d) (finiteDenominators d) selection).det ≠ 0 := by
    rw [← he]
    exact (map_ne_zero σ).mpr (fieldMinor_det_ne_zero d H selection hne)
  have hh := ConjugateAnalytic.normalized_log_det_le
    (MatrixArithmetic.selectedMinorAt base σ d.K d.w0 d.v0 d.base.theta d.F0 H
      (finiteNumerators d) (finiteDenominators d) selection)
    (directError d) H hH (actualRowCount_pos d hH) hdet
    (norm_conjugate_entry_le d hnu σ hH selection)
  rw [← he] at hh
  exact hh

def allEmbeddingRemainder (d : FixedData base nu) (H : ℝ) : ℝ :=
  analyticRemainder d H + base.ratio * (Real.log (actualRowCount d H : ℝ) / H)

theorem actual_norm_analytic_bound (d : FixedData base nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H)
    (hne : (actualMinor d H selection).det ≠ 0) :
    normLog d H selection ≤ d.analyticError + allEmbeddingRemainder d H +
      max (-collisionRate d H) (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)) := by
  classical
  let z : (base.carrier →ₐ[ℚ] ℂ) → ℝ := fun σ =>
    Real.log ‖σ (fieldMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H)
  let U : ℝ := directError d + Real.log (actualRowCount d H : ℝ) / H
  let V : ℝ := d.goodAnalyticError + analyticRemainder d H +
    max (-collisionRate d H) (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H))
  have hU : 0 ≤ U := by
    apply add_nonneg (directError_nonneg d)
    apply div_nonneg _ hH.le
    apply Real.log_nonneg
    exact_mod_cast actualRowCount_pos d hH
  have hcard : ((base.goodᶜ).card : ℝ) ≤ base.degree := by
    calc
      _ ≤ (Fintype.card (base.carrier →ₐ[ℚ] ℂ) : ℝ) := by
        exact_mod_cast Finset.card_le_univ base.goodᶜ
      _ = _ := by simp [Base.degree, Base.degreeNat]
  have hother : (∑ σ ∈ base.goodᶜ, z σ) ≤ base.degree * U := by
    calc
      _ ≤ ∑ _σ ∈ base.goodᶜ, U :=
        Finset.sum_le_sum (fun σ _ => conjugate_normalized_log_bound d hnu σ hH selection hne)
      _ = ((base.goodᶜ).card : ℝ) * U := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hU
  have hgood : (∑ σ ∈ base.good, z σ) ≤ base.goodCount * V := by
    have hb : ∀ σ ∈ base.good, z σ ≤ V := by
      intro σ hσ
      dsimp only [z, V]
      rw [map_fieldMinor_det d σ H selection]
      exact actual_minor_analytic_bound d σ hσ hnu hH selection
        (actualMinorAt_det_ne_zero d σ H selection hne)
    simpa only [Finset.sum_const, nsmul_eq_mul, Base.goodCount] using Finset.sum_le_sum hb
  have htotal : (∑ σ, z σ) ≤ base.goodCount * V + base.degree * U := by
    rw [← Finset.sum_add_sum_compl base.good z]
    exact add_le_add hgood hother
  have hnorm : normLog d H selection = (∑ σ, z σ) / base.goodCount := by
    unfold normLog
    dsimp only [z]
    rw [← Finset.sum_div]
    dsimp only [actualRowCount]
    ring
  rw [hnorm]
  apply (div_le_div_of_nonneg_right htotal base.goodCount_pos.le).trans
  apply le_of_eq
  dsimp only [V, U]
  unfold AdmissibleParameters.analyticError AdmissibleParameters.goodAnalyticError
    AdmissibleParameters.otherEmbeddingError allEmbeddingRemainder directError Base.ratio
  field_simp [base.goodCount_pos.ne']
  ring

theorem tendsto_allEmbeddingRemainder (d : FixedData base nu) :
    Tendsto (allEmbeddingRemainder d) atTop (𝓝 0) := by
  have hv : 0 < d.v0 := by exact_mod_cast d.v0_pos
  have ht : 0 < d.base.theta := by exact_mod_cast d.base.theta_pos
  have hcount := MatrixCounting.tendsto_rowCount_normalized d.K d.v0 d.base.theta
    (finiteDenominators d) hv ht (finiteDenominators_two_le d)
  have hlead : 0 < (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m + 1).factorial : ℝ) * (d.v0 : ℝ) *
        ∏ i, MatrixArithmetic.logWeights (finiteDenominators d) i) := by
    apply div_pos
    · exact mul_pos (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one d.K_pos)
        (pow_pos d.base.theta_pos _)
    · exact mul_pos (mul_pos (by positivity) d.v0_pos)
        (Finset.prod_pos (fun i _ => fixedWeights_pos d i))
  have hlog := tendsto_log_div_of_normalized_pow
    (f := fun H => (actualRowCount d H : ℝ)) hcount hlead
  have hh := (tendsto_analyticRemainder d).add (hlog.const_mul base.ratio)
  change Tendsto (fun H : ℝ => analyticRemainder d H +
    base.ratio * (Real.log (actualRowCount d H : ℝ) / H)) atTop (𝓝 0)
  simpa only [mul_zero, add_zero] using hh

theorem analyticAggregate (base : Base) : AnalyticAggregateStatement base := by
  intro nu hnu d
  refine ⟨allEmbeddingRemainder d, tendsto_allEmbeddingRemainder d, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  intro selection hne
  exact actual_norm_analytic_bound d (by nlinarith [base.ratio_pos]) hH selection hne

#print axioms analyticAggregate

end LogarithmExtension.CompatibleLog.AllEmbeddings
