import Mathlib
import LogarithmExtension.AlgebraicLogAdmissibleParameters
import OAI.NumberTheory.PiExponent.Approximation.Comparison
import LogarithmExtension.AlgebraicLogMatrixArithmetic
import OAI.NumberTheory.PiExponent.Approximation.MatrixCounting
import LogarithmExtension.Target

/-! Number-field logarithm determinant contradiction, adapted from upstream (Apache-2.0). -/
namespace LogarithmExtension
open OAI OAI.PiExponent

open Filter
open scoped Topology

namespace AlgebraicLog.DeterminantContradiction

variable {base : Base}

noncomputable def collisionConstant : ℝ := Real.log 2 / 4

theorem collisionConstant_pos : 0 < collisionConstant := by
  unfold collisionConstant
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

abbrev FixedData (base : Base) (nu : ℝ) := AdmissibleParameters base nu Arithmetic.lcmConstant collisionConstant

noncomputable def finiteNumerators {nu : ℝ} (d : FixedData base nu) : Fin d.m → ℤ :=
  fun i => d.p i.val

noncomputable def finiteDenominators {nu : ℝ} (d : FixedData base nu) : Fin d.m → ℕ :=
  fun i => d.q i.val

theorem finiteDenominators_two_le {nu : ℝ} (d : FixedData base nu) (i : Fin d.m) :
    2 ≤ finiteDenominators d i := (d.approximations i.val).1

theorem logWeights_eq {nu : ℝ} (d : FixedData base nu) (i : Fin d.m) :
    MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) :=
  (d.x_log i.val).symm

abbrev Row {nu : ℝ} (d : FixedData base nu) (H : ℝ) :=
  InterpolationMatrix.Row d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H

abbrev Column {nu : ℝ} (d : FixedData base nu) (H : ℝ) :=
  InterpolationMatrix.Column d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H

noncomputable def actualMatrix {nu : ℝ} (d : FixedData base nu) (H : ℝ) :
    Matrix (Row d H) (Column d H) ℂ :=
  MatrixArithmetic.matrix base d.K d.w0 d.v0 d.base.theta d.F0 H
    (finiteNumerators d) (finiteDenominators d)

noncomputable def actualMinor {nu : ℝ} (d : FixedData base nu) (H : ℝ)
    (selection : Row d H → Column d H) : Matrix (Row d H) (Row d H) ℂ :=
  MatrixArithmetic.selectedMinor base d.K d.w0 d.v0 d.base.theta d.F0 H
    (finiteNumerators d) (finiteDenominators d) selection

noncomputable def fieldMinor {nu : ℝ} (d : FixedData base nu) (H : ℝ)
    (selection : Row d H → Column d H) : Matrix (Row d H) (Row d H) base.carrier :=
  MatrixArithmetic.fieldSelectedMinor base d.K d.w0 d.v0 d.base.theta d.F0 H
    (finiteNumerators d) (finiteDenominators d) selection

theorem fieldMinor_det_ne_zero {nu : ℝ} (d : FixedData base nu) (H : ℝ)
    (selection : Row d H → Column d H)
    (hne : (actualMinor d H selection).det ≠ 0) :
    (fieldMinor d H selection).det ≠ 0 := by
  intro hzero
  have he := MatrixArithmetic.map_fieldSelectedMinor_det base base.embedding
    d.K d.w0 d.v0 d.base.theta d.F0 H (finiteNumerators d) (finiteDenominators d) selection
  change base.embedding (fieldMinor d H selection).det = (actualMinor d H selection).det at he
  rw [hzero, map_zero] at he
  exact hne he.symm

noncomputable def normLog {nu : ℝ} (d : FixedData base nu) (H : ℝ)
    (selection : Row d H → Column d H) : ℝ :=
  (∑ σ : base.carrier →ₐ[ℚ] ℂ, Real.log ‖σ (fieldMinor d H selection).det‖) /
    ((Fintype.card (Row d H) : ℝ) * H)

noncomputable def actualMean {nu : ℝ} (d : FixedData base nu) (H : ℝ) : ℝ :=
  MatrixArithmetic.meanRowWeight d.K d.v0 d.base.theta (finiteDenominators d) H

noncomputable def actualRowCount {nu : ℝ} (d : FixedData base nu) (H : ℝ) : ℕ :=
  Fintype.card (Row d H)

noncomputable def lowIndexCount {nu : ℝ} (d : FixedData base nu) (H : ℝ) : ℕ :=
  (realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d))
    ((d.base.A : ℝ) * H)).card

noncomputable def collisionRate {nu : ℝ} (d : FixedData base nu) (H : ℝ) : ℝ :=
  collisionConstant * d.base.eta ^ 2 * (actualRowCount d H : ℝ) /
    (H * (lowIndexCount d H : ℝ))

noncomputable def collisionLimit {nu : ℝ} (d : FixedData base nu) : ℝ :=
  collisionConstant *
    (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m))

theorem actual_minor_arithmetic_lower_bound {nu : ℝ} (d : FixedData base nu)
    (H : ℝ) (hH : 0 < H) (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    -base.degree * (1 - actualMean d H) - d.arithmeticError ≤
      normLog d H selection := by
  have hh := MatrixArithmetic.selectedMinor_arithmetic_lower_bound base
    (finiteNumerators d) (finiteDenominators d) (finiteDenominators_two_le d)
    (Nat.zero_lt_of_lt d.K_pos) d.w0_pos d.v0_pos d.base.theta_pos d.F0_pos.le hH
    d.wstar_pos (fun i => by rw [logWeights_eq]; exact d.wstar_lower i) selection
      (fieldMinor_det_ne_zero d H selection hdet)
  simpa only [fieldMinor, normLog, actualMean, actualRowCount,
    AdmissibleParameters.arithmeticError, logWeights_eq] using hh

theorem actualMean_bounds {nu : ℝ} (d : FixedData base nu) (H : ℝ) (hH : 0 < H) :
    0 ≤ actualMean d H ∧ actualMean d H ≤ (d.base.theta : ℝ) := by
  exact ⟨MatrixArithmetic.meanRowWeight_nonneg _ _ _ _ hH.le,
    MatrixArithmetic.meanRowWeight_le_theta (finiteDenominators d)
      (finiteDenominators_two_le d) (Nat.zero_lt_of_lt d.K_pos)
      d.v0_pos d.base.theta_pos hH⟩

def GlobalInterpolationStatement (base : Base) : Prop :=
  ∀ nu : ℝ, 2 * base.degree < nu → ∀ d : FixedData base nu,
    ∀ L : ℝ, ∃ H : ℝ, L ≤ H ∧ Function.Surjective (actualMatrix d H).mulVecLin

def CompatibleAnalyticStatement (base : Base) : Prop :=
  ∀ nu : ℝ, 2 * base.degree < nu → ∀ d : FixedData base nu,
    ∃ error : ℝ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ᶠ H : ℝ in atTop, ∀ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 →
        Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H) ≤
          d.goodAnalyticError + error H +
            max (-collisionRate d H)
              (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H))

def AnalyticAggregateStatement (base : Base) : Prop :=
  ∀ nu : ℝ, 2 * base.degree < nu → ∀ d : FixedData base nu,
    ∃ error : ℝ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ᶠ H : ℝ in atTop, ∀ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 →
        normLog d H selection ≤ d.analyticError + error H +
            max (-collisionRate d H)
              (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H))

theorem tendsto_collisionRate {nu : ℝ} (d : FixedData base nu) :
    Tendsto (collisionRate d) atTop (𝓝 (collisionLimit d)) := by
  have hv : 0 < d.v0 := by exact_mod_cast d.v0_pos
  have ht : 0 < d.base.theta := by exact_mod_cast d.base.theta_pos
  have hA : 0 < d.base.A := by exact_mod_cast d.base.A_pos
  have hh := MatrixCounting.tendsto_collisionRatio d.K d.v0 d.base.theta d.base.A
    (finiteDenominators d) hv ht hA (finiteDenominators_two_le d)
    collisionConstant d.base.eta
  have he : collisionConstant * d.base.eta ^ 2 * (d.K : ℝ) *
      (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m) =
        collisionLimit d := by
    unfold collisionLimit
    ring
  rw [he] at hh
  exact hh

theorem no_fixed_data_of_interpolation_and_analytic_aggregate
    (hgeometry : GlobalInterpolationStatement base) (hanalytic : AnalyticAggregateStatement base)
    (nu : ℝ) (hnu : 2 * base.degree < nu) (d : FixedData base nu) : False := by
  classical
  obtain ⟨error, herror, hupper⟩ := hanalytic nu hnu d
  have hsum : Tendsto (fun H : ℝ => d.arithmeticError + d.analyticError + error H)
      atTop (𝓝 (d.arithmeticError + d.analyticError + 0)) :=
    tendsto_const_nhds.add herror
  have hsmall : ∀ᶠ H : ℝ in atTop,
      d.arithmeticError + d.analyticError + error H <
        nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
          base.degree * (1 - d.base.theta) :=
    hsum.eventually (Iio_mem_nhds (by simpa using d.error_sum_lt_gap))
  have hdiff : Tendsto (fun H : ℝ =>
      collisionRate d H - (base.degree + d.arithmeticError + d.analyticError + error H))
      atTop (𝓝 (collisionLimit d - (base.degree + d.arithmeticError + d.analyticError + 0))) :=
    (tendsto_collisionRate d).sub (tendsto_const_nhds.add herror)
  have hlarge : ∀ᶠ H : ℝ in atTop,
      0 < collisionRate d H - (base.degree + d.arithmeticError + d.analyticError + error H) := by
    apply hdiff.eventually (Ioi_mem_nhds ?_)
    have hh := d.collision_exceeds_error_sum
    change base.degree + d.arithmeticError + d.analyticError < collisionLimit d at hh
    linarith
  have hcontradiction : ∀ᶠ H : ℝ in atTop,
      Function.Surjective (actualMatrix d H).mulVecLin → False := by
    filter_upwards [hsmall, hlarge, hupper,
      eventually_gt_atTop (0 : ℝ)] with H hsmall hlarge hupper hH
    intro hsurj
    obtain ⟨selection, _hselection, hdet⟩ :=
      InterpolationMatrix.exists_full_row_minor_of_surjective (actualMatrix d H) hsurj
    have hdet' : (actualMinor d H selection).det ≠ 0 := hdet
    have hlower := actual_minor_arithmetic_lower_bound d H hH selection hdet'
    have hb := actualMean_bounds d H hH
    exact LogarithmExtension.determinant_comparison base.degree nu d.base.A d.base.eta
      d.base.theta (actualMean d H) d.arithmeticError (d.analyticError + error H)
      1 (collisionRate d H) (normLog d H selection) base.degree_pos.le
      (by nlinarith [base.degree_pos]) hb.1 hb.2 (by linarith) (by linarith) hlower
      (by simpa only [one_mul, neg_one_mul] using hupper selection hdet')
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hcontradiction
  obtain ⟨H, hLH, hsurj⟩ := hgeometry nu hnu d L
  exact hL H hLH hsurj

theorem eventualLowerBound_of_interpolation_and_analytic_aggregate
    (hgeometry : GlobalInterpolationStatement base) (hanalytic : AnalyticAggregateStatement base) :
    LogarithmExtension.EventualLowerBound base.logValue (2 * base.degree) := by
  intro nu hnu
  by_contra h
  push Not at h
  have hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |base.logValue - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu) := by
    intro Q
    obtain ⟨p, q, hq, herr⟩ := h (max Q 2) (le_max_right _ _)
    exact ⟨p, q, (le_max_left _ _).trans hq, herr.le⟩
  obtain ⟨d⟩ := exists_admissible_parameters base nu Arithmetic.lcmConstant collisionConstant
    hnu Arithmetic.lcmConstant_pos collisionConstant_pos hbad
  exact no_fixed_data_of_interpolation_and_analytic_aggregate hgeometry hanalytic nu hnu d

end AlgebraicLog.DeterminantContradiction

end LogarithmExtension

