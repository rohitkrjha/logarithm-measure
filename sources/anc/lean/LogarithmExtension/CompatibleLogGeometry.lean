import LogarithmExtension.CompatibleLogCurveWeights
import LogarithmExtension.CompatibleLogDeterminantContradiction
import LogarithmExtension.MatrixIdentification

/-! Instantiation of the checked logarithmic geometry at arbitrary algebraic
slopes, with either distinct multiplicative centers or a common fiber at one. -/
noncomputable section
namespace LogarithmExtension.CompatibleLog.Geometry

open OAI OAI.PiExponent Filter
open DeterminantContradiction
variable {base : Base} {nu : ℝ} (d : FixedData base nu)

theorem scaledCenters_ne_zero (i : Fin d.m) :
    MatrixArithmetic.scaledCenters base base.embedding
      (finiteNumerators d) (finiteDenominators d) i ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero ((map_ne_zero base.embedding).mpr base.slope_ne_zero)
      (by exact_mod_cast (d.approximations i.val).2.1)
  · exact_mod_cast (show finiteDenominators d i ≠ 0 by
      have h := finiteDenominators_two_le d i
      omega)

def geometry
    (hsep : Function.Injective (fun n : ℕ => base.element ^ n) ∨ base.element = 1) :
    GeometryData where
  m := d.m
  K := d.K
  curveDegreeWeights := d.curveDegreeWeights
  curveJetWeights := d.curveJetWeights
  curveDegreeWeights_pos := d.curveDegreeWeights_pos
  curveJetWeights_pos := d.curveJetWeights_pos
  centerY := fun j => (base.embedding base.element) ^ j.val
  centerY_ne_zero := fun j => pow_ne_zero _ ((map_ne_zero base.embedding).mpr base.element_ne_zero)
  center_separation := by
    rcases hsep with hinj | hbase
    · left
      intro j k he
      exact Fin.ext ((base.embedding_powers_injective hinj base.embedding) he)
    · right
      refine ⟨?_, ?_, d.m_pos, d.curve_fibre_volume⟩
      · funext j
        simp only [hbase, map_one, one_pow]
      · intro i j k he
        apply Fin.ext
        exact_mod_cast (mul_right_cancel₀ (scaledCenters_ne_zero d i) he)
  curveCenters := fun j i => (j.val : ℂ) *
    MatrixArithmetic.scaledCenters base base.embedding (finiteNumerators d) (finiteDenominators d) i
  sigma := d.sigma
  sigma_pos := by exact_mod_cast d.sigma_pos
  curve_volume := d.curve_volume
  curve_separated_weight_products := d.curve_separated_weight_products
  curve_coordinate_ratio := d.curve_coordinate_ratio

theorem degreeWeights_eq_matrix (i : Fin (d.m+1)) :
    (d.curveDegreeWeights i : ℝ) =
      InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [AdmissibleParameters.curveDegreeWeights_succ,
      d.cast_rationalWeight, InterpolationMatrix.columnWeights, Fin.cases_succ,
      logWeights_eq]

theorem jetWeights_eq_matrix (i : Fin (d.m+1)) :
    (d.curveJetWeights i : ℝ) =
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [AdmissibleParameters.curveJetWeights_succ, Rat.cast_div,
      d.cast_rationalWeight, InterpolationMatrix.rowWeights, Fin.cases_succ,
      logWeights_eq]

theorem actual_truncation_weight_bound (i : Fin d.m) :
    d.curveJetWeights i.succ ≤
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℚ) *
        d.curveJetWeights 0 := by
  have hw : 0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    rw [logWeights_eq]
    exact zero_lt_one.trans_le (d.x_one_le _)
  have hF : 1 / (d.base.theta : ℝ) < d.F0 :=
    (div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 2) d.base.theta_pos).trans d.F0_large
  have hceil := Nat.le_ceil
    (d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i / (d.v0 : ℝ))
  have hbound : MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
        (d.v0 : ℝ) := by
    calc
      _ = (1 / (d.base.theta : ℝ)) *
          MatrixArithmetic.logWeights (finiteDenominators d) i := by ring
      _ ≤ d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i :=
        mul_le_mul_of_nonneg_right hF.le hw.le
      _ ≤ _ := (div_le_iff₀ d.v0_pos).mp hceil
  have hcast : (d.curveJetWeights i.succ : ℝ) ≤
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
        (d.curveJetWeights 0 : ℝ) := by
    simpa only [AdmissibleParameters.curveJetWeights_zero,
      AdmissibleParameters.curveJetWeights_succ, Rat.cast_div,
      d.cast_rationalWeight, logWeights_eq] using hbound
  exact_mod_cast hcast


theorem actualMatrix_surjective_of_geometry
    (hsep : Function.Injective (fun n : ℕ => base.element ^ n) ∨ base.element = 1) (H : ℚ)
    (hsurj : Function.Surjective
      (BoundedJetMatrix.matrix (geometry d hsep)
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) H).mulVecLin) :
    Function.Surjective (actualMatrix d (H : ℝ)).mulVecLin := by
  have hm := MatrixIdentification.actualMatrix_eq (geometry d hsep) (base.embedding base.element)
    (MatrixArithmetic.scaledCenters base base.embedding (finiteNumerators d) (finiteDenominators d))
    (fun _ => rfl) (fun _ _ => rfl)
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) H
  rw [← hm] at hsurj
  change Function.Surjective
    (Matrix.mulVecLin (fun (row : Fin d.K × ↥(strictWeightedSimplex
        (fun i => (d.curveJetWeights i : ℝ)) (H : ℝ)))
      (col : ↥(realWeightedSimplex (fun i => (d.curveDegreeWeights i : ℝ)) (H : ℝ))) =>
      AnalyticTranslation.matrixEntry (base.embedding base.element)
        (MatrixArithmetic.scaledCenters base base.embedding (finiteNumerators d) (finiteDenominators d))
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
        row.1.val (row.2.val 0) (fun i => row.2.val i.succ)
        (col.val 0) (fun i => col.val i.succ))) at hsurj
  have hw := funext (degreeWeights_eq_matrix d)
  have hv := funext (jetWeights_eq_matrix d)
  rw [hw, hv] at hsurj
  exact hsurj

theorem cofinal_actualMatrix
    (hsep : Function.Injective (fun n : ℕ => base.element ^ n) ∨ base.element = 1) (L : ℝ) :
    ∃ H : ℝ, L ≤ H ∧ Function.Surjective (actualMatrix d H).mulVecLin := by
  have hevent := BoundedJetMatrix.eventually_surjective (geometry d hsep)
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (actual_truncation_weight_bound d)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let R : ℕ := (BlowupGeometry.scale (geometry d hsep)).radius
  let n := max N (Nat.ceil (L / (R : ℝ)))
  have hR : (0 : ℝ) < R := by
    exact_mod_cast (BlowupGeometry.scale (geometry d hsep)).radius_pos
  have hL : L ≤ (n : ℝ) * (R : ℝ) := by
    apply (div_le_iff₀ hR).mp
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right N (Nat.ceil (L / (R : ℝ)))))
  refine ⟨(n : ℝ) * (R : ℝ), hL, ?_⟩
  have hs := actualMatrix_surjective_of_geometry d hsep ((n : ℚ) * (R : ℚ))
    (hN n (le_max_left _ _))
  have hc : (((n : ℚ) * (R : ℚ) : ℚ) : ℝ) = (n : ℝ) * (R : ℝ) := by
    push_cast
    rfl
  exact hc ▸ hs

theorem globalInterpolation (base : Base) (hinj : Function.Injective (fun n : ℕ => base.element ^ n)) : GlobalInterpolationStatement base := by
  intro nu _ d L
  exact cofinal_actualMatrix d (Or.inl hinj) L

theorem commonFiberGlobalInterpolation (base : Base) (hbase : base.element = 1) :
    GlobalInterpolationStatement base := by
  intro nu _ d L
  exact cofinal_actualMatrix d (Or.inr hbase) L

end LogarithmExtension.CompatibleLog.Geometry


#print axioms LogarithmExtension.CompatibleLog.Geometry.globalInterpolation
#print axioms LogarithmExtension.CompatibleLog.Geometry.commonFiberGlobalInterpolation
