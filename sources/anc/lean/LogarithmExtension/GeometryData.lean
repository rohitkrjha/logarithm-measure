import LogarithmExtension.CommonFiberCurve

/-!
# Target-independent data for the logarithmic interpolation geometry

The reference development's `AdmissibleParameters` includes approximations
to pi. This structure does not: its hypotheses are precisely the geometric
inequalities used by the checked logarithm curve theorem. LogThreeGeometry
constructs these data from the logarithm-specific admissible parameters.
-/

noncomputable section
namespace LogarithmExtension

open OAI OAI.PiExponent
open scoped BigOperators

structure GeometryData where
  m : ℕ
  K : ℕ
  curveDegreeWeights : Fin (m+1) → ℚ
  curveJetWeights : Fin (m+1) → ℚ
  curveDegreeWeights_pos : ∀ i, 0 < curveDegreeWeights i
  curveJetWeights_pos : ∀ i, 0 < curveJetWeights i
  centerY : Fin K → ℂ
  centerY_ne_zero : ∀ j, centerY j ≠ 0
  curveCenters : Fin K → Fin m → ℂ
  sigma : ℚ
  sigma_pos : 0 < sigma
  curve_volume : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
    (∏ i, (curveDegreeWeights i : ℝ)) / (∏ i, (curveJetWeights i : ℝ)) < 1
  curve_separated_weight_products : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
    ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
    (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
    PersistentWeightComparison.comparisonConstant m sigma *
      (∏ j ∈ B, (curveJetWeights j : ℝ)) < ∏ j ∈ A, (curveDegreeWeights j : ℝ)
  curve_coordinate_ratio : ∀ i : Fin m,
    (1+(sigma : ℝ)) * (curveDegreeWeights i.succ : ℝ) < curveJetWeights i.succ
  /-- Either the multiplicative centers are distinct, or all of them are
  one and the additive centers satisfy the common-fiber hypotheses. -/
  center_separation : Function.Injective centerY ∨
    (centerY = fun _ => 1) ∧
      (∀ i, Function.Injective (fun j => curveCenters j i)) ∧ 0 < m ∧
        (K : ℝ) * (1+3*(sigma : ℝ))^m *
          (∏ i : Fin m, (curveDegreeWeights i.succ : ℝ)) /
            (∏ i : Fin m, (curveJetWeights i.succ : ℝ)) < 1

namespace GeometryData

theorem sigma_pos_real (d : GeometryData) : (0 : ℝ) < d.sigma := by
  exact_mod_cast d.sigma_pos

theorem fullCenters_injective (d : GeometryData) :
    Function.Injective (fun j =>
      (Fin.cases (d.centerY j) (d.curveCenters j) : Fin (d.m+1) → ℂ)) := by
  intro j k he
  rcases d.center_separation with hY | ⟨_, hX, hm, _⟩
  · exact hY (congrFun he 0)
  · exact hX ⟨0, hm⟩ (congrFun he (Fin.succ ⟨0, hm⟩))

/-- All curve-inequality assumptions are discharged by the explicit data;
there is no interpolation or irrationality-measure hypothesis here. -/
theorem curve_inequality (d : GeometryData)
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (z : Fin (d.m+1) → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let hz := CurveGeometry.nonconstant_coordinates z hgen htrdeg
    (1+(d.sigma : ℝ)) * ∑ p ∈ CurveContactFamily.places hfinite z d.centerY d.curveCenters hz,
        (CurveContactFamily.contact hres hfinite z d.centerY d.centerY_ne_zero
          d.curveCenters hz d.curveJetWeights p : ℝ) ≤
      CurveContactSum.weightedDegree hfinite z d.curveDegreeWeights := by
  rcases d.center_separation with hY | ⟨hY, hX, _, hvol⟩
  · exact CurveGeometry.weighted_curve_inequality_intrinsic z d.centerY d.centerY_ne_zero
      hY d.curveCenters hgen htrdeg d.curveDegreeWeights d.curveJetWeights
      d.curveDegreeWeights_pos d.curveJetWeights_pos d.sigma d.sigma_pos d.curve_volume
      d.curve_separated_weight_products d.curve_coordinate_ratio
  · have h := CommonFiberCurve.weighted_curve_inequality z d.curveCenters hX hgen htrdeg
      d.curveDegreeWeights d.curveJetWeights d.curveDegreeWeights_pos d.curveJetWeights_pos
      d.sigma d.sigma_pos d.curve_volume hvol d.curve_separated_weight_products
      d.curve_coordinate_ratio
    dsimp only at h ⊢
    simpa only [hY] using h

end GeometryData
end LogarithmExtension
