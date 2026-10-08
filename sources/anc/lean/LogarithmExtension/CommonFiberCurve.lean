import LogarithmExtension.CurveGeometry
import OAI.NumberTheory.PiExponent.Geometry.CurveInequalityIntrinsic

/-! The reference common-fiber curve inequality, transported to the same
normalized contact functions used by the distinct-fiber geometry. -/

noncomputable section
namespace LogarithmExtension.CommonFiberCurve

open OAI OAI.PiExponent
open CurveValuationCenter PlaceValuationRing CurveCenters
open scoped BigOperators

variable {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}

theorem normalize_one (z : Fin (m+1) → E) : CoordinateScaling.normalize 1 z = z := by
  funext i
  cases i using Fin.cases <;> simp [CoordinateScaling.normalize]

theorem coordinate_contact_one (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases 1 c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) :
    CoordinateScaling.contact p 1 one_ne_zero z c hc hnc v =
      PlaceCenteredBranch.logContact p z c hc hnc v := by
  have congr_contact {u u' : Fin (m+1) → E} (he : u = u')
      (hu : Centered u (Fin.cases 1 c) p) (hu' : Centered u' (Fin.cases 1 c) p)
      (hnu : ∃ i, u i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
      (hnu' : ∃ i, u' i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i)) :
      PlaceCenteredBranch.logContact p u c hu hnu v =
        PlaceCenteredBranch.logContact p u' c hu' hnu' v := by
    subst u'
    rfl
  exact congr_contact (normalize_one z) _ _ _ _

theorem places_one
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) :
    CurveContactFamily.places hfinite z (fun _ => 1) c hz =
      OAI.PiExponent.CurveContactFamily.places hfinite z c hz := rfl

theorem contact_one
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ)
    (p : NormalizedPlace ℂ E) :
    CurveContactFamily.contact hres hfinite z (fun _ => 1) (fun _ => one_ne_zero) c hz v p =
      OAI.PiExponent.CurveContactFamily.contact hres hfinite z c hz v p := by
  classical
  let := hres p
  by_cases hp : p ∈ OAI.PiExponent.CurveContactFamily.places hfinite z c hz
  · have hp' : p ∈ CurveContactFamily.places hfinite z (fun _ => 1) c hz := hp
    rw [CurveContactFamily.contact, dite_eq_left hp',
      OAI.PiExponent.CurveContactFamily.contact, dite_eq_left hp]
    exact coordinate_contact_one p z _ _ _ v
  · have hp' : p ∉ CurveContactFamily.places hfinite z (fun _ => 1) c hz := hp
    rw [CurveContactFamily.contact, dite_eq_right hp',
      OAI.PiExponent.CurveContactFamily.contact, dite_eq_right hp]

variable [Algebra.EssFiniteType ℂ E]

theorem weighted_curve_inequality {m K : ℕ}
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hc : ∀ i, Function.Injective (fun j => c j i))
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hfibrevol : (K : ℝ) * (1+3*(sigma : ℝ))^m *
      (∏ i : Fin m, (w i.succ : ℝ)) / (∏ i : Fin m, (v i.succ : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      PersistentWeightComparison.comparisonConstant m sigma *
        (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ : ℝ) < v i.succ) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let hz := CurveGeometry.nonconstant_coordinates z hgen htrdeg
    (1+(sigma : ℝ)) * ∑ p ∈ CurveContactFamily.places hfinite z (fun _ => 1) c hz,
      (CurveContactFamily.contact hres hfinite z (fun _ => 1) (fun _ => one_ne_zero) c hz v p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z w := by
  have he : Fin.cases (z 0) (fun i => z i.succ) = z := by
    funext i
    cases i using Fin.cases <;> rfl
  have hgen' : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases (z 0) (fun i => z i.succ))) = ⊤ := by rwa [he]
  have h := OAI.PiExponent.CurveInequality.weighted_curve_inequality
    (z 0) (fun i => z i.succ) c hc hgen' htrdeg w v hw hv sigma hsigma
    hvol hfibrevol hseparated hratio
  dsimp only at h ⊢
  simp only [he] at h
  simpa only [places_one, contact_one] using h

#print axioms weighted_curve_inequality

end LogarithmExtension.CommonFiberCurve
