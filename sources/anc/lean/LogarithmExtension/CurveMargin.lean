import LogarithmExtension.GeometryData
import OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin

/-! The affine-curve numerical margin, adapted from upstream (Apache-2.0),
using the proved normalized contact inequality. -/

noncomputable section
namespace LogarithmExtension.CurveMargin
open OAI OAI.PiExponent
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
open OAI.PiExponent.BlowupCurveMargin
open scoped BigOperators
variable {B : Scheme.{0}}

variable (d : GeometryData)
variable {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]

def contactSum (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ℝ :=
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let z : Fin (d.m+1) → E := Fin.cases y x
  let hz := CurveGeometry.nonconstant_coordinates z hgen htrdeg
  ∑ q ∈ CurveContactFamily.places hfinite z d.centerY d.curveCenters hz,
    (CurveContactFamily.contact hres hfinite z d.centerY d.centerY_ne_zero d.curveCenters hz d.curveJetWeights q : ℝ)

def poleDegree (y : E) (x : Fin d.m → E) (htrdeg : Algebra.trdeg ℂ E = 1) : ℝ :=
  CurveContactSum.weightedDegree
    (CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg)
    (Fin.cases y x : Fin (d.m+1) → E) d.curveDegreeWeights

theorem actual_contact_bound (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    (1 + (d.sigma : ℝ)) * contactSum d y x hgen htrdeg ≤ poleDegree d y x htrdeg := by
  let z : Fin (d.m+1) → E := Fin.cases y x
  have hzgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤ := hgen
  have h := @GeometryData.curve_inequality d E _ _ _ z hzgen htrdeg
  exact h

theorem margin_of_actual_contact_degrees
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (A J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (C : IntegralCurve B) (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) (R : ℚ) (hR : 0 < R)
    (hA : (curveDegree p A C : ℝ) = (R : ℝ) * poleDegree d y x htrdeg)
    (hJ : (curveDegree p J C : ℝ) = -(R : ℝ) * contactSum d y x hgen htrdeg) :
    marginCoefficient a d.sigma * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) := by
  apply margin_of_nonnegative_degree p A J a ha hample d.sigma d.sigma_pos_real C
  rw [hA, hJ]
  have hR' : (0 : ℝ) ≤ R := by exact_mod_cast hR.le
  have h := mul_le_mul_of_nonneg_left (actual_contact_bound d y x hgen htrdeg) hR'
  nlinarith


end LogarithmExtension.CurveMargin
