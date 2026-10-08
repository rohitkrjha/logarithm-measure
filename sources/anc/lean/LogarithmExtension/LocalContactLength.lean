import LogarithmExtension.JetLocalization
import LogarithmExtension.CurveContactFamily

/-! # Actual local ideal lengths equal the normalized branch contacts -/

noncomputable section
namespace LogarithmExtension.LocalContactLength

open OAI OAI.PiExponent
open CurveCenters CurveValuationCenter PlaceValuationRing PlaceCenteredBranch
open CoordinateScaling JetLocalization

variable {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}

theorem lift_normalize (p : NormalizedPlace ℂ E) (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (c : Fin m → ℂ) (hc : Centered z (Fin.cases y c) p) :
    normalizeTuple y (lift p z (Fin.cases y c) hc) =
      lift p (normalize y z) (Fin.cases 1 c) (centered_normalize y hy z c p hc) := by
  funext i
  apply Subtype.ext
  cases i using Fin.cases with
  | zero =>
    change algebraMap ℂ E y⁻¹ * z 0 = z 0 / algebraMap ℂ E y
    rw [map_inv₀, div_eq_mul_inv, mul_comm]
  | succ i => rfl

theorem colength_eq_contact (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    {K : ℕ} (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0) (c : Fin K → Fin m → ℂ)
    (hcent : Function.Injective (fun j => (Fin.cases (y j) (c j) : Fin (m+1) → ℂ)))
    (k : Fin K) (z : Fin (m+1) → E)
    (hc : Centered z (Fin.cases (y k) (c k)) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E ((Fin.cases (y k) (c k) : Fin (m+1) → ℂ) i))
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    ((Module.length (ring p) ((ring p) ⧸
      (NormalizedJetIdeal.polynomialIdeal y c T e).map
        (MvPolynomial.aeval (lift p z (Fin.cases (y k) (c k)) hc)).toRingHom)).toNat : ℚ) =
      R * CoordinateScaling.contact p (y k) (hy k) z (c k) hc hnc v := by
  let a := lift p z (Fin.cases (y k) (c k)) hc
  let zn := normalize (y k) z
  let hcn := centered_normalize (y k) (hy k) z (c k) p hc
  let an := lift p zn (Fin.cases 1 (c k)) hcn
  have hn := normalize_nonconstant (y k) (hy k) z (c k) hnc
  have heq : normalizeTuple (y k) a = an := lift_normalize p (y k) (hy k) z (c k) hc
  have hzero : normalizeTuple (y k) a 0 = an 0 := congrFun heq 0
  have htail : (fun i : Fin m => a i.succ) = (fun i : Fin m => an i.succ) := by
    funext i
    exact congrFun heq i.succ
  rw [JetLocalization.map_polynomialIdeal_eq_selected y hy c hcent T e a k
    (lift_residue p z (Fin.cases (y k) (c k)) hc)]
  change ((Module.length (ring p) ((ring p) ⧸
    LogarithmicContactIdeal.logarithmicIdeal (c k)
      (normalizeTuple (y k) a 0) (fun i => a i.succ) T e)).toNat : ℚ) = _
  rw [hzero, htail]
  exact LogarithmicContactIdeal.logarithmicIdeal_colength_eq_contact v hv (c k)
    (an 0) (fun i => an i.succ)
    (lift_residue p zn (Fin.cases 1 (c k)) hcn 0)
    (fun i => lift_residue p zn (Fin.cases 1 (c k)) hcn i.succ)
    (logLift_nonconstant p zn (c k) hcn hn) T hT R e he

end LogarithmExtension.LocalContactLength
