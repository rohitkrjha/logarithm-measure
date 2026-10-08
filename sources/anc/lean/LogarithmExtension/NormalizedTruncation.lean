import LogarithmExtension.CoordinateScaling
import OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation

/-! # Truncated logarithm jets preserve simultaneous weighted interpolation -/

noncomputable section
namespace LogarithmExtension.NormalizedTruncation

open OAI OAI.PiExponent OAI.PiExponentApprox
open CoordinateScaling FormalLogTruncation JetGeometry

def truncatedJet {m : ℕ} (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ) :
    FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  (truncatedFormalJet c T).comp (scaleY y)

theorem shiftMap_truncatedJet {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (P : FramePolynomial m) :
    shiftMap (fun i => logTail (T i)) (fun i => logTail_constantCoeff (T i))
      (truncatedJet y c T P) = NormalizedLogJet.formalJet y c P := by
  change shiftMap _ _ (truncatedFormalJet c T (scaleY y P)) = _
  rw [shiftMap_truncatedFormalJet, formalJet_scaleY]

/-- Scaling can depend on the centre: the common series automorphism acts
on the packets, not on the source polynomial family. -/
theorem packets_surjective_iff_truncated {m : ℕ} {α J : Type*}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (y : J → ℂ) (c : J → Fin m → ℂ) (P : α → FramePolynomial m) :
    Function.Surjective (fun a j => rationalCoefficientPacket v H
      (NormalizedLogJet.formalJet (y j) (c j) (P a))) ↔
    Function.Surjective (fun a j => rationalCoefficientPacket v H
      (truncatedJet (y j) (c j) T (P a))) := by
  let tail := fun i => logTail (T i)
  let ht := fun i => logTail_constantCoeff (T i)
  let e := shiftEquiv tail ht
  have hw : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ) :=
    fun i => logTail_mem_rationalWeightedIdeal v hv (T i) (v i.succ) (hT i)
  have he : ∀ F ∈ rationalWeightedIdeal v hv H, e F ∈ rationalWeightedIdeal v hv H :=
    fun F hF => (shiftEquiv_mem_iff tail ht v hv hw H F).mpr hF
  have hi : ∀ F ∈ rationalWeightedIdeal v hv H, e.symm F ∈ rationalWeightedIdeal v hv H := by
    intro F hF
    apply (shiftEquiv_mem_iff tail ht v hv hw H (e.symm F)).mp
    change e (e.symm F) ∈ rationalWeightedIdeal v hv H
    simpa only [AlgEquiv.apply_symm_apply] using hF
  have hh := packets_surjective_comp_equiv_iff v hv H e he hi
    (fun a j => truncatedJet (y j) (c j) T (P a))
  simpa only [e, tail, ht, shiftEquiv_apply, shiftMap_truncatedJet] using hh

end LogarithmExtension.NormalizedTruncation
