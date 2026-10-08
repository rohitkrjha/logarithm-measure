import LogarithmExtension.NormalizedJetIdeal
import OAI.NumberTheory.PiExponent.Jets.JetProductLocalization

/-!
# Local images of normalized jet ideals

These identities are the bridge between the concrete polynomial ideal and
the local logarithmic-contact lengths used by exceptional-divisor degrees.
The other center factors become units because the full center tuples differ;
this includes distinct first coordinates and distinct additive coordinates.
-/

noncomputable section
namespace LogarithmExtension.JetLocalization

open OAI OAI.PiExponent OAI.PiExponentApprox
open NormalizedJetIdeal CoordinateScaling
open LogarithmicContactIdeal
open scoped BigOperators

variable {m : ℕ}

theorem powerIdeal_eq_map (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (e : Fin (m+1) → ℕ) :
    powerIdeal y c G e =
      (CompactJetPolynomial.powerIdeal c G e).map (scaleY y⁻¹).toRingHom := by
  exact (Ideal.map_symm (scaleEquiv y hy).toRingEquiv).symm

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Multiplication by the inverse scalar also makes sense in a local ring. -/
def normalizeTuple (y : ℂ) (z : Fin (m+1) → A) : Fin (m+1) → A :=
  Fin.cases (algebraMap ℂ A y⁻¹ * z 0) (fun i => z i.succ)

theorem aeval_normalizeTuple (y : ℂ) (z : Fin (m+1) → A) :
    MvPolynomial.aeval (normalizeTuple y z) =
      (MvPolynomial.aeval z).comp (scaleY y⁻¹) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases <;> simp [normalizeTuple, AlgHom.comp_apply]

theorem map_powerIdeal_aeval (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (z : Fin (m+1) → A) :
    (powerIdeal y c (CompactJetPolynomial.logPolynomials T) e).map
      (MvPolynomial.aeval z).toRingHom =
      logarithmicIdeal c (normalizeTuple y z 0) (fun i => z i.succ) T e := by
  rw [powerIdeal_eq_map y hy, Ideal.map_map]
  have he : (MvPolynomial.aeval z).toRingHom.comp (scaleY y⁻¹).toRingHom =
      (MvPolynomial.aeval (normalizeTuple y z)).toRingHom := by
    rw [aeval_normalizeTuple]
    rfl
  rw [he]
  exact CompactJetPolynomial.map_powerIdeal_aeval c T e _ _

theorem map_polynomialIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (z : Fin (m+1) → A) :
    (polynomialIdeal y c T e).map (MvPolynomial.aeval z).toRingHom =
      ∏ j, logarithmicIdeal (c j) (normalizeTuple (y j) z 0) (fun i => z i.succ) T e := by
  unfold polynomialIdeal
  change Ideal.mapHom (MvPolynomial.aeval z).toRingHom _ = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact map_powerIdeal_aeval (y j) (hy j) (c j) T e z

variable [IsLocalRing A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem residue_normalize_zero (y : ℂ) (z : Fin (m+1) → A) :
    CurveLocalOrder.residueAugmentation ℂ A (normalizeTuple y z 0) =
      y⁻¹ * CurveLocalOrder.residueAugmentation ℂ A (z 0) := by
  simp [normalizeTuple, map_mul, CurveLocalOrder.residueAugmentation_algebraMap]

theorem residue_normalize_zero_eq_one_iff (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → A) :
    CurveLocalOrder.residueAugmentation ℂ A (normalizeTuple y z 0) = 1 ↔
      CurveLocalOrder.residueAugmentation ℂ A (z 0) = y := by
  rw [residue_normalize_zero]
  constructor
  · intro h
    have he := congrArg (fun a : ℂ => y * a) h
    simpa [← mul_assoc, hy] using he
  · intro h
    rw [h, inv_mul_cancel₀ hy]

theorem map_powerIdeal_eq_top_of_ne {J : Type*}
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ)
    (hcent : Function.Injective (fun j => (Fin.cases (y j) (c j) : Fin (m+1) → ℂ)))
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (z : Fin (m+1) → A) (j k : J) (hkj : k ≠ j)
    (hz : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (z i) =
      (Fin.cases (y j) (c j) : Fin (m+1) → ℂ) i) :
    (powerIdeal (y k) (c k) (CompactJetPolynomial.logPolynomials T) e).map
      (MvPolynomial.aeval z).toRingHom = ⊤ := by
  rw [map_powerIdeal_aeval (y k) (hy k)]
  apply JetProductLocalization.logarithmicIdeal_eq_top_of_residue_ne
  rintro ⟨hk, hc⟩
  apply hkj
  apply hcent
  funext i
  cases i using Fin.cases with
  | zero =>
    exact ((residue_normalize_zero_eq_one_iff (y k) (hy k) z).mp hk).symm.trans (hz 0)
  | succ i => exact (hc i).symm.trans (hz i.succ)

theorem map_polynomialIdeal_eq_selected {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ)
    (hcent : Function.Injective (fun j => (Fin.cases (y j) (c j) : Fin (m+1) → ℂ)))
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (z : Fin (m+1) → A) (j : J)
    (hz : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (z i) =
      (Fin.cases (y j) (c j) : Fin (m+1) → ℂ) i) :
    (polynomialIdeal y c T e).map (MvPolynomial.aeval z).toRingHom =
      logarithmicIdeal (c j) (normalizeTuple (y j) z 0) (fun i => z i.succ) T e := by
  classical
  rw [map_polynomialIdeal y hy]
  apply Finset.prod_eq_single j
  · intro k _ hkj
    rw [Ideal.one_eq_top, ← map_powerIdeal_aeval (y k) (hy k)]
    exact map_powerIdeal_eq_top_of_ne y hy c hcent T e z j k hkj hz
  · simp

theorem map_polynomialIdeal_eq_top_outside {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (z : Fin (m+1) → A)
    (hout : ¬ ∃ j, CurveLocalOrder.residueAugmentation ℂ A (z 0) = y j ∧
      ∀ i, CurveLocalOrder.residueAugmentation ℂ A (z i.succ) = c j i) :
    (polynomialIdeal y c T e).map (MvPolynomial.aeval z).toRingHom = ⊤ := by
  rw [map_polynomialIdeal y hy, ← Ideal.one_eq_top]
  apply Finset.prod_eq_one
  intro j _
  rw [Ideal.one_eq_top]
  apply JetProductLocalization.logarithmicIdeal_eq_top_of_residue_ne
  rintro ⟨hz, hx⟩
  exact hout ⟨j, (residue_normalize_zero_eq_one_iff (y j) (hy j) z).mp hz, hx⟩

end LogarithmExtension.JetLocalization
