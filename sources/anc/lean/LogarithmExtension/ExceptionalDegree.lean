import LogarithmExtension.CenterIdentification
import LogarithmExtension.LocalContactLength
import LogarithmExtension.BlowupGeometry
import LogarithmExtension.CurveMargin
import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree

/-!
# Exceptional degree for the normalized logarithmic centre ideal

The generic divisor-degree theorems are reused from the upstream development.
The centre-dependent parts are proved here for varying first coordinates.
Adapted portions of `ExceptionalCurveDegree` are Apache-2.0.
-/

noncomputable section
namespace LogarithmExtension.ExceptionalDegree

open OAI OAI.PiExponent
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open OAI.PiExponent.ExceptionalCurveDegree
open CurveNormalizationModel CurveValuationCenter CurvePlaceCenter

variable {X Y : Scheme.{0}}

theorem localIdeal_compactIdeal {A : Type} [CommRing A]
    {m : ℕ} {K : Type} [Fintype K] (y : K → ℂ) (c : K → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (j : CompactNormalizedJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (φ : CompactNormalizedJetIdeal.coordinateRing m →+* A) :
    localIdeal (CompactNormalizedJetIdeal.compactIdeal y c T e j)
      (Spec.map (CommRingCat.ofHom φ) ≫ j) =
        (NormalizedJetIdeal.polynomialIdeal y c T e).map φ := by
  unfold localIdeal
  rw [Scheme.IdealSheafData.comap_comp, CompactNormalizedJetIdeal.restrict_compactIdeal]
  exact localIdeal_specIdeal _ φ

variable {E : Type} [Field E] [Algebra ℂ E]

theorem map_powerIdeal_eq_top_of_transcendental {m : ℕ}
    (z : Fin (m+1) → E) (hz : ∃ i, Transcendental ℂ (z i))
    (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    (NormalizedJetIdeal.powerIdeal y c (CompactJetPolynomial.logPolynomials T) e).map
      (MvPolynomial.aeval z).toRingHom = ⊤ := by
  obtain ⟨i, hi⟩ := hz
  let P := MvPolynomial.X i - MvPolynomial.C (NormalizedJetIdeal.center y c i)
  have hP : P ∈ (NormalizedJetIdeal.powerIdeal y c
      (CompactJetPolynomial.logPolynomials T) e).radical := by
    rw [NormalizedJetIdeal.radical_powerIdeal y c _
      (CompactJetPolynomial.logPolynomials_eval_zero T) e he]
    change MvPolynomial.aeval (NormalizedJetIdeal.center y c) P = 0
    simp [P]
  obtain ⟨n, hn⟩ := hP
  have hne : MvPolynomial.aeval z P ≠ 0 := by
    intro h
    have heq : z i = algebraMap ℂ E (NormalizedJetIdeal.center y c i) := by
      simpa [P, sub_eq_zero] using h
    exact hi (heq ▸ isAlgebraic_algebraMap _)
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hn)
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow] using
    (isUnit_iff_ne_zero.mpr hne).pow n

variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem compactIdeal_comap_ne_bot_of_generic {m : ℕ} {K : Type} [Fintype K]
    (y : K → ℂ) (c : K → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i)
    (j : CompactNormalizedJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (g : parameterCurve f hf ⟶ X) (z : Fin (m+1) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j) :
    (CompactNormalizedJetIdeal.compactIdeal y c T e j).comap g ≠ ⊥ := by
  have htop : localIdeal (CompactNormalizedJetIdeal.compactIdeal y c T e j)
      (parameterCurveGenericPoint f hf ≫ g) = ⊤ := by
    rw [hgeneric, localIdeal_compactIdeal]
    unfold NormalizedJetIdeal.polynomialIdeal
    change Ideal.mapHom (MvPolynomial.aeval z).toRingHom _ = _
    rw [map_prod]
    have ht : ∀ k : K, (NormalizedJetIdeal.powerIdeal (y k) (c k)
        (CompactJetPolynomial.logPolynomials T) e).map (MvPolynomial.aeval z).toRingHom = ⊤ :=
      fun k => map_powerIdeal_eq_top_of_transcendental z hz (y k) (c k) T e he
    simp only [Ideal.mapHom_apply, ht]
    rw [← Ideal.one_eq_top]
    exact Finset.prod_const_one
  intro hzero
  have hb : localIdeal (CompactNormalizedJetIdeal.compactIdeal y c T e j)
      (parameterCurveGenericPoint f hf ≫ g) = ⊥ := by
    simp only [localIdeal, Scheme.IdealSheafData.comap_comp, hzero,
      Scheme.IdealSheafData.comap_bot]
    exact Ideal.map_bot
  exact bot_ne_top (hb.symm.trans htop)

theorem centerMorphism_eq_centeredLift [X.IsSeparated]
    {m : ℕ} (j : CompactNormalizedJetIdeal.affineSpace m ⟶ X)
    (g : parameterCurve f hf ⟶ X) (z : Fin (m+1) → E)
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (p : NormalizedPlace ℂ E) (y : ℂ) (c : Fin m → ℂ)
    (hc : CurveCenters.Centered z (Fin.cases y c) p) :
    centerMorphism f hf p ≫ g =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (PlaceCenteredBranch.lift p z (Fin.cases y c) hc)).toRingHom) ≫ j := by
  apply centerMorphism_comp_eq_of_generic f hf p g
  rw [hgeneric, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro P
  exact PlaceCenteredBranch.lift_aeval p z (Fin.cases y c) hc P

theorem localIdeal_length_eq_logContact [X.IsSeparated]
    {m K : ℕ} (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0) (c : Fin K → Fin m → ℂ)
    (hcent : Function.Injective (fun j => (Fin.cases (y j) (c j) : Fin (m+1) → ℂ)))
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (j : CompactNormalizedJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (g : parameterCurve f hf ⟶ X) (z : Fin (m+1) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p))]
    (k : Fin K) (hc : CurveCenters.Centered z (Fin.cases (y k) (c k)) p) :
    ((Module.length (PlaceValuationRing.ring p)
      ((PlaceValuationRing.ring p) ⧸
        localIdeal (CompactNormalizedJetIdeal.compactIdeal y c T e j)
          (centerMorphism f hf p ≫ g))).toNat : ℚ) =
      R * CoordinateScaling.contact p (y k) (hy k) z (c k) hc
        (CurveCenters.Centered.exists_nonzero_difference z _ hz) v := by
  rw [centerMorphism_eq_centeredLift f hf j g z hgeneric p (y k) (c k) hc,
    localIdeal_compactIdeal]
  exact LocalContactLength.colength_eq_contact p y hy c hcent k z hc
    (CurveCenters.Centered.exists_nonzero_difference z _ hz) T e v hv R he hT

open scoped BigOperators

theorem compactIdeal_degree_eq_neg_contact_sum [X.IsSeparated]
    {m K : ℕ} (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0) (c : Fin K → Fin m → ℂ)
    (hcent : Function.Injective (fun j => (Fin.cases (y j) (c j) : Fin (m+1) → ℂ)))
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (j : CompactNormalizedJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (pX : X ⟶ Spec (CommRingCat.of ℂ)) [IsSeparated pX]
    (hj : j ≫ pX = CompactNormalizedJetIdeal.structureMap m)
    (π : Y ⟶ X) (J : LineBundle Y) (ι : J.sheaf ⟶ PiExponentSeshadri.Frames.O Y)
    (hJ : PresentsPullbackIdeal (CompactNormalizedJetIdeal.compactIdeal y c T e j) π J ι)
    (g : parameterCurve f hf ⟶ Y) (z : Fin (m+1) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g ≫ π =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p)))
    (hfinite : ∀ t : E, Transcendental ℂ t →
      FiniteDimensional (IntermediateField.adjoin ℂ {t}) E) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -R * ∑ p ∈ CurveContactFamily.places hfinite z y c hz,
        CurveContactFamily.contact hres hfinite z y hy c hz v p := by
  classical
  let I := CompactNormalizedJetIdeal.compactIdeal y c T e j
  have hg : I.comap (g ≫ π) ≠ ⊥ :=
    compactIdeal_comap_ne_bot_of_generic f hf y c T e hepos j (g ≫ π) z hz hgeneric
  let D := idealDivisor f hf I π J ι hJ g hg
  let P := CurveContactFamily.places hfinite z y c hz
  have hzero (p : NormalizedPlace ℂ E) (hp : p ∉ P) : D p = 0 := by
    have havoid : (centerMorphism f hf p ≫ g ≫ π)
        (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ∉ I.support := by
      intro hmem
      change _ ∈ ((CompactNormalizedJetIdeal.compactIdeal y c T e j).support : Set X) at hmem
      rw [CompactNormalizedJetIdeal.support_compactIdeal y c T e hepos j pX hj] at hmem
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨a, ha⟩ := hk
      have hap : CompactNormalizedJetIdeal.point (y k) (c k) a = NormalizedJetIdeal.centerPoint (y k) (c k) := by
        have h := Set.mem_range_self (f := CompactNormalizedJetIdeal.point (y k) (c k)) a
        rw [CompactNormalizedJetIdeal.range_point] at h
        exact h
      have hclosed : (centerMorphism f hf p ≫ g ≫ π)
          (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) =
          j (NormalizedJetIdeal.centerPoint (y k) (c k)) := by
        exact ha.symm.trans (congrArg j hap)
      have hfield : Spec.map (CommRingCat.ofHom
          (algebraMap (PlaceValuationRing.ring p) E)) ≫
          (centerMorphism f hf p ≫ g ≫ π) =
          Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j := by
        rw [← Category.assoc, centerMorphism_generic]
        exact hgeneric
      apply hp
      exact (CurveContactFamily.mem_places hfinite z y c hz p).mpr
        ⟨k, CenterIdentification.centered_of_closedPoint_eq p z (y k) (c k) j _ hfield hclosed⟩
    change idealDivisor f hf I π J ι hJ g hg p = 0
    rw [idealDivisor_apply, localIdeal_eq_top_of_not_mem I _ havoid]
    simp
  have hsupport : D.support ⊆ P := by
    intro p hp
    by_contra h
    exact (Finsupp.mem_support_iff.mp hp) (hzero p h)
  have hvalue (p : NormalizedPlace ℂ E) (hp : p ∈ P) :
      (D p : ℚ) = R * CurveContactFamily.contact hres hfinite z y hy c hz v p := by
    let := hres p
    have hp' : p ∈ CurveContactFamily.places hfinite z y c hz := hp
    let k := CurveContactFamily.center hfinite z y c hz p hp
    have hcenter := CurveContactFamily.centered hfinite z y c hz p hp
    have h := localIdeal_length_eq_logContact f hf y hy c hcent T e v hv R he hT j (g ≫ π)
      z hz hgeneric p k hcenter
    change (idealDivisor f hf I π J ι hJ g hg p : ℚ) = _
    rw [idealDivisor_apply]
    simpa only [CurveContactFamily.contact, dite_eq_left hp', I, k] using h
  have hsum : D.sum (fun _ n => (n : ℚ)) =
      R * ∑ p ∈ P, CurveContactFamily.contact hres hfinite z y hy c hz v p := by
    rw [D.sum_of_support_subset hsupport (fun _ n => (n : ℚ)) (by simp)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => hvalue p hp)
  have hd := degree_eq_neg_idealDivisor_sum f hf I π J ι hJ g hg
  have hdq : ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -D.sum (fun _ n => (n : ℚ)) := by
    simpa only [Int.cast_neg, Finsupp.sum, Int.cast_sum, Int.cast_natCast] using
      congrArg (fun a : ℤ => (a : ℚ)) hd
  rw [hsum] at hdq
  simpa only [neg_mul, P] using hdq

theorem geometry_degree_eq_neg_contactSum
    (d : GeometryData)
    {E : Type} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (f : E) (hf : Transcendental ℂ f) :
    letI := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg f hf
    ∀ (g : CurveNormalizationModel.parameterCurve f hf ⟶ BlowupGeometry.blowup d),
    CurveNormalizationModel.parameterCurveGenericPoint f hf ≫ g ≫
      BlowupGeometry.projection d =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (Fin.cases y x)).toRingHom) ≫
        BlowupGeometry.affineChart d →
    ((eulerCharacteristic (CurveNormalizationModel.parameterCurveStructureMap f hf) 1
        ((BlowupGeometry.J d).pullback g).sheaf -
      eulerCharacteristic (CurveNormalizationModel.parameterCurveStructureMap f hf) 1
        (structureSheaf (CurveNormalizationModel.parameterCurve f hf)) : ℤ) : ℝ) =
      -((BlowupGeometry.scale d).radius : ℝ) *
        CurveMargin.contactSum d y x hgen htrdeg := by
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let := hfinite f hf
  intro g hgeneric
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let z : Fin (d.m+1) → E := Fin.cases y x
  let hz := CurveGeometry.nonconstant_coordinates z hgen htrdeg
  have h := compactIdeal_degree_eq_neg_contact_sum f hf d.centerY d.centerY_ne_zero
    d.curveCenters d.fullCenters_injective
    (BlowupGeometry.logCutoff d) (BlowupGeometry.scale d).jetPowers
    (BlowupGeometry.scale d).jetPowers_pos d.curveJetWeights d.curveJetWeights_pos
    (BlowupGeometry.scale d).radius (BlowupGeometry.scale d).jetPowers_eq
    (BlowupGeometry.logCutoff_strict d) (BlowupGeometry.affineChart d)
    (BlowupGeometry.compactificationStructureMap d)
    (BlowupGeometry.affineChart_over d)
    (BlowupGeometry.projection d) (BlowupGeometry.J d)
    (BlowupGeometry.exceptionalInclusion d)
    (BlowupGeometry.exceptional_presents d) g z hz hgeneric hres hfinite
  change _ = -((BlowupGeometry.scale d).radius : ℝ) *
    ∑ p ∈ CurveContactFamily.places hfinite z d.centerY d.curveCenters hz,
      (CurveContactFamily.contact hres hfinite z d.centerY d.centerY_ne_zero d.curveCenters hz d.curveJetWeights p : ℝ)
  exact_mod_cast h


end LogarithmExtension.ExceptionalDegree
