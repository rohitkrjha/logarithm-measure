import LogarithmExtension.CompatibleLogNonTorsion

/-!
# The complete compatible-embedding irrationality bound

For a number field F of degree d, nonzero algebraic slope gamma, nonzero
real x, and s compatible embeddings satisfying exp(sigma(gamma)*x)=sigma(xi),
the irrationality exponent of x is between 2 and 2d/s. Both geometric
branches, including roots of unity, are supplied below. There is no rank,
determinant, analytic-estimate, or irrationality hypothesis in the endpoint.
-/

noncomputable section
namespace LogarithmExtension.CompatibleLog

theorem commonFiberInterpolation : CommonFiberInterpolationStatement :=
  Geometry.commonFiberGlobalInterpolation

theorem eventual_lower_bound (base : Base) :
    EventualLowerBound base.value (2 * base.ratio) :=
  eventual_lower_bound_of_commonFiber_interpolation commonFiberInterpolation base

theorem irrational (base : Base) : Irrational base.value :=
  irrational_of_eventualLowerBound (eventual_lower_bound base)

theorem irrationalityExponent_bounds (base : Base) :
    2 ≤ OAI.PiExponent.irrationalityExponent base.value ∧
      OAI.PiExponent.irrationalityExponent base.value ≤ 2 * base.ratio :=
  ⟨two_le_irrationalityExponent_of_eventualLowerBound (eventual_lower_bound base),
    irrationalityExponent_le_of_eventualLowerBound (eventual_lower_bound base)⟩

theorem approximation_bound (base : Base) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-(2 * base.ratio + epsilon)) ≤
        |base.value - (p : ℝ) / (q : ℝ)| :=
  eventual_lower_bound base (2 * base.ratio + epsilon) (by linarith)

theorem irrationalityExponent_eq_two_of_count_eq_degree (base : Base)
    (hcount : base.goodCount = base.degree) :
    OAI.PiExponent.irrationalityExponent base.value = 2 := by
  have hr : base.ratio = 1 := by
    rw [Base.ratio, hcount, div_self base.degree_pos.ne']
  apply LogarithmExtension.irrationalityExponent_eq_two
  simpa only [hr, mul_one] using eventual_lower_bound base

/-- The unbundled mathematical data; in particular, no interpolation input. -/
def ofCompatibility (F : Type) [Field F] [NumberField F]
    (gamma xi : F) (x : ℝ) (hgamma : gamma ≠ 0) (hx : x ≠ 0)
    (S : Finset (F →ₐ[ℚ] ℂ)) (hS : S.Nonempty)
    (hcompatible : ∀ sigma ∈ S, Complex.exp (sigma gamma * (x : ℂ)) = sigma xi) : Base where
  carrier := F
  element := xi
  slope := gamma
  slope_ne_zero := hgamma
  value := x
  value_ne_zero := hx
  good := S
  good_nonempty := hS
  compatible := hcompatible

theorem compatible_embedding_eventual_lower_bound
    (F : Type) [Field F] [NumberField F]
    (gamma xi : F) (x : ℝ) (hgamma : gamma ≠ 0) (hx : x ≠ 0)
    (S : Finset (F →ₐ[ℚ] ℂ)) (hS : S.Nonempty)
    (hcompatible : ∀ sigma ∈ S, Complex.exp (sigma gamma * (x : ℂ)) = sigma xi) :
    EventualLowerBound x (2 * (Module.finrank ℚ F : ℝ) / (S.card : ℝ)) := by
  have h := eventual_lower_bound (ofCompatibility F gamma xi x hgamma hx S hS hcompatible)
  change EventualLowerBound x (2 * ((Module.finrank ℚ F : ℝ) / (S.card : ℝ))) at h
  simpa only [mul_div_assoc] using h

theorem compatible_embedding_irrationalityExponent_bounds
    (F : Type) [Field F] [NumberField F]
    (gamma xi : F) (x : ℝ) (hgamma : gamma ≠ 0) (hx : x ≠ 0)
    (S : Finset (F →ₐ[ℚ] ℂ)) (hS : S.Nonempty)
    (hcompatible : ∀ sigma ∈ S, Complex.exp (sigma gamma * (x : ℂ)) = sigma xi) :
    2 ≤ OAI.PiExponent.irrationalityExponent x ∧
      OAI.PiExponent.irrationalityExponent x ≤
        2 * (Module.finrank ℚ F : ℝ) / (S.card : ℝ) := by
  have h := compatible_embedding_eventual_lower_bound F gamma xi x hgamma hx S hS hcompatible
  exact ⟨two_le_irrationalityExponent_of_eventualLowerBound h,
    irrationalityExponent_le_of_eventualLowerBound h⟩

/-- If every complex embedding is compatible, the bound is exactly two. -/
theorem all_embeddings_irrationalityExponent_eq_two
    (F : Type) [Field F] [NumberField F]
    (gamma xi : F) (x : ℝ) (hgamma : gamma ≠ 0) (hx : x ≠ 0)
    (hcompatible : ∀ sigma : F →ₐ[ℚ] ℂ,
      Complex.exp (sigma gamma * (x : ℂ)) = sigma xi) :
    OAI.PiExponent.irrationalityExponent x = 2 := by
  classical
  have hcard : Fintype.card (F →ₐ[ℚ] ℂ) = Module.finrank ℚ F := by simp
  have hS : (Finset.univ : Finset (F →ₐ[ℚ] ℂ)).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_univ, hcard]
    exact Module.finrank_pos
  let base := ofCompatibility F gamma xi x hgamma hx Finset.univ
    hS (fun sigma _ => hcompatible sigma)
  apply irrationalityExponent_eq_two_of_count_eq_degree base
  change ((Finset.univ : Finset (F →ₐ[ℚ] ℂ)).card : ℝ) = (Module.finrank ℚ F : ℝ)
  exact_mod_cast (Finset.card_univ.trans hcard)

#print axioms eventual_lower_bound
#print axioms compatible_embedding_irrationalityExponent_bounds
#print axioms all_embeddings_irrationalityExponent_eq_two

end LogarithmExtension.CompatibleLog
