import LogarithmExtension.NumberFieldNorm
import LogarithmExtension.MatrixArithmetic

/-!
# Logarithmic jet matrices over number fields

The matrix is first defined over its number field, then transported along
each complex embedding. This keeps all conjugate estimates attached to
the same algebraic determinant.
-/

noncomputable section
namespace LogarithmExtension.NumberFieldArithmetic

open scoped BigOperators NumberField
open OAI.PiExponent

variable {F : Type*} [Field F] [NumberField F]

def logTrunc (F : Type*) [Field F] [NumberField F] (T : ℕ) : Polynomial F :=
  PowerSeries.trunc T (PowerSeries.log F)

def entry {m : ℕ} (ξ γ : F) (T q : Fin m → ℕ) (p : Fin m → ℤ)
    (j s : ℕ) (β : Fin m → ℕ) (h : ℕ) (α : Fin m → ℕ) : F :=
  ξ ^ (j * h) * (∏ i, ((α i).choose (β i) : F)) *
    (((1 + Polynomial.X) ^ h * ∏ i,
      (Polynomial.C ((j : F) * (γ * (p i : F) / (q i : F))) + logTrunc F (T i)) ^
        (α i - β i)).coeff s)

theorem map_logTrunc (σ : F →ₐ[ℚ] ℂ) (T : ℕ) :
    (logTrunc F T).map σ.toRingHom = InterpolationMatrix.truncatedLog T := by
  rw [logTrunc, ← PowerSeries.trunc_map, PowerSeries.map_log]
  rfl

theorem map_entry {m : ℕ} (σ : F →ₐ[ℚ] ℂ) (ξ γ : F)
    (T q : Fin m → ℕ) (p : Fin m → ℤ)
    (j s : ℕ) (β : Fin m → ℕ) (h : ℕ) (α : Fin m → ℕ) :
    σ (entry ξ γ T q p j s β h α) =
      AnalyticTranslation.matrixEntry (σ ξ)
        (fun i => σ γ * (p i : ℂ) / (q i : ℂ)) T j s β h α := by
  rw [entry, AnalyticTranslation.matrixEntry, InterpolationMatrix.entry_eq_binomial_product]
  simp only [map_mul, map_pow, map_prod, map_natCast]
  have hcoeff (P : Polynomial F) : σ (P.coeff s) = (P.map σ.toRingHom).coeff s :=
    (Polynomial.coeff_map _ _).symm
  rw [hcoeff]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_X, Polynomial.map_prod, Polynomial.map_C,
    Polynomial.map_natCast, map_mul, map_natCast, map_div₀, map_intCast,
    map_logTrunc]
  simp only [mul_assoc]
  rfl

theorem entry_eq_zero_of_not_le {m : ℕ} (ξ γ : F)
    (T q : Fin m → ℕ) (p : Fin m → ℤ)
    (j s : ℕ) (β : Fin m → ℕ) (h : ℕ) (α : Fin m → ℕ)
    (hβα : ¬ ∀ i, β i ≤ α i) : entry ξ γ T q p j s β h α = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hβα
  have hc : (∏ i, ((α i).choose (β i) : F)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hi)]
  simp only [entry, hc, mul_zero, zero_mul]

def integralPolynomials (F : Type*) [Field F] [NumberField F] : Subring (Polynomial F) :=
  (Polynomial.mapRingHom (algebraMap (𝓞 F) F)).range

theorem mem_integralPolynomials_iff (P : Polynomial F) :
    P ∈ integralPolynomials F ↔ ∀ k, IsIntegral ℤ (P.coeff k) := by
  rw [integralPolynomials, Polynomial.mem_map_range]
  constructor
  · intro h k
    obtain ⟨z, hz⟩ := h k
    rw [← hz]
    exact z.2
  · intro h k
    exact ⟨⟨P.coeff k, h k⟩, rfl⟩

theorem integralPolynomials_C {z : F} (hz : IsIntegral ℤ z) :
    Polynomial.C z ∈ integralPolynomials F := by
  refine ⟨Polynomial.C (⟨z, hz⟩ : 𝓞 F), ?_⟩
  change (Polynomial.C (⟨z, hz⟩ : 𝓞 F)).map (algebraMap (𝓞 F) F) = Polynomial.C z
  erw [Polynomial.map_C]
  rfl

theorem integralPolynomials_natCast (n : ℕ) :
    Polynomial.C (n : F) ∈ integralPolynomials F :=
  integralPolynomials_C (isIntegral_natCast n)

theorem lcm_mul_log_coeff_integral (T k : ℕ) (hk : k ≤ T) :
    IsIntegral ℤ ((Nat.lcmUpto T : F) * PowerSeries.coeff k (PowerSeries.log F)) := by
  by_cases hk0 : k = 0
  · simp only [hk0, PowerSeries.coeff_log, ite_true, mul_zero]
    exact isIntegral_zero
  obtain ⟨n, hn⟩ := Arithmetic.dvd_lcmUpto_of_pos_le (Nat.pos_of_ne_zero hk0) hk
  have he : (Nat.lcmUpto T : F) * PowerSeries.coeff k (PowerSeries.log F) =
      (-1 : F) ^ (k + 1) * (n : F) := by
    rw [PowerSeries.coeff_log, ite_eq_right hk0, hn]
    have hkF : (k : F) ≠ 0 := by exact_mod_cast hk0
    simp only [map_div₀, map_pow, map_neg, map_one, map_natCast, Nat.cast_mul]
    field_simp
  rw [he]
  exact ((isIntegral_one : IsIntegral ℤ (1 : F)).neg.pow _).mul (isIntegral_natCast n)

theorem cleared_logTrunc_integral (T : ℕ) :
    Polynomial.C (Nat.lcmUpto T : F) * logTrunc F T ∈ integralPolynomials F := by
  apply (mem_integralPolynomials_iff _).mpr
  intro k
  rw [Polynomial.coeff_C_mul, logTrunc, PowerSeries.coeff_trunc]
  split_ifs with hk
  · exact lcm_mul_log_coeff_integral T k hk.le
  · simp only [mul_zero]
    exact isIntegral_zero

theorem cleared_shifted_logTrunc_integral (T q : ℕ) (z : F) (hz : IsIntegral ℤ z) :
    Polynomial.C (Nat.lcmUpto T : F) *
      (Polynomial.C z + Polynomial.C (q : F) * logTrunc F T) ∈ integralPolynomials F := by
  have h := (integralPolynomials F).add_mem
    ((integralPolynomials F).mul_mem (integralPolynomials_natCast (Nat.lcmUpto T))
      (integralPolynomials_C hz))
    ((integralPolynomials F).mul_mem (integralPolynomials_natCast q)
      (cleared_logTrunc_integral T))
  convert h using 1
  ring

theorem cleared_polynomial_power_integral (L e d : ℕ) (P : Polynomial F) (hd : d ≤ e)
    (hP : Polynomial.C (L : F) * P ∈ integralPolynomials F) :
    Polynomial.C ((L : F) ^ e) * P ^ d ∈ integralPolynomials F := by
  have h := (integralPolynomials F).mul_mem
    ((integralPolynomials F).pow_mem (integralPolynomials_natCast L) (e - d))
    ((integralPolynomials F).pow_mem hP d)
  have he : e = (e - d) + d := (Nat.sub_add_cancel hd).symm
  rw [he, map_pow, pow_add]
  simpa only [mul_pow, mul_assoc] using h

theorem cleared_polynomial_product_integral {ι : Type*} (s : Finset ι)
    (L e d : ι → ℕ) (P : ι → Polynomial F) (hd : ∀ i ∈ s, d i ≤ e i)
    (hP : ∀ i ∈ s, Polynomial.C (L i : F) * P i ∈ integralPolynomials F) :
    Polynomial.C (∏ i ∈ s, (L i : F) ^ e i) * (∏ i ∈ s, P i ^ d i) ∈
      integralPolynomials F := by
  have h := (integralPolynomials F).prod_mem (fun i hi =>
    cleared_polynomial_power_integral (L i) (e i) (d i) (P i) (hd i hi) (hP i hi))
  simpa only [← Finset.prod_mul_distrib, map_prod] using h

theorem common_denominator_coeff_integral {ι : Type*} (s : Finset ι)
    (L e d : ι → ℕ) (f : ι → Polynomial F) (P : Polynomial F)
    (hP : P ∈ integralPolynomials F) (hd : ∀ i ∈ s, d i ≤ e i)
    (hf : ∀ i ∈ s, Polynomial.C (L i : F) * f i ∈ integralPolynomials F) (k : ℕ) :
    IsIntegral ℤ ((∏ i ∈ s, (L i : F) ^ e i) *
      (P * ∏ i ∈ s, f i ^ d i).coeff k) := by
  have h := (integralPolynomials F).mul_mem hP
    (cleared_polynomial_product_integral s L e d f hd hf)
  have he : P * (Polynomial.C (∏ i ∈ s, (L i : F) ^ e i) * ∏ i ∈ s, f i ^ d i) =
      Polynomial.C (∏ i ∈ s, (L i : F) ^ e i) * (P * ∏ i ∈ s, f i ^ d i) := by ring
  rw [he] at h
  simpa only [Polynomial.coeff_C_mul] using (mem_integralPolynomials_iff _).mp h k

theorem scaled_shifted_logTrunc_integral (D T q : ℕ) (z : F)
    (hz : IsIntegral ℤ ((D : F) * z)) :
    Polynomial.C ((D * Nat.lcmUpto T : ℕ) : F) *
      (Polynomial.C z + Polynomial.C (q : F) * logTrunc F T) ∈ integralPolynomials F := by
  have h := cleared_shifted_logTrunc_integral T (D * q) ((D : F) * z) hz
  convert h using 1
  push_cast
  simp only [map_mul]
  ring

omit [NumberField F] in
theorem scalar_product_mul_coeff {m : ℕ} (q : Fin m → F)
    (d : Fin m → ℕ) (P : Polynomial F) (f : Fin m → Polynomial F) (s : ℕ) :
    (∏ i, q i ^ d i) * (P * ∏ i, f i ^ d i).coeff s =
      (P * ∏ i, (Polynomial.C (q i) * f i) ^ d i).coeff s := by
  have he : P * ∏ i, (Polynomial.C (q i) * f i) ^ d i =
      Polynomial.C (∏ i, q i ^ d i) * (P * ∏ i, f i ^ d i) := by
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    ring
  rw [he, Polynomial.coeff_C_mul]

omit [NumberField F] in
theorem clear_center_power (ξ : F) (D : ℕ) (hξ : IsIntegral ℤ ((D : F) * ξ))
    (J j h : ℕ) (hj : j ≤ J) :
    IsIntegral ℤ ((D : F) ^ (J * h) * ξ ^ (j * h)) := by
  have he : (D : F) ^ (J * h) * ξ ^ (j * h) =
      ((D : F) * ξ) ^ (j * h) * (D : F) ^ ((J - j) * h) := by
    have hJ : J = j + (J - j) := (Nat.add_sub_of_le hj).symm
    nth_rw 1 [hJ]
    rw [Nat.add_mul, pow_add, mul_pow]
    ring
  rw [he]
  exact (hξ.pow _).mul ((isIntegral_natCast D).pow _)

/-- Denominator clearing for the actual number-field entry. The uniform
slope denominator is conservative: its later logarithmic cost is
log(Dgamma) * sum_i 1/w_i, which tends to zero with the separated weights. -/
theorem entry_cleared {m : ℕ} (ξ γ : F) (Dξ Dγ : ℕ)
    (hξ : IsIntegral ℤ ((Dξ : F) * ξ)) (hγ : IsIntegral ℤ ((Dγ : F) * γ))
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (J j s h : ℕ) (hj : j ≤ J) (β α : Fin m → ℕ) (hα : ∀ i, α i ≤ e i) :
    IsIntegral ℤ ((∏ i, ((Dγ * Nat.lcmUpto (T i) : ℕ) : F) ^ e i) *
      (∏ i, (q i : F) ^ α i) / (∏ i, (q i : F) ^ β i) *
      (Dξ : F) ^ (J * h) * entry ξ γ T q p j s β h α) := by
  classical
  by_cases hβα : ∀ i, β i ≤ α i
  swap
  · rw [entry_eq_zero_of_not_le ξ γ T q p j s β h α hβα, mul_zero]
    exact isIntegral_zero
  have hqF : ∀ i, (q i : F) ≠ 0 := fun i => by exact_mod_cast hq i
  have hratio : (∏ i, (q i : F) ^ α i) / (∏ i, (q i : F) ^ β i) =
      ∏ i, (q i : F) ^ (α i - β i) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simpa only [div_eq_mul_inv] using (pow_sub₀ (q i : F) (hqF i) (hβα i)).symm
  have hz (i : Fin m) : Polynomial.C (q i : F) *
      (Polynomial.C ((j : F) * (γ * (p i : F) / (q i : F))) + logTrunc F (T i)) =
      Polynomial.C ((j : F) * γ * (p i : F)) +
        Polynomial.C (q i : F) * logTrunc F (T i) := by
    rw [mul_add, ← map_mul]
    congr 1
    apply congrArg Polynomial.C
    field_simp [hqF i]
  have hP : ((1 + Polynomial.X) ^ h : Polynomial F) ∈ integralPolynomials F := by
    apply (integralPolynomials F).pow_mem
    apply (integralPolynomials F).add_mem (integralPolynomials F).one_mem
    exact ⟨Polynomial.X, by simp⟩
  have hshift (i : Fin m) :
      IsIntegral ℤ ((Dγ : F) * ((j : F) * γ * (p i : F))) := by
    have hh := (hγ.mul (isIntegral_natCast j)).mul (isIntegral_intCast (p i))
    convert hh using 1
    ring
  have hclear := common_denominator_coeff_integral Finset.univ
    (fun i => Dγ * Nat.lcmUpto (T i)) e (fun i => α i - β i)
    (fun i => Polynomial.C ((j : F) * γ * (p i : F)) +
      Polynomial.C (q i : F) * logTrunc F (T i)) ((1 + Polynomial.X) ^ h) hP
    (fun i _ => (Nat.sub_le (α i) (β i)).trans (hα i))
    (fun i _ => scaled_shifted_logTrunc_integral Dγ (T i) (q i) _ (hshift i)) s
  have hscalar := scalar_product_mul_coeff (fun i => (q i : F)) (fun i => α i - β i)
    ((1 + Polynomial.X) ^ h)
    (fun i => Polynomial.C ((j : F) * (γ * (p i : F) / (q i : F))) +
      logTrunc F (T i)) s
  simp_rw [hz] at hscalar
  rw [← hscalar] at hclear
  have hchoose : IsIntegral ℤ (∏ i, ((α i).choose (β i) : F)) :=
    IsIntegral.prod _ (fun i _ => isIntegral_natCast _)
  have hbase := clear_center_power ξ Dξ hξ J j h hj
  have hall := hbase.mul (hchoose.mul hclear)
  rw [mul_div_assoc, hratio, entry]
  convert hall using 1
  ring

#print axioms entry_cleared

end LogarithmExtension.NumberFieldArithmetic
