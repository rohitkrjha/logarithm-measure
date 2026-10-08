import LogarithmExtension.AnalyticTranslation
import OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic

/-!
# Denominator clearing for logarithmic power centres

The unit-centre entry proof adapts the pinned OpenAI MatrixArithmetic source
(Apache-2.0), with real rational centres instead of imaginary rational ones.
A uniform extra column multiplier clears every rational-base centre.
-/

noncomputable section
namespace LogarithmExtension.MatrixArithmetic

open OAI OAI.PiExponent OAI.PiExponent.InterpolationMatrix
open scoped BigOperators

theorem unit_entry_cleared {m : ℕ}
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (j s h : ℕ) (β α : Fin m → ℕ) (hα : ∀ i, α i ≤ e i) :
    (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) *
      entry (fun i => (p i : ℂ) / (q i : ℂ))
        (fun i => truncatedLog (T i)) j s β h α ∈ GaussianInt.toComplex.range := by
  classical
  by_cases hβα : ∀ i, β i ≤ α i
  swap
  · rw [entry_eq_zero_of_not_le _ _ _ _ _ _ _ hβα, mul_zero]
    exact GaussianInt.toComplex.range.zero_mem
  have hqC : ∀ i, (q i : ℂ) ≠ 0 := by
    intro i
    exact_mod_cast hq i
  have hratio : (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) =
      ∏ i, (q i : ℂ) ^ (α i - β i) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    simpa only [div_eq_mul_inv] using (pow_sub₀ (q i : ℂ) (hqC i) (hβα i)).symm
  let z : Fin m → GaussianInt := fun i => ((j : ℤ) * p i : ℤ)
  have hz (i : Fin m) : Polynomial.C (q i : ℂ) *
      (Polynomial.C ((j : ℂ) * ((p i : ℂ) / (q i : ℂ))) +
        truncatedLog (T i)) =
      Polynomial.C (z i : ℂ) + Polynomial.C (q i : ℂ) *
        PowerSeries.trunc (T i) (PowerSeries.log ℂ) := by
    rw [mul_add, ← map_mul]
    congr 1
    apply congrArg Polynomial.C
    rw [show (z i : ℂ) = (j : ℂ) * ((p i : ℂ)) from
      by simp [z]]
    field_simp [hqC i]
  have hclear := Arithmetic.shifted_truncation_product_coeff_gaussian Finset.univ
    T q e (fun i => α i - β i) z ((1 + Polynomial.X) ^ h)
    (fun i hi => (Nat.sub_le (α i) (β i)).trans (hα i)) s
  have hP : (((1 + Polynomial.X) ^ h : Polynomial GaussianInt).map GaussianInt.toComplex) =
      (1 + Polynomial.X) ^ h := by simp
  simp only [hP] at hclear
  have hchoose : (∏ i, ((α i).choose (β i) : ℂ)) ∈ GaussianInt.toComplex.range := by
    apply GaussianInt.toComplex.range.prod_mem
    intro i hi
    exact ⟨((α i).choose (β i) : GaussianInt), by simp⟩
  have hscalar := scalar_product_mul_coeff (fun i => (q i : ℂ)) (fun i => α i - β i)
    ((1 + Polynomial.X) ^ h)
    (fun i => Polynomial.C ((j : ℂ) * ((p i : ℂ) / (q i : ℂ))) +
      truncatedLog (T i)) s
  simp_rw [hz] at hscalar
  rw [mul_div_assoc, hratio, entry_eq_binomial_product]
  have he := GaussianInt.toComplex.range.mul_mem hchoose hclear
  rw [← hscalar] at he
  convert he using 1
  ring

theorem clear_complex_center_power (a b : ℤ) (hb : b ≠ 0) (j k h : ℕ) :
    (b : ℂ) ^ ((j+k)*h) * ((a : ℂ)/(b : ℂ)) ^ (j*h) =
      (a : ℂ) ^ (j*h) * (b : ℂ) ^ (k*h) := by
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  rw [Nat.add_mul, pow_add, div_pow]
  field_simp

theorem entry_cleared (a b : ℤ) (hb : b ≠ 0) {m : ℕ}
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (j k s h : ℕ) (β α : Fin m → ℕ) (hα : ∀ i, α i ≤ e i) :
    (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) *
      (b : ℂ) ^ ((j+k)*h) *
      AnalyticTranslation.matrixEntry ((a : ℂ)/(b : ℂ))
        (fun i => (p i : ℂ)/(q i : ℂ)) T j s β h α ∈ GaussianInt.toComplex.range := by
  have hc := unit_entry_cleared T q e p hq j s h β α hα
  have hf : (b : ℂ) ^ ((j+k)*h) * ((a : ℂ)/(b : ℂ)) ^ (j*h) ∈
      GaussianInt.toComplex.range := by
    rw [clear_complex_center_power a b hb]
    refine ⟨((a : GaussianInt) ^ (j*h)) * ((b : GaussianInt) ^ (k*h)), ?_⟩
    simp
  have hh := GaussianInt.toComplex.range.mul_mem hc hf
  unfold AnalyticTranslation.matrixEntry
  convert hh using 1
  ring

/-- The exponent J is fixed for all rows j ≤ J, so the extra factor is genuinely
a column scaling, even though the original base factor depends on both j and h. -/
theorem entry_cleared_uniform (a b : ℤ) (hb : b ≠ 0) {m : ℕ}
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (J j s h : ℕ) (hj : j ≤ J) (β α : Fin m → ℕ) (hα : ∀ i, α i ≤ e i) :
    (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) *
      (b : ℂ) ^ (J*h) *
      AnalyticTranslation.matrixEntry ((a : ℂ)/(b : ℂ))
        (fun i => (p i : ℂ)/(q i : ℂ)) T j s β h α ∈ GaussianInt.toComplex.range := by
  simpa only [Nat.add_sub_of_le hj] using
    entry_cleared a b hb T q e p hq j (J-j) s h β α hα

/-- Arithmetic lower bound for every nonzero square minor of the actual
rational-base matrix. The base-denominator cost is kept explicitly. -/
theorem determinant_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ℤ) (hb : 0 < b) {m : ℕ}
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, 0 < q i)
    (J : ℕ) (j s h : ι → ℕ) (hj : ∀ r, j r ≤ J)
    (β α : ι → Fin m → ℕ) (hα : ∀ c i, α c i ≤ e i)
    (hne : Matrix.det (fun r c => AnalyticTranslation.matrixEntry ((a : ℂ)/(b : ℂ))
      (fun i => (p i : ℂ)/(q i : ℂ)) T (j r) (s r) (β r) (h c) (α c)) ≠ 0) :
    -(Fintype.card ι : ℝ) * Real.log (∏ i, (Nat.lcmUpto (T i) : ℝ) ^ e i) -
      (∑ c : ι, (((J*h c : ℕ) : ℝ) * Real.log (b : ℝ) +
        ∑ i, (α c i : ℝ) * Real.log (q i : ℝ))) +
      (∑ r : ι, ∑ i, (β r i : ℝ) * Real.log (q i : ℝ)) ≤
      Real.log ‖Matrix.det (fun r c => AnalyticTranslation.matrixEntry ((a : ℂ)/(b : ℂ))
        (fun i => (p i : ℂ)/(q i : ℂ)) T (j r) (s r) (β r) (h c) (α c))‖ := by
  let A : Matrix ι ι ℂ := fun r c => AnalyticTranslation.matrixEntry ((a : ℂ)/(b : ℂ))
    (fun i => (p i : ℂ)/(q i : ℂ)) T (j r) (s r) (β r) (h c) (α c)
  let D : ℝ := ∏ i, (Nat.lcmUpto (T i) : ℝ) ^ e i
  let row : ι → ℝ := fun r => (∏ i, (q i : ℝ) ^ β r i)⁻¹
  let col : ι → ℝ := fun c => (b : ℝ) ^ (J*h c) * ∏ i, (q i : ℝ) ^ α c i
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : ∀ i, (0 : ℝ) < q i := fun i => by exact_mod_cast hq i
  have hD : 0 < D := by
    apply Finset.prod_pos
    intro i _
    exact pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero (T i))) _
  have hr : ∀ r, 0 < row r := fun r =>
    inv_pos.mpr (Finset.prod_pos (fun i _ => pow_pos (hqR i) _))
  have hc : ∀ c, 0 < col c := fun c =>
    mul_pos (pow_pos hbR _) (Finset.prod_pos (fun i _ => pow_pos (hqR i) _))
  have hh := Arithmetic.cleared_det_log_bound_with_denominator A row col D hD hr hc hne (by
    intro r c
    have he := entry_cleared_uniform a b hb.ne' T q e p (fun i => (hq i).ne')
      J (j r) (s r) (h c) (hj r) (β r) (α c) (hα c)
    dsimp [D, row, col, A]
    simp only [Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_natCast,
      Complex.ofReal_intCast, Complex.ofReal_inv, Complex.ofReal_mul]
    convert he using 1
    ring)
  have hrow (r : ι) : Real.log (row r) = -∑ i, (β r i : ℝ)*Real.log (q i : ℝ) := by
    dsimp only [row]
    rw [Real.log_inv, Real.log_prod (fun i _ => pow_ne_zero _ (hqR i).ne')]
    simp only [Real.log_pow]
  have hcol (c : ι) : Real.log (col c) =
      ((J*h c : ℕ) : ℝ)*Real.log (b : ℝ) + ∑ i, (α c i : ℝ)*Real.log (q i : ℝ) := by
    dsimp only [col]
    rw [Real.log_mul (pow_ne_zero _ hbR.ne')
      (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hqR i).ne')),
      Real.log_pow, Real.log_prod (fun i _ => pow_ne_zero _ (hqR i).ne')]
    simp only [Real.log_pow]
  simp only [hrow, hcol, Finset.sum_neg_distrib] at hh
  dsimp only [A, D] at hh
  linarith

#print axioms entry_cleared_uniform
#print axioms determinant_lower_bound

end LogarithmExtension.MatrixArithmetic
