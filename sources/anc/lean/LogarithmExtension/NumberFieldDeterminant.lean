import LogarithmExtension.NumberFieldMatrix

/-! The norm lower bound for actual logarithmic jet determinants over a
number field, including both algebraic denominator costs. -/

noncomputable section
namespace LogarithmExtension.NumberFieldArithmetic

open scoped BigOperators NumberField

variable {F : Type*} [Field F] [NumberField F]

theorem map_entry_determinant {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (σ : F →ₐ[ℚ] ℂ) (ξ γ : F) (T q : Fin m → ℕ) (p : Fin m → ℤ)
    (j s h : ι → ℕ) (β α : ι → Fin m → ℕ) :
    σ (Matrix.det (fun r c => entry ξ γ T q p (j r) (s r) (β r) (h c) (α c))) =
      Matrix.det (fun r c => AnalyticTranslation.matrixEntry (σ ξ)
        (fun i => σ γ * (p i : ℂ) / (q i : ℂ)) T (j r) (s r) (β r) (h c) (α c)) := by
  have he := RingHom.map_det σ.toRingHom
    (fun r c => entry ξ γ T q p (j r) (s r) (β r) (h c) (α c))
  calc
    _ = Matrix.det (fun r c => σ (entry ξ γ T q p (j r) (s r) (β r) (h c) (α c))) := he
    _ = _ := by
      congr 1
      funext r c
      exact map_entry σ ξ γ T q p (j r) (s r) (β r) (h c) (α c)

theorem determinant_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ξ γ : F) (Dξ Dγ : ℕ) (hDξ : 0 < Dξ) (hDγ : 0 < Dγ)
    (hξ : IsIntegral ℤ ((Dξ : F) * ξ)) (hγ : IsIntegral ℤ ((Dγ : F) * γ))
    {m : ℕ} (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, 0 < q i)
    (J : ℕ) (j s h : ι → ℕ) (hj : ∀ r, j r ≤ J)
    (β α : ι → Fin m → ℕ) (hα : ∀ c i, α c i ≤ e i)
    (hne : Matrix.det (fun r c => entry ξ γ T q p (j r) (s r) (β r) (h c) (α c)) ≠ 0) :
    -(Module.finrank ℚ F : ℝ) *
      ((Fintype.card ι : ℝ) * Real.log (∏ i, ((Dγ * Nat.lcmUpto (T i) : ℕ) : ℝ) ^ e i) +
        (∑ c : ι, (((J * h c : ℕ) : ℝ) * Real.log (Dξ : ℝ) +
          ∑ i, (α c i : ℝ) * Real.log (q i : ℝ))) -
        (∑ r : ι, ∑ i, (β r i : ℝ) * Real.log (q i : ℝ))) ≤
      ∑ σ : F →ₐ[ℚ] ℂ,
        Real.log ‖σ (Matrix.det (fun r c =>
          entry ξ γ T q p (j r) (s r) (β r) (h c) (α c)))‖ := by
  let A : Matrix ι ι F := fun r c => entry ξ γ T q p (j r) (s r) (β r) (h c) (α c)
  let D : ℚ := ∏ i, ((Dγ * Nat.lcmUpto (T i) : ℕ) : ℚ) ^ e i
  let row : ι → ℚ := fun r => (∏ i, (q i : ℚ) ^ β r i)⁻¹
  let col : ι → ℚ := fun c => (Dξ : ℚ) ^ (J * h c) * ∏ i, (q i : ℚ) ^ α c i
  have hqQ : ∀ i, (0 : ℚ) < q i := fun i => by exact_mod_cast hq i
  have hDξQ : (0 : ℚ) < Dξ := by exact_mod_cast hDξ
  have hDpos : 0 < D := by
    apply Finset.prod_pos
    intro i _
    apply pow_pos
    exact_mod_cast Nat.mul_pos hDγ (Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero (T i)))
  have hrow : ∀ r, 0 < row r := fun r =>
    inv_pos.mpr (Finset.prod_pos (fun i _ => pow_pos (hqQ i) _))
  have hcol : ∀ c, 0 < col c := fun c =>
    mul_pos (pow_pos hDξQ _) (Finset.prod_pos (fun i _ => pow_pos (hqQ i) _))
  have hh := cleared_matrix_log_bound_with_denominator A row col D hDpos hrow hcol hne (by
    intro r c
    have he := entry_cleared ξ γ Dξ Dγ hξ hγ T q e p (fun i => (hq i).ne')
      J (j r) (s r) (h c) (hj r) (β r) (α c) (hα c)
    dsimp only [D, row, col, A]
    simp only [Rat.cast_prod, Rat.cast_pow, Rat.cast_natCast, Rat.cast_inv, Rat.cast_mul]
    convert he using 1
    ring)
  have hqR : ∀ i, (0 : ℝ) < q i := fun i => by exact_mod_cast hq i
  have hDξR : (0 : ℝ) < Dξ := by exact_mod_cast hDξ
  have hrowlog (r : ι) : Real.log (row r : ℝ) =
      -∑ i, (β r i : ℝ) * Real.log (q i : ℝ) := by
    simp only [row, Rat.cast_inv, Rat.cast_prod, Rat.cast_pow, Rat.cast_natCast,
      Real.log_inv, Real.log_prod (fun i _ => pow_ne_zero _ (hqR i).ne'), Real.log_pow]
  have hcollog (c : ι) : Real.log (col c : ℝ) =
      ((J * h c : ℕ) : ℝ) * Real.log (Dξ : ℝ) +
        ∑ i, (α c i : ℝ) * Real.log (q i : ℝ) := by
    simp only [col, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_prod,
      Real.log_mul (pow_ne_zero _ hDξR.ne')
        (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hqR i).ne')),
      Real.log_pow, Real.log_prod (fun i _ => pow_ne_zero _ (hqR i).ne')]
  simp only [hrowlog, hcollog, Finset.sum_neg_distrib] at hh
  dsimp only [D, A] at hh
  simp only [Rat.cast_prod, Rat.cast_pow, Rat.cast_natCast] at hh
  convert hh using 1
  ring

#print axioms determinant_lower_bound

end LogarithmExtension.NumberFieldArithmetic
