import LogarithmExtension.MatrixArithmetic

/-! Arithmetic normalization for the actual base-three matrix.
The generic denominator and row/column cost estimates are reused unchanged;
the cleared entries retain the integer factor 3^(j*h).
Adapted arithmetic-normalization proofs are Apache-2.0. -/

noncomputable section
namespace LogarithmExtension.LogThree.MatrixArithmetic

open OAI OAI.PiExponent
open scoped BigOperators

export OAI.PiExponent.MatrixArithmetic
  (logWeights columnScale rowScale denominator truncationOrders
   columnScale_pos rowScale_pos denominator_pos log_columnScale log_rowScale
   log_denominator_le rowWeightedSum meanRowWeight rowCost columnCost
   actual_row_card_pos ceil_log_weight_pos column_coordinate_le_floor
   column_log_cost_le_H selected_column_log_cost_le row_weighted_cost_le
   all_row_log_cost_lower meanRowWeight_nonneg meanRowWeight_le_theta)

def rationalCenters {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ) : Fin m → ℂ :=
  fun i => (p i : ℂ) / (q i : ℂ)

def matrix {m : ℕ} (K : ℕ) (w0 v0 θ F H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ) :
    Matrix (InterpolationMatrix.Row K v0 θ (logWeights q) H)
      (InterpolationMatrix.Column w0 (logWeights q) H) ℂ :=
  fun row col => AnalyticTranslation.matrixEntry 3 (rationalCenters p q)
    (truncationOrders q F v0) row.1.val (row.2.val 0) (fun i => row.2.val i.succ)
    (col.val 0) (fun i => col.val i.succ)

def selectedMinor {m : ℕ} (K : ℕ) (w0 v0 θ F H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H) :
    Matrix (InterpolationMatrix.Row K v0 θ (logWeights q) H)
      (InterpolationMatrix.Row K v0 θ (logWeights q) H) ℂ :=
  (matrix K w0 v0 θ F H p q).submatrix id selection

theorem selectedMinor_entries_gaussian {m K : ℕ} {w0 v0 θ F H : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (ρ σ : InterpolationMatrix.Row K v0 θ (logWeights q) H) :
    (denominator q (truncationOrders q F v0) H : ℂ) *
      (rowScale q (fun i => ρ.2.1 i.succ) : ℂ) *
        ((columnScale q (fun i => (selection σ).1 i.succ) : ℂ) *
          selectedMinor K w0 v0 θ F H p q selection ρ σ) ∈
        GaussianInt.toComplex.range := by
  have hw : ∀ i, 0 < logWeights q i := fun i => ceil_log_weight_pos (hq i)
  have he := LogarithmExtension.MatrixArithmetic.entry_cleared 3 1 (by norm_num)
    (truncationOrders q F v0) q (fun i => ⌊H / logWeights q i⌋₊) p
    (fun i => by have := hq i; omega) ρ.1.val 0 (ρ.2.1 0) ((selection σ).1 0)
    (fun i => ρ.2.1 i.succ) (fun i => (selection σ).1 i.succ)
    (column_coordinate_le_floor hw0 hw (selection σ))
  simp only [Int.cast_one, Int.cast_ofNat, div_one, Nat.add_zero, one_pow, mul_one] at he
  simp only [denominator, rowScale, columnScale, selectedMinor,
    matrix,
    Matrix.submatrix_apply, id_eq,
    Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_natCast,
    Complex.ofReal_inv]
  have hcenters : rationalCenters p q =
      (fun i => (p i : ℂ) / (q i : ℂ)) := rfl
  rw [← hcenters] at he
  convert he using 1
  ring

theorem selectedMinor_clearing_bound {m K : ℕ} {w0 v0 θ F H : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (selectedMinor K w0 v0 θ F H p q selection).det ≠ 0) :
    -(Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) *
      Real.log (denominator q (truncationOrders q F v0) H) -
      columnCost q selection + rowCost K v0 θ q H ≤
      Real.log ‖(selectedMinor K w0 v0 θ F H p q selection).det‖ := by
  have hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le (by decide) (hq i)
  have hc := Arithmetic.cleared_det_log_bound_with_denominator
    (selectedMinor K w0 v0 θ F H p q selection)
    (fun ρ => rowScale q (fun i => ρ.2.1 i.succ))
    (fun σ => columnScale q (fun i => (selection σ).1 i.succ))
    (denominator q (truncationOrders q F v0) H)
    (denominator_pos _ _ _) (fun ρ => rowScale_pos hqpos _)
    (fun σ => columnScale_pos hqpos _) hdet
    (selectedMinor_entries_gaussian p q hq hw0 selection)
  simp only [log_rowScale hqpos, log_columnScale hqpos,
    Finset.sum_neg_distrib, sub_neg_eq_add] at hc
  dsimp [columnCost, rowCost]
  linarith

theorem selectedMinor_arithmetic_lower_bound {m K : ℕ} {w0 v0 θ F H wmin : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hF : 0 ≤ F) (hH : 0 < H) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ logWeights q i)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (selectedMinor K w0 v0 θ F H p q selection).det ≠ 0) :
    -(1 - meanRowWeight K v0 θ q H) -
      (Arithmetic.lcmConstant * F * m / v0 +
        Arithmetic.lcmConstant * ∑ i, 1 / logWeights q i + θ / wmin) ≤
      Real.log ‖(selectedMinor K w0 v0 θ F H p q selection).det‖ /
        ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H) := by
  have hw : ∀ i, 0 < logWeights q i := fun i => ceil_log_weight_pos (hq i)
  have hM : 0 < (Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) := by
    exact_mod_cast actual_row_card_pos hK hv0 hθ hH hw
  apply Arithmetic.normalized_arithmetic_bound _ _ _ _ _ _ _ _ _ hM hH
  · exact selectedMinor_clearing_bound p q hq hw0 selection hdet
  · exact log_denominator_le F v0 H hF hv0 hH hw
  · exact selected_column_log_cost_le q hq hw0 selection
  · have hrow (ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H) :=
      Arithmetic.row_log_cost_lower Finset.univ (fun i => ρ.2.1 i.succ) q
        wmin (H * θ) hmin (fun i _ => hwmin i)
        (row_weighted_cost_le hv0 hθ hw ρ)
    have hr := Finset.sum_le_sum (s := Finset.univ) (fun ρ _ => hrow ρ)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hr
    have hb :
        (Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H *
          meanRowWeight K v0 θ q H = rowWeightedSum K v0 θ q H := by
      unfold meanRowWeight
      field_simp [(mul_pos hM hH).ne']
    rw [hb]
    simpa only [rowWeightedSum, rowCost, logWeights, mul_div_assoc, mul_assoc] using hr


end LogarithmExtension.LogThree.MatrixArithmetic

