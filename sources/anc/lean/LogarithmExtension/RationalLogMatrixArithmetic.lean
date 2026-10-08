import LogarithmExtension.MatrixArithmetic
import LogarithmExtension.RationalLogBase

/-! Rational-base determinant arithmetic with an explicit uniform base-denominator
multiplier. Its normalized cost is log(b)*K/w0. -/

noncomputable section
namespace LogarithmExtension.RationalLog.MatrixArithmetic

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

def matrix (r : Base) {m : ℕ} (K : ℕ) (w0 v0 θ F H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ) :
    Matrix (InterpolationMatrix.Row K v0 θ (logWeights q) H)
      (InterpolationMatrix.Column w0 (logWeights q) H) ℂ :=
  fun row col => AnalyticTranslation.matrixEntry r.complexValue (rationalCenters p q)
    (truncationOrders q F v0) row.1.val (row.2.val 0) (fun i => row.2.val i.succ)
    (col.val 0) (fun i => col.val i.succ)

def selectedMinor (r : Base) {m : ℕ} (K : ℕ) (w0 v0 θ F H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H) :
    Matrix (InterpolationMatrix.Row K v0 θ (logWeights q) H)
      (InterpolationMatrix.Row K v0 θ (logWeights q) H) ℂ :=
  (matrix r K w0 v0 θ F H p q).submatrix id selection

def baseDenominator {m : ℕ} (r : Base) (K : ℕ) (w0 : ℝ)
    (q T : Fin m → ℕ) (H : ℝ) : ℝ :=
  denominator q T H * (r.denominator : ℝ) ^ (K * ⌊H / w0⌋₊)

theorem baseDenominator_pos {m : ℕ} (r : Base) (K : ℕ) (w0 : ℝ)
    (q T : Fin m → ℕ) (H : ℝ) : 0 < baseDenominator r K w0 q T H := by
  exact mul_pos (denominator_pos _ _ _)
    (pow_pos (by exact_mod_cast r.denominator_pos) _)

theorem log_baseDenominator_le {m : ℕ} {q : Fin m → ℕ}
    (r : Base) (K : ℕ) (F w0 v0 H : ℝ)
    (hF : 0 ≤ F) (hw0 : 0 < w0) (hv0 : 0 < v0) (hH : 0 < H)
    (hw : ∀ i, 0 < logWeights q i) :
    Real.log (baseDenominator r K w0 q (truncationOrders q F v0) H) ≤
      H * (Arithmetic.lcmConstant * F * m / v0 +
        Arithmetic.lcmConstant * ∑ i, 1 / logWeights q i + r.denominatorCost * K / w0) := by
  have hd : (0 : ℝ) < r.denominator := by exact_mod_cast r.denominator_pos
  rw [baseDenominator, Real.log_mul (denominator_pos _ _ _).ne' (pow_ne_zero _ hd.ne'),
    Real.log_pow]
  have hbase := log_denominator_le F v0 H hF hv0 hH hw
  have hf : (⌊H / w0⌋₊ : ℝ) ≤ H / w0 := Nat.floor_le (div_nonneg hH.le hw0.le)
  have hcost : ((K * ⌊H / w0⌋₊ : ℕ) : ℝ) * Real.log (r.denominator : ℝ) ≤
      H * (r.denominatorCost * K / w0) := by
    calc
      _ = (r.denominatorCost * K) * (⌊H / w0⌋₊ : ℝ) := by
        rw [Nat.cast_mul]
        unfold Base.denominatorCost
        ring
      _ ≤ (r.denominatorCost * K) * (H / w0) :=
        mul_le_mul_of_nonneg_left hf (mul_nonneg r.denominatorCost_nonneg (Nat.cast_nonneg _))
      _ = _ := by ring
  nlinarith

theorem column_zero_le_floor {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (col : InterpolationMatrix.Column w0 w H) :
    col.val 0 ≤ ⌊H / w0⌋₊ := by
  apply Nat.le_floor
  apply (le_div_iff₀ hw0).mpr
  have h := InterpolationMatrix.column_weight_le hw0 hw col
  have hs : 0 ≤ ∑ i, w i * (col.val i.succ : ℝ) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).le (Nat.cast_nonneg _))
  nlinarith

theorem selectedMinor_entries_gaussian (r : Base) {m K : ℕ} {w0 v0 θ F H : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (ρ σ : InterpolationMatrix.Row K v0 θ (logWeights q) H) :
    (baseDenominator r K w0 q (truncationOrders q F v0) H : ℂ) *
      (rowScale q (fun i => ρ.2.1 i.succ) : ℂ) *
        ((columnScale q (fun i => (selection σ).1 i.succ) : ℂ) *
          selectedMinor r K w0 v0 θ F H p q selection ρ σ) ∈
        GaussianInt.toComplex.range := by
  have hw : ∀ i, 0 < logWeights q i := fun i => ceil_log_weight_pos (hq i)
  have he := LogarithmExtension.MatrixArithmetic.entry_cleared_uniform
    (r.numerator : ℤ) (r.denominator : ℤ) (by exact_mod_cast r.denominator_pos.ne')
    (truncationOrders q F v0) q (fun i => ⌊H / logWeights q i⌋₊) p
    (fun i => by have := hq i; omega) K ρ.1.val (ρ.2.1 0) ((selection σ).1 0)
    ρ.1.isLt.le (fun i => ρ.2.1 i.succ) (fun i => (selection σ).1 i.succ)
    (column_coordinate_le_floor hw0 hw (selection σ))
  simp only [Int.cast_natCast] at he
  have hcol := column_zero_le_floor hw0 hw (selection σ)
  have hg : (r.denominator : ℂ) ^ (K * (⌊H / w0⌋₊ - (selection σ).val 0)) ∈
      GaussianInt.toComplex.range := by
    exact ⟨(r.denominator : GaussianInt) ^ (K * (⌊H / w0⌋₊ - (selection σ).val 0)),
      by simp⟩
  have hh := GaussianInt.toComplex.range.mul_mem hg he
  have hcenters : rationalCenters p q = (fun i => (p i : ℂ) / (q i : ℂ)) := rfl
  rw [← hcenters] at hh
  have hpow : (r.denominator : ℂ) ^ (K * ⌊H / w0⌋₊) =
      (r.denominator : ℂ) ^ (K * (⌊H / w0⌋₊ - (selection σ).val 0)) *
        (r.denominator : ℂ) ^ (K * (selection σ).val 0) := by
    rw [← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hcol]
  simp only [baseDenominator, denominator, rowScale, columnScale, selectedMinor,
    matrix, Base.complexValue, Matrix.submatrix_apply, id_eq,
    Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_natCast,
    Complex.ofReal_inv, hpow]
  convert hh using 1
  ring

theorem selectedMinor_clearing_bound (r : Base) {m K : ℕ} {w0 v0 θ F H : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (selectedMinor r K w0 v0 θ F H p q selection).det ≠ 0) :
    -(Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) *
      Real.log (baseDenominator r K w0 q (truncationOrders q F v0) H) -
      columnCost q selection + rowCost K v0 θ q H ≤
      Real.log ‖(selectedMinor r K w0 v0 θ F H p q selection).det‖ := by
  have hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le (by decide) (hq i)
  have hc := Arithmetic.cleared_det_log_bound_with_denominator
    (selectedMinor r K w0 v0 θ F H p q selection)
    (fun ρ => rowScale q (fun i => ρ.2.1 i.succ))
    (fun σ => columnScale q (fun i => (selection σ).1 i.succ))
    (baseDenominator r K w0 q (truncationOrders q F v0) H)
    (baseDenominator_pos r K w0 _ _ _) (fun ρ => rowScale_pos hqpos _)
    (fun σ => columnScale_pos hqpos _) hdet
    (selectedMinor_entries_gaussian r p q hq hw0 selection)
  simp only [log_rowScale hqpos, log_columnScale hqpos,
    Finset.sum_neg_distrib, sub_neg_eq_add] at hc
  dsimp [columnCost, rowCost]
  linarith

theorem selectedMinor_arithmetic_lower_bound (r : Base) {m K : ℕ} {w0 v0 θ F H wmin : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hF : 0 ≤ F) (hH : 0 < H) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ logWeights q i)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (selectedMinor r K w0 v0 θ F H p q selection).det ≠ 0) :
    -(1 - meanRowWeight K v0 θ q H) -
      (Arithmetic.lcmConstant * F * m / v0 +
        Arithmetic.lcmConstant * ∑ i, 1 / logWeights q i + r.denominatorCost * K / w0 + θ / wmin) ≤
      Real.log ‖(selectedMinor r K w0 v0 θ F H p q selection).det‖ /
        ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H) := by
  have hw : ∀ i, 0 < logWeights q i := fun i => ceil_log_weight_pos (hq i)
  have hM : 0 < (Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) := by
    exact_mod_cast actual_row_card_pos hK hv0 hθ hH hw
  apply Arithmetic.normalized_arithmetic_bound _ _ _ _ _ _ _ _ _ hM hH
  · exact selectedMinor_clearing_bound r p q hq hw0 selection hdet
  · exact log_baseDenominator_le r K F w0 v0 H hF hw0 hv0 hH hw
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


end LogarithmExtension.RationalLog.MatrixArithmetic

