import LogarithmExtension.NumberFieldDeterminant
import LogarithmExtension.CompatibleLogBase
import LogarithmExtension.RationalLogMatrixArithmetic

/-! The selected logarithmic interpolation minor over the base number field,
with the corresponding complex matrix and its full norm lower bound. -/

noncomputable section
namespace LogarithmExtension.CompatibleLog.MatrixArithmetic

open OAI OAI.PiExponent
open scoped BigOperators

export OAI.PiExponent.MatrixArithmetic
  (logWeights columnScale rowScale denominator truncationOrders
   columnScale_pos rowScale_pos denominator_pos log_columnScale log_rowScale
   log_denominator_le rowWeightedSum meanRowWeight rowCost columnCost
   actual_row_card_pos ceil_log_weight_pos column_coordinate_le_floor
   column_log_cost_le_H selected_column_log_cost_le row_weighted_cost_le
   all_row_log_cost_lower meanRowWeight_nonneg meanRowWeight_le_theta)

abbrev rationalCenters := @RationalLog.MatrixArithmetic.rationalCenters

def scaledCenters (r : Base) (σ : r.carrier →ₐ[ℚ] ℂ) {m : ℕ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) : Fin m → ℂ :=
  fun i => σ r.slope * (p i : ℂ) / (q i : ℂ)

def fieldMatrix (r : Base) {m : ℕ} (K : ℕ) (w0 v0 θ F H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ) :
    Matrix (InterpolationMatrix.Row K v0 θ (logWeights q) H)
      (InterpolationMatrix.Column w0 (logWeights q) H) r.carrier :=
  fun row col => NumberFieldArithmetic.entry r.element r.slope
    (truncationOrders q F v0) q p row.1.val (row.2.val 0)
    (fun i => row.2.val i.succ) (col.val 0) (fun i => col.val i.succ)

def matrixAt (r : Base) (σ : r.carrier →ₐ[ℚ] ℂ) {m : ℕ}
    (K : ℕ) (w0 v0 θ F H : ℝ) (p : Fin m → ℤ) (q : Fin m → ℕ) :
    Matrix (InterpolationMatrix.Row K v0 θ (logWeights q) H)
      (InterpolationMatrix.Column w0 (logWeights q) H) ℂ :=
  fun row col => AnalyticTranslation.matrixEntry (σ r.element) (scaledCenters r σ p q)
    (truncationOrders q F v0) row.1.val (row.2.val 0) (fun i => row.2.val i.succ)
    (col.val 0) (fun i => col.val i.succ)

def matrix (r : Base) {m : ℕ} (K : ℕ) (w0 v0 θ F H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ) :=
  matrixAt r r.embedding K w0 v0 θ F H p q

def fieldSelectedMinor (r : Base) {m : ℕ} (K : ℕ) (w0 v0 θ F H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H) :=
  (fieldMatrix r K w0 v0 θ F H p q).submatrix id selection

def selectedMinorAt (r : Base) (σ : r.carrier →ₐ[ℚ] ℂ) {m : ℕ}
    (K : ℕ) (w0 v0 θ F H : ℝ) (p : Fin m → ℤ) (q : Fin m → ℕ)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H) :=
  (matrixAt r σ K w0 v0 θ F H p q).submatrix id selection

def selectedMinor (r : Base) {m : ℕ} (K : ℕ) (w0 v0 θ F H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H) :=
  selectedMinorAt r r.embedding K w0 v0 θ F H p q selection

theorem map_fieldMatrix (r : Base) (σ : r.carrier →ₐ[ℚ] ℂ) {m : ℕ}
    (K : ℕ) (w0 v0 θ F H : ℝ) (p : Fin m → ℤ) (q : Fin m → ℕ) :
    (fieldMatrix r K w0 v0 θ F H p q).map σ = matrixAt r σ K w0 v0 θ F H p q := by
  ext row col
  have he := NumberFieldArithmetic.map_entry σ r.element r.slope (truncationOrders q F v0) q p
      row.1.val (row.2.val 0) (fun i => row.2.val i.succ)
      (col.val 0) (fun i => col.val i.succ)
  exact he

theorem map_fieldSelectedMinor_det (r : Base) (σ : r.carrier →ₐ[ℚ] ℂ) {m : ℕ}
    (K : ℕ) (w0 v0 θ F H : ℝ) (p : Fin m → ℤ) (q : Fin m → ℕ)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H) :
    σ (fieldSelectedMinor r K w0 v0 θ F H p q selection).det =
      (selectedMinorAt r σ K w0 v0 θ F H p q selection).det := by
  have he := RingHom.map_det σ.toRingHom (fieldSelectedMinor r K w0 v0 θ F H p q selection)
  have hm : (fieldSelectedMinor r K w0 v0 θ F H p q selection).map σ =
      selectedMinorAt r σ K w0 v0 θ F H p q selection := by
    ext ρ τ
    exact congrFun (congrFun (map_fieldMatrix r σ K w0 v0 θ F H p q) ρ) (selection τ)
  exact he.trans (congrArg Matrix.det hm)

def baseDenominator {m : ℕ} (r : Base) (K : ℕ) (w0 : ℝ)
    (q T : Fin m → ℕ) (H : ℝ) : ℚ :=
  (∏ i, ((r.slopeDenominator * Nat.lcmUpto (T i) : ℕ) : ℚ) ^ ⌊H / logWeights q i⌋₊) *
    (r.denominator : ℚ) ^ (K * ⌊H / w0⌋₊)

theorem baseDenominator_pos {m : ℕ} (r : Base) (K : ℕ) (w0 : ℝ)
    (q T : Fin m → ℕ) (H : ℝ) : 0 < baseDenominator r K w0 q T H := by
  apply mul_pos
  · apply Finset.prod_pos
    intro i _
    exact pow_pos (by exact_mod_cast (mul_pos r.slopeDenominator_pos
      (Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero (T i))))) _
  · exact pow_pos (by exact_mod_cast r.denominator_pos) _

theorem cast_baseDenominator {m : ℕ} (r : Base) (K : ℕ) (w0 : ℝ)
    (q T : Fin m → ℕ) (H : ℝ) :
    (baseDenominator r K w0 q T H : ℝ) =
      denominator q T H * (∏ i, (r.slopeDenominator : ℝ) ^ ⌊H / logWeights q i⌋₊) *
        (r.denominator : ℝ) ^ (K * ⌊H / w0⌋₊) := by
  simp only [baseDenominator, denominator, Rat.cast_mul, Rat.cast_prod, Rat.cast_pow,
    Rat.cast_natCast, Nat.cast_mul, mul_pow, Finset.prod_mul_distrib]
  ring

theorem log_baseDenominator_le {m : ℕ} {q : Fin m → ℕ}
    (r : Base) (K : ℕ) (F w0 v0 H : ℝ)
    (hF : 0 ≤ F) (hw0 : 0 < w0) (hv0 : 0 < v0) (hH : 0 < H)
    (hw : ∀ i, 0 < logWeights q i) :
    Real.log (baseDenominator r K w0 q (truncationOrders q F v0) H : ℝ) ≤
      H * (Arithmetic.lcmConstant * F * m / v0 +
        (Arithmetic.lcmConstant + r.slopeDenominatorCost) * ∑ i, 1 / logWeights q i + r.denominatorCost * K / w0) := by
  have hd : (0 : ℝ) < r.denominator := by exact_mod_cast r.denominator_pos
  have hγ : (0 : ℝ) < r.slopeDenominator := by exact_mod_cast r.slopeDenominator_pos
  have hprod : 0 < ∏ i, (r.slopeDenominator : ℝ) ^ ⌊H / logWeights q i⌋₊ :=
    Finset.prod_pos (fun _ _ => pow_pos hγ _)
  have hslope : Real.log (∏ i, (r.slopeDenominator : ℝ) ^ ⌊H / logWeights q i⌋₊) ≤
      H * (r.slopeDenominatorCost * ∑ i, 1 / logWeights q i) := by
    rw [Real.log_prod (fun _ _ => pow_ne_zero _ hγ.ne')]
    simp only [Real.log_pow]
    calc
      _ ≤ ∑ i, (H / logWeights q i) * r.slopeDenominatorCost :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
          (Nat.floor_le (div_nonneg hH.le (hw i).le)) r.slopeDenominatorCost_nonneg)
      _ = _ := by
        simp only [div_eq_mul_inv, one_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [cast_baseDenominator,
    Real.log_mul (mul_pos (denominator_pos _ _ _) hprod).ne' (pow_ne_zero _ hd.ne'),
    Real.log_mul (denominator_pos _ _ _).ne' hprod.ne', Real.log_pow]
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

def rowScaleQ {m : ℕ} (q : Fin m → ℕ) (β : Fin m → ℕ) : ℚ :=
  (∏ i, (q i : ℚ) ^ β i)⁻¹

def columnScaleQ {m : ℕ} (q : Fin m → ℕ) (α : Fin m → ℕ) : ℚ :=
  ∏ i, (q i : ℚ) ^ α i

theorem selectedMinor_entries_integral (r : Base) {m K : ℕ} {w0 v0 θ F H : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (ρ τ : InterpolationMatrix.Row K v0 θ (logWeights q) H) :
    IsIntegral ℤ ((baseDenominator r K w0 q (truncationOrders q F v0) H : r.carrier) *
      (rowScaleQ q (fun i => ρ.2.1 i.succ) : r.carrier) *
        ((columnScaleQ q (fun i => (selection τ).1 i.succ) : r.carrier) *
          fieldSelectedMinor r K w0 v0 θ F H p q selection ρ τ)) := by
  have hw : ∀ i, 0 < logWeights q i := fun i => ceil_log_weight_pos (hq i)
  have he := NumberFieldArithmetic.entry_cleared r.element r.slope
    r.denominator r.slopeDenominator r.denominator_integral r.slopeDenominator_integral
    (truncationOrders q F v0) q (fun i => ⌊H / logWeights q i⌋₊) p
    (fun i => by have := hq i; omega) K ρ.1.val (ρ.2.1 0) ((selection τ).1 0)
    ρ.1.isLt.le (fun i => ρ.2.1 i.succ) (fun i => (selection τ).1 i.succ)
    (column_coordinate_le_floor hw0 hw (selection τ))
  have hcol := RationalLog.MatrixArithmetic.column_zero_le_floor hw0 hw (selection τ)
  have hh := ((isIntegral_natCast r.denominator : IsIntegral ℤ (r.denominator : r.carrier)).pow
    (K * (⌊H / w0⌋₊ - (selection τ).val 0))).mul he
  have hpow : (r.denominator : r.carrier) ^ (K * ⌊H / w0⌋₊) =
      (r.denominator : r.carrier) ^ (K * (⌊H / w0⌋₊ - (selection τ).val 0)) *
        (r.denominator : r.carrier) ^ (K * (selection τ).val 0) := by
    rw [← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hcol]
  simp only [baseDenominator, rowScaleQ, columnScaleQ, fieldSelectedMinor,
    fieldMatrix, Matrix.submatrix_apply, id_eq, Rat.cast_mul, Rat.cast_prod,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_inv, hpow]
  convert hh using 1
  ring

theorem cast_rowScaleQ {m : ℕ} (q : Fin m → ℕ) (β : Fin m → ℕ) :
    (rowScaleQ q β : ℝ) = rowScale q β := by
  simp only [rowScaleQ, rowScale, columnScale, Rat.cast_inv, Rat.cast_prod, Rat.cast_pow, Rat.cast_natCast]

theorem cast_columnScaleQ {m : ℕ} (q : Fin m → ℕ) (α : Fin m → ℕ) :
    (columnScaleQ q α : ℝ) = columnScale q α := by
  simp only [columnScaleQ, columnScale, Rat.cast_prod, Rat.cast_pow, Rat.cast_natCast]

theorem selectedMinor_clearing_bound (r : Base) {m K : ℕ} {w0 v0 θ F H : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (fieldSelectedMinor r K w0 v0 θ F H p q selection).det ≠ 0) :
    -r.degree *
      ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) *
        Real.log (baseDenominator r K w0 q (truncationOrders q F v0) H : ℝ) +
        columnCost q selection - rowCost K v0 θ q H) ≤
      ∑ σ : r.carrier →ₐ[ℚ] ℂ,
        Real.log ‖σ (fieldSelectedMinor r K w0 v0 θ F H p q selection).det‖ := by
  have hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le (by decide) (hq i)
  have hrow : ∀ β : Fin m → ℕ, 0 < rowScaleQ q β := by
    intro β
    apply inv_pos.mpr
    exact Finset.prod_pos (fun i _ => pow_pos (by exact_mod_cast hqpos i) _)
  have hcol : ∀ α : Fin m → ℕ, 0 < columnScaleQ q α := by
    intro α
    exact Finset.prod_pos (fun i _ => pow_pos (by exact_mod_cast hqpos i) _)
  have hc := NumberFieldArithmetic.cleared_matrix_log_bound_with_denominator
    (fieldSelectedMinor r K w0 v0 θ F H p q selection)
    (fun ρ => rowScaleQ q (fun i => ρ.2.1 i.succ))
    (fun τ => columnScaleQ q (fun i => (selection τ).1 i.succ))
    (baseDenominator r K w0 q (truncationOrders q F v0) H)
    (baseDenominator_pos r K w0 _ _ _) (fun ρ => hrow _) (fun τ => hcol _) hdet
    (selectedMinor_entries_integral r p q hq hw0 selection)
  simp only [cast_rowScaleQ, cast_columnScaleQ, log_rowScale hqpos, log_columnScale hqpos,
    Finset.sum_neg_distrib] at hc
  change -(r.degree) * _ ≤ _ at hc
  convert hc using 1
  dsimp [columnCost, rowCost]
  ring

theorem selectedMinor_arithmetic_lower_bound (r : Base) {m K : ℕ} {w0 v0 θ F H wmin : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hF : 0 ≤ F) (hH : 0 < H) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ logWeights q i)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (fieldSelectedMinor r K w0 v0 θ F H p q selection).det ≠ 0) :
    -r.degree * (1 - meanRowWeight K v0 θ q H) - r.degree *
      (Arithmetic.lcmConstant * F * m / v0 +
        (Arithmetic.lcmConstant + r.slopeDenominatorCost) * ∑ i, 1 / logWeights q i + r.denominatorCost * K / w0 + θ / wmin) ≤
      (∑ σ : r.carrier →ₐ[ℚ] ℂ,
        Real.log ‖σ (fieldSelectedMinor r K w0 v0 θ F H p q selection).det‖) /
          ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H) := by
  have hw : ∀ i, 0 < logWeights q i := fun i => ceil_log_weight_pos (hq i)
  have hM : 0 < (Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) := by
    exact_mod_cast actual_row_card_pos hK hv0 hθ hH hw
  apply NumberFieldArithmetic.normalized_arithmetic_bound _ _ _ _ _ _ _ _ _ _ r.degree_pos.le hM hH
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


/-- Norm averaging by the nonempty compatible set yields the exact d/s
arithmetic coefficient. The determinant itself is unchanged. -/
theorem selectedMinor_arithmetic_average_lower_bound (r : Base) {m K : ℕ} {w0 v0 θ F H wmin : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hF : 0 ≤ F) (hH : 0 < H) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ logWeights q i)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (fieldSelectedMinor r K w0 v0 θ F H p q selection).det ≠ 0) :
    -r.ratio * (1 - meanRowWeight K v0 θ q H) - r.ratio *
      (Arithmetic.lcmConstant * F * m / v0 +
        (Arithmetic.lcmConstant + r.slopeDenominatorCost) * ∑ i, 1 / logWeights q i +
          r.denominatorCost * K / w0 + θ / wmin) ≤
      (∑ σ : r.carrier →ₐ[ℚ] ℂ,
        Real.log ‖σ (fieldSelectedMinor r K w0 v0 θ F H p q selection).det‖) /
          (r.goodCount * ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H)) := by
  have hh := div_le_div_of_nonneg_right
    (selectedMinor_arithmetic_lower_bound r p q hq hK hw0 hv0 hθ hF hH hmin hwmin selection hdet)
    r.goodCount_pos.le
  unfold Base.ratio
  convert hh using 1 <;> ring

#print axioms selectedMinor_entries_integral
#print axioms selectedMinor_arithmetic_lower_bound
#print axioms selectedMinor_arithmetic_average_lower_bound

end LogarithmExtension.CompatibleLog.MatrixArithmetic
