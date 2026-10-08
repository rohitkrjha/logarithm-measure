import LogarithmExtension.AnalyticTranslation
import OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic

/-!
# Direct bounds at arbitrary complex conjugates

These estimates do not assume exponential compatibility and do not claim
collision saving. They are the missing upper bounds for embeddings at
which the rational approximations do not approximate a logarithmic period.
-/

noncomputable section
namespace LogarithmExtension.ConjugateAnalytic

open scoped BigOperators Topology
open OAI OAI.PiExponent
open AnalyticCollision

theorem hasSum_polynomial_coeff (P : Polynomial ℂ) (z : ℂ) :
    HasSum (fun n => P.coeff n * z ^ n) (P.eval z) := by
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := P.support) (f := fun n => P.coeff n * z ^ n) (by
      intro n hn
      simp only [Polynomial.mem_support_iff, not_not] at hn
      rw [hn, zero_mul])
  simpa only [Polynomial.eval_eq_sum, Polynomial.sum] using h

theorem hasFPowerSeriesAt_polynomial (P : Polynomial ℂ) :
    HasFPowerSeriesAt (fun z => P.eval z)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => P.coeff n)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  apply Filter.Eventually.of_forall
  intro z
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul, mul_comm] using
    hasSum_polynomial_coeff P z

theorem rowTest_polynomial_eq_coeff (P : Polynomial ℂ) (s : ℕ) :
    rowTest s (fun z => P.eval z) = P.coeff s := by
  have hd : DifferentiableOn ℂ (fun z => P.eval z) (Metric.closedBall 0 (1 / 2)) := by
    fun_prop
  have hp := hd.hasFPowerSeriesOnBall (R := (1 / 2 : NNReal)) (by norm_num)
  have he := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesAt_polynomial P)
  have hh := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p s (fun _ => 1)) he
  simpa only [rowTest, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Finset.prod_const_one, one_smul, FormalMultilinearSeries.coeff_ofScalars,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh

theorem norm_polynomial_coeff_le (P : Polynomial ℂ) (s : ℕ) (D : ℝ)
    (hD : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2), ‖P.eval z‖ ≤ D) :
    ‖P.coeff s‖ ≤ (2 : ℝ) ^ s * D := by
  rw [← rowTest_polynomial_eq_coeff]
  exact norm_rowTest_le hD s

theorem norm_truncatedLog_le_two (T : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖(InterpolationMatrix.truncatedLog T).eval z‖ ≤ 2 := by
  rw [InterpolationMatrix.truncatedLog, LogTailAnalytic.eval_trunc_log]
  by_cases hT : T = 0
  · simp [hT, Complex.logTaylor]
  have ht := LogTailAnalytic.norm_logTail_le_one T (Nat.one_le_iff_ne_zero.mpr hT) hz
  have hl := Complex.norm_log_one_add_half_le_self hz
  have he : Complex.logTaylor T z =
      LogTailAnalytic.logTail T z + Complex.log (1 + z) := by
    unfold LogTailAnalytic.logTail
    ring
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

theorem norm_shifted_truncation_le {m K j : ℕ} (T : Fin m → ℕ)
    (r : Fin m → ℂ) (A : ℝ) (hr : ∀ i, ‖r i‖ ≤ A) (hA : 0 ≤ A) (hj : j ≤ K)
    (i : Fin m) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖(Polynomial.C ((j : ℂ) * r i) + InterpolationMatrix.truncatedLog (T i)).eval z‖ ≤
      (K : ℝ) * A + 2 := by
  simp only [Polynomial.eval_add, Polynomial.eval_C]
  calc
    _ ≤ ‖(j : ℂ) * r i‖ + ‖(InterpolationMatrix.truncatedLog (T i)).eval z‖ := norm_add_le _ _
    _ ≤ (j : ℝ) * A + 2 := by
      rw [norm_mul, Complex.norm_natCast]
      exact add_le_add (mul_le_mul_of_nonneg_left (hr i) (Nat.cast_nonneg _))
        (norm_truncatedLog_le_two (T i) hz)
    _ ≤ (K : ℝ) * A + 2 := by
      gcongr

theorem norm_entry_polynomial_le {m K j : ℕ} (T : Fin m → ℕ)
    (r : Fin m → ℂ) (A : ℝ) (hr : ∀ i, ‖r i‖ ≤ A) (hA : 0 ≤ A) (hj : j ≤ K)
    (h : ℕ) (α β : Fin m → ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖(((1 + Polynomial.X) ^ h * ∏ i,
      (Polynomial.C ((j : ℂ) * r i) + InterpolationMatrix.truncatedLog (T i)) ^
        (α i - β i) : Polynomial ℂ).eval z)‖ ≤
      (3 / 2 : ℝ) ^ h * ((K : ℝ) * A + 2) ^ (∑ i, α i) := by
  have hB : 1 ≤ (K : ℝ) * A + 2 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg K) hA]
  have hone : ‖(1 : ℂ) + z‖ ≤ (3 / 2 : ℝ) := by
    have hh := norm_add_le (1 : ℂ) z
    norm_num only [norm_one] at hh
    linarith
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_prod, norm_mul, norm_pow, norm_prod]
  apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hone h) ?_ (by positivity) (by positivity)
  calc
    _ ≤ ∏ i, ((K : ℝ) * A + 2) ^ (α i - β i) := by
      apply Finset.prod_le_prod₀ (fun i _ => by positivity)
      intro i _
      simpa only [Polynomial.eval_add] using pow_le_pow_left₀ (norm_nonneg _)
        (norm_shifted_truncation_le T r A hr hA hj i hz) (α i - β i)
    _ ≤ ∏ i, ((K : ℝ) * A + 2) ^ α i := by
      apply Finset.prod_le_prod₀ (fun i _ => by positivity)
      intro i _
      exact pow_le_pow_right₀ hB (Nat.sub_le _ _)
    _ = _ := Finset.prod_pow_eq_pow_sum Finset.univ _ _

theorem norm_matrixEntry_le {m K j : ℕ} (base : ℂ) (T : Fin m → ℕ)
    (r : Fin m → ℂ) (A : ℝ) (hr : ∀ i, ‖r i‖ ≤ A) (hA : 0 ≤ A) (hj : j ≤ K)
    (s h : ℕ) (α β : Fin m → ℕ) :
    ‖AnalyticTranslation.matrixEntry base r T j s β h α‖ ≤
      (2 : ℝ) ^ s * ((max 1 ‖base‖) ^ K * (3 / 2)) ^ h *
        (2 * ((K : ℝ) * A + 2)) ^ (∑ i, α i) := by
  have hb : ‖base ^ (j * h)‖ ≤ (max 1 ‖base‖) ^ (K * h) := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) (Nat.mul_le_mul_right h hj))
  have hc : ‖∏ i, ((α i).choose (β i) : ℂ)‖ ≤ (2 : ℝ) ^ (∑ i, α i) := by
    simpa only [InterpolationMatrix.exponentVector_apply, Nat.cast_prod] using
      PeriodAnalytic.norm_binomial_product_le α (InterpolationMatrix.exponentVector β)
  have hp := norm_polynomial_coeff_le
    ((1 + Polynomial.X) ^ h * ∏ i,
      (Polynomial.C ((j : ℂ) * r i) + InterpolationMatrix.truncatedLog (T i)) ^ (α i - β i))
    s ((3 / 2 : ℝ) ^ h * ((K : ℝ) * A + 2) ^ (∑ i, α i)) (by
      intro z hz
      apply norm_entry_polynomial_le T r A hr hA hj h α β
      exact (by simpa only [Metric.mem_sphere, dist_zero_right] using hz : ‖z‖ = 1 / 2).le)
  rw [AnalyticTranslation.matrixEntry, InterpolationMatrix.entry_eq_binomial_product,
    norm_mul, norm_mul]
  calc
    _ ≤ (max 1 ‖base‖) ^ (K * h) * ((2 : ℝ) ^ (∑ i, α i) *
        ((2 : ℝ) ^ s * ((3 / 2 : ℝ) ^ h * ((K : ℝ) * A + 2) ^ (∑ i, α i)))) := by
      exact mul_le_mul hb (mul_le_mul hc hp (norm_nonneg _) (by positivity))
        (by positivity) (by positivity)
    _ = _ := by
      rw [pow_mul]
      simp only [mul_pow]
      ring

theorem weighted_power_bound (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h n s : ℕ) (H w0 wmin v0 : ℝ)
    (hh : (h : ℝ) ≤ H / w0) (hn : (n : ℝ) ≤ H / wmin) (hs : (s : ℝ) ≤ H / v0) :
    (2 : ℝ) ^ s * a ^ h * b ^ n ≤
      Real.exp (H * (Real.log a / w0 + Real.log b / wmin + Real.log 2 / v0)) := by
  have hpow (x : ℝ) (hx : 0 < x) (k : ℕ) : x ^ k = Real.exp ((k : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx]
  rw [hpow 2 (by norm_num), hpow a (by linarith), hpow b (by linarith),
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ H / v0 * Real.log 2 + H / w0 * Real.log a + H / wmin * Real.log b := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hs (Real.log_nonneg (by norm_num)))
        (mul_le_mul_of_nonneg_right hh (Real.log_nonneg ha)))
        (mul_le_mul_of_nonneg_right hn (Real.log_nonneg hb))
    _ = _ := by ring

def conjugateError (base : ℂ) (A : ℝ) (K : ℕ) (w0 wmin v0 : ℝ) : ℝ :=
  ((K : ℝ) * Real.log (max 1 ‖base‖) + Real.log (3 / 2)) / w0 +
    Real.log (2 * ((K : ℝ) * A + 2)) / wmin + Real.log 2 / v0

theorem norm_matrixEntry_exp_le {m K j : ℕ} (base : ℂ) (T : Fin m → ℕ)
    (r : Fin m → ℂ) (A : ℝ) (hr : ∀ i, ‖r i‖ ≤ A) (hA : 0 ≤ A) (hj : j ≤ K)
    (s h : ℕ) (α β : Fin m → ℕ) (w : Fin m → ℝ) (H w0 wmin v0 : ℝ)
    (hw0 : 0 < w0) (hwmin : 0 < wmin) (hw : ∀ i, wmin ≤ w i)
    (hcol : w0 * h + ∑ i, w i * α i ≤ H) (hs : (s : ℝ) ≤ H / v0) :
    ‖AnalyticTranslation.matrixEntry base r T j s β h α‖ ≤
      Real.exp (H * conjugateError base A K w0 wmin v0) := by
  have hwpos (i) : 0 ≤ w i := hwmin.le.trans (hw i)
  have hsum : 0 ≤ ∑ i, w i * α i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hwpos i) (Nat.cast_nonneg _))
  have hh : (h : ℝ) ≤ H / w0 := by
    apply (le_div_iff₀ hw0).mpr
    nlinarith
  have hn : ((∑ i, α i : ℕ) : ℝ) ≤ H / wmin := by
    apply (le_div_iff₀ hwmin).mpr
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg (α i) : (0 : ℝ) ≤ α i))
    have hw0h : 0 ≤ w0 * h := mul_nonneg hw0.le (Nat.cast_nonneg _)
    rw [← Finset.mul_sum] at hh
    push_cast
    nlinarith
  have hV : 0 < max 1 ‖base‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hbase : 1 ≤ (max 1 ‖base‖) ^ K * (3 / 2 : ℝ) := by
    have hpow := one_le_pow₀ (le_max_left 1 ‖base‖) (n := K)
    nlinarith
  have hB : 1 ≤ 2 * ((K : ℝ) * A + 2) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg K) hA]
  have hp := weighted_power_bound ((max 1 ‖base‖) ^ K * (3 / 2))
    (2 * ((K : ℝ) * A + 2)) hbase hB h (∑ i, α i) s H w0 wmin v0 hh hn hs
  have he : Real.log ((max 1 ‖base‖) ^ K * (3 / 2 : ℝ)) =
      (K : ℝ) * Real.log (max 1 ‖base‖) + Real.log (3 / 2) := by
    rw [Real.log_mul (pow_ne_zero _ hV.ne') (by norm_num), Real.log_pow]
  rw [he] at hp
  exact (norm_matrixEntry_le base T r A hr hA hj s h α β).trans hp

/-- The direct determinant estimate costs only log(M)/H after normalization.
No compatible period or collision hypothesis is used. -/
theorem normalized_log_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (U H : ℝ) (hH : 0 < H) (hM : 0 < Fintype.card ι)
    (hne : A.det ≠ 0) (hentry : ∀ i j, ‖A i j‖ ≤ Real.exp (H * U)) :
    Real.log ‖A.det‖ / ((Fintype.card ι : ℝ) * H) ≤
      U + Real.log (Fintype.card ι : ℝ) / H := by
  have hMreal : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hM
  have hfinite := norm_det_le_factorial_mul_pow A (Real.exp_pos (H * U)).le hentry
  have hnorm : ‖A.det‖ ≤
      Real.exp ((Fintype.card ι : ℝ) * Real.log (Fintype.card ι : ℝ) +
        (Fintype.card ι : ℝ) * (H * U)) := by
    calc
      _ ≤ (Fintype.card ι).factorial * Real.exp (H * U) ^ Fintype.card ι := hfinite
      _ ≤ Real.exp ((Fintype.card ι : ℝ) * Real.log (Fintype.card ι : ℝ)) *
          Real.exp (H * U) ^ Fintype.card ι :=
        mul_le_mul_of_nonneg_right (Collision.factorial_le_exp_card_log _) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  have hlog := Real.log_le_log (norm_pos_iff.mpr hne) hnorm
  rw [Real.log_exp] at hlog
  apply (div_le_iff₀ (mul_pos hMreal hH)).mpr
  calc
    _ ≤ (Fintype.card ι : ℝ) * Real.log (Fintype.card ι : ℝ) +
        (Fintype.card ι : ℝ) * (H * U) := hlog
    _ = _ := by field_simp; ring

#print axioms norm_matrixEntry_exp_le
#print axioms normalized_log_det_le

end LogarithmExtension.ConjugateAnalytic
