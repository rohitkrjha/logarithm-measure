import LogarithmExtension.Endpoint
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

/-!
# Sharp limitations of an unrestricted logarithm theorem

No finite irrationality bound holds for the logarithms of all positive real
numbers. These counterexamples do not concern the rational-base theorem.
-/
namespace LogarithmExtension.LogarithmCounterexamples

theorem logarithm_on_positive_reals_surjective :
    Function.Surjective (fun x : {x : ℝ // 0 < x} => Real.log x.val) := by
  intro y
  exact ⟨⟨Real.exp y, Real.exp_pos y⟩, Real.log_exp y⟩

theorem logarithm_exp_one_not_irrational :
    ¬ Irrational (Real.log (Real.exp 1)) := by
  intro h
  exact h.ne_rat 1 (by simp)

theorem positive_nonunit_with_rational_log :
    ∃ x : ℝ, 0 < x ∧ x ≠ 1 ∧ Real.log x = 1 := by
  refine ⟨Real.exp 1, Real.exp_pos _, ?_, Real.log_exp _⟩
  intro h
  have hh := congrArg Real.log h
  norm_num [Real.log_exp] at hh

theorem no_finite_bound_of_liouville {x : ℝ} (hx : Liouville x) (bound : ℝ) :
    ¬ EventualLowerBound x bound := by
  intro h
  obtain ⟨Q, _, hQ⟩ := h (bound + 1) (by linarith)
  have hf := (hx.liouvilleWith (bound + 2)).frequently_lt_rpow_neg
    (q := bound + 1) (by linarith)
  obtain ⟨q, hq, p, _, herr⟩ :=
    ((Filter.eventually_ge_atTop Q).and_frequently hf).exists
  exact (not_lt_of_ge (hQ p q hq)) herr

/-- Explicit positive input whose irrational logarithm has no finite
approximation-exponent bound. The Liouville number is sum_{n>=0} 10^(-n!). -/
theorem liouville_log_counterexample :
    ∃ x : ℝ, 0 < x ∧ x ≠ 1 ∧ Irrational (Real.log x) ∧
      ∀ bound : ℝ, ¬ EventualLowerBound (Real.log x) bound := by
  let L : ℝ := liouvilleNumber 10
  have hL : Liouville L := liouville_liouvilleNumber (m := 10) (by norm_num)
  refine ⟨Real.exp L, Real.exp_pos _, ?_, ?_, ?_⟩
  · intro h
    have hh := congrArg Real.log h
    rw [Real.log_exp, Real.log_one] at hh
    exact hL.irrational.ne_zero hh
  · simpa only [Real.log_exp] using hL.irrational
  · intro bound
    simpa only [Real.log_exp] using no_finite_bound_of_liouville hL bound

theorem not_universal_logarithm_bound :
    ¬ ∀ x : ℝ, 0 < x → x ≠ 1 →
      Irrational (Real.log x) ∧ EventualLowerBound (Real.log x) 2 := by
  intro h
  obtain ⟨x, hx, hx1, _, hbad⟩ := liouville_log_counterexample
  exact hbad 2 (h x hx hx1).2

theorem not_universal_bound_even_for_irrational_logs :
    ¬ ∀ x : ℝ, 0 < x → Irrational (Real.log x) →
      ∃ bound : ℝ, EventualLowerBound (Real.log x) bound := by
  intro h
  obtain ⟨x, hx, _, hi, hbad⟩ := liouville_log_counterexample
  obtain ⟨bound, hb⟩ := h x hx hi
  exact hbad bound hb

#print axioms liouville_log_counterexample
#print axioms not_universal_bound_even_for_irrational_logs

end LogarithmExtension.LogarithmCounterexamples

