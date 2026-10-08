import Mathlib

/-! Log-three approximation selection, adapted from the pinned upstream
pi development (Apache-2.0). The target in every approximation is log 3. -/

namespace LogarithmExtension

namespace LogThree

theorem exists_large_log_approximation
    (nu X : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |(Real.log 3) - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ p : ℤ, ∃ q : ℕ,
      2 ≤ q ∧ X < Real.log q ∧ p ≠ 0 ∧
        |(Real.log 3) - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp X)
  obtain ⟨p, q, hq, happrox⟩ := hbad (max 2 N)
  have hq2 : 2 ≤ q := le_trans (le_max_left _ _) hq
  have hNq : N ≤ q := le_trans (le_max_right _ _) hq
  have hexp : Real.exp X < (q : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hNq)
  have hlog : X < Real.log q := by
    simpa using Real.log_lt_log (Real.exp_pos X) hexp
  have hp : p ≠ 0 := by
    intro hp0
    have hpow : (q : ℝ) ^ (-nu) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ q))
        (by linarith)
    have hpi : (Real.log 3) ≤ (q : ℝ) ^ (-nu) := by
      simpa [hp0, abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 3))] using happrox
    have hpi2 : 1 < Real.log 3 := lt_trans (by norm_num) Real.log_three_gt_d9
    linarith
  exact ⟨p, q, hq2, hlog, hp, happrox⟩

end LogThree

end LogarithmExtension
