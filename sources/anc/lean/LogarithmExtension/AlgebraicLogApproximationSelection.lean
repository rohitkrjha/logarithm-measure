import LogarithmExtension.AlgebraicLogBase

/-! Approximation selection for every nonzero algebraic logarithm, including
negative logarithms and logarithms arbitrarily close to zero. -/
namespace LogarithmExtension.AlgebraicLog

theorem exists_large_log_approximation (r : Base)
    (nu X : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |r.logValue - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ p : ℤ, ∃ q : ℕ,
      2 ≤ q ∧ X < Real.log q ∧ p ≠ 0 ∧
        |r.logValue - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu) := by
  let Z : ℝ := max X (-Real.log |r.logValue| / nu)
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp Z)
  obtain ⟨p, q, hq, happ⟩ := hbad (max 2 N)
  have hq2 : 2 ≤ q := (le_max_left _ _).trans hq
  have hNq : N ≤ q := (le_max_right _ _).trans hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hexp : Real.exp Z < (q : ℝ) := hN.trans_le (by exact_mod_cast hNq)
  have hlog : Z < Real.log q := by
    simpa using Real.log_lt_log (Real.exp_pos Z) hexp
  have hlogX : X < Real.log q := (le_max_left _ _).trans_lt hlog
  have hlogsmall : -Real.log |r.logValue| / nu < Real.log q :=
    (le_max_right _ _).trans_lt hlog
  have habs : 0 < |r.logValue| := abs_pos.mpr r.logValue_ne_zero
  have hpow : (q : ℝ) ^ (-nu) < |r.logValue| := by
    rw [Real.rpow_def_of_pos hqpos, ← Real.exp_log habs]
    apply Real.exp_lt_exp.mpr
    have hm := (div_lt_iff₀ hnu).mp hlogsmall
    nlinarith
  have hp : p ≠ 0 := by
    intro hp
    have hh : |r.logValue| ≤ (q : ℝ) ^ (-nu) := by simpa [hp] using happ
    exact (not_lt_of_ge hh) hpow
  exact ⟨p, q, hq2, hlogX, hp, happ⟩

end LogarithmExtension.AlgebraicLog


