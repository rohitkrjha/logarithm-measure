import LogarithmExtension.Endpoint
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

/-! Rational affine invariance of the exponent-two approximation bound. -/
namespace LogarithmExtension

theorem eventualLowerBound_two_iff_no_liouvilleWith {x : ℝ} (hx : Irrational x) :
    EventualLowerBound x 2 ↔ ∀ nu : ℝ, 2 < nu → ¬ LiouvilleWith nu x := by
  constructor
  · intro h nu hnu hgood
    let tau : ℝ := (2 + nu) / 2
    have htau : 2 < tau := by dsimp [tau]; linarith
    have htau' : tau < nu := by dsimp [tau]; linarith
    obtain ⟨Q, _, hQ⟩ := h tau htau
    obtain ⟨q, hq, p, _, herr⟩ :=
      ((Filter.eventually_ge_atTop Q).and_frequently
        (hgood.frequently_lt_rpow_neg htau')).exists
    exact (not_lt_of_ge (hQ p q hq)) herr
  · intro h nu hnu
    by_contra hbad
    push Not at hbad
    apply h nu hnu
    refine ⟨1, ?_⟩
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨p, q, hq, herr⟩ := hbad (max N 2) (le_max_right _ _)
    refine ⟨q, (le_max_left _ _).trans hq, p, ?_, ?_⟩
    · simpa only [Int.cast_natCast] using hx.ne_rational p (q : ℤ)
    · simpa only [Real.rpow_neg (Nat.cast_nonneg q), one_div] using herr

theorem EventualLowerBound.rat_mul {x : ℝ} (h : EventualLowerBound x 2)
    (c : ℚ) (hc : c ≠ 0) : EventualLowerBound ((c : ℝ) * x) 2 := by
  have hx := irrational_of_eventualLowerBound h
  apply (eventualLowerBound_two_iff_no_liouvilleWith (hx.ratCast_mul hc)).mpr
  intro nu hnu hh
  exact (eventualLowerBound_two_iff_no_liouvilleWith hx).mp h nu hnu
    ((LiouvilleWith.rat_mul_iff hc).mp hh)

theorem EventualLowerBound.add_rat {x : ℝ} (h : EventualLowerBound x 2)
    (c : ℚ) : EventualLowerBound (x + (c : ℝ)) 2 := by
  have hx := irrational_of_eventualLowerBound h
  apply (eventualLowerBound_two_iff_no_liouvilleWith (hx.add_ratCast c)).mpr
  intro nu hnu hh
  exact (eventualLowerBound_two_iff_no_liouvilleWith hx).mp h nu hnu
    (LiouvilleWith.add_rat_iff.mp hh)

end LogarithmExtension

