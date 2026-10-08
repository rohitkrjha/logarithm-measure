import LogarithmExtension.GeneralExponent
import LogarithmExtension.CompatibleLogGeometry
import LogarithmExtension.CompatibleLogAllEmbeddings

/-!
# Compatible-embedding bound for non-root-of-unity algebraic values

This completes the full d/s norm comparison in the distinct-fiber case.
The last theorem isolates the common-fiber interpolation input; it is
supplied by CompatibleLogMain.lean to obtain the unconditional full theorem.
-/

namespace LogarithmExtension.CompatibleLog

theorem eventual_lower_bound_of_powers_injective (base : Base)
    (hinj : Function.Injective (fun n : ℕ => base.element ^ n)) :
    EventualLowerBound base.value (2 * base.ratio) :=
  DeterminantContradiction.eventualLowerBound_of_interpolation_and_analytic_aggregate
    (Geometry.globalInterpolation base hinj) (AllEmbeddings.analyticAggregate base)

theorem eventual_lower_bound_of_not_root_of_unity (base : Base)
    (hroot : ¬ ∃ n : ℕ, 0 < n ∧ base.element ^ n = 1) :
    EventualLowerBound base.value (2 * base.ratio) :=
  eventual_lower_bound_of_powers_injective base (base.powers_injective_of_no_root hroot)

theorem irrationalityExponent_bounds_of_not_root_of_unity (base : Base)
    (hroot : ¬ ∃ n : ℕ, 0 < n ∧ base.element ^ n = 1) :
    2 ≤ OAI.PiExponent.irrationalityExponent base.value ∧
      OAI.PiExponent.irrationalityExponent base.value ≤ 2 * base.ratio :=
  ⟨two_le_irrationalityExponent_of_eventualLowerBound
      (eventual_lower_bound_of_not_root_of_unity base hroot),
    irrationalityExponent_le_of_eventualLowerBound
      (eventual_lower_bound_of_not_root_of_unity base hroot)⟩

/-- The common-fiber geometric interface, inhabited by
CompatibleLog.commonFiberInterpolation in CompatibleLogMain.lean. -/
def CommonFiberInterpolationStatement : Prop :=
  ∀ base : Base, base.element = 1 → DeterminantContradiction.GlobalInterpolationStatement base

theorem eventual_lower_bound_of_commonFiber_interpolation
    (hcommon : CommonFiberInterpolationStatement) (base : Base) :
    EventualLowerBound base.value (2 * base.ratio) := by
  obtain ⟨b, hv, hr, hcase⟩ := base.exists_normalized
  have hb : EventualLowerBound b.value (2 * b.ratio) := by
    rcases hcase with hcommonValue | hinj
    · exact DeterminantContradiction.eventualLowerBound_of_interpolation_and_analytic_aggregate
        (hcommon b hcommonValue) (AllEmbeddings.analyticAggregate b)
    · exact eventual_lower_bound_of_powers_injective b hinj
  simpa only [hv, hr] using hb

#print axioms eventual_lower_bound_of_not_root_of_unity
#print axioms irrationalityExponent_bounds_of_not_root_of_unity
#print axioms eventual_lower_bound_of_commonFiber_interpolation

end LogarithmExtension.CompatibleLog
