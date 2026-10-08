import Lean
import Lean.Replay

/-!
Replay the complete dependency closure of the general compatible-embedding
theorem, all supplied logarithm specializations, and the explicit real-input
counterexamples in an empty Lean kernel environment. Only the three standard
axioms below are admitted. Unsafe and partial dependencies are rejected.

First finish `lake build LogarithmExtension.Verification`, then run:
  lake env lean --run VerifyGeneralLog.lean
Do not rebuild imported modules while this verifier is running.
-/

open Lean

def generalLogRoots : Array Name := #[
  `LogarithmExtension.logThree_eventual_lower_bound,
  `LogarithmExtension.logThree_irrationalityExponent_eq_two,
  `LogarithmExtension.logThree_target,
  `LogarithmExtension.rationalLogarithm_target,
  `LogarithmExtension.rationalLog_eventual_lower_bound,
  `LogarithmExtension.rationalLog_irrational,
  `LogarithmExtension.rationalLog_irrationalityExponent_eq_two,
  `LogarithmExtension.rationalLog_approximation_bound,
  `LogarithmExtension.rationalPowerLog_irrationalityExponent_eq_two,
  `LogarithmExtension.log_sqrt_two_irrationalityExponent_eq_two,
  `LogarithmExtension.algebraicLogarithm_target,
  `LogarithmExtension.algebraicLog_eventual_lower_bound,
  `LogarithmExtension.algebraicLog_irrational,
  `LogarithmExtension.algebraicLog_irrationalityExponent_bounds,
  `LogarithmExtension.algebraicLog_approximation_bound,
  `LogarithmExtension.CompatibleLog.commonFiberInterpolation,
  `LogarithmExtension.CompatibleLog.eventual_lower_bound,
  `LogarithmExtension.CompatibleLog.irrational,
  `LogarithmExtension.CompatibleLog.irrationalityExponent_bounds,
  `LogarithmExtension.CompatibleLog.approximation_bound,
  `LogarithmExtension.CompatibleLog.irrationalityExponent_eq_two_of_count_eq_degree,
  `LogarithmExtension.CompatibleLog.compatible_embedding_eventual_lower_bound,
  `LogarithmExtension.CompatibleLog.compatible_embedding_irrationalityExponent_bounds,
  `LogarithmExtension.CompatibleLog.all_embeddings_irrationalityExponent_eq_two,
  `LogarithmExtension.rationalArctan_irrationalityExponent_eq_two,
  `LogarithmExtension.arctan_one_irrationalityExponent_eq_two,
  `LogarithmExtension.quadraticNormalizedLog_irrationalityExponent_eq_two,
  `LogarithmExtension.log_three_add_two_sqrt_two_normalized_irrationalityExponent_eq_two,
  `LogarithmExtension.LogarithmCounterexamples.logarithm_on_positive_reals_surjective,
  `LogarithmExtension.LogarithmCounterexamples.positive_nonunit_with_rational_log,
  `LogarithmExtension.LogarithmCounterexamples.liouville_log_counterexample,
  `LogarithmExtension.LogarithmCounterexamples.not_universal_logarithm_bound,
  `LogarithmExtension.LogarithmCounterexamples.not_universal_bound_even_for_irrational_logs]

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let sourceEnv ← importModules #[{ module := `LogarithmExtension }] {}
  let mut pending := generalLogRoots
  let mut selected : Std.HashMap Name ConstantInfo := {}
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if selected.contains name then
      continue
    let some info := sourceEnv.find? name |
      throw <| IO.userError s!"Missing dependency {name}"
    if info.isUnsafe || info.isPartial then
      throw <| IO.userError s!"Unsafe or partial dependency {name}"
    if info matches .axiomInfo _ then
      unless permitted.contains name do
        throw <| IO.userError s!"Nonstandard axiom {name}"
    selected := selected.insert name info
    for dependency in info.getUsedConstantsAsSet do
      pending := pending.push dependency
    match info with
    | .defnInfo value => pending := pending ++ value.all.toArray
    | .thmInfo value => pending := pending ++ value.all.toArray
    | .inductInfo value =>
      pending := pending ++ value.all.toArray ++ value.ctors.toArray
    | .ctorInfo value => pending := pending.push value.induct
    | .recInfo value => pending := pending ++ value.all.toArray
    | .quotInfo _ => pending := pending.push `Eq
    | _ => pure ()
  IO.println s!"Replaying {selected.size} endpoint dependencies in an empty kernel environment."
  (← IO.getStdout).flush
  let fresh ← mkEmptyEnvironment
  let checked ← fresh.toKernelEnv.replay selected
  for name in generalLogRoots do
    unless (checked.find? name).isSome do
      throw <| IO.userError s!"Endpoint absent after replay: {name}"
  IO.println s!"PASS: all {generalLogRoots.size} general-logarithm and counterexample endpoints."
  IO.println "PASS: their complete dependency closure rechecked in an empty kernel environment."
  IO.println "PASS: only propext, Classical.choice, and Quot.sound allowed as axioms."
