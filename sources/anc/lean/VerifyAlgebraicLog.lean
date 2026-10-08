import Lean
import Lean.Replay

/-!
Replay the exact dependency closure of the positive-algebraic logarithm
degree bound in an empty kernel environment, admitting only standard axioms.

Run after building LogarithmExtension.AlgebraicLogMain:
  lake env lean --run VerifyAlgebraicLog.lean
-/

open Lean

def algebraicLogRoots : Array Name := #[
  `LogarithmExtension.algebraicBase_eventual_lower_bound,
  `LogarithmExtension.algebraicLogarithm_target,
  `LogarithmExtension.algebraicLog_eventual_lower_bound,
  `LogarithmExtension.algebraicLog_irrational,
  `LogarithmExtension.algebraicLog_irrationalityExponent_le,
  `LogarithmExtension.algebraicLog_irrationalityExponent_bounds,
  `LogarithmExtension.algebraicLog_approximation_bound]

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let sourceEnv ← importModules #[{ module := `LogarithmExtension.AlgebraicLogMain }] {}
  let mut pending := algebraicLogRoots
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
  for name in algebraicLogRoots do
    unless (checked.find? name).isSome do
      throw <| IO.userError s!"Endpoint absent after replay: {name}"
  IO.println s!"PASS: all {algebraicLogRoots.size} selected algebraic-logarithm endpoints."
  IO.println "PASS: their complete dependency closure rechecked in an empty kernel environment."
  IO.println "PASS: only propext, Classical.choice, and Quot.sound allowed as axioms."
