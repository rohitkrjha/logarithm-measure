import Lean
import Lean.Replay

/-!
Replay the exact log-three endpoint dependency closure in an empty kernel
environment. This avoids replaying unrelated imported mathematics, while
still checking every declaration used by the selected endpoints.

Run after building LogarithmExtension.LogThreeMain:
  lake env lean --run VerifyLogThree.lean
-/

open Lean

def logThreeRoots : Array Name := #[
  `LogarithmExtension.logThree_eventual_lower_bound,
  `LogarithmExtension.logThree_irrational,
  `LogarithmExtension.logThree_irrationalityExponent_eq_two,
  `LogarithmExtension.logThree_target,
  `LogarithmExtension.logThree_approximation_bound]

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let sourceEnv ← importModules #[{ module := `LogarithmExtension.LogThreeMain }] {}
  let mut pending := logThreeRoots
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
    -- Include full mutual blocks and all constructors, as required by replay.
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
  let fresh ← mkEmptyEnvironment
  let checked ← fresh.toKernelEnv.replay selected
  for name in logThreeRoots do
    unless (checked.find? name).isSome do
      throw <| IO.userError s!"Endpoint absent after replay: {name}"
  IO.println "PASS: all five unconditional log-three endpoints and their complete dependency closure."
  IO.println "PASS: only propext, Classical.choice, and Quot.sound allowed as axioms."

