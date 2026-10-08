import LogarithmExtension
import LogarithmExtension.UpstreamAudit
import Lean.Util.CollectAxioms

/-!
# Transitive axiom audit

This audits every theorem in the extension namespace, including all
dependencies, including rational logarithms, rational-power logarithms,
explicit counterexamples, the degree bound for positive algebraic bases,
the complete compatible-embedding bound (including roots of unity),
rational arctangents, quadratic-normalized logarithms, and the reference
pi endpoint.
-/

open Lean Elab Command

run_cmd do
  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in (← getEnv).constants.toList do
    if (`LogarithmExtension).isPrefixOf name then
      match info with
      | .thmInfo _ =>
        let axioms ← collectAxioms name
        for axName in axioms do
          unless permitted.contains axName do
            throwError "Unexpected axiom {axName} in {name}"
        checked := checked + 1
      | _ => pure ()
  unless checked > 0 do
    throwError "No extension theorems were audited"
  for name in #[``LogarithmExtension.logThree_eventual_lower_bound,
      ``LogarithmExtension.logThree_irrationalityExponent_eq_two,
      ``LogarithmExtension.logThree_target,
      ``LogarithmExtension.rationalLogarithm_target,
      ``LogarithmExtension.rationalLog_irrationalityExponent_eq_two,
      ``LogarithmExtension.rationalPowerLog_irrationalityExponent_eq_two,
      ``LogarithmExtension.algebraicLogarithm_target,
      ``LogarithmExtension.algebraicLog_irrationalityExponent_bounds,
      ``LogarithmExtension.algebraicLog_approximation_bound,
      ``LogarithmExtension.CompatibleLog.eventual_lower_bound_of_not_root_of_unity,
      ``LogarithmExtension.CompatibleLog.irrationalityExponent_bounds_of_not_root_of_unity,
      ``LogarithmExtension.CompatibleLog.commonFiberInterpolation,
      ``LogarithmExtension.CompatibleLog.eventual_lower_bound,
      ``LogarithmExtension.CompatibleLog.compatible_embedding_irrationalityExponent_bounds,
      ``LogarithmExtension.CompatibleLog.all_embeddings_irrationalityExponent_eq_two,
      ``LogarithmExtension.rationalArctan_irrationalityExponent_eq_two,
      ``LogarithmExtension.arctan_one_irrationalityExponent_eq_two,
      ``LogarithmExtension.quadraticNormalizedLog_irrationalityExponent_eq_two,
      ``LogarithmExtension.log_three_add_two_sqrt_two_normalized_irrationalityExponent_eq_two,
      ``LogarithmExtension.LogarithmCounterexamples.liouville_log_counterexample,
      ``OAI.PiExponent.pi_eventual_lower_bound,
      ``OAI.PiExponent.pi_irrationalityExponent_eq_two, ``OAI.PiExponent.main] do
    for axName in (← collectAxioms name) do
      unless permitted.contains axName do
        throwError "Unexpected axiom {axName} in {name}"
  logInfo m!"PASS: {checked} extension theorem declarations; only standard axioms."
  logInfo "PASS: upstream pi endpoint; only standard axioms."
  logInfo "PASS: unconditional log-three eventual approximation bound and exact irrationality exponent two."
  logInfo "PASS: LogThreeTarget is inhabited by logThree_target; no extra hypotheses or nonstandard axioms."
  logInfo "PASS: RationalLogarithmTarget; exponent two for all positive rational bases other than one."
  logInfo "PASS: exponent two for positive bases with a nontrivial rational integer power."
  logInfo "PASS: explicit counterexamples to unrestricted real-logarithm claims."
  logInfo "PASS: every positive real algebraic base other than one; exponent between 2 and twice its minimal-polynomial degree."
  logInfo "PASS: complete compatible-embedding bound 2d/s, including roots of unity."
  logInfo "PASS: exponent two when all embeddings are compatible."
  logInfo "PASS: rational arctangents and quadratic-normalized logarithms."
