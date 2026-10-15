import ShiftedGcd

/-! Run with `lake env lean scripts/CheckAxioms.lean` after `lake build`.
Reject nonstandard axioms in the external Jacobsthal theorem, the imported analytic
declarations, and this project's namespace, including private and generated declarations. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.fold
      (init := #[``OAI.Erdos970.Erdos970Final.erdos_970_quadratic]) fun names name _ =>
    let publicName := privateToUserName name
    if (`ShiftedGcd).isPrefixOf publicName || (`OAI.Problem337).isPrefixOf publicName then
      names.push name
    else names
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} declarations; only propext, Classical.choice and Quot.sound found."
