import CP
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) =>
    if name.toString.startsWith "CP." && info.isTheorem then some name else none
  let names := names.toArray.qsort (fun a b => a.toString < b.toString)
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"AXIOM_AUDIT {name} {axioms}"
  unless names.size > 0 do throwError "No project theorems found"
  logInfo m!"AXIOM_AUDIT_TOTAL {names.size}"
