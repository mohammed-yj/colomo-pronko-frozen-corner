import Lake
import Lean.Elab.Frontend
open Lake DSL Lean
package driver
@[«script»] unsafe def check : ScriptFn := fun args => do
  let root ← IO.getEnv "LEAN_SYSROOT"
  let some root := root | throw <| IO.userError "LEAN_SYSROOT is required"
  initSearchPath root
  enableInitializersExecution
  let file := args[0]!
  let mod := args[1]!.toName
  let (env, ok) ← Elab.runFrontend (← IO.FS.readFile file) {} file mod (trustLevel := 0)
  if !ok then return 1
  if let some out := args[2]? then
    writeModule env ⟨out⟩
  return 0
