import Solutions.Sol_ExpandingCodes_Computation_SourceFieldSetup_setup_stops
open Lean Elab Command
set_option autoImplicit false
run_meta do
  let env ← getEnv
  let some target := env.find? `ExpandingCodes.Computation.SourceFieldSetup.setup_stops | throwError "Missing target"
  let some sol := env.find? `solution | throwError "Missing solution"
  unless ← Meta.isDefEq target.type sol.type do
    throwError "Exact solution type differs from target"
  let axes ← collectAxioms `solution
  unless axes.all (fun n => #[`propext, `Classical.choice, `Quot.sound].contains n) do
    throwError "Unexpected solution axioms: {axes}"
  IO.FS.writeFile "harness/submission/partition/field_setup-upload-audit.json" (Json.mkObj [("theorem_name",toJson "ExpandingCodes.Computation.SourceFieldSetup.setup_stops"),("exact_solution_type",toJson true),("axioms",toJson (axes.map Name.toString)),("source_sha256",toJson "7178edcd9eca7d9fb67925fce7f9e2641f28e42b14f8341e2f44fb2501454be4"),("source_bytes",toJson 261667)]).pretty
  logInfo m!"Exact solution type checked; transitive axioms: {axes}"
