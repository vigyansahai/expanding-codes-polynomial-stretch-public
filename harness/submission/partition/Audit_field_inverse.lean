import Solutions.Sol_ExpandingCodes_Computation_SourceFieldArithmetic_inverse_stops
open Lean Elab Command
set_option autoImplicit false
run_meta do
  let env ← getEnv
  let some target := env.find? `ExpandingCodes.Computation.SourceFieldArithmetic.inverse_stops | throwError "Missing target"
  let some sol := env.find? `solution | throwError "Missing solution"
  unless ← Meta.isDefEq target.type sol.type do
    throwError "Exact solution type differs from target"
  let axes ← collectAxioms `solution
  unless axes.all (fun n => #[`propext, `Classical.choice, `Quot.sound].contains n) do
    throwError "Unexpected solution axioms: {axes}"
  IO.FS.writeFile "harness/submission/partition/field_inverse-upload-audit.json" (Json.mkObj [("theorem_name",toJson "ExpandingCodes.Computation.SourceFieldArithmetic.inverse_stops"),("exact_solution_type",toJson true),("axioms",toJson (axes.map Name.toString)),("source_sha256",toJson "5dec0710f647c23ebea1cbe7a6fe87e26e0a0e24a3637ac540c932fda3b9b9d7"),("source_bytes",toJson 254415)]).pretty
  logInfo m!"Exact solution type checked; transitive axioms: {axes}"
