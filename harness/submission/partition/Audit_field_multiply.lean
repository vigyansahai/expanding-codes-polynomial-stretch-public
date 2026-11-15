import Solutions.Sol_ExpandingCodes_Computation_SourceFieldArithmetic_multiply_stops
open Lean Elab Command
set_option autoImplicit false
run_meta do
  let env ← getEnv
  let some target := env.find? `ExpandingCodes.Computation.SourceFieldArithmetic.multiply_stops | throwError "Missing target"
  let some sol := env.find? `solution | throwError "Missing solution"
  unless ← Meta.isDefEq target.type sol.type do
    throwError "Exact solution type differs from target"
  let axes ← collectAxioms `solution
  unless axes.all (fun n => #[`propext, `Classical.choice, `Quot.sound].contains n) do
    throwError "Unexpected solution axioms: {axes}"
  IO.FS.writeFile "harness/submission/partition/field_multiply-upload-audit.json" (Json.mkObj [("theorem_name",toJson "ExpandingCodes.Computation.SourceFieldArithmetic.multiply_stops"),("exact_solution_type",toJson true),("axioms",toJson (axes.map Name.toString)),("source_sha256",toJson "884c23fde5001562ff4311cb204b5d76bb223ed719d8d89f0c39ba264b0e4bcf"),("source_bytes",toJson 224259)]).pretty
  logInfo m!"Exact solution type checked; transitive axioms: {axes}"
