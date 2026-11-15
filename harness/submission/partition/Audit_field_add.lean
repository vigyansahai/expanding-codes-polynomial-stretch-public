import Solutions.Sol_ExpandingCodes_Computation_SourceFieldArithmetic_addition_stops
open Lean Elab Command
set_option autoImplicit false
run_meta do
  let env ← getEnv
  let some target := env.find? `ExpandingCodes.Computation.SourceFieldArithmetic.addition_stops | throwError "Missing target"
  let some sol := env.find? `solution | throwError "Missing solution"
  unless ← Meta.isDefEq target.type sol.type do
    throwError "Exact solution type differs from target"
  let axes ← collectAxioms `solution
  unless axes.all (fun n => #[`propext, `Classical.choice, `Quot.sound].contains n) do
    throwError "Unexpected solution axioms: {axes}"
  IO.FS.writeFile "harness/submission/partition/field_add-upload-audit.json" (Json.mkObj [("theorem_name",toJson "ExpandingCodes.Computation.SourceFieldArithmetic.addition_stops"),("exact_solution_type",toJson true),("axioms",toJson (axes.map Name.toString)),("source_sha256",toJson "8e86c633678d2bdf35ec063175d17f844d29e1231f5a706f94400ed1035b2939"),("source_bytes",toJson 211592)]).pretty
  logInfo m!"Exact solution type checked; transitive axioms: {axes}"
