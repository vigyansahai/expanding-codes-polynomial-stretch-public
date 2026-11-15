import Solutions.Sol_ExpandingCodes_Computation_TesterFrontend_program_stops
open Lean Elab Command
set_option autoImplicit false
run_meta do
  let env ← getEnv
  let some target := env.find? `ExpandingCodes.Computation.TesterFrontend.program_stops | throwError "Missing target"
  let some sol := env.find? `solution | throwError "Missing solution"
  unless ← Meta.isDefEq target.type sol.type do
    throwError "Exact solution type differs from target"
  let axes ← collectAxioms `solution
  IO.FS.writeFile "harness/submission/partition/tester_frontend-upload-audit.json" (Json.mkObj [("theorem_name",toJson "ExpandingCodes.Computation.TesterFrontend.program_stops"),("exact_solution_type",toJson true),("axioms",toJson (axes.map Name.toString)),("source_sha256",toJson "0e0830a135d34d11993d9398b8189aefe65a294cd718a4222def5f84291bf13c"),("source_bytes",toJson 234221)]).pretty
  logInfo m!"Exact solution type checked; transitive axioms: {axes}"
