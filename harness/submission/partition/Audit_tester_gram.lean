import Solutions.Sol_ExpandingCodes_Computation_TesterGram_program_stops
open Lean Elab Command
set_option autoImplicit false
run_meta do
  let env ← getEnv
  let some target := env.find? `ExpandingCodes.Computation.TesterGram.program_stops | throwError "Missing target"
  let some sol := env.find? `solution | throwError "Missing solution"
  unless ← Meta.isDefEq target.type sol.type do
    throwError "Exact solution type differs from target"
  let axes ← collectAxioms `solution
  IO.FS.writeFile "harness/submission/partition/tester_gram-upload-audit.json" (Json.mkObj [("theorem_name",toJson "ExpandingCodes.Computation.TesterGram.program_stops"),("exact_solution_type",toJson true),("axioms",toJson (axes.map Name.toString)),("source_sha256",toJson "650cb8051949297af2b4945caa94778251eab2d9115bd120039c4d842891d85b"),("source_bytes",toJson 306894)]).pretty
  logInfo m!"Exact solution type checked; transitive axioms: {axes}"
