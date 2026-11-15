import Solutions.Sol_ExpandingCodes_Computation_GaussianDriver_rankProgram_stops_canonical
open Lean Elab Command
set_option autoImplicit false
run_meta do
  let env ← getEnv
  let some target := env.find? `ExpandingCodes.Computation.GaussianDriver.rankProgram_stops_canonical | throwError "Missing target"
  let some sol := env.find? `solution | throwError "Missing solution"
  unless ← Meta.isDefEq target.type sol.type do
    throwError "Exact solution type differs from target"
  let axes ← collectAxioms `solution
  IO.FS.writeFile "harness/submission/partition/gaussian_rank-upload-audit.json" (Json.mkObj [("theorem_name",toJson "ExpandingCodes.Computation.GaussianDriver.rankProgram_stops_canonical"),("exact_solution_type",toJson true),("axioms",toJson (axes.map Name.toString)),("source_sha256",toJson "48cfffece092555ef64e3789b99c6f9692b3175539c6ae4acfadaff1a598b95b"),("source_bytes",toJson 328588)]).pretty
  logInfo m!"Exact solution type checked; transitive axioms: {axes}"
