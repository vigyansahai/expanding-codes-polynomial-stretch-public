import Solutions.Sol_ExpandingCodes_Computation_SamplerProgram_layer_stops
open Lean Elab Command
set_option autoImplicit false
run_meta do
  let env ← getEnv
  let some target := env.find? `ExpandingCodes.Computation.SamplerProgram.layer_stops | throwError "Missing target"
  let some sol := env.find? `solution | throwError "Missing solution"
  unless ← Meta.isDefEq target.type sol.type do
    throwError "Exact solution type differs from target"
  let axes ← collectAxioms `solution
  IO.FS.writeFile "harness/submission/partition/sampler_layer-upload-audit.json" (Json.mkObj [("theorem_name",toJson "ExpandingCodes.Computation.SamplerProgram.layer_stops"),("exact_solution_type",toJson true),("axioms",toJson (axes.map Name.toString)),("source_sha256",toJson "4f67b71b5e89514731ee55e047b2ff4e535e0b5fec09098dce930fe7d970e9c5"),("source_bytes",toJson 255118)]).pretty
  logInfo m!"Exact solution type checked; transitive axioms: {axes}"
