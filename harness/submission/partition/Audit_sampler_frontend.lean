import Solutions.Sol_ExpandingCodes_Computation_SamplerAssembly_prelude_stops
open Lean Elab Command
set_option autoImplicit false
run_meta do
  let env ← getEnv
  let some target := env.find? `ExpandingCodes.Computation.SamplerAssembly.prelude_stops | throwError "Missing target"
  let some sol := env.find? `solution | throwError "Missing solution"
  unless ← Meta.isDefEq target.type sol.type do
    throwError "Exact solution type differs from target"
  let axes ← collectAxioms `solution
  IO.FS.writeFile "harness/submission/partition/sampler_frontend-upload-audit.json" (Json.mkObj [("theorem_name",toJson "ExpandingCodes.Computation.SamplerAssembly.prelude_stops"),("exact_solution_type",toJson true),("axioms",toJson (axes.map Name.toString)),("source_sha256",toJson "f448e65c291b37578aed8fb2bacf87b645186348b73f028a4945d1e733bcd2b0"),("source_bytes",toJson 289220)]).pretty
  logInfo m!"Exact solution type checked; transitive axioms: {axes}"
