import Solutions.Sol_ExpandingCodes_Computation_TapeCompiler_compile_halts
open Lean Elab Command
set_option autoImplicit false
run_meta do
  let env ← getEnv
  let some target := env.find? `ExpandingCodes.Computation.TapeCompiler.compile_halts | throwError "Missing target"
  let some sol := env.find? `solution | throwError "Missing solution"
  unless ← Meta.isDefEq target.type sol.type do
    throwError "Exact solution type differs from target"
  let axes ← collectAxioms `solution
  unless axes.all (fun n => #[`propext, `Classical.choice, `Quot.sound].contains n) do
    throwError "Unexpected solution axioms: {axes}"
  IO.FS.writeFile "harness/submission/partition/tape_compile-upload-audit.json" (Json.mkObj [("theorem_name",toJson "ExpandingCodes.Computation.TapeCompiler.compile_halts"),("exact_solution_type",toJson true),("axioms",toJson (axes.map Name.toString)),("source_sha256",toJson "98a36a87915e6ae2b67153f3a4389619cb83164ef7e3876c8bd9aadc4e39e657"),("source_bytes",toJson 108571)]).pretty
  logInfo m!"Exact solution type checked; transitive axioms: {axes}"
