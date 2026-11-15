import harness.submission.Upload
open Lean Elab Command
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes false

run_meta do
  let env ← getEnv
  let mut types : Array Json := #[]
  for n in #[`ExpandingCodes.Computation.TapeCompiler.compile_halts,
`ExpandingCodes.Computation.SourceFieldSetup.setup_stops,
`ExpandingCodes.Computation.SourceFieldArithmetic.multiply_stops,
`ExpandingCodes.Computation.SourceFieldArithmetic.addition_stops,
`ExpandingCodes.Computation.SourceFieldArithmetic.inverse_stops,
`ExpandingCodes.Computation.SamplerProgram.layer_stops,
`ExpandingCodes.Computation.SamplerAssembly.prelude_stops,
`ExpandingCodes.Computation.TesterFrontend.program_stops,
`ExpandingCodes.Computation.TesterGram.program_stops,
`ExpandingCodes.Computation.GaussianDriver.rankProgram_stops_canonical] do
    let some ci := env.find? n | throwError "Missing original declaration {n}"
    let type ← Meta.ppExpr ci.type
    types := types.push (Json.mkObj [("name", toJson n.toString), ("type", toJson type.pretty)])
  IO.FS.writeFile "harness/submission/partition/original-types.json" (Json.arr types).pretty
