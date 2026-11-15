import harness.submission.Upload
open Lean Elab Command
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes false

run_meta do
  let env ← getEnv
  let mut types : Array Json := #[]
  for n in #[`ExpandingCodes.PolynomialStretch.binary_sampler_implementation_source,
      `ExpandingCodes.PolynomialStretch.binary_tester_implementation_source] do
    let some ci := env.find? n | throwError "Missing original declaration {n}"
    let type ← Meta.ppExpr ci.type
    types := types.push (Json.mkObj [("name", toJson n.toString), ("type", toJson type.pretty)])
  IO.FS.writeFile "harness/submission/runtime/original-types.json" (Json.arr types).pretty
