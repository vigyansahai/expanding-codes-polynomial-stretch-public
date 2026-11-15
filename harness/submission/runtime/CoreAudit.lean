import harness.submission.runtime.ProofCore
open Lean Elab Command
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true

#print axioms ExpandingCodes.PolynomialStretch.binary_sampler_implementation_source
#print axioms ExpandingCodes.PolynomialStretch.binary_tester_implementation_source
#print axioms ExpandingCodes.PolynomialStretch.auxiliary_rate

run_meta do
  let env ← getEnv
  let endpoints := #[`ExpandingCodes.PolynomialStretch.binary_sampler_implementation_source,
    `ExpandingCodes.PolynomialStretch.binary_tester_implementation_source,
    `ExpandingCodes.PolynomialStretch.auxiliary_rate]
  let mut report : Array Json := #[]
  for n in endpoints do
    let some ci := env.find? n | throwError "Missing endpoint {n}"
    let axioms ← collectAxioms n
    unless axioms.all (fun a => #[`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Unexpected endpoint axioms {n}: {axioms}"
    let type ← Meta.ppExpr ci.type
    report := report.push (Json.mkObj [("name",toJson n.toString),
      ("type",toJson type.pretty),("axioms",toJson (axioms.map Name.toString))])
  if env.find? `solution |>.isSome then throwError "Cache Core exports global solution"
  let modules := env.header.moduleNames
  let simpTheorems ← Meta.getSimpTheorems
  let mut publicSourceNames : Array String := #[]
  let mut privateSimpNames : Array String := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    unless modules[idx.toNat]? == some `harness.submission.runtime.ProofCore do continue
    if ← Meta.isInstance n then throwError "Cache Core exports an extra instance {n}"
    if simpTheorems.isDeclToUnfold n ||
        simpTheorems.isLemma (.decl n true false) || simpTheorems.isLemma (.decl n false false) ||
        simpTheorems.isLemma (.decl n true true) || simpTheorems.isLemma (.decl n false true) then
      privateSimpNames := privateSimpNames.push n.toString
    if (privateToUserName? n).isSome then continue
    let range ← findDeclarationRanges? n
    let some range := range | continue
    if range.range.pos.line == 0 then continue
    unless endpoints.contains n do throwError "Unexpected public source helper {n}"
    publicSourceNames := publicSourceNames.push n.toString
  IO.FS.writeFile "harness/submission/runtime/core-audit.json" (Json.mkObj [
    ("endpoints",Json.arr report),("public_source_declarations",toJson publicSourceNames),
    ("private_simp_annotations_requiring_separate_portability_check",toJson privateSimpNames),
    ("closed_proof_audit_only",toJson true)]).pretty
