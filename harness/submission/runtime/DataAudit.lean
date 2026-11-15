import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime
open Lean Elab Command
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes false

run_meta do
  let env ← getEnv
  let modules := env.header.moduleNames
  let mut checked : Array Json := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    unless modules[idx.toNat]? == some `Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime do continue
    let axioms ← collectAxioms n
    unless axioms.all (fun a => #[`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Unexpected axioms for {n}: {axioms}"
    checked := checked.push (Json.mkObj [("name", toJson n.toString),
      ("axioms", toJson (axioms.map Name.toString))])
  IO.FS.writeFile "harness/submission/runtime/data-axioms.json" (Json.arr checked).pretty
  logInfo m!"Audited {checked.size} data declarations: only standard axioms"
