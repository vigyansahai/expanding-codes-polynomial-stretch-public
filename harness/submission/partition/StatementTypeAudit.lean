-- METADATA ONLY. This file intentionally imports the already closed parent
-- environment to compare statement types. It is never imported by a helper
-- proof, closed helper cache, forwarder, or submitted solution.
import harness.submission.runtime.ProofCore

set_option autoImplicit false
open scoped Classical
open NKtLB

theorem ExpandingCodes.Computation.TapeCompiler.compile_halts {R B L : ℕ} (P : ExpandingCodes.Computation.TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (t : ℕ) (hh : P.halted (P.run inp t)) :
    (ExpandingCodes.Computation.TapeCompiler.compile P).HaltsWith O inp (1+2*t) (bitsSym (P.run inp t).output) := by sorry

theorem ExpandingCodes.Computation.SourceFieldSetup.setup_stops {R B : ℕ} (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (ell : ℕ) (h : 0 < ell) (M : ℕ) (d : ExpandingCodes.Computation.TapeStore R B) (hd : ∀ j,d.reg j ≤ M)
    (hell : d.reg (r 20) = ell) (hq : d.reg (r 23) = 2^ell)
    (hN : 3*ell+1 ≤ M) (h2q : 2*(2^ell) ≤ M) (hQ : 2^(2*ell) ≤ M) :
    ∃ t e,t ≤ 40000*(M+1)^7 ∧ (ExpandingCodes.Computation.SourceFieldSetup.setup r).Stops inp (d.toCfg (ExpandingCodes.Computation.SourceFieldSetup.setup (B:=B) r).entry) t e ∧
      e.store = ExpandingCodes.Computation.SourceFieldSetup.setupStore r d ∧ ExpandingCodes.Computation.SourceFieldSetup.Environment r ell h e.store ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ ExpandingCodes.Computation.FieldConvolution.tapeData e.store = ExpandingCodes.Computation.FieldConvolution.tapeData d := by sorry

theorem ExpandingCodes.Computation.SourceFieldArithmetic.multiply_stops {R B : ℕ} (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (h : 0 < ell) (m a b : Fin (2^ell))
    (M : ℕ) (hM : 1 ≤ M) (d : ExpandingCodes.Computation.TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (ha : d.reg (r 0) = a.val) (hb : d.reg (r 1) = b.val)
    (hm : d.reg (r 3) = 2^ell+m.val) (hN : d.reg (r 19) = 3*ell+1)
    (hq : d.reg (r 23) = 2^ell) (hQ : d.reg (r 24) = 2^(2*ell)) :
    ∃ t e, t ≤ 10000*(M+1)^6 ∧
      (ExpandingCodes.Computation.SourceFieldArithmetic.multiply r).Stops inp (d.toCfg (ExpandingCodes.Computation.SourceFieldArithmetic.multiply (B := B) r).entry) t e ∧
      e.store = ExpandingCodes.Computation.SourceFieldArithmetic.multiplyResult r d ∧
      e.reg (r 20) = (ExpandingCodes.PolynomialStretch.BinaryField.multiplyIndex ell h m (ExpandingCodes.PolynomialStretch.BinaryPolynomial.indexEquiv ell a) (ExpandingCodes.PolynomialStretch.BinaryPolynomial.indexEquiv ell b)).val ∧
      (∀ i, i < 2 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j, (∀ i, j ≠ r i) → e.reg j = d.reg j) ∧
      (∀ j, e.reg j ≤ M) ∧ ExpandingCodes.Computation.FieldConvolution.tapeData e.store = ExpandingCodes.Computation.FieldConvolution.tapeData d := by sorry

theorem ExpandingCodes.Computation.SourceFieldArithmetic.addition_stops {R B : ℕ} (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (a b : Fin (2^ell)) (M : ℕ) (hM : 1 ≤ M)
    (d : ExpandingCodes.Computation.TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (ha : d.reg (r 0) = a.val) (hb : d.reg (r 3) = b.val)
    (hN : d.reg (r 19) = 3*ell+1) (hq : d.reg (r 23) = 2^ell) :
    ∃ t e,t ≤ 3000*(M+1)^5 ∧
      (ExpandingCodes.Computation.SourceFieldArithmetic.addition r).Stops inp (d.toCfg (ExpandingCodes.Computation.SourceFieldArithmetic.addition (B:=B) r).entry) t e ∧ e.store = ExpandingCodes.Computation.SourceFieldArithmetic.additionResult r d ∧
      e.reg (r 20) = (ExpandingCodes.PolynomialStretch.BinaryField.addIndex ell a b).val ∧
      (∀ i,i = 0 ∨ i = 3 ∨ i = 19 ∨ 23 ≤ i → i ≠ 25 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ ExpandingCodes.Computation.FieldConvolution.tapeData e.store = ExpandingCodes.Computation.FieldConvolution.tapeData d := by sorry

theorem ExpandingCodes.Computation.SourceFieldArithmetic.inverse_stops {R B : ℕ} (r : Fin 31 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell)) (M : ℕ) (hM : 1 ≤ M)
    (d : ExpandingCodes.Computation.TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hs : ExpandingCodes.Computation.SourceFieldArithmetic.InverseSetup r ell h a d) :
    ∃ t e,t ≤ 20000*(M+1)^7 ∧ (ExpandingCodes.Computation.SourceFieldArithmetic.inverse r).Stops inp (d.toCfg (ExpandingCodes.Computation.SourceFieldArithmetic.inverse (B:=B) r).entry) t e ∧
      e.store = ExpandingCodes.Computation.SourceFieldArithmetic.inverseResult r d ∧ e.reg (r 27) = (ExpandingCodes.PolynomialStretch.BinaryField.inverseIndex ell h a).val ∧
      (∀ i,i = 0 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ ExpandingCodes.Computation.FieldConvolution.tapeData e.store = ExpandingCodes.Computation.FieldConvolution.tapeData d := by sorry

theorem ExpandingCodes.Computation.SamplerProgram.layer_stops {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (hk : k≤2^ell) (hb : 0<b) (hM : 1≤M) (caps : ExpandingCodes.Computation.SamplerProgram.LayerCaps d k ell b M)
    (inp : Inputs) (s : ExpandingCodes.Computation.TapeStore (ExpandingCodes.Computation.SamplerProgram.Storage.registers d k) 2)
    (hs : ExpandingCodes.Computation.SamplerProgram.LayerInvariant d k ell b h forms hashes z M s) :
    ∃ t e,t≤ExpandingCodes.Computation.SamplerProgram.layerTimeBound d k i M ∧
      (ExpandingCodes.Computation.SamplerProgram.layer d k i).Stops inp (s.toCfg (ExpandingCodes.Computation.SamplerProgram.layer d k i).entry) t e ∧
      ExpandingCodes.Computation.SamplerProgram.LayerInvariant d k ell b h forms hashes z M e.store ∧ ExpandingCodes.Computation.TapeStore.SamePayload e.store s ∧
      e.reg (ExpandingCodes.Computation.SamplerProgram.Storage.neighbor d k i)=i.val*b+
        (ExpandingCodes.Computation.EncodedSampler.neighbor (ExpandingCodes.PolynomialStretch.BinaryField.indexOperations ell h) forms hashes i z).val ∧
      (∀ j,e.reg (ExpandingCodes.Computation.SamplerProgram.Storage.point d k j)=s.reg (ExpandingCodes.Computation.SamplerProgram.Storage.point d k j)) ∧
      (∀ j,e.reg (ExpandingCodes.Computation.SamplerProgram.Storage.countdown d k j)=s.reg (ExpandingCodes.Computation.SamplerProgram.Storage.countdown d k j)) ∧
      (∀ a : Fin 80,(32≤a.val ∧ a.val<46) ∨ (60≤a.val ∧ a.val<69) →
        e.reg (ExpandingCodes.Computation.SamplerProgram.Storage.low d k a)=s.reg (ExpandingCodes.Computation.SamplerProgram.Storage.low d k a)) ∧
      e.output=s.output ∧
      (∀ a : Fin k,a≠i → e.reg (ExpandingCodes.Computation.SamplerProgram.Storage.neighbor d k a)=s.reg (ExpandingCodes.Computation.SamplerProgram.Storage.neighbor d k a)) ∧
      ExpandingCodes.Computation.SamplerProgram.LayerFrame d k i s e.store := by sorry

theorem ExpandingCodes.Computation.SamplerAssembly.prelude_stops {R : ℕ} (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) (hd : 1 ≤ d) (hk : 0<k) (hn : 2 ≤ n) (hnk : k ≤ n)
    (inp : Inputs) (hi : inp.input=ExpandingCodes.PolynomialStretch.sizeInput n) (M : ℕ) (hM : ExpandingCodes.PolynomialStretch.SamplerEnvelopeCovers d k n M) :
    ∃ t e,t ≤ ExpandingCodes.Computation.SamplerAssembly.preludeTime d n M ∧
      (ExpandingCodes.Computation.SamplerAssembly.samplerFrontendProgram r hr d k).Stops inp ((ExpandingCodes.Computation.SamplerAssembly.initialStore R 2).toCfg (ExpandingCodes.Computation.SamplerAssembly.samplerFrontendProgram r hr d k).entry) t e ∧
      e.store=ExpandingCodes.Computation.SamplerAssembly.preludeStore r hr d n k inp ∧ ExpandingCodes.Computation.SamplerAssembly.RuntimeReady r d n k inp M e.store ∧ e.output=[] := by sorry

theorem ExpandingCodes.Computation.TesterFrontend.program_stops (d n M : ℕ) (hd : 4 ≤ d) (hn : 2 ≤ n)
    (inp : Inputs) (y : ExpandingCodes.PolynomialStretch.Word (ExpandingCodes.PolynomialStretch.rowCount d n)) (hi : inp.input=ExpandingCodes.PolynomialStretch.sizeInput n++ExpandingCodes.PolynomialStretch.wordBits y)
    (hcover : ExpandingCodes.PolynomialStretch.TesterEnvelopeCovers d n M) :
    ∃ t e,t ≤ ExpandingCodes.Computation.TesterFrontend.time d n M ∧
      (ExpandingCodes.Computation.TesterFrontend.program d).Stops inp ((ExpandingCodes.Computation.TesterPrefix.initialStore d).toCfg (ExpandingCodes.Computation.TesterFrontend.program d).entry) t e ∧
      ExpandingCodes.Computation.TesterGram.Core d (ExpandingCodes.PolynomialStretch.fieldExponent d n) (ExpandingCodes.PolynomialStretch.fieldExponent_pos d n) (ExpandingCodes.PolynomialStretch.auxiliaryDegree (ExpandingCodes.PolynomialStretch.fieldSize d n) d) M
        (fun z => decide (y z≠0)) e.store ∧
      e.output=[] ∧ e.bufferHead 0=1 ∧ e.bufferHead 1=1 ∧
      (∀ b,ExpandingCodes.Computation.TapeArrays.BottomMarked e.store b) := by sorry

theorem ExpandingCodes.Computation.TesterGram.program_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
    (y : Fin ((2^ell)^d) → Bool) (inp : Inputs) (s : ExpandingCodes.Computation.TapeStore (80+6*d) 3)
    (hc : ExpandingCodes.Computation.TesterGram.Core d ell h D M y s) (hh : s.bufferHead 0=1)
    (hm : ExpandingCodes.Computation.TapeArrays.BottomMarked s 0) (hsp : ExpandingCodes.Computation.TapeArrays.BottomMarked s 1)
    (hdM : d*((2^ell)-1) ≤ M) (hhead : 1+(2^ell)^d*(2^ell) ≤ M)
    (hmatrix : (2^ell)^d*(2^ell)^d ≤ M) :
    ∃ t e,t ≤ ExpandingCodes.Computation.TesterGram.programTime d M ((2^ell)^d) ∧ (ExpandingCodes.Computation.TesterGram.program d).Stops inp (s.toCfg (ExpandingCodes.Computation.TesterGram.program d).entry) t e ∧
      ExpandingCodes.Computation.TesterGram.BuildState d ell h D M y s ((2^ell)^d*(2^ell)^d) e.store := by sorry

theorem ExpandingCodes.Computation.GaussianDriver.rankProgram_stops_canonical (degree n M : ℕ) (inp : Inputs) (d : ExpandingCodes.Computation.GaussianProgram.Store)
    (y : ExpandingCodes.PolynomialStretch.Word (ExpandingCodes.PolynomialStretch.rowCount degree n))
    (hc : ExpandingCodes.Computation.GaussianDriver.Common (ExpandingCodes.PolynomialStretch.fieldExponent degree n) (ExpandingCodes.PolynomialStretch.fieldExponent_pos degree n) (ExpandingCodes.PolynomialStretch.rowCount degree n) M d)
    (B : ExpandingCodes.Computation.Gaussian.Table (Fin (ExpandingCodes.PolynomialStretch.fieldSize degree n)) (ExpandingCodes.PolynomialStretch.rowCount degree n) (ExpandingCodes.PolynomialStretch.rowCount degree n))
    (ha : ExpandingCodes.Computation.GaussianProgram.MatrixStored d 0 (ExpandingCodes.PolynomialStretch.binaryTestTable degree n y)) (hb : ExpandingCodes.Computation.GaussianProgram.MatrixStored d 1 B) :
    ∃ (t : ℕ) (e : ExpandingCodes.Computation.TapeCfg 64 2 4260),t ≤ 100000*(M+1)^9 ∧
      ExpandingCodes.Computation.GaussianDriver.rankProgram.Stops inp (d.toCfg ExpandingCodes.Computation.GaussianDriver.rankProgram.entry) t e ∧
      ExpandingCodes.Computation.GaussianDriver.Common (ExpandingCodes.PolynomialStretch.fieldExponent degree n) (ExpandingCodes.PolynomialStretch.fieldExponent_pos degree n) (ExpandingCodes.PolynomialStretch.rowCount degree n) M e.store ∧
      e.reg 48 = (ExpandingCodes.PolynomialStretch.testMatrix (ExpandingCodes.PolynomialStretch.binaryGeometry degree n) y).rank ∧
      e.reg 62 = 0 ∧ e.roHead = d.roHead ∧ e.output = d.output := by sorry

open Lean Elab Command
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes false

run_meta do
  let env ← getEnv
  let mut checked : Array Json := #[]
  for target in #[
    `ExpandingCodes.Computation.TapeCompiler.compile_halts,
    `ExpandingCodes.Computation.SourceFieldSetup.setup_stops,
    `ExpandingCodes.Computation.SourceFieldArithmetic.multiply_stops,
    `ExpandingCodes.Computation.SourceFieldArithmetic.addition_stops,
    `ExpandingCodes.Computation.SourceFieldArithmetic.inverse_stops,
    `ExpandingCodes.Computation.SamplerProgram.layer_stops,
    `ExpandingCodes.Computation.SamplerAssembly.prelude_stops,
    `ExpandingCodes.Computation.TesterFrontend.program_stops,
    `ExpandingCodes.Computation.TesterGram.program_stops,
    `ExpandingCodes.Computation.GaussianDriver.rankProgram_stops_canonical  ] do
    let candidates :=  env.constants.toList.filterMap fun (n, ci) =>
      if privateToUserName? n == some target then some (n, ci) else none
    unless candidates.length == 1 do
      throwError "Expected one private original for {target}; got {candidates.map Prod.fst}"
    let (original, orig) := candidates.head!
    let some declared := env.find? target | throwError "Missing statement {target}"
    unless ← Meta.isDefEq orig.type declared.type do
      throwError "Statement type differs from closed original: {target}"
    let printed ← Meta.ppExpr declared.type
    checked := checked.push (Json.mkObj [("name", toJson target.toString),
      ("closed_original", toJson original.toString), ("type", toJson printed.pretty),
      ("exact_type", toJson true)])
  IO.FS.writeFile "harness/submission/partition/statement-type-audit.json" (Json.arr checked).pretty
  logInfo m!"All {checked.size} helper statements exactly match their closed original types"
