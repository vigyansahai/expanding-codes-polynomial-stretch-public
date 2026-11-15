import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime

set_option autoImplicit false

open scoped Classical
open NKtLB

theorem ExpandingCodes.Computation.SamplerAssembly.prelude_stops {R : ℕ} (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) (hd : 1 ≤ d) (hk : 0<k) (hn : 2 ≤ n) (hnk : k ≤ n)
    (inp : Inputs) (hi : inp.input=ExpandingCodes.PolynomialStretch.sizeInput n) (M : ℕ) (hM : ExpandingCodes.PolynomialStretch.SamplerEnvelopeCovers d k n M) :
    ∃ t e,t ≤ ExpandingCodes.Computation.SamplerAssembly.preludeTime d n M ∧
      (ExpandingCodes.Computation.SamplerAssembly.samplerFrontendProgram r hr d k).Stops inp ((ExpandingCodes.Computation.SamplerAssembly.initialStore R 2).toCfg (ExpandingCodes.Computation.SamplerAssembly.samplerFrontendProgram r hr d k).entry) t e ∧
      e.store=ExpandingCodes.Computation.SamplerAssembly.preludeStore r hr d n k inp ∧ ExpandingCodes.Computation.SamplerAssembly.RuntimeReady r d n k inp M e.store ∧ e.output=[] := by sorry
