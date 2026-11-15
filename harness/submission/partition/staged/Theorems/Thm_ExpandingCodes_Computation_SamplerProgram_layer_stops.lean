import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime

set_option autoImplicit false

open scoped Classical
open NKtLB

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
