import ExpandingCodes.Computation.TesterBackendComplete
import ExpandingCodes.Computation.TesterGram

set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterAssembly
open NKtLB GaussianProgram TapeArrays
open ExpandingCodes.PolynomialStretch

def view (degree : ℕ) (d : TapeStore (80+6*degree) 3) : TapeStore 80 3 :=
  d.projectStorage (TesterGram.low degree) id

theorem low_injective (degree : ℕ) : Function.Injective (TesterGram.low degree) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin (80+6*degree) => x.val) h

def backend (θ : ℚ) (degree : ℕ) :=
  (TesterBackendComplete.program θ).renameStorage (TesterGram.low degree) id

def program (θ : ℚ) (degree : ℕ) :=
  TapeProgram.seq (TesterGram.construct degree) (backend θ degree)

theorem backend_stops (θ : ℚ) (hθ : θ ≤ 1) (degree n M : ℕ) (inp : Inputs)
    (d : TapeStore (80+6*degree) 3) (y : Word (rowCount degree n))
    (hr : TesterBackendComplete.Ready (fieldExponent degree n) (fieldExponent_pos degree n)
      (rowCount degree n) M (view degree d))
    (ha : ThermometerTable d 0 (fieldSize degree n)
      (fun i : Fin (rowCount degree n*rowCount degree n) => flatEntry (binaryTestTable degree n y) i.val)) :
    ∃ t e, t ≤ TesterBackendComplete.timeBound θ M ∧
      (backend θ degree).Stops inp (d.toCfg (backend θ degree).entry) t e ∧
      e.output = d.output ++ [rankTest (θ : ℝ) (binaryGeometry degree n) y] := by
  obtain ⟨t,c,ht,hc,hco⟩ := TesterBackendComplete.program_stops θ hθ degree n M inp
    (view degree d) y hr ha
  obtain ⟨e,he,_,heo⟩ := hc.liftStorage (TesterGram.low degree) id (low_injective degree)
    Function.injective_id (d.toCfg (backend θ degree).entry) rfl
  exact ⟨t,e,ht,he,heo.trans hco⟩

/-- Compose an actual Gram-prefix trace with the complete actual backend.
The prefix premise contains its executed trace and physical final matrix. -/
theorem program_stops_of_construct (θ : ℚ) (hθ : θ ≤ 1) (degree n M : ℕ)
    (inp : Inputs) (d : TapeStore (80+6*degree) 3) (y : Word (rowCount degree n))
    (t : ℕ) (c : TapeCfg (80+6*degree) 3 _)
    (hc : (TesterGram.construct degree).Stops inp (d.toCfg (TesterGram.construct degree).entry) t c)
    (hr : TesterBackendComplete.Ready (fieldExponent degree n) (fieldExponent_pos degree n)
      (rowCount degree n) M (view degree c.store))
    (ha : ThermometerTable c.store 0 (fieldSize degree n)
      (fun i : Fin (rowCount degree n*rowCount degree n) => flatEntry (binaryTestTable degree n y) i.val))
    (ho : c.output = []) :
    ∃ s e, s ≤ t+1+TesterBackendComplete.timeBound θ M ∧
      (program θ degree).Stops inp (d.toCfg (program θ degree).entry) s e ∧
      e.output = [rankTest (θ : ℝ) (binaryGeometry degree n) y] := by
  obtain ⟨s,e,hs,he,heo⟩ := backend_stops θ hθ degree n M inp c.store y hr ha
  refine ⟨t+1+s,e.mapPC (TapeProgram.rightLabel _),by omega,?_,?_⟩
  · exact hc.seq he
  · change e.output = _
    simpa only [ho,List.nil_append] using heo

#print axioms backend_stops
#print axioms program_stops_of_construct
end ExpandingCodes.Computation.TesterAssembly
