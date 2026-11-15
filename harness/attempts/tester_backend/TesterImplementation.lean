import ExpandingCodes.Computation.TesterFrontend
import ExpandingCodes.Computation.TesterAssembly
import ExpandingCodes.Computation.TesterSource
import ExpandingCodes.Construction.ParameterBounds

set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterImplementation
open NKtLB TesterGram
open ExpandingCodes.PolynomialStretch

def clock (θ : ℚ) (d x : ℕ) : ℕ :=
  TesterFrontend.clock d x (testerEnvelope d x)+1+
    programTime d (testerEnvelope d x) x+1+
      TesterBackendComplete.timeBound θ (testerEnvelope d x)

theorem clock_polynomial (θ : ℚ) (d : ℕ) : PolynomialBound (clock θ d) := by
  have hf := TesterFrontend.clock_polynomial d
  have hg := programTime_polynomial d (testerEnvelope_polynomial d) PolynomialBound.identity
  have hb := (TesterBackendComplete.timeBound_polynomial θ).comp (testerEnvelope_polynomial d)
  exact ((((hf.add (PolynomialBound.const 1)).add hg).add (PolynomialBound.const 1)).add hb)

theorem source_stops (θ : ℚ) (hθ : θ ≤ 1) (d n : ℕ) (hd : 4 ≤ d) (hn : 2 ≤ n)
    (y : Word (rowCount d n)) :
    ∃ t e,t ≤ clock θ d (rowCount d n+n) ∧
      (TesterAssembly.program θ d).Stops ⟨sizeInput n++wordBits y,[],[],[]⟩
        ((TesterPrefix.initialStore d).toCfg (TesterAssembly.program θ d).entry) t e ∧
      e.output=[rankTest (θ : ℝ) (binaryGeometry d n) y] := by
  let M := testerEnvelope d (rowCount d n+n)
  let inp : Inputs := ⟨sizeInput n++wordBits y,[],[],[]⟩
  have hc : TesterEnvelopeCovers d n M := testerEnvelope_covers d n (by omega)
  obtain ⟨t₁,c₁,ht₁,h₁,hcore,hout,hh0,hh1,hmarks⟩ :=
    TesterFrontend.program_stops d n M hd hn inp y rfl hc
  have hq0 : 0 < fieldSize d n := fieldSize_pos d n
  have hprod : rowCount d n*rowCount d n*fieldSize d n ≤ M := by have := hc.gram;omega
  have hmatrix : rowCount d n*rowCount d n ≤ M :=
    (Nat.le_mul_of_pos_right _ hq0).trans hprod
  obtain ⟨t₂,c₂,ht₂,h₂,hbuild⟩ := TesterGram.program_stops d (fieldExponent d n)
    (fieldExponent_pos d n) (auxiliaryDegree (fieldSize d n) d) M (by have := hc.two;omega)
    (fun z => decide (y z≠0)) inp c₁.store hcore hh0 (hmarks 0) (hmarks 1)
    hc.digitSum hc.word hmatrix
  have hconstruct : (TesterGram.construct d).Stops inp
      ((TesterPrefix.initialStore d).toCfg (TesterGram.construct d).entry)
      (t₁+1+t₂) (c₂.mapPC (TapeProgram.rightLabel _)) := h₁.seq h₂
  have hlarge : 1 < rowCount d n := by
    have hqrow : fieldSize d n ≤ rowCount d n := Nat.le_self_pow (by omega) _
    have := fieldSize_ge_two d n
    omega
  have hready : TesterBackendComplete.Ready (fieldExponent d n) (fieldExponent_pos d n)
      (rowCount d n) M (TesterAssembly.view d c₂.store) := by
    refine ⟨?_,?_,?_,?_,?_,?_,hlarge,hprod,?_,?_,hbuild.marked,hbuild.spareMarked⟩
    · intro r
      exact hbuild.core.bounded (low d r)
    · exact hbuild.core.environment.cardinal
    · exact hbuild.core.environment.square
    · exact hbuild.core.environment.length
    · exact hbuild.core.environment.modulus
    · exact hbuild.core.size
    · change c₂.bufferHead 0 ≤ (M+1)^2
      have hh : c₂.bufferHead 0 ≤ M := hbuild.head.trans_le hc.gram
      nlinarith
    · exact hbuild.spareHead.trans hh1
  have htable : TapeArrays.ThermometerTable c₂.store 0 (fieldSize d n)
      (fun k : Fin (rowCount d n*rowCount d n) => GaussianProgram.flatEntry (binaryTestTable d n y) k.val) :=
    hbuild.table
  have houtput : c₂.output=[] := hbuild.output.trans hout
  obtain ⟨t,e,ht,he,heo⟩ := TesterAssembly.program_stops_of_construct θ hθ d n M inp
    (TesterPrefix.initialStore d) y (t₁+1+t₂) (c₂.mapPC (TapeProgram.rightLabel _)) hconstruct
    hready htable houtput
  refine ⟨t,e,?_,he,heo⟩
  change t₂ ≤ programTime d M (rowCount d n) at ht₂
  have hf := TesterFrontend.time_le_clock d n M
  have hg := programTime_mono_m d M (show rowCount d n ≤ rowCount d n+n by omega)
  unfold clock
  dsimp only [M] at *
  omega

end ExpandingCodes.Computation.TesterImplementation

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation

theorem binary_tester_implementation_source (θ : ℚ)
    (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2) :
    TesterImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) := by
  let d := dimension (θ : ℝ)
  have hd : 4 ≤ d := dimension_ge_four _ hθ
  have hθ1 : θ ≤ 1 := by exact_mod_cast (show (θ : ℝ) ≤ 1 by linarith [hθ.2])
  apply binary_tester_of_source θ (TesterAssembly.program θ d) (TesterImplementation.clock θ d) 2
    (TesterImplementation.clock_polynomial θ d)
  intro n hn y
  obtain ⟨t,e,ht,he,heo⟩ := TesterImplementation.source_stops θ hθ1 d n hd hn y
  have hr := he.exec.iterate
  change (TesterAssembly.program θ d).run ⟨sizeInput n++wordBits y,[],[],[]⟩ t=e at hr
  exact ⟨t,ht,by rw [hr];exact he.halted,by rw [hr];exact heo⟩

#print axioms binary_tester_implementation_source
end ExpandingCodes.PolynomialStretch
