import ExpandingCodes.Computation.TesterPrefix

set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterFrontend
open NKtLB TesterGram TesterPrefix
open ExpandingCodes.PolynomialStretch

def program (d : ℕ) := TapeProgram.seq
  (TapeProgram.seq (TesterGram.setup d) (TesterGram.input d))
  (TesterEvaluation.degree (degreeLayout d) d)

theorem degree_injective (d : ℕ) : Function.Injective (degreeLayout d) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [degreeLayout,low]

theorem degree_width (d : ℕ) (s : TapeStore (80+6*d) 3) :
    (TesterEvaluation.degreeStore (degreeLayout d) d s).reg (low d 23)=s.reg (low d 23) := by
  simp [TesterEvaluation.degreeStore,TesterEvaluation.degreeScaled,TesterEvaluation.degreePrepare,
    FieldPrograms.halfStore,SamplerEvaluation.scaleStore,degreeLayout,TapeStore.setReg,low]

theorem degree_stops (d n M : ℕ) (hd : 4 ≤ d) (inp : Inputs)
    (y : Word (rowCount d n)) (s : TapeStore (80+6*d) 3)
    (hs : InputReady d n M y s) (hcover : TesterEnvelopeCovers d n M) :
    ∃ t e,t ≤ (d+1)*(30*(M+1)) ∧
      (TesterEvaluation.degree (degreeLayout d) d).Stops inp
        (s.toCfg (TesterEvaluation.degree (B := 3) (degreeLayout d) d).entry) t e ∧
      Core d (fieldExponent d n) (fieldExponent_pos d n) (auxiliaryDegree (fieldSize d n) d) M
        (fun z => decide (y z≠0)) e.store ∧
      e.output=[] ∧ e.bufferHead 0=1 ∧ e.bufferHead 1=1 ∧
      (∀ b,TapeArrays.BottomMarked e.store b) := by
  have hq : s.reg (degreeLayout d 0)=fieldSize d n := hs.environment.cardinal
  obtain ⟨t,e,ht,he,hes,hval,hframe,heb,hed⟩ := TesterEvaluation.degree_stops
    (degreeLayout d) (degree_injective d) d inp M (by have := hcover.two;omega) s hs.bounded
    (by rw [hq];exact hcover.cutoff)
  have hfield (j : Fin 80) (hj : j≠23 ∧ j≠0 ∧ j≠1 ∧ j≠2 ∧ j≠65) :
      e.reg (low d j)=s.reg (low d j) := by
    apply hframe
    intro i
    rcases hj with ⟨hj23,hj0,hj1,hj2,hj65⟩
    fin_cases i
    · exact (low_eq_iff d j 23).not.mpr hj23
    · exact (low_eq_iff d j 0).not.mpr hj0
    · exact (low_eq_iff d j 1).not.mpr hj1
    · exact (low_eq_iff d j 2).not.mpr hj2
    · exact (low_eq_iff d j 65).not.mpr hj65
  have htapes : e.bufferTape=s.bufferTape := congrArg (fun v => v.2.2.1) hed
  have hheads : e.store.bufferHead=s.bufferHead := congrArg (fun v => v.2.2.2) hed
  refine ⟨t,e,ht,he,?_,?_,?_,?_,?_⟩
  · refine ⟨heb,?_,?_,?_,?_,?_,?_⟩
    · constructor
      · exact (hfield 3 (by decide)).trans hs.environment.modulus
      · exact (hfield 19 (by decide)).trans hs.environment.length
      · change e.store.reg (low d 23)=_
        rw [hes,degree_width]
        exact hs.environment.cardinal
      · exact (hfield 24 (by decide)).trans hs.environment.square
    · change e.reg (low d 65)=_
      rw [TesterEvaluation.auxiliaryDegree_nat _ _ hd (fieldSize_ge_two d n)]
      change e.reg (low d 65)=((d-3)*(s.reg (low d 23)-1)-1)/2 at hval
      have hhq : s.reg (low d 23)=fieldSize d n := hs.environment.cardinal
      rw [hhq] at hval
      exact hval
    · exact (hfield 70 (by decide)).trans hs.size
    · simpa only [TapeArrays.BottomMarked,htapes] using hs.marked 2
    · simpa only [TapeArrays.ThermometerTable,TapeArrays.ThermometerAt,htapes,
        decide_eq_true_eq,fieldSize,rowCount] using hs.table
    · rw [hheads]
      exact hs.inputHead
  · exact (congrArg (fun v => v.2.1) hed).trans hs.output
  · change e.store.bufferHead 0=1
    rw [hheads]
    exact hs.gramHead
  · change e.store.bufferHead 1=1
    rw [hheads]
    exact hs.spareHead
  · intro b
    simpa only [TapeArrays.BottomMarked,htapes] using hs.marked b

def time (d n M : ℕ) : ℕ := setupTime d n M+inputTime d n M+2+(d+1)*(30*(M+1))

theorem program_stops (d n M : ℕ) (hd : 4 ≤ d) (hn : 2 ≤ n)
    (inp : Inputs) (y : Word (rowCount d n)) (hi : inp.input=sizeInput n++wordBits y)
    (hcover : TesterEnvelopeCovers d n M) :
    ∃ t e,t ≤ time d n M ∧
      (program d).Stops inp ((initialStore d).toCfg (program d).entry) t e ∧
      Core d (fieldExponent d n) (fieldExponent_pos d n) (auxiliaryDegree (fieldSize d n) d) M
        (fun z => decide (y z≠0)) e.store ∧
      e.output=[] ∧ e.bufferHead 0=1 ∧ e.bufferHead 1=1 ∧
      (∀ b,TapeArrays.BottomMarked e.store b) := by
  obtain ⟨t₁,c₁,ht₁,h₁,_,hr₁⟩ := setup_initial_stops d n M (by omega) hn inp (wordBits y) hi hcover
  obtain ⟨t₂,c₂,ht₂,h₂,hr₂⟩ := input_stops d n M inp y hi c₁.store hr₁ hcover
  obtain ⟨t₃,c₃,ht₃,h₃,hcore,hout,hh0,hh1,hmarks⟩ := degree_stops d n M hd inp y c₂.store hr₂ hcover
  exact ⟨t₁+1+t₂+1+t₃,c₃.mapPC (TapeProgram.rightLabel _),by unfold time;omega,
    (h₁.seq h₂).seq h₃,hcore,hout,hh0,hh1,hmarks⟩

theorem setupTimeBound_mono (d : ℕ) : Monotone (ParameterPrograms.setupTimeBound d) := by
  intro a b hab
  unfold ParameterPrograms.setupTimeBound ParameterPrograms.powerTimeBound
    ParameterPrograms.ceilingTimeBound ParameterPrograms.divisionTimeBound ParameterPrograms.floorTimeBound
    ParameterPrograms.setupBound₃ ParameterPrograms.setupBound₂ ParameterPrograms.setupBound₁
    ParameterPrograms.powerCounterBound ParameterPrograms.ceilingCounterBound
  gcongr

def clock (d x M : ℕ) : ℕ :=
  (2*x+4+ParameterPrograms.setupTimeBound d (x+1))+
    (28*M+42+40000*(M+1)^7)+
    (x*(20*(M+1)+2)+(d+1)*(30*(M+1)))

theorem time_le_clock (d n M : ℕ) : time d n M ≤ clock d (rowCount d n+n) M := by
  have hs := setupTimeBound_mono d (show n+1 ≤ rowCount d n+n+1 by omega)
  have hm := Nat.mul_le_mul_right (20*(M+1)+2) (show rowCount d n ≤ rowCount d n+n by omega)
  unfold time setupTime inputTime clock
  omega

theorem clock_polynomial (d : ℕ) : PolynomialBound (fun x => clock d x (testerEnvelope d x)) := by
  have hi := PolynomialBound.identity
  have hM := testerEnvelope_polynomial d
  have hM1 := hM.add (PolynomialBound.const 1)
  have hsetup := ((ParameterPrograms.setup_bounds_polynomial d).1.comp
    (ParameterPrograms.PolynomialMajorant.id.add (ParameterPrograms.PolynomialMajorant.const 1))).toPolynomialBound
  have hfirst := (((PolynomialBound.const 2).mul hi).add (PolynomialBound.const 4)).add hsetup
  have hsecond := (((PolynomialBound.const 28).mul hM).add (PolynomialBound.const 42)).add
    ((PolynomialBound.const 40000).mul (hM1.pow 7))
  have hthird := (hi.mul (((PolynomialBound.const 20).mul hM1).add (PolynomialBound.const 2))).add
    ((PolynomialBound.const (d+1)).mul ((PolynomialBound.const 30).mul hM1))
  exact (hfirst.add hsecond).add hthird

#print axioms program_stops
#print axioms clock_polynomial
end ExpandingCodes.Computation.TesterFrontend
