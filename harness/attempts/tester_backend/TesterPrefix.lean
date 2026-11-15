import ExpandingCodes.Computation.TesterGramCorrectness
import ExpandingCodes.Computation.TesterEnvelope

set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterPrefix
open NKtLB TesterGram FieldPrograms
open ExpandingCodes.PolynomialStretch

def initialStore (d : ℕ) : TapeStore (80+6*d) 3 :=
  ⟨fun _ => 0,fun _ => 0,[],fun _ => [],fun _ => 0⟩

theorem parameter_injective (d : ℕ) : Function.Injective (parameterLayout d) := by
  intro i j h; apply Fin.ext
  exact congrArg (fun x : Registers d => x.val) h
theorem field_injective (d : ℕ) : Function.Injective (fieldSetupLayout d) := by
  intro i j h; apply Fin.ext
  exact congrArg (fun x : Registers d => x.val) h

def sizeResult (d n : ℕ) : TapeStore (80+6*d) 3 :=
  ParameterPrograms.setupStore (parameterLayout d) d 1
    (SizeReader.sizeStore (low d 0) n (initialStore d))

def copyParameters (d : ℕ) (s : TapeStore (80+6*d) 3) : TapeStore (80+6*d) 3 :=
  let s₁ := (s.setReg (low d 70) (s.reg (low d 4))).setReg (low d 79) 0
  let s₂ := (s₁.setReg (low d 20) (s.reg (low d 2))).setReg (low d 79) 0
  (s₂.setReg (low d 23) (s.reg (low d 3))).setReg (low d 79) 0

def setupResult (d n : ℕ) : TapeStore (80+6*d) 3 :=
  SourceFieldSetup.setupStore (fieldSetupLayout d) (copyParameters d (sizeResult d n))

def setupTime (d n M : ℕ) : ℕ :=
  2*n+4+ParameterPrograms.setupTimeBound d (n+1)+21*M+25+40000*(M+1)^7

structure SetupReady (d n M : ℕ) (s : TapeStore (80+6*d) 3) : Prop where
  bounded : ∀ r,s.reg r ≤ M
  environment : SamplerProgram.Environment (termWorkspace d) (fieldExponent d n)
    (BinaryPolynomial.selectedIndex (fieldExponent d n) (fieldExponent_pos d n)) s
  size : s.reg (low d 70)=rowCount d n
  inputHead : s.roHead 0=n+1
  output : s.output=[]
  buffers : s.bufferTape=fun _ => []
  heads : s.bufferHead=fun _ => 0

theorem setup_initial_stops (d n M : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (inp : Inputs) (tail : List Bool) (hi : inp.input=sizeInput n++tail)
    (hcover : TesterEnvelopeCovers d n M) :
    ∃ t e,t ≤ setupTime d n M ∧
      (TesterGram.setup d).Stops inp ((initialStore d).toCfg (TesterGram.setup d).entry) t e ∧
      e.store=setupResult d n ∧ SetupReady d n M e.store := by
  have hread := SizeReader.sizeInput_unary (low d 0) inp n tail (initialStore d) rfl (by
    simpa only [sizeInput,List.append_assoc,List.singleton_append] using hi)
  have hb : ∀ j,(SizeReader.sizeStore (low d 0) n (initialStore d)).reg j ≤ n+1 := by
    intro j
    by_cases h:j=low d 0
    · subst j; simp [SizeReader.sizeStore,initialStore,TapeStore.setReg]
    · simp [SizeReader.sizeStore,initialStore,TapeStore.setReg,h]
  obtain ⟨t₀,c₀,ht₀,h₀,hs₀,hb₀⟩ := ParameterPrograms.setup_stops (parameterLayout d)
    (parameter_injective d) d 1 (by decide) inp (n+1) (by omega)
    (SizeReader.sizeStore (low d 0) n (initialStore d)) hb
    (by simp [parameterLayout,SizeReader.sizeStore]; omega)
    (by simp [parameterLayout,SizeReader.sizeStore]; omega)
  have hs₀' : c₀.store=sizeResult d n := hs₀
  have hvalues := ParameterPrograms.setupStore_values (parameterLayout d) (parameter_injective d)
    d 1 hd (by decide) (SizeReader.sizeStore (low d 0) n (initialStore d))
    (by simpa [parameterLayout,SizeReader.sizeStore] using hn)
    (by simp [parameterLayout,SizeReader.sizeStore]; omega)
  have hv4 : c₀.reg (low d 4)=rowCount d n := by
    change c₀.store.reg (low d 4)=_
    rw [hs₀]
    simpa [parameterLayout,SizeReader.sizeStore] using hvalues.2.2.2.2.1
  have hv2 : c₀.reg (low d 2)=fieldExponent d n := by
    change c₀.store.reg (low d 2)=_
    rw [hs₀]
    simpa [parameterLayout,SizeReader.sizeStore] using hvalues.2.2.1
  have hv3 : c₀.reg (low d 3)=fieldSize d n := by
    change c₀.store.reg (low d 3)=_
    rw [hs₀]
    simpa [parameterLayout,SizeReader.sizeStore] using hvalues.2.2.2.1
  have hb₀' : ∀ j,c₀.reg j ≤ M := fun j => (hb₀ j).trans hcover.setup
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := SamplerEvaluation.copy_stops_bound
    (low d 4) (low d 70) (low d 79) (by simp [low]) (by simp [low]) (by simp [low]) inp M c₀.store hb₀'
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂,hb₂⟩ := SamplerEvaluation.copy_stops_bound
    (low d 2) (low d 20) (low d 79) (by simp [low]) (by simp [low]) (by simp [low]) inp M c₁.store hb₁
  obtain ⟨t₃,c₃,ht₃,h₃,hs₃,hb₃⟩ := SamplerEvaluation.copy_stops_bound
    (low d 3) (low d 23) (low d 79) (by simp [low]) (by simp [low]) (by simp [low]) inp M c₂.store hb₂
  have hp : c₃.store=copyParameters d (sizeResult d n) := by
    rw [hs₃,hs₂,hs₁,hs₀']
    simp [copyParameters,TapeStore.setReg,low]
  have hell : c₃.reg (fieldSetupLayout d 20)=fieldExponent d n := by
    change c₃.store.reg (fieldSetupLayout d 20)=_
    rw [hs₃,hs₂,hs₁]
    simpa [fieldSetupLayout,TapeStore.setReg,low] using hv2
  have hq : c₃.reg (fieldSetupLayout d 23)=2^fieldExponent d n := by
    change c₃.store.reg (fieldSetupLayout d 23)=_
    rw [hs₃,hs₂,hs₁]
    simpa [fieldSetupLayout,TapeStore.setReg,low,fieldSize] using hv3
  have hm : c₃.reg (low d 70)=rowCount d n := by
    change c₃.store.reg (low d 70)=_
    rw [hs₃,hs₂,hs₁]
    simpa [TapeStore.setReg,low] using hv4
  obtain ⟨t₄,c₄,ht₄,h₄,hs₄,henv,hframe,hb₄,hdata⟩ := SourceFieldSetup.setup_stops
    (fieldSetupLayout d) (field_injective d) inp (fieldExponent d n) (fieldExponent_pos d n) M
    c₃.store hb₃ hell hq hcover.coefficients hcover.twiceField (by
      simpa only [fieldSize,pow_two,← pow_add,two_mul] using hcover.square)
  have houtside : ∀ i : Fin 32, low d 70 ≠ fieldSetupLayout d i := by
    intro i h
    have hh := congrArg (fun x : Registers d => x.val) h
    change 70=i.val at hh
    have := i.isLt
    omega
  have hro : FieldConvolution.tapeData c₃.store =
      FieldConvolution.tapeData (SizeReader.sizeStore (low d 0) n (initialStore d)) := by
    rw [hs₃,hs₂,hs₁]
    simp only [FieldConvolution.tapeData_setReg]
    rw [hs₀]
    have h := ParameterPrograms.setupStore_payload (parameterLayout d) (parameter_injective d) d 1
      (SizeReader.sizeStore (low d 0) n (initialStore d))
    exact congrArg₂ Prod.mk h.1 (congrArg₂ Prod.mk h.2.1
      (congrArg₂ Prod.mk h.2.2.1 h.2.2.2))
  have hfinalData := hdata.trans hro
  have hall := ((((hread.seq h₀).seq h₁).seq h₂).seq h₃).seq h₄
  refine ⟨_,c₄.mapPC (TapeProgram.rightLabel _),?_,hall,?_,?_⟩
  · change 0+2*n+3+1+t₀+1+t₁+1+t₂+1+t₃+1+t₄ ≤ setupTime d n M
    unfold setupTime
    omega
  · change c₄.store=setupResult d n
    rw [hs₄,hp]
    rfl
  · change SetupReady d n M c₄.store
    refine ⟨hb₄,?_,(hframe _ houtside).trans hm,?_,?_,?_,?_⟩
    · exact ⟨henv.2.2.2.1,henv.2.2.1,henv.2.1,henv.2.2.2.2.1⟩
    · have hh := congrArg (fun v => v.1 0) hfinalData
      simpa [FieldConvolution.tapeData,SizeReader.sizeStore,initialStore,TapeStore.setReg] using hh
    · exact congrArg (fun v => v.2.1) hfinalData
    · exact congrArg (fun v => v.2.2.1) hfinalData
    · exact congrArg (fun v => v.2.2.2) hfinalData

def markers (d : ℕ) :=
  TapeProgram.seq (TapeProgram.seq
    (TapeArrays.initializeBuffer (R := 80+6*d) (0 : Fin 3))
    (TapeArrays.initializeBuffer (1 : Fin 3))) (TapeArrays.initializeBuffer (2 : Fin 3))

def markedStore (d : ℕ) (s : TapeStore (80+6*d) 3) : TapeStore (80+6*d) 3 :=
  TapeArrays.painted (TapeArrays.painted (TapeArrays.painted s 0 .bot) 1 .bot) 2 .bot

theorem markers_stops (d : ℕ) (inp : Inputs) (s : TapeStore (80+6*d) 3) :
    (markers d).Stops inp (s.toCfg (markers d).entry) 5
      ((markedStore d s).toCfg (TapeProgram.rightLabel 4 (1 : Fin 2))) := by
  have h₀ := TapeMacros.cell_stops (0 : Fin 3) (fun _ => (Sym.bot,Move.right)) inp s
  have h₁ := TapeMacros.cell_stops (1 : Fin 3) (fun _ => (Sym.bot,Move.right)) inp
    (TapeArrays.painted s 0 .bot)
  have h₂ := TapeMacros.cell_stops (2 : Fin 3) (fun _ => (Sym.bot,Move.right)) inp
    (TapeArrays.painted (TapeArrays.painted s 0 .bot) 1 .bot)
  exact (h₀.seq h₁).seq h₂

theorem markedStore_tapes (d : ℕ) (s : TapeStore (80+6*d) 3)
    (ht : s.bufferTape=fun _ => []) (hh : s.bufferHead=fun _ => 0) :
    (markedStore d s).bufferTape=(fun _ => [.bot]) ∧
    (markedStore d s).bufferHead=(fun _ => 1) := by
  constructor <;> funext b <;> fin_cases b <;>
    simp [markedStore,TapeArrays.painted,TapeMacros.cellStore,ht,hh,Machine.writeAt,Machine.moveHead]

theorem markedStore_bottom (d : ℕ) (s : TapeStore (80+6*d) 3)
    (ht : s.bufferTape=fun _ => []) (hh : s.bufferHead=fun _ => 0) (b : Fin 3) :
    TapeArrays.BottomMarked (markedStore d s) b := by
  rw [TapeArrays.BottomMarked,(markedStore_tapes d s ht hh).1]
  constructor
  · rfl
  · intro k hk
    cases k with
    | zero => omega
    | succ k => simp

structure InputReady (d n M : ℕ) (y : Word (rowCount d n))
    (s : TapeStore (80+6*d) 3) : Prop where
  bounded : ∀ r,s.reg r ≤ M
  environment : SamplerProgram.Environment (termWorkspace d) (fieldExponent d n)
    (BinaryPolynomial.selectedIndex (fieldExponent d n) (fieldExponent_pos d n)) s
  size : s.reg (low d 70)=rowCount d n
  output : s.output=[]
  table : TapeArrays.ThermometerTable s 2 (fieldSize d n) (fun z => if y z≠0 then 1 else 0)
  inputHead : s.bufferHead 2 ≤ M
  gramHead : s.bufferHead 0=1
  spareHead : s.bufferHead 1=1
  marked : ∀ b,TapeArrays.BottomMarked s b

def inputTime (d n M : ℕ) : ℕ :=
  7*M+14+rowCount d n*(20*(M+1)+2)+1

theorem input_stops (d n M : ℕ) (inp : Inputs) (y : Word (rowCount d n))
    (hi : inp.input=sizeInput n++wordBits y) (s : TapeStore (80+6*d) 3)
    (hs : SetupReady d n M s) (hcover : TesterEnvelopeCovers d n M) :
    ∃ t e,t ≤ inputTime d n M ∧ (TesterGram.input d).Stops inp
      (s.toCfg (TesterGram.input d).entry) t e ∧ InputReady d n M y e.store := by
  have hmarks := markers_stops d inp s
  let marked := markedStore d s
  have htapes := markedStore_tapes d s hs.buffers hs.heads
  have hb : ∀ j,marked.reg j ≤ M := hs.bounded
  obtain ⟨t,c,ht,hc,hcs,hcb⟩ := SamplerEvaluation.copy_stops_bound
    (low d 70) (low d 76) (low d 2) (by simp [low]) (by simp [low]) (by simp [low]) inp M marked hb
  have hr (j : Fin 80) (hj : j≠76) (hj2 : j≠2) : c.reg (low d j)=s.reg (low d j) := by
    change c.store.reg (low d j)=_
    rw [hcs]
    simp [Fin.ext_iff] at hj hj2
    simp [TapeStore.setReg,low,Function.update,Fin.ext_iff,hj,hj2,marked,markedStore,TapeArrays.painted,TapeMacros.cellStore]
  have hcount : c.reg (inputLayout d 4)=rowCount d n := by
    change c.store.reg (inputLayout d 4)=_
    rw [hcs]
    simpa [inputLayout,TapeStore.setReg,low,marked,markedStore,TapeArrays.painted,TapeMacros.cellStore] using hs.size
  have hwidth : c.store.reg (inputLayout d 0)=fieldSize d n := hr 23 (by decide) (by decide) |>.trans hs.environment.cardinal
  have hro : c.roHead 0=n+1 := by
    change c.store.roHead 0=_
    rw [hcs]
    exact hs.inputHead
  have hhead : c.bufferHead 2=1 := by
    change c.store.bufferHead 2=_
    rw [hcs]
    exact congrFun htapes.2 2
  have hmarked (b : Fin 3) : TapeArrays.BottomMarked c.store b := by
    rw [hcs]
    exact markedStore_bottom d s hs.buffers hs.heads b
  have hri : Function.Injective (inputLayout d) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [inputLayout,low]
  obtain ⟨u,hu,hload,hloadB,hloadRO,hloadH,hloadMark,hloadTable⟩ := TesterInput.load_stops
    (inputLayout d) hri 2 inp M (by have := hcover.two;omega)
    (rowCount d n) (n+1) (fun z => decide (y z≠0)) c.store hcb
    (by rw [hwidth];exact (fieldSize_pos d n)) hcount hro hhead (hmarked 2) (by
      intro j
      simpa using TesterInput.word_symbols inp n _ y hi j)
  let post := TesterInput.loadStore (inputLayout d) 2 inp (rowCount d n) c.store
  have hframe (j : Fin 80) (hj1 : j≠79) (hj2 : j≠78) (hj3 : j≠5) (hj4 : j≠76)
      (hj5 : j≠2) : post.reg (low d j)=s.reg (low d j) := by
    rw [TesterInput.loadStore_register_frame (inputLayout d) hri 2 inp _ c.store]
    · exact hr j hj4 hj5
    · simpa [inputLayout,low,Fin.ext_iff] using And.intro hj1 (And.intro hj2 (And.intro hj3 hj4))
  refine ⟨5+1+t+1+u,_,?_,(hmarks.seq hc).seq hload,?_⟩
  · unfold inputTime
    omega
  · change InputReady d n M y post
    refine ⟨hloadB,?_,hframe 70 (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans hs.size,?_,?_,?_,?_,?_,?_⟩
    · apply hs.environment.frame
      intro i hi
      rcases hi with rfl|rfl|rfl|rfl <;>
        exact hframe _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [TesterInput.loadStore_output]
      rw [hcs]
      exact hs.output
    · have hw : c.reg (inputLayout d 0)=fieldSize d n := hwidth
      simpa only [hw,decide_eq_true_eq] using hloadTable
    · rw [hloadH,hwidth]
      exact hcover.word
    · rw [TesterInput.loadStore_bufferHead_frame _ _ _ (by decide)]
      rw [hcs]
      exact congrFun htapes.2 0
    · rw [TesterInput.loadStore_bufferHead_frame _ _ _ (by decide)]
      rw [hcs]
      exact congrFun htapes.2 1
    · intro b
      by_cases hb : b=2
      · subst b;exact hloadMark
      · have hz (k : ℕ) := TesterInput.loadStore_bufferSymbol_frame (inputLayout d) 2 b hb inp
          (rowCount d n) c.store k
        exact ⟨(hz 0).trans (hmarked b).1,fun k hk => by rw [hz];exact (hmarked b).2 k hk⟩

#print axioms setup_initial_stops
#print axioms input_stops
end ExpandingCodes.Computation.TesterPrefix
