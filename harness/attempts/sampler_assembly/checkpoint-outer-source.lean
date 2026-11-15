import ExpandingCodes.Computation.ParameterSetup
import ExpandingCodes.Computation.RandomTables
import ExpandingCodes.Computation.SourceFieldSetup
import ExpandingCodes.Computation.SamplerEvaluation
import ExpandingCodes.Computation.SamplerProgram
import ExpandingCodes.Computation.SamplerOdometer
import ExpandingCodes.Computation.NeighborWriter
import ExpandingCodes.Computation.SamplerEnvelope
import ExpandingCodes.Computation.SamplerRows

set_option autoImplicit false
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false
namespace ExpandingCodes.Computation.SamplerAssembly
open NKtLB UnaryArithmetic FieldPrograms ParameterPrograms SamplerEvaluation
open ExpandingCodes.PolynomialStretch
variable {R B : ℕ}

/-- The sampler prelude uses the agreed fixed low eighty registers. -/
def sizeLayout (r : Fin 80 → Fin R) (i : Fin 14) : Fin R := r ⟨32+i.val,by omega⟩
def randomRegisters (r : Fin 80 → Fin R) (i : Fin 6) : Fin R := r ⟨46+i.val,by omega⟩

def randomLayout (r : Fin 80 → Fin R) (hr : Function.Injective r) : RandomTables.Layout R where
  random.reg := ⟨randomRegisters r,by
    intro i j h
    apply Fin.ext
    have hh := congrArg Fin.val (hr h)
    simp only [randomRegisters,Fin.val_mk] at hh
    omega⟩
  count := r 52
  fresh j := by
    intro h
    have hh := congrArg Fin.val (hr h)
    have hj := j.isLt
    simp only [randomRegisters,Fin.val_mk] at hh
    omega

theorem sizeLayout_injective (r : Fin 80 → Fin R) (hr : Function.Injective r) :
    Function.Injective (sizeLayout r) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val (hr h)
  simp only [sizeLayout,Fin.val_mk] at hh
  omega

/-- Two real preserving copies install the random entry length and width. -/
def prepareRandom (r : Fin 80 → Fin R) (ell width : Fin 80) : TapeProgram R B 22 :=
  TapeProgram.seq (TapeMacros.copy (r ell) (r 46) (r 51))
    (TapeMacros.copy (r width) (r 47) (r 51))

def prepareRandomStore (r : Fin 80 → Fin R) (ell width : Fin 80)
    (s : TapeStore R B) : TapeStore R B :=
  let c := (s.setReg (r 46) (s.reg (r ell))).setReg (r 51) 0
  (c.setReg (r 47) (c.reg (r width))).setReg (r 51) 0

theorem prepareRandom_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (ell width : Fin 80) (he : ell≠46 ∧ ell≠51) (hw : width≠47 ∧ width≠51)
    (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M) :
    ∃ t e,t ≤ 14*M+15 ∧
      (prepareRandom r ell width).Stops inp
        (s.toCfg (prepareRandom (B:=B) r ell width).entry) t e ∧
      e.store=prepareRandomStore r ell width s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := copy_stops_bound (r ell) (r 46) (r 51)
    (hr.ne he.1) (hr.ne he.2) (hr.ne (by decide)) inp M s hs
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂,hb₂⟩ := copy_stops_bound (r width) (r 47) (r 51)
    (hr.ne hw.1) (hr.ne hw.2) (hr.ne (by decide)) inp M c₁.store hb₁
  have hall := h₁.seq h₂
  refine ⟨_,_,by omega,hall,?_,hb₂⟩
  change c₂.store=_
  rw [hs₂,hs₁]
  rfl

theorem prepareRandomStore_values (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (ell width : Fin 80) (hw : width≠46 ∧ width≠51) (s : TapeStore R B) :
    (prepareRandomStore r ell width s).reg (r 46)=s.reg (r ell) ∧
    (prepareRandomStore r ell width s).reg (r 47)=s.reg (r width) ∧
    (prepareRandomStore r ell width s).reg (r 51)=0 := by
  simp [prepareRandomStore,SamplerEvaluation.reg_layout r hr,hw.1,hw.2]

theorem prepareRandomStore_fresh (r : Fin 80 → Fin R) (ell width : Fin 80)
    (s : TapeStore R B) (j : Fin R) (ha : j≠r 46) (hb : j≠r 47) (hc : j≠r 51) :
    (prepareRandomStore r ell width s).reg j=s.reg j := by
  simp [prepareRandomStore,TapeStore.setReg,ha,hb,hc]

/-- The bottom marker is written by an actual one-cell source instruction. -/
def initializeStore (s : TapeStore R B) (b : Fin B) : TapeStore R B := TapeArrays.painted s b .bot

def markedFill (l : RandomTables.Layout R) (b : Fin B) : TapeProgram R B 57 :=
  TapeProgram.seq (TapeArrays.initializeBuffer b) (RandomTables.fill l b)

def markedFillStore (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) : TapeStore R B :=
  RandomTables.fillStore l b inp K (initializeStore s b)

theorem initializeStore_head (s : TapeStore R B) (b : Fin B) (hh : s.bufferHead b=0) :
    (initializeStore s b).bufferHead=Function.update s.bufferHead b 1 := by
  simp [initializeStore,TapeArrays.painted,TapeMacros.cellStore,hh,Machine.moveHead]

theorem markedFill_stops (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (hk : s.reg l.count=K)
    (hq : s.reg l.random.q=2^(s.reg l.random.ell))
    (he : s.reg l.random.ell ≤ s.reg l.random.q) (hc : RandomTables.Clean l.random s) :
    ∃ t e,t ≤ K*(RandomTables.entryBound (s.reg l.random.q)+2)+3 ∧
      (markedFill l b).Stops inp (s.toCfg (markedFill (B:=B) l b).entry) t e ∧
      e.store=markedFillStore l b inp K s := by
  have hi := TapeMacros.cell_stops b (fun _ => (.bot,.right)) inp s
  obtain ⟨t,ht,hstop⟩ := RandomTables.fill_stops l b inp K (initializeStore s b) hk hq he hc
  have hall := hi.seq hstop
  change t ≤ K*(RandomTables.entryBound (s.reg l.random.q)+2)+1 at ht
  refine ⟨_,_,by omega,hall,rfl⟩

/-- The physical random fill preserves every counter outside its five mutable
registers; the entry count is actually exhausted. -/
theorem markedFillStore_reg_other (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (j : Fin R)
    (ha : j≠l.random.acc) (hc : j≠l.random.count) (ht : j≠l.random.tmp)
    (hs : j≠l.random.scratch) (hk : j≠l.count) :
    (markedFillStore l b inp K s).reg j=s.reg j :=
  RandomTables.fillStore_reg_other l b inp K (initializeStore s b) j ha hc ht hs hk

theorem markedFillStore_bound (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (M : ℕ) (hs : ∀ j,s.reg j ≤ M)
    (hc : RandomTables.Clean l.random s) :
    ∀ j,(markedFillStore l b inp K s).reg j ≤ M := by
  intro j
  unfold markedFillStore
  have hclean := RandomTables.fillStore_clean l b inp K (initializeStore s b) hc
  by_cases ha : j=l.random.acc
  · subst j; rw [hclean.1];omega
  by_cases hc' : j=l.random.count
  · subst j; rw [hclean.2.1];omega
  by_cases ht : j=l.random.tmp
  · subst j; rw [hclean.2.2.1];omega
  by_cases hsc : j=l.random.scratch
  · subst j; rw [hclean.2.2.2];omega
  by_cases hk : j=l.count
  · subst j
    rw [RandomTables.fillStore_count]
    exact (Nat.sub_le _ _).trans (hs _)
  · change (markedFillStore l b inp K s).reg j ≤ M
    rw [markedFillStore_reg_other l b inp K s j ha hc' ht hsc hk]
    exact hs j

theorem markedFillStore_output (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) : (markedFillStore l b inp K s).output=s.output :=
  RandomTables.fillStore_output l b inp K (initializeStore s b)

theorem markedFillStore_roHead (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) :
    (markedFillStore l b inp K s).roHead=
      Function.update s.roHead 3 (s.roHead 3+K*s.reg l.random.ell) :=
  RandomTables.fillStore_roHead l b inp K (initializeStore s b)

theorem markedFillStore_head (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (hq : s.reg l.random.q=2^(s.reg l.random.ell))
    (hh : s.bufferHead b=0) :
    (markedFillStore l b inp K s).bufferHead=
      Function.update s.bufferHead b (1+K*s.reg l.random.q) := by
  rw [markedFillStore,RandomTables.fillStore_head l b inp K (initializeStore s b) hq,
    initializeStore_head s b hh]
  simp only [Function.update_self,Function.update_idem]
  rfl

theorem markedFillStore_table (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (hq : s.reg l.random.q=2^(s.reg l.random.ell))
    (hh : s.bufferHead b=0) :
    TapeArrays.ThermometerTable (markedFillStore l b inp K s) b (s.reg l.random.q)
      (fun i => (RandomTables.sampledValues inp K (s.reg l.random.ell) (s.roHead 3) i).val) := by
  intro i
  have h := RandomTables.fillStore_sampledValues l b inp K (initializeStore s b) hq i
  simpa [markedFillStore,initializeStore,TapeArrays.painted,TapeMacros.cellStore,Machine.moveHead,hh,
    TapeArrays.entryOffset] using h

/-- Multiplication by a compile-time constant, implemented by a real constant
loader followed by the uniform unary multiplication program. -/
def staticScale (r : Fin 5 → Fin R) (c : ℕ) :
    TapeProgram R B ((2+raiseLabels c)+24) :=
  TapeProgram.seq (loadConstant (r 1) c) (multiply (r 0) (r 1) (r 2) (r 3) (r 4))

def staticScaleStore (r : Fin 5 → Fin R) (c : ℕ) (s : TapeStore R B) : TapeStore R B :=
  multiplyStore (s.setReg (r 1) c) (r 0) (r 1) (r 2) (r 3) (r 4)

theorem staticScale_stops (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (c : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M)
    (hc : c ≤ M) (hp : s.reg (r 0)*c ≤ M) :
    ∃ t e,t ≤ 40*(M+1)^2 ∧
      (staticScale r c).Stops inp (s.toCfg (staticScale (B:=B) r c).entry) t e ∧
      e.store=staticScaleStore r c s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨a,ha,has⟩ := loadConstant_stops (r 1) c inp s
  have hab : ∀ j,a.reg j ≤ M := by
    change ∀ j,a.store.reg j ≤ M
    rw [has];exact setReg_bound _ _ _ M hs hc
  obtain ⟨t,e,ht,he,hes⟩ := multiply_stops_polynomial (r 0) (r 1) (r 2) (r 3) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    inp a.store M (hab _) (hab _) (hab _) (hab _) (hab _)
  have hep : e.store=staticScaleStore r c s := by rw [hes,has];rfl
  have heb : ∀ j,e.reg j ≤ M := by
    change ∀ j,e.store.reg j ≤ M
    rw [hep]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M (setReg_bound s _ c M hs hc)
    simpa [SamplerEvaluation.reg_layout r hr] using hp
  have hall := ha.seq he
  refine ⟨_,_,?_,hall,hep,heb⟩
  have := hs (r 1)
  nlinarith

theorem staticScaleStore_value (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (c : ℕ) (s : TapeStore R B) :
    (staticScaleStore r c s).reg (r 2)=s.reg (r 0)*c := by
  simp [staticScaleStore,multiplyStore,SamplerEvaluation.reg_layout r hr]

theorem staticScaleStore_fresh (r : Fin 5 → Fin R) (c : ℕ) (s : TapeStore R B)
    (j : Fin R) (h₁ : j≠r 1) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4) :
    (staticScaleStore r c s).reg j=s.reg j := by
  simp [staticScaleStore,multiplyStore,TapeStore.setReg,h₁,h₂,h₃,h₄]

/-- Runtime q cubed, using two actual unary multiplications. No q-dependent
unrolling or field-arithmetic primitive occurs in this finite program. -/
def cube (r : Fin 80 → Fin R) : TapeProgram R B 48 :=
  TapeProgram.seq (multiply (r 35) (r 35) (r 53) (r 54) (r 55))
    (multiply (r 35) (r 53) (r 56) (r 54) (r 55))

def cubeSquare (r : Fin 80 → Fin R) (s : TapeStore R B) : TapeStore R B :=
  multiplyStore s (r 35) (r 35) (r 53) (r 54) (r 55)
def cubeStore (r : Fin 80 → Fin R) (s : TapeStore R B) : TapeStore R B :=
  multiplyStore (cubeSquare r s) (r 35) (r 53) (r 56) (r 54) (r 55)

theorem cube_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M)
    (hQ : (s.reg (r 35))^2 ≤ M) (hC : (s.reg (r 35))^3 ≤ M) :
    ∃ t e,t ≤ 65*(M+1)^2 ∧
      (cube r).Stops inp (s.toCfg (cube (B:=B) r).entry) t e ∧
      e.store=cubeStore r s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,a,ht₁,ha,has⟩ := multiply_stops_polynomial (r 35) (r 35) (r 53) (r 54) (r 55)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    inp s M (hs _) (hs _) (hs _) (hs _) (hs _)
  have ha' : a.store=cubeSquare r s := has
  have hab : ∀ j,a.reg j ≤ M := by
    change ∀ j,a.store.reg j ≤ M
    rw [has,multiplyStore]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M hs
    simpa [pow_two] using hQ
  obtain ⟨t₂,e,ht₂,he,hes⟩ := multiply_stops_polynomial (r 35) (r 53) (r 56) (r 54) (r 55)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    inp a.store M (hab _) (hab _) (hab _) (hab _) (hab _)
  have hep : e.store=cubeStore r s := by rw [hes,ha'];rfl
  have heb : ∀ j,e.reg j ≤ M := by
    change ∀ j,e.store.reg j ≤ M
    rw [hes,multiplyStore]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M hab
    rw [has]
    simpa [multiplyStore,SamplerEvaluation.reg_layout r hr,pow_succ,pow_two,Nat.mul_assoc] using hC
  exact ⟨_,_,by nlinarith,ha.seq he,hep,heb⟩

theorem cubeStore_value (r : Fin 80 → Fin R) (hr : Function.Injective r) (s : TapeStore R B) :
    (cubeStore r s).reg (r 56)=(s.reg (r 35))^3 := by
  simp [cubeStore,cubeSquare,multiplyStore,SamplerEvaluation.reg_layout r hr,pow_succ,pow_two,Nat.mul_assoc]

theorem cubeStore_fresh (r : Fin 80 → Fin R) (s : TapeStore R B)
    (j : Fin R) (h₁ : j≠r 53) (h₂ : j≠r 54) (h₃ : j≠r 55) (h₄ : j≠r 56) :
    (cubeStore r s).reg j=s.reg j := by
  simp [cubeStore,cubeSquare,multiplyStore,TapeStore.setReg,h₁,h₂,h₃,h₄]

theorem fillStore_bottomMarked (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (hq : s.reg l.random.q=2^(s.reg l.random.ell))
    (hh : 0<s.bufferHead b) (hm : TapeArrays.BottomMarked s b) :
    TapeArrays.BottomMarked (RandomTables.fillStore l b inp K s) b := by
  induction K generalizing s with
  | zero => exact hm
  | succ K ih =>
    let c := TapeProgram.decStore l.count s
    let e := RandomTables.entryStore l.random b inp c
    have hcq : c.reg l.random.q=2^(c.reg l.random.ell) := by
      simpa [c,TapeProgram.decStore,l.fresh 0,l.fresh 1] using hq
    have heq : e.reg l.random.q=2^(e.reg l.random.ell) := by
      rw [RandomTables.entryStore_reg,RandomTables.entryStore_reg]
      simpa [RandomBits.Layout.q,RandomBits.Layout.ell,RandomBits.Layout.acc,
        RandomBits.Layout.count,RandomBits.Layout.tmp,RandomBits.Layout.scratch] using hcq
    have heh : 0<e.bufferHead b := by
      rw [RandomTables.entryStore_head l.random b inp c hcq]
      simp only [Function.update_self]
      change 0<s.bufferHead b+c.reg l.random.q
      omega
    have hem : TapeArrays.BottomMarked e b := by
      constructor
      · rw [RandomTables.entryStore_symbol l.random b inp c hcq]
        have hc0 : ¬c.bufferHead b ≤ 0 := by change ¬s.bufferHead b ≤ 0;omega
        simpa [hc0] using hm.1
      · intro j hj
        rw [RandomTables.entryStore_symbol l.random b inp c hcq]
        split_ifs <;> first | decide | exact hm.2 j hj
    exact ih e heq heh hem

theorem markedFillStore_bottomMarked (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (hq : s.reg l.random.q=2^(s.reg l.random.ell))
    (hh : s.bufferHead b=0) (hb : ∀ j,(s.bufferTape b).getD j .blank=.blank) :
    TapeArrays.BottomMarked (markedFillStore l b inp K s) b := by
  have hm : TapeArrays.BottomMarked (initializeStore s b) b := by
    constructor
    · simp only [initializeStore,TapeArrays.painted,TapeMacros.cellStore,Function.update_self,hh,
        getD_writeAt,if_pos rfl,if_true]
    · intro j hj
      simp only [initializeStore,TapeArrays.painted,TapeMacros.cellStore,Function.update_self,hh,
        getD_writeAt]
      rw [if_neg (by omega : j≠0),hb j]
      decide
  exact fillStore_bottomMarked l b inp K (initializeStore s b) hq
    (by rw [initializeStore_head s b hh];simp) hm

theorem markedFillStore_other_symbol (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (hq : s.reg l.random.q=2^(s.reg l.random.ell))
    (c : Fin B) (hcb : c≠b) (j : ℕ) :
    ((markedFillStore l b inp K s).bufferTape c).getD j .blank=(s.bufferTape c).getD j .blank := by
  rw [markedFillStore,RandomTables.fillStore_outside l b inp K (initializeStore s b) hq c j
    (Or.inl hcb)]
  simp [initializeStore,TapeArrays.painted,TapeMacros.cellStore,hcb]

/-- Actual code computing the number 2*k*q*d of random form coefficients. -/
def formCountLayout (r : Fin 80 → Fin R) : Fin 5 → Fin R := r ∘ ![35,53,52,54,55]
def formCountLabels (d k : ℕ) : ℕ := (2+raiseLabels (2*k*d))+24
def formCount (r : Fin 80 → Fin R) (d k : ℕ) : TapeProgram R B (formCountLabels d k) :=
  staticScale (formCountLayout r) (2*k*d)
def formCountStore (r : Fin 80 → Fin R) (d k : ℕ) (s : TapeStore R B) : TapeStore R B :=
  staticScaleStore (formCountLayout r) (2*k*d) s

theorem formCountLayout_injective (r : Fin 80 → Fin R) (hr : Function.Injective r) :
    Function.Injective (formCountLayout r) := hr.comp (by decide)

theorem formCount_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M)
    (hc : 2*k*d ≤ M) (hp : 2*k*s.reg (r 35)*d ≤ M) :
    ∃ t e,t ≤ 40*(M+1)^2 ∧
      (formCount r d k).Stops inp (s.toCfg (formCount (B:=B) r d k).entry) t e ∧
      e.store=formCountStore r d k s ∧ (∀ j,e.reg j ≤ M) := by
  apply staticScale_stops (formCountLayout r) (formCountLayout_injective r hr) (2*k*d) inp M s hs hc
  change s.reg (r 35)*(2*k*d) ≤ M
  nlinarith [hp]

theorem formCountStore_value (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (s : TapeStore R B) :
    (formCountStore r d k s).reg (r 52)=2*k*s.reg (r 35)*d := by
  have h := staticScaleStore_value (formCountLayout r) (formCountLayout_injective r hr) (2*k*d) s
  change (formCountStore r d k s).reg (r 52)=s.reg (r 35)*(2*k*d) at h
  rw [h]
  ring

/-- Actual code computing k*q^3, with q a runtime unary counter. -/
def hashScaleLayout (r : Fin 80 → Fin R) : Fin 5 → Fin R := r ∘ ![56,57,52,54,55]
def hashCountLabels (k : ℕ) : ℕ := 48+((2+raiseLabels k)+24)
def hashCount (r : Fin 80 → Fin R) (k : ℕ) : TapeProgram R B (hashCountLabels k) :=
  TapeProgram.seq (cube r) (staticScale (hashScaleLayout r) k)
def hashCountStore (r : Fin 80 → Fin R) (k : ℕ) (s : TapeStore R B) : TapeStore R B :=
  staticScaleStore (hashScaleLayout r) k (cubeStore r s)

theorem hashScaleLayout_injective (r : Fin 80 → Fin R) (hr : Function.Injective r) :
    Function.Injective (hashScaleLayout r) := hr.comp (by decide)

theorem hashCount_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M)
    (hk : k ≤ M) (hQ : (s.reg (r 35))^2 ≤ M) (hC : (s.reg (r 35))^3 ≤ M)
    (hp : k*(s.reg (r 35))^3 ≤ M) :
    ∃ t e,t ≤ 106*(M+1)^2 ∧
      (hashCount r k).Stops inp (s.toCfg (hashCount (B:=B) r k).entry) t e ∧
      e.store=hashCountStore r k s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,a,ht₁,ha,has,hab⟩ := cube_stops r hr inp M s hs hQ hC
  have hap : a.reg (r 56)*k ≤ M := by
    change a.store.reg (r 56)*k ≤ M
    rw [has,cubeStore_value r hr]
    simpa [Nat.mul_comm] using hp
  obtain ⟨t₂,e,ht₂,he,hes,heb⟩ := staticScale_stops (hashScaleLayout r)
    (hashScaleLayout_injective r hr) k inp M a.store hab hk hap
  have hall := ha.seq he
  refine ⟨_,_,by nlinarith,hall,?_,heb⟩
  change e.store=_
  rw [hes,has]
  rfl

theorem hashCountStore_value (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (s : TapeStore R B) :
    (hashCountStore r k s).reg (r 52)=k*(s.reg (r 35))^3 := by
  have h := staticScaleStore_value (hashScaleLayout r) (hashScaleLayout_injective r hr) k (cubeStore r s)
  change (hashCountStore r k s).reg (r 52)=(cubeStore r s).reg (r 56)*k at h
  rw [h,cubeStore_value r hr]
  ring

theorem formCountStore_fresh (r : Fin 80 → Fin R) (d k : ℕ) (s : TapeStore R B)
    (j : Fin R) (h₁ : j≠r 53) (h₂ : j≠r 52) (h₃ : j≠r 54) (h₄ : j≠r 55) :
    (formCountStore r d k s).reg j=s.reg j :=
  staticScaleStore_fresh (formCountLayout r) (2*k*d) s j h₁ h₂ h₃ h₄

theorem hashCountStore_fresh (r : Fin 80 → Fin R) (k : ℕ) (s : TapeStore R B)
    (j : Fin R) (h₁ : j≠r 52) (h₂ : j≠r 53) (h₃ : j≠r 54) (h₄ : j≠r 55)
    (h₅ : j≠r 56) (h₆ : j≠r 57) :
    (hashCountStore r k s).reg j=s.reg j := by
  unfold hashCountStore
  rw [staticScaleStore_fresh (hashScaleLayout r) k (cubeStore r s) j h₆ h₁ h₃ h₄]
  exact cubeStore_fresh r s j h₂ h₃ h₄ h₅

theorem prepareRandomStore_payload (r : Fin 80 → Fin R) (ell width : Fin 80)
    (s : TapeStore R B) : ParameterPrograms.SamePayload s (prepareRandomStore r ell width s) :=
  ⟨rfl,rfl,rfl,rfl⟩
theorem formCountStore_payload (r : Fin 80 → Fin R) (d k : ℕ) (s : TapeStore R B) :
    ParameterPrograms.SamePayload s (formCountStore r d k s) := ⟨rfl,rfl,rfl,rfl⟩
theorem hashCountStore_payload (r : Fin 80 → Fin R) (k : ℕ) (s : TapeStore R B) :
    ParameterPrograms.SamePayload s (hashCountStore r k s) := ⟨rfl,rfl,rfl,rfl⟩

theorem entryBound_le (q M : ℕ) (hq : q ≤ M) :
    RandomTables.entryBound q+2 ≤ 80*(M+1)^2 := by
  unfold RandomTables.entryBound
  nlinarith [Nat.mul_self_le_mul_self hq]

theorem markedFill_stops_bound (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (M : ℕ) (hk : s.reg l.count=K)
    (hK : K ≤ M) (hQ : s.reg l.random.q ≤ M)
    (hq : s.reg l.random.q=2^(s.reg l.random.ell))
    (he : s.reg l.random.ell ≤ s.reg l.random.q) (hc : RandomTables.Clean l.random s) :
    ∃ t e,t ≤ 100*(M+1)^3 ∧
      (markedFill l b).Stops inp (s.toCfg (markedFill (B:=B) l b).entry) t e ∧
      e.store=markedFillStore l b inp K s := by
  obtain ⟨t,e,ht,he,hes⟩ := markedFill_stops l b inp K s hk hq he hc
  refine ⟨t,e,ht.trans ?_,he,hes⟩
  have hb := Nat.mul_le_mul hK (entryBound_le _ M hQ)
  nlinarith

/-- Source code for the entire forms-table stage. -/
def formFillLabels (d k : ℕ) : ℕ := (formCountLabels d k+22)+57
def formFill (r : Fin 80 → Fin R) (hr : Function.Injective r) (d k : ℕ) (b : Fin B) :
    TapeProgram R B (formFillLabels d k) :=
  TapeProgram.seq (TapeProgram.seq (formCount r d k) (prepareRandom r 34 35))
    (markedFill (randomLayout r hr) b)

def formPrepareStore (r : Fin 80 → Fin R) (d k : ℕ) (s : TapeStore R B) : TapeStore R B :=
  prepareRandomStore r 34 35 (formCountStore r d k s)
def formFillStore (r : Fin 80 → Fin R) (hr : Function.Injective r) (d k : ℕ)
    (b : Fin B) (inp : Inputs) (s : TapeStore R B) : TapeStore R B :=
  markedFillStore (randomLayout r hr) b inp (2*k*s.reg (r 35)*d) (formPrepareStore r d k s)

theorem formPrepareStore_values (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (s : TapeStore R B) :
    (formPrepareStore r d k s).reg (r 46)=s.reg (r 34) ∧
    (formPrepareStore r d k s).reg (r 47)=s.reg (r 35) ∧
    (formPrepareStore r d k s).reg (r 52)=2*k*s.reg (r 35)*d := by
  have h := prepareRandomStore_values r hr 34 35 (by decide) (formCountStore r d k s)
  refine ⟨?_,?_,?_⟩
  · rw [show (formPrepareStore r d k s).reg (r 46)=(formCountStore r d k s).reg (r 34) from h.1]
    exact formCountStore_fresh r d k s _ (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) (hr.ne (by decide))
  · rw [show (formPrepareStore r d k s).reg (r 47)=(formCountStore r d k s).reg (r 35) from h.2.1]
    exact formCountStore_fresh r d k s _ (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) (hr.ne (by decide))
  · rw [formPrepareStore,prepareRandomStore_fresh r 34 35 _ _
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)),formCountStore_value r hr]

theorem formPrepareStore_clean (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (s : TapeStore R B) (hc : RandomTables.Clean (randomLayout r hr).random s) :
    RandomTables.Clean (randomLayout r hr).random (formPrepareStore r d k s) := by
  change s.reg (r 48)=0 ∧ s.reg (r 49)=0 ∧ s.reg (r 50)=0 ∧ s.reg (r 51)=0 at hc
  change (formPrepareStore r d k s).reg (r 48)=0 ∧
    (formPrepareStore r d k s).reg (r 49)=0 ∧
    (formPrepareStore r d k s).reg (r 50)=0 ∧ (formPrepareStore r d k s).reg (r 51)=0
  rcases hc with ⟨h48,h49,h50,h51⟩
  simp [formPrepareStore,prepareRandomStore,formCountStore,staticScaleStore,formCountLayout,
    multiplyStore,SamplerEvaluation.reg_layout r hr,h48,h49,h50]

theorem formFill_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ j,s.reg j ≤ M) (hc : 2*k*d ≤ M) (hp : 2*k*s.reg (r 35)*d ≤ M)
    (hq : s.reg (r 35)=2^(s.reg (r 34))) (he : s.reg (r 34) ≤ s.reg (r 35))
    (hclean : RandomTables.Clean (randomLayout r hr).random s) :
    ∃ t e,t ≤ 160*(M+1)^3 ∧
      (formFill r hr d k b).Stops inp (s.toCfg (formFill r hr d k b).entry) t e ∧
      e.store=formFillStore r hr d k b inp s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,a,ht₁,ha,has,hab⟩ := formCount_stops r hr d k inp M s hs hc hp
  obtain ⟨t₂,c,ht₂,hc,hcs,hcb⟩ := prepareRandom_stops r hr 34 35 (by decide) (by decide)
    inp M a.store hab
  have hcp : c.store=formPrepareStore r d k s := by rw [hcs,has];rfl
  have hcv := formPrepareStore_values r hr d k s
  have hcc : RandomTables.Clean (randomLayout r hr).random c.store := by
    rw [hcp];exact formPrepareStore_clean r hr d k s hclean
  have hcq : c.reg (randomLayout r hr).random.q=2^(c.reg (randomLayout r hr).random.ell) := by
    change c.store.reg (r 47)=2^(c.store.reg (r 46))
    rw [hcp,hcv.1,hcv.2.1]
    exact hq
  have hce : c.reg (randomLayout r hr).random.ell ≤ c.reg (randomLayout r hr).random.q := by
    change c.store.reg (r 46) ≤ c.store.reg (r 47)
    rw [hcp,hcv.1,hcv.2.1]
    exact he
  have hck : c.reg (randomLayout r hr).count=2*k*s.reg (r 35)*d := by change c.store.reg (r 52)=_;rw [hcp];exact hcv.2.2
  obtain ⟨t₃,e,ht₃,he,hes⟩ := markedFill_stops_bound (randomLayout r hr) b inp
    (2*k*s.reg (r 35)*d) c.store M hck hp (hcb _) hcq hce hcc
  have hall := (ha.seq hc).seq he
  refine ⟨_,_,?_,hall,?_,?_⟩
  · nlinarith
  · change e.store=_
    rw [hes,hcp]
    rfl
  · change ∀ j,e.store.reg j ≤ M
    rw [hes]
    exact markedFillStore_bound _ _ _ _ _ M hcb hcc

/-- Source code for the hash-table stage, whose q-cubed entry count is runtime data. -/
def hashFillLabels (k : ℕ) : ℕ := (hashCountLabels k+22)+57
def hashFill (r : Fin 80 → Fin R) (hr : Function.Injective r) (k : ℕ) (b : Fin B) :
    TapeProgram R B (hashFillLabels k) :=
  TapeProgram.seq (TapeProgram.seq (hashCount r k) (prepareRandom r 38 39))
    (markedFill (randomLayout r hr) b)

def hashPrepareStore (r : Fin 80 → Fin R) (k : ℕ) (s : TapeStore R B) : TapeStore R B :=
  prepareRandomStore r 38 39 (hashCountStore r k s)
def hashFillStore (r : Fin 80 → Fin R) (hr : Function.Injective r) (k : ℕ)
    (b : Fin B) (inp : Inputs) (s : TapeStore R B) : TapeStore R B :=
  markedFillStore (randomLayout r hr) b inp (k*(s.reg (r 35))^3) (hashPrepareStore r k s)

theorem hashPrepareStore_values (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (s : TapeStore R B) :
    (hashPrepareStore r k s).reg (r 46)=s.reg (r 38) ∧
    (hashPrepareStore r k s).reg (r 47)=s.reg (r 39) ∧
    (hashPrepareStore r k s).reg (r 52)=k*(s.reg (r 35))^3 := by
  have h := prepareRandomStore_values r hr 38 39 (by decide) (hashCountStore r k s)
  refine ⟨?_,?_,?_⟩
  · rw [show (hashPrepareStore r k s).reg (r 46)=(hashCountStore r k s).reg (r 38) from h.1]
    exact hashCountStore_fresh r k s _ (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
  · rw [show (hashPrepareStore r k s).reg (r 47)=(hashCountStore r k s).reg (r 39) from h.2.1]
    exact hashCountStore_fresh r k s _ (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
  · rw [hashPrepareStore,prepareRandomStore_fresh r 38 39 _ _
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)),hashCountStore_value r hr]

theorem hashPrepareStore_clean (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (s : TapeStore R B) (hc : RandomTables.Clean (randomLayout r hr).random s) :
    RandomTables.Clean (randomLayout r hr).random (hashPrepareStore r k s) := by
  change s.reg (r 48)=0 ∧ s.reg (r 49)=0 ∧ s.reg (r 50)=0 ∧ s.reg (r 51)=0 at hc
  change (hashPrepareStore r k s).reg (r 48)=0 ∧
    (hashPrepareStore r k s).reg (r 49)=0 ∧
    (hashPrepareStore r k s).reg (r 50)=0 ∧ (hashPrepareStore r k s).reg (r 51)=0
  rcases hc with ⟨h48,h49,h50,h51⟩
  simp [hashPrepareStore,prepareRandomStore,hashCountStore,staticScaleStore,hashScaleLayout,
    cubeStore,cubeSquare,multiplyStore,SamplerEvaluation.reg_layout r hr,h48,h49,h50]

theorem hashFill_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (b : Fin B) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ j,s.reg j ≤ M) (hk : k ≤ M)
    (hQ : (s.reg (r 35))^2 ≤ M) (hC : (s.reg (r 35))^3 ≤ M)
    (hp : k*(s.reg (r 35))^3 ≤ M)
    (hq : s.reg (r 39)=2^(s.reg (r 38))) (he : s.reg (r 38) ≤ s.reg (r 39))
    (hclean : RandomTables.Clean (randomLayout r hr).random s) :
    ∃ t e,t ≤ 230*(M+1)^3 ∧
      (hashFill r hr k b).Stops inp (s.toCfg (hashFill r hr k b).entry) t e ∧
      e.store=hashFillStore r hr k b inp s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,a,ht₁,ha,has,hab⟩ := hashCount_stops r hr k inp M s hs hk hQ hC hp
  obtain ⟨t₂,c,ht₂,hc,hcs,hcb⟩ := prepareRandom_stops r hr 38 39 (by decide) (by decide)
    inp M a.store hab
  have hcp : c.store=hashPrepareStore r k s := by rw [hcs,has];rfl
  have hcv := hashPrepareStore_values r hr k s
  have hcc : RandomTables.Clean (randomLayout r hr).random c.store := by
    rw [hcp];exact hashPrepareStore_clean r hr k s hclean
  have hcq : c.reg (randomLayout r hr).random.q=2^(c.reg (randomLayout r hr).random.ell) := by
    change c.store.reg (r 47)=2^(c.store.reg (r 46))
    rw [hcp,hcv.1,hcv.2.1]
    exact hq
  have hce : c.reg (randomLayout r hr).random.ell ≤ c.reg (randomLayout r hr).random.q := by
    change c.store.reg (r 46) ≤ c.store.reg (r 47)
    rw [hcp,hcv.1,hcv.2.1]
    exact he
  have hck : c.reg (randomLayout r hr).count=k*(s.reg (r 35))^3 := by change c.store.reg (r 52)=_;rw [hcp];exact hcv.2.2
  obtain ⟨t₃,e,ht₃,he,hes⟩ := markedFill_stops_bound (randomLayout r hr) b inp
    (k*(s.reg (r 35))^3) c.store M hck hp (hcb _) hcq hce hcc
  have hall := (ha.seq hc).seq he
  refine ⟨_,_,?_,hall,?_,?_⟩
  · nlinarith
  · change e.store=_
    rw [hes,hcp]
    rfl
  · change ∀ j,e.store.reg j ≤ M
    rw [hes]
    exact markedFillStore_bound _ _ _ _ _ M hcb hcc

theorem formFillStore_low (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B) (j : Fin 80) (hj : j.val<46) :
    (formFillStore r hr d k b inp s).reg (r j)=s.reg (r j) := by
  unfold formFillStore
  rw [markedFillStore_reg_other]
  · rw [formPrepareStore,prepareRandomStore_fresh]
    · exact formCountStore_fresh r d k s _ (hr.ne (by omega)) (hr.ne (by omega))
        (hr.ne (by omega)) (hr.ne (by omega))
    all_goals exact hr.ne (by omega)
  all_goals apply hr.ne;apply Fin.ne_of_val_ne; dsimp [randomLayout,randomRegisters,
    RandomBits.Layout.acc,RandomBits.Layout.count,RandomBits.Layout.tmp,RandomBits.Layout.scratch];omega

theorem hashFillStore_low (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B) (j : Fin 80) (hj : j.val<46) :
    (hashFillStore r hr k b inp s).reg (r j)=s.reg (r j) := by
  unfold hashFillStore
  rw [markedFillStore_reg_other]
  · rw [hashPrepareStore,prepareRandomStore_fresh]
    · exact hashCountStore_fresh r k s _ (hr.ne (by omega)) (hr.ne (by omega))
        (hr.ne (by omega)) (hr.ne (by omega)) (hr.ne (by omega)) (hr.ne (by omega))
    all_goals exact hr.ne (by omega)
  all_goals apply hr.ne;apply Fin.ne_of_val_ne; dsimp [randomLayout,randomRegisters,
    RandomBits.Layout.acc,RandomBits.Layout.count,RandomBits.Layout.tmp,RandomBits.Layout.scratch];omega

theorem formFillStore_clean (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hc : RandomTables.Clean (randomLayout r hr).random s) :
    RandomTables.Clean (randomLayout r hr).random (formFillStore r hr d k b inp s) :=
  RandomTables.fillStore_clean _ _ _ _ _ (formPrepareStore_clean r hr d k s hc)

theorem formFillStore_roHead (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B) :
    (formFillStore r hr d k b inp s).roHead=
      Function.update s.roHead 3 (s.roHead 3+(2*k*s.reg (r 35)*d)*s.reg (r 34)) := by
  unfold formFillStore
  rw [markedFillStore_roHead]
  change Function.update s.roHead 3
    (s.roHead 3+(2*k*s.reg (r 35)*d)*(formPrepareStore r d k s).reg (r 46))=_
  rw [(formPrepareStore_values r hr d k s).1]

theorem hashFillStore_roHead (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B) :
    (hashFillStore r hr k b inp s).roHead=
      Function.update s.roHead 3 (s.roHead 3+(k*(s.reg (r 35))^3)*s.reg (r 38)) := by
  unfold hashFillStore
  rw [markedFillStore_roHead]
  change Function.update s.roHead 3
    (s.roHead 3+(k*(s.reg (r 35))^3)*(hashPrepareStore r k s).reg (r 46))=_
  rw [(hashPrepareStore_values r hr k s).1]

theorem formFillStore_table (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 35)=2^(s.reg (r 34))) (hh : s.bufferHead b=0) :
    TapeArrays.ThermometerTable (formFillStore r hr d k b inp s) b (s.reg (r 35))
      (fun i => (RandomTables.sampledValues inp (2*k*s.reg (r 35)*d) (s.reg (r 34)) (s.roHead 3) i).val) := by
  have hv := formPrepareStore_values r hr d k s
  have hpq : (formPrepareStore r d k s).reg (randomLayout r hr).random.q=
      2^((formPrepareStore r d k s).reg (randomLayout r hr).random.ell) := by
    change (formPrepareStore r d k s).reg (r 47)=2^((formPrepareStore r d k s).reg (r 46))
    rw [hv.1,hv.2.1];exact hq
  have h := markedFillStore_table (randomLayout r hr) b inp (2*k*s.reg (r 35)*d)
    (formPrepareStore r d k s) hpq hh
  change TapeArrays.ThermometerTable (formFillStore r hr d k b inp s) b
    ((formPrepareStore r d k s).reg (r 47))
    (fun i => (RandomTables.sampledValues inp (2*k*s.reg (r 35)*d)
      ((formPrepareStore r d k s).reg (r 46)) (s.roHead 3) i).val) at h
  simpa [RandomTables.sampledValues,hv.1,hv.2.1] using h

theorem hashFillStore_table (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 39)=2^(s.reg (r 38))) (hh : s.bufferHead b=0) :
    TapeArrays.ThermometerTable (hashFillStore r hr k b inp s) b (s.reg (r 39))
      (fun i => (RandomTables.sampledValues inp (k*(s.reg (r 35))^3) (s.reg (r 38)) (s.roHead 3) i).val) := by
  have hv := hashPrepareStore_values r hr k s
  have hpq : (hashPrepareStore r k s).reg (randomLayout r hr).random.q=
      2^((hashPrepareStore r k s).reg (randomLayout r hr).random.ell) := by
    change (hashPrepareStore r k s).reg (r 47)=2^((hashPrepareStore r k s).reg (r 46))
    rw [hv.1,hv.2.1];exact hq
  have h := markedFillStore_table (randomLayout r hr) b inp (k*(s.reg (r 35))^3)
    (hashPrepareStore r k s) hpq hh
  change TapeArrays.ThermometerTable (hashFillStore r hr k b inp s) b
    ((hashPrepareStore r k s).reg (r 47))
    (fun i => (RandomTables.sampledValues inp (k*(s.reg (r 35))^3)
      ((hashPrepareStore r k s).reg (r 46)) (s.roHead 3) i).val) at h
  simpa [RandomTables.sampledValues,hv.1,hv.2.1] using h

theorem markedFillStore_other_head (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (hq : s.reg l.random.q=2^(s.reg l.random.ell))
    (c : Fin B) (hcb : c≠b) : (markedFillStore l b inp K s).bufferHead c=s.bufferHead c := by
  rw [markedFillStore,RandomTables.fillStore_head l b inp K (initializeStore s b) hq]
  simp [initializeStore,TapeArrays.painted,TapeMacros.cellStore,hcb]

theorem formFillStore_head (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 35)=2^(s.reg (r 34))) (hh : s.bufferHead b=0) :
    (formFillStore r hr d k b inp s).bufferHead=
      Function.update s.bufferHead b (1+(2*k*s.reg (r 35)*d)*s.reg (r 35)) := by
  have hv := formPrepareStore_values r hr d k s
  have hpq : (formPrepareStore r d k s).reg (randomLayout r hr).random.q=
      2^((formPrepareStore r d k s).reg (randomLayout r hr).random.ell) := by
    change (formPrepareStore r d k s).reg (r 47)=2^((formPrepareStore r d k s).reg (r 46))
    rw [hv.1,hv.2.1];exact hq
  rw [formFillStore,markedFillStore_head _ _ _ _ _ hpq hh]
  change Function.update s.bufferHead b
    (1+(2*k*s.reg (r 35)*d)*(formPrepareStore r d k s).reg (r 47))=_
  rw [hv.2.1]

theorem hashFillStore_head (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 39)=2^(s.reg (r 38))) (hh : s.bufferHead b=0) :
    (hashFillStore r hr k b inp s).bufferHead=
      Function.update s.bufferHead b (1+(k*(s.reg (r 35))^3)*s.reg (r 39)) := by
  have hv := hashPrepareStore_values r hr k s
  have hpq : (hashPrepareStore r k s).reg (randomLayout r hr).random.q=
      2^((hashPrepareStore r k s).reg (randomLayout r hr).random.ell) := by
    change (hashPrepareStore r k s).reg (r 47)=2^((hashPrepareStore r k s).reg (r 46))
    rw [hv.1,hv.2.1];exact hq
  rw [hashFillStore,markedFillStore_head _ _ _ _ _ hpq hh]
  change Function.update s.bufferHead b
    (1+(k*(s.reg (r 35))^3)*(hashPrepareStore r k s).reg (r 47))=_
  rw [hv.2.1]

def tablesLabels (d k : ℕ) : ℕ := formFillLabels d k+hashFillLabels k
/-- Both physical tables use one continuously advanced RO randomness head. -/
def tables (r : Fin 80 → Fin R) (hr : Function.Injective r) (d k : ℕ) (bf bh : Fin B) :
    TapeProgram R B (tablesLabels d k) :=
  TapeProgram.seq (formFill r hr d k bf) (hashFill r hr k bh)
def tablesStore (r : Fin 80 → Fin R) (hr : Function.Injective r) (d k : ℕ)
    (bf bh : Fin B) (inp : Inputs) (s : TapeStore R B) : TapeStore R B :=
  hashFillStore r hr k bh inp (formFillStore r hr d k bf inp s)

theorem tables_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (bf bh : Fin B) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ j,s.reg j ≤ M) (hc : 2*k*d ≤ M) (hf : 2*k*s.reg (r 35)*d ≤ M)
    (hk : k ≤ M) (hQ : (s.reg (r 35))^2 ≤ M) (hC : (s.reg (r 35))^3 ≤ M)
    (hh : k*(s.reg (r 35))^3 ≤ M)
    (hq : s.reg (r 35)=2^(s.reg (r 34))) (he : s.reg (r 34) ≤ s.reg (r 35))
    (hb : s.reg (r 39)=2^(s.reg (r 38))) (hbe : s.reg (r 38) ≤ s.reg (r 39))
    (hclean : RandomTables.Clean (randomLayout r hr).random s) :
    ∃ t e,t ≤ 391*(M+1)^3 ∧
      (tables r hr d k bf bh).Stops inp (s.toCfg (tables r hr d k bf bh).entry) t e ∧
      e.store=tablesStore r hr d k bf bh inp s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,a,ht₁,ha,has,hab⟩ := formFill_stops r hr d k bf inp M s hs hc hf hq he hclean
  have hav (j : Fin 80) (hj : j.val<46) : a.reg (r j)=s.reg (r j) := by
    change a.store.reg (r j)=_
    rw [has];exact formFillStore_low r hr d k bf inp s j hj
  have hac : RandomTables.Clean (randomLayout r hr).random a.store := by
    rw [has];exact formFillStore_clean r hr d k bf inp s hclean
  obtain ⟨t₂,e,ht₂,he,hes,heb⟩ := hashFill_stops r hr k bh inp M a.store hab hk
    (by simpa only [TapeCfg.store,hav 35 (by decide)] using hQ)
    (by simpa only [TapeCfg.store,hav 35 (by decide)] using hC)
    (by simpa only [TapeCfg.store,hav 35 (by decide)] using hh)
    (by simpa only [TapeCfg.store,hav 39 (by decide),hav 38 (by decide)] using hb)
    (by simpa only [TapeCfg.store,hav 39 (by decide),hav 38 (by decide)] using hbe) hac
  have hpos : 1 ≤ (M+1)^3 := Nat.one_le_pow _ _ (by omega)
  refine ⟨_,_,by omega,ha.seq he,?_,heb⟩
  change e.store=_
  rw [hes,has]
  rfl

/-- The actual field setup is embedded in the low32 registers. -/
def fieldLayout (r : Fin 80 → Fin R) (i : Fin 32) : Fin R := r ⟨i.val,by omega⟩
def scalarLayout (r : Fin 80 → Fin R) (i : Fin 31) : Fin R := r ⟨i.val,by omega⟩

theorem fieldLayout_injective (r : Fin 80 → Fin R) (hr : Function.Injective r) :
    Function.Injective (fieldLayout r) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val (hr h)
  exact hh

def prepareField (r : Fin 80 → Fin R) : TapeProgram R B 22 :=
  TapeProgram.seq (TapeMacros.copy (r 34) (r 20) (r 31))
    (TapeMacros.copy (r 35) (r 23) (r 31))
def prepareFieldStore (r : Fin 80 → Fin R) (s : TapeStore R B) : TapeStore R B :=
  let c := (s.setReg (r 20) (s.reg (r 34))).setReg (r 31) 0
  (c.setReg (r 23) (c.reg (r 35))).setReg (r 31) 0

theorem prepareField_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M) :
    ∃ t e,t ≤ 14*M+15 ∧
      (prepareField r).Stops inp (s.toCfg (prepareField (B:=B) r).entry) t e ∧
      e.store=prepareFieldStore r s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := copy_stops_bound (r 34) (r 20) (r 31)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M s hs
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂,hb₂⟩ := copy_stops_bound (r 35) (r 23) (r 31)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M c₁.store hb₁
  refine ⟨_,_,by omega,h₁.seq h₂,?_,hb₂⟩
  change c₂.store=_
  rw [hs₂,hs₁]
  rfl

def fieldSetup (r : Fin 80 → Fin R) : TapeProgram R B 538 :=
  TapeProgram.seq (prepareField r) (SourceFieldSetup.setup (fieldLayout r))
def fieldSetupStore (r : Fin 80 → Fin R) (s : TapeStore R B) : TapeStore R B :=
  SourceFieldSetup.setupStore (fieldLayout r) (prepareFieldStore r s)

theorem fieldSetup_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (hell : 0<ell) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ j,s.reg j ≤ M) (he : s.reg (r 34)=ell) (hq : s.reg (r 35)=2^ell)
    (hN : 3*ell+1 ≤ M) (h2q : 2*(2^ell) ≤ M) (hQ : 2^(2*ell) ≤ M) :
    ∃ t e,t ≤ 40020*(M+1)^7 ∧
      (fieldSetup r).Stops inp (s.toCfg (fieldSetup (B:=B) r).entry) t e ∧
      e.store=fieldSetupStore r s ∧
      SamplerProgram.Environment (scalarLayout r) ell (ExpandingCodes.PolynomialStretch.BinaryPolynomial.selectedIndex ell hell) e.store ∧
      (∀ j,e.reg j ≤ M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨t₁,c,ht₁,hc,hcs,hcb⟩ := prepareField_stops r hr inp M s hs
  have hce : c.reg (fieldLayout r 20)=ell := by
    change c.store.reg (r 20)=ell
    rw [hcs]
    simpa [prepareFieldStore,SamplerEvaluation.reg_layout r hr] using he
  have hcq : c.reg (fieldLayout r 23)=2^ell := by
    change c.store.reg (r 23)=2^ell
    rw [hcs]
    simpa [prepareFieldStore,SamplerEvaluation.reg_layout r hr] using hq
  obtain ⟨t₂,e,ht₂,he,hes,henv,hef,heb,het⟩ := SourceFieldSetup.setup_stops (fieldLayout r)
    (fieldLayout_injective r hr) inp ell hell M c.store hcb hce hcq hN h2q hQ
  have hep : e.store=fieldSetupStore r s := by rw [hes,hcs];rfl
  refine ⟨_,_,?_,hc.seq he,hep,?_,heb,?_⟩
  · have hp : M+1 ≤ (M+1)^7 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1 ≤ 7 by decide)
    omega
  · exact ⟨henv.2.2.2.1,henv.2.2.1,henv.2.1,henv.2.2.2.2.1⟩
  · rw [het,hcs]
    rfl

theorem fieldSetupStore_fresh (r : Fin 80 → Fin R) (s : TapeStore R B)
    (j : Fin R) (hj : ∀ i : Fin 32,j≠fieldLayout r i) :
    (fieldSetupStore r s).reg j=s.reg j := by
  rw [fieldSetupStore,SourceFieldSetup.setupStore_outside (fieldLayout r) _ j hj]
  have h20 := hj 20
  have h23 := hj 23
  have h31 := hj 31
  simp [prepareFieldStore,TapeStore.setReg,fieldLayout] at h20 h23 h31 ⊢
  simp [h20,h23,h31]

/-- This loop rule uses the proved physical post-counter frame of its body.
It does not assume a runtime evaluator or a unit-cost body transition. -/
theorem countedLoop_stops_frame {L : ℕ} (P : TapeProgram R B L) (r : Fin R)
    (inp : Inputs) (C : ℕ) (Inv : ℕ → TapeStore R B → Prop)
    (hbody : ∀ n s,s.reg r=n+1 → Inv (n+1) s →
      ∃ t c,t ≤ C ∧ P.Stops inp ((TapeProgram.decStore r s).toCfg P.entry) t c ∧
        Inv n c.store ∧ c.reg r=n)
    (n : ℕ) (s : TapeStore R B) (hn : s.reg r=n) (hi : Inv n s) :
    ∃ t e,t ≤ n*(C+2)+1 ∧
      (TapeProgram.countedLoop P r).Stops inp (s.toCfg (TapeProgram.loopHeader L)) t
        (e.toCfg (TapeProgram.loopExit L)) ∧ Inv 0 e ∧ e.reg r=0 := by
  induction n generalizing s with
  | zero => exact ⟨1,s,by omega,TapeProgram.loop_zero P r inp s hn,hi,hn⟩
  | succ n ih =>
    obtain ⟨t,c,ht,hc,hIc,hcr⟩ := hbody n s hn hi
    obtain ⟨u,e,hu,he,hIe,her⟩ := ih c.store hcr hIc
    have hheader := TapeProgram.loop_positive_header P r inp s (by omega)
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2) (TapeProgram.loop_code_body_active P r)
    have hreturn := TapeProgram.loop_body_return P r inp c hc.halted
    refine ⟨1+t+1+u,e,?_,⟨((hheader.trans hrun).trans hreturn).trans he.exec,he.halted⟩,hIe,her⟩
    simp only [Nat.succ_mul]
    omega

/-- The initial source storage is independent of the number of finite labels. -/
def initialStore (R B : ℕ) : TapeStore R B := ⟨fun _ => 0,fun _ => 0,[],fun _ => [],fun _ => 0⟩

def sizeStageStore (r : Fin 80 → Fin R) (d n k : ℕ) : TapeStore R B :=
  setupStore (sizeLayout r) d k (SizeReader.sizeStore (r 32) n (initialStore R B))
def sizeStageTime (d n : ℕ) : ℕ := 2*n+4+setupTimeBound d (n+1)

structure Sizes (r : Fin 80 → Fin R) (d n k : ℕ) (s : TapeStore R B) : Prop where
  input : s.reg (r 32)=n
  power : s.reg (r 33)=n^(2*d)
  ell : s.reg (r 34)=ExpandingCodes.PolynomialStretch.fieldExponent d n
  field : s.reg (r 35)=ExpandingCodes.PolynomialStretch.fieldSize d n
  rows : s.reg (r 36)=ExpandingCodes.PolynomialStretch.rowCount d n
  quotient : s.reg (r 37)=n/k
  beta : s.reg (r 38)=Nat.log 2 (n/k)
  buckets : s.reg (r 39)=2^Nat.log 2 (n/k)

theorem Sizes.frame {r : Fin 80 → Fin R} {d n k : ℕ} {s e : TapeStore R B}
    (h : Sizes r d n k s) (hf : ∀ j : Fin 80,32 ≤ j.val → j.val<40 → e.reg (r j)=s.reg (r j)) :
    Sizes r d n k e := by
  rcases h with ⟨a,b,c,d,e,f,g,h⟩
  constructor
  all_goals first | rw [hf _ (by decide) (by decide)];assumption

 theorem sizeStageStore_sizes (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) (hd : 1 ≤ d) (hk : 0<k) (hn : 2 ≤ n) (hnk : k ≤ n) :
    Sizes r d n k (sizeStageStore (B:=B) r d n k) := by
  have h := setupStore_values (sizeLayout r) (sizeLayout_injective r hr) d k hd hk
    (SizeReader.sizeStore (r 32) n (initialStore R B))
    (by simpa [sizeLayout,SizeReader.sizeStore] using hn)
    (by simpa [sizeLayout,SizeReader.sizeStore] using hnk)
  constructor
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.1
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.2.1
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.2.2.1
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.2.2.2.1
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.2.2.2.2.1
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.2.2.2.2.2.1
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.2.2.2.2.2.2.1
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.2.2.2.2.2.2.2

theorem sizeStage_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) (hk : 0<k) (hn : 2 ≤ n) (hnk : k ≤ n) (inp : Inputs)
    (hi : inp.input=ExpandingCodes.PolynomialStretch.sizeInput n) :
    ∃ t e,t ≤ sizeStageTime d n ∧
      (setupInput (sizeLayout r) d k).Stops inp
        ((initialStore R B).toCfg (setupInput (B:=B) (sizeLayout r) d k).entry) t e ∧
      e.store=sizeStageStore r d n k ∧ (∀ j,e.reg j ≤ setupCounterBound d (n+1)) := by
  have hread := SizeReader.sizeInput_unary (r 32) inp n [] (initialStore R B) rfl hi
  have hb : ∀ j,(SizeReader.sizeStore (r 32) n (initialStore R B)).reg j ≤ n+1 := by
    intro j
    by_cases h:j=r 32
    · subst j;simp [SizeReader.sizeStore,initialStore,TapeStore.setReg]
    · simp [SizeReader.sizeStore,initialStore,TapeStore.setReg,h]
  obtain ⟨t,e,ht,he,hes,heb⟩ := setup_stops (sizeLayout r) (sizeLayout_injective r hr)
    d k hk inp (n+1) (by omega) (SizeReader.sizeStore (r 32) n (initialStore R B)) hb
    (by simp [sizeLayout,SizeReader.sizeStore];omega)
    (by simpa [sizeLayout,SizeReader.sizeStore] using hnk)
  have hall := hread.seq he
  refine ⟨_,_,?_,hall,hes,heb⟩
  change 0+2*n+3+1+t ≤ 2*n+4+setupTimeBound d (n+1)
  omega

theorem sizeStageTime_polynomial (d : ℕ) : PolynomialBound (sizeStageTime d) := by
  have hp : ParameterPrograms.PolynomialMajorant (fun n => 2*n+4+setupTimeBound d (n+1)) :=
    (((ParameterPrograms.PolynomialMajorant.const 2).mul ParameterPrograms.PolynomialMajorant.id).add
      (ParameterPrograms.PolynomialMajorant.const 4)).add
      ((setup_bounds_polynomial d).1.comp
        (ParameterPrograms.PolynomialMajorant.id.add (ParameterPrograms.PolynomialMajorant.const 1)))
  exact hp.toPolynomialBound

theorem sizeStageStore_outside (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) (j : Fin R) (hj : ∀ i,j≠sizeLayout r i) :
    (sizeStageStore (B:=B) r d n k).reg j=0 := by
  rw [sizeStageStore,setupStore_fresh (sizeLayout r) (sizeLayout_injective r hr) d k _ j hj]
  have h32 : j≠r 32 := hj 0
  simp [SizeReader.sizeStore,TapeStore.setReg,h32,initialStore]

theorem sizeStageStore_clean (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) : RandomTables.Clean (randomLayout r hr).random (sizeStageStore (B:=B) r d n k) := by
  constructor
  · apply sizeStageStore_outside r hr
    intro i heq
    have hh := congrArg Fin.val (hr heq)
    have := i.isLt
    change (48 : ℕ)=32+i.val at hh
    omega
  constructor
  · apply sizeStageStore_outside r hr
    intro i heq
    have hh := congrArg Fin.val (hr heq)
    have := i.isLt
    change (49 : ℕ)=32+i.val at hh
    omega
  constructor
  · apply sizeStageStore_outside r hr
    intro i heq
    have hh := congrArg Fin.val (hr heq)
    have := i.isLt
    change (50 : ℕ)=32+i.val at hh
    omega
  · apply sizeStageStore_outside r hr
    intro i heq
    have hh := congrArg Fin.val (hr heq)
    have := i.isLt
    change (51 : ℕ)=32+i.val at hh
    omega

theorem sizeStageStore_tapeData (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) : FieldConvolution.tapeData (sizeStageStore (B:=B) r d n k)=
      FieldConvolution.tapeData (SizeReader.sizeStore (r 32) n (initialStore R B)) := by
  have h := setupStore_payload (sizeLayout r) (sizeLayout_injective r hr) d k
    (SizeReader.sizeStore (r 32) n (initialStore R B))
  exact congrArg₂ Prod.mk h.1 (congrArg₂ Prod.mk h.2.1 (congrArg₂ Prod.mk h.2.2.1 h.2.2.2))

theorem formPrepareStore_q (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (s : TapeStore R B) (hq : s.reg (r 35)=2^(s.reg (r 34))) :
    (formPrepareStore r d k s).reg (randomLayout r hr).random.q=
      2^((formPrepareStore r d k s).reg (randomLayout r hr).random.ell) := by
  change (formPrepareStore r d k s).reg (r 47)=2^((formPrepareStore r d k s).reg (r 46))
  rw [(formPrepareStore_values r hr d k s).1,(formPrepareStore_values r hr d k s).2.1]
  exact hq

theorem hashPrepareStore_q (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (s : TapeStore R B) (hq : s.reg (r 39)=2^(s.reg (r 38))) :
    (hashPrepareStore r k s).reg (randomLayout r hr).random.q=
      2^((hashPrepareStore r k s).reg (randomLayout r hr).random.ell) := by
  change (hashPrepareStore r k s).reg (r 47)=2^((hashPrepareStore r k s).reg (r 46))
  rw [(hashPrepareStore_values r hr k s).1,(hashPrepareStore_values r hr k s).2.1]
  exact hq

theorem formFillStore_other_symbol (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 35)=2^(s.reg (r 34))) (c : Fin B) (hcb : c≠b) (j : ℕ) :
    ((formFillStore r hr d k b inp s).bufferTape c).getD j .blank=(s.bufferTape c).getD j .blank :=
  markedFillStore_other_symbol _ b inp _ (formPrepareStore r d k s)
    (formPrepareStore_q r hr d k s hq) c hcb j

theorem hashFillStore_other_symbol (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 39)=2^(s.reg (r 38))) (c : Fin B) (hcb : c≠b) (j : ℕ) :
    ((hashFillStore r hr k b inp s).bufferTape c).getD j .blank=(s.bufferTape c).getD j .blank :=
  markedFillStore_other_symbol _ b inp _ (hashPrepareStore r k s)
    (hashPrepareStore_q r hr k s hq) c hcb j

theorem formFillStore_bottomMarked (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 35)=2^(s.reg (r 34))) (hh : s.bufferHead b=0)
    (hb : ∀ j,(s.bufferTape b).getD j .blank=.blank) :
    TapeArrays.BottomMarked (formFillStore r hr d k b inp s) b :=
  markedFillStore_bottomMarked _ b inp _ (formPrepareStore r d k s)
    (formPrepareStore_q r hr d k s hq) hh hb

theorem hashFillStore_bottomMarked (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 39)=2^(s.reg (r 38))) (hh : s.bufferHead b=0)
    (hb : ∀ j,(s.bufferTape b).getD j .blank=.blank) :
    TapeArrays.BottomMarked (hashFillStore r hr k b inp s) b :=
  markedFillStore_bottomMarked _ b inp _ (hashPrepareStore r k s)
    (hashPrepareStore_q r hr k s hq) hh hb

theorem formFillStore_output (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B) :
    (formFillStore r hr d k b inp s).output=s.output :=
  markedFillStore_output _ _ _ _ _

theorem hashFillStore_output (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B) :
    (hashFillStore r hr k b inp s).output=s.output :=
  markedFillStore_output _ _ _ _ _

theorem tablesStore_output (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (bf bh : Fin B) (inp : Inputs) (s : TapeStore R B) :
    (tablesStore r hr d k bf bh inp s).output=s.output := by
  rw [tablesStore,hashFillStore_output,formFillStore_output]

theorem tablesStore_sizes (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) (bf bh : Fin B) (inp : Inputs) (s : TapeStore R B) (hs : Sizes r d n k s) :
    Sizes r d n k (tablesStore r hr d k bf bh inp s) := by
  apply hs.frame
  intro j hj hj'
  rw [tablesStore,hashFillStore_low r hr k bh inp _ j (by omega),
    formFillStore_low r hr d k bf inp s j (by omega)]

/-- Numeric table readiness used by the actual layer program. These are explicit
physical cell predicates for the exact blocks read from the finite random tape. -/
structure TablesReady (d n k : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R 2) : Prop where
  forms : TapeArrays.ThermometerTable s 0 (ExpandingCodes.PolynomialStretch.fieldSize d n)
    (fun i => (RandomTables.sampledValues inp
      (2*k*ExpandingCodes.PolynomialStretch.fieldSize d n*d)
      (ExpandingCodes.PolynomialStretch.fieldExponent d n) 0 i).val)
  hashes : TapeArrays.ThermometerTable s 1 (2^Nat.log 2 (n/k))
    (fun i => (RandomTables.sampledValues inp
      (k*ExpandingCodes.PolynomialStretch.fieldSize d n*ExpandingCodes.PolynomialStretch.fieldSize d n*
        ExpandingCodes.PolynomialStretch.fieldSize d n) (Nat.log 2 (n/k))
      ((2*k*ExpandingCodes.PolynomialStretch.fieldSize d n*d)*
        ExpandingCodes.PolynomialStretch.fieldExponent d n) i).val)
  marked : ∀ b,TapeArrays.BottomMarked s b
  heads : ∀ b,s.bufferHead b ≤ M

theorem TablesReady.frame {d n k M : ℕ} {inp : Inputs} {s e : TapeStore R 2}
    (h : TablesReady d n k inp M s)
    (hsym : ∀ b j,(e.bufferTape b).getD j .blank=(s.bufferTape b).getD j .blank)
    (hh : ∀ b,e.bufferHead b ≤ M) : TablesReady d n k inp M e := by
  constructor
  · intro i
    exact ⟨(h.forms i).1,fun j hj => by rw [hsym];exact (h.forms i).2 j hj⟩
  · intro i
    exact ⟨(h.hashes i).1,fun j hj => by rw [hsym];exact (h.hashes i).2 j hj⟩
  · intro b
    exact ⟨by rw [hsym];exact (h.marked b).1,fun j hj => by rw [hsym];exact (h.marked b).2 j hj⟩
  · exact hh

theorem tablesStore_ready (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R 2) (hs : Sizes r d n k s)
    (hro : s.roHead 3=0) (hhead : ∀ b,s.bufferHead b=0)
    (hblank : ∀ b j,(s.bufferTape b).getD j .blank=.blank)
    (hfM : 1+2*k*ExpandingCodes.PolynomialStretch.fieldSize d n*d*
      ExpandingCodes.PolynomialStretch.fieldSize d n ≤ M)
    (hhM : 1+k*(ExpandingCodes.PolynomialStretch.fieldSize d n)^3*2^Nat.log 2 (n/k) ≤ M) :
    TablesReady d n k inp M (tablesStore r hr d k 0 1 inp s) := by
  let a := formFillStore r hr d k (0 : Fin 2) inp s
  have hq : s.reg (r 35)=2^(s.reg (r 34)) := by rw [hs.field,hs.ell];rfl
  have hav (j : Fin 80) (hj : j.val<46) : a.reg (r j)=s.reg (r j) :=
    formFillStore_low r hr d k 0 inp s j hj
  have haβ : a.reg (r 39)=2^(a.reg (r 38)) := by
    rw [hav 39 (by decide),hav 38 (by decide),hs.buckets,hs.beta]
  have hah : a.bufferHead 1=0 := by
    have ht := formFillStore_head r hr d k (0 : Fin 2) inp s hq (hhead 0)
    change a.bufferHead=Function.update s.bufferHead 0 (1+(2*k*s.reg (r 35)*d)*s.reg (r 35)) at ht
    rw [ht]
    simpa using hhead 1
  have hab : ∀ j,(a.bufferTape 1).getD j .blank=.blank := by
    intro j
    rw [formFillStore_other_symbol r hr d k 0 inp s hq 1 (by decide)]
    exact hblank 1 j
  have hf : TapeArrays.ThermometerTable a 0 (ExpandingCodes.PolynomialStretch.fieldSize d n)
      (fun i => (RandomTables.sampledValues inp (2*k*ExpandingCodes.PolynomialStretch.fieldSize d n*d)
        (ExpandingCodes.PolynomialStretch.fieldExponent d n) 0 i).val) := by
    have ht := formFillStore_table r hr d k 0 inp s hq (hhead 0)
    rw [hs.field,hs.ell,hro] at ht
    simpa [RandomTables.sampledValues] using ht
  have hhash : TapeArrays.ThermometerTable (hashFillStore r hr k 1 inp a) 1 (2^Nat.log 2 (n/k))
      (fun i => (RandomTables.sampledValues inp
        (k*ExpandingCodes.PolynomialStretch.fieldSize d n*ExpandingCodes.PolynomialStretch.fieldSize d n*
          ExpandingCodes.PolynomialStretch.fieldSize d n) (Nat.log 2 (n/k))
        ((2*k*ExpandingCodes.PolynomialStretch.fieldSize d n*d)*ExpandingCodes.PolynomialStretch.fieldExponent d n) i).val) := by
    have ht := hashFillStore_table r hr k 1 inp a haβ hah
    have har : a.roHead 3=(2*k*ExpandingCodes.PolynomialStretch.fieldSize d n*d)*
        ExpandingCodes.PolynomialStretch.fieldExponent d n := by
      rw [formFillStore_roHead]
      simp [hro,hs.field,hs.ell]
    rw [hav 35 (by decide),hav 38 (by decide),hav 39 (by decide),hs.field,hs.beta,hs.buckets,har] at ht
    rw [show k*(fieldSize d n)^3=k*fieldSize d n*fieldSize d n*fieldSize d n by ring] at ht
    simpa [RandomTables.sampledValues,Nat.mul_assoc] using ht
  have hfm : TapeArrays.BottomMarked a 0 :=
    formFillStore_bottomMarked r hr d k 0 inp s hq (hhead 0) (hblank 0)
  have hhm : TapeArrays.BottomMarked (hashFillStore r hr k 1 inp a) 1 :=
    hashFillStore_bottomMarked r hr k 1 inp a haβ hah hab
  constructor
  · intro i
    refine ⟨(hf i).1,?_⟩
    intro j hj
    change ((hashFillStore r hr k 1 inp a).bufferTape 0).getD _ .blank=_
    rw [hashFillStore_other_symbol r hr k 1 inp a haβ 0 (by decide)]
    exact (hf i).2 j hj
  · exact hhash
  · intro b
    fin_cases b
    · constructor
      · change ((hashFillStore r hr k 1 inp a).bufferTape 0).getD 0 .blank=.bot
        rw [hashFillStore_other_symbol r hr k 1 inp a haβ 0 (by decide)]
        exact hfm.1
      · intro j hj
        change ((hashFillStore r hr k 1 inp a).bufferTape 0).getD j .blank≠.bot
        rw [hashFillStore_other_symbol r hr k 1 inp a haβ 0 (by decide)]
        exact hfm.2 j hj
    · exact hhm
  · intro b
    change (hashFillStore r hr k 1 inp a).bufferHead b ≤ M
    rw [hashFillStore_head r hr k 1 inp a haβ hah]
    fin_cases b
    · simp only [Function.update_of_ne (by decide : (0 : Fin 2)≠1)]
      change (formFillStore r hr d k 0 inp s).bufferHead 0 ≤ M
      rw [formFillStore_head r hr d k 0 inp s hq (hhead 0)]
      simp only [Function.update_self]
      simpa [hs.field,Nat.mul_assoc] using hfM
    · simp only [Function.update_self]
      simpa [hav 35 (by decide),hav 39 (by decide),hs.field,hs.buckets] using hhM

open ExpandingCodes.PolynomialStretch

structure RuntimeReady (r : Fin 80 → Fin R) (d n k : ℕ) (inp : Inputs) (M : ℕ)
    (s : TapeStore R 2) : Prop where
  sizes : Sizes r d n k s
  environment : SamplerProgram.Environment (scalarLayout r) (fieldExponent d n)
    (BinaryPolynomial.selectedIndex (fieldExponent d n) (fieldExponent_pos d n)) s
  tables : TablesReady d n k inp M s
  counters : ∀ j,s.reg j ≤ M

def preludeLabels (d k : ℕ) : ℕ := ((5+setupLabels d k)+tablesLabels d k)+538
/-- The complete actual frontend, fixed before any runtime size is read. -/
def prelude (r : Fin 80 → Fin R) (hr : Function.Injective r) (d k : ℕ) :
    TapeProgram R 2 (preludeLabels d k) :=
  TapeProgram.seq (TapeProgram.seq (setupInput (sizeLayout r) d k) (tables r hr d k 0 1)) (fieldSetup r)
def preludeStore (r : Fin 80 → Fin R) (hr : Function.Injective r) (d n k : ℕ) (inp : Inputs) : TapeStore R 2 :=
  fieldSetupStore r (tablesStore r hr d k 0 1 inp (sizeStageStore r d n k))
def preludeTime (d n M : ℕ) : ℕ := sizeStageTime d n+391*(M+1)^3+40020*(M+1)^7+2

theorem prelude_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) (hd : 1 ≤ d) (hk : 0<k) (hn : 2 ≤ n) (hnk : k ≤ n)
    (inp : Inputs) (hi : inp.input=sizeInput n) (M : ℕ) (hM : SamplerEnvelopeCovers d k n M) :
    ∃ t e,t ≤ preludeTime d n M ∧
      (prelude r hr d k).Stops inp ((initialStore R 2).toCfg (prelude r hr d k).entry) t e ∧
      e.store=preludeStore r hr d n k inp ∧ RuntimeReady r d n k inp M e.store ∧ e.output=[] := by
  obtain ⟨t₁,a,ht₁,ha,has,hab⟩ := sizeStage_stops (B:=2) r hr d n k hk hn hnk inp hi
  have haSizes : Sizes r d n k a.store := by rw [has];exact sizeStageStore_sizes r hr d n k hd hk hn hnk
  have haBounds : ∀ j,a.reg j ≤ M := fun j => (hab j).trans hM.setup
  have haField : a.reg (r 35)=fieldSize d n := haSizes.field
  have haEll : a.reg (r 34)=fieldExponent d n := haSizes.ell
  have haBeta : a.reg (r 38)=Nat.log 2 (n/k) := haSizes.beta
  have haBucket : a.reg (r 39)=2^Nat.log 2 (n/k) := haSizes.buckets
  have haClean : RandomTables.Clean (randomLayout r hr).random a.store := by
    rw [has];exact sizeStageStore_clean r hr d n k
  have haq : a.reg (r 35)=2^(a.reg (r 34)) := by rw [haField,haEll];rfl
  have hae : a.reg (r 34) ≤ a.reg (r 35) := by
    change a.store.reg _ ≤ a.store.reg _
    rw [haSizes.field,haSizes.ell]
    exact (Nat.lt_two_pow_self : fieldExponent d n<2^(fieldExponent d n)).le
  have haβ : a.reg (r 39)=2^(a.reg (r 38)) := by
    rw [haBucket,haBeta]
  have habe : a.reg (r 38) ≤ a.reg (r 39) := by
    change a.store.reg _ ≤ a.store.reg _
    rw [haSizes.buckets,haSizes.beta]
    exact (Nat.lt_two_pow_self : Nat.log 2 (n/k)<2^Nat.log 2 (n/k)).le
  have hq1 : 1 ≤ fieldSize d n := Nat.one_le_pow _ _ (by decide)
  have hb1 : 1 ≤ samplerBucketCount k n := Nat.one_le_pow _ _ (by decide)
  have hkc : k ≤ M := by have := hM.constants;omega
  have hc : 2*k*d ≤ M := by have := hM.constants;omega
  have hf : 2*k*fieldSize d n*d ≤ M := by
    have hp := Nat.mul_le_mul_left (2*k*fieldSize d n*d) hq1
    have hc := hM.forms
    nlinarith
  have hh : k*(fieldSize d n)^3 ≤ M := by
    have hp := Nat.mul_le_mul_left (k*(fieldSize d n)^3) hb1
    have hc := hM.hashes
    unfold samplerBucketCount at hp hc
    nlinarith
  have hC : (fieldSize d n)^3 ≤ M := by
    have hp := Nat.mul_le_mul_right ((fieldSize d n)^3) (show 1 ≤ k by omega)
    simpa only [one_mul] using hp.trans hh
  obtain ⟨t₂,c,ht₂,hc,hcs,hcb⟩ := tables_stops r hr d k 0 1 inp M a.store haBounds hc
    (by simpa only [haField] using hf) hkc
    (by simpa only [haField] using hM.square)
    (by simpa only [haField] using hC)
    (by simpa only [haField] using hh) haq hae haβ habe haClean
  have hcSizes : Sizes r d n k c.store := by rw [hcs];exact tablesStore_sizes r hr d n k 0 1 inp a.store haSizes
  have haTape := sizeStageStore_tapeData (B:=2) r hr d n k
  have har : a.roHead 3=0 := by
    change a.store.roHead 3=0
    rw [has]
    exact congrArg (fun z => z.1 3) haTape
  have hah : ∀ b,a.bufferHead b=0 := by
    intro b
    change a.store.bufferHead b=0
    rw [has]
    exact congrArg (fun z => z.2.2.2 b) haTape
  have hab : ∀ b j,(a.bufferTape b).getD j .blank=.blank := by
    intro b j
    have h := congrArg (fun z => (z.2.2.1 b).getD j .blank) haTape
    change (a.store.bufferTape b).getD j .blank=.blank
    rw [has]
    exact h
  have hcTables : TablesReady d n k inp M c.store := by
    rw [hcs]
    apply tablesStore_ready r hr d n k inp M a.store haSizes har hah hab
    · simpa only [Nat.add_comm,Nat.mul_assoc] using hM.forms
    · simpa only [samplerBucketCount,Nat.add_comm] using hM.hashes
  have hQ : 2^(2*fieldExponent d n) ≤ M := by
    rw [show 2*fieldExponent d n=fieldExponent d n*2 by omega,pow_mul]
    exact hM.square
  obtain ⟨t₃,e,ht₃,he,hes,henv,heb,het⟩ := fieldSetup_stops r hr inp (fieldExponent d n)
    (fieldExponent_pos d n) M c.store hcb hcSizes.ell hcSizes.field hM.coefficients hM.twiceField hQ
  have hep : e.store=preludeStore r hr d n k inp := by rw [hes,hcs,has];rfl
  have heSizes : Sizes r d n k e.store := by
    apply hcSizes.frame
    intro j hj hj'
    rw [hes]
    apply fieldSetupStore_fresh
    intro i heq
    have h := congrArg Fin.val (hr heq)
    change j.val=i.val at h
    have := i.isLt
    omega
  have heTables : TablesReady d n k inp M e.store := by
    apply hcTables.frame
    · intro b j
      exact congrArg (fun z => (z.2.2.1 b).getD j .blank) het
    · intro b
      have hh := congrArg (fun z => z.2.2.2 b) het
      exact hh.le.trans (hcTables.heads b)
  have heOut : e.output=[] := by
    have heo := congrArg (fun z => z.2.1) het
    change e.store.output=c.store.output at heo
    change e.store.output=[]
    rw [heo,hcs,tablesStore_output,has]
    exact congrArg (fun z => z.2.1) haTape
  refine ⟨_,_,?_,(ha.seq hc).seq he,hep,⟨heSizes,henv,heTables,heb⟩,heOut⟩
  unfold preludeTime
  omega

theorem preludeTime_polynomial (d k : ℕ) (hd : 0<d) :
    PolynomialBound (fun n => preludeTime d n (samplerEnvelope d k n)) := by
  have hM := (samplerEnvelope_polynomial d k hd).add (PolynomialBound.const 1)
  exact (((sizeStageTime_polynomial d).add ((PolynomialBound.const 391).mul (hM.pow 3))).add
    ((PolynomialBound.const 40020).mul (hM.pow 7))).add (PolynomialBound.const 2)

/-- Stable scalar values needed by every row computation. -/
def Protected (j : Fin 80) : Prop :=
  j=3 ∨ j=19 ∨ j=23 ∨ j=24 ∨ (32 ≤ j.val ∧ j.val<40)

theorem RuntimeReady.frame {r : Fin 80 → Fin R} {d n k M : ℕ} {inp : Inputs}
    {s e : TapeStore R 2} (h : RuntimeReady r d n k inp M s)
    (hr : ∀ j,Protected j → e.reg (r j)=s.reg (r j))
    (ht : ∀ b j,(e.bufferTape b).getD j .blank=(s.bufferTape b).getD j .blank)
    (hh : ∀ b,e.bufferHead b ≤ M) (hb : ∀ j,e.reg j ≤ M) : RuntimeReady r d n k inp M e := by
  constructor
  · apply h.sizes.frame
    intro j hj hj'
    exact hr j (Or.inr (Or.inr (Or.inr (Or.inr ⟨hj,hj'⟩))))
  · apply h.environment.frame
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact hr 3 (Or.inl rfl)
    · exact hr 19 (Or.inr (Or.inl rfl))
    · exact hr 23 (Or.inr (Or.inr (Or.inl rfl)))
    · exact hr 24 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact h.tables.frame ht hh
  · exact hb

theorem RuntimeReady.setReg {r : Fin 80 → Fin R} {d n k M : ℕ} {inp : Inputs}
    {s : TapeStore R 2} (h : RuntimeReady r d n k inp M s) (j : Fin R) (a : ℕ)
    (ha : a ≤ M) (hj : ∀ i,Protected i → r i≠j) : RuntimeReady r d n k inp M (s.setReg j a) := by
  apply h.frame
  · intro i hi;simp [TapeStore.setReg,hj i hi]
  · intro b n;rfl
  · exact h.tables.heads
  · exact setReg_bound s j a M h.counters ha

namespace Concrete
open SamplerProgram

def writerIndex : Fin 8 → Fin 80 := ![32,62,63,64,65,66,67,68]

def writerRegisters (d k : ℕ) : Fin 8 ⊕ Fin k → Fin (Storage.registers d k)
  | .inl i => Storage.low d k (writerIndex i)
  | .inr i => Storage.neighbor d k i

theorem writerRegisters_injective (d k : ℕ) : Function.Injective (writerRegisters d k) := by
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      apply congrArg Sum.inl
      apply (show Function.Injective writerIndex by decide)
      exact Storage.low_injective d k hab
    | inr j =>
      have h := congrArg Fin.val hab
      have hj := j.isLt
      fin_cases i <;> simp [writerRegisters,writerIndex,Storage.low_val,Storage.neighbor_val] at h <;> omega
  | inr i =>
    cases b with
    | inl j =>
      have h := congrArg Fin.val hab
      have hi := i.isLt
      fin_cases j <;> simp [writerRegisters,writerIndex,Storage.low_val,Storage.neighbor_val] at h <;> omega
    | inr j =>
      apply congrArg Sum.inr
      apply Fin.ext
      have h := congrArg Fin.val hab
      simp only [writerRegisters,Storage.neighbor_val] at h
      omega

def writerLayout (d k : ℕ) : NeighborWriter.Layout (Storage.registers d k) k :=
  ⟨writerRegisters d k,writerRegisters_injective d k⟩

def layersLabels (d k : ℕ) : List (Fin k) → ℕ
  | [] => 1
  | i::is => layerLabels d k i+layersLabels d k is

def layers (d k : ℕ) : (is : List (Fin k)) → TapeProgram (Storage.registers d k) 2 (layersLabels d k is)
  | [] => TapeProgram.skip
  | i::is => TapeProgram.seq (layer d k i) (layers d k is)

def rowBodyLabels (d k : ℕ) : ℕ :=
  (layersLabels d k (List.finRange k)+(15+(NeighborWriter.bodyLabels k+2)))+
    SamplerOdometer.labels (Storage.pointPairs d k)

/-- One complete actual row: all k layer evaluations, physical n-bit row writer,
and physical little-endian carry. None of n,q,ell,m,b enters this code table. -/
def rowBody (d k : ℕ) : TapeProgram (Storage.registers d k) 2 (rowBodyLabels d k) :=
  TapeProgram.seq (TapeProgram.seq (layers d k (List.finRange k)) (NeighborWriter.writeRow (writerLayout d k)))
    (SamplerOdometer.program (Storage.low d k 35) (Storage.low d k 61) (Storage.pointPairs d k))

def finishLabels (d k : ℕ) : ℕ :=
  (SamplerOdometer.initializeLabels (Storage.pointPairs d k)+11)+(rowBodyLabels d k+2)

def finish (d k : ℕ) : TapeProgram (Storage.registers d k) 2 (finishLabels d k) :=
  TapeProgram.seq (TapeProgram.seq
    (SamplerOdometer.initDigits (Storage.low d k 35) (Storage.low d k 61) (Storage.pointPairs d k))
    (TapeMacros.copy (Storage.low d k 36) (Storage.low d k 60) (Storage.low d k 61)))
    (TapeProgram.countedLoop (rowBody d k) (Storage.low d k 60))

def samplerLabels (d k : ℕ) : ℕ := preludeLabels d k+finishLabels d k

/-- Fully concrete finite sampler source, including its unary frontend, physical
random tables, field construction, runtime row loop, and physical output writes. -/
def sampler (d k : ℕ) : TapeProgram (Storage.registers d k) 2 (samplerLabels d k) :=
  TapeProgram.seq (prelude (Storage.low d k) (Storage.low_injective d k) d k) (finish d k)

/-- A finite sequential composition rule for the actual layer code. The
single-layer premise is strictly smaller than the k-layer program; the result
tracks all produced neighbor counters and the untouched remaining counters. -/
theorem layers_stops_of (d k : ℕ) (inp : Inputs) (C : ℕ)
    (Good : TapeStore (Storage.registers d k) 2 → Prop) (value : Fin k → ℕ)
    (hstep : ∀ i s,Good s → ∃ t e,t ≤ C ∧
      (layer d k i).Stops inp (s.toCfg (layer d k i).entry) t e ∧ Good e.store ∧
      e.reg (Storage.neighbor d k i)=value i ∧
      (∀ j,j≠i → e.reg (Storage.neighbor d k j)=s.reg (Storage.neighbor d k j)))
    (is : List (Fin k)) (s : TapeStore (Storage.registers d k) 2) (hs : Good s) :
    ∃ t e,t ≤ is.length*(C+1) ∧
      (layers d k is).Stops inp (s.toCfg (layers d k is).entry) t e ∧ Good e.store ∧
      (∀ i,i∈is → e.reg (Storage.neighbor d k i)=value i) ∧
      (∀ i,i∉is → e.reg (Storage.neighbor d k i)=s.reg (Storage.neighbor d k i)) := by
  induction is generalizing s with
  | nil =>
    exact ⟨0,s.toCfg ⟨0,by simp [layersLabels]⟩,by simp,TapeProgram.skip_stops inp s,hs,by simp,by simp⟩
  | cons i is ih =>
    obtain ⟨t,c,ht,hc,hGc,hnew,hframe⟩ := hstep i s hs
    obtain ⟨u,e,hu,he,hGe,hvalues,htail⟩ := ih c.store hGc
    refine ⟨_,_,?_,hc.seq he,hGe,?_,?_⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · intro j hj
      rcases List.mem_cons.mp hj with hji|hj
      · subst j
        by_cases hi : i∈is
        · exact hvalues i hi
        · rw [htail i hi]
          exact hnew
      · exact hvalues j hj
    · intro j hj
      have hji : j≠i := by intro heq;subst j;exact hj (by simp)
      have hjtail : j∉is := by intro hin;exact hj (by simp [hin])
      rw [htail j hjtail]
      exact hframe j hji

theorem writeRow_matches {d k n q b : ℕ}
    (O : EncodedGaussian.Operations (Fin q)) (forms : Fin (2*k*q*d) → Fin q)
    (hashes : Fin (k*q*q*q) → Fin b) (z : Fin (q^d))
    (s : TapeStore (Storage.registers d k) 2) (hn : s.reg (Storage.low d k 32)=n)
    (hv : ∀ i,s.reg (Storage.neighbor d k i)=i.val*b+
      (EncodedSampler.neighbor O forms hashes i (EncodedTester.digits q d z)).val) :
    (NeighborWriter.writeRowStore (writerLayout d k) s).output=
      s.output++SamplerRows.row (n:=n) O forms hashes z := by
  have h := NeighborWriter.writeRow_output (writerLayout d k) s
  change (NeighborWriter.writeRowStore (writerLayout d k) s).output=s.output++
    List.ofFn (fun j : Fin (s.reg (Storage.low d k 32)) =>
      decide (∃ i,j.val=s.reg (Storage.neighbor d k i))) at h
  rw [hn] at h
  simpa only [hv,SamplerRows.row] using h

theorem low_not_used (d k : ℕ) (j : Fin 80) :
    Storage.low d k j∉SamplerOdometer.used (Storage.pointPairs d k) := by
  intro hj
  obtain ⟨p,hp,hj⟩ := (SamplerOdometer.used_mem_iff _ _).mp hj
  obtain ⟨i,hi,hpi⟩ := List.mem_map.mp hp
  subst p
  rcases hj with hj|hj
  · have h := congrArg Fin.val hj
    have := j.isLt
    simp only [Storage.low_val,Storage.point_val] at h
    omega
  · have h := congrArg Fin.val hj
    have := j.isLt
    simp only [Storage.low_val,Storage.countdown_val] at h
    omega

theorem initializeStore_payload (q tmp : Fin R) (ps : List (SamplerOdometer.Digit R))
    (s : TapeStore R B) : FieldConvolution.tapeData (SamplerOdometer.initializeStore q tmp ps s)=
      FieldConvolution.tapeData s := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    rw [SamplerOdometer.initializeStore,ih]
    rfl

theorem nextStore_tapeData (q tmp : Fin R) (ps : List (SamplerOdometer.Digit R))
    (s : TapeStore R B) : FieldConvolution.tapeData (SamplerOdometer.nextStore q tmp ps s)=
      FieldConvolution.tapeData s := by
  have h := SamplerOdometer.nextStore_payload q tmp ps s
  exact congrArg₂ Prod.mk h.1 (congrArg₂ Prod.mk h.2.1 (congrArg₂ Prod.mk h.2.2.1 h.2.2.2))

theorem odometer_frame (d n k M : ℕ) (inp : Inputs)
    (s e : TapeStore (Storage.registers d k) 2)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s)
    (hf : ∀ j : Fin 80,j≠61 → e.reg (Storage.low d k j)=s.reg (Storage.low d k j))
    (ht : FieldConvolution.tapeData e=FieldConvolution.tapeData s) (hb : ∀ j,e.reg j ≤ M) :
    RuntimeReady (Storage.low d k) d n k inp M e := by
  apply hs.frame
  · intro j hj
    apply hf
    rcases hj with rfl|rfl|rfl|rfl|hj <;> omega
  · intro b j;exact congrArg (fun z => (z.2.2.1 b).getD j .blank) ht
  · intro b
    exact (congrArg (fun z => z.2.2.2 b) ht).le.trans (hs.tables.heads b)
  · exact hb

theorem initializeStore_ready (d n k M : ℕ) (inp : Inputs)
    (s : TapeStore (Storage.registers d k) 2)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s)
    (hb : ∀ j,(SamplerOdometer.initializeStore (Storage.low d k 35) (Storage.low d k 61)
      (Storage.pointPairs d k) s).reg j ≤ M) :
    RuntimeReady (Storage.low d k) d n k inp M
      (SamplerOdometer.initializeStore (Storage.low d k 35) (Storage.low d k 61) (Storage.pointPairs d k) s) := by
  apply odometer_frame d n k M inp s _ hs
  · intro j hj
    exact SamplerOdometer.initializeStore_fresh _ _ _ s _
      ((Storage.low_injective d k).ne hj) (low_not_used d k j)
  · exact initializeStore_payload _ _ _ s
  · exact hb

theorem nextStore_ready (d n k M : ℕ) (inp : Inputs)
    (s : TapeStore (Storage.registers d k) 2)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s)
    (hb : ∀ j,(SamplerOdometer.nextStore (Storage.low d k 35) (Storage.low d k 61)
      (Storage.pointPairs d k) s).reg j ≤ M) :
    RuntimeReady (Storage.low d k) d n k inp M
      (SamplerOdometer.nextStore (Storage.low d k 35) (Storage.low d k 61) (Storage.pointPairs d k) s) := by
  apply odometer_frame d n k M inp s _ hs
  · intro j hj
    exact SamplerOdometer.nextStore_fresh _ _ _ s _
      ((Storage.low_injective d k).ne hj) (low_not_used d k j)
  · exact nextStore_tapeData _ _ _ s
  · exact hb

theorem writeRow_low (d k : ℕ) (s : TapeStore (Storage.registers d k) 2)
    (j : Fin 80) (hj : j.val<40) :
    (NeighborWriter.writeRowStore (writerLayout d k) s).reg (Storage.low d k j)=s.reg (Storage.low d k j) := by
  by_cases h32 : j=32
  · subst j;exact NeighborWriter.writeRow_n _ s
  apply NeighborWriter.writeRow_fresh
  intro i
  cases i with
  | inl a =>
    intro heq
    have h := congrArg Fin.val heq
    change j.val=(writerIndex a).val at h
    fin_cases a <;> simp [writerIndex] at h <;> first | exact h32 (Fin.ext h) | omega
  | inr a =>
    intro heq
    have h := congrArg Fin.val heq
    change j.val=80+4*d+a.val at h
    omega

theorem writeRow_point (d k : ℕ) (s : TapeStore (Storage.registers d k) 2) (j : Fin d) :
    (NeighborWriter.writeRowStore (writerLayout d k) s).reg (Storage.point d k j)=s.reg (Storage.point d k j) := by
  apply NeighborWriter.writeRow_fresh
  intro i
  cases i with
  | inl a =>
    intro heq
    have h := congrArg Fin.val heq
    change 80+j.val=(writerIndex a).val at h
    fin_cases a <;> simp [writerIndex] at h <;> omega
  | inr a =>
    intro heq
    have h := congrArg Fin.val heq
    change 80+j.val=80+4*d+a.val at h
    have := j.isLt
    omega

theorem writeRow_countdown (d k : ℕ) (s : TapeStore (Storage.registers d k) 2) (j : Fin d) :
    (NeighborWriter.writeRowStore (writerLayout d k) s).reg (Storage.countdown d k j)=s.reg (Storage.countdown d k j) := by
  apply NeighborWriter.writeRow_fresh
  intro i
  cases i with
  | inl a =>
    intro heq
    have h := congrArg Fin.val heq
    change 80+d+j.val=(writerIndex a).val at h
    fin_cases a <;> simp [writerIndex] at h <;> omega
  | inr a =>
    intro heq
    have h := congrArg Fin.val heq
    change 80+d+j.val=80+4*d+a.val at h
    have := j.isLt
    omega

theorem writeRow_remaining (d k : ℕ) (s : TapeStore (Storage.registers d k) 2) :
    (NeighborWriter.writeRowStore (writerLayout d k) s).reg (Storage.low d k 60)=s.reg (Storage.low d k 60) := by
  apply NeighborWriter.writeRow_fresh
  intro i
  cases i with
  | inl a =>
    intro heq
    have h := congrArg Fin.val heq
    change 60=(writerIndex a).val at h
    fin_cases a <;> simp [writerIndex] at h
  | inr a =>
    intro heq
    have h := congrArg Fin.val heq
    change 60=80+4*d+a.val at h
    omega

theorem writeRow_ready (d n k M : ℕ) (inp : Inputs)
    (s : TapeStore (Storage.registers d k) 2) (hM : 1 ≤ M)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s) :
    RuntimeReady (Storage.low d k) d n k inp M (NeighborWriter.writeRowStore (writerLayout d k) s) := by
  have ht := NeighborWriter.writeRow_payload (writerLayout d k) s
  apply hs.frame
  · intro j hj
    apply writeRow_low
    rcases hj with rfl|rfl|rfl|rfl|hj <;> omega
  · intro b j;rw [ht.2.1]
  · intro b;rw [ht.2.2];exact hs.tables.heads b
  · exact NeighborWriter.writeRowStore_bound (writerLayout d k) s M hM hs.counters

theorem writeRow_valid (d k : ℕ) (s : TapeStore (Storage.registers d k) 2)
    (hv : SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) s) :
    SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k)
      (NeighborWriter.writeRowStore (writerLayout d k) s) := by
  intro p hp
  obtain ⟨i,hi,hpi⟩ := List.mem_map.mp hp
  subst p
  change _+_+1=_
  rw [writeRow_point,writeRow_countdown,writeRow_low d k s 35 (by decide)]
  exact hv _ (List.mem_map.mpr ⟨i,hi,rfl⟩)

theorem writeRow_readings (d k : ℕ) (s : TapeStore (Storage.registers d k) 2) :
    SamplerOdometer.readings (Storage.pointPairs d k) (NeighborWriter.writeRowStore (writerLayout d k) s)=
      SamplerOdometer.readings (Storage.pointPairs d k) s := by
  apply SamplerOdometer.readings_congr
  intro p hp
  obtain ⟨i,hi,hpi⟩ := List.mem_map.mp hp
  subst p
  exact writeRow_point d k s i

def operations (d n : ℕ) : EncodedGaussian.Operations (Fin (fieldSize d n)) := BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n)
def formValues (d n k : ℕ) (inp : Inputs) : Fin (2*k*fieldSize d n*d) → Fin (fieldSize d n) :=
  RandomTables.sampledValues inp (2*k*fieldSize d n*d) (fieldExponent d n) 0
def hashValues (d n k : ℕ) (inp : Inputs) :
    Fin (k*fieldSize d n*fieldSize d n*fieldSize d n) → Fin (2^Nat.log 2 (n/k)) :=
  RandomTables.sampledValues inp (k*fieldSize d n*fieldSize d n*fieldSize d n) (Nat.log 2 (n/k))
    ((2*k*fieldSize d n*d)*fieldExponent d n)

structure RowState (d n k M : ℕ) (inp : Inputs) (r : ℕ) (hr : r ≤ rowCount d n)
    (s : TapeStore (Storage.registers d k) 2) : Prop where
  ready : RuntimeReady (Storage.low d k) d n k inp M s
  valid : SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) s
  number : Nat.ofDigits (fieldSize d n) (SamplerOdometer.readings (Storage.pointPairs d k) s)=r%rowCount d n
  output : s.output=SamplerRows.rowsBefore (n:=n) (operations d n) (formValues d n k inp)
    (hashValues d n k inp) r hr

theorem pointPairs_readings (d k : ℕ) (s : TapeStore (Storage.registers d k) 2) :
    SamplerOdometer.readings (Storage.pointPairs d k) s=List.ofFn (fun j => s.reg (Storage.point d k j)) := by
  simp [SamplerOdometer.readings,Storage.pointPairs,List.map_map,List.ofFn_eq_map]

theorem RowState.point (d n k M : ℕ) (inp : Inputs) (r : ℕ) (hr : r<rowCount d n)
    (s : TapeStore (Storage.registers d k) 2) (hs : RowState d n k M inp r (Nat.le_of_lt hr) s) :
    ∀ j,s.reg (Storage.point d k j)=(EncodedTester.digits (fieldSize d n) d ⟨r,hr⟩ j).val := by
  exact SamplerRows.readings_eq_digits (Storage.low d k 35) (Storage.pointPairs d k) s hs.valid
    hs.ready.sizes.field (Storage.point d k) (pointPairs_readings d k s) r hr
    (by rw [hs.number,Nat.mod_eq_of_lt hr])

/-- The operational contract for the k actual layer fragments within one row.
All fields are postconditions over actual source configurations and table cells. -/
structure LayerBlockPost (d n k M : ℕ) (inp : Inputs)
    (s : TapeStore (Storage.registers d k) 2) (z : Fin ((fieldSize d n)^d))
    (e : TapeStore (Storage.registers d k) 2) : Prop where
  ready : RuntimeReady (Storage.low d k) d n k inp M e
  valid : SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) e
  readings : SamplerOdometer.readings (Storage.pointPairs d k) e=SamplerOdometer.readings (Storage.pointPairs d k) s
  remaining : e.reg (Storage.low d k 60)=s.reg (Storage.low d k 60)
  output : e.output=s.output
  neighbors : ∀ i,e.reg (Storage.neighbor d k i)=i.val*(2^Nat.log 2 (n/k))+
    (EncodedSampler.neighbor (operations d n) (formValues d n k inp) (hashValues d n k inp) i
      (EncodedTester.digits (fieldSize d n) d z)).val

def rowBodyTime (d k C M : ℕ) : ℕ := C+NeighborWriter.writeRowBound k M+d*(8*M+20)+2

theorem rowBody_stops_of_layers (d n k M : ℕ) (inp : Inputs) (hM : 1 ≤ M)
    (huniq : (Storage.low d k 35::Storage.low d k 61::SamplerOdometer.used (Storage.pointPairs d k)).Nodup)
    (C : ℕ)
    (hLayers : ∀ (s : TapeStore (Storage.registers d k) 2) (z : Fin ((fieldSize d n)^d)),
      RuntimeReady (Storage.low d k) d n k inp M s →
      SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) s →
      (∀ j,s.reg (Storage.point d k j)=(EncodedTester.digits (fieldSize d n) d z j).val) →
      ∃ t e,t ≤ C ∧ (layers d k (List.finRange k)).Stops inp
        (s.toCfg (layers d k (List.finRange k)).entry) t e ∧ LayerBlockPost d n k M inp s z e.store)
    (r : ℕ) (hr : r<rowCount d n) (s : TapeStore (Storage.registers d k) 2)
    (hs : RowState d n k M inp r (Nat.le_of_lt hr) s) :
    ∃ t e,t ≤ rowBodyTime d k C M ∧
      (rowBody d k).Stops inp (s.toCfg (rowBody d k).entry) t e ∧
      RowState d n k M inp (r+1) (by omega) e.store ∧
      e.reg (Storage.low d k 60)=s.reg (Storage.low d k 60) := by
  let z : Fin ((fieldSize d n)^d) := ⟨r,hr⟩
  obtain ⟨t₁,a,ht₁,ha,hap⟩ := hLayers s z hs.ready hs.valid (RowState.point d n k M inp r hr s hs)
  obtain ⟨t₂,b,ht₂,hb,hbs⟩ := NeighborWriter.writeRow_stops (writerLayout d k) inp a.store M hM hap.ready.counters
  have hbReady : RuntimeReady (Storage.low d k) d n k inp M b.store := by
    rw [hbs];exact writeRow_ready d n k M inp a.store hM hap.ready
  have hbValid : SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) b.store := by
    rw [hbs];exact writeRow_valid d k a.store hap.valid
  obtain ⟨t₃,e,ht₃,he,hes,heb⟩ := SamplerOdometer.program_stops_valid (Storage.low d k 35)
    (Storage.low d k 61) (Storage.pointPairs d k) huniq inp M b.store hbReady.counters hbValid
  have heReady : RuntimeReady (Storage.low d k) d n k inp M e.store := by
    rw [hes]
    apply nextStore_ready d n k M inp b.store hbReady
    simpa only [← hes] using heb
  have heValid : SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) e.store := by
    rw [hes];exact SamplerOdometer.program_valid _ _ _ huniq b.store hbValid
  have hbn : Nat.ofDigits (fieldSize d n) (SamplerOdometer.readings (Storage.pointPairs d k) b.store)=r := by
    rw [hbs,writeRow_readings,hap.readings,hs.number,Nat.mod_eq_of_lt hr]
  have hen := SamplerOdometer.program_number (Storage.low d k 35) (Storage.low d k 61)
    (Storage.pointPairs d k) huniq b.store hbValid
    (by rw [hbReady.sizes.field];have := fieldSize_ge_two d n;omega)
  have hnum : Nat.ofDigits (fieldSize d n) (SamplerOdometer.readings (Storage.pointPairs d k) e.store)=
      (r+1)%rowCount d n := by
    rw [hes]
    rw [hbReady.sizes.field] at hen
    rw [hbn] at hen
    simpa only [rowCount,Storage.pointPairs,List.length_map,List.length_finRange] using hen
  have hrnext : r+1 ≤ (fieldSize d n)^d := by change r+1 ≤ rowCount d n;omega
  have heo := (SamplerOdometer.nextStore_payload (Storage.low d k 35) (Storage.low d k 61)
    (Storage.pointPairs d k) b.store).2.1
  have hout : e.output=SamplerRows.rowsBefore (n:=n) (operations d n) (formValues d n k inp)
      (hashValues d n k inp) (r+1) hrnext := by
    change e.store.output=_
    rw [hes,heo,hbs,writeRow_matches (operations d n) (formValues d n k inp) (hashValues d n k inp)
      z a.store hap.ready.sizes.input hap.neighbors,hap.output,hs.output]
    exact (SamplerRows.prefix_succ (operations d n) (formValues d n k inp) (hashValues d n k inp) r hrnext).symm
  have hremaining : e.reg (Storage.low d k 60)=s.reg (Storage.low d k 60) := by
    change e.store.reg _=_
    rw [hes,SamplerOdometer.nextStore_fresh _ _ _ _ _
      ((Storage.low_injective d k).ne (by decide)) (low_not_used d k 60),hbs,writeRow_remaining,hap.remaining]
  refine ⟨_,_,?_,(ha.seq hb).seq he,⟨heReady,heValid,hnum,hout⟩,hremaining⟩
  unfold rowBodyTime
  simp only [Storage.pointPairs,List.length_map,List.length_finRange] at ht₃
  omega

theorem point_ne_low (d k : ℕ) (i : Fin d) (j : Fin 80) : Storage.point d k i≠Storage.low d k j := by
  intro heq
  have h := congrArg Fin.val heq
  have := j.isLt
  simp only [Storage.point_val,Storage.low_val] at h
  omega

theorem countdown_ne_low (d k : ℕ) (i : Fin d) (j : Fin 80) : Storage.countdown d k i≠Storage.low d k j := by
  intro heq
  have h := congrArg Fin.val heq
  have := j.isLt
  simp only [Storage.countdown_val,Storage.low_val] at h
  omega

theorem RowState.setLow (d n k M : ℕ) (inp : Inputs) (r : ℕ) (hr : r ≤ rowCount d n)
    (s : TapeStore (Storage.registers d k) 2) (hs : RowState d n k M inp r hr s)
    (j : Fin 80) (hj : ¬Protected j) (a : ℕ) (ha : a ≤ M) :
    RowState d n k M inp r hr (s.setReg (Storage.low d k j) a) := by
  have hf : ∀ i,Protected i → Storage.low d k i≠Storage.low d k j := by
    intro i hi heq
    have h := Storage.low_injective d k heq
    subst i
    exact hj hi
  have hq := hf 35 (by right;right;right;right;decide)
  have hread : SamplerOdometer.readings (Storage.pointPairs d k) (s.setReg (Storage.low d k j) a)=
      SamplerOdometer.readings (Storage.pointPairs d k) s := by
    rw [pointPairs_readings,pointPairs_readings]
    congr 1
    funext i
    simp [TapeStore.setReg,point_ne_low d k i j]
  constructor
  · exact hs.ready.setReg _ _ ha hf
  · intro p hp
    obtain ⟨i,hi,hpi⟩ := List.mem_map.mp hp
    subst p
    simpa [TapeStore.setReg,point_ne_low d k i j,countdown_ne_low d k i j,hq] using hs.valid _
      (List.mem_map.mpr ⟨i,hi,rfl⟩)
  · rw [hread];exact hs.number
  · exact hs.output

def LayerBlockContract (d n k M : ℕ) (inp : Inputs) (C : ℕ) : Prop :=
  ∀ (s : TapeStore (Storage.registers d k) 2) (z : Fin ((fieldSize d n)^d)),
    RuntimeReady (Storage.low d k) d n k inp M s →
    SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) s →
    (∀ j,s.reg (Storage.point d k j)=(EncodedTester.digits (fieldSize d n) d z j).val) →
    ∃ t e,t ≤ C ∧ (layers d k (List.finRange k)).Stops inp
      (s.toCfg (layers d k (List.finRange k)).entry) t e ∧ LayerBlockPost d n k M inp s z e.store

def finishTime (d n k C M : ℕ) : ℕ :=
  d*(8*M+20)+(7*M+7)+2+rowCount d n*(rowBodyTime d k C M+2)+1

/-- Full actual runtime row loop, reduced only to the strictly smaller actual
layer block. The invariant accounts for every written row and physical carry. -/
theorem finish_stops_of_layers (d n k M : ℕ) (inp : Inputs) (hM : 1 ≤ M)
    (huniq : (Storage.low d k 35::Storage.low d k 61::SamplerOdometer.used (Storage.pointPairs d k)).Nodup)
    (C : ℕ) (hLayers : LayerBlockContract d n k M inp C)
    (s : TapeStore (Storage.registers d k) 2)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s) (hout : s.output=[]) :
    ∃ t e,t ≤ finishTime d n k C M ∧
      (finish d k).Stops inp (s.toCfg (finish d k).entry) t e ∧
      e.output=matrixBits (binarySamplerFromInput d n k (Nat.log 2 (n/k)) inp) := by
  let q := Storage.low d k 35
  let tmp := Storage.low d k 61
  let ps := Storage.pointPairs d k
  obtain ⟨t₁,a,ht₁,ha,has,hab⟩ := SamplerOdometer.initialize_stops q tmp ps huniq inp M s hs.counters
  have haReady : RuntimeReady (Storage.low d k) d n k inp M a.store := by
    rw [has]
    apply initializeStore_ready d n k M inp s hs
    intro j
    have h : a.store.reg j ≤ M := hab j
    rw [has] at h
    exact h
  have haValid : SamplerOdometer.Valid q ps a.store := by
    rw [has]
    apply SamplerOdometer.initializeStore_valid q tmp ps huniq s
    rw [hs.sizes.field]
    exact fieldSize_pos d n
  have haNumber : Nat.ofDigits (fieldSize d n) (SamplerOdometer.readings ps a.store)=0 := by
    rw [has]
    change Nat.ofDigits (fieldSize d n) (SamplerOdometer.readings (Storage.pointPairs d k) _)=0
    rw [pointPairs_readings,SamplerOdometer.number_ofFn]
    apply Finset.sum_eq_zero
    intro i hi
    have hv := SamplerOdometer.initializeStore_values q tmp ps huniq s
      (Storage.point d k i,Storage.countdown d k i)
      (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
    simp only [hv.1,zero_mul]
  have haOut : a.output=[] := by
    have ht := initializeStore_payload q tmp ps s
    change a.store.output=[]
    rw [has]
    exact (congrArg (fun z => z.2.1) ht).trans hout
  have haState : RowState d n k M inp 0 (Nat.zero_le _) a.store := by
    exact ⟨haReady,haValid,by simpa using haNumber,by simpa [SamplerRows.rowsBefore] using haOut⟩
  obtain ⟨t₂,b,ht₂,hb,hbs,hbb⟩ := copy_stops_bound (Storage.low d k 36) (Storage.low d k 60)
    (Storage.low d k 61) ((Storage.low_injective d k).ne (by decide))
    ((Storage.low_injective d k).ne (by decide)) ((Storage.low_injective d k).ne (by decide)) inp M a.store hab
  have hmM : rowCount d n ≤ M := by rw [← haReady.sizes.rows];exact hab _
  have hbState : RowState d n k M inp 0 (Nat.zero_le _) b.store := by
    rw [hbs,haReady.sizes.rows]
    exact (haState.setLow d n k M inp 0 (Nat.zero_le _) a.store 60 (by simp [Protected]) _ hmM).setLow
      d n k M inp 0 (Nat.zero_le _) _ 61 (by simp [Protected]) 0 (Nat.zero_le _)
  have hbCount : b.reg (Storage.low d k 60)=rowCount d n := by
    change b.store.reg _=_
    rw [hbs]
    simpa [SamplerEvaluation.reg_layout (Storage.low d k) (Storage.low_injective d k)] using haReady.sizes.rows
  let m := rowCount d n
  let Inv : ℕ → TapeStore (Storage.registers d k) 2 → Prop := fun rem c =>
    rem ≤ m ∧ RowState d n k M inp (m-rem) (Nat.sub_le m rem) c
  have hbody : ∀ rem c,c.reg (Storage.low d k 60)=rem+1 → Inv (rem+1) c →
      ∃ t e,t ≤ rowBodyTime d k C M ∧
        (rowBody d k).Stops inp ((TapeProgram.decStore (Storage.low d k 60) c).toCfg (rowBody d k).entry) t e ∧
        Inv rem e.store ∧ e.reg (Storage.low d k 60)=rem := by
    intro rem c hcr hI
    rcases hI with ⟨hrem,hstate⟩
    have hdec : RowState d n k M inp (m-(rem+1)) (Nat.sub_le m (rem+1))
        (TapeProgram.decStore (Storage.low d k 60) c) :=
      hstate.setLow d n k M inp _ _ c 60 (by simp [Protected]) _
        ((Nat.sub_le _ _).trans (hstate.ready.counters _))
    have hr : m-(rem+1)<rowCount d n := by change m-(rem+1) < m;omega
    obtain ⟨t,e,ht,he,hpost,her⟩ := rowBody_stops_of_layers d n k M inp hM huniq C hLayers
      (m-(rem+1)) hr (TapeProgram.decStore (Storage.low d k 60) c) hdec
    refine ⟨t,e,ht,he,⟨by omega,?_⟩,?_⟩
    · have heq : m-(rem+1)+1=m-rem := by omega
      simpa only [heq] using hpost
    · rw [her]
      simp [TapeProgram.decStore,hcr]
  have hbI : Inv m b.store := by
    constructor
    · rfl
    · simpa [Inv] using hbState
  obtain ⟨t₃,e,ht₃,he,hIe,her⟩ := countedLoop_stops_frame (rowBody d k) (Storage.low d k 60) inp
    (rowBodyTime d k C M) Inv hbody m b.store hbCount hbI
  have heOut : e.output=matrixBits (binarySamplerFromInput d n k (Nat.log 2 (n/k)) inp) := by
    have ho := hIe.2.output
    change e.output=SamplerRows.rowsBefore (n:=n) (operations d n) (formValues d n k inp)
      (hashValues d n k inp) ((fieldSize d n)^d) le_rfl at ho
    exact ho.trans (SamplerRows.prefix_full (q:=fieldSize d n) (d:=d) (k:=k) (b:=2^Nat.log 2 (n/k))
      (n:=n) (operations d n) (formValues d n k inp) (hashValues d n k inp))
  refine ⟨_,_,?_,(ha.seq hb).seq he,heOut⟩
  unfold finishTime
  simp only [ps,Storage.pointPairs,List.length_map,List.length_finRange] at ht₁
  change t₃ ≤ rowCount d n*(rowBodyTime d k C M+2)+1 at ht₃
  omega

theorem layerInvariant_of_ready (d n k M : ℕ) (inp : Inputs)
    (s : TapeStore (Storage.registers d k) 2)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s) (z : Fin ((fieldSize d n)^d))
    (hz : ∀ j,s.reg (Storage.point d k j)=(EncodedTester.digits (fieldSize d n) d z j).val) :
    LayerInvariant d k (fieldExponent d n) (2^Nat.log 2 (n/k)) (fieldExponent_pos d n)
      (formValues d n k inp) (hashValues d n k inp) (EncodedTester.digits (fieldSize d n) d z) M s := by
  refine ⟨hs.environment,hs.sizes.buckets,hz,hs.counters,hs.tables.heads,?_⟩
  exact ⟨hs.tables.marked 0,hs.tables.marked 1,hs.tables.forms,hs.tables.hashes⟩

theorem layerCaps_of_envelope (d n k M : ℕ) (hd : 1 ≤ d) (hM : SamplerEnvelopeCovers d k n M) :
    LayerCaps d k (fieldExponent d n) (2^Nat.log 2 (n/k)) M := by
  constructor
  · simpa [fieldSize,Nat.add_comm] using hM.forms
  · simpa [fieldSize,samplerBucketCount,pow_succ,pow_two,Nat.mul_assoc,Nat.add_comm] using hM.hashes
  · have hq1 : 1 ≤ fieldSize d n := Nat.one_le_pow _ _ (by decide)
    have hd' := Nat.mul_le_mul_left (2*k*fieldSize d n) hd
    have hq' := Nat.mul_le_mul_left (2*k*fieldSize d n*d) hq1
    change 2*k*fieldSize d n ≤ M
    have hf := hM.forms
    nlinarith
  · exact hM.neighbors

theorem ready_of_layerInvariant (d n k M : ℕ) (inp : Inputs)
    (s e : TapeStore (Storage.registers d k) 2)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s) (z : Fin ((fieldSize d n)^d))
    (he : LayerInvariant d k (fieldExponent d n) (2^Nat.log 2 (n/k)) (fieldExponent_pos d n)
      (formValues d n k inp) (hashValues d n k inp) (EncodedTester.digits (fieldSize d n) d z) M e)
    (hf : ∀ j : Fin 80,32 ≤ j.val → j.val<40 → e.reg (Storage.low d k j)=s.reg (Storage.low d k j)) :
    RuntimeReady (Storage.low d k) d n k inp M e := by
  refine ⟨hs.sizes.frame hf,he.field,?_,he.counters⟩
  refine ⟨he.tables.formTable,he.tables.hashTable,?_,he.heads⟩
  intro b
  fin_cases b
  · exact he.tables.formMarked
  · exact he.tables.hashMarked

structure StablePost (d n k M : ℕ) (inp : Inputs)
    (s e : TapeStore (Storage.registers d k) 2) : Prop where
  ready : RuntimeReady (Storage.low d k) d n k inp M e
  points : ∀ j,e.reg (Storage.point d k j)=s.reg (Storage.point d k j)
  countdowns : ∀ j,e.reg (Storage.countdown d k j)=s.reg (Storage.countdown d k j)
  remaining : e.reg (Storage.low d k 60)=s.reg (Storage.low d k 60)
  output : e.output=s.output

theorem StablePost.refl (d n k M : ℕ) (inp : Inputs) (s : TapeStore (Storage.registers d k) 2)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s) : StablePost d n k M inp s s :=
  ⟨hs,fun _ => rfl,fun _ => rfl,rfl,rfl⟩

theorem StablePost.trans {d n k M : ℕ} {inp : Inputs}
    {s e f : TapeStore (Storage.registers d k) 2}
    (h : StablePost d n k M inp s e) (g : StablePost d n k M inp e f) : StablePost d n k M inp s f :=
  ⟨g.ready,fun j => (g.points j).trans (h.points j),fun j => (g.countdowns j).trans (h.countdowns j),
    g.remaining.trans h.remaining,g.output.trans h.output⟩

structure StepPost (d n k M : ℕ) (inp : Inputs) (i : Fin k)
    (s : TapeStore (Storage.registers d k) 2) (z : Fin ((fieldSize d n)^d))
    (e : TapeStore (Storage.registers d k) 2) : Prop where
  stable : StablePost d n k M inp s e
  neighbor : e.reg (Storage.neighbor d k i)=i.val*(2^Nat.log 2 (n/k))+
    (EncodedSampler.neighbor (operations d n) (formValues d n k inp) (hashValues d n k inp) i
      (EncodedTester.digits (fieldSize d n) d z)).val
  other : ∀ j,j≠i → e.reg (Storage.neighbor d k j)=s.reg (Storage.neighbor d k j)

def StepContract (d n k M : ℕ) (inp : Inputs) (C : ℕ) : Prop :=
  ∀ (i : Fin k) (s : TapeStore (Storage.registers d k) 2) (z : Fin ((fieldSize d n)^d)),
    RuntimeReady (Storage.low d k) d n k inp M s →
    (∀ j,s.reg (Storage.point d k j)=(EncodedTester.digits (fieldSize d n) d z j).val) →
    ∃ t e,t ≤ C ∧ (layer d k i).Stops inp (s.toCfg (layer d k i).entry) t e ∧
      StepPost d n k M inp i s z e.store

theorem block_contract_of_step (d n k M : ℕ) (inp : Inputs) (C : ℕ)
    (hStep : StepContract d n k M inp C) : LayerBlockContract d n k M inp (k*(C+1)) := by
  intro s z hs hv hz
  let Good : TapeStore (Storage.registers d k) 2 → Prop := StablePost d n k M inp s
  let value : Fin k → ℕ := fun i => i.val*(2^Nat.log 2 (n/k))+
    (EncodedSampler.neighbor (operations d n) (formValues d n k inp) (hashValues d n k inp) i
      (EncodedTester.digits (fieldSize d n) d z)).val
  have hstep : ∀ i c,Good c → ∃ t e,t ≤ C ∧
      (layer d k i).Stops inp (c.toCfg (layer d k i).entry) t e ∧ Good e.store ∧
      e.reg (Storage.neighbor d k i)=value i ∧
      (∀ j,j≠i → e.reg (Storage.neighbor d k j)=c.reg (Storage.neighbor d k j)) := by
    intro i c hc
    obtain ⟨t,e,ht,he,hpost⟩ := hStep i c z hc.ready (fun j => (hc.points j).trans (hz j))
    exact ⟨t,e,ht,he,hc.trans hpost.stable,hpost.neighbor,hpost.other⟩
  obtain ⟨t,e,ht,he,hstable,hvalues,hframe⟩ := layers_stops_of d k inp C Good value hstep
    (List.finRange k) s (StablePost.refl d n k M inp s hs)
  have heValid : SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) e.store := by
    intro p hp
    obtain ⟨i,hi,hpi⟩ := List.mem_map.mp hp
    subst p
    rw [hstable.points,hstable.countdowns,hstable.ready.sizes.field,← hs.sizes.field]
    exact hv _ (List.mem_map.mpr ⟨i,hi,rfl⟩)
  have heRead : SamplerOdometer.readings (Storage.pointPairs d k) e.store=
      SamplerOdometer.readings (Storage.pointPairs d k) s := by
    apply SamplerOdometer.readings_congr
    intro p hp
    obtain ⟨i,hi,hpi⟩ := List.mem_map.mp hp
    subst p
    exact hstable.points i
  refine ⟨t,e,by simpa using ht,he,⟨hstable.ready,heValid,heRead,hstable.remaining,hstable.output,?_⟩⟩
  intro i
  exact hvalues i (List.mem_finRange i)

def blockTime (d k M : ℕ) : ℕ := k*(layerTimeUniform d k M+1)
def sourceTime (d n k : ℕ) : ℕ :=
  preludeTime d n (samplerEnvelope d k n)+1+
    finishTime d n k (blockTime d k (samplerEnvelope d k n)) (samplerEnvelope d k n)

theorem sourceTime_polynomial (d k : ℕ) (hd : 0<d) : PolynomialBound (fun n => sourceTime d n k) := by
  have hM := samplerEnvelope_polynomial d k hd
  have hC : PolynomialBound (fun n => blockTime d k (samplerEnvelope d k n)) :=
    (PolynomialBound.const k).mul (((layerTimeUniform_polynomial d k).comp hM).add (PolynomialBound.const 1))
  have hW0 : PolynomialBound (fun M => NeighborWriter.writeRowBound k M) :=
    ((PolynomialBound.const (161*k+25)).mul
      ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 2)).of_le
      (fun M _ => NeighborWriter.writeRowBound_polynomial k M)
  have hW := hW0.comp hM
  have hO : PolynomialBound (fun n => d*(8*samplerEnvelope d k n+20)) :=
    (PolynomialBound.const d).mul (((PolynomialBound.const 8).mul hM).add (PolynomialBound.const 20))
  have hRow : PolynomialBound (fun n => rowBodyTime d k (blockTime d k (samplerEnvelope d k n))
      (samplerEnvelope d k n)) :=
    ((hC.add hW).add hO).add (PolynomialBound.const 2)
  have hF : PolynomialBound (fun n => finishTime d n k (blockTime d k (samplerEnvelope d k n))
      (samplerEnvelope d k n)) :=
    (((hO.add (((PolynomialBound.const 7).mul hM).add (PolynomialBound.const 7))).add
      (PolynomialBound.const 2)).add
      ((rowCount_polynomial d hd).mul (hRow.add (PolynomialBound.const 2)))).add (PolynomialBound.const 1)
  exact ((preludeTime_polynomial d k hd).add (PolynomialBound.const 1)).add hF

theorem sampler_stops_of_step (d n k : ℕ) (hd : 1 ≤ d) (hk : 0<k) (hn : 2 ≤ n) (hnk : k ≤ n)
    (inp : Inputs) (hi : inp.input=sizeInput n)
    (hStep : StepContract d n k (samplerEnvelope d k n) inp
      (layerTimeUniform d k (samplerEnvelope d k n))) :
    ∃ t e,t ≤ sourceTime d n k ∧
      (sampler d k).Stops inp ((initialStore (Storage.registers d k) 2).toCfg (sampler d k).entry) t e ∧
      e.output=matrixBits (binarySamplerFromInput d n k (Nat.log 2 (n/k)) inp) := by
  have hM := samplerEnvelope_covers d k n
  obtain ⟨t₁,a,ht₁,ha,has,haReady,haOut⟩ := prelude_stops (Storage.low d k)
    (Storage.low_injective d k) d n k hd hk hn hnk inp hi (samplerEnvelope d k n) hM
  obtain ⟨t₂,e,ht₂,he,heo⟩ := finish_stops_of_layers d n k (samplerEnvelope d k n) inp
    (by have := hM.two;omega) (Storage.pointPairs_nodup d k) (blockTime d k (samplerEnvelope d k n))
    (block_contract_of_step d n k _ inp _ hStep) a.store haReady haOut
  refine ⟨_,_,?_,ha.seq he,heo⟩
  unfold sourceTime
  omega

theorem sampler_source_of_step (d n k : ℕ) (hd : 1 ≤ d) (hk : 0<k) (hn : 2 ≤ n) (hnk : k ≤ n)
    (ω : List Bool)
    (hStep : StepContract d n k (samplerEnvelope d k n) ⟨sizeInput n,[],[],ω⟩
      (layerTimeUniform d k (samplerEnvelope d k n))) :
    ∃ t ≤ sourceTime d n k,
      (sampler d k).halted ((sampler d k).run ⟨sizeInput n,[],[],ω⟩ t) ∧
      ((sampler d k).run ⟨sizeInput n,[],[],ω⟩ t).output=
        matrixBits (binarySamplerFromInput d n k (Nat.log 2 (n/k)) ⟨sizeInput n,[],[],ω⟩) := by
  obtain ⟨t,e,ht,he,heo⟩ := sampler_stops_of_step d n k hd hk hn hnk ⟨sizeInput n,[],[],ω⟩ rfl hStep
  have hr := he.exec.iterate
  change (sampler d k).run ⟨sizeInput n,[],[],ω⟩ t=e at hr
  exact ⟨t,ht,by rw [hr];exact he.halted,by rw [hr];exact heo⟩

end Concrete
end ExpandingCodes.Computation.SamplerAssembly
