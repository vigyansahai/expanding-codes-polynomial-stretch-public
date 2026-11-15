import ExpandingCodes.Computation.SamplerEvaluation
import Definitions.Def_ExpandingCodes_PolynomialStretch_OperationalFamily

set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterInput
open NKtLB SamplerEvaluation
open FieldPrograms UnaryArithmetic
variable {R B : ℕ}

/-- The current RO0 input bit, normalized to a unary zero or one. -/
def bit (inp : Inputs) (p : ℕ) : ℕ := if Machine.readRO inp.input p=.one then 1 else 0

theorem bit_le_one (inp : Inputs) (p : ℕ) : bit inp p ≤ 1 := by unfold bit; split <;> omega

def readBit (a : Fin R) : TapeProgram R B 4 where
  entry := 0
  code j := if j=0 then .read 0 (fun s => if s=.one then 1 else 2)
    else if j=1 then .inc a 3 else if j=2 then .jump 3 else .halt

def readBitStore (a : Fin R) (inp : Inputs) (s : TapeStore R B) : TapeStore R B :=
  { s.setReg a (s.reg a+bit inp (s.roHead 0)) with
    roHead := Function.update s.roHead 0 (s.roHead 0+1) }

theorem readBit_stops (a : Fin R) (inp : Inputs) (s : TapeStore R B) :
    (readBit a).Stops inp (s.toCfg 0) 2 ((readBitStore a inp s).toCfg 3) := by
  let e : TapeStore R B := {s with roHead := Function.update s.roHead 0 (s.roHead 0+1)}
  let j : Fin 4 := if Machine.readRO inp.input (s.roHead 0)=.one then 1 else 2
  have h₁ : (readBit a).step inp (s.toCfg 0)=e.toCfg j := by
    simp [TapeProgram.step,readBit,TapeStore.toCfg,e,j,Inputs.get]
    split_ifs <;> simp_all
  have h₂ : (readBit a).step inp (e.toCfg j)=(readBitStore a inp s).toCfg 3 := by
    by_cases h : Machine.readRO inp.input (s.roHead 0)=.one <;>
      simp [TapeProgram.step,readBit,TapeStore.toCfg,e,j,h,readBitStore,TapeStore.setReg,bit]
  constructor
  · apply TapeProgram.Exec.step (by simp [TapeProgram.halted,readBit]) h₁
    apply TapeProgram.Exec.one
    · dsimp [j]; split_ifs <;> simp [TapeProgram.halted,readBit]
    · exact h₂
  · simp [TapeProgram.halted,readBit]

/-- Four scalar registers: preserved q0, consumed width1, bit2, copy scratch3.
One input bit becomes one physical q-cell thermometer block. -/
def block (r : Fin 4 → Fin R) (b : Fin B) : TapeProgram R B 24 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeMacros.clear (r 2)) (readBit (r 2)))
    (TapeMacros.copy (r 0) (r 1) (r 3))) (TapeArrays.writeBlock (r 2) (r 1) b)

def blockPrepare (r : Fin 4 → Fin R) (inp : Inputs) (s : TapeStore R B) : TapeStore R B :=
  (((readBitStore (r 2) inp (s.setReg (r 2) 0)).setReg (r 1) (s.reg (r 0))).setReg (r 3) 0)

def blockStore (r : Fin 4 → Fin R) (b : Fin B) (inp : Inputs) (s : TapeStore R B) : TapeStore R B :=
  TapeArrays.writeBlockStore (r 2) (r 1) b (bit inp (s.roHead 0)) (s.reg (r 0)) (blockPrepare r inp s)

theorem blockStore_reg (r : Fin 4 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (s : TapeStore R B) :
    (blockStore r b inp s).reg=(((s.setReg (r 1) 0).setReg (r 2) 0).setReg (r 3) 0).reg := by
  rw [blockStore,TapeArrays.writeBlockStore_reg]
  funext j
  simp only [blockPrepare,readBitStore,TapeStore.setReg]
  by_cases h₁ : j=r 1 <;> by_cases h₂ : j=r 2 <;> by_cases h₃ : j=r 3 <;>
    simp_all [Function.update,hr.eq_iff]

def advanced (s : TapeStore R B) : TapeStore R B :=
  {s with roHead := Function.update s.roHead 0 (s.roHead 0+1)}

theorem blockStore_written (r : Fin 4 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (s : TapeStore R B) (hq : 1 ≤ s.reg (r 0)) :
    TapeArrays.EntryWritten (advanced s) (blockStore r b inp s) b (s.bufferHead b) (s.reg (r 0))
      (bit inp (s.roHead 0)) := by
  have hb : bit inp (s.roHead 0) ≤ s.reg (r 0) := (bit_le_one _ _).trans hq
  constructor
  · simp [blockStore,TapeArrays.writeBlockStore_roHead,blockPrepare,readBitStore,advanced,TapeStore.setReg]
  · simp [blockStore,TapeArrays.writeBlockStore_output,blockPrepare,readBitStore,advanced,TapeStore.setReg]
  · simp [blockStore,TapeArrays.writeBlockStore_head _ _ _ _ _ _ hb,blockPrepare,readBitStore,advanced,TapeStore.setReg]
  · intro c k
    rw [blockStore,TapeArrays.writeBlockStore_symbol _ _ _ _ _ _ hb]
    rfl

theorem block_stops (r : Fin 4 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (M : ℕ) (hM : 1 ≤ M)
    (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M) (hq : 1 ≤ s.reg (r 0)) :
    ∃ t e, t ≤ 20*(M+1) ∧
      (block r b).Stops inp (s.toCfg (block (B := B) r b).entry) t e ∧
      e.store=blockStore r b inp s ∧ ∀ j,e.reg j ≤ M := by
  have hclear := TapeMacros.clear_stops (r 2) inp (s.reg (r 2)) s rfl
  have hread := readBit_stops (r 2) inp (s.setReg (r 2) 0)
  let d := readBitStore (r 2) inp (s.setReg (r 2) 0)
  have hdb : ∀ j,d.reg j ≤ M := by
    intro j
    simpa [d,readBitStore,TapeStore.setReg] using
      setReg_bound s (r 2) (bit inp (s.roHead 0)) M hs ((bit_le_one _ _).trans hM) j
  obtain ⟨u,c,hu,hcopy,hcs,hcb⟩ := copy_stops_bound (r 0) (r 1) (r 3)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M d hdb
  have hcpre : c.store=blockPrepare r inp s := by
    rw [hcs]
    have hdq : d.reg (r 0)=s.reg (r 0) := by simp [d,readBitStore,reg_layout r hr]
    rw [hdq]; rfl
  have hcv : c.reg (r 2)=bit inp (s.roHead 0) := by
    change c.store.reg (r 2)=_
    rw [hcpre]
    simp [blockPrepare,readBitStore,TapeStore.setReg,Function.update,hr.eq_iff]
  have hcw : c.reg (r 1)=s.reg (r 0) := by
    change c.store.reg (r 1)=_
    rw [hcpre]
    simp [blockPrepare,reg_layout r hr]
  obtain ⟨e,he,hes⟩ := TapeArrays.writeBlock_stops (r 2) (r 1) (hr.ne (by decide)) b inp
    (bit inp (s.roHead 0)) (s.reg (r 0)) c.store hcv hcw ((bit_le_one _ _).trans hq)
  have hall := ((hclear.seq hread).seq hcopy).seq he
  refine ⟨s.reg (r 2)+1+1+2+1+u+1+(2*s.reg (r 0)+bit inp (s.roHead 0)+3),_,?_,hall,?_,?_⟩
  · have hb₂ := hs (r 2); have hb₀ := hs (r 0); have hbit := bit_le_one inp (s.roHead 0); omega
  · rw [hes,hcpre]; rfl
  · intro j
    change e.store.reg j ≤ M
    rw [hes,hcpre]
    change (blockStore r b inp s).reg j ≤ M
    rw [blockStore_reg r hr]
    exact setReg_bound _ _ 0 M (setReg_bound _ _ 0 M (setReg_bound s _ 0 M hs (by omega)) (by omega)) (by omega) j

/-- Runtime m-fold input storage. Neither m nor q enters this code table. -/
def loadLayout (r : Fin 5 → Fin R) (i : Fin 4) : Fin R := r i.castSucc

theorem loadLayout_injective (r : Fin 5 → Fin R) (hr : Function.Injective r) :
    Function.Injective (loadLayout r) := by
  intro i j hij
  have hh := congrArg (Fin.val : Fin 5 → ℕ) (hr hij)
  exact Fin.ext hh

def load (r : Fin 5 → Fin R) (b : Fin B) : TapeProgram R B 26 :=
  TapeProgram.countedLoop (block (loadLayout r) b) (r 4)

def loadStore (r : Fin 5 → Fin R) (b : Fin B) (inp : Inputs) (n : ℕ) (s : TapeStore R B) : TapeStore R B :=
  SourceFieldArithmetic.loopResult (r 4) (blockStore (loadLayout r) b inp) n s

theorem load_counter (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (s : TapeStore R B) :
    (blockStore (loadLayout r) b inp s).reg (r 4)=s.reg (r 4) := by
  rw [blockStore_reg _ (loadLayout_injective r hr)]
  simp [loadLayout,reg_layout r hr]

/-- Prefix invariant for the eager q-cell input table. All already written cells
are retained while the next bit is read and appended. -/
structure Loading (r : Fin 5 → Fin R) (b : Fin B) (q M start N : ℕ)
    (y : Fin N → Bool) (rem : ℕ) (s : TapeStore R B) : Prop where
  remaining : rem ≤ N
  bounded : ∀ j,s.reg j ≤ M
  width : s.reg (r 0)=q
  positive : 1 ≤ q
  inputHead : s.roHead 0=start+(N-rem)
  head : s.bufferHead b=1+(N-rem)*q
  marked : TapeArrays.BottomMarked s b
  table : ∀ j : Fin N,j.val<N-rem → TapeArrays.ThermometerAt s b (TapeArrays.entryOffset j.val q) q (if y j then 1 else 0)

theorem load_stops (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (M : ℕ) (hM : 1 ≤ M)
    (N start : ℕ) (y : Fin N → Bool) (s : TapeStore R B)
    (hs : ∀ j,s.reg j ≤ M) (hq : 1 ≤ s.reg (r 0)) (hn : s.reg (r 4)=N)
    (hro : s.roHead 0=start) (hh : s.bufferHead b=1) (hm : TapeArrays.BottomMarked s b)
    (hy : ∀ j : Fin N,Machine.readRO inp.input (start+j.val)=if y j then .one else .zero) :
    ∃ t, t ≤ N*(20*(M+1)+2)+1 ∧
      (load r b).Stops inp (s.toCfg (load (B := B) r b).entry) t
        ((loadStore r b inp N s).toCfg (TapeProgram.loopExit 24)) ∧
      (∀ j,(loadStore r b inp N s).reg j ≤ M) ∧
      (loadStore r b inp N s).roHead 0=start+N ∧
      (loadStore r b inp N s).bufferHead b=1+N*s.reg (r 0) ∧
      TapeArrays.BottomMarked (loadStore r b inp N s) b ∧
      TapeArrays.ThermometerTable (loadStore r b inp N s) b (s.reg (r 0)) (fun j => if y j then 1 else 0) := by
  let Inv := Loading r b (s.reg (r 0)) M start N y
  have hi : Inv N s := ⟨by omega,hs,rfl,hq,by simpa using hro,by simpa using hh,hm,by simp⟩
  have hbody : ∀ n d, d.reg (r 4)=n+1 → Inv (n+1) d →
      ∃ t c,t ≤ 20*(M+1) ∧ (block (loadLayout r) b).Stops inp
        ((d.setReg (r 4) n).toCfg (block (B := B) (loadLayout r) b).entry) t c ∧
        c.store=blockStore (loadLayout r) b inp (d.setReg (r 4) n) ∧ Inv n c.store := by
    intro n d hdn hdi
    let p := d.setReg (r 4) n
    have hpb : ∀ j,p.reg j ≤ M := setReg_bound d _ n M hdi.bounded (by have := hdi.bounded (r 4); omega)
    have hpq : p.reg ((loadLayout r) 0)=s.reg (r 0) := by
      simpa [p,loadLayout,reg_layout r hr] using hdi.width
    obtain ⟨t,c,ht,hc,hcs,hcb⟩ := block_stops (loadLayout r) (loadLayout_injective r hr)
      b inp M hM p hpb (by rw [hpq]; exact hq)
    let j : Fin N := ⟨N-(n+1),by have := hdi.remaining; omega⟩
    have hj : j.val=N-(n+1) := rfl
    have hnN : n+1 ≤ N := hdi.remaining
    have hbit : bit inp (p.roHead 0)=(if y j then 1 else 0) := by
      have hsym : Machine.readRO inp.input (p.roHead 0)=if y j then .one else .zero := by
        rw [show p.roHead 0=start+j.val by simpa [p,hj,TapeStore.setReg] using hdi.inputHead]
        exact hy j
      simp only [bit,hsym]
      cases y j <;> rfl
    have hw := blockStore_written (loadLayout r) (loadLayout_injective r hr) b inp p (by rw [hpq]; exact hq)
    have hphead : p.bufferHead b=1+j.val*s.reg (r 0) := by simpa [p,hj,TapeStore.setReg] using hdi.head
    refine ⟨t,c,ht,hc,hcs,?_⟩
    rw [hcs]
    constructor
    · omega
    · change ∀ j,c.store.reg j ≤ M at hcb
      rw [hcs] at hcb
      exact hcb
    · rw [blockStore_reg _ (loadLayout_injective r hr)]
      simpa [loadLayout,reg_layout r hr] using hpq
    · exact hq
    · rw [hw.roHead]
      change p.roHead 0+1=start+(N-n)
      simp only [p,TapeStore.setReg,hdi.inputHead]
      omega
    · rw [hw.head]
      simp only [Function.update_self,hphead,hpq]
      have hcount : N-n=j.val+1 := by omega
      rw [hcount,Nat.add_mul,Nat.one_mul]
      omega
    · exact hw.bottomMarked (by simp [hphead]) hdi.marked
    · intro k hk
      by_cases hkj : k=j
      · subst k
        have hstart : TapeArrays.entryOffset j.val (s.reg (r 0))=p.bufferHead b := by
          simp [TapeArrays.entryOffset,hphead]
        rw [hstart,← hbit,← hpq]
        exact ⟨(bit_le_one _ _).trans (by rw [hpq]; exact hq),by
          intro u hu
          rw [hw.symbol]
          have h₁ : p.bufferHead b ≤ p.bufferHead b+u := by omega
          have h₂ : p.bufferHead b+u<p.bufferHead b+p.reg ((loadLayout r) 0) := by omega
          simp [h₁,h₂,Nat.add_lt_add_iff_left]⟩
      · have hkjlt : k.val<j.val := by
          have hne : k.val≠j.val := fun heq => hkj (Fin.ext heq)
          omega
        have hprior := hdi.table k (by omega)
        refine ⟨hprior.1,?_⟩
        intro u hu
        rw [hw.symbol]
        have hout : ¬(b=b ∧ p.bufferHead b ≤ TapeArrays.entryOffset k.val (s.reg (r 0))+u ∧
            TapeArrays.entryOffset k.val (s.reg (r 0))+u<p.bufferHead b+p.reg ((loadLayout r) 0)) := by
          rw [hphead,TapeArrays.entryOffset]
          have hmul : (k.val+1)*s.reg (r 0) ≤ j.val*s.reg (r 0) := Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul,Nat.one_mul] at hmul
          omega
        rw [if_neg hout]
        exact hprior.2 u hu
  obtain ⟨t,ht,hstop,hfinal⟩ := SourceFieldArithmetic.loop_stops
    (block (loadLayout r) b) (r 4) (blockStore (loadLayout r) b inp) inp (20*(M+1)) Inv
    (load_counter r hr b inp) hbody N s hn hi
  refine ⟨t,ht,hstop,hfinal.bounded,?_,?_,hfinal.marked,?_⟩
  · simpa [loadStore] using hfinal.inputHead
  · simpa [loadStore] using hfinal.head
  · intro j
    exact hfinal.table j (by simpa using j.isLt)

#print axioms block_stops
#print axioms load_stops

theorem loadStore_register_frame (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (n : ℕ) (s : TapeStore R B)
    (j : Fin R) (hj : j≠r 1 ∧ j≠r 2 ∧ j≠r 3 ∧ j≠r 4) :
    (loadStore r b inp n s).reg j=s.reg j := by
  apply SourceFieldArithmetic.loopResult_frame _ _ j hj.2.2.2
  intro d
  rw [blockStore_reg _ (loadLayout_injective r hr)]
  simp [loadLayout,TapeStore.setReg,hj]

theorem loadStore_count (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (n : ℕ) (s : TapeStore R B) (hn : s.reg (r 4)=n) :
    (loadStore r b inp n s).reg (r 4)=0 :=
  SourceFieldArithmetic.loopResult_count _ _ (load_counter r hr b inp) n s hn

theorem loadStore_output (r : Fin 5 → Fin R) (b : Fin B) (inp : Inputs)
    (n : ℕ) (s : TapeStore R B) : (loadStore r b inp n s).output=s.output := by
  unfold loadStore
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [SourceFieldArithmetic.loopResult,ih]
    simp [blockStore,TapeArrays.writeBlockStore_output,blockPrepare,readBitStore,TapeStore.setReg]

theorem loadStore_RO_frame (r : Fin 5 → Fin R) (b : Fin B) (inp : Inputs)
    (n : ℕ) (s : TapeStore R B) (i : Fin 4) (hi : i≠0) :
    (loadStore r b inp n s).roHead i=s.roHead i := by
  unfold loadStore
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [SourceFieldArithmetic.loopResult,ih]
    simp [blockStore,TapeArrays.writeBlockStore_roHead,blockPrepare,readBitStore,TapeStore.setReg,hi]

theorem loadStore_bufferHead_frame (r : Fin 5 → Fin R) (b c : Fin B) (hcb : c≠b) (inp : Inputs)
    (n : ℕ) (s : TapeStore R B) : (loadStore r b inp n s).bufferHead c=s.bufferHead c := by
  unfold loadStore
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [SourceFieldArithmetic.loopResult,ih]
    simp [blockStore,TapeArrays.writeBlockStore,TapeArrays.fillStore_head,blockPrepare,readBitStore,TapeStore.setReg,hcb]

theorem loadStore_bufferSymbol_frame (r : Fin 5 → Fin R) (b c : Fin B) (hcb : c≠b) (inp : Inputs)
    (n : ℕ) (s : TapeStore R B) (k : ℕ) :
    ((loadStore r b inp n s).bufferTape c).getD k .blank=(s.bufferTape c).getD k .blank := by
  unfold loadStore
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [SourceFieldArithmetic.loopResult,ih]
    simp only [blockStore,TapeArrays.writeBlockStore,TapeArrays.fillStore_symbol,hcb,false_and,if_false,blockPrepare,readBitStore,TapeStore.setReg]

/-- Exact current-cell symbols after an arbitrary prefix, including sizeInput. -/
theorem input_symbols (inp : Inputs) (pre : List Bool) {N : ℕ} (y : Fin N → Bool)
    (hi : inp.input=pre++List.ofFn y) (j : Fin N) :
    Machine.readRO inp.input (pre.length+j.val)=if y j then .one else .zero := by
  unfold Machine.readRO
  rw [hi,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,List.getElem?_ofFn]
  simp only [j.isLt,dite_true]
  cases y j <;> rfl

theorem word_symbols (inp : Inputs) (n N : ℕ) (y : ExpandingCodes.PolynomialStretch.Word N)
    (hi : inp.input=ExpandingCodes.PolynomialStretch.sizeInput n++ExpandingCodes.PolynomialStretch.wordBits y)
    (j : Fin N) : Machine.readRO inp.input (n+1+j.val)=if y j≠0 then .one else .zero := by
  have hh := input_symbols inp (ExpandingCodes.PolynomialStretch.sizeInput n)
    (fun j => decide (y j≠0)) hi j
  simpa [ExpandingCodes.PolynomialStretch.sizeInput] using hh

#print axioms loadStore_output
#print axioms word_symbols
end ExpandingCodes.Computation.TesterInput
