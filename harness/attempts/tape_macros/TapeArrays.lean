import ExpandingCodes.Computation.TapeMacros
import ExpandingCodes.Computation.UnaryArithmetic

set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace TapeStore
variable {R B : ℕ}

/-- Payload equality is extensional: physical finite lists may acquire trailing
blank cells during an idle write without changing any observable tape symbol. -/
structure SamePayload (d e : TapeStore R B) : Prop where
  roHead : d.roHead = e.roHead
  output : d.output = e.output
  symbol : ∀ b k, (d.bufferTape b).getD k .blank = (e.bufferTape b).getD k .blank

 theorem SamePayload.refl (d : TapeStore R B) : SamePayload d d :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

 theorem SamePayload.trans {d e f : TapeStore R B}
    (h : SamePayload d e) (k : SamePayload e f) : SamePayload d f :=
  ⟨h.roHead.trans k.roHead, h.output.trans k.output, fun b n => (h.symbol b n).trans (k.symbol b n)⟩

 theorem setReg_payload (d : TapeStore R B) (r : Fin R) (n : ℕ) :
    SamePayload (d.setReg r n) d := ⟨rfl, rfl, fun _ _ => rfl⟩
end TapeStore

namespace TapeArrays
variable {R B : ℕ}
open TapeMacros

/-- One preserving-symbol move, including the actual finite-list write performed
by the source instruction. -/
abbrev moved (d : TapeStore R B) (b : Fin B) (m : Move) : TapeStore R B :=
  cellStore d b (fun s => (s,m))

 theorem moved_payload (d : TapeStore R B) (b : Fin B) (m : Move) :
    TapeStore.SamePayload (moved d b m) d := by
  constructor
  · rfl
  · rfl
  · intro c k
    by_cases h : c = b
    · subst c
      simp only [moved, cellStore, Function.update_self]
      rw [getD_writeAt]
      split <;> simp_all
    · simp [moved, cellStore, Function.update_of_ne h]

@[simp] theorem moved_reg (d : TapeStore R B) (b : Fin B) (m : Move) :
    (moved d b m).reg = d.reg := rfl

@[simp] theorem moved_head (d : TapeStore R B) (b : Fin B) (m : Move) :
    (moved d b m).bufferHead = Function.update d.bufferHead b (Machine.moveHead m (d.bufferHead b)) := rfl

/-- A real charged right seek. Every unit consumes one counter decrement and
one cell move. It does not assume constant-time indexing. -/
def seekRight (r : Fin R) (b : Fin B) : TapeProgram R B 3 where
  entry := 0
  code j := if j = 0 then .dec r 2 1 else if j = 1 then
    .buffer b (fun s => (s, .right, 0)) else .halt

 theorem seekRight_stops (r : Fin R) (b : Fin B) (inp : Inputs)
    (n : ℕ) (d : TapeStore R B) (hd : d.reg r = n) :
    ∃ e, (seekRight r b).Stops inp (d.toCfg 0) (2*n+1) (e.toCfg 2) ∧
      e.reg = Function.update d.reg r 0 ∧
      e.bufferHead = Function.update d.bufferHead b (d.bufferHead b+n) ∧
      TapeStore.SamePayload e d := by
  induction n generalizing d with
  | zero =>
    refine ⟨d, ?_, ?_, ?_, TapeStore.SamePayload.refl d⟩
    · constructor
      · apply TapeProgram.Exec.one
        · simp [TapeProgram.halted, seekRight]
        · simp [TapeProgram.step, seekRight, TapeStore.toCfg, hd]
      · simp [TapeProgram.halted, seekRight]
    · simp [← hd]
    · simp
  | succ n ih =>
    let d₁ := d.setReg r n
    let d₂ := moved d₁ b .right
    have hd₂ : d₂.reg r = n := by simp [d₂, d₁, TapeStore.setReg]
    obtain ⟨e, he, her, heh, hep⟩ := ih d₂ hd₂
    refine ⟨e, ?_, ?_, ?_, ?_⟩
    · have hs₁ : (seekRight r b).step inp (d.toCfg 0) = d₁.toCfg 1 := by
        simp [TapeProgram.step, seekRight, TapeStore.toCfg, TapeStore.setReg, d₁, hd]
      have hs₂ : (seekRight r b).step inp (d₁.toCfg 1) = d₂.toCfg 0 := by
        simp [TapeProgram.step, seekRight, TapeStore.toCfg, d₂, moved, cellStore]
      constructor
      · have h := TapeProgram.Exec.step (by simp [TapeProgram.halted, seekRight]) hs₁
          (TapeProgram.Exec.step (by simp [TapeProgram.halted, seekRight]) hs₂ he.exec)
        simpa [Nat.mul_succ, Nat.add_assoc] using h
      · exact he.halted
    · simpa [d₂, d₁, TapeStore.setReg, Function.update_idem] using her
    · rw [heh]
      simp [d₂, d₁, moved, cellStore, TapeStore.setReg, Machine.moveHead, Function.update_idem, Nat.add_assoc, Nat.add_comm]
    · exact hep.trans ((moved_payload d₁ b .right).trans (TapeStore.setReg_payload d r n))

/-- Reset scans left until the reserved bottom marker, with no lookahead or
whole-buffer primitive. The marker is inspected once before halting. -/
def reset (b : Fin B) : TapeProgram R B 2 where
  entry := 0
  code j := if j = 0 then .buffer b (fun s => if s = .bot then (s,.stay,1) else (s,.left,0))
    else .halt

/-- The active prefix down to cell zero contains exactly one bottom marker. -/
def Marked (d : TapeStore R B) (b : Fin B) : Prop :=
  (d.bufferTape b).getD 0 .blank = .bot ∧
    ∀ k, 0 < k → k ≤ d.bufferHead b → (d.bufferTape b).getD k .blank ≠ .bot

 theorem reset_stops (b : Fin B) (inp : Inputs) (h : ℕ) (d : TapeStore R B)
    (hd : d.bufferHead b = h) (hm : Marked d b) :
    ∃ e, (reset b).Stops inp (d.toCfg 0) (h+1) (e.toCfg 1) ∧
      e.reg = d.reg ∧ e.bufferHead = Function.update d.bufferHead b 0 ∧
      TapeStore.SamePayload e d := by
  induction h generalizing d with
  | zero =>
    let e := moved d b .stay
    have hm0 := hm.1
    change ((d.bufferTape b)[0]?).getD .blank = .bot at hm0
    refine ⟨e, ?_, rfl, ?_, moved_payload d b .stay⟩
    · constructor
      · apply TapeProgram.Exec.one
        · simp [TapeProgram.halted, reset]
        · simp [TapeProgram.step, reset, TapeStore.toCfg, hd, hm0, e, moved, cellStore]
      · simp [TapeProgram.halted, reset]
    · simp [e, moved, cellStore, hd, Machine.moveHead]
  | succ h ih =>
    let d₁ := moved d b .left
    have hs : (d.bufferTape b).getD (d.bufferHead b) .blank ≠ .bot :=
      hm.2 _ (by omega) (by omega)
    have hd₁ : d₁.bufferHead b = h := by simp [d₁, moved, cellStore, hd, Machine.moveHead]
    have hp := moved_payload d b .left
    have hm₁ : Marked d₁ b := by
      constructor
      · rw [hp.symbol]
        exact hm.1
      · intro k hk hkh
        rw [hp.symbol]
        exact hm.2 k hk (by rw [hd₁] at hkh; omega)
    obtain ⟨e, he, her, heh, hep⟩ := ih d₁ hd₁ hm₁
    refine ⟨e, ?_, her, ?_, hep.trans hp⟩
    · constructor
      · have hs₁ : (reset b).step inp (d.toCfg 0) = d₁.toCfg 0 := by
          change ((d.bufferTape b)[d.bufferHead b]?).getD .blank ≠ .bot at hs
          simp [TapeProgram.step, reset, TapeStore.toCfg, hs, d₁, moved, cellStore]
        exact TapeProgram.Exec.step (by simp [TapeProgram.halted, reset]) hs₁ he.exec
      · exact he.halted
    · rw [heh]
      simp [d₁, moved, cellStore, Function.update_idem]

/-- Finite branch destinations for the four canonical tape symbols. -/
def symbolLabel : Sym → Fin 6
  | .zero => 1
  | .one => 2
  | .bot => 3
  | .blank => 4

/-- Copy exactly one read-only cell to the current work-buffer cell and move
the buffer head right. Reading and writing are two separate source steps. -/
def copyCell (i : Fin 4) (b : Fin B) : TapeProgram R B 6 where
  entry := 0
  code j := if j = 0 then .read i symbolLabel
    else if j = 1 then .buffer b (fun _ => (.zero,.right,5))
    else if j = 2 then .buffer b (fun _ => (.one,.right,5))
    else if j = 3 then .buffer b (fun _ => (.bot,.right,5))
    else if j = 4 then .buffer b (fun _ => (.blank,.right,5)) else .halt

def copyCellStore (d : TapeStore R B) (inp : Inputs) (i : Fin 4) (b : Fin B) : TapeStore R B :=
  let s := Machine.readRO (inp.get i) (d.roHead i)
  cellStore { d with roHead := Function.update d.roHead i (d.roHead i+1) } b (fun _ => (s,.right))

 theorem copyCell_stops (i : Fin 4) (b : Fin B) (inp : Inputs) (d : TapeStore R B) :
    (copyCell i b).Stops inp (d.toCfg 0) 2 ((copyCellStore d inp i b).toCfg 5) := by
  let s := Machine.readRO (inp.get i) (d.roHead i)
  let e : TapeStore R B := { d with roHead := Function.update d.roHead i (d.roHead i+1) }
  have hs₁ : (copyCell i b).step inp (d.toCfg 0) = e.toCfg (symbolLabel s) := by
    simp [TapeProgram.step, copyCell, TapeStore.toCfg, e, s]
  have hs₂ : (copyCell i b).step inp (e.toCfg (symbolLabel s)) =
      (copyCellStore d inp i b).toCfg 5 := by
    cases hs : Machine.readRO (inp.get i) (d.roHead i) <;>
      simp [TapeProgram.step, copyCell, symbolLabel, TapeStore.toCfg,
        copyCellStore, cellStore, e, s, hs]
  constructor
  · apply TapeProgram.Exec.step (by simp [TapeProgram.halted, copyCell]) hs₁
    apply TapeProgram.Exec.one
    · cases hs : s <;> simp [TapeProgram.halted, copyCell, symbolLabel, hs]
    · exact hs₂
  · simp [TapeProgram.halted, copyCell]

/-- A counted finite program copying an arbitrary number of read-only symbols
into consecutive buffer cells. Its code size is independent of that number. -/
def copyCells (r : Fin R) (i : Fin 4) (b : Fin B) : TapeProgram R B 8 :=
  TapeProgram.countedLoop (copyCell i b) r

/-- Data-only specification of the successive explicit one-cell copies. -/
def copyCellsStore (r : Fin R) (i : Fin 4) (b : Fin B) (inp : Inputs) :
    ℕ → TapeStore R B → TapeStore R B
  | 0, d => d
  | n+1, d => copyCellsStore r i b inp n
      (copyCellStore (TapeProgram.decStore r d) inp i b)

 theorem copyCells_stops (r : Fin R) (i : Fin 4) (b : Fin B) (inp : Inputs)
    (n : ℕ) (d : TapeStore R B) (hd : d.reg r = n) :
    (copyCells r i b).Stops inp (d.toCfg (TapeProgram.loopHeader 6)) (4*n+1)
      ((copyCellsStore r i b inp n d).toCfg (TapeProgram.loopExit 6)) := by
  induction n generalizing d with
  | zero => exact TapeProgram.loop_zero (copyCell i b) r inp d hd
  | succ n ih =>
    let d₁ := TapeProgram.decStore r d
    let d₂ := copyCellStore d₁ inp i b
    have hr : d₂.reg r = n := by
      simp [d₂, d₁, copyCellStore, cellStore, TapeProgram.decStore, hd]
    have ht := ih d₂ hr
    have hc := copyCell_stops i b inp d₁
    have hh := TapeProgram.loop_positive_header (copyCell i b) r inp d (by omega)
    have hb := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (copyCell i b) r)
    have hx := TapeProgram.loop_body_return (copyCell i b) r inp
      (d₂.toCfg 5) hc.halted
    constructor
    · have h := ((hh.trans hb).trans hx).trans ht.exec
      simpa [copyCells, copyCellsStore, d₂, d₁, Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    · exact ht.halted

 theorem copyCellsStore_reg (r : Fin R) (i : Fin 4) (b : Fin B) (inp : Inputs)
    (n : ℕ) (d : TapeStore R B) :
    (copyCellsStore r i b inp n d).reg = Function.update d.reg r (d.reg r-n) := by
  induction n generalizing d with
  | zero => simp [copyCellsStore]
  | succ n ih =>
    rw [copyCellsStore, ih]
    simp [copyCellStore, cellStore, TapeProgram.decStore, Function.update_idem, Nat.sub_sub, Nat.add_comm]

 theorem copyCellsStore_roHead (r : Fin R) (i : Fin 4) (b : Fin B) (inp : Inputs)
    (n : ℕ) (d : TapeStore R B) :
    (copyCellsStore r i b inp n d).roHead = Function.update d.roHead i (d.roHead i+n) := by
  induction n generalizing d with
  | zero => simp [copyCellsStore]
  | succ n ih =>
    rw [copyCellsStore, ih]
    simp [copyCellStore, cellStore, TapeProgram.decStore, Function.update_idem,
      Nat.add_assoc, Nat.add_comm]

 theorem copyCellsStore_head (r : Fin R) (i : Fin 4) (b : Fin B) (inp : Inputs)
    (n : ℕ) (d : TapeStore R B) :
    (copyCellsStore r i b inp n d).bufferHead =
      Function.update d.bufferHead b (d.bufferHead b+n) := by
  induction n generalizing d with
  | zero => simp [copyCellsStore]
  | succ n ih =>
    rw [copyCellsStore, ih]
    simp [copyCellStore, cellStore, TapeProgram.decStore, Function.update_idem,
      Machine.moveHead, Nat.add_assoc, Nat.add_comm]

 theorem copyCellsStore_output (r : Fin R) (i : Fin 4) (b : Fin B) (inp : Inputs)
    (n : ℕ) (d : TapeStore R B) :
    (copyCellsStore r i b inp n d).output = d.output := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => exact ih _

/-- Exact extensional flat-buffer semantics: the copied interval is read from
successive RO cells; every cell outside it, including other buffers, is preserved. -/
 theorem copyCellsStore_symbol (r : Fin R) (i : Fin 4) (b : Fin B) (inp : Inputs)
    (n : ℕ) (d : TapeStore R B) (c : Fin B) (k : ℕ) :
    ((copyCellsStore r i b inp n d).bufferTape c).getD k .blank =
      if c = b ∧ d.bufferHead b ≤ k ∧ k < d.bufferHead b+n then
        Machine.readRO (inp.get i) (d.roHead i+(k-d.bufferHead b))
      else (d.bufferTape c).getD k .blank := by
  induction n generalizing d with
  | zero =>
    simp only [copyCellsStore, Nat.add_zero]
    split_ifs with hc
    · omega
    · rfl
  | succ n ih =>
    rw [copyCellsStore, ih]
    simp only [copyCellStore, cellStore, TapeProgram.decStore, Machine.moveHead,
      Function.update_self]
    by_cases hc : c = b
    · subst c
      simp only [Function.update_self, true_and, getD_writeAt]
      by_cases hk : k = d.bufferHead b
      · subst k
        simp
      · by_cases hl : d.bufferHead b < k
        · have h₁ : d.bufferHead b+1 ≤ k := by omega
          have h₂ : (d.bufferHead b+1 ≤ k ∧ k < d.bufferHead b+1+n) ↔
              (d.bufferHead b ≤ k ∧ k < d.bufferHead b+(n+1)) := by omega
          have h₃ : d.roHead i+1+(k-(d.bufferHead b+1)) =
              d.roHead i+(k-d.bufferHead b) := by omega
          simp only [h₂, h₃, if_neg hk]
        · have h₁ : ¬ d.bufferHead b+1 ≤ k := by omega
          have h₂ : ¬ d.bufferHead b ≤ k := by omega
          simp [h₁, h₂, hk]
    · simp [hc, Function.update_of_ne hc]

/-- One physical constant write and right move. -/
abbrev painted (d : TapeStore R B) (b : Fin B) (s : Sym) : TapeStore R B :=
  cellStore d b (fun _ => (s,.right))

/-- Repeated writes, used only as a data specification of the finite programs. -/
def fillStore (b : Fin B) (s : Sym) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d
  | n+1, d => fillStore b s n (painted d b s)

 theorem fillStore_reg (b : Fin B) (s : Sym) (n : ℕ) (d : TapeStore R B) :
    (fillStore b s n d).reg = d.reg := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => exact ih _

 theorem fillStore_roHead (b : Fin B) (s : Sym) (n : ℕ) (d : TapeStore R B) :
    (fillStore b s n d).roHead = d.roHead := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => exact ih _

 theorem fillStore_output (b : Fin B) (s : Sym) (n : ℕ) (d : TapeStore R B) :
    (fillStore b s n d).output = d.output := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => exact ih _

 theorem fillStore_head (b : Fin B) (s : Sym) (n : ℕ) (d : TapeStore R B) :
    (fillStore b s n d).bufferHead = Function.update d.bufferHead b (d.bufferHead b+n) := by
  induction n generalizing d with
  | zero => simp [fillStore]
  | succ n ih =>
    rw [fillStore, ih]
    simp [painted, cellStore, Machine.moveHead, Function.update_idem, Nat.add_assoc, Nat.add_comm]

 theorem fillStore_symbol (b : Fin B) (s : Sym) (n : ℕ) (d : TapeStore R B)
    (c : Fin B) (k : ℕ) :
    ((fillStore b s n d).bufferTape c).getD k .blank =
      if c = b ∧ d.bufferHead b ≤ k ∧ k < d.bufferHead b+n then s
      else (d.bufferTape c).getD k .blank := by
  induction n generalizing d with
  | zero =>
    simp only [fillStore, Nat.add_zero]
    split_ifs with hc
    · omega
    · rfl
  | succ n ih =>
    rw [fillStore, ih]
    simp only [painted, cellStore, Machine.moveHead, Function.update_self]
    by_cases hc : c = b
    · subst c
      simp only [Function.update_self, true_and, getD_writeAt]
      by_cases hk : k = d.bufferHead b
      · subst k
        simp
      · by_cases hl : d.bufferHead b < k
        · have h₂ : (d.bufferHead b+1 ≤ k ∧ k < d.bufferHead b+1+n) ↔
              (d.bufferHead b ≤ k ∧ k < d.bufferHead b+(n+1)) := by omega
          simp only [h₂, if_neg hk]
        · have h₁ : ¬ d.bufferHead b+1 ≤ k := by omega
          have h₂ : ¬ d.bufferHead b ≤ k := by omega
          simp [h₁, h₂, hk]
    · simp [hc, Function.update_of_ne hc]

/-- Write as many identical cells as the unary counter specifies. -/
def writeRun (r : Fin R) (b : Fin B) (s : Sym) : TapeProgram R B 3 where
  entry := 0
  code j := if j = 0 then .dec r 2 1 else if j = 1 then .buffer b (fun _ => (s,.right,0))
    else .halt

 theorem writeRun_stops (r : Fin R) (b : Fin B) (s : Sym) (inp : Inputs)
    (n : ℕ) (d : TapeStore R B) (hd : d.reg r = n) :
    (writeRun r b s).Stops inp (d.toCfg 0) (2*n+1)
      ((fillStore b s n (d.setReg r 0)).toCfg 2) := by
  induction n generalizing d with
  | zero =>
    have hc : d.setReg r 0 = d := by simp [TapeStore.setReg, ← hd]
    constructor
    · apply TapeProgram.Exec.one
      · simp [TapeProgram.halted, writeRun]
      · simp [TapeProgram.step, writeRun, TapeStore.toCfg, hd, fillStore, hc]
    · simp [TapeProgram.halted, writeRun]
  | succ n ih =>
    let d₁ := d.setReg r n
    let e := painted d₁ b s
    have he : e.reg r = n := by simp [e, d₁, painted, cellStore, TapeStore.setReg]
    have ht := ih e he
    have hs₁ : (writeRun r b s).step inp (d.toCfg 0) = d₁.toCfg 1 := by
      simp [TapeProgram.step, writeRun, TapeStore.toCfg, d₁, TapeStore.setReg, hd]
    have hs₂ : (writeRun r b s).step inp (d₁.toCfg 1) = e.toCfg 0 := by
      simp [TapeProgram.step, writeRun, TapeStore.toCfg, e, painted, cellStore]
    have hpost : e.setReg r 0 = painted (d.setReg r 0) b s := by
      simp [e, d₁, painted, cellStore, TapeStore.setReg, Function.update_idem]
    constructor
    · have h := TapeProgram.Exec.step (by simp [TapeProgram.halted, writeRun]) hs₁
        (TapeProgram.Exec.step (by simp [TapeProgram.halted, writeRun]) hs₂ ht.exec)
      simpa [hpost, fillStore, Nat.mul_succ, Nat.add_assoc] using h
    · exact ht.halted

/-- Each written cell additionally decrements a distinct width counter. The
width decrement saturates at zero, so the code has total semantics for all stores. -/
def writeDebit (value width : Fin R) (b : Fin B) (s : Sym) : TapeProgram R B 4 where
  entry := 0
  code j := if j = 0 then .dec value 3 1 else if j = 1 then .dec width 2 2
    else if j = 2 then .buffer b (fun _ => (s,.right,0)) else .halt

 theorem writeDebit_stops (value width : Fin R) (hne : value ≠ width) (b : Fin B)
    (s : Sym) (inp : Inputs) (n : ℕ) (d : TapeStore R B) (hd : d.reg value = n) :
    (writeDebit value width b s).Stops inp (d.toCfg 0) (3*n+1)
      ((fillStore b s n ((d.setReg value 0).setReg width (d.reg width-n))).toCfg 3) := by
  induction n generalizing d with
  | zero =>
    have hc : (d.setReg value 0).setReg width (d.reg width-0) = d := by
      have hv : d.setReg value 0 = d := by simp [TapeStore.setReg, ← hd]
      rw [hv]
      simp [TapeStore.setReg]
    constructor
    · apply TapeProgram.Exec.one
      · simp [TapeProgram.halted, writeDebit]
      · change (writeDebit value width b s).step inp (d.toCfg 0) =
          (((d.setReg value 0).setReg width (d.reg width-0)).toCfg 3)
        rw [hc]
        simp [TapeProgram.step, writeDebit, TapeStore.toCfg, hd]
    · simp [TapeProgram.halted, writeDebit]
  | succ n ih =>
    let d₁ := d.setReg value n
    let d₂ := d₁.setReg width (d.reg width-1)
    let e := painted d₂ b s
    have he : e.reg value = n := by simp [e, d₂, d₁, painted, cellStore, TapeStore.setReg, hne]
    have ht := ih e he
    have hs₁ : (writeDebit value width b s).step inp (d.toCfg 0) = d₁.toCfg 1 := by
      simp [TapeProgram.step, writeDebit, TapeStore.toCfg, d₁, TapeStore.setReg, hd]
    have hs₂ : (writeDebit value width b s).step inp (d₁.toCfg 1) = d₂.toCfg 2 := by
      simp only [TapeProgram.step, writeDebit, TapeStore.toCfg, show (1 : Fin 4) ≠ 0 by decide,
        if_false, if_true]
      split <;> simp_all [d₂, d₁, TapeStore.setReg, Function.update_of_ne (Ne.symm hne)]
    have hs₃ : (writeDebit value width b s).step inp (d₂.toCfg 2) = e.toCfg 0 := by
      simp [TapeProgram.step, writeDebit, TapeStore.toCfg, e, painted, cellStore]
    have hpost : (e.setReg value 0).setReg width (e.reg width-n) =
        painted ((d.setReg value 0).setReg width (d.reg width-(n+1))) b s := by
      simp only [e, d₂, d₁, painted, cellStore, TapeStore.setReg]
      congr 1
      funext j
      by_cases hw : j = width
      · subst j
        simp [Function.update, hne, Ne.symm hne, Nat.sub_sub, Nat.add_comm]
      · by_cases hv : j = value
        · subst j
          simp [Function.update, hne, Ne.symm hne]
        · simp [Function.update, hw, hv]
    constructor
    · have h := TapeProgram.Exec.step (by simp [TapeProgram.halted, writeDebit]) hs₁
        (TapeProgram.Exec.step (by simp [TapeProgram.halted, writeDebit]) hs₂
          (TapeProgram.Exec.step (by simp [TapeProgram.halted, writeDebit]) hs₃ ht.exec))
      rw [hpost] at h
      convert h using 1 <;> first | rfl | omega
    · exact ht.halted

/-- q-cell thermometer write: the first value cells are one, and the remaining
width-value cells are zero. Both unary input counters are consumed. -/
def writeBlock (value width : Fin R) (b : Fin B) : TapeProgram R B 7 :=
  TapeProgram.seq (writeDebit value width b .one) (writeRun width b .zero)

def writeBlockStore (value width : Fin R) (b : Fin B) (v w : ℕ) (d : TapeStore R B) : TapeStore R B :=
  fillStore b .zero (w-v) ((fillStore b .one v
    ((d.setReg value 0).setReg width (w-v))).setReg width 0)

 theorem writeBlock_stops (value width : Fin R) (hne : value ≠ width) (b : Fin B)
    (inp : Inputs) (v w : ℕ) (d : TapeStore R B) (hv : d.reg value = v)
    (hw : d.reg width = w) (hvw : v ≤ w) :
    ∃ e, (writeBlock value width b).Stops inp (d.toCfg (writeBlock (B := B) value width b).entry)
      (2*w+v+3) e ∧ e.store = writeBlockStore value width b v w d := by
  let d₁ := fillStore b .one v ((d.setReg value 0).setReg width (w-v))
  have h₁ := writeDebit_stops value width hne b .one inp v d hv
  have h₁' : (writeDebit value width b .one).Stops inp (d.toCfg 0) (3*v+1) (d₁.toCfg 3) := by
    simpa [d₁, hw] using h₁
  have hr : d₁.reg width = w-v := by simp [d₁, fillStore_reg, TapeStore.setReg]
  have h₂ := writeRun_stops width b .zero inp (w-v) d₁ hr
  have hall := h₁'.seq h₂
  refine ⟨((writeBlockStore value width b v w d).toCfg (2 : Fin 3)).mapPC (TapeProgram.rightLabel 4), ?_, rfl⟩
  · convert hall using 1 <;> first | rfl | omega

/-- One field/hash value occupies a fixed width of physical bit cells. -/
def ThermometerAt (d : TapeStore R B) (b : Fin B) (start width value : ℕ) : Prop :=
  value ≤ width ∧ ∀ j, j < width →
    (d.bufferTape b).getD (start+j) .blank = if j < value then .one else .zero

 theorem writeBlockStore_reg (value width : Fin R) (b : Fin B) (v w : ℕ) (d : TapeStore R B) :
    (writeBlockStore value width b v w d).reg =
      ((d.setReg value 0).setReg width 0).reg := by
  simp [writeBlockStore, fillStore_reg, TapeStore.setReg, Function.update_idem]

 theorem writeBlockStore_head (value width : Fin R) (b : Fin B) (v w : ℕ)
    (d : TapeStore R B) (hv : v ≤ w) :
    (writeBlockStore value width b v w d).bufferHead =
      Function.update d.bufferHead b (d.bufferHead b+w) := by
  have h : v+(w-v) = w := by omega
  simp [writeBlockStore, fillStore_head, TapeStore.setReg, Function.update_idem, Nat.add_assoc, h]

 theorem writeBlockStore_roHead (value width : Fin R) (b : Fin B) (v w : ℕ) (d : TapeStore R B) :
    (writeBlockStore value width b v w d).roHead = d.roHead := by
  simp [writeBlockStore, fillStore_roHead, TapeStore.setReg]

 theorem writeBlockStore_output (value width : Fin R) (b : Fin B) (v w : ℕ) (d : TapeStore R B) :
    (writeBlockStore value width b v w d).output = d.output := by
  simp [writeBlockStore, fillStore_output, TapeStore.setReg]

 theorem writeBlockStore_symbol (value width : Fin R) (b : Fin B) (v w : ℕ)
    (d : TapeStore R B) (hv : v ≤ w) (c : Fin B) (k : ℕ) :
    ((writeBlockStore value width b v w d).bufferTape c).getD k .blank =
      if c = b ∧ d.bufferHead b ≤ k ∧ k < d.bufferHead b+w then
        if k < d.bufferHead b+v then .one else .zero
      else (d.bufferTape c).getD k .blank := by
  simp only [writeBlockStore, fillStore_symbol, fillStore_head, TapeStore.setReg,
    Function.update_self]
  by_cases hc : c = b
  · subst c
    simp only [true_and]
    split_ifs <;> first | rfl | omega
  · simp [hc]

 theorem writeBlockStore_thermometer (value width : Fin R) (b : Fin B) (v w : ℕ)
    (d : TapeStore R B) (hv : v ≤ w) :
    ThermometerAt (writeBlockStore value width b v w d) b (d.bufferHead b) w v := by
  refine ⟨hv, ?_⟩
  intro j hj
  rw [writeBlockStore_symbol value width b v w d hv]
  have h₁ : d.bufferHead b ≤ d.bufferHead b+j := by omega
  have h₂ : d.bufferHead b+j < d.bufferHead b+w := by omega
  have h₃ : d.bufferHead b+j < d.bufferHead b+v ↔ j < v := by omega
  simp [h₁, h₂, h₃]

/-- Moving a preserving scanner one cell shifts a thermometer window and
removes one possible leading one. -/
 theorem ThermometerAt.tail {d e : TapeStore R B} {b : Fin B} {w v : ℕ}
    (h : ThermometerAt d b (d.bufferHead b) (w+1) v)
    (hp : TapeStore.SamePayload e d) (hh : e.bufferHead b = d.bufferHead b+1) :
    ThermometerAt e b (e.bufferHead b) w (v-1) := by
  refine ⟨by have := h.1; omega, ?_⟩
  intro j hj
  rw [hp.symbol, hh]
  have hk := h.2 (j+1) (by omega)
  have he : d.bufferHead b+1+j = d.bufferHead b+(j+1) := by omega
  rw [he, hk]
  have hi : j+1 < v ↔ j < v-1 := by omega
  simp only [hi]

/-- Read a fixed-width thermometer entry by explicitly scanning every cell and
incrementing the value counter once for each one. -/
def readBlock (width value : Fin R) (b : Fin B) : TapeProgram R B 4 where
  entry := 0
  code j := if j = 0 then .dec width 3 1
    else if j = 1 then .buffer b (fun s => (s,.right, if s = .one then 2 else 0))
    else if j = 2 then .inc value 0 else .halt

/-- Value added by the one scanned symbol in a read iteration. -/
def readDelta (d : TapeStore R B) (b : Fin B) : ℕ :=
  if (d.bufferTape b).getD (d.bufferHead b) .blank = .one then 1 else 0

def readTickStore (width value : Fin R) (b : Fin B) (d : TapeStore R B) : TapeStore R B :=
  let e := moved (TapeProgram.decStore width d) b .right
  if (d.bufferTape b).getD (d.bufferHead b) .blank = .one then
    e.setReg value (d.reg value+1) else e

 theorem readTick_payload (width value : Fin R) (b : Fin B) (d : TapeStore R B) :
    TapeStore.SamePayload (readTickStore width value b d) d := by
  have hp := (moved_payload (TapeProgram.decStore width d) b .right).trans
    (TapeStore.setReg_payload d width (d.reg width-1))
  unfold readTickStore
  split
  · exact (TapeStore.setReg_payload _ value (d.reg value+1)).trans hp
  · exact hp

 theorem readTick_head (width value : Fin R) (b : Fin B) (d : TapeStore R B) :
    (readTickStore width value b d).bufferHead =
      Function.update d.bufferHead b (d.bufferHead b+1) := by
  unfold readTickStore
  split <;> rfl

 theorem readTick_reg (width value : Fin R) (hne : width ≠ value) (b : Fin B) (d : TapeStore R B) :
    (readTickStore width value b d).reg =
      Function.update (Function.update d.reg width (d.reg width-1)) value
        (d.reg value + readDelta d b) := by
  unfold readTickStore readDelta
  split
  · rfl
  · simp [TapeStore.setReg, moved, cellStore, TapeProgram.decStore,
      Function.update_of_ne (Ne.symm hne)]

 theorem readTick_exec (width value : Fin R) (hne : width ≠ value) (b : Fin B)
    (inp : Inputs) (d : TapeStore R B) (hd : d.reg width ≠ 0) :
    (readBlock width value b).Exec inp (d.toCfg 0) (2+readDelta d b)
      ((readTickStore width value b d).toCfg 0) := by
  let d₁ := TapeProgram.decStore width d
  let d₂ := moved d₁ b .right
  have hs₁ : (readBlock width value b).step inp (d.toCfg 0) = d₁.toCfg 1 := by
    simp [TapeProgram.step, readBlock, TapeStore.toCfg, hd, d₁, TapeProgram.decStore]
  by_cases hs : (d.bufferTape b).getD (d.bufferHead b) .blank = .one
  · have hs' := hs
    change ((d.bufferTape b)[d.bufferHead b]?).getD .blank = .one at hs'
    have hs₂ : (readBlock width value b).step inp (d₁.toCfg 1) = d₂.toCfg 2 := by
      simp [TapeProgram.step, readBlock, TapeStore.toCfg, d₂, d₁, TapeProgram.decStore,
        moved, cellStore, hs']
    have hs₃ : (readBlock width value b).step inp (d₂.toCfg 2) =
        (readTickStore width value b d).toCfg 0 := by
      simp [TapeProgram.step, readBlock, TapeStore.toCfg, readTickStore, hs', d₂, d₁,
        moved, cellStore, TapeStore.setReg, TapeProgram.decStore, Function.update_of_ne (Ne.symm hne)]
    have h := TapeProgram.Exec.step (by simp [TapeProgram.halted, readBlock]) hs₁
      (TapeProgram.Exec.step (by simp [TapeProgram.halted, readBlock]) hs₂
        (TapeProgram.Exec.one (by simp [TapeProgram.halted, readBlock]) hs₃))
    simpa only [readDelta, if_pos hs] using h
  · have hs' := hs
    change ((d.bufferTape b)[d.bufferHead b]?).getD .blank ≠ .one at hs'
    have hs₂ : (readBlock width value b).step inp (d₁.toCfg 1) =
        (readTickStore width value b d).toCfg 0 := by
      simp [TapeProgram.step, readBlock, TapeStore.toCfg, readTickStore, hs, d₁,
        TapeProgram.decStore, moved, cellStore, hs']
    have h := TapeProgram.Exec.step (by simp [TapeProgram.halted, readBlock]) hs₁
      (TapeProgram.Exec.one (by simp [TapeProgram.halted, readBlock]) hs₂)
    simpa only [readDelta, if_neg hs] using h

 theorem readBlock_stops (width value : Fin R) (hne : width ≠ value) (b : Fin B)
    (inp : Inputs) (w v : ℕ) (d : TapeStore R B) (hw : d.reg width = w)
    (ht : ThermometerAt d b (d.bufferHead b) w v) :
    ∃ e, (readBlock width value b).Stops inp (d.toCfg 0) (2*w+v+1) (e.toCfg 3) ∧
      e.reg = Function.update (Function.update d.reg width 0) value (d.reg value+v) ∧
      e.bufferHead = Function.update d.bufferHead b (d.bufferHead b+w) ∧
      TapeStore.SamePayload e d := by
  induction w generalizing d v with
  | zero =>
    have hv : v = 0 := by have := ht.1; omega
    refine ⟨d, ?_, ?_, ?_, TapeStore.SamePayload.refl d⟩
    · constructor
      · simpa [hv] using TapeProgram.Exec.one
          (by simp [TapeProgram.halted, readBlock])
          (show (readBlock width value b).step inp (d.toCfg 0) = d.toCfg 3 by
            simp [TapeProgram.step, readBlock, TapeStore.toCfg, hw])
      · simp [TapeProgram.halted, readBlock]
    · rw [show Function.update d.reg width 0 = d.reg by simp [← hw]]
      simp [hv]
    · simp
  | succ w ih =>
    let d₁ := readTickStore width value b d
    have hd₁ : d₁.reg width = w := by
      rw [readTick_reg width value hne]
      simp [Function.update_of_ne hne, hw]
    have hh : d₁.bufferHead b = d.bufferHead b+1 := by
      rw [readTick_head]
      simp
    have hp := readTick_payload width value b d
    have ht₁ := ht.tail hp hh
    obtain ⟨e, he, her, heh, hep⟩ := ih (v-1) d₁ hd₁ ht₁
    have hδ : readDelta d b+(v-1) = v := by
      have hfirst := ht.2 0 (by omega)
      simp only [Nat.add_zero] at hfirst
      cases v with
      | zero => simp only [readDelta, hfirst, Nat.lt_irrefl, if_false, Nat.zero_sub, Nat.add_zero]; decide
      | succ v => simp only [readDelta, hfirst, Nat.zero_lt_succ, if_true, Nat.add_sub_cancel]; omega
    refine ⟨e, ?_, ?_, ?_, hep.trans hp⟩
    · constructor
      · have hprefix := readTick_exec width value hne b inp d (by omega)
        have h := hprefix.trans he.exec
        convert h using 1 <;> first | rfl | omega
      · exact he.halted
    · rw [her, readTick_reg width value hne]
      funext j
      by_cases hv : j = value
      · subst j
        simp only [Function.update_self]
        omega
      · by_cases hw' : j = width
        · subst j
          simp [Function.update, hne, Ne.symm hne]
        · simp [Function.update, hv, hw']
    · rw [heh, readTick_head]
      simp [Function.update_idem, Nat.add_assoc, Nat.add_comm]

/-- Physical entries begin after the reserved bottom marker. The offset is an
individual bounded unary register; construction of 1+i*width is charged separately. -/
def entryOffset (i width : ℕ) : ℕ := 1+i*width

/-- Reset and then traverse exactly the supplied unary offset. -/
def seekEntry (offset : Fin R) (b : Fin B) : TapeProgram R B 5 :=
  TapeProgram.seq (reset b) (seekRight offset b)

 theorem seekEntry_stops (offset : Fin R) (b : Fin B) (inp : Inputs)
    (i w : ℕ) (d : TapeStore R B) (ho : d.reg offset = entryOffset i w)
    (hm : Marked d b) :
    ∃ e, (seekEntry offset b).Stops inp (d.toCfg (seekEntry (R := R) offset b).entry)
      (d.bufferHead b+2*entryOffset i w+3) e ∧
      e.reg = Function.update d.reg offset 0 ∧
      e.bufferHead = Function.update d.bufferHead b (entryOffset i w) ∧
      TapeStore.SamePayload e.store d := by
  obtain ⟨d₁, h₁, hr₁, hh₁, hp₁⟩ := reset_stops b inp (d.bufferHead b) d rfl hm
  have ho₁ : d₁.reg offset = entryOffset i w := by rw [hr₁]; exact ho
  obtain ⟨e, h₂, hr₂, hh₂, hp₂⟩ := seekRight_stops offset b inp (entryOffset i w) d₁ ho₁
  have hall := h₁.seq h₂
  refine ⟨(e.toCfg (2 : Fin 3)).mapPC (TapeProgram.rightLabel 2), ?_, ?_, ?_, hp₂.trans hp₁⟩
  · convert hall using 1 <;> first | rfl | omega
  · simpa [hr₁] using hr₂
  · change e.bufferHead = _
    rw [hh₂, hh₁]
    simp [Function.update_idem]

/-- A table is physically present in successive fixed-width bit blocks. This
is a specification over explicit buffer cells, not a new array instruction. -/
def ThermometerTable {N : ℕ} (d : TapeStore R B) (b : Fin B) (width : ℕ)
    (values : Fin N → ℕ) : Prop :=
  ∀ i, ThermometerAt d b (entryOffset i.val width) width (values i)

 theorem ThermometerAt.of_payload {d e : TapeStore R B} {b : Fin B} {start w v : ℕ}
    (h : ThermometerAt d b start w v) (hp : TapeStore.SamePayload e d) :
    ThermometerAt e b start w v := by
  refine ⟨h.1, ?_⟩
  intro j hj
  rw [hp.symbol]
  exact h.2 j hj

/-- Full physical indexing: multiply individual index/width counters, add the
marker offset, reset, and traverse. There is no uncharged random-access operation. -/
def positionEntry (index width offset tmp count : Fin R) (b : Fin B) : TapeProgram R B 31 :=
  TapeProgram.seq (TapeProgram.seq
    (UnaryArithmetic.multiply index width offset tmp count) (TapeMacros.increment offset))
    (seekEntry offset b)

 theorem positionEntry_stops (index width offset tmp count : Fin R)
    (hio : index ≠ offset) (hit : index ≠ tmp) (hic : index ≠ count)
    (hwo : width ≠ offset) (hwt : width ≠ tmp) (hwc : width ≠ count)
    (hot : offset ≠ tmp) (hoc : offset ≠ count) (htc : tmp ≠ count)
    (b : Fin B) (inp : Inputs) (d : TapeStore R B) (hm : Marked d b) :
    ∃ t e, t ≤ d.reg offset+d.reg count+d.reg tmp+5*d.reg width+
        d.reg width*(5*d.reg index+7)+11 + d.bufferHead b+
        2*entryOffset (d.reg index) (d.reg width)+6 ∧
      (positionEntry index width offset tmp count b).Stops inp
        (d.toCfg (positionEntry index width offset tmp count b).entry) t e ∧
      e.reg = (((d.setReg offset 0).setReg tmp 0).setReg count 0).reg ∧
      e.bufferHead = Function.update d.bufferHead b (entryOffset (d.reg index) (d.reg width)) ∧
      TapeStore.SamePayload e.store d := by
  obtain ⟨t, c, ht, hc, hcs⟩ := UnaryArithmetic.multiply_stops index width offset tmp count
    hio hit hic hwo hwt hwc hot hoc htc inp d
  have ho : c.reg offset = d.reg index*d.reg width := by
    change c.store.reg offset = _
    rw [hcs]
    simp [UnaryArithmetic.multiplyStore, TapeStore.setReg, hot, hoc]
  let d₂ := c.store.setReg offset (c.reg offset+1)
  have hinc := TapeMacros.increment_stops offset inp c.store
  have ho₂ : d₂.reg offset = entryOffset (d.reg index) (d.reg width) := by
    simp [d₂, TapeStore.setReg, ho, entryOffset, Nat.add_comm]
  have hheads : d₂.bufferHead = d.bufferHead := by
    change c.store.bufferHead = d.bufferHead
    rw [hcs]
    rfl
  have hpMul : TapeStore.SamePayload c.store d := by
    rw [hcs]
    exact (TapeStore.setReg_payload _ count 0).trans
      ((TapeStore.setReg_payload _ tmp 0).trans
        (TapeStore.setReg_payload d offset (d.reg index*d.reg width)))
  have hp₂ : TapeStore.SamePayload d₂ d :=
    (TapeStore.setReg_payload c.store offset (c.reg offset+1)).trans hpMul
  have hm₂ : Marked d₂ b := by
    constructor
    · rw [hp₂.symbol]
      exact hm.1
    · intro k hk hkh
      rw [hp₂.symbol]
      exact hm.2 k hk (by simpa [hheads] using hkh)
  obtain ⟨e, hseek, her, heh, hep⟩ := seekEntry_stops offset b inp
    (d.reg index) (d.reg width) d₂ ho₂ hm₂
  have hall := (hc.seq hinc).seq hseek
  refine ⟨(t+1+1)+1+(d₂.bufferHead b+2*entryOffset (d.reg index) (d.reg width)+3),
    e.mapPC (TapeProgram.rightLabel 26), ?_, ?_, ?_, ?_, hep.trans hp₂⟩
  · rw [hheads]
    omega
  · convert hall using 1 <;> rfl
  · change e.reg = _
    rw [her]
    change Function.update d₂.reg offset 0 = _
    simp only [d₂, TapeStore.setReg, Function.update_idem]
    change Function.update c.store.reg offset 0 = _
    rw [hcs]
    simp only [UnaryArithmetic.multiplyStore, TapeStore.setReg]
    funext j
    by_cases ho' : j = offset
    · subst j
      simp [Function.update, hot, hoc, htc]
    · by_cases ht' : j = tmp
      · subst j
        simp [Function.update, hot, hoc, htc, Ne.symm hot, Ne.symm hoc, Ne.symm htc]
      · by_cases hc' : j = count
        · subst j
          simp [Function.update, hot, hoc, htc, Ne.symm hot, Ne.symm hoc, Ne.symm htc]
        · simp [Function.update, ho', ht', hc']
  · simpa [hheads] using heh

 theorem positionEntry_stops_polynomial (index width offset tmp count : Fin R)
    (hio : index ≠ offset) (hit : index ≠ tmp) (hic : index ≠ count)
    (hwo : width ≠ offset) (hwt : width ≠ tmp) (hwc : width ≠ count)
    (hot : offset ≠ tmp) (hoc : offset ≠ count) (htc : tmp ≠ count)
    (b : Fin B) (inp : Inputs) (M : ℕ) (d : TapeStore R B) (hm : Marked d b)
    (hi : d.reg index ≤ M) (hw : d.reg width ≤ M) (ho : d.reg offset ≤ M)
    (ht : d.reg tmp ≤ M) (hc : d.reg count ≤ M) (hh : d.bufferHead b ≤ M) :
    ∃ t e, t ≤ 40*(M+1)^2 ∧
      (positionEntry index width offset tmp count b).Stops inp
        (d.toCfg (positionEntry index width offset tmp count b).entry) t e ∧
      e.reg = (((d.setReg offset 0).setReg tmp 0).setReg count 0).reg ∧
      e.bufferHead = Function.update d.bufferHead b (entryOffset (d.reg index) (d.reg width)) ∧
      TapeStore.SamePayload e.store d := by
  obtain ⟨t, e, htime, hstop, her, heh, hep⟩ := positionEntry_stops index width offset tmp count
    hio hit hic hwo hwt hwc hot hoc htc b inp d hm
  refine ⟨t, e, ?_, hstop, her, heh, hep⟩
  have hp : d.reg index*d.reg width ≤ M*M := Nat.mul_le_mul hi hw
  have hq : d.reg width*(5*d.reg index+7) ≤ M*(5*M+7) :=
    Nat.mul_le_mul hw (by omega)
  unfold entryOffset at htime
  nlinarith

/-- Proved source-step budget for multiplication, marker offset and charged seek. -/
def positionBound (d : TapeStore R B) (index width offset tmp count : Fin R) (b : Fin B) : ℕ :=
  d.reg offset+d.reg count+d.reg tmp+5*d.reg width+
    d.reg width*(5*d.reg index+7)+11+d.bufferHead b+
    2*entryOffset (d.reg index) (d.reg width)+6

/-- A common loose budget for either complete indexed read or indexed write. -/
def entryAccessBound (d : TapeStore R B) (index width offset tmp count : Fin R) (b : Fin B) : ℕ :=
  positionBound d index width offset tmp count b+3*d.reg width+4

 theorem entryAccessBound_le (d : TapeStore R B) (index width offset tmp count : Fin R)
    (b : Fin B) (M : ℕ) (hi : d.reg index ≤ M) (hw : d.reg width ≤ M)
    (ho : d.reg offset ≤ M) (ht : d.reg tmp ≤ M) (hc : d.reg count ≤ M)
    (hh : d.bufferHead b ≤ M) : entryAccessBound d index width offset tmp count b ≤ 50*(M+1)^2 := by
  have hp : d.reg index*d.reg width ≤ M*M := Nat.mul_le_mul hi hw
  have hq : d.reg width*(5*d.reg index+7) ≤ M*(5*M+7) :=
    Nat.mul_le_mul hw (by omega)
  unfold entryAccessBound positionBound entryOffset
  nlinarith

/-- A complete physical array read. The width register is consumed and the
value accumulator must start at zero; every indexed traversal is real code. -/
def readEntry (index width offset tmp count value : Fin R) (b : Fin B) : TapeProgram R B 35 :=
  TapeProgram.seq (positionEntry index width offset tmp count b) (readBlock width value b)

 theorem readEntry_stops (index width offset tmp count value : Fin R)
    (hio : index ≠ offset) (hit : index ≠ tmp) (hic : index ≠ count)
    (hwo : width ≠ offset) (hwt : width ≠ tmp) (hwc : width ≠ count)
    (hot : offset ≠ tmp) (hoc : offset ≠ count) (htc : tmp ≠ count)
    (hwv : width ≠ value) (hvo : value ≠ offset) (hvt : value ≠ tmp) (hvc : value ≠ count)
    (b : Fin B) (inp : Inputs) (d : TapeStore R B) (hm : Marked d b)
    (hv : d.reg value = 0) (v : ℕ)
    (hblock : ThermometerAt d b (entryOffset (d.reg index) (d.reg width)) (d.reg width) v) :
    ∃ t e, t ≤ entryAccessBound d index width offset tmp count b ∧
      (readEntry index width offset tmp count value b).Stops inp
        (d.toCfg (readEntry index width offset tmp count value b).entry) t e ∧
      e.reg = Function.update (Function.update
        (((d.setReg offset 0).setReg tmp 0).setReg count 0).reg width 0) value v ∧
      e.bufferHead = Function.update d.bufferHead b
        (entryOffset (d.reg index) (d.reg width)+d.reg width) ∧
      TapeStore.SamePayload e.store d := by
  obtain ⟨t, c, ht, hc, hcr, hch, hcp⟩ := positionEntry_stops index width offset tmp count
    hio hit hic hwo hwt hwc hot hoc htc b inp d hm
  have hcwidth : c.reg width = d.reg width := by
    rw [hcr]
    simp [TapeStore.setReg, hwo, hwt, hwc]
  have hcvalue : c.reg value = 0 := by
    rw [hcr]
    simp [TapeStore.setReg, hvo, hvt, hvc, hv]
  have hchead : c.bufferHead b = entryOffset (d.reg index) (d.reg width) := by
    rw [hch]
    simp
  have hct : ThermometerAt c.store b (c.bufferHead b) (d.reg width) v := by
    rw [hchead]
    exact hblock.of_payload hcp
  obtain ⟨e, he, her, heh, hep⟩ := readBlock_stops width value hwv b inp
    (d.reg width) v c.store hcwidth hct
  have hall := hc.seq he
  refine ⟨t+1+(2*d.reg width+v+1), (e.toCfg (3 : Fin 4)).mapPC (TapeProgram.rightLabel 31),
    ?_, ?_, ?_, ?_, hep.trans hcp⟩
  · have := hblock.1
    change t ≤ positionBound d index width offset tmp count b at ht
    unfold entryAccessBound
    omega
  · convert hall using 1 <;> rfl
  · change e.reg = _
    simpa [hcr, hcvalue] using her
  · change e.bufferHead = _
    rw [heh]
    change Function.update c.bufferHead b (c.bufferHead b+d.reg width) = _
    rw [hch]
    simp [Function.update_idem]

/-- Complete extensional effect of one physical field/hash entry overwrite. -/
structure EntryWritten (d e : TapeStore R B) (b : Fin B) (start width value : ℕ) : Prop where
  roHead : e.roHead = d.roHead
  output : e.output = d.output
  head : e.bufferHead = Function.update d.bufferHead b (start+width)
  symbol : ∀ c k, (e.bufferTape c).getD k .blank =
    if c = b ∧ start ≤ k ∧ k < start+width then
      if k < start+value then .one else .zero
    else (d.bufferTape c).getD k .blank

/-- A complete physical indexed array write, including offset multiplication. -/
def writeEntry (index width offset tmp count value : Fin R) (b : Fin B) : TapeProgram R B 38 :=
  TapeProgram.seq (positionEntry index width offset tmp count b) (writeBlock value width b)

 theorem writeEntry_stops (index width offset tmp count value : Fin R)
    (hio : index ≠ offset) (hit : index ≠ tmp) (hic : index ≠ count)
    (hwo : width ≠ offset) (hwt : width ≠ tmp) (hwc : width ≠ count)
    (hot : offset ≠ tmp) (hoc : offset ≠ count) (htc : tmp ≠ count)
    (hvw : value ≠ width) (hvo : value ≠ offset) (hvt : value ≠ tmp) (hvc : value ≠ count)
    (b : Fin B) (inp : Inputs) (d : TapeStore R B) (hm : Marked d b)
    (hv : d.reg value ≤ d.reg width) :
    ∃ t e, t ≤ entryAccessBound d index width offset tmp count b ∧
      (writeEntry index width offset tmp count value b).Stops inp
        (d.toCfg (writeEntry index width offset tmp count value b).entry) t e ∧
      e.reg = (((((d.setReg offset 0).setReg tmp 0).setReg count 0).setReg value 0).setReg width 0).reg ∧
      EntryWritten d e.store b (entryOffset (d.reg index) (d.reg width)) (d.reg width) (d.reg value) := by
  obtain ⟨t, c, ht, hc, hcr, hch, hcp⟩ := positionEntry_stops index width offset tmp count
    hio hit hic hwo hwt hwc hot hoc htc b inp d hm
  have hcwidth : c.reg width = d.reg width := by
    rw [hcr]
    simp [TapeStore.setReg, hwo, hwt, hwc]
  have hcvalue : c.reg value = d.reg value := by
    rw [hcr]
    simp [TapeStore.setReg, hvo, hvt, hvc]
  have hchead : c.bufferHead b = entryOffset (d.reg index) (d.reg width) := by
    rw [hch]
    simp
  obtain ⟨e, he, hes⟩ := writeBlock_stops value width hvw b inp
    (d.reg value) (d.reg width) c.store hcvalue hcwidth hv
  have hall := hc.seq he
  refine ⟨t+1+(2*d.reg width+d.reg value+3), e.mapPC (TapeProgram.rightLabel 31), ?_, ?_, ?_, ?_⟩
  · change t ≤ positionBound d index width offset tmp count b at ht
    unfold entryAccessBound
    omega
  · convert hall using 1 <;> rfl
  · change e.store.reg = _
    rw [hes, writeBlockStore_reg]
    change Function.update (Function.update c.reg value 0) width 0 = _
    rw [hcr]
    rfl
  · change EntryWritten d e.store b _ _ _
    rw [hes]
    constructor
    · rw [writeBlockStore_roHead]
      exact hcp.roHead
    · rw [writeBlockStore_output]
      exact hcp.output
    · rw [writeBlockStore_head value width b (d.reg value) (d.reg width) c.store hv]
      change Function.update c.bufferHead b (c.bufferHead b+d.reg width) = _
      rw [hch]
      simp [Function.update_idem]
    · intro f k
      rw [writeBlockStore_symbol value width b (d.reg value) (d.reg width) c.store hv]
      have hcsh : c.store.bufferHead b = entryOffset (d.reg index) (d.reg width) := hchead
      rw [hcsh, hcp.symbol]

/-- A reserved bottom marker with no other bottom symbols on this buffer. This
invariant permits reset after arbitrary indexed reads and thermometer writes. -/
def BottomMarked (d : TapeStore R B) (b : Fin B) : Prop :=
  (d.bufferTape b).getD 0 .blank = .bot ∧
    ∀ k, 0 < k → (d.bufferTape b).getD k .blank ≠ .bot

 theorem BottomMarked.marked {d : TapeStore R B} {b : Fin B} (h : BottomMarked d b) :
    Marked d b := ⟨h.1, fun k hk _ => h.2 k hk⟩

 theorem BottomMarked.of_payload {d e : TapeStore R B} {b : Fin B}
    (h : BottomMarked d b) (hp : TapeStore.SamePayload e d) : BottomMarked e b := by
  constructor
  · rw [hp.symbol]
    exact h.1
  · intro k hk
    rw [hp.symbol]
    exact h.2 k hk

 theorem EntryWritten.bottomMarked {d e : TapeStore R B} {b : Fin B} {start w v : ℕ}
    (h : EntryWritten d e b start w v) (hs : 0 < start) (hm : BottomMarked d b) :
    BottomMarked e b := by
  constructor
  · rw [h.symbol]
    have hn : ¬ start ≤ 0 := by omega
    have hout : ¬(b = b ∧ start ≤ 0 ∧ 0 < start+w) := by omega
    rw [if_neg hout]
    exact hm.1
  · intro k hk
    rw [h.symbol]
    split_ifs <;> first | decide | exact hm.2 k hk

/-- Install the reserved marker using one actual cell write. -/
def initializeBuffer (b : Fin B) : TapeProgram R B 2 := TapeMacros.write b .bot .right

 theorem initializeBuffer_stops (b : Fin B) (inp : Inputs) (d : TapeStore R B)
    (hh : d.bufferHead b = 0) (hb : ∀ k, (d.bufferTape b).getD k .blank = .blank) :
    ∃ e, (initializeBuffer b).Stops inp (d.toCfg 0) 1 (e.toCfg 1) ∧
      e.reg = d.reg ∧ e.roHead = d.roHead ∧ e.output = d.output ∧
      e.bufferHead = Function.update d.bufferHead b 1 ∧ BottomMarked e b := by
  let e := painted d b .bot
  refine ⟨e, cell_stops b (fun _ => (.bot,.right)) inp d, rfl, rfl, rfl, ?_, ?_⟩
  · simp [e, painted, cellStore, hh, Machine.moveHead]
  · constructor
    · simp only [e, painted, cellStore, Function.update_self, hh, getD_writeAt, if_pos rfl, if_true]
    · intro k hk
      simp only [e, painted, cellStore, Function.update_self, hh, getD_writeAt]
      rw [if_neg (by omega : k ≠ 0), hb k]
      decide

/-- A checked physical overwrite updates exactly one logical table entry. -/
 theorem EntryWritten.table {N : ℕ} {d e : TapeStore R B} {b : Fin B} {w v : ℕ}
    {a : Fin N → ℕ} {i : Fin N}
    (h : EntryWritten d e b (entryOffset i.val w) w v) (hv : v ≤ w)
    (ht : ThermometerTable d b w a) :
    ThermometerTable e b w (Function.update a i v) := by
  intro j
  by_cases hji : j = i
  · subst j
    refine ⟨by simpa using hv, ?_⟩
    intro k hk
    rw [h.symbol]
    have h₁ : entryOffset i.val w ≤ entryOffset i.val w+k := by omega
    have h₂ : entryOffset i.val w+k < entryOffset i.val w+w := by omega
    have h₃ : entryOffset i.val w+k < entryOffset i.val w+v ↔ k < v := by omega
    simp [h₁, h₂, h₃]
  · refine ⟨?_, ?_⟩
    · simpa [Function.update_of_ne hji] using (ht j).1
    · intro k hk
      rw [h.symbol]
      have hne : j.val ≠ i.val := by intro he; exact hji (Fin.ext he)
      have hn : ¬(entryOffset i.val w ≤ entryOffset j.val w+k ∧
          entryOffset j.val w+k < entryOffset i.val w+w) := by
        intro hoverlap
        unfold entryOffset at hoverlap
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hle : (j.val+1)*w ≤ i.val*w := Nat.mul_le_mul_right w (by omega)
          nlinarith
        · have hle : (i.val+1)*w ≤ j.val*w := Nat.mul_le_mul_right w (by omega)
          nlinarith
      simp only [true_and, if_neg hn, Function.update_of_ne hji]
      exact (ht j).2 k hk

#print axioms seekRight_stops
#print axioms reset_stops
#print axioms copyCell_stops
end TapeArrays
end ExpandingCodes.Computation

#print axioms ExpandingCodes.Computation.TapeArrays.copyCells_stops

#print axioms ExpandingCodes.Computation.TapeArrays.copyCellsStore_symbol

#print axioms ExpandingCodes.Computation.TapeArrays.writeBlock_stops

#print axioms ExpandingCodes.Computation.TapeArrays.readBlock_stops
#print axioms ExpandingCodes.Computation.TapeArrays.writeBlockStore_thermometer

#print axioms ExpandingCodes.Computation.TapeArrays.seekEntry_stops

#print axioms ExpandingCodes.Computation.TapeArrays.positionEntry_stops_polynomial

#print axioms ExpandingCodes.Computation.TapeArrays.readEntry_stops
#print axioms ExpandingCodes.Computation.TapeArrays.writeEntry_stops
#print axioms ExpandingCodes.Computation.TapeArrays.entryAccessBound_le

#print axioms ExpandingCodes.Computation.TapeArrays.initializeBuffer_stops
#print axioms ExpandingCodes.Computation.TapeArrays.EntryWritten.table
