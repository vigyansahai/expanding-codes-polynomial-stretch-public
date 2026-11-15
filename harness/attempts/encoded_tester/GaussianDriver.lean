import ExpandingCodes.Computation.GaussianGrid
import ExpandingCodes.Computation.GaussianPivot
import ExpandingCodes.Computation.PaddedGaussian

set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianDriver

open NKtLB GaussianProgram GaussianGrid

section Branch
variable {R B L K : ℕ}

def zeroLabel (K : ℕ) (j : Fin L) : Fin ((L+K)+2) :=
  TapeProgram.leftLabel 2 (TapeProgram.leftLabel K j)
def positiveLabel (L : ℕ) (j : Fin K) : Fin ((L+K)+2) :=
  TapeProgram.leftLabel 2 (TapeProgram.rightLabel L j)
def branchLabel (L K : ℕ) (j : Fin 2) : Fin ((L+K)+2) := TapeProgram.rightLabel (L+K) j

/-- A real preserving zero/positive branch. The positive path decrements and
restores the tested unary counter before entering its finite program. -/
def branchZero (P : TapeProgram R B L) (Q : TapeProgram R B K) (r : Fin R) :
    TapeProgram R B ((L+K)+2) where
  entry := branchLabel L K 0
  code j := match finSumFinEquiv.symm j with
    | .inl a => match finSumFinEquiv.symm a with
      | .inl i => (P.code i).relabel (zeroLabel K)
      | .inr i => (Q.code i).relabel (positiveLabel L)
    | .inr k => if k = 0 then .dec r (zeroLabel K P.entry) (branchLabel L K 1)
      else .inc r (positiveLabel L Q.entry)

@[simp] theorem branchZero_code_zero (P : TapeProgram R B L) (Q : TapeProgram R B K) (r : Fin R) (j : Fin L) :
    (branchZero P Q r).code (zeroLabel K j) = (P.code j).relabel (zeroLabel K) := by
  simp [branchZero,zeroLabel,TapeProgram.leftLabel]

@[simp] theorem branchZero_code_positive (P : TapeProgram R B L) (Q : TapeProgram R B K) (r : Fin R) (j : Fin K) :
    (branchZero P Q r).code (positiveLabel L j) = (Q.code j).relabel (positiveLabel L) := by
  simp [branchZero,positiveLabel,TapeProgram.leftLabel,TapeProgram.rightLabel]

@[simp] theorem branchZero_code_header (P : TapeProgram R B L) (Q : TapeProgram R B K) (r : Fin R) (j : Fin 2) :
    (branchZero P Q r).code (branchLabel L K j) =
      if j = 0 then .dec r (zeroLabel K P.entry) (branchLabel L K 1)
      else .inc r (positiveLabel L Q.entry) := by
  simp [branchZero,branchLabel,TapeProgram.rightLabel]

theorem branchZero_stops_zero (P : TapeProgram R B L) (Q : TapeProgram R B K) (r : Fin R)
    (inp : Inputs) (d : TapeStore R B) (hr : d.reg r = 0) (t : ℕ) (e : TapeCfg R B L)
    (he : P.Stops inp (d.toCfg P.entry) t e) :
    (branchZero P Q r).Stops inp (d.toCfg (branchZero P Q r).entry) (t+1) (e.mapPC (zeroLabel K)) := by
  have hh : (branchZero P Q r).Exec inp (d.toCfg (branchLabel L K 0)) 1
      (d.toCfg (zeroLabel K P.entry)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted]
    · simp [TapeProgram.step,TapeStore.toCfg,hr]
  have hb := he.exec.relabel (zeroLabel K) (fun j _ => branchZero_code_zero P Q r j)
  constructor
  · convert hh.trans hb using 1 <;> first | rfl | omega
  · change (branchZero P Q r).code (zeroLabel K e.pc) = .halt
    rw [branchZero_code_zero,he.halted]
    rfl

theorem branchZero_stops_positive (P : TapeProgram R B L) (Q : TapeProgram R B K) (r : Fin R)
    (inp : Inputs) (d : TapeStore R B) (hr : 0 < d.reg r) (t : ℕ) (e : TapeCfg R B K)
    (he : Q.Stops inp (d.toCfg Q.entry) t e) :
    (branchZero P Q r).Stops inp (d.toCfg (branchZero P Q r).entry) (t+2) (e.mapPC (positiveLabel L)) := by
  let d₁ := d.setReg r (d.reg r-1)
  have hh : (branchZero P Q r).Exec inp (d.toCfg (branchLabel L K 0)) 1
      (d₁.toCfg (branchLabel L K 1)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted]
    · simp [TapeProgram.step,TapeStore.toCfg,d₁,TapeStore.setReg,Nat.ne_of_gt hr]
  have hrestore : (branchZero P Q r).Exec inp (d₁.toCfg (branchLabel L K 1)) 1
      (d.toCfg (positiveLabel L Q.entry)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted]
    · simp [TapeProgram.step,TapeStore.toCfg,d₁,TapeStore.setReg,Function.update_idem,Nat.sub_add_cancel hr]
  have hb := he.exec.relabel (positiveLabel L) (fun j _ => branchZero_code_positive P Q r j)
  constructor
  · convert (hh.trans hrestore).trans hb using 1 <;> first | rfl | omega
  · change (branchZero P Q r).code (positiveLabel L e.pc) = .halt
    rw [branchZero_code_positive,he.halted]
    rfl

end Branch

def skip : TapeProgram 64 2 1 where
  entry := 0
  code _ := .halt

theorem skip_stops (inp : Inputs) (d : Store) : skip.Stops inp (d.toCfg 0) 0 (d.toCfg 0) :=
  ⟨TapeProgram.Exec.refl _,rfl⟩

def scanSetup : TapeProgram 64 2 17 :=
  TapeProgram.seq (TapeMacros.clear 2)
    (TapeProgram.seq (TapeMacros.clear 6) (TapeProgram.seq (TapeMacros.clear 8) (TapeMacros.copy 51 7 63)))

def inputBuffer (b : Bool) : Fin 2 := if b then 1 else 0
def outputBuffer (b : Bool) : Fin 2 := if b then 0 else 1
def bit (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem inputBuffer_not (b : Bool) : inputBuffer (!b) = outputBuffer b := by cases b <;> rfl
@[simp] theorem outputBuffer_not (b : Bool) : outputBuffer (!b) = inputBuffer b := by cases b <;> rfl
theorem buffers_ne (b : Bool) : outputBuffer b ≠ inputBuffer b := by cases b <;> decide

def flip (b : Bool) : TapeProgram 64 2 2 := if b then TapeMacros.clear 60 else TapeMacros.increment 60

def afterPivot (b : Bool) : TapeProgram 64 2 2043 :=
  TapeProgram.seq GaussianPivot.preparePivot
    (TapeProgram.seq (materializeGrid (inputBuffer b) (outputBuffer b))
      (TapeProgram.seq (TapeMacros.increment 48) (flip b)))

def afterPivot₀ : TapeProgram 64 2 2043 := afterPivot false
def afterPivot₁ : TapeProgram 64 2 2043 := afterPivot true

def scanRound (b : Bool) : TapeProgram 64 2 2118 :=
  TapeProgram.seq scanSetup (TapeProgram.seq (pivotScan (inputBuffer b))
    (branchZero (TapeMacros.increment 61) (afterPivot b) 8))

def scanRound₀ : TapeProgram 64 2 2118 := scanRound false
def scanRound₁ : TapeProgram 64 2 2118 := scanRound true

def round : TapeProgram 64 2 4241 :=
  branchZero (branchZero scanRound₀ scanRound₁ 60) skip 61

def loop : TapeProgram 64 2 4243 := TapeProgram.countedLoop round 62

def initializeProgram : TapeProgram 64 2 17 :=
  TapeProgram.seq (TapeMacros.clear 48)
    (TapeProgram.seq (TapeMacros.clear 60) (TapeProgram.seq (TapeMacros.clear 61) (TapeMacros.copy 49 62 63)))

/-- Actual fixed finite physical Gaussian program. It performs at most the
runtime number of rows, swapping the two buffers only after successful pivots.
The refinement theorem is developed separately against the exact padded run. -/
def rankProgram : TapeProgram 64 2 4260 := TapeProgram.seq initializeProgram loop

#print axioms branchZero_stops_zero
#print axioms branchZero_stops_positive

def clear3Copy (r : Fin 6 → Fin 64) : TapeProgram 64 2 17 :=
  TapeProgram.seq (TapeMacros.clear (r 0)) (TapeProgram.seq (TapeMacros.clear (r 1))
    (TapeProgram.seq (TapeMacros.clear (r 2)) (TapeMacros.copy (r 3) (r 4) (r 5))))

def clear3CopyStore (r : Fin 6 → Fin 64) (d : Store) : Store :=
  ((((d.setReg (r 0) 0).setReg (r 1) 0).setReg (r 2) 0).setReg (r 4) (d.reg (r 3))).setReg (r 5) 0

theorem clear3Copy_stops (r : Fin 6 → Fin 64) (hr : Function.Injective r) (inp : Inputs) (d : Store) :
    ∃ e,(clear3Copy r).Stops inp (d.toCfg (clear3Copy r).entry)
      (d.reg (r 0)+d.reg (r 1)+d.reg (r 2)+d.reg (r 4)+d.reg (r 5)+5*d.reg (r 3)+13) e ∧
      e.store = clear3CopyStore r d := by
  let d₁ := d.setReg (r 0) 0
  let d₂ := d₁.setReg (r 1) 0
  let d₃ := d₂.setReg (r 2) 0
  have h₁ := TapeMacros.clear_stops (r 0) inp (d.reg (r 0)) d rfl
  have h₂ := TapeMacros.clear_stops (r 1) inp (d.reg (r 1)) d₁ (by simp [d₁,TapeStore.setReg,hr.eq_iff])
  have h₃ := TapeMacros.clear_stops (r 2) inp (d.reg (r 2)) d₂ (by simp [d₂,d₁,TapeStore.setReg,hr.eq_iff])
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops (r 3) (r 4) (r 5)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d₃
  have hall := h₁.seq (h₂.seq (h₃.seq he))
  refine ⟨((e.mapPC (TapeProgram.rightLabel 2)).mapPC (TapeProgram.rightLabel 2)).mapPC (TapeProgram.rightLabel 2),?_,?_⟩
  · convert hall using 1 <;> first | rfl | (simp [d₃,d₂,d₁,TapeStore.setReg,hr.eq_iff];omega)
  · change e.store = _
    simpa [clear3CopyStore,d₃,d₂,d₁,TapeStore.setReg,hr.eq_iff] using hes

theorem clear3CopyStore_bounded (r : Fin 6 → Fin 64) (d : Store) (M : ℕ) (hd : ∀ j,d.reg j ≤ M) :
    ∀ j,(clear3CopyStore r d).reg j ≤ M :=
  FieldPrograms.setReg_bound _ (r 5) 0 M
    (FieldPrograms.setReg_bound _ (r 4) (d.reg (r 3)) M
      (FieldPrograms.setReg_bound _ (r 2) 0 M
        (FieldPrograms.setReg_bound _ (r 1) 0 M
          (FieldPrograms.setReg_bound d (r 0) 0 M hd (Nat.zero_le M)) (Nat.zero_le M))
        (Nat.zero_le M)) (hd (r 3))) (Nat.zero_le M)

def scanLayout (i : Fin 6) : Fin 64 := #v[2,6,8,51,7,63][i.val]
def initialLayout (i : Fin 6) : Fin 64 := #v[48,60,61,49,62,63][i.val]

theorem scanLayout_injective : Function.Injective scanLayout := by decide
theorem initialLayout_injective : Function.Injective initialLayout := by decide

def scanSetupStore (d : Store) : Store := clear3CopyStore scanLayout d
def initializeStore (d : Store) : Store := clear3CopyStore initialLayout d

theorem scanSetup_stops (inp : Inputs) (d : Store) (M : ℕ) (hd : ∀ r,d.reg r ≤ M) :
    ∃ t e,t ≤ 10*M+13 ∧ scanSetup.Stops inp (d.toCfg scanSetup.entry) t e ∧
      e.store = scanSetupStore d ∧ (∀ r,e.reg r ≤ M) := by
  obtain ⟨e,he,hes⟩ := clear3Copy_stops scanLayout scanLayout_injective inp d
  refine ⟨_,e,?_,he,hes,?_⟩
  · change d.reg 2+d.reg 6+d.reg 8+d.reg 7+d.reg 63+5*d.reg 51+13 ≤ _
    have := hd 2;have := hd 6;have := hd 8;have := hd 7;have := hd 63;have := hd 51;omega
  · change ∀ r,e.store.reg r ≤ M
    rw [hes]
    exact clear3CopyStore_bounded scanLayout d M hd

theorem initialize_stops (inp : Inputs) (d : Store) (M : ℕ) (hd : ∀ r,d.reg r ≤ M) :
    ∃ t e,t ≤ 10*M+13 ∧ initializeProgram.Stops inp (d.toCfg initializeProgram.entry) t e ∧
      e.store = initializeStore d ∧ (∀ r,e.reg r ≤ M) := by
  obtain ⟨e,he,hes⟩ := clear3Copy_stops initialLayout initialLayout_injective inp d
  refine ⟨_,e,?_,he,hes,?_⟩
  · change d.reg 48+d.reg 60+d.reg 61+d.reg 62+d.reg 63+5*d.reg 49+13 ≤ _
    have := hd 48;have := hd 60;have := hd 61;have := hd 62;have := hd 63;have := hd 49;omega
  · change ∀ r,e.store.reg r ≤ M
    rw [hes]
    exact clear3CopyStore_bounded initialLayout d M hd

#print axioms scanSetup_stops
#print axioms initialize_stops

theorem scanSetupStore_payload (d : Store) : TapeStore.SamePayload (scanSetupStore d) d :=
  ⟨rfl,rfl,fun _ _ => rfl⟩

theorem initializeStore_payload (d : Store) : TapeStore.SamePayload (initializeStore d) d :=
  ⟨rfl,rfl,fun _ _ => rfl⟩

theorem scanSetupStore_frame (d : Store) (r : Fin 64)
    (h2 : r ≠ 2) (h6 : r ≠ 6) (h8 : r ≠ 8) (h7 : r ≠ 7) (h63 : r ≠ 63) :
    (scanSetupStore d).reg r = d.reg r := by
  simp [scanSetupStore,clear3CopyStore,scanLayout,TapeStore.setReg,h2,h6,h8,h7,h63]

structure Common (ell : ℕ) (h : 0 < ell) (m M : ℕ) (d : Store) : Prop where
  state : SchurCellState ell h 0 1 d M
  columns : d.reg 40 = m
  rows : d.reg 49 = m
  cells : d.reg 51 = m*m
  large : 1 < m

theorem Common.selected {ell : ℕ} {h : 0 < ell} {m M : ℕ} {d : Store}
    (hc : Common ell h m M d) (b : Bool) : SchurCellState ell h (inputBuffer b) (outputBuffer b) d M := by
  cases b with
  | false => exact hc.state
  | true => exact ⟨hc.state.setup,hc.state.bounded,hc.state.outputHead,hc.state.inputHead,
      hc.state.outputMarked,hc.state.inputMarked⟩

theorem common_of_selected {ell : ℕ} {h : 0 < ell} {m M : ℕ} {d : Store} (b : Bool)
    (hs : SchurCellState ell h (inputBuffer b) (outputBuffer b) d M)
    (h40 : d.reg 40 = m) (h49 : d.reg 49 = m) (h51 : d.reg 51 = m*m) (hm : 1 < m) : Common ell h m M d := by
  cases b with
  | false => exact ⟨hs,h40,h49,h51,hm⟩
  | true => exact ⟨⟨hs.setup,hs.bounded,hs.outputHead,hs.inputHead,hs.outputMarked,hs.inputMarked⟩,h40,h49,h51,hm⟩

theorem Common.scanSetupStore {ell : ℕ} {h : 0 < ell} {m M : ℕ} {d : Store}
    (hc : Common ell h m M d) : Common ell h m M (scanSetupStore d) := by
  refine ⟨?_,?_,?_,?_,hc.large⟩
  · exact state_setReg (state_setReg (state_setReg (state_setReg (state_setReg hc.state 2 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)) 6 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)) 8 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)) 7 (d.reg 51)
      (by decide) (by decide) (by decide) (by decide) (hc.state.bounded 51)) 63 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)
  · exact (scanSetupStore_frame d 40 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.columns
  · exact (scanSetupStore_frame d 49 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.rows
  · exact (scanSetupStore_frame d 51 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.cells

abbrev Model (ell m : ℕ) := PaddedGaussian.State (2^ell) m m

structure Represents (ell m : ℕ) (b : Bool) (s : Model ell m) (d : Store) : Prop where
  buffer : d.reg 60 = bit b
  done : d.reg 61 = bit s.done
  rank : d.reg 48 = s.rank
  current : MatrixStored d (inputBuffer b) s.table
  spare : ∃ A : Gaussian.Table (Fin (2^ell)) m m,MatrixStored d (outputBuffer b) A

theorem Represents.of_payload {ell m : ℕ} {b : Bool} {s : Model ell m} {d e : Store}
    (hr : Represents ell m b s d) (hp : TapeStore.SamePayload e d)
    (h60 : e.reg 60 = d.reg 60) (h61 : e.reg 61 = d.reg 61) (h48 : e.reg 48 = d.reg 48) :
    Represents ell m b s e := by
  rcases hr.spare with ⟨A,ha⟩
  exact ⟨h60.trans hr.buffer,h61.trans hr.done,h48.trans hr.rank,
    matrixStored_of_payload hr.current hp,⟨A,matrixStored_of_payload ha hp⟩⟩

theorem Represents.scanSetupStore {ell m : ℕ} {b : Bool} {s : Model ell m} {d : Store}
    (hr : Represents ell m b s d) : Represents ell m b s (scanSetupStore d) :=
  hr.of_payload (scanSetupStore_payload d)
    (scanSetupStore_frame d 60 (by decide) (by decide) (by decide) (by decide) (by decide))
    (scanSetupStore_frame d 61 (by decide) (by decide) (by decide) (by decide) (by decide))
    (scanSetupStore_frame d 48 (by decide) (by decide) (by decide) (by decide) (by decide))

theorem common_after_scan {ell : ℕ} {h : 0 < ell} {m M : ℕ} {d e : Store} {b : Fin 2}
    {A : Gaussian.Table (Fin (2^ell)) m m} (hc : Common ell h m M d)
    (ho : ScanOutcome (flatEntry A) (2^ell) 0 (m*m) M b d e) (hb : ∀ r,e.reg r ≤ M) :
    Common ell h m M e := by
  have hhead (c : Fin 2) : e.bufferHead c ≤ (M+1)^2 := by
    by_cases heq : c = b
    · subst c;exact ho.head
    · rw [ho.otherHead c heq]
      fin_cases c
      · exact hc.state.inputHead
      · exact hc.state.outputHead
  have hs : FieldSetup ell h e := by
    rcases hc.state.setup with ⟨h0,h36,h37,h38⟩
    exact ⟨ho.width,(ho.outside 36 (by decide)).trans h36,(ho.outside 37 (by decide)).trans h37,
      (ho.outside 38 (by decide)).trans h38⟩
  exact ⟨⟨hs,hb,hhead 0,hhead 1,hc.state.inputMarked.of_payload ho.payload,
    hc.state.outputMarked.of_payload ho.payload⟩,(ho.outside 40 (by decide)).trans hc.columns,
    (ho.outside 49 (by decide)).trans hc.rows,(ho.outside 51 (by decide)).trans hc.cells,hc.large⟩

theorem model_rank_step_le (ell : ℕ) (h : 0 < ell) (m : ℕ) (s : Model ell m) :
    (PaddedGaussian.step (PolynomialStretch.BinaryField.indexOperations ell h) s).rank ≤ s.rank+1 := by
  unfold PaddedGaussian.step
  split
  · omega
  · split <;> simp

abbrev ops (ell : ℕ) (h : 0 < ell) := PolynomialStretch.BinaryField.indexOperations ell h

theorem bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> decide

theorem Common.one_le {ell : ℕ} {h : 0 < ell} {m M : ℕ} {d : Store}
    (hc : Common ell h m M d) : 1 ≤ M := by
  have hq := hc.state.bounded 0
  rw [hc.state.setup.1] at hq
  have hp : 0 < 2^ell := pow_pos (by decide) ell
  omega

theorem Common.setReg {ell : ℕ} {h : 0 < ell} {m M : ℕ} {d : Store}
    (hc : Common ell h m M d) (r : Fin 64) (v : ℕ)
    (h0 : r ≠ 0) (h36 : r ≠ 36) (h37 : r ≠ 37) (h38 : r ≠ 38)
    (h40 : r ≠ 40) (h49 : r ≠ 49) (h51 : r ≠ 51) (hv : v ≤ M) :
    Common ell h m M (d.setReg r v) := by
  refine ⟨state_setReg hc.state r v h0 h36 h37 h38 hv,?_,?_,?_,hc.large⟩
  · simpa [TapeStore.setReg,Ne.symm h40] using hc.columns
  · simpa [TapeStore.setReg,Ne.symm h49] using hc.rows
  · simpa [TapeStore.setReg,Ne.symm h51] using hc.cells

theorem flip_stops (b : Bool) (inp : Inputs) (d : Store) (hd : d.reg 60 = bit b) :
    ∃ t e,t ≤ 2 ∧ (flip b).Stops inp (d.toCfg (flip b).entry) t e ∧
      e.store = d.setReg 60 (bit (!b)) := by
  cases b with
  | false =>
    have hs := TapeMacros.increment_stops (60 : Fin 64) inp d
    refine ⟨1,(d.setReg 60 1).toCfg 1,by decide,?_,rfl⟩
    simpa [flip,bit,hd,TapeMacros.increment] using hs
  | true =>
    have hs := TapeMacros.clear_stops (60 : Fin 64) inp 1 d hd
    exact ⟨2,(d.setReg 60 0).toCfg 1,by decide,hs,rfl⟩

theorem flat_coordinates {m : ℕ} (p : Fin m × Fin m) :
    (finProdFinEquiv p).val % m = p.2.val ∧
      (finProdFinEquiv p).val / m * m = p.1.val*m := by
  have he := finProdFinEquiv.symm_apply_apply p
  have hc := congrArg (fun x : Fin m × Fin m => x.2.val) he
  have hr := congrArg (fun x : Fin m × Fin m => x.1.val) he
  change (finProdFinEquiv p).val % m = p.2.val at hc
  change (finProdFinEquiv p).val / m = p.1.val at hr
  exact ⟨hc,congrArg (fun v : ℕ => v*m) hr⟩

def gridBudget (m M : ℕ) : ℕ := 20*(M+1)+m*(rowBudget m M+2)+2
def successBudget (m M : ℕ) : ℕ := 21000*(M+1)^7+gridBudget m M+10
def scanBudget (m M : ℕ) : ℕ := m*m*(100*((M+1)^2+1)^2+5)+1
def roundBudget (m M : ℕ) : ℕ := 10*M+13+scanBudget m M+successBudget m M+20

theorem afterPivot_stops (b : Bool) (ell : ℕ) (h : 0 < ell) (m : ℕ) (s : Model ell m)
    (p : Fin m × Fin m) (inp : Inputs) (d : Store) (M : ℕ)
    (hc : Common ell h m M d) (hr : Represents ell m b s d) (hdone : s.done = false)
    (hflat : d.reg 2 = (finProdFinEquiv p).val)
    (hvalue : d.reg 6 = (Gaussian.toMatrix s.table p.1 p.2).val) (hnext : s.rank+1 ≤ M) :
    ∃ t e,t ≤ successBudget m M ∧ (afterPivot b).Stops inp (d.toCfg (afterPivot b).entry) t e ∧
      Common ell h m M e.store ∧
      Represents ell m (!b) (⟨paddedSchur (ops ell h) s.table p,s.rank+1,false⟩ : Model ell m) e.store ∧
      e.reg 62 = d.reg 62 ∧ e.roHead = d.roHead ∧ e.output = d.output := by
  have hflatB : d.reg 2 < (d.reg 40)^2 := by
    rw [hflat,hc.columns,pow_two]
    exact (finProdFinEquiv p).isLt
  obtain ⟨t₁,c,ht₁,hcs,hco⟩ := GaussianPivot.preparePivot_stops ell h d inp M hc.state.setup hc.state.bounded
    (by rw [hc.columns];exact hc.large) hflatB (Gaussian.toMatrix s.table p.1 p.2) hvalue
  have hcf (r : Fin 64) (hr40 : 40 ≤ r.val) (hC : GaussianPivot.OutsidePivotCoordinates r) (h50 : r ≠ 50) :
      c.store.reg r = d.reg r := hco.frame r hr40 hC h50
  have hseed : SchurCellState ell h (inputBuffer b) (outputBuffer b) c.store M :=
    ⟨hco.setup,hco.bounded,(congrFun hco.heads (inputBuffer b)).le.trans (hc.selected b).inputHead,
      (congrFun hco.heads (outputBuffer b)).le.trans (hc.selected b).outputHead,
      (hc.selected b).inputMarked.of_payload hco.payload,(hc.selected b).outputMarked.of_payload hco.payload⟩
  have hcol : c.store.reg 43 = p.2.val := by
    rw [hco.col,hflat,hc.columns]
    exact (flat_coordinates p).1
  have hrow : c.store.reg 44 = p.1.val*m := by
    rw [hco.rowBase,hflat,hc.columns]
    exact (flat_coordinates p).2
  rcases hr.spare with ⟨Aold,hOld⟩
  have hsize : m*m ≤ M := by rw [← hc.cells];exact hc.state.bounded 51
  obtain ⟨t₂,f,ht₂,hfs,hfo,hInput,hOutput,h41,h45,h46,hff,hro,hout⟩ := materializeGrid_stops
    (inputBuffer b) (outputBuffer b) (buffers_ne b) ell h inp s.table p
      (fun k : Fin (m*m) => flatEntry Aold k.val) M hsize c.store hseed
      ((hcf 40 (by decide) (by decide) (by decide)).trans hc.columns)
      ((hcf 49 (by decide) (by decide) (by decide)).trans hc.rows) hcol hrow hco.inverse
      (matrixStored_of_payload hr.current hco.payload) (matrixStored_of_payload hOld hco.payload)
  have hfc (r : Fin 64) (hr40 : 40 ≤ r.val) (h41 : r ≠ 41) (h42 : r ≠ 42)
      (h45 : r ≠ 45) (h46 : r ≠ 46) (h47 : r ≠ 47) : f.store.reg r = c.store.reg r :=
    hff r hr40 h41 h42 h45 h46 h47
  have hfCommon : Common ell h m M f.store := common_of_selected b hfo
    ((hfc 40 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hcf 40 (by decide) (by decide) (by decide)).trans hc.columns))
    ((hfc 49 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hcf 49 (by decide) (by decide) (by decide)).trans hc.rows))
    ((hfc 51 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hcf 51 (by decide) (by decide) (by decide)).trans hc.cells)) hc.large
  have hfRank : f.store.reg 48 = s.rank :=
    (hfc 48 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hcf 48 (by decide) (by decide) (by decide)).trans hr.rank)
  have hfFlag : f.store.reg 60 = bit b :=
    (hfc 60 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hcf 60 (by decide) (by decide) (by decide)).trans hr.buffer)
  have hfDone : f.store.reg 61 = 0 := by
    have hh := (hfc 61 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hcf 61 (by decide) (by decide) (by decide)).trans hr.done)
    simpa [hdone,bit] using hh
  have hf62 : f.store.reg 62 = d.reg 62 :=
    (hfc 62 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (hcf 62 (by decide) (by decide) (by decide))
  let dRank := f.store.setReg 48 (f.reg 48+1)
  have hRank := TapeMacros.increment_stops (48 : Fin 64) inp f.store
  have hRankCommon : Common ell h m M dRank := hfCommon.setReg 48 (f.reg 48+1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      ((congrArg (fun v : ℕ => v+1) hfRank).le.trans hnext)
  have hRankFlag : dRank.reg 60 = bit b :=
    (show dRank.reg 60 = f.store.reg 60 by simp [dRank,TapeStore.setReg]).trans hfFlag
  obtain ⟨t₃,e,ht₃,he,hes⟩ := flip_stops b inp dRank hRankFlag
  have heCommon : Common ell h m M e.store := by
    rw [hes]
    exact hRankCommon.setReg 60 (bit (!b)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) ((bit_le_one (!b)).trans hc.one_le)
  have hep : TapeStore.SamePayload e.store f.store := by
    rw [hes]
    exact (TapeStore.setReg_payload dRank 60 (bit (!b))).trans
      (TapeStore.setReg_payload f.store 48 (f.reg 48+1))
  have heRank : e.store.reg 48 = f.store.reg 48+1 := by rw [hes];simp [dRank,TapeStore.setReg]
  have heDone : e.store.reg 61 = 0 :=
    (show e.store.reg 61 = f.store.reg 61 by rw [hes];simp [dRank,TapeStore.setReg]).trans hfDone
  have he62 : e.store.reg 62 = d.reg 62 :=
    (show e.store.reg 62 = f.store.reg 62 by rw [hes];simp [dRank,TapeStore.setReg]).trans hf62
  have hall := hcs.seq (hfs.seq (hRank.seq he))
  refine ⟨_,_,?_,hall,heCommon,?_,he62,hep.roHead.trans (hro.trans hco.payload.roHead),
    hep.output.trans (hout.trans hco.payload.output)⟩
  · change t₂ ≤ gridBudget m M at ht₂
    unfold successBudget
    omega
  · refine ⟨?_,heDone,heRank.trans (congrArg (fun v : ℕ => v+1) hfRank),?_,?_⟩
    · change e.store.reg 60 = bit (!b)
      rw [hes]
      simp [TapeStore.setReg]
    · rw [inputBuffer_not]
      exact matrixStored_of_payload hOutput hep
    · refine ⟨s.table,?_⟩
      rw [outputBuffer_not]
      exact matrixStored_of_payload hInput hep

#print axioms afterPivot_stops

theorem Represents.setDone {ell m : ℕ} {b : Bool} {s : Model ell m} {d : Store}
    (hr : Represents ell m b s d) : Represents ell m b {s with done:=true} (d.setReg 61 1) := by
  rcases hr.spare with ⟨A,ha⟩
  exact ⟨by simpa [TapeStore.setReg] using hr.buffer,by simp [TapeStore.setReg,bit],
    by simpa [TapeStore.setReg] using hr.rank,
    matrixStored_of_payload hr.current (TapeStore.setReg_payload d 61 1),
    ⟨A,matrixStored_of_payload ha (TapeStore.setReg_payload d 61 1)⟩⟩

def scanRoundBudget (m M : ℕ) : ℕ := 10*M+13+scanBudget m M+successBudget m M+10

theorem scanRound_stops (b : Bool) (ell : ℕ) (h : 0 < ell) (m : ℕ) (s : Model ell m)
    (inp : Inputs) (d : Store) (M : ℕ) (hc : Common ell h m M d) (hr : Represents ell m b s d)
    (hdone : s.done = false) (hnext : s.rank+1 ≤ M) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 2118) (b' : Bool),t ≤ scanRoundBudget m M ∧
      (scanRound b).Stops inp (d.toCfg (scanRound b).entry) t e ∧ Common ell h m M e.store ∧
      Represents ell m b' (PaddedGaussian.step (ops ell h) s) e.store ∧
      e.reg 62 = d.reg 62 ∧ e.roHead = d.roHead ∧ e.output = d.output := by
  obtain ⟨t₀,c,ht₀,hcs,hcstore,hcb⟩ := scanSetup_stops inp d M hc.state.bounded
  have hcCommon : Common ell h m M c.store := by rw [hcstore];exact hc.scanSetupStore
  have hcRep : Represents ell m b s c.store := by rw [hcstore];exact hr.scanSetupStore
  have hcp : TapeStore.SamePayload c.store d := by rw [hcstore];exact scanSetupStore_payload d
  have hc2 : c.store.reg 2 = 0 := by rw [hcstore];simp [GaussianDriver.scanSetupStore,clear3CopyStore,scanLayout,TapeStore.setReg]
  have hc6 : c.store.reg 6 = 0 := by rw [hcstore];simp [GaussianDriver.scanSetupStore,clear3CopyStore,scanLayout,TapeStore.setReg]
  have hc8 : c.store.reg 8 = 0 := by rw [hcstore];simp [GaussianDriver.scanSetupStore,clear3CopyStore,scanLayout,TapeStore.setReg]
  have hc7 : c.store.reg 7 = m*m := by rw [hcstore];simp [GaussianDriver.scanSetupStore,clear3CopyStore,scanLayout,TapeStore.setReg,hc.cells]
  have hsize : m*m ≤ M := by rw [← hc.cells];exact hc.state.bounded 51
  obtain ⟨t₁,f,ht₁,hfs,hfo,hfb⟩ := pivotScan_table_stops (inputBuffer b) inp s.table c.store M hc.one_le hcb hsize
    hcCommon.state.setup.1 hc2 hc6 hc7 hc8 (hcCommon.selected b).inputMarked
    (hcCommon.selected b).inputHead hcRep.current
  have hfCommon : Common ell h m M f := common_after_scan hcCommon hfo hfb
  have hfRep : Represents ell m b s f := hcRep.of_payload hfo.payload
    (hfo.outside 60 (by decide)) (hfo.outside 61 (by decide)) (hfo.outside 48 (by decide))
  have hfp : TapeStore.SamePayload f d := hfo.payload.trans hcp
  have hf62 : f.reg 62 = d.reg 62 := (hfo.outside 62 (by decide)).trans (by
    rw [hcstore]
    exact scanSetupStore_frame d 62 (by decide) (by decide) (by decide) (by decide) (by decide))
  change t₁ ≤ scanBudget m M at ht₁
  cases hp : PaddedGaussian.pivot s.table with
  | none =>
    have hz := (PaddedGaussian.pivot_none_iff s.table).mp hp
    have hf8 : f.reg 8 = 0 := by simpa [hz] using hfo.found
    have hf61 : f.reg 61 = 0 := by simpa [hdone,bit] using hfRep.done
    have hnone : (TapeMacros.increment (61 : Fin 64)).Stops inp (f.toCfg 0) 1 ((f.setReg 61 1).toCfg 1) := by
      simpa only [hf61,Nat.zero_add] using TapeMacros.increment_stops (61 : Fin 64) inp f
    have hbranch := branchZero_stops_zero (TapeMacros.increment 61) (afterPivot b) 8 inp f hf8 1 _ hnone
    have hall := hcs.seq (hfs.seq hbranch)
    have heCommon : Common ell h m M (f.setReg 61 1) := hfCommon.setReg 61 1
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.one_le
    have heRep : Represents ell m b (PaddedGaussian.step (ops ell h) s) (f.setReg 61 1) := by
      simpa [PaddedGaussian.step,hdone,hp] using hfRep.setDone
    have hep : TapeStore.SamePayload (f.setReg 61 1) d := (TapeStore.setReg_payload f 61 1).trans hfp
    refine ⟨_,_,b,?_,hall,heCommon,heRep,?_,hep.roHead,hep.output⟩
    · unfold scanRoundBudget;omega
    · change (f.setReg 61 1).reg 62 = d.reg 62
      simpa [TapeStore.setReg] using hf62
  | some p =>
    have hp' := (PaddedGaussian.pivot_some_iff s.table p).mp hp
    have hf8 : 0 < f.reg 8 := by rw [hfo.found,if_neg hp'.1];decide
    have hf2 : f.reg 2 = (finProdFinEquiv p).val := hfo.index.trans hp'.2
    have hf6 : f.reg 6 = (Gaussian.toMatrix s.table p.1 p.2).val := hfo.value.trans (PaddedGaussian.pivot_value hp)
    obtain ⟨t₂,e,ht₂,he,heo,her,he62,hero,heout⟩ := afterPivot_stops b ell h m s p inp f M hfCommon hfRep hdone hf2 hf6 hnext
    have hbranch := branchZero_stops_positive (TapeMacros.increment 61) (afterPivot b) 8 inp f hf8 t₂ e he
    have hall := hcs.seq (hfs.seq hbranch)
    refine ⟨_,_,!b,?_,hall,heo,?_,he62.trans hf62,hero.trans hfp.roHead,heout.trans hfp.output⟩
    · unfold scanRoundBudget;omega
    · simpa [PaddedGaussian.step,hdone,hp] using her

#print axioms scanRound_stops

theorem round_stops (b : Bool) (ell : ℕ) (h : 0 < ell) (m : ℕ) (s : Model ell m)
    (inp : Inputs) (d : Store) (M : ℕ) (hc : Common ell h m M d) (hr : Represents ell m b s d)
    (hnext : s.rank+1 ≤ M) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 4241) (b' : Bool),t ≤ roundBudget m M ∧
      round.Stops inp (d.toCfg round.entry) t e ∧ Common ell h m M e.store ∧
      Represents ell m b' (PaddedGaussian.step (ops ell h) s) e.store ∧
      e.reg 62 = d.reg 62 ∧ e.roHead = d.roHead ∧ e.output = d.output := by
  cases hd : s.done with
  | false =>
    obtain ⟨t,e,b',ht,he,heo,her,he62,hero,heout⟩ := scanRound_stops b ell h m s inp d M hc hr hd hnext
    have hselect : ∃ (u : ℕ) (g : TapeCfg 64 2 4238),u ≤ t+2 ∧
        (branchZero scanRound₀ scanRound₁ 60).Stops inp
          (d.toCfg (branchZero scanRound₀ scanRound₁ 60).entry) u g ∧ g.store = e.store := by
      cases b with
      | false =>
        have h0 : d.reg 60 = 0 := by simpa [bit] using hr.buffer
        exact ⟨t+1,e.mapPC (zeroLabel 2118),by omega,
          branchZero_stops_zero scanRound₀ scanRound₁ 60 inp d h0 t e he,rfl⟩
      | true =>
        have h1 : 0 < d.reg 60 := by have hh := hr.buffer; simp [bit] at hh;omega
        exact ⟨t+2,e.mapPC (positiveLabel 2118),le_rfl,
          branchZero_stops_positive scanRound₀ scanRound₁ 60 inp d h1 t e he,rfl⟩
    obtain ⟨u,g,hu,hgs,hstore⟩ := hselect
    have hdone0 : d.reg 61 = 0 := by simpa [hd,bit] using hr.done
    have hall := branchZero_stops_zero (branchZero scanRound₀ scanRound₁ 60) skip 61 inp d hdone0 u g hgs
    refine ⟨_,_,b',?_,hall,?_,?_,?_,?_,?_⟩
    · unfold roundBudget scanRoundBudget at *
      omega
    · change Common ell h m M g.store
      rw [hstore]
      exact heo
    · change Represents ell m b' (PaddedGaussian.step (ops ell h) s) g.store
      rw [hstore]
      exact her
    · change g.store.reg 62 = d.reg 62
      exact (congrArg (fun x : Store => x.reg 62) hstore).trans he62
    · change g.store.roHead = d.roHead
      exact (congrArg TapeStore.roHead hstore).trans hero
    · change g.store.output = d.output
      exact (congrArg TapeStore.output hstore).trans heout
  | true =>
    have hdone1 : 0 < d.reg 61 := by have hh := hr.done;simp [hd,bit] at hh;omega
    have hall := branchZero_stops_positive (branchZero scanRound₀ scanRound₁ 60) skip 61 inp d hdone1 0 _ (skip_stops inp d)
    refine ⟨2,_,b,?_,hall,hc,?_,rfl,rfl,rfl⟩
    · unfold roundBudget;omega
    · simpa only [PaddedGaussian.step_done (ops ell h) s hd] using hr

#print axioms round_stops

theorem initializeStore_frame (d : Store) (r : Fin 64)
    (h48 : r ≠ 48) (h60 : r ≠ 60) (h61 : r ≠ 61) (h62 : r ≠ 62) (h63 : r ≠ 63) :
    (initializeStore d).reg r = d.reg r := by
  simp [initializeStore,clear3CopyStore,initialLayout,TapeStore.setReg,h48,h60,h61,h62,h63]

theorem Common.initializeStore {ell : ℕ} {h : 0 < ell} {m M : ℕ} {d : Store}
    (hc : Common ell h m M d) : Common ell h m M (initializeStore d) := by
  refine ⟨?_,?_,?_,?_,hc.large⟩
  · exact state_setReg (state_setReg (state_setReg (state_setReg (state_setReg hc.state 48 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)) 60 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)) 61 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)) 62 (d.reg 49)
      (by decide) (by decide) (by decide) (by decide) (hc.state.bounded 49)) 63 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)
  · exact (initializeStore_frame d 40 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.columns
  · exact (initializeStore_frame d 49 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.rows
  · exact (initializeStore_frame d 51 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.cells

def LoopInv (ell : ℕ) (h : 0 < ell) (m M : ℕ) (initial : Model ell m) (base : Store)
    (remaining : ℕ) (d : Store) : Prop :=
  Common ell h m M d ∧ d.roHead = base.roHead ∧ d.output = base.output ∧
    ∃ (b : Bool) (s : Model ell m),Represents ell m b s d ∧ s.rank+remaining ≤ m ∧
      ((PaddedGaussian.step (ops ell h))^[remaining] s) = ((PaddedGaussian.step (ops ell h))^[m] initial)

theorem loop_stops (ell : ℕ) (h : 0 < ell) (m M : ℕ) (initial : Model ell m) (base : Store)
    (inp : Inputs) (remaining : ℕ) (d : Store) (hd : d.reg 62 = remaining)
    (hi : LoopInv ell h m M initial base remaining d) :
    ∃ t e,t ≤ remaining*(roundBudget m M+2)+1 ∧
      loop.Stops inp (d.toCfg (TapeProgram.loopHeader 4241)) t (e.toCfg (TapeProgram.loopExit 4241)) ∧
      LoopInv ell h m M initial base 0 e ∧ e.reg 62 = 0 := by
  apply countedLoop_stops_of_body round 62 inp (roundBudget m M) (LoopInv ell h m M initial base)
    _ remaining d hd hi
  intro r s hs62 hs
  rcases hs with ⟨hc,hro,hout,b,model,hr,hprogress,hfuture⟩
  let s₀ := TapeProgram.decStore (62 : Fin 64) s
  have hp : TapeStore.SamePayload s₀ s := TapeStore.setReg_payload s 62 (s.reg 62-1)
  have hc0 : Common ell h m M s₀ := hc.setReg 62 (s.reg 62-1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ((Nat.sub_le _ _).trans (hc.state.bounded 62))
  have hr0 : Represents ell m b model s₀ := hr.of_payload hp
    (by simp [s₀,TapeProgram.decStore]) (by simp [s₀,TapeProgram.decStore]) (by simp [s₀,TapeProgram.decStore])
  have hmM : m ≤ M := by rw [← hc.rows];exact hc.state.bounded 49
  have hnext : model.rank+1 ≤ M := by omega
  obtain ⟨t,e,b',ht,he,heo,her,he62,hero,heout⟩ := round_stops b ell h m model inp s₀ M hc0 hr0 hnext
  have he62' : e.reg 62 = r := by
    rw [he62]
    simp [s₀,TapeProgram.decStore,hs62]
  have hprogress' : (PaddedGaussian.step (ops ell h) model).rank+r ≤ m := by
    have hh : (PaddedGaussian.step (ops ell h) model).rank ≤ model.rank+1 :=
      model_rank_step_le ell h m model
    omega
  have hfuture' : ((PaddedGaussian.step (ops ell h))^[r] (PaddedGaussian.step (ops ell h) model)) =
      ((PaddedGaussian.step (ops ell h))^[m] initial) := by
    simpa only [Function.iterate_succ_apply] using hfuture
  exact ⟨t,e,ht,he,he62',heo,hero.trans hro,heout.trans hout,b',
    PaddedGaussian.step (ops ell h) model,her,hprogress',hfuture'⟩

/-- Actual physical Gaussian elimination from two encoded square buffers.
The finite code has4260 labels regardless of the runtime field/dimension.
Every source loop is bounded, every field operation is a checked source
program, and the resulting register48 matches the exact padded iteration. -/
theorem rankProgram_stops (ell : ℕ) (h : 0 < ell) (m M : ℕ) (inp : Inputs) (d : Store)
    (hc : Common ell h m M d) (A B : Gaussian.Table (Fin (2^ell)) m m)
    (ha : MatrixStored d 0 A) (hb : MatrixStored d 1 B) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 4260),t ≤ 10*M+13+m*(roundBudget m M+2)+2 ∧
      rankProgram.Stops inp (d.toCfg rankProgram.entry) t e ∧ Common ell h m M e.store ∧
      e.reg 48 = ((PaddedGaussian.step (ops ell h))^[m] (⟨A,0,false⟩ : Model ell m)).rank ∧
      e.reg 62 = 0 ∧ e.roHead = d.roHead ∧ e.output = d.output := by
  let initial : Model ell m := ⟨A,0,false⟩
  obtain ⟨t₀,c,ht₀,hcs,hcstore,hcb⟩ := initialize_stops inp d M hc.state.bounded
  have hcCommon : Common ell h m M c.store := by rw [hcstore];exact hc.initializeStore
  have hcp : TapeStore.SamePayload c.store d := by rw [hcstore];exact initializeStore_payload d
  have hc62 : c.reg 62 = m := by
    change c.store.reg 62 = m
    rw [hcstore]
    simp [GaussianDriver.initializeStore,clear3CopyStore,initialLayout,TapeStore.setReg,hc.rows]
  have hrep : Represents ell m false initial c.store := by
    refine ⟨?_,?_,?_,matrixStored_of_payload ha hcp,⟨B,matrixStored_of_payload hb hcp⟩⟩
    · rw [hcstore];simp [GaussianDriver.initializeStore,clear3CopyStore,initialLayout,TapeStore.setReg,bit]
    · rw [hcstore];simp [GaussianDriver.initializeStore,clear3CopyStore,initialLayout,TapeStore.setReg,initial,bit]
    · rw [hcstore];simp [GaussianDriver.initializeStore,clear3CopyStore,initialLayout,TapeStore.setReg,initial]
  have hi : LoopInv ell h m M initial d m c.store :=
    ⟨hcCommon,hcp.roHead,hcp.output,false,initial,hrep,by simp [initial],rfl⟩
  obtain ⟨t₁,e,ht₁,hes,hend,he62⟩ := loop_stops ell h m M initial d inp m c.store hc62 hi
  rcases hend with ⟨heCommon,hero,heout,b',model,her,hprogress,hfuture⟩
  have hmodel : model = (PaddedGaussian.step (ops ell h))^[m] initial := by simpa using hfuture
  have hall := hcs.seq hes
  refine ⟨_,_,by omega,hall,heCommon,?_,he62,hero,heout⟩
  · exact her.rank.trans (congrArg PaddedGaussian.State.rank hmodel)

#print axioms loop_stops
#print axioms rankProgram_stops

end ExpandingCodes.Computation.GaussianDriver
