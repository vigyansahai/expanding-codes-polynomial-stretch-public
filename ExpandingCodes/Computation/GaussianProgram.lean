import ExpandingCodes.Computation.TapeArrays
import ExpandingCodes.Computation.EncodedGaussian
import ExpandingCodes.Computation.SourceFieldArithmetic

set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianProgram

open NKtLB TapeArrays

/-- Register layout for physical Gaussian array access: persistent width 0,
scratch width 1, flat index 2, offset 3, scratch 4/5, entry value 6,
remaining cells 7, and found flag 8. The remaining fixed registers are
available for dimensions, pivot coordinates, rank and field routines. -/
abbrev Store := TapeStore 64 2

def readCurrent (b : Fin 2) : TapeProgram 64 2 48 :=
  TapeProgram.seq (TapeMacros.copy 0 1 4)
    (TapeProgram.seq (TapeMacros.clear 6) (readEntry 2 1 3 4 5 6 b))

def readPost (d : Store) (v : ℕ) : Store :=
  ((((d.setReg 1 0).setReg 3 0).setReg 4 0).setReg 5 0).setReg 6 v

theorem readPost_outside (d : Store) (v : ℕ) (r : Fin 64) (hr : 9 ≤ r.val) :
    (readPost d v).reg r = d.reg r := by
  have h1 : r ≠ 1 := by intro h; subst r; norm_num at hr
  have h3 : r ≠ 3 := by intro h; subst r; norm_num at hr
  have h4 : r ≠ 4 := by intro h; subst r; norm_num at hr
  have h5 : r ≠ 5 := by intro h; subst r; norm_num at hr
  have h6 : r ≠ 6 := by intro h; subst r; norm_num at hr
  simp [readPost, TapeStore.setReg, h1, h3, h4, h5, h6]

theorem readPost_scratch_zero (d : Store) (v : ℕ) (r : Fin 64)
    (hr : r = 1 ∨ r = 3 ∨ r = 4 ∨ r = 5) : (readPost d v).reg r = 0 := by
  rcases hr with rfl | rfl | rfl | rfl <;> simp [readPost,TapeStore.setReg]

def AccessBounded (d : Store) (M : ℕ) : Prop :=
  d.reg 0 ≤ M ∧ d.reg 1 ≤ M ∧ d.reg 2 ≤ M ∧ d.reg 3 ≤ M ∧
    d.reg 4 ≤ M ∧ d.reg 5 ≤ M ∧ d.reg 6 ≤ M

/-- Complete physical read with a persistent q register. Copying q and clearing
the accumulator are actual finite source routines, included in the bound. -/
theorem readCurrent_stops (b : Fin 2) (inp : Inputs) (d : Store) (M v : ℕ)
    (hm : BottomMarked d b) (hM : AccessBounded d M) (hh : d.bufferHead b ≤ M)
    (hv : ThermometerAt d b (entryOffset (d.reg 2) (d.reg 0)) (d.reg 0) v) :
    ∃ t e, t ≤ 100*(M+1)^2 ∧
      (readCurrent b).Stops inp (d.toCfg (readCurrent b).entry) t e ∧
      e.reg = (readPost d v).reg ∧
      e.bufferHead = Function.update d.bufferHead b
        (entryOffset (d.reg 2) (d.reg 0)+d.reg 0) ∧
      TapeStore.SamePayload e.store d := by
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops
    (B := 2) (0 : Fin 64) 1 4 (by decide) (by decide) (by decide) inp d
  have hcr : c.reg = ((d.setReg 1 (d.reg 0)).setReg 4 0).reg :=
    congrArg TapeStore.reg hcs
  let d₁ := c.store.setReg 6 0
  have hclear := TapeMacros.clear_stops (6 : Fin 64) inp (c.reg 6) c.store rfl
  have hcp : TapeStore.SamePayload c.store d := by
    rw [hcs]
    exact (TapeStore.setReg_payload _ 4 0).trans
      (TapeStore.setReg_payload d 1 (d.reg 0))
  have hdp : TapeStore.SamePayload d₁ d :=
    (TapeStore.setReg_payload c.store 6 0).trans hcp
  have hdh : d₁.bufferHead = d.bufferHead := by
    change c.store.bufferHead = d.bufferHead
    rw [hcs]
    rfl
  have hd1 : d₁.reg 1 = d.reg 0 := by simp [d₁, hcr, TapeStore.setReg]
  have hd2 : d₁.reg 2 = d.reg 2 := by simp [d₁, hcr, TapeStore.setReg]
  have hdt : ThermometerAt d₁ b (entryOffset (d₁.reg 2) (d₁.reg 1)) (d₁.reg 1) v := by
    rw [hd1, hd2]
    exact hv.of_payload hdp
  obtain ⟨s, e, hs, he, her, heh, hep⟩ := readEntry_stops
    (2 : Fin 64) 1 3 4 5 6 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) b inp d₁
      (hm.of_payload hdp).marked (by simp [d₁, TapeStore.setReg]) v hdt
  have hbound : entryAccessBound d₁ 2 1 3 4 5 b ≤ 50*(M+1)^2 := by
    rcases hM with ⟨h0,h1,h2,h3,h4,h5,h6⟩
    apply entryAccessBound_le d₁ 2 1 3 4 5 b M
    · simpa [d₁, hcr, TapeStore.setReg] using h2
    · simpa [d₁, hcr, TapeStore.setReg] using h0
    · simpa [d₁, hcr, TapeStore.setReg] using h3
    · simp [d₁, hcr, TapeStore.setReg]
    · simpa [d₁, hcr, TapeStore.setReg] using h5
    · simpa [hdh] using hh
  have hall := hc.seq (hclear.seq he)
  refine ⟨_, _, ?_, hall, ?_, ?_, hep.trans hdp⟩
  · have hc6 : c.reg 6 = d.reg 6 := by change c.store.reg 6 = _; rw [hcs]; simp [TapeStore.setReg]
    rw [hc6]
    rcases hM with ⟨h0,h1,h2,h3,h4,h5,h6⟩
    nlinarith
  · change e.reg = _
    rw [her]
    simp only [d₁, hcr, readPost, TapeStore.setReg]
    funext r
    by_cases h6 : r = 6
    · subst r; simp
    · by_cases h5 : r = 5
      · subst r; simp
      · by_cases h4 : r = 4
        · subst r; simp
        · by_cases h3 : r = 3
          · subst r; simp
          · by_cases h1 : r = 1
            · subst r; simp
            · simp [Function.update, h1, h3, h4, h5, h6]
  · change e.bufferHead = _
    rw [heh, hd1, hd2, hdh]

#print axioms readCurrent_stops

section SearchLoop

variable {R B L : ℕ}

def searchLabel (L : ℕ) (k : Fin 6) : Fin (L+6) := TapeProgram.rightLabel L k

/-- Actual finite early-exit loop. Body halt jumps to an explicit unary test;
zero advances the flat index, while positive restores the value and marks a
successful pivot. All destinations are finite labels, with no array oracle. -/
def searchLoop (P : TapeProgram R B L) (remaining value index found : Fin R) :
    TapeProgram R B (L+6) where
  entry := searchLabel L 0
  code j := match finSumFinEquiv.symm j with
    | .inl i => match P.code i with
      | .halt => .jump (searchLabel L 1)
      | a => a.relabel (TapeProgram.leftLabel 6)
    | .inr k =>
      if k = 0 then .dec remaining (searchLabel L 5) (TapeProgram.leftLabel 6 P.entry)
      else if k = 1 then .dec value (searchLabel L 2) (searchLabel L 3)
      else if k = 2 then .inc index (searchLabel L 0)
      else if k = 3 then .inc value (searchLabel L 4)
      else if k = 4 then .inc found (searchLabel L 5) else .halt

theorem searchLoop_body_active (P : TapeProgram R B L) (remaining value index found : Fin R)
    (j : Fin L) (hj : P.code j ≠ .halt) :
    (searchLoop P remaining value index found).code (TapeProgram.leftLabel 6 j) =
      (P.code j).relabel (TapeProgram.leftLabel 6) := by
  simp only [searchLoop, TapeProgram.leftLabel, Equiv.symm_apply_apply]

theorem searchLoop_body_halt (P : TapeProgram R B L) (remaining value index found : Fin R)
    (j : Fin L) (hj : P.code j = .halt) :
    (searchLoop P remaining value index found).code (TapeProgram.leftLabel 6 j) =
      .jump (searchLabel L 1) := by
  simp [searchLoop, TapeProgram.leftLabel, hj]

@[simp] theorem searchLoop_tail (P : TapeProgram R B L) (remaining value index found : Fin R)
    (k : Fin 6) :
    (searchLoop P remaining value index found).code (searchLabel L k) =
      if k = 0 then .dec remaining (searchLabel L 5) (TapeProgram.leftLabel 6 P.entry)
      else if k = 1 then .dec value (searchLabel L 2) (searchLabel L 3)
      else if k = 2 then .inc index (searchLabel L 0)
      else if k = 3 then .inc value (searchLabel L 4)
      else if k = 4 then .inc found (searchLabel L 5) else .halt := by
  simp [searchLoop, searchLabel, TapeProgram.rightLabel]

theorem searchLoop_zero (P : TapeProgram R B L) (remaining value index found : Fin R)
    (inp : Inputs) (d : TapeStore R B) (hr : d.reg remaining = 0) :
    (searchLoop P remaining value index found).Stops inp (d.toCfg (searchLabel L 0)) 1
      (d.toCfg (searchLabel L 5)) := by
  constructor
  · apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, searchLoop_tail]
    · simp [TapeProgram.step, searchLoop_tail, TapeStore.toCfg, hr]
  · simp [TapeProgram.halted, searchLoop_tail]

theorem searchLoop_header (P : TapeProgram R B L) (remaining value index found : Fin R)
    (inp : Inputs) (d : TapeStore R B) (hr : 0 < d.reg remaining) :
    (searchLoop P remaining value index found).Exec inp (d.toCfg (searchLabel L 0)) 1
      ((TapeProgram.decStore remaining d).toCfg (TapeProgram.leftLabel 6 P.entry)) := by
  apply TapeProgram.Exec.one
  · simp [TapeProgram.halted, searchLoop_tail]
  · simp [TapeProgram.step, searchLoop_tail, TapeStore.toCfg, TapeProgram.decStore, Nat.ne_of_gt hr]

theorem searchLoop_return (P : TapeProgram R B L) (remaining value index found : Fin R)
    (inp : Inputs) (c : TapeCfg R B L) (hc : P.halted c) :
    (searchLoop P remaining value index found).Exec inp (c.mapPC (TapeProgram.leftLabel 6)) 1
      (c.store.toCfg (searchLabel L 1)) := by
  apply TapeProgram.Exec.one
  · change (searchLoop P remaining value index found).code (TapeProgram.leftLabel 6 c.pc) ≠ .halt
    rw [searchLoop_body_halt _ _ _ _ _ _ hc]
    simp
  · simp only [TapeProgram.step, TapeCfg.mapPC]
    rw [searchLoop_body_halt _ _ _ _ _ _ hc]

theorem searchLoop_continue (P : TapeProgram R B L) (remaining value index found : Fin R)
    (inp : Inputs) (d : TapeStore R B) (hr : 0 < d.reg remaining)
    (t : ℕ) (c : TapeCfg R B L)
    (hc : P.Stops inp ((TapeProgram.decStore remaining d).toCfg P.entry) t c)
    (hv : c.reg value = 0) :
    (searchLoop P remaining value index found).Exec inp (d.toCfg (searchLabel L 0)) (t+4)
      ((c.store.setReg index (c.reg index+1)).toCfg (searchLabel L 0)) := by
  have hh := searchLoop_header P remaining value index found inp d hr
  have hb := hc.exec.relabel (TapeProgram.leftLabel 6)
    (searchLoop_body_active P remaining value index found)
  have hreturn := searchLoop_return P remaining value index found inp c hc.halted
  have htest : (searchLoop P remaining value index found).Exec inp
      (c.store.toCfg (searchLabel L 1)) 1 (c.store.toCfg (searchLabel L 2)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, searchLoop_tail]
    · simp [TapeProgram.step, searchLoop_tail, TapeStore.toCfg, hv]
  have hinc : (searchLoop P remaining value index found).Exec inp
      (c.store.toCfg (searchLabel L 2)) 1
      ((c.store.setReg index (c.reg index+1)).toCfg (searchLabel L 0)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, searchLoop_tail]
    · simp [TapeProgram.step, searchLoop_tail, TapeStore.toCfg, TapeStore.setReg]
  convert (((hh.trans hb).trans hreturn).trans htest).trans hinc using 1 <;> first | rfl | omega

theorem searchLoop_found (P : TapeProgram R B L) (remaining value index found : Fin R)
    (inp : Inputs) (d : TapeStore R B) (hr : 0 < d.reg remaining)
    (t : ℕ) (c : TapeCfg R B L)
    (hc : P.Stops inp ((TapeProgram.decStore remaining d).toCfg P.entry) t c)
    (hv : 0 < c.reg value) :
    (searchLoop P remaining value index found).Stops inp (d.toCfg (searchLabel L 0)) (t+5)
      ((c.store.setReg found (c.reg found+1)).toCfg (searchLabel L 5)) := by
  have hh := searchLoop_header P remaining value index found inp d hr
  have hb := hc.exec.relabel (TapeProgram.leftLabel 6)
    (searchLoop_body_active P remaining value index found)
  have hreturn := searchLoop_return P remaining value index found inp c hc.halted
  let d₁ := c.store.setReg value (c.reg value-1)
  have htest : (searchLoop P remaining value index found).Exec inp
      (c.store.toCfg (searchLabel L 1)) 1 (d₁.toCfg (searchLabel L 3)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, searchLoop_tail]
    · simp [TapeProgram.step, searchLoop_tail, TapeStore.toCfg, d₁, TapeStore.setReg, Nat.ne_of_gt hv]
  have hrestore : (searchLoop P remaining value index found).Exec inp
      (d₁.toCfg (searchLabel L 3)) 1 (c.store.toCfg (searchLabel L 4)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, searchLoop_tail]
    · simp [TapeProgram.step, searchLoop_tail, TapeStore.toCfg, d₁, TapeStore.setReg,
        Function.update_idem, Nat.sub_add_cancel hv]
  have hmark : (searchLoop P remaining value index found).Exec inp
      (c.store.toCfg (searchLabel L 4)) 1
      ((c.store.setReg found (c.reg found+1)).toCfg (searchLabel L 5)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, searchLoop_tail]
    · simp [TapeProgram.step, searchLoop_tail, TapeStore.toCfg, TapeStore.setReg]
  constructor
  · convert ((((hh.trans hb).trans hreturn).trans htest).trans hrestore).trans hmark using 1
      <;> first | rfl | omega
  · simp [TapeProgram.halted, searchLoop_tail]

end SearchLoop

def pivotScan (b : Fin 2) : TapeProgram 64 2 54 := searchLoop (readCurrent b) 7 6 2 8

/-- First nonzero entry of a bounded consecutive row-major interval. A failed
search returns the first index after that interval and value zero. -/
def scanResult (a : ℕ → ℕ) : ℕ → ℕ → ℕ × ℕ
  | i, 0 => (i, 0)
  | i, n+1 => if a i = 0 then scanResult a (i+1) n else (i, a i)

theorem scanResult_spec (a : ℕ → ℕ) (i n : ℕ) :
    ((scanResult a i n).2 = 0 ∧ (scanResult a i n).1 = i+n ∧
      ∀ j, i ≤ j → j < i+n → a j = 0) ∨
    (i ≤ (scanResult a i n).1 ∧ (scanResult a i n).1 < i+n ∧
      (scanResult a i n).2 = a (scanResult a i n).1 ∧ (scanResult a i n).2 ≠ 0 ∧
      ∀ j, i ≤ j → j < (scanResult a i n).1 → a j = 0) := by
  induction n generalizing i with
  | zero => exact Or.inl ⟨rfl, by simp [scanResult], by intro j hj hj'; omega⟩
  | succ n ih =>
    by_cases ha : a i = 0
    · simp only [scanResult, if_pos ha]
      rcases ih (i+1) with h | h
      · left
        refine ⟨h.1, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.2.1, ?_⟩
        intro j hji hjn
        by_cases hji' : j = i
        · simpa [hji'] using ha
        · exact h.2.2 j (by omega) (by omega)
      · right
        refine ⟨by omega, by have := h.2.1; omega, h.2.2.1, h.2.2.2.1, ?_⟩
        intro j hji hjn
        by_cases hji' : j = i
        · simpa [hji'] using ha
        · exact h.2.2.2.2 j (by omega) hjn
    · right
      simp only [scanResult, if_neg ha]
      exact ⟨le_rfl, by omega, trivial, ha, by intro j hj hj'; omega⟩

def flatEntry {q m n : ℕ} (A : Gaussian.Table (Fin q) m n) (k : ℕ) : ℕ :=
  if hk : k < m*n then
    (Gaussian.toMatrix A (finProdFinEquiv.symm ⟨k,hk⟩).1 (finProdFinEquiv.symm ⟨k,hk⟩).2).val
  else 0

/-- Representation of one full rectangular matrix by actual q-cell blocks. -/
def MatrixStored {q m n : ℕ} (d : Store) (b : Fin 2) (A : Gaussian.Table (Fin q) m n) : Prop :=
  ThermometerTable d b q (fun k : Fin (m*n) => flatEntry A k.val)

structure ScanOutcome (a : ℕ → ℕ) (q i n K : ℕ) (b : Fin 2)
    (d e : Store) : Prop where
  width : e.reg 0 = q
  index : e.reg 2 = (scanResult a i n).1
  value : e.reg 6 = (scanResult a i n).2
  found : e.reg 8 = if (scanResult a i n).2 = 0 then 0 else 1
  bounded : AccessBounded e ((K+1)^2)
  head : e.bufferHead b ≤ (K+1)^2
  payload : TapeStore.SamePayload e d
  outside : ∀ r : Fin 64, 9 ≤ r.val → e.reg r = d.reg r
  otherHead : ∀ c : Fin 2, c ≠ b → e.bufferHead c = d.bufferHead c
  scratch : ∀ r : Fin 64, r = 1 ∨ r = 3 ∨ r = 4 ∨ r = 5 → e.reg r ≤ d.reg r
  remaining : e.reg 7 ≤ d.reg 7

/-- Uniform physical pivot search. The invariant preserves the whole encoded
matrix while advancing the runtime flat index past exactly the zero entries.
Both code size and register count are independent of q and the cell count. -/
theorem pivotScan_stops (b : Fin 2) (inp : Inputs) (a : ℕ → ℕ)
    (q i n K : ℕ) (d : Store) (hq : q ≤ K) (hi : i+n ≤ K)
    (hr0 : d.reg 0 = q) (hr2 : d.reg 2 = i) (hr6 : d.reg 6 = 0)
    (hr7 : d.reg 7 = n) (hr8 : d.reg 8 = 0)
    (hm : BottomMarked d b) (hb : AccessBounded d ((K+1)^2))
    (hh : d.bufferHead b ≤ (K+1)^2)
    (hblocks : ∀ j, j < n → ThermometerAt d b (entryOffset (i+j) q) q (a (i+j))) :
    ∃ (t : ℕ) (e : Store), t ≤ n*(100*((K+1)^2+1)^2+5)+1 ∧
      (pivotScan b).Stops inp (d.toCfg (searchLabel 48 0)) t (e.toCfg (searchLabel 48 5)) ∧
      ScanOutcome a q i n K b d e := by
  induction n generalizing i d with
  | zero =>
    refine ⟨1, d, by simp, searchLoop_zero (readCurrent b) 7 6 2 8 inp d hr7, ?_⟩
    exact ⟨hr0, hr2, hr6, by simpa [scanResult] using hr8, hb, hh,
      TapeStore.SamePayload.refl d, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => le_rfl, le_rfl⟩
  | succ n ih =>
    let d₀ := TapeProgram.decStore (7 : Fin 64) d
    have hd₀p : TapeStore.SamePayload d₀ d := TapeStore.setReg_payload d 7 (d.reg 7-1)
    have hd₀0 : d₀.reg 0 = q := by simp [d₀, TapeProgram.decStore, hr0]
    have hd₀2 : d₀.reg 2 = i := by simp [d₀, TapeProgram.decStore, hr2]
    have hd₀b : AccessBounded d₀ ((K+1)^2) := by
      simpa [AccessBounded, d₀, TapeProgram.decStore] using hb
    have hblock : ThermometerAt d₀ b (entryOffset (d₀.reg 2) (d₀.reg 0)) (d₀.reg 0) (a i) := by
      rw [hd₀0, hd₀2]
      simpa using (hblocks 0 (by omega)).of_payload hd₀p
    obtain ⟨s, c, hs, hc, hcr, hch, hcp⟩ := readCurrent_stops b inp d₀ ((K+1)^2) (a i)
      (hm.of_payload hd₀p) hd₀b hh hblock
    have hc0 : c.reg 0 = q := by rw [hcr]; simp [readPost, TapeStore.setReg, hd₀0]
    have hc2 : c.reg 2 = i := by rw [hcr]; simp [readPost, TapeStore.setReg, hd₀2]
    have hc6 : c.reg 6 = a i := by rw [hcr]; simp [readPost, TapeStore.setReg]
    have hc7 : c.reg 7 = n := by
      rw [hcr]
      simp [readPost, TapeStore.setReg, d₀, TapeProgram.decStore, hr7]
    have hc8 : c.reg 8 = 0 := by
      rw [hcr]
      simp [readPost, TapeStore.setReg, d₀, TapeProgram.decStore, hr8]
    have hcpd : TapeStore.SamePayload c.store d := hcp.trans hd₀p
    have hK : K ≤ (K+1)^2 := by nlinarith
    have hqK : q ≤ (K+1)^2 := hq.trans hK
    have hiK : i ≤ (K+1)^2 := (by omega : i ≤ K).trans hK
    have haK : a i ≤ (K+1)^2 := hblock.1.trans (by rw [hd₀0]; exact hqK)
    have hcb : AccessBounded c.store ((K+1)^2) := by
      simp [AccessBounded, hcr, readPost, TapeStore.setReg, hd₀0, hd₀2, hqK, hiK, haK]
    have hchead : c.bufferHead b ≤ (K+1)^2 := by
      rw [hch]
      simp only [Function.update_self, hd₀0, hd₀2]
      have hmul : (i+1)*q ≤ K*K := Nat.mul_le_mul (by omega) hq
      unfold entryOffset
      nlinarith
    have hcframe (r : Fin 64) (hr : 9 ≤ r.val) : c.reg r = d.reg r := by
      rw [hcr]
      rw [readPost_outside d₀ (a i) r hr]
      have h7 : r ≠ 7 := by intro h; subst r; norm_num at hr
      simp [d₀, TapeProgram.decStore, h7]
    have hcheadframe (c' : Fin 2) (hne : c' ≠ b) : c.bufferHead c' = d.bufferHead c' := by
      rw [hch]
      simp [Function.update_of_ne hne, d₀, TapeProgram.decStore]
    by_cases hai : a i = 0
    · let d₁ := c.store.setReg 2 (c.reg 2+1)
      have hd₁p : TapeStore.SamePayload d₁ d :=
        (TapeStore.setReg_payload c.store 2 (c.reg 2+1)).trans hcpd
      have hd₁0 : d₁.reg 0 = q := by simp [d₁, TapeStore.setReg, hc0]
      have hd₁2 : d₁.reg 2 = i+1 := by simp [d₁, TapeStore.setReg, hc2]
      have hd₁6 : d₁.reg 6 = 0 := by simp [d₁, TapeStore.setReg, hc6, hai]
      have hd₁7 : d₁.reg 7 = n := by simp [d₁, TapeStore.setReg, hc7]
      have hd₁8 : d₁.reg 8 = 0 := by simp [d₁, TapeStore.setReg, hc8]
      have hd₁b : AccessBounded d₁ ((K+1)^2) := by
        have hi1 : i+1 ≤ (K+1)^2 := (by omega : i+1 ≤ K).trans hK
        simpa [AccessBounded, d₁, TapeStore.setReg, hc2, hiK, hi1] using hcb
      have htail : ∀ j, j < n → ThermometerAt d₁ b
          (entryOffset (i+1+j) q) q (a (i+1+j)) := by
        intro j hj
        have h := (hblocks (j+1) (by omega)).of_payload hd₁p
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      obtain ⟨t, e, ht, he, ho⟩ := ih (i+1) d₁ (by omega) hd₁0 hd₁2 hd₁6 hd₁7 hd₁8
        (hm.of_payload hd₁p) hd₁b hchead htail
      have hcont := searchLoop_continue (readCurrent b) 7 6 2 8 inp d
        (by omega) s c hc (by rw [hc6]; exact hai)
      refine ⟨s+4+t, e, ?_, ⟨hcont.trans he.exec, he.halted⟩, ?_⟩
      · rw [show (n+1)*(100*((K+1)^2+1)^2+5) =
          n*(100*((K+1)^2+1)^2+5)+(100*((K+1)^2+1)^2+5) by ring]
        omega
      · refine ⟨ho.width, ?_, ?_, ?_, ho.bounded, ho.head, ho.payload.trans hd₁p, ?_, ?_, ?_, ?_⟩
        · simpa [scanResult, hai] using ho.index
        · simpa [scanResult, hai] using ho.value
        · simpa [scanResult, hai] using ho.found
        · intro r hr
          rw [ho.outside r hr]
          have hne : r ≠ 2 := by intro h; subst r; norm_num at hr
          simpa [d₁, TapeStore.setReg, hne] using hcframe r hr
        · intro c' hne
          rw [ho.otherHead c' hne]
          exact hcheadframe c' hne
        · intro r hr
          have hr2 : r ≠ 2 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
          have hz : d₁.reg r = 0 := by
            simp only [d₁,TapeStore.setReg,Function.update_of_ne hr2]
            rw [hcr]
            exact readPost_scratch_zero d₀ (a i) r hr
          have hh := ho.scratch r hr
          rw [hz] at hh
          exact hh.trans (Nat.zero_le _)
        · have hh := ho.remaining
          rw [hd₁7] at hh
          rw [hr7]
          omega
    · have hfound := searchLoop_found (readCurrent b) 7 6 2 8 inp d
        (by omega) s c hc (by rw [hc6]; omega)
      let e := c.store.setReg 8 (c.reg 8+1)
      refine ⟨s+5, e, ?_, hfound, ?_⟩
      · rw [show (n+1)*(100*((K+1)^2+1)^2+5) =
          n*(100*((K+1)^2+1)^2+5)+(100*((K+1)^2+1)^2+5) by ring]
        nlinarith
      · refine ⟨?_, ?_, ?_, ?_, ?_, hchead, ?_, ?_, ?_, ?_, ?_⟩
        · simp [e, TapeStore.setReg, hc0]
        · simp [e, TapeStore.setReg, hc2, scanResult, hai]
        · simp [e, TapeStore.setReg, hc6, scanResult, hai]
        · simp [e, TapeStore.setReg, hc8, scanResult, hai]
        · simpa [AccessBounded, e, TapeStore.setReg] using hcb
        · exact (TapeStore.setReg_payload c.store 8 (c.reg 8+1)).trans hcpd
        · intro r hr
          have hne : r ≠ 8 := by intro h; subst r; norm_num at hr
          simpa [e, TapeStore.setReg, hne] using hcframe r hr
        · exact hcheadframe
        · intro r hr
          have hr8 : r ≠ 8 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
          change Function.update c.reg 8 (c.reg 8+1) r ≤ _
          rw [Function.update_of_ne hr8,hcr,readPost_scratch_zero d₀ (a i) r hr]
          exact Nat.zero_le _
        · simp [e,TapeStore.setReg,hc7,hr7]

#print axioms pivotScan_stops

theorem ScanOutcome.all_bounded {a : ℕ → ℕ} {q i n K M : ℕ} {b : Fin 2} {d e : Store}
    (h : ScanOutcome a q i n K b d e) (hM : 1 ≤ M) (hd : ∀ r,d.reg r ≤ M)
    (hq : q ≤ M) (hi : i+n ≤ M) (hv : ∀ j,j < n → a (i+j) ≤ M) : ∀ r,e.reg r ≤ M := by
  have h0 : e.reg 0 ≤ M := h.width.le.trans hq
  have h2 : e.reg 2 ≤ M := by
    rw [h.index]
    rcases scanResult_spec a i n with hs | hs
    · rw [hs.2.1];exact hi
    · have := hs.2.1;omega
  have h6 : e.reg 6 ≤ M := by
    rw [h.value]
    rcases scanResult_spec a i n with hs | hs
    · rw [hs.1];exact Nat.zero_le M
    · have hj : (scanResult a i n).1-i < n := by have := hs.1;have := hs.2.1;omega
      have hh := hv ((scanResult a i n).1-i) hj
      rw [Nat.add_sub_of_le hs.1] at hh
      exact hs.2.2.1.le.trans hh
  have h7 : e.reg 7 ≤ M := h.remaining.trans (hd 7)
  have h8 : e.reg 8 ≤ M := by
    rw [h.found]
    split <;> omega
  intro r
  fin_cases r <;> first
    | exact h0
    | exact h2
    | exact h6
    | exact h7
    | exact h8
    | exact (h.scratch _ (by decide)).trans (hd _)
    | exact (h.outside _ (by decide)).le.trans (hd _)

theorem pivotScan_table_stops {q m n : ℕ} (b : Fin 2) (inp : Inputs)
    (A : Gaussian.Table (Fin q) m n) (d : Store) (M : ℕ) (hM : 1 ≤ M)
    (hd : ∀ r,d.reg r ≤ M) (hsize : m*n ≤ M)
    (hr0 : d.reg 0 = q) (hr2 : d.reg 2 = 0) (hr6 : d.reg 6 = 0)
    (hr7 : d.reg 7 = m*n) (hr8 : d.reg 8 = 0)
    (hm : BottomMarked d b) (hh : d.bufferHead b ≤ (M+1)^2) (ht : MatrixStored d b A) :
    ∃ (t : ℕ) (e : Store),t ≤ m*n*(100*((M+1)^2+1)^2+5)+1 ∧
      (pivotScan b).Stops inp (d.toCfg (searchLabel 48 0)) t (e.toCfg (searchLabel 48 5)) ∧
      ScanOutcome (flatEntry A) q 0 (m*n) M b d e ∧ (∀ r,e.reg r ≤ M) := by
  have hq : q ≤ M := by rw [← hr0];exact hd 0
  have hb : AccessBounded d ((M+1)^2) := by
    have hMS : M ≤ (M+1)^2 := by nlinarith
    exact ⟨(hd 0).trans hMS,(hd 1).trans hMS,(hd 2).trans hMS,(hd 3).trans hMS,
      (hd 4).trans hMS,(hd 5).trans hMS,(hd 6).trans hMS⟩
  obtain ⟨t,e,htime,hstop,ho⟩ := pivotScan_stops b inp (flatEntry A) q 0 (m*n) M d hq
    (by simpa using hsize) hr0 hr2 hr6 hr7 hr8 hm hb hh (by
      intro j hj
      simpa using ht ⟨j,hj⟩)
  refine ⟨t,e,htime,hstop,ho,ho.all_bounded hM hd hq (by simpa using hsize) ?_⟩
  intro j hj
  rw [Nat.zero_add,flatEntry,dif_pos hj]
  exact (Nat.le_of_lt (Fin.isLt _)).trans hq

#print axioms pivotScan_table_stops

theorem physicalPivot_nonzero {q m n K : ℕ} (O : EncodedGaussian.Operations (Fin q))
    (hz : O.zero.val = 0) (A : Gaussian.Table (Fin q) m n) (b : Fin 2) (d e : Store)
    (h : ScanOutcome (flatEntry A) q 0 (m*n) K b d e) (hf : e.reg 8 = 1) :
    ∃ p : Fin m × Fin n, Gaussian.toMatrix A p.1 p.2 ≠ O.zero ∧
      e.reg 2 = (finProdFinEquiv p).val ∧ e.reg 6 = (Gaussian.toMatrix A p.1 p.2).val := by
  have hn : (scanResult (flatEntry A) 0 (m*n)).2 ≠ 0 := by
    intro he
    have hh := h.found
    rw [he, if_pos rfl, hf] at hh
    omega
  rcases scanResult_spec (flatEntry A) 0 (m*n) with hs | hs
  · exact (hn hs.1).elim
  · let k : Fin (m*n) := ⟨(scanResult (flatEntry A) 0 (m*n)).1, by simpa using hs.2.1⟩
    let p : Fin m × Fin n := finProdFinEquiv.symm k
    have hflat : flatEntry A k.val = (Gaussian.toMatrix A p.1 p.2).val := by
      rw [flatEntry, dif_pos k.isLt]
    refine ⟨p, ?_, ?_, ?_⟩
    · intro he
      have hh := congrArg Fin.val he
      rw [hz, ← hflat] at hh
      exact hn (hs.2.2.1.trans hh)
    · have heq : finProdFinEquiv p = k := finProdFinEquiv.apply_symm_apply k
      rw [heq]
      exact h.index
    · exact h.value.trans (hs.2.2.1.trans hflat)

theorem physicalPivot_zero {q m n K : ℕ} (O : EncodedGaussian.Operations (Fin q))
    (hz : O.zero.val = 0) (A : Gaussian.Table (Fin q) m n) (b : Fin 2) (d e : Store)
    (h : ScanOutcome (flatEntry A) q 0 (m*n) K b d e) (hf : e.reg 8 = 0) :
    Gaussian.toMatrix A = fun _ _ => O.zero := by
  have hn : (scanResult (flatEntry A) 0 (m*n)).2 = 0 := by
    by_contra hn
    have hh := h.found
    rw [if_neg hn, hf] at hh
    omega
  rcases scanResult_spec (flatEntry A) 0 (m*n) with hs | hs
  · funext i j
    apply Fin.ext
    let k : Fin (m*n) := finProdFinEquiv (i,j)
    have hh := hs.2.2 k.val (by omega) (by simpa using k.isLt)
    have hflat : flatEntry A k.val = (Gaussian.toMatrix A i j).val := by
      rw [flatEntry, dif_pos k.isLt]
      change (Gaussian.toMatrix A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).val = _
      rw [show finProdFinEquiv.symm k = (i,j) from finProdFinEquiv.symm_apply_apply (i,j)]
    rw [hflat] at hh
    exact hh.trans hz.symm
  · exact (hs.2.2.2.1 hn).elim

theorem binary_zeroIndex_val (ell : ℕ) : (PolynomialStretch.BinaryField.zeroIndex ell).val = 0 := by
  rw [PolynomialStretch.BinaryField.zeroIndex, PolynomialStretch.BinaryPolynomial.indexEquiv_inverse_value]
  simp [PolynomialStretch.BinaryField.zero]

/-- Nonzero pivots returned by the physical scan discharge the exact encoded
Schur rank reduction; no pivot certificate is chosen noncomputably. -/
theorem encoded_schur_rank_step {q m n : ℕ} {F : Type*} [Field F] [DecidableEq F]
    {O : EncodedGaussian.Operations (Fin q)} {decode : Fin q → F}
    (h : EncodedGaussian.Interpretation O decode)
    (A : Gaussian.Table (Fin q) (m+1) (n+1)) (p : Fin (m+1) × Fin (n+1))
    (hp : Gaussian.toMatrix A p.1 p.2 ≠ O.zero) :
    (Gaussian.toMatrix (EncodedGaussian.mapTable decode A)).rank =
      (Gaussian.toMatrix (EncodedGaussian.mapTable decode (EncodedGaussian.schur O A p))).rank+1 := by
  rw [EncodedGaussian.schur_decode h]
  apply Gaussian.rank_eq_schur_add_one
  rw [EncodedGaussian.toMatrix_mapTable]
  intro he
  exact hp (h.injective (he.trans h.zero.symm))

theorem high_ne_low (r : Fin 64) (hr : 9 ≤ r.val) (k : Fin 64) (hk : k.val < 9) :
    r ≠ k := by intro h; subst r; omega

def fetch (b : Fin 2) (address dest : Fin 64) : TapeProgram 64 2 70 :=
  TapeProgram.seq (TapeMacros.copy address 2 4)
    (TapeProgram.seq (readCurrent b) (TapeMacros.copy 6 dest 4))

def fetchPost (d : Store) (address dest : Fin 64) (v : ℕ) : Store :=
  (readPost (d.setReg 2 (d.reg address)) v).setReg dest v

theorem fetchPost_bounded (d : Store) (address dest : Fin 64) (v M : ℕ)
    (hM : ∀ r, d.reg r ≤ M) (hv : v ≤ M) :
    ∀ r, (fetchPost d address dest v).reg r ≤ M := by
  intro r
  simp only [fetchPost, readPost, TapeStore.setReg, Function.update_apply]
  split_ifs <;> first | exact hv | exact Nat.zero_le M | exact hM address | exact hM r

/-- Three real finite routines fetch one addressed matrix cell into a scalar
register. Every multiplication, reset and physical traversal is charged. -/
theorem fetch_stops (b : Fin 2) (address dest : Fin 64)
    (ha : 9 ≤ address.val) (hd : 9 ≤ dest.val) (inp : Inputs) (d : Store) (M v : ℕ)
    (hm : BottomMarked d b) (hM : ∀ r, d.reg r ≤ M) (hh : d.bufferHead b ≤ M)
    (hv : ThermometerAt d b (entryOffset (d.reg address) (d.reg 0)) (d.reg 0) v) :
    ∃ t e, t ≤ 120*(M+1)^2 ∧
      (fetch b address dest).Stops inp (d.toCfg (fetch b address dest).entry) t e ∧
      e.reg = (fetchPost d address dest v).reg ∧
      e.bufferHead = Function.update d.bufferHead b
        (entryOffset (d.reg address) (d.reg 0)+d.reg 0) ∧
      TapeStore.SamePayload e.store d := by
  have ha2 : address ≠ 2 := high_ne_low address ha 2 (by decide)
  have ha4 : address ≠ 4 := high_ne_low address ha 4 (by decide)
  have hd1 : dest ≠ 1 := high_ne_low dest hd 1 (by decide)
  have hd2 : dest ≠ 2 := high_ne_low dest hd 2 (by decide)
  have hd3 : dest ≠ 3 := high_ne_low dest hd 3 (by decide)
  have hd4 : dest ≠ 4 := high_ne_low dest hd 4 (by decide)
  have hd5 : dest ≠ 5 := high_ne_low dest hd 5 (by decide)
  have hd6 : dest ≠ 6 := high_ne_low dest hd 6 (by decide)
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops address (2 : Fin 64) 4
    ha2 ha4 (by decide) inp d
  have hcr : c.reg = ((d.setReg 2 (d.reg address)).setReg 4 0).reg := congrArg TapeStore.reg hcs
  have hcp : TapeStore.SamePayload c.store d := by
    rw [hcs]
    exact (TapeStore.setReg_payload _ 4 0).trans (TapeStore.setReg_payload d 2 (d.reg address))
  have hcBound : AccessBounded c.store M := by
    simp [AccessBounded, hcr, TapeStore.setReg, hM]
  have hct : ThermometerAt c.store b (entryOffset (c.reg 2) (c.reg 0)) (c.reg 0) v := by
    have hc2 : c.reg 2 = d.reg address := by rw [hcr]; simp [TapeStore.setReg]
    have hc0 : c.reg 0 = d.reg 0 := by rw [hcr]; simp [TapeStore.setReg]
    rw [hc2, hc0]
    exact hv.of_payload hcp
  obtain ⟨s, f, hs, hf, hfr, hfh, hfp⟩ := readCurrent_stops b inp c.store M v
    (hm.of_payload hcp) hcBound (by rw [hcs]; exact hh) hct
  obtain ⟨e, he, hes⟩ := TapeMacros.copy_stops (6 : Fin 64) dest 4
    (Ne.symm hd6) (by decide) hd4 inp f.store
  have her : e.reg = ((f.store.setReg dest (f.reg 6)).setReg 4 0).reg := congrArg TapeStore.reg hes
  have hfpd : TapeStore.SamePayload f.store d := hfp.trans hcp
  have hep : TapeStore.SamePayload e.store f.store := by
    rw [hes]
    exact (TapeStore.setReg_payload _ 4 0).trans (TapeStore.setReg_payload f.store dest (f.reg 6))
  have hf6 : f.reg 6 = v := by rw [hfr]; simp [readPost, TapeStore.setReg]
  have hf4 : f.reg 4 = 0 := by rw [hfr]; simp [readPost, TapeStore.setReg]
  have hfd : f.reg dest = d.reg dest := by
    rw [hfr]
    simp [readPost, TapeStore.setReg, hcr, hd1, hd2, hd3, hd4, hd5, hd6]
  have hall := hc.seq (hf.seq he)
  refine ⟨_, _, ?_, hall, ?_, ?_, hep.trans hfpd⟩
  · dsimp only [TapeCfg.store]
    rw [hf6, hf4, hfd]
    have hvM := hv.1.trans (hM 0)
    have h2 := hM 2
    have h4 := hM 4
    have haM := hM address
    have hdM := hM dest
    nlinarith
  · change e.reg = _
    rw [her]
    simp only [hfr, hcr, fetchPost, readPost, TapeStore.setReg]
    funext r
    by_cases hdest : r = dest
    · subst r
      simp [hd1, hd2, hd3, hd4, hd5, hd6]
    · by_cases h6 : r = 6
      · subst r; simp [Ne.symm hd6]
      · by_cases h5 : r = 5
        · subst r; simp [Ne.symm hd5]
        · by_cases h4 : r = 4
          · subst r; simp [Ne.symm hd4]
          · by_cases h3 : r = 3
            · subst r; simp [Ne.symm hd3]
            · by_cases h2 : r = 2
              · subst r; simp [Ne.symm hd2]
              · by_cases h1 : r = 1
                · subst r; simp [Ne.symm hd1]
                · simp [Function.update, hdest, h1, h2, h3, h4, h5, h6]
  · change e.bufferHead = _
    rw [show e.bufferHead = f.bufferHead from congrArg TapeStore.bufferHead hes, hfh]
    simp only [hcr, TapeStore.setReg]
    rw [show c.bufferHead = d.bufferHead from congrArg TapeStore.bufferHead hcs]
    simp

#print axioms fetch_stops

def writeCurrent (b : Fin 2) (address : Fin 64) : TapeProgram 64 2 60 :=
  TapeProgram.seq (TapeMacros.copy address 2 4)
    (TapeProgram.seq (TapeMacros.copy 0 1 4) (writeEntry 2 1 3 4 5 6 b))

/-- Physical addressed write of the computed Schur entry. The finite code
reconstructs the width and computes every offset before moving the buffer head. -/
theorem writeCurrent_stops (b : Fin 2) (address : Fin 64) (ha : 9 ≤ address.val)
    (inp : Inputs) (d : Store) (M : ℕ) (hm : BottomMarked d b)
    (hM : ∀ r, d.reg r ≤ M) (hh : d.bufferHead b ≤ M) (hv : d.reg 6 ≤ d.reg 0) :
    ∃ t e, t ≤ 100*(M+1)^2 ∧
      (writeCurrent b address).Stops inp (d.toCfg (writeCurrent b address).entry) t e ∧
      e.reg = (readPost (d.setReg 2 (d.reg address)) 0).reg ∧
      EntryWritten d e.store b (entryOffset (d.reg address) (d.reg 0)) (d.reg 0) (d.reg 6) := by
  have ha2 : address ≠ 2 := high_ne_low address ha 2 (by decide)
  have ha4 : address ≠ 4 := high_ne_low address ha 4 (by decide)
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops address (2 : Fin 64) 4
    ha2 ha4 (by decide) inp d
  have hcr : c.reg = ((d.setReg 2 (d.reg address)).setReg 4 0).reg := congrArg TapeStore.reg hcs
  obtain ⟨f, hf, hfs⟩ := TapeMacros.copy_stops (0 : Fin 64) 1 4
    (by decide) (by decide) (by decide) inp c.store
  have hfr : f.reg = ((c.store.setReg 1 (c.reg 0)).setReg 4 0).reg := congrArg TapeStore.reg hfs
  have hcp : TapeStore.SamePayload c.store d := by
    rw [hcs]
    exact (TapeStore.setReg_payload _ 4 0).trans (TapeStore.setReg_payload d 2 (d.reg address))
  have hfp : TapeStore.SamePayload f.store d := by
    rw [hfs]
    exact ((TapeStore.setReg_payload _ 4 0).trans (TapeStore.setReg_payload c.store 1 (c.reg 0))).trans hcp
  have hfh : f.bufferHead = d.bufferHead := by
    change f.store.bufferHead = d.bufferHead
    rw [hfs, hcs]
    rfl
  have hf2 : f.reg 2 = d.reg address := by rw [hfr]; simp [TapeStore.setReg, hcr]
  have hf1 : f.reg 1 = d.reg 0 := by rw [hfr]; simp [TapeStore.setReg, hcr]
  have hf6 : f.reg 6 = d.reg 6 := by rw [hfr]; simp [TapeStore.setReg, hcr]
  have hfv : f.reg 6 ≤ f.reg 1 := by simpa only [hf1, hf6] using hv
  obtain ⟨s, e, hs, he, her, hew⟩ := writeEntry_stops
    (2 : Fin 64) 1 3 4 5 6 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) b inp f.store
      (hm.of_payload hfp).marked hfv
  have hbound : entryAccessBound f.store 2 1 3 4 5 b ≤ 50*(M+1)^2 := by
    apply entryAccessBound_le f.store 2 1 3 4 5 b M
    · simpa only [hf2] using hM address
    · simpa only [hf1] using hM 0
    · simpa [hfr, hcr, TapeStore.setReg] using hM 3
    · simp [hfr, TapeStore.setReg]
    · simpa [hfr, hcr, TapeStore.setReg] using hM 5
    · simpa only [hfh] using hh
  have hall := hc.seq (hf.seq he)
  refine ⟨_, _, ?_, hall, ?_, ?_⟩
  · dsimp only [TapeCfg.store]
    have hc1 : c.reg 1 = d.reg 1 := by rw [hcr]; simp [TapeStore.setReg]
    have hc4 : c.reg 4 = 0 := by rw [hcr]; simp [TapeStore.setReg]
    have hc0 : c.reg 0 = d.reg 0 := by rw [hcr]; simp [TapeStore.setReg]
    rw [hc1, hc4, hc0]
    have h0 := hM 0
    have h1 := hM 1
    have h2 := hM 2
    have h4 := hM 4
    have haM := hM address
    nlinarith
  · change e.reg = _
    rw [her]
    simp only [hfr, hcr, readPost, TapeStore.setReg]
    funext r
    by_cases h6 : r = 6
    · subst r; simp
    · by_cases h5 : r = 5
      · subst r; simp
      · by_cases h4 : r = 4
        · subst r; simp
        · by_cases h3 : r = 3
          · subst r; simp
          · by_cases h1 : r = 1
            · subst r; simp
            · simp [Function.update, h1, h3, h4, h5, h6]
  · change EntryWritten d e.store b _ _ _
    change EntryWritten f.store e.store b (entryOffset (f.reg 2) (f.reg 1)) (f.reg 1) (f.reg 6) at hew
    rw [hf1, hf2, hf6] at hew
    constructor
    · exact hew.roHead.trans hfp.roHead
    · exact hew.output.trans hfp.output
    · simpa [hfh] using hew.head
    · intro c' k
      rw [hew.symbol, hfp.symbol]

#print axioms writeCurrent_stops

/-- Concrete setup expected by the independently implemented finite field
source routines. These are scalar unary values, never a packed matrix. -/
def FieldSetup (ell : ℕ) (h : 0 < ell) (d : Store) : Prop :=
  d.reg 0 = 2^ell ∧ d.reg 36 = 2^(2*ell) ∧ d.reg 37 = 3*ell+1 ∧
    d.reg 38 = 2^ell+(PolynomialStretch.BinaryPolynomial.selectedIndex ell h).val

def Protected (r : Fin 64) : Prop :=
  r = 0 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 16 ∨
    r = 36 ∨ r = 37 ∨ r = 38 ∨ 40 ≤ r.val

structure ScalarOutcome (d e : Store) (out : Fin 64) (v M : ℕ) : Prop where
  value : e.reg out = v
  frame : ∀ r, Protected r → e.reg r = d.reg r
  bounded : ∀ r, e.reg r ≤ M
  payload : TapeStore.SamePayload e d
  heads : e.bufferHead = d.bufferHead

theorem ScalarOutcome.setup {ell : ℕ} {h : 0 < ell} {d e : Store} {out : Fin 64} {v M : ℕ}
    (hs : ScalarOutcome d e out v M) (hd : FieldSetup ell h d) : FieldSetup ell h e := by
  rcases hd with ⟨h0,h36,h37,h38⟩
  refine ⟨(hs.frame 0 (by simp [Protected])).trans h0,
    (hs.frame 36 (by simp [Protected])).trans h36,
    (hs.frame 37 (by simp [Protected])).trans h37,
    (hs.frame 38 (by simp [Protected])).trans h38⟩

abbrev ScalarFunction := (ell : ℕ) → (h : 0 < ell) →
  Fin (2^ell) → Fin (2^ell) → Fin (2^ell)

/-- An explicit contract for an actual finite source subroutine. P and its
label count are fixed outside the ell quantifier; this is a conditional source
interface, not an assertion that the required field implementations exist. -/
structure ScalarContract {L : ℕ} (P : TapeProgram 64 2 L) (f : ScalarFunction)
    (left right out : Fin 64) (C k : ℕ) : Prop where
  stops : ∀ (ell : ℕ) (h : 0 < ell) (inp : Inputs) (d : Store) (M : ℕ),
    FieldSetup ell h d → (∀ r, d.reg r ≤ M) →
    ∀ (a b : Fin (2^ell)), d.reg left = a.val → d.reg right = b.val →
    ∃ t e, t ≤ C*(M+1)^k ∧ P.Stops inp (d.toCfg P.entry) t e ∧
      ScalarOutcome d e.store out (f ell h a b).val M

def multiplyFunction : ScalarFunction := fun ell h =>
  (PolynomialStretch.BinaryField.indexOperations ell h).mul

def subtractFunction : ScalarFunction := fun ell h =>
  (PolynomialStretch.BinaryField.indexOperations ell h).sub

def schurArithmetic {L₁ L₂ L₃ : ℕ} (mul₁ : TapeProgram 64 2 L₁)
    (mul₂ : TapeProgram 64 2 L₂) (sub : TapeProgram 64 2 L₃) : TapeProgram 64 2 (L₁+(L₂+L₃)) :=
  TapeProgram.seq mul₁ (TapeProgram.seq mul₂ sub)

/-- Composition of three actual finite field programs computes precisely one
Schur expression, retaining the pivot inverse and Gaussian loop state. -/
theorem schurArithmetic_stops {L₁ L₂ L₃ : ℕ}
    (mul₁ : TapeProgram 64 2 L₁) (mul₂ : TapeProgram 64 2 L₂) (sub : TapeProgram 64 2 L₃)
    (C₁ k₁ C₂ k₂ C₃ k₃ : ℕ)
    (hm₁ : ScalarContract mul₁ multiplyFunction 15 13 17 C₁ k₁)
    (hm₂ : ScalarContract mul₂ multiplyFunction 17 16 18 C₂ k₂)
    (hs : ScalarContract sub subtractFunction 14 18 6 C₃ k₃)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (d : Store) (M : ℕ)
    (hsetup : FieldSetup ell h d) (hM : ∀ r, d.reg r ≤ M)
    (x y z aInv : Fin (2^ell))
    (hx : d.reg 14 = x.val) (hy : d.reg 15 = y.val)
    (hz : d.reg 16 = z.val) (ha : d.reg 13 = aInv.val) :
    ∃ t e, t ≤ C₁*(M+1)^k₁+C₂*(M+1)^k₂+C₃*(M+1)^k₃+2 ∧
      (schurArithmetic mul₁ mul₂ sub).Stops inp
        (d.toCfg (schurArithmetic mul₁ mul₂ sub).entry) t e ∧
      ScalarOutcome d e.store 6
        ((PolynomialStretch.BinaryField.indexOperations ell h).sub x
          ((PolynomialStretch.BinaryField.indexOperations ell h).mul
            ((PolynomialStretch.BinaryField.indexOperations ell h).mul y aInv) z)).val M := by
  obtain ⟨t₁,c,ht₁,hc,hco⟩ := hm₁.stops ell h inp d M hsetup hM y aInv hy ha
  have hc16 : c.store.reg 16 = z.val :=
    (hco.frame 16 (by simp [Protected])).trans hz
  obtain ⟨t₂,f,ht₂,hf,hfo⟩ := hm₂.stops ell h inp c.store M (hco.setup hsetup) hco.bounded
    (multiplyFunction ell h y aInv) z hco.value hc16
  have hf14 : f.store.reg 14 = x.val :=
    (hfo.frame 14 (by simp [Protected])).trans
      ((hco.frame 14 (by simp [Protected])).trans hx)
  obtain ⟨t₃,e,ht₃,he,heo⟩ := hs.stops ell h inp f.store M (hfo.setup (hco.setup hsetup))
    hfo.bounded x (multiplyFunction ell h (multiplyFunction ell h y aInv) z) hf14 hfo.value
  have hall := hc.seq (hf.seq he)
  refine ⟨_, _, by omega, hall, ?_⟩
  refine ⟨heo.value, ?_, heo.bounded, heo.payload.trans (hfo.payload.trans hco.payload), ?_⟩
  · intro r hr
    exact (heo.frame r hr).trans ((hfo.frame r hr).trans (hco.frame r hr))
  · exact heo.heads.trans (hfo.heads.trans hco.heads)

#print axioms schurArithmetic_stops

theorem multiply_source_contract (r : Fin 27 → Fin 64) (hr : Function.Injective r)
    (left right out : Fin 64) (h0 : r 0 = left) (h1 : r 1 = right) (h20 : r 20 = out)
    (h3 : r 3 = 38) (h19 : r 19 = 37) (h23 : r 23 = 0) (h24 : r 24 = 36)
    (hframe : ∀ p, Protected p →
      (∃ i : Fin 27, (i < 2 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24) ∧ r i = p) ∨
      (∀ i, p ≠ r i)) :
    ScalarContract (SourceFieldArithmetic.multiply r) multiplyFunction left right out 10000 6 := by
  constructor
  intro ell h inp d M hs hd a b ha hb
  rcases hs with ⟨hq,hQ,hN,hm⟩
  have hM : 1 ≤ M := by
    have hp : 0 < 2^ell := pow_pos (by decide) ell
    have hbnd := hd 0
    omega
  obtain ⟨t,e,ht,he,_,hans,hin,hout,hbound,htape⟩ := SourceFieldArithmetic.multiply_stops
    r hr inp ell h (PolynomialStretch.BinaryPolynomial.selectedIndex ell h) a b M hM d hd
      (by simpa only [h0] using ha) (by simpa only [h1] using hb)
      (by simpa only [h3] using hm) (by simpa only [h19] using hN)
      (by simpa only [h23] using hq) (by simpa only [h24] using hQ)
  refine ⟨t,e,ht,he,?_⟩
  have hro : e.store.roHead = d.roHead := congrArg Prod.fst htape
  have houtput : e.store.output = d.output := congrArg (fun x => x.2.1) htape
  have hbuffer : e.store.bufferTape = d.bufferTape := congrArg (fun x => x.2.2.1) htape
  have hheads : e.store.bufferHead = d.bufferHead := congrArg (fun x => x.2.2.2) htape
  refine ⟨?_,?_,hbound,⟨hro,houtput,?_⟩,hheads⟩
  · simpa only [h20, multiplyFunction, PolynomialStretch.BinaryField.indexOperations] using hans
  · intro p hp
    rcases hframe p hp with ⟨i,hi,heq⟩ | hf
    · simpa only [heq] using hin i hi
    · exact hout p hf
  · intro b k
    rw [hbuffer]

/-- Two concrete embeddings of the checked 374-label multiplication program.
All mapped scratch registers are below 40, outside the Gaussian loop state. -/
def mulLayout (left right out : Fin 64) (i : Fin 27) : Fin 64 :=
  #v[left,right,1,38,2,3,4,5,6,7,8,9,10,11,19,20,21,22,23,37,out,24,25,0,36,26,27][i.val]

set_option maxRecDepth 10000 in
theorem mulLayout₁_injective : Function.Injective (mulLayout 15 13 17) := by decide

set_option maxRecDepth 10000 in
theorem mulLayout₂_injective : Function.Injective (mulLayout 17 16 18) := by decide

set_option maxRecDepth 10000 in
theorem mulLayout₁_frame : ∀ p, Protected p →
    (∃ i : Fin 27, (i < 2 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24) ∧ mulLayout 15 13 17 i = p) ∨
    (∀ i, p ≠ mulLayout 15 13 17 i) := by unfold Protected; decide

set_option maxRecDepth 10000 in
theorem mulLayout₂_frame : ∀ p, Protected p →
    (∃ i : Fin 27, (i < 2 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24) ∧ mulLayout 17 16 18 i = p) ∨
    (∀ i, p ≠ mulLayout 17 16 18 i) := by unfold Protected; decide

def schurMultiply₁ : TapeProgram 64 2 374 := SourceFieldArithmetic.multiply (mulLayout 15 13 17)
def schurMultiply₂ : TapeProgram 64 2 374 := SourceFieldArithmetic.multiply (mulLayout 17 16 18)

theorem schurMultiply₁_contract : ScalarContract schurMultiply₁ multiplyFunction 15 13 17 10000 6 :=
  multiply_source_contract (mulLayout 15 13 17) mulLayout₁_injective 15 13 17
    rfl rfl rfl rfl rfl rfl rfl mulLayout₁_frame

theorem schurMultiply₂_contract : ScalarContract schurMultiply₂ multiplyFunction 17 16 18 10000 6 :=
  multiply_source_contract (mulLayout 17 16 18) mulLayout₂_injective 17 16 18
    rfl rfl rfl rfl rfl rfl rfl mulLayout₂_frame

#print axioms schurMultiply₁_contract
#print axioms schurMultiply₂_contract

theorem fetchPost_frame (d : Store) (address dest : Fin 64) (v : ℕ) (r : Fin 64)
    (hr : r = 0 ∨ 9 ≤ r.val) (hne : r ≠ dest) :
    (fetchPost d address dest v).reg r = d.reg r := by
  simp only [fetchPost, TapeStore.setReg, Function.update_of_ne hne]
  rcases hr with rfl | hr
  · simp [readPost, TapeStore.setReg]
  · rw [readPost_outside _ _ r hr]
    simp [TapeStore.setReg, high_ne_low r hr 2 (by decide)]

theorem fetchPost_setup (ell : ℕ) (h : 0 < ell) (d : Store) (address dest : Fin 64) (v : ℕ)
    (hs : FieldSetup ell h d) (hd0 : dest ≠ 0) (hd36 : dest ≠ 36)
    (hd37 : dest ≠ 37) (hd38 : dest ≠ 38) : FieldSetup ell h (fetchPost d address dest v) := by
  rcases hs with ⟨h0,h36,h37,h38⟩
  exact ⟨(fetchPost_frame d address dest v 0 (Or.inl rfl) (Ne.symm hd0)).trans h0,
    (fetchPost_frame d address dest v 36 (Or.inr (by decide)) (Ne.symm hd36)).trans h36,
    (fetchPost_frame d address dest v 37 (Or.inr (by decide)) (Ne.symm hd37)).trans h37,
    (fetchPost_frame d address dest v 38 (Or.inr (by decide)) (Ne.symm hd38)).trans h38⟩

theorem entryEnd_le (index q M : ℕ) (hi : index ≤ M) (hq : q ≤ M) :
    entryOffset index q+q ≤ (M+1)^2 := by
  have hp := Nat.mul_le_mul hi hq
  unfold entryOffset
  nlinarith

def fetchSchur (b : Fin 2) : TapeProgram 64 2 210 :=
  TapeProgram.seq (fetch b 9 14) (TapeProgram.seq (fetch b 10 15) (fetch b 11 16))

structure FetchSchurOutcome (ell : ℕ) (h : 0 < ell) (b : Fin 2) (d e : Store)
    (x y z : Fin (2^ell)) (M : ℕ) : Prop where
  setup : FieldSetup ell h e
  x : e.reg 14 = x.val
  y : e.reg 15 = y.val
  z : e.reg 16 = z.val
  inverse : e.reg 13 = d.reg 13
  target : e.reg 12 = d.reg 12
  bounded : ∀ r, e.reg r ≤ M
  head : e.bufferHead b ≤ (M+1)^2
  otherHead : ∀ c, c ≠ b → e.bufferHead c = d.bufferHead c
  payload : TapeStore.SamePayload e d
  caller : ∀ r, 40 ≤ r.val → e.reg r = d.reg r

theorem fetchSchur_stops (b : Fin 2) (ell : ℕ) (h : 0 < ell) (inp : Inputs)
    (d : Store) (M : ℕ) (hs : FieldSetup ell h d) (hM : ∀ r, d.reg r ≤ M)
    (hh : d.bufferHead b ≤ (M+1)^2) (hm : BottomMarked d b)
    (x y z : Fin (2^ell))
    (hx : ThermometerAt d b (entryOffset (d.reg 9) (d.reg 0)) (d.reg 0) x.val)
    (hy : ThermometerAt d b (entryOffset (d.reg 10) (d.reg 0)) (d.reg 0) y.val)
    (hz : ThermometerAt d b (entryOffset (d.reg 11) (d.reg 0)) (d.reg 0) z.val) :
    ∃ t e, t ≤ 360*((M+1)^2+1)^2+2 ∧
      (fetchSchur b).Stops inp (d.toCfg (fetchSchur b).entry) t e ∧
      FetchSchurOutcome ell h b d e.store x y z M := by
  have hMS : M ≤ (M+1)^2 := by nlinarith
  have hxM : x.val ≤ M := hx.1.trans (hM 0)
  have hyM : y.val ≤ M := hy.1.trans (hM 0)
  have hzM : z.val ≤ M := hz.1.trans (hM 0)
  obtain ⟨t₁,c,ht₁,hc,hcr,hch,hcp⟩ := fetch_stops b 9 14 (by decide) (by decide) inp d
    ((M+1)^2) x.val hm (fun r => (hM r).trans hMS) hh hx
  have hcb : ∀ r, c.reg r ≤ M := by
    rw [hcr]
    exact fetchPost_bounded d 9 14 x.val M hM hxM
  have hcf (r : Fin 64) (hr : r = 0 ∨ 9 ≤ r.val) (hne : r ≠ 14) : c.reg r = d.reg r :=
    (congrFun hcr r).trans (fetchPost_frame d 9 14 x.val r hr hne)
  have hcs : FieldSetup ell h c.store := by
    change FieldSetup ell h { c.store with reg := c.reg }
    rw [hcr]
    exact fetchPost_setup ell h d 9 14 x.val hs (by decide) (by decide) (by decide) (by decide)
  have hcHead : c.bufferHead b ≤ (M+1)^2 := by
    rw [hch]
    simp only [Function.update_self]
    exact entryEnd_le _ _ M (hM 9) (hM 0)
  have hcy : ThermometerAt c.store b (entryOffset (c.reg 10) (c.reg 0)) (c.reg 0) y.val := by
    rw [hcf 10 (Or.inr (by decide)) (by decide), hcf 0 (Or.inl rfl) (by decide)]
    exact hy.of_payload hcp
  obtain ⟨t₂,f,ht₂,hf,hfr,hfh,hfp⟩ := fetch_stops b 10 15 (by decide) (by decide) inp c.store
    ((M+1)^2) y.val (hm.of_payload hcp) (fun r => (hcb r).trans hMS) hcHead hcy
  have hfb : ∀ r, f.reg r ≤ M := by
    rw [hfr]
    exact fetchPost_bounded c.store 10 15 y.val M hcb hyM
  have hff (r : Fin 64) (hr : r = 0 ∨ 9 ≤ r.val) (hne : r ≠ 15) : f.reg r = c.reg r :=
    (congrFun hfr r).trans (fetchPost_frame c.store 10 15 y.val r hr hne)
  have hfs : FieldSetup ell h f.store := by
    change FieldSetup ell h { f.store with reg := f.reg }
    rw [hfr]
    exact fetchPost_setup ell h c.store 10 15 y.val hcs (by decide) (by decide) (by decide) (by decide)
  have hfHead : f.bufferHead b ≤ (M+1)^2 := by
    rw [hfh]
    simp only [Function.update_self]
    exact entryEnd_le _ _ M (hcb 10) (hcb 0)
  have hfpd := hfp.trans hcp
  have hfz : ThermometerAt f.store b (entryOffset (f.reg 11) (f.reg 0)) (f.reg 0) z.val := by
    rw [hff 11 (Or.inr (by decide)) (by decide), hff 0 (Or.inl rfl) (by decide),
      hcf 11 (Or.inr (by decide)) (by decide), hcf 0 (Or.inl rfl) (by decide)]
    exact hz.of_payload hfpd
  obtain ⟨t₃,e,ht₃,he,her,heh,hep⟩ := fetch_stops b 11 16 (by decide) (by decide) inp f.store
    ((M+1)^2) z.val (hm.of_payload hfpd) (fun r => (hfb r).trans hMS) hfHead hfz
  have hef (r : Fin 64) (hr : r = 0 ∨ 9 ≤ r.val) (hne : r ≠ 16) : e.reg r = f.reg r :=
    (congrFun her r).trans (fetchPost_frame f.store 11 16 z.val r hr hne)
  have hall := hc.seq (hf.seq he)
  refine ⟨_,_,by omega,hall,?_⟩
  change FetchSchurOutcome ell h b d e.store x y z M
  constructor
  · change FieldSetup ell h { e.store with reg := e.reg }
    rw [her]
    exact fetchPost_setup ell h f.store 11 16 z.val hfs (by decide) (by decide) (by decide) (by decide)
  · change e.reg 14 = x.val
    rw [hef 14 (Or.inr (by decide)) (by decide), hff 14 (Or.inr (by decide)) (by decide), hcr]
    simp [fetchPost, TapeStore.setReg]
  · change e.reg 15 = y.val
    rw [hef 15 (Or.inr (by decide)) (by decide), hfr]
    simp [fetchPost, TapeStore.setReg]
  · change e.reg 16 = z.val
    rw [her]
    simp [fetchPost, TapeStore.setReg]
  · exact (hef 13 (Or.inr (by decide)) (by decide)).trans
      ((hff 13 (Or.inr (by decide)) (by decide)).trans (hcf 13 (Or.inr (by decide)) (by decide)))
  · exact (hef 12 (Or.inr (by decide)) (by decide)).trans
      ((hff 12 (Or.inr (by decide)) (by decide)).trans (hcf 12 (Or.inr (by decide)) (by decide)))
  · change ∀ r, e.reg r ≤ M
    rw [her]
    exact fetchPost_bounded f.store 11 16 z.val M hfb hzM
  · change e.bufferHead b ≤ (M+1)^2
    rw [heh]
    simp only [Function.update_self]
    exact entryEnd_le _ _ M (hfb 11) (hfb 0)
  · intro c' hne
    change e.bufferHead c' = d.bufferHead c'
    rw [heh, Function.update_of_ne hne]
    change f.bufferHead c' = d.bufferHead c'
    rw [hfh, Function.update_of_ne hne]
    change c.bufferHead c' = d.bufferHead c'
    rw [hch, Function.update_of_ne hne]
  · exact hep.trans hfpd
  · intro r hr
    have hr9 : r = 0 ∨ 9 ≤ r.val := Or.inr (by omega)
    have h14 : r ≠ 14 := by intro he; subst r; norm_num at hr
    have h15 : r ≠ 15 := by intro he; subst r; norm_num at hr
    have h16 : r ≠ 16 := by intro he; subst r; norm_num at hr
    exact (hef r hr9 h16).trans ((hff r hr9 h15).trans (hcf r hr9 h14))

#print axioms fetchSchur_stops

def schurEntry {L : ℕ} (sub : TapeProgram 64 2 L) (input output : Fin 2) :
    TapeProgram 64 2 (210+((374+(374+L))+60)) :=
  TapeProgram.seq (fetchSchur input)
    (TapeProgram.seq (schurArithmetic schurMultiply₁ schurMultiply₂ sub) (writeCurrent output 12))

theorem accessPost_bounded (d : Store) (address : Fin 64) (v M : ℕ)
    (hM : ∀ r, d.reg r ≤ M) (hv : v ≤ M) :
    ∀ r, (readPost (d.setReg 2 (d.reg address)) v).reg r ≤ M := by
  intro r
  simp only [readPost, TapeStore.setReg, Function.update_apply]
  split_ifs <;> first | exact hv | exact Nat.zero_le M | exact hM address | exact hM r

structure SchurCellState (ell : ℕ) (h : 0 < ell) (input output : Fin 2) (e : Store) (M : ℕ) : Prop where
  setup : FieldSetup ell h e
  bounded : ∀ r, e.reg r ≤ M
  inputHead : e.bufferHead input ≤ (M+1)^2
  outputHead : e.bufferHead output ≤ (M+1)^2
  inputMarked : BottomMarked e input
  outputMarked : BottomMarked e output

/-- Complete physical Schur-cell update. All three input cells are actually
read, both multiplications are the concrete checked 374-label source program,
and the result is actually written into the second thermometer buffer. Only
the subtraction source routine is still a contracted finite-program parameter. -/
theorem schurEntry_stops {L : ℕ} (sub : TapeProgram 64 2 L) (C k : ℕ)
    (hsub : ScalarContract sub subtractFunction 14 18 6 C k)
    (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (d : Store) (M : ℕ)
    (hs : FieldSetup ell h d) (hM : ∀ r, d.reg r ≤ M)
    (hhI : d.bufferHead input ≤ (M+1)^2) (hhO : d.bufferHead output ≤ (M+1)^2)
    (hmI : BottomMarked d input) (hmO : BottomMarked d output)
    (x y z aInv : Fin (2^ell)) (hInv : d.reg 13 = aInv.val)
    (hx : ThermometerAt d input (entryOffset (d.reg 9) (d.reg 0)) (d.reg 0) x.val)
    (hy : ThermometerAt d input (entryOffset (d.reg 10) (d.reg 0)) (d.reg 0) y.val)
    (hz : ThermometerAt d input (entryOffset (d.reg 11) (d.reg 0)) (d.reg 0) z.val) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 (210+((374+(374+L))+60))) (beforeWrite : Store),
      t ≤ 460*((M+1)^2+1)^2+20000*(M+1)^6+C*(M+1)^k+6 ∧
      (schurEntry sub input output).Stops inp (d.toCfg (schurEntry sub input output).entry) t e ∧
      TapeStore.SamePayload beforeWrite d ∧
      EntryWritten beforeWrite e.store output (entryOffset (d.reg 12) (2^ell)) (2^ell)
        ((PolynomialStretch.BinaryField.indexOperations ell h).sub x
          ((PolynomialStretch.BinaryField.indexOperations ell h).mul
            ((PolynomialStretch.BinaryField.indexOperations ell h).mul y aInv) z)).val ∧
      (∀ r, 40 ≤ r.val → e.reg r = d.reg r) ∧ SchurCellState ell h input output e.store M := by
  obtain ⟨t₁,c,ht₁,hc,hco⟩ := fetchSchur_stops input ell h inp d M hs hM hhI hmI x y z hx hy hz
  obtain ⟨t₂,f,ht₂,hf,hfo⟩ := schurArithmetic_stops schurMultiply₁ schurMultiply₂ sub
    10000 6 10000 6 C k schurMultiply₁_contract schurMultiply₂_contract hsub
    ell h inp c.store M hco.setup hco.bounded x y z aInv hco.x hco.y hco.z
      (hco.inverse.trans hInv)
  have hfp : TapeStore.SamePayload f.store d := hfo.payload.trans hco.payload
  have hfh : f.store.bufferHead output = d.bufferHead output := by
    rw [hfo.heads]
    exact hco.otherHead output hio
  have hsetup : FieldSetup ell h f.store := hfo.setup hco.setup
  have h0 : f.store.reg 0 = 2^ell := hsetup.1
  have h12 : f.store.reg 12 = d.reg 12 :=
    (hfo.frame 12 (by simp [Protected])).trans hco.target
  have hv : f.store.reg 6 ≤ f.store.reg 0 := by
    rw [hfo.value, h0]
    exact Nat.le_of_lt (Fin.isLt _)
  have hMS : M ≤ (M+1)^2 := by nlinarith
  obtain ⟨t₃,e,ht₃,he,her,hew⟩ := writeCurrent_stops output 12 (by decide) inp f.store ((M+1)^2)
    (hmO.of_payload hfp) (fun r => (hfo.bounded r).trans hMS) (hfh.le.trans hhO) hv
  have heh : e.bufferHead = Function.update f.store.bufferHead output
      (entryOffset (f.store.reg 12) (f.store.reg 0)+f.store.reg 0) := hew.head
  have hall := hc.seq (hf.seq he)
  refine ⟨_,_,f.store,?_,hall,hfp,?_,?_,?_⟩
  · nlinarith
  · change EntryWritten f.store e.store output (entryOffset (d.reg 12) (2^ell)) (2^ell) _
    rw [h12, h0, hfo.value] at hew
    exact hew
  · intro r hr
    change e.reg r = _
    rw [her]
    rw [readPost_outside _ 0 r (by omega)]
    have hr2 : r ≠ 2 := by intro he; subst r; norm_num at hr
    simp only [TapeStore.setReg, Function.update_of_ne hr2]
    exact (hfo.frame r (by simp [Protected, hr])).trans (hco.caller r hr)
  · change SchurCellState ell h input output e.store M
    constructor
    · rcases hsetup with ⟨h0',h36,h37,h38⟩
      unfold FieldSetup
      change e.reg 0 = _ ∧ e.reg 36 = _ ∧ e.reg 37 = _ ∧ e.reg 38 = _
      rw [her]
      simpa [readPost, TapeStore.setReg] using And.intro h0' (And.intro h36 (And.intro h37 h38))
    · change ∀ r, e.reg r ≤ M
      rw [her]
      exact accessPost_bounded f.store 12 0 M hfo.bounded (Nat.zero_le M)
    · change e.bufferHead input ≤ (M+1)^2
      rw [heh, Function.update_of_ne (Ne.symm hio), hfo.heads]
      exact hco.head
    · change e.bufferHead output ≤ (M+1)^2
      rw [heh]
      simp only [Function.update_self]
      exact entryEnd_le _ _ M (hfo.bounded 12) (hfo.bounded 0)
    · have hpre := hmI.of_payload hfp
      constructor
      · rw [hew.symbol]
        simpa [Ne.symm hio] using hpre.1
      · intro j hj
        rw [hew.symbol]
        simpa [Ne.symm hio] using hpre.2 j hj
    · exact hew.bottomMarked (by simp [entryOffset]) (hmO.of_payload hfp)

#print axioms schurEntry_stops

theorem addition_source_contract (r : Fin 27 → Fin 64) (hr : Function.Injective r)
    (left right out : Fin 64) (h0 : r 0 = left) (h3 : r 3 = right) (h20 : r 20 = out)
    (h19 : r 19 = 37) (h23 : r 23 = 0)
    (hframe : ∀ p, Protected p →
      (∃ i : Fin 27, (i = 0 ∨ i = 3 ∨ i = 19 ∨ 23 ≤ i) ∧ i ≠ 25 ∧ r i = p) ∨
      (∀ i, p ≠ r i)) :
    ScalarContract (SourceFieldArithmetic.addition r) subtractFunction left right out 3000 5 := by
  constructor
  intro ell h inp d M hs hd a b ha hb
  rcases hs with ⟨hq,_,hN,_⟩
  have hM : 1 ≤ M := by
    have hp : 0 < 2^ell := pow_pos (by decide) ell
    have hbnd := hd 0
    omega
  obtain ⟨t,e,ht,he,_,hans,hin,hout,hbound,htape⟩ := SourceFieldArithmetic.addition_stops
    r hr inp ell a b M hM d hd (by simpa only [h0] using ha) (by simpa only [h3] using hb)
      (by simpa only [h19] using hN) (by simpa only [h23] using hq)
  refine ⟨t,e,ht,he,?_⟩
  have hro : e.store.roHead = d.roHead := congrArg Prod.fst htape
  have houtput : e.store.output = d.output := congrArg (fun x => x.2.1) htape
  have hbuffer : e.store.bufferTape = d.bufferTape := congrArg (fun x => x.2.2.1) htape
  have hheads : e.store.bufferHead = d.bufferHead := congrArg (fun x => x.2.2.2) htape
  refine ⟨?_,?_,hbound,⟨hro,houtput,?_⟩,hheads⟩
  · simpa only [h20, subtractFunction, PolynomialStretch.BinaryField.indexOperations] using hans
  · intro p hp
    rcases hframe p hp with ⟨i,hi,h25,heq⟩ | hf
    · simpa only [heq] using hin i hi h25
    · exact hout p hf
  · intro b k
    rw [hbuffer]

def subLayout (i : Fin 27) : Fin 64 :=
  #v[14,1,2,18,3,4,5,7,8,9,10,11,15,17,19,20,21,22,23,37,6,24,25,0,36,26,38][i.val]

set_option maxRecDepth 10000 in
theorem subLayout_injective : Function.Injective subLayout := by decide

set_option maxRecDepth 10000 in
theorem subLayout_frame : ∀ p, Protected p →
    (∃ i : Fin 27, (i = 0 ∨ i = 3 ∨ i = 19 ∨ 23 ≤ i) ∧ i ≠ 25 ∧ subLayout i = p) ∨
    (∀ i, p ≠ subLayout i) := by unfold Protected; decide

def schurSubtract : TapeProgram 64 2 365 := SourceFieldArithmetic.addition subLayout

theorem schurSubtract_contract : ScalarContract schurSubtract subtractFunction 14 18 6 3000 5 :=
  addition_source_contract subLayout subLayout_injective 14 18 6
    rfl rfl rfl rfl rfl subLayout_frame

/-- Fully concrete 1383-label physical Schur-cell program. The inverse and
three source/output addresses remain explicit caller-provided scalar inputs. -/
def concreteSchurEntry (input output : Fin 2) : TapeProgram 64 2 1383 :=
  schurEntry schurSubtract input output

theorem concreteSchurEntry_stops (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (d : Store) (M : ℕ)
    (hs : FieldSetup ell h d) (hM : ∀ r, d.reg r ≤ M)
    (hhI : d.bufferHead input ≤ (M+1)^2) (hhO : d.bufferHead output ≤ (M+1)^2)
    (hmI : BottomMarked d input) (hmO : BottomMarked d output)
    (x y z aInv : Fin (2^ell)) (hInv : d.reg 13 = aInv.val)
    (hx : ThermometerAt d input (entryOffset (d.reg 9) (d.reg 0)) (d.reg 0) x.val)
    (hy : ThermometerAt d input (entryOffset (d.reg 10) (d.reg 0)) (d.reg 0) y.val)
    (hz : ThermometerAt d input (entryOffset (d.reg 11) (d.reg 0)) (d.reg 0) z.val) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 1383) (beforeWrite : Store),
      t ≤ 460*((M+1)^2+1)^2+20000*(M+1)^6+3000*(M+1)^5+6 ∧
      (concreteSchurEntry input output).Stops inp (d.toCfg (concreteSchurEntry input output).entry) t e ∧
      TapeStore.SamePayload beforeWrite d ∧
      EntryWritten beforeWrite e.store output (entryOffset (d.reg 12) (2^ell)) (2^ell)
        ((PolynomialStretch.BinaryField.indexOperations ell h).sub x
          ((PolynomialStretch.BinaryField.indexOperations ell h).mul
            ((PolynomialStretch.BinaryField.indexOperations ell h).mul y aInv) z)).val ∧
      (∀ r, 40 ≤ r.val → e.reg r = d.reg r) ∧ SchurCellState ell h input output e.store M :=
  schurEntry_stops schurSubtract 3000 5 schurSubtract_contract input output hio
    ell h inp d M hs hM hhI hhO hmI hmO x y z aInv hInv hx hy hz

#print axioms schurSubtract_contract
#print axioms concreteSchurEntry_stops

/-- Keep the original physical rectangle and annihilate the chosen row and
column. This avoids compaction, subtype enumeration, and dynamic division in
the Schur materialization loop. -/
def paddedSchur {α : Type*} (O : EncodedGaussian.Operations α) {m n : ℕ}
    (A : Gaussian.Table α m n) (p : Fin m × Fin n) : Gaussian.Table α m n :=
  let B := Gaussian.toMatrix A
  let aInv := O.inv (B p.1 p.2)
  Gaussian.ofMatrix fun i j => O.sub (B i j) (O.mul (O.mul (B i p.2) aInv) (B p.1 j))

@[simp] theorem paddedSchur_apply {α : Type*} (O : EncodedGaussian.Operations α) {m n : ℕ}
    (A : Gaussian.Table α m n) (p : Fin m × Fin n) (i : Fin m) (j : Fin n) :
    Gaussian.toMatrix (paddedSchur O A p) i j = O.sub (Gaussian.toMatrix A i j)
      (O.mul (O.mul (Gaussian.toMatrix A i p.2) (O.inv (Gaussian.toMatrix A p.1 p.2)))
        (Gaussian.toMatrix A p.1 j)) := by
  simp [paddedSchur, Gaussian.toMatrix, Gaussian.ofMatrix]

theorem paddedSchur_rank {q m n : ℕ} {F : Type*} [Field F] [DecidableEq F]
    {O : EncodedGaussian.Operations (Fin q)} {decode : Fin q → F}
    (h : EncodedGaussian.Interpretation O decode)
    (A : Gaussian.Table (Fin q) (m+1) (n+1)) (p : Fin (m+1) × Fin (n+1))
    (hp : Gaussian.toMatrix A p.1 p.2 ≠ O.zero) :
    (Gaussian.toMatrix (EncodedGaussian.mapTable decode (paddedSchur O A p))).rank =
      (Gaussian.toMatrix (EncodedGaussian.mapTable decode (EncodedGaussian.schur O A p))).rank := by
  have hd : decode (Gaussian.toMatrix A p.1 p.2) ≠ 0 := by
    intro he
    exact hp (h.injective (he.trans h.zero.symm))
  have hpad (i : Fin (m+1)) (j : Fin (n+1)) :
      Gaussian.toMatrix (EncodedGaussian.mapTable decode (paddedSchur O A p)) i j =
        decode (Gaussian.toMatrix A i j) - decode (Gaussian.toMatrix A i p.2) *
          (decode (Gaussian.toMatrix A p.1 p.2))⁻¹ * decode (Gaussian.toMatrix A p.1 j) := by
    rw [EncodedGaussian.toMatrix_mapTable, paddedSchur_apply, h.sub, h.mul, h.mul, h.inv]
  have hsmall (i : Fin m) (j : Fin n) :
      Gaussian.toMatrix (EncodedGaussian.mapTable decode (EncodedGaussian.schur O A p)) i j =
        decode (Gaussian.toMatrix A (p.1.succAbove i) (p.2.succAbove j)) -
          decode (Gaussian.toMatrix A (p.1.succAbove i) p.2) *
          (decode (Gaussian.toMatrix A p.1 p.2))⁻¹ * decode (Gaussian.toMatrix A p.1 (p.2.succAbove j)) := by
    rw [EncodedGaussian.toMatrix_mapTable]
    simp [EncodedGaussian.schur, Gaussian.toMatrix, Gaussian.ofMatrix, h.sub, h.mul, h.inv]
  have he : (Gaussian.toMatrix (EncodedGaussian.mapTable decode (paddedSchur O A p))).submatrix
      (Gaussian.pivotEquiv p.1) (Gaussian.pivotEquiv p.2) =
      Matrix.fromBlocks (0 : Matrix PUnit.{1} PUnit.{1} F) 0 0
        (Gaussian.toMatrix (EncodedGaussian.mapTable decode (EncodedGaussian.schur O A p))) := by
    ext (i | i) (j | j) <;>
      simp [Matrix.submatrix_apply, Matrix.fromBlocks, Gaussian.pivotEquiv_inl,
        Gaussian.pivotEquiv_inr, hpad, hsmall, mul_assoc, hd]
  calc
    _ = ((Gaussian.toMatrix (EncodedGaussian.mapTable decode (paddedSchur O A p))).submatrix
        (Gaussian.pivotEquiv p.1) (Gaussian.pivotEquiv p.2)).rank :=
      (Matrix.rank_submatrix _ _ _).symm
    _ = _ := by rw [he, Gaussian.rank_fromBlocks_zero, Matrix.rank_zero, Nat.zero_add]

theorem paddedSchur_rank_step {q m n : ℕ} {F : Type*} [Field F] [DecidableEq F]
    {O : EncodedGaussian.Operations (Fin q)} {decode : Fin q → F}
    (h : EncodedGaussian.Interpretation O decode)
    (A : Gaussian.Table (Fin q) (m+1) (n+1)) (p : Fin (m+1) × Fin (n+1))
    (hp : Gaussian.toMatrix A p.1 p.2 ≠ O.zero) :
    (Gaussian.toMatrix (EncodedGaussian.mapTable decode A)).rank =
      (Gaussian.toMatrix (EncodedGaussian.mapTable decode (paddedSchur O A p))).rank+1 := by
  rw [paddedSchur_rank h A p hp]
  exact encoded_schur_rank_step h A p hp

#print axioms paddedSchur_rank_step

end ExpandingCodes.Computation.GaussianProgram
