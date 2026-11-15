import ExpandingCodes.Computation.TapeMacros
import ExpandingCodes.Computation.BinaryPolynomial
import ExpandingCodes.Probability.FiniteUniform

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ExpandingCodes.Computation
open NKtLB

namespace RandomBits
variable {R B : ℕ}

/-- Six fixed source registers. Their contents, including ell and q, are runtime data. -/
structure Layout (R : ℕ) where
  reg : Fin 6 ↪ Fin R

abbrev Layout.ell (l : Layout R) := l.reg 0
abbrev Layout.q (l : Layout R) := l.reg 1
abbrev Layout.acc (l : Layout R) := l.reg 2
abbrev Layout.count (l : Layout R) := l.reg 3
abbrev Layout.tmp (l : Layout R) := l.reg 4
abbrev Layout.scratch (l : Layout R) := l.reg 5

@[simp] theorem Layout.reg_eq (l : Layout R) (i j : Fin 6) :
    l.reg i = l.reg j ↔ i = j := l.reg.injective.eq_iff

/-- A symbol outside the fair-bit pre is interpreted as zero. The read is
still an actual single-cell read and advances the RO randomness head once. -/
def bitAt (inp : Inputs) (h : ℕ) : Bool :=
  decide (Machine.readRO inp.rand h = .one)

def bitNat (b : Bool) : ℕ := if b then 1 else 0

/-- Constant two-instruction read, with one branch adding one and the other
executing a jump. No input size enters the code table. -/
def readBit (a : Fin R) : TapeProgram R B 4 where
  entry := 0
  code j := if j = 0 then .read 3 (fun s => if s = .one then 1 else 2)
    else if j = 1 then .inc a 3 else if j = 2 then .jump 3 else .halt

def readBitStore (a : Fin R) (inp : Inputs) (d : TapeStore R B) : TapeStore R B :=
  { d.setReg a (d.reg a + bitNat (bitAt inp (d.roHead 3))) with
    roHead := Function.update d.roHead 3 (d.roHead 3 + 1) }

 theorem readBit_stops (a : Fin R) (inp : Inputs) (d : TapeStore R B) :
    (readBit a).Stops inp (d.toCfg 0) 2 ((readBitStore a inp d).toCfg 3) := by
  let e : TapeStore R B := { d with roHead := Function.update d.roHead 3 (d.roHead 3+1) }
  let j : Fin 4 := if Machine.readRO inp.rand (d.roHead 3) = .one then 1 else 2
  have h₁ : (readBit a).step inp (d.toCfg 0) = e.toCfg j := by
    simp [TapeProgram.step, readBit, TapeStore.toCfg, e, j, Inputs.get]
    split_ifs with h <;> simp_all
  have h₂ : (readBit a).step inp (e.toCfg j) = (readBitStore a inp d).toCfg 3 := by
    by_cases h : Machine.readRO inp.rand (d.roHead 3) = .one
    · simp [TapeProgram.step, readBit, TapeStore.toCfg, e, j, h, readBitStore,
        TapeStore.setReg, bitAt, bitNat]
    · simp [TapeProgram.step, readBit, TapeStore.toCfg, e, j, h, readBitStore,
        TapeStore.setReg, bitAt, bitNat]
  constructor
  · apply TapeProgram.Exec.step (by simp [TapeProgram.halted, readBit]) h₁
    apply TapeProgram.Exec.one
    · dsimp [j]
      split_ifs <;> simp [TapeProgram.halted, readBit]
    · exact h₂
  · simp [TapeProgram.halted, readBit]

/-- Actual unary doubling: copy accumulator into a temporary, then transfer it
back. The preserving-copy macro uses the third unary scratch register. -/
def double (l : Layout R) : TapeProgram R B 14 :=
  TapeProgram.seq (TapeMacros.copy l.acc l.tmp l.scratch) (TapeMacros.transfer l.tmp l.acc)

def doubleStore (l : Layout R) (d : TapeStore R B) : TapeStore R B :=
  ((d.setReg l.acc (2*d.reg l.acc)).setReg l.tmp 0).setReg l.scratch 0

 theorem double_post (l : Layout R) (d : TapeStore R B) :
    TapeMacros.transferStore ((d.setReg l.tmp (d.reg l.acc)).setReg l.scratch 0) l.tmp l.acc =
      doubleStore l d := by
  have hat : l.acc ≠ l.tmp := l.reg.injective.ne (by decide)
  have has : l.acc ≠ l.scratch := l.reg.injective.ne (by decide)
  have hts : l.tmp ≠ l.scratch := l.reg.injective.ne (by decide)
  simp only [TapeMacros.transferStore, doubleStore, TapeStore.setReg]
  congr 1
  funext j
  by_cases ha : j = l.acc
  · subst j
    simp [Function.update, hat, has, Ne.symm hat, Ne.symm has]
    omega
  · by_cases ht : j = l.tmp
    · subst j
      simp [Function.update, hat, has, hts, Ne.symm hat]
    · by_cases hs : j = l.scratch
      · subst j
        simp [Function.update, hat, has, hts, Ne.symm has, Ne.symm hts]
      · simp [Function.update, ha, ht, hs]

 theorem double_stops (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (double l).Stops inp (d.toCfg (double (B := B) l).entry)
      (d.reg l.tmp+d.reg l.scratch+7*d.reg l.acc+9) e ∧ e.store = doubleStore l d := by
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops l.acc l.tmp l.scratch
    (l.reg.injective.ne (by decide)) (l.reg.injective.ne (by decide))
    (l.reg.injective.ne (by decide)) inp d
  have ht : c.store.reg l.tmp = d.reg l.acc := by
    rw [hcs]
    simp [TapeStore.setReg, Layout.tmp, Layout.acc, Layout.scratch, l.reg.injective.ne (by decide : (4 : Fin 6) ≠ 5)]
  have htr := TapeMacros.transfer_stops l.tmp l.acc (l.reg.injective.ne (by decide))
    inp (d.reg l.acc) c.store ht
  have hall := hc.seq htr
  refine ⟨((TapeMacros.transferStore c.store l.tmp l.acc).toCfg (2 : Fin 3)).mapPC
      (TapeProgram.rightLabel 11), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change TapeMacros.transferStore c.store l.tmp l.acc = _
    rw [hcs]
    exact double_post l d

/-- One binary Horner step a := 2*a + nextBit. -/
def nextBit (l : Layout R) : TapeProgram R B 18 :=
  TapeProgram.seq (double l) (readBit l.acc)

def nextBitStore (l : Layout R) (inp : Inputs) (d : TapeStore R B) : TapeStore R B :=
  readBitStore l.acc inp (doubleStore l d)

 theorem nextBit_stops (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (nextBit l).Stops inp (d.toCfg (nextBit (B := B) l).entry)
      (d.reg l.tmp+d.reg l.scratch+7*d.reg l.acc+12) e ∧ e.store = nextBitStore l inp d := by
  obtain ⟨c, hc, hcs⟩ := double_stops l inp d
  have hr := readBit_stops l.acc inp c.store
  have hall := hc.seq hr
  refine ⟨((readBitStore l.acc inp c.store).toCfg (3 : Fin 4)).mapPC
      (TapeProgram.rightLabel 14), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change readBitStore l.acc inp c.store = _
    rw [hcs]
    rfl

/-- Explicit numerical semantics of successive most-significant-first reads. -/
def value (inp : Inputs) : ℕ → ℕ → ℕ → ℕ
  | 0, _, a => a
  | n+1, h, a => value inp n (h+1) (2*a+bitNat (bitAt inp h))

 theorem value_lt (inp : Inputs) (n h a : ℕ) :
    value inp n h a < 2^n*(a+1) := by
  induction n generalizing h a with
  | zero => simp [value]
  | succ n ih =>
    have hi := ih (h+1) (2*a+bitNat (bitAt inp h))
    have hb : bitNat (bitAt inp h) ≤ 1 := by unfold bitNat; split <;> omega
    rw [value]
    apply hi.trans_le
    rw [pow_succ]
    nlinarith

/-- Exact data semantics of a counted sequence of finite Horner steps. -/
def bitsStore (l : Layout R) (inp : Inputs) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d
  | n+1, d => bitsStore l inp n (nextBitStore l inp (TapeProgram.decStore l.count d))

def bitsTime (l : Layout R) (inp : Inputs) : ℕ → TapeStore R B → ℕ
  | 0, _ => 1
  | n+1, d => d.reg l.tmp+d.reg l.scratch+7*d.reg l.acc+14 +
      bitsTime l inp n (nextBitStore l inp (TapeProgram.decStore l.count d))

/-- Fixed finite random-read loop; its number of labels is independent of ell. -/
def readBits (l : Layout R) : TapeProgram R B 20 :=
  TapeProgram.countedLoop (nextBit l) l.count

 theorem nextBitStore_reg (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (nextBitStore l inp d).reg =
      Function.update (Function.update (Function.update d.reg l.acc
        (2*d.reg l.acc+bitNat (bitAt inp (d.roHead 3)))) l.tmp 0) l.scratch 0 := by
  have hat : l.acc ≠ l.tmp := l.reg.injective.ne (by decide)
  have has : l.acc ≠ l.scratch := l.reg.injective.ne (by decide)
  have hts : l.tmp ≠ l.scratch := l.reg.injective.ne (by decide)
  simp only [nextBitStore, readBitStore, doubleStore, TapeStore.setReg]
  funext j
  by_cases ha : j = l.acc
  · subst j
    simp [Function.update, hat, has]
  · by_cases ht : j = l.tmp
    · subst j
      simp [Function.update, hat, hts, Ne.symm hat]
    · by_cases hs : j = l.scratch
      · subst j
        simp [Function.update, Ne.symm has, Ne.symm hts]
      · simp [Function.update, ha, ht, hs]

 theorem nextBitStore_count (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (nextBitStore l inp d).reg l.count = d.reg l.count := by
  rw [nextBitStore_reg]
  simp [Layout.count, Layout.acc, Layout.tmp, Layout.scratch,
    l.reg.injective.ne (by decide : (3 : Fin 6) ≠ 2),
    l.reg.injective.ne (by decide : (3 : Fin 6) ≠ 4),
    l.reg.injective.ne (by decide : (3 : Fin 6) ≠ 5)]

 theorem readBits_stops (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hd : d.reg l.count = n) :
    (readBits l).Stops inp (d.toCfg (TapeProgram.loopHeader 18)) (bitsTime l inp n d)
      ((bitsStore l inp n d).toCfg (TapeProgram.loopExit 18)) := by
  induction n generalizing d with
  | zero => exact TapeProgram.loop_zero (nextBit l) l.count inp d hd
  | succ n ih =>
    let d₁ := TapeProgram.decStore l.count d
    let d₂ := nextBitStore l inp d₁
    have hr : d₂.reg l.count = n := by
      rw [nextBitStore_count]
      simp [d₁, TapeProgram.decStore, hd]
    have ht := ih d₂ hr
    obtain ⟨c, hc, hcs⟩ := nextBit_stops l inp d₁
    have hh := TapeProgram.loop_positive_header (nextBit l) l.count inp d (by omega)
    have hb := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (nextBit l) l.count)
    have hx := TapeProgram.loop_body_return (nextBit l) l.count inp c hc.halted
    have he : c.store.toCfg (TapeProgram.loopHeader 18) = d₂.toCfg (TapeProgram.loopHeader 18) := by
      rw [hcs]
    rw [he] at hx
    constructor
    · have h := ((hh.trans hb).trans hx).trans ht.exec
      convert h using 1 <;> first | rfl | skip
      simp only [bitsTime, d₂, d₁, TapeProgram.decStore, Function.update_of_ne
        (l.reg.injective.ne (by decide : (4 : Fin 6) ≠ 3)), Function.update_of_ne
        (l.reg.injective.ne (by decide : (5 : Fin 6) ≠ 3)), Function.update_of_ne
        (l.reg.injective.ne (by decide : (2 : Fin 6) ≠ 3))]
      simp only [Layout.acc, Layout.tmp, Layout.scratch] at *
      omega
    · exact ht.halted

 theorem bitsStore_roHead (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (bitsStore l inp n d).roHead = Function.update d.roHead 3 (d.roHead 3+n) := by
  induction n generalizing d with
  | zero => simp [bitsStore]
  | succ n ih =>
    rw [bitsStore, ih]
    simp [nextBitStore, readBitStore, doubleStore, TapeStore.setReg,
      TapeProgram.decStore, Function.update_idem, Nat.add_assoc, Nat.add_comm]

 theorem bitsStore_payload (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (bitsStore l inp n d).output = d.output ∧
    (bitsStore l inp n d).bufferTape = d.bufferTape ∧
    (bitsStore l inp n d).bufferHead = d.bufferHead := by
  induction n generalizing d with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih => exact ih _

theorem bitsStore_acc (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (bitsStore l inp n d).reg l.acc = value inp n (d.roHead 3) (d.reg l.acc) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [bitsStore, ih]
    simp [nextBitStore, readBitStore, doubleStore, TapeStore.setReg, TapeProgram.decStore,
      Layout.acc, Layout.count, Layout.tmp, Layout.scratch, value]

 theorem bitsStore_reg_other (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (j : Fin R) (ha : j ≠ l.acc) (hc : j ≠ l.count)
    (ht : j ≠ l.tmp) (hs : j ≠ l.scratch) :
    (bitsStore l inp n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [bitsStore, ih, nextBitStore_reg]
    simp [TapeProgram.decStore, ha, hc, ht, hs]

 theorem bitsStore_count (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (bitsStore l inp n d).reg l.count = d.reg l.count-n := by
  induction n generalizing d with
  | zero => simp [bitsStore]
  | succ n ih =>
    rw [bitsStore, ih, nextBitStore_count]
    simp [TapeProgram.decStore, Nat.sub_sub, Nat.add_comm]

 theorem bitsStore_tmp (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hd : d.reg l.tmp = 0) : (bitsStore l inp n d).reg l.tmp = 0 := by
  induction n generalizing d with
  | zero => exact hd
  | succ n ih =>
    apply ih
    rw [nextBitStore_reg]
    simp [Layout.tmp, Layout.scratch]

 theorem bitsStore_scratch (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hd : d.reg l.scratch = 0) : (bitsStore l inp n d).reg l.scratch = 0 := by
  induction n generalizing d with
  | zero => exact hd
  | succ n ih =>
    apply ih
    rw [nextBitStore_reg]
    simp

 theorem bitsTime_le (l : Layout R) (inp : Inputs) (n Q : ℕ) (d : TapeStore R B)
    (ht : d.reg l.tmp = 0) (hs : d.reg l.scratch = 0)
    (hQ : 2^n*(d.reg l.acc+1) ≤ Q) :
    bitsTime l inp n d ≤ n*(7*Q+14)+1 := by
  induction n generalizing d with
  | zero => simp [bitsTime]
  | succ n ih =>
    let e := nextBitStore l inp (TapeProgram.decStore l.count d)
    have he : e.reg l.acc = 2*d.reg l.acc + bitNat (bitAt inp (d.roHead 3)) := by
      simp [e, nextBitStore, readBitStore, doubleStore, TapeStore.setReg,
        TapeProgram.decStore, Layout.acc, Layout.count, Layout.tmp, Layout.scratch]
    have het : e.reg l.tmp = 0 := by
      rw [nextBitStore_reg]
      simp [Layout.tmp, Layout.scratch]
    have hes : e.reg l.scratch = 0 := by rw [nextBitStore_reg]; simp
    have hb : bitNat (bitAt inp (d.roHead 3)) ≤ 1 := by unfold bitNat; split <;> omega
    have hQe : 2^n*(e.reg l.acc+1) ≤ Q := by
      rw [he]
      rw [pow_succ] at hQ
      nlinarith
    have hi := ih e het hes hQe
    have hpow : 1 ≤ 2^(n+1) := Nat.one_le_pow _ _ (by omega)
    have ha : d.reg l.acc ≤ Q := by nlinarith
    simp only [bitsTime, ht, hs, zero_add]
    have hd₁ : (TapeProgram.decStore l.count d).reg l.tmp = 0 := by
      simp [TapeProgram.decStore, Layout.tmp, Layout.count, ht]
    have hd₂ : (TapeProgram.decStore l.count d).reg l.scratch = 0 := by
      simp [TapeProgram.decStore, Layout.scratch, Layout.count, hs]
    change 7*d.reg l.acc+14+bitsTime l inp n e ≤ _
    nlinarith

/-- Clear the accumulator and doubling temporary after copying runtime ell
into the loop counter. The original ell and q registers are preserved. -/
def prepare (l : Layout R) : TapeProgram R B 15 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.copy l.ell l.count l.scratch)
    (TapeMacros.clear l.acc)) (TapeMacros.clear l.tmp)

def prepareStore (l : Layout R) (d : TapeStore R B) : TapeStore R B :=
  (((d.setReg l.count (d.reg l.ell)).setReg l.scratch 0).setReg l.acc 0).setReg l.tmp 0

 theorem prepare_stops (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (prepare l).Stops inp (d.toCfg (prepare (B := B) l).entry)
      (d.reg l.count+d.reg l.scratch+5*d.reg l.ell+d.reg l.acc+d.reg l.tmp+11) e ∧
      e.store = prepareStore l d := by
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops l.ell l.count l.scratch
    (l.reg.injective.ne (by decide)) (l.reg.injective.ne (by decide))
    (l.reg.injective.ne (by decide)) inp d
  have ha : c.reg l.acc = d.reg l.acc := by
    change c.store.reg l.acc = _
    rw [hcs]
    simp [TapeStore.setReg, Layout.acc, Layout.count, Layout.scratch]
  let e := c.store.setReg l.acc 0
  have ht : e.reg l.tmp = d.reg l.tmp := by
    simp only [e, TapeStore.setReg]
    change (Function.update c.store.reg l.acc 0) l.tmp = _
    rw [Function.update_of_ne (l.reg.injective.ne (by decide : (4 : Fin 6) ≠ 2)), hcs]
    simp [TapeStore.setReg, Layout.tmp, Layout.count, Layout.scratch]
  have h₁ := TapeMacros.clear_stops l.acc inp (d.reg l.acc) c.store ha
  have h₂ := TapeMacros.clear_stops l.tmp inp (d.reg l.tmp) e ht
  have hall := (hc.seq h₁).seq h₂
  refine ⟨((e.setReg l.tmp 0).toCfg (1 : Fin 2)).mapPC (TapeProgram.rightLabel 13), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change (c.store.setReg l.acc 0).setReg l.tmp 0 = _
    rw [hcs]
    rfl

/-- The complete finite random-index routine (35 labels). All variable sizes
are stored in runtime registers; only six register addresses enter the code. -/
def randomIndex (l : Layout R) : TapeProgram R B 35 :=
  TapeProgram.seq (prepare l) (readBits l)

def indexStore (l : Layout R) (inp : Inputs) (d : TapeStore R B) : TapeStore R B :=
  bitsStore l inp (d.reg l.ell) (prepareStore l d)

 theorem randomIndex_stops (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    ∃ t e, t ≤ d.reg l.count+d.reg l.scratch+d.reg l.acc+d.reg l.tmp+
        5*d.reg l.ell+13+d.reg l.ell*(7*2^(d.reg l.ell)+14) ∧
      (randomIndex l).Stops inp (d.toCfg (randomIndex (B := B) l).entry) t e ∧
      e.store = indexStore l inp d := by
  obtain ⟨c, hc, hcs⟩ := prepare_stops l inp d
  have hcount : c.store.reg l.count = d.reg l.ell := by
    rw [hcs]
    simp [prepareStore, TapeStore.setReg, Layout.count, Layout.acc, Layout.tmp, Layout.scratch]
  have htmp : c.store.reg l.tmp = 0 := by rw [hcs]; simp [prepareStore, TapeStore.setReg]
  have hscratch : c.store.reg l.scratch = 0 := by
    rw [hcs]
    simp [prepareStore, TapeStore.setReg, Layout.scratch, Layout.acc, Layout.tmp]
  have hacc : c.store.reg l.acc = 0 := by
    rw [hcs]
    simp [prepareStore, TapeStore.setReg, Layout.acc, Layout.tmp]
  have hr := readBits_stops l inp (d.reg l.ell) c.store hcount
  have hb := bitsTime_le l inp (d.reg l.ell) (2^(d.reg l.ell)) c.store htmp hscratch
    (by rw [hacc]; simp)
  have hall := hc.seq hr
  refine ⟨d.reg l.count+d.reg l.scratch+5*d.reg l.ell+d.reg l.acc+d.reg l.tmp+11+1+
    bitsTime l inp (d.reg l.ell) c.store,
    ((bitsStore l inp (d.reg l.ell) c.store).toCfg (TapeProgram.loopExit 18)).mapPC
    (TapeProgram.rightLabel 15 : Fin 20 → Fin 35), ?_, ?_, ?_⟩
  · omega
  · exact hall
  · change bitsStore l inp (d.reg l.ell) c.store = _
    rw [hcs]
    rfl

 theorem indexStore_acc (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).reg l.acc = value inp (d.reg l.ell) (d.roHead 3) 0 := by
  rw [indexStore, bitsStore_acc]
  simp [prepareStore, TapeStore.setReg, Layout.acc, Layout.tmp]

 theorem indexStore_acc_lt (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).reg l.acc < 2^(d.reg l.ell) := by
  rw [indexStore_acc]
  simpa using value_lt inp (d.reg l.ell) (d.roHead 3) 0

 theorem indexStore_roHead (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).roHead = Function.update d.roHead 3 (d.roHead 3+d.reg l.ell) := by
  rw [indexStore, bitsStore_roHead]
  rfl

 theorem indexStore_ell (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).reg l.ell = d.reg l.ell := by
  rw [indexStore, bitsStore_reg_other l inp _ _ l.ell]
  · simp [prepareStore, TapeStore.setReg, Layout.ell, Layout.count, Layout.acc, Layout.tmp, Layout.scratch]
  all_goals exact l.reg.injective.ne (by decide)

 theorem indexStore_q (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).reg l.q = d.reg l.q := by
  rw [indexStore, bitsStore_reg_other l inp _ _ l.q]
  · simp [prepareStore, TapeStore.setReg, Layout.q, Layout.count, Layout.acc, Layout.tmp, Layout.scratch]
  all_goals exact l.reg.injective.ne (by decide)

 theorem indexStore_count (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).reg l.count = 0 := by
  rw [indexStore, bitsStore_count]
  simp [prepareStore, TapeStore.setReg, Layout.count, Layout.acc, Layout.tmp, Layout.scratch]

 theorem indexStore_tmp (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).reg l.tmp = 0 := by
  apply bitsStore_tmp
  simp [prepareStore, TapeStore.setReg]

 theorem indexStore_scratch (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).reg l.scratch = 0 := by
  apply bitsStore_scratch
  simp [prepareStore, TapeStore.setReg, Layout.scratch, Layout.acc, Layout.tmp]

 theorem indexStore_payload (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).output = d.output ∧
    (indexStore l inp d).bufferTape = d.bufferTape ∧
    (indexStore l inp d).bufferHead = d.bufferHead :=
  bitsStore_payload l inp _ _

/-- A deliberately loose fixed polynomial in q, valid even when the four
mutable counters initially contain arbitrary values bounded by q. -/
 theorem randomIndex_polynomial (l : Layout R) (inp : Inputs) (d : TapeStore R B)
    (hq : d.reg l.q = 2^(d.reg l.ell)) (he : d.reg l.ell ≤ d.reg l.q)
    (hc : d.reg l.count ≤ d.reg l.q) (hs : d.reg l.scratch ≤ d.reg l.q)
    (ha : d.reg l.acc ≤ d.reg l.q) (ht : d.reg l.tmp ≤ d.reg l.q) :
    ∃ t e, t ≤ (d.reg l.q+1)*(7*d.reg l.q+30) ∧
      (randomIndex l).Stops inp (d.toCfg (randomIndex (B := B) l).entry) t e ∧
      e.store = indexStore l inp d := by
  obtain ⟨t, e, hb, hr, hpost⟩ := randomIndex_stops l inp d
  refine ⟨t, e, ?_, hr, hpost⟩
  rw [← hq] at hb
  nlinarith

open scoped BigOperators
open ExpandingCodes.PolynomialStretch

/-- A finite equivalence from the read order of ell fair coins to the index
order of the explicit binary-polynomial coefficient representation. -/
def reverseBits (ell : ℕ) : (Fin ell → Bool) ≃ (Fin ell → Bool) where
  toFun x j := x j.rev
  invFun x j := x j.rev
  left_inv x := by funext j; simp
  right_inv x := by funext j; simp

def bitsIndexEquiv (ell : ℕ) : (Fin ell → Bool) ≃ Fin (2^ell) :=
  (reverseBits ell).trans
    ((BinaryPolynomial.bitsEquiv ell).trans (BinaryPolynomial.indexEquiv ell).symm)

 theorem bitsIndexEquiv_val (ell : ℕ) (x : Fin ell → Bool) :
    (bitsIndexEquiv ell x).val = ∑ j : Fin ell, bitNat (x j) * 2^(ell-1-j.val) := by
  rw [bitsIndexEquiv, Equiv.trans_apply, Equiv.trans_apply,
    BinaryPolynomial.indexEquiv_inverse_value]
  change (∑ j : Fin ell, (BinaryPolynomial.bitEquiv (x j.rev)).val * 2^j.val) = _
  have hb (b : Bool) : (BinaryPolynomial.bitEquiv b).val = bitNat b := by cases b <;> rfl
  simp_rw [hb]
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin ell))]
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  simp only [Fin.val_rev]
  omega

 theorem value_eq_sum (inp : Inputs) (n h a : ℕ) :
    value inp n h a = 2^n*a +
      ∑ j : Fin n, bitNat (bitAt inp (h+j.val)) * 2^(n-1-j.val) := by
  induction n generalizing h a with
  | zero => simp [value]
  | succ n ih =>
    rw [value, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero, Nat.add_sub_cancel,
      Nat.sub_zero]
    have ht : (∑ j : Fin n, bitNat (bitAt inp (h+1+j.val)) * 2^(n-1-j.val)) =
        ∑ j : Fin n, bitNat (bitAt inp (h+(j.val+1))) * 2^(n-(j.val+1)) := by
      apply Finset.sum_congr rfl
      intro j _
      have hj : n-1-j.val = n-(j.val+1) := by omega
      rw [hj]
      congr 3 <;> omega
    rw [ht, pow_succ]
    ring

/-- The exact value computed at any random-head offset is the finite bit
bijection; this also fixes the endianness relative to `indexEquiv`. -/
 theorem value_eq_bitsIndex (inp : Inputs) (ell h : ℕ) :
    value inp ell h 0 =
      (bitsIndexEquiv ell (fun j => bitAt inp (h+j.val))).val := by
  rw [value_eq_sum, bitsIndexEquiv_val]
  simp

 theorem value_congr_pre (inp inp' : Inputs) (ell h : ℕ)
    (he : ∀ j : Fin ell, bitAt inp (h+j.val) = bitAt inp' (h+j.val)) :
    value inp ell h 0 = value inp' ell h 0 := by
  rw [value_eq_bitsIndex, value_eq_bitsIndex]
  congr 2
  funext j
  exact he j

/-- Exact uniform output, with no statistical approximation. -/
 theorem uniform_bitsIndex (ell : ℕ) (E : Fin (2^ell) → Prop) :
    uniformProb (fun x : Fin ell → Bool => E (bitsIndexEquiv ell x)) = uniformProb E :=
  uniformProb_equiv (bitsIndexEquiv ell) E

 theorem uniform_bitsIndex_point (ell : ℕ) (i : Fin (2^ell)) :
    uniformProb (fun x : Fin ell → Bool => bitsIndexEquiv ell x = i) = 1/(2^ell : ℝ) := by
  classical
  letI : Unique {j : Fin (2^ell) // j = i} :=
    { default := ⟨i, rfl⟩
      uniq := by intro j; apply Subtype.ext; exact j.property }
  rw [uniform_bitsIndex ell (fun j => j = i), uniformProb_eq_card_subtype]
  simp

#print axioms randomIndex_stops
#print axioms randomIndex_polynomial
#print axioms value_eq_bitsIndex
#print axioms uniform_bitsIndex

theorem bitAt_block (inp : Inputs) (pre suffix : List Bool) {ell : ℕ}
    (x : Fin ell → Bool) (j : Fin ell) :
    bitAt {inp with rand := pre ++ (List.ofFn x ++ suffix)} (pre.length+j.val) = x j := by
  unfold bitAt Machine.readRO
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simpa using j.isLt), List.getElem?_ofFn]
  simp only [j.isLt, dite_true]
  cases hx : x j <;> rfl

/-- Prefix and suffix contents are unrestricted; only the ell scanned cells
influence the exact output of the source routine. -/
 theorem randomIndex_block_value (l : Layout R) (inp : Inputs) (d : TapeStore R B)
    (pre suffix : List Bool) (x : Fin (d.reg l.ell) → Bool)
    (hh : d.roHead 3 = pre.length) :
    (indexStore l {inp with rand := pre ++ (List.ofFn x ++ suffix)} d).reg l.acc =
      (bitsIndexEquiv (d.reg l.ell) x).val := by
  rw [indexStore_acc, value_eq_bitsIndex, hh]
  congr 2
  funext j
  exact bitAt_block inp pre suffix x j

 theorem randomIndex_suffix_independent (l : Layout R) (inp : Inputs) (d : TapeStore R B)
    (pre suffix suffix' : List Bool) (x : Fin (d.reg l.ell) → Bool)
    (hh : d.roHead 3 = pre.length) :
    (indexStore l {inp with rand := pre ++ (List.ofFn x ++ suffix)} d).reg l.acc =
    (indexStore l {inp with rand := pre ++ (List.ofFn x ++ suffix')} d).reg l.acc := by
  rw [randomIndex_block_value l inp d pre suffix x hh,
    randomIndex_block_value l inp d pre suffix' x hh]

/-- Direct finite fair-coin law of the actual source accumulator, including
arbitrary fixed pre and unused suffix. -/
 theorem randomIndex_uniform (l : Layout R) (inp : Inputs) (d : TapeStore R B)
    (pre suffix : List Bool) (hh : d.roHead 3 = pre.length)
    (E : Fin (2^(d.reg l.ell)) → Prop) :
    uniformProb (fun x : Fin (d.reg l.ell) → Bool =>
      E ⟨(indexStore l {inp with rand := pre ++ (List.ofFn x ++ suffix)} d).reg l.acc,
        indexStore_acc_lt l _ d⟩) = uniformProb E := by
  have he (x : Fin (d.reg l.ell) → Bool) :
      (⟨(indexStore l {inp with rand := pre ++ (List.ofFn x ++ suffix)} d).reg l.acc,
        indexStore_acc_lt l _ d⟩ : Fin (2^(d.reg l.ell))) = bitsIndexEquiv (d.reg l.ell) x := by
    apply Fin.ext
    exact randomIndex_block_value l inp d pre suffix x hh
  simp_rw [he]
  exact uniform_bitsIndex _ E

#print axioms randomIndex_uniform

theorem indexStore_reg_other (l : Layout R) (inp : Inputs) (d : TapeStore R B)
    (j : Fin R) (hj : ∀ i, l.reg i ≠ j) :
    (indexStore l inp d).reg j = d.reg j := by
  rw [indexStore, bitsStore_reg_other l inp _ _ j
    (Ne.symm (hj 2)) (Ne.symm (hj 3)) (Ne.symm (hj 4)) (Ne.symm (hj 5))]
  simp [prepareStore, TapeStore.setReg, Ne.symm (hj 2), Ne.symm (hj 3),
    Ne.symm (hj 4), Ne.symm (hj 5)]

end RandomBits
end ExpandingCodes.Computation
