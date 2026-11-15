import ExpandingCodes.Computation.UnaryArithmetic
import ExpandingCodes.Computation.EncodedTester

set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterProgram

open NKtLB

variable {R B : ℕ}

/-- Six fixed labels compare two runtime unary counters and emit exactly one
bit. Each iteration performs actual decrement/test instructions. -/
def compareLE (a b : Fin R) : TapeProgram R B 6 where
  entry := 0
  code j := if j = 0 then .dec a 3 1
    else if j = 1 then .dec b 4 0
    else if j = 3 then .emit true 5
    else if j = 4 then .emit false 5 else .halt

def compareTime : ℕ → ℕ → ℕ
  | 0, _ => 2
  | _+1, 0 => 3
  | a+1, b+1 => compareTime a b+2

theorem compareTime_le (a b : ℕ) : compareTime a b ≤ 2*a+3 := by
  induction a generalizing b with
  | zero => simp [compareTime]
  | succ a ih =>
    cases b with
    | zero => simp [compareTime]
    | succ b => have h := ih b; simp only [compareTime]; omega

def emitStore (d : TapeStore R B) (v : Bool) : TapeStore R B :=
  { d with output := d.output ++ [v] }

/-- Exact source trace and a frame contract. Only the two consumed counters
and output can change. No buffer access or read-only input occurs. -/
theorem compareLE_stops (a b : Fin R) (hab : a ≠ b) (inp : Inputs)
    (x y : ℕ) (d : TapeStore R B) (ha : d.reg a = x) (hb : d.reg b = y) :
    ∃ e : TapeStore R B, (compareLE a b).Stops inp (d.toCfg 0) (compareTime x y) (e.toCfg 5) ∧
      e.output = d.output ++ [decide (x ≤ y)] ∧
      e.roHead = d.roHead ∧ e.bufferTape = d.bufferTape ∧ e.bufferHead = d.bufferHead ∧
      (∀ r, r ≠ a → r ≠ b → e.reg r = d.reg r) ∧
      (∀ r, e.reg r ≤ d.reg r) := by
  induction x generalizing y d with
  | zero =>
    refine ⟨emitStore d true, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
    · constructor
      · apply TapeProgram.Exec.step (d := d.toCfg 3) (by simp [TapeProgram.halted, compareLE])
          (by simp [TapeProgram.step, compareLE, TapeStore.toCfg, ha])
        apply TapeProgram.Exec.one (by simp [TapeProgram.halted, compareLE])
        simp [TapeProgram.step, compareLE, TapeStore.toCfg, emitStore]
      · simp [TapeProgram.halted, compareLE]
    · simp [emitStore]
    · intro r _ _; rfl
    · intro r; exact le_rfl
  | succ x ih =>
    let d₁ := d.setReg a x
    have hs₁ : (compareLE a b).step inp (d.toCfg 0) = d₁.toCfg 1 := by
      simp [TapeProgram.step, compareLE, TapeStore.toCfg, d₁, TapeStore.setReg, ha]
    cases y with
    | zero =>
      refine ⟨emitStore d₁ false, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · constructor
        · apply TapeProgram.Exec.step (by simp [TapeProgram.halted, compareLE]) hs₁
          apply TapeProgram.Exec.step (d := d₁.toCfg 4) (by simp [TapeProgram.halted, compareLE])
            (by simp [TapeProgram.step, compareLE, TapeStore.toCfg, d₁, TapeStore.setReg,
              Ne.symm hab, hb])
          apply TapeProgram.Exec.one (by simp [TapeProgram.halted, compareLE])
          simp [TapeProgram.step, compareLE, TapeStore.toCfg, emitStore]
        · simp [TapeProgram.halted, compareLE]
      · simp [emitStore, d₁, TapeStore.setReg]
      · intro r hra _
        simp [emitStore, d₁, TapeStore.setReg, hra]
      · intro r
        by_cases hr : r = a
        · subst r; simp [emitStore, d₁, TapeStore.setReg, ha]
        · simp [emitStore, d₁, TapeStore.setReg, hr]
    | succ y =>
      let d₂ := d₁.setReg b y
      have h₂a : d₂.reg a = x := by simp [d₂, d₁, TapeStore.setReg, hab]
      have h₂b : d₂.reg b = y := by simp [d₂, TapeStore.setReg]
      obtain ⟨e, he, heo, her, het, heh, hef, heb⟩ := ih y d₂ h₂a h₂b
      refine ⟨e, ?_, ?_, her, het, heh, ?_, ?_⟩
      · constructor
        · apply TapeProgram.Exec.step (by simp [TapeProgram.halted, compareLE]) hs₁
          apply TapeProgram.Exec.step (d := d₂.toCfg 0) (by simp [TapeProgram.halted, compareLE])
            (by simp [TapeProgram.step, compareLE, TapeStore.toCfg, d₂, d₁,
              TapeStore.setReg, Ne.symm hab, hb])
          exact he.exec
        · exact he.halted
      · simpa [d₂, d₁, TapeStore.setReg] using heo
      · intro r hra hrb
        rw [hef r hra hrb]
        simp [d₂, d₁, TapeStore.setReg, hra, hrb]
      · intro r
        apply (heb r).trans
        by_cases hra : r = a
        · subst r; simp [d₂, d₁, TapeStore.setReg, hab, ha]
        · by_cases hrb : r = b
          · subst r; simp [d₂, d₁, TapeStore.setReg, hb]
          · simp [d₂, d₁, TapeStore.setReg, hra, hrb]

theorem compareLE_stops_linear (a b : Fin R) (hab : a ≠ b) (inp : Inputs)
    (d : TapeStore R B) :
    ∃ (t : ℕ) (e : TapeStore R B), t ≤ 2*d.reg a+3 ∧
      (compareLE a b).Stops inp (d.toCfg 0) t (e.toCfg 5) ∧
      e.output = d.output ++ [decide (d.reg a ≤ d.reg b)] ∧
      e.roHead = d.roHead ∧ e.bufferTape = d.bufferTape ∧ e.bufferHead = d.bufferHead ∧
      (∀ r, r ≠ a → r ≠ b → e.reg r = d.reg r) ∧
      (∀ r, e.reg r ≤ d.reg r) := by
  obtain ⟨e, he⟩ := compareLE_stops a b hab inp (d.reg a) (d.reg b) d rfl rfl
  exact ⟨compareTime (d.reg a) (d.reg b), e, compareTime_le _ _, he⟩

#print axioms compareLE_stops
#print axioms compareLE_stops_linear

/-- A fixed 54-label suffix computes both cross products and emits the exact
natural comparison. Registers 0,1 hold rank and table size; 2,3 hold the fixed
rational denominator and nonnegative numerator. Their initialization is a
separate part of the full tester. Registers 4..7 are scalar scratch. -/
def rankThreshold {B : ℕ} : TapeProgram 8 B 54 :=
  TapeProgram.seq
    (TapeProgram.seq (UnaryArithmetic.multiply 0 2 4 6 7)
      (UnaryArithmetic.multiply 1 3 5 6 7))
    (compareLE 4 5)

theorem rankThreshold_stops {B : ℕ} (inp : Inputs) (d : TapeStore 8 B) (M : ℕ)
    (hM : ∀ r, d.reg r ≤ M) :
    ∃ t e, t ≤ 100*(M+1)^2 ∧
      (rankThreshold (B := B)).Stops inp (d.toCfg (rankThreshold (B := B)).entry) t e ∧
      e.output = d.output ++ [decide (d.reg 0*d.reg 2 ≤ d.reg 3*d.reg 1)] ∧
      e.roHead = d.roHead ∧ e.bufferTape = d.bufferTape ∧ e.bufferHead = d.bufferHead ∧
      (∀ r : Fin 8, r.val < 4 → e.reg r = d.reg r) := by
  obtain ⟨t₁, c, ht₁, hc, hcs⟩ := UnaryArithmetic.multiply_stops_polynomial
    (B := B) (0 : Fin 8) 2 4 6 7 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      inp d M (hM 0) (hM 2) (hM 4) (hM 6) (hM 7)
  have hcm (r : Fin 8) (hr : r ≠ 4) : c.store.reg r ≤ M := by
    rw [hcs]
    simp only [UnaryArithmetic.multiplyStore, TapeStore.setReg]
    by_cases h6 : r = 6
    · subst r; simp
    · by_cases h7 : r = 7
      · subst r; simp
      · simpa [Function.update, hr, h6, h7] using hM r
  obtain ⟨t₂, f, ht₂, hf, hfs⟩ := UnaryArithmetic.multiply_stops_polynomial
    (B := B) (1 : Fin 8) 3 5 6 7 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      inp c.store M (hcm 1 (by decide)) (hcm 3 (by decide))
        (hcm 5 (by decide)) (hcm 6 (by decide)) (hcm 7 (by decide))
  have hleft : f.store.reg 4 = d.reg 0*d.reg 2 := by
    rw [hfs, hcs]
    simp [UnaryArithmetic.multiplyStore, TapeStore.setReg]
  have hright : f.store.reg 5 = d.reg 1*d.reg 3 := by
    rw [hfs, hcs]
    simp [UnaryArithmetic.multiplyStore, TapeStore.setReg]
  obtain ⟨s, hs, hso, hsr, hst, hsh, hsf, _⟩ := compareLE_stops
    (B := B) (4 : Fin 8) 5 (by decide) inp (f.store.reg 4) (f.store.reg 5)
      f.store rfl rfl
  have hall := (hc.seq hf).seq hs
  refine ⟨_, _, ?_, hall, ?_, ?_, ?_, ?_, ?_⟩
  · have ht := compareTime_le (f.store.reg 4) (f.store.reg 5)
    rw [hleft] at ht
    rw [hleft]
    have hp := Nat.mul_le_mul (hM 0) (hM 2)
    nlinarith
  · change s.output = _
    rw [hso, hleft, hright]
    rw [hfs, hcs]
    simp [UnaryArithmetic.multiplyStore, TapeStore.setReg, Nat.mul_comm]
  · change s.roHead = _
    rw [hsr, hfs, hcs]
    rfl
  · change s.bufferTape = _
    rw [hst, hfs, hcs]
    rfl
  · change s.bufferHead = _
    rw [hsh, hfs, hcs]
    rfl
  · intro r hr
    change s.reg r = _
    rw [hsf r (by intro he; subst r; simp at hr) (by intro he; subst r; simp at hr), hfs, hcs]
    have h4 : r ≠ 4 := by intro he; subst r; simp at hr
    have h5 : r ≠ 5 := by intro he; subst r; simp at hr
    have h6 : r ≠ 6 := by intro he; subst r; simp at hr
    have h7 : r ≠ 7 := by intro he; subst r; simp at hr
    simp [UnaryArithmetic.multiplyStore, TapeStore.setReg, h4, h5, h6, h7]

#print axioms rankThreshold_stops

/-- The physical suffix emits the immutable mission tester bit once earlier
source stages have actually produced the encoded rank, size, and constants.
These preconditions do not assert that those earlier stages exist. -/
theorem rankThreshold_canonical {B : ℕ} (θ : ℚ) (hθ : θ ≤ 1) (d n : ℕ)
    (y : PolynomialStretch.Word (PolynomialStretch.rowCount d n))
    (inp : Inputs) (s : TapeStore 8 B) (M : ℕ) (hM : ∀ r, s.reg r ≤ M)
    (hr : s.reg 0 = (EncodedGaussian.run
      (PolynomialStretch.BinaryField.indexOperations
        (PolynomialStretch.fieldExponent d n) (PolynomialStretch.fieldExponent_pos d n))
      (PolynomialStretch.binaryTestTable d n y)).1)
    (hm : s.reg 1 = PolynomialStretch.rowCount d n)
    (hd : s.reg 2 = (1/2-θ/2).den)
    (hn : s.reg 3 = (1/2-θ/2).num.toNat) :
    ∃ t e, t ≤ 100*(M+1)^2 ∧
      (rankThreshold (B := B)).Stops inp (s.toCfg (rankThreshold (B := B)).entry) t e ∧
      e.output = s.output ++ [PolynomialStretch.rankTest (θ : ℝ)
        (PolynomialStretch.binaryGeometry d n) y] ∧
      e.roHead = s.roHead ∧ e.bufferTape = s.bufferTape ∧ e.bufferHead = s.bufferHead ∧
      (∀ r : Fin 8, r.val < 4 → e.reg r = s.reg r) := by
  obtain ⟨t, e, ht, he, heo, hef⟩ := rankThreshold_stops inp s M hM
  have hbit : decide (s.reg 0*s.reg 2 ≤ s.reg 3*s.reg 1) =
      PolynomialStretch.rankTest (θ : ℝ) (PolynomialStretch.binaryGeometry d n) y := by
    calc
      _ = PolynomialStretch.binaryRankTest θ d n y := by
        simp only [hr, hm, hd, hn, PolynomialStretch.binaryRankTest]
      _ = _ := PolynomialStretch.binaryRankTest_eq θ hθ d n y
  exact ⟨t, e, ht, he, by simpa only [hbit] using heo, hef⟩

#print axioms rankThreshold_canonical

end ExpandingCodes.Computation.TesterProgram
