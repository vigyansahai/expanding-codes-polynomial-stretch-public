import ExpandingCodes.Computation.UnaryArithmetic

set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace FieldPrograms
open UnaryArithmetic
variable {R B : ℕ}

/-- Destructive division by two and parity. All operands and bounds are runtime
counter values; this nine-label table is independent of field size. -/
def halve (src quotient parity : Fin R) : TapeProgram R B 9 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.clear quotient) (TapeMacros.clear parity))
    (halveLoop src quotient parity)

def halfStore (d : TapeStore R B) (src quotient parity : Fin R) : TapeStore R B :=
  ((d.setReg src 0).setReg quotient (d.reg src/2)).setReg parity (d.reg src%2)

theorem halve_stops (src quotient parity : Fin R)
    (hsq : src ≠ quotient) (hsp : src ≠ parity) (hqp : quotient ≠ parity)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (halve src quotient parity).Stops inp
      (d.toCfg (halve (B := B) src quotient parity).entry)
      (d.reg quotient+d.reg parity+3*(d.reg src/2)+2*(d.reg src%2)+5) e ∧
      e.store = halfStore d src quotient parity := by
  let d₁ := d.setReg quotient 0
  let d₂ := d₁.setReg parity 0
  have h₁ := TapeMacros.clear_stops quotient inp (d.reg quotient) d rfl
  have h₂ := TapeMacros.clear_stops parity inp (d.reg parity) d₁
    (by simp [d₁, TapeStore.setReg, Ne.symm hqp])
  have hn : d₂.reg src = d.reg src := by
    simp [d₂, d₁, TapeStore.setReg, hsq, hsp]
  have h₃ := halveLoop_stops src quotient parity hsq hsp hqp inp (d.reg src) d₂ hn
  have hall := (h₁.seq h₂).seq h₃
  have hpost : halveStore d₂ src quotient parity (d.reg src) = halfStore d src quotient parity := by
    simp only [halveStore, halfStore, d₂, d₁, TapeStore.setReg]
    congr 1
    funext j
    by_cases hp : j = parity
    · subst j
      simp [Function.update, Ne.symm hqp]
    · simp only [Function.update_of_ne hp]
      by_cases hq : j = quotient
      · subst j
        simp [Function.update, hqp]
      · simp only [Function.update_of_ne hq]
        by_cases hs : j = src
        · subst j; simp [Function.update]
        · simp [Function.update, hp, hq, hs]
  refine ⟨((halveStore d₂ src quotient parity (d.reg src)).toCfg (4 : Fin 5)).mapPC
    (TapeProgram.rightLabel 4), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change halveStore d₂ src quotient parity (d.reg src) = _
    exact hpost

/-- One right shift: pair peeling followed by actual unary transfer of its
quotient into the input counter. -/
def halfStep (src quotient parity : Fin R) : TapeProgram R B 12 :=
  TapeProgram.seq (halve src quotient parity) (TapeMacros.transfer quotient src)

def halfStepStore (d : TapeStore R B) (src quotient parity : Fin R) : TapeStore R B :=
  ((d.setReg src (d.reg src/2)).setReg quotient 0).setReg parity (d.reg src%2)

theorem halfStep_stops (src quotient parity : Fin R)
    (hsq : src ≠ quotient) (hsp : src ≠ parity) (hqp : quotient ≠ parity)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (halfStep src quotient parity).Stops inp
      (d.toCfg (halfStep (B := B) src quotient parity).entry)
      (d.reg quotient+d.reg parity+5*(d.reg src/2)+2*(d.reg src%2)+7) e ∧
      e.store = halfStepStore d src quotient parity := by
  obtain ⟨c, hc, hcs⟩ := halve_stops src quotient parity hsq hsp hqp inp d
  have hcq : c.reg quotient = d.reg src/2 := by
    change c.store.reg quotient = _
    rw [hcs]
    simp [halfStore, TapeStore.setReg, hqp]
  have h₂ := TapeMacros.transfer_stops quotient src (Ne.symm hsq) inp (d.reg src/2) c.store hcq
  have hall := hc.seq h₂
  have hpost : TapeMacros.transferStore c.store quotient src = halfStepStore d src quotient parity := by
    rw [hcs]
    simp only [TapeMacros.transferStore, halfStore, halfStepStore, TapeStore.setReg]
    congr 1
    funext j
    by_cases hp : j = parity
    · subst j
      simp [Function.update, Ne.symm hsp, Ne.symm hqp]
    · by_cases hq : j = quotient
      · subst j
        simp [Function.update, Ne.symm hsq, hqp]
      · by_cases hs : j = src
        · subst j
          simp [Function.update, hsq, hsp, hqp]
        · simp [Function.update, hp, hq, hs]
  refine ⟨((TapeMacros.transferStore c.store quotient src).toCfg (2 : Fin 3)).mapPC
    (TapeProgram.rightLabel 9), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change TapeMacros.transferStore c.store quotient src = _
    exact hpost

theorem halfStep_time_le (n q p : ℕ) : q+p+5*(n/2)+2*(n%2)+7 ≤ q+p+3*n+7 := by omega

def shiftRight (src quotient parity count : Fin R) : TapeProgram R B 14 :=
  TapeProgram.countedLoop (halfStep src quotient parity) count

/-- Exact store semantics of the finite pair-peeling loop. This recursive value
is used only in the specification; the machine code above is a fixed table. -/
def shiftStore (src quotient parity count : Fin R) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d.setReg count 0
  | n+1, d => shiftStore src quotient parity count n
      (halfStepStore (d.setReg count n) src quotient parity)

theorem shiftStore_src (src quotient parity count : Fin R)
    (hsq : src ≠ quotient) (hsp : src ≠ parity) (hsc : src ≠ count)
    (n : ℕ) (d : TapeStore R B) :
    (shiftStore src quotient parity count n d).reg src = d.reg src/2^n := by
  induction n generalizing d with
  | zero => simp [shiftStore, TapeStore.setReg, hsc]
  | succ n ih =>
    rw [shiftStore, ih]
    have hsrc : (halfStepStore (d.setReg count n) src quotient parity).reg src = d.reg src/2 := by
      simp [halfStepStore, TapeStore.setReg, hsp, hsq, hsc]
    rw [hsrc, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm 2]

theorem shiftRight_stops (src quotient parity count : Fin R)
    (hsq : src ≠ quotient) (hsp : src ≠ parity) (hsc : src ≠ count)
    (hqp : quotient ≠ parity) (hqc : quotient ≠ count) (hpc : parity ≠ count)
    (inp : Inputs) (M n : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hn : d.reg count = n) (hs : d.reg src ≤ M)
    (hq : d.reg quotient ≤ M) (hp : d.reg parity ≤ M) :
    ∃ t, t ≤ n*(5*M+9)+1 ∧
      (shiftRight src quotient parity count).Stops inp
        (d.toCfg (TapeProgram.loopHeader 12)) t
        ((shiftStore src quotient parity count n d).toCfg (TapeProgram.loopExit 12)) := by
  induction n generalizing d with
  | zero =>
    have he : d.setReg count 0 = d := by simp [TapeStore.setReg, ← hn]
    exact ⟨1, by omega, by simpa [shiftRight, shiftStore, he] using
      TapeProgram.loop_zero (halfStep src quotient parity) count inp d hn⟩
  | succ n ih =>
    let d₁ := d.setReg count n
    obtain ⟨c, hc, hcs⟩ := halfStep_stops src quotient parity hsq hsp hqp inp d₁
    have hcsrc : c.reg src = d.reg src/2 := by
      change c.store.reg src = _
      rw [hcs]
      simp [halfStepStore, d₁, TapeStore.setReg, hsq, hsp, hsc]
    have hcq : c.reg quotient = 0 := by
      change c.store.reg quotient = _
      rw [hcs]
      simp [halfStepStore, TapeStore.setReg, hqp]
    have hcp : c.reg parity = d.reg src%2 := by
      change c.store.reg parity = _
      rw [hcs]
      simp [halfStepStore, d₁, TapeStore.setReg, hsc]
    have hcn : c.reg count = n := by
      change c.store.reg count = _
      rw [hcs]
      simp [halfStepStore, d₁, TapeStore.setReg, Ne.symm hsc, Ne.symm hqc, Ne.symm hpc]
    obtain ⟨t, ht, htail⟩ := ih c.store hcn (by simp only [TapeCfg.store, hcsrc]; omega)
      (by simp only [TapeCfg.store, hcq]; omega) (by simp only [TapeCfg.store, hcp]; omega)
    have hhead := TapeProgram.loop_positive_header (halfStep src quotient parity) count inp d (by omega)
    have hdec : TapeProgram.decStore count d = d₁ := by
      simp [TapeProgram.decStore, d₁, TapeStore.setReg, hn]
    rw [hdec] at hhead
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (halfStep src quotient parity) count)
    have hreturn := TapeProgram.loop_body_return (halfStep src quotient parity) count inp c hc.halted
    have hpost : shiftStore src quotient parity count n c.store =
        shiftStore src quotient parity count (n+1) d := by rw [shiftStore, hcs]
    have hall := ((hhead.trans hrun).trans hreturn).trans htail.exec
    rw [hpost] at hall
    refine ⟨_, ?_, ⟨hall, ?_⟩⟩
    · have hbody := halfStep_time_le (d.reg src) (d.reg quotient) (d.reg parity)
      simp only [d₁, TapeStore.setReg, Function.update_of_ne hqc,
        Function.update_of_ne hpc, Function.update_of_ne hsc]
      nlinarith
    · exact TapeProgram.loop_code_exit (halfStep src quotient parity) count

theorem setReg_bound (d : TapeStore R B) (r : Fin R) (n M : ℕ)
    (hd : ∀ j, d.reg j ≤ M) (hn : n ≤ M) : ∀ j, (d.setReg r n).reg j ≤ M := by
  intro j
  by_cases h : j = r
  · subst j; simpa using hn
  · simpa [TapeStore.setReg, h] using hd j

theorem halfStepStore_bound (d : TapeStore R B) (src quotient parity : Fin R)
    (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (halfStepStore d src quotient parity).reg j ≤ M := by
  apply setReg_bound _ parity _ M
  · apply setReg_bound _ quotient 0 M
    · apply setReg_bound d src _ M hd
      exact (Nat.div_le_self _ _).trans (hd src)
    · omega
  · omega

theorem shiftStore_bound (src quotient parity count : Fin R)
    (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) (hn : n ≤ M) :
    ∀ j, (shiftStore src quotient parity count n d).reg j ≤ M := by
  induction n generalizing d with
  | zero => exact setReg_bound d count 0 M hd (by omega)
  | succ n ih =>
    rw [shiftStore]
    exact ih _ (halfStepStore_bound _ src quotient parity M hM
      (setReg_bound d count n M hd (by omega))) (by omega)

theorem shiftStore_count (src quotient parity count : Fin R)
    (n : ℕ) (d : TapeStore R B) :
    (shiftStore src quotient parity count n d).reg count = 0 := by
  induction n generalizing d with
  | zero => simp [shiftStore]
  | succ n ih => exact ih _

theorem shiftStore_fresh (src quotient parity count j : Fin R)
    (hs : j ≠ src) (hq : j ≠ quotient) (hp : j ≠ parity) (hc : j ≠ count)
    (n : ℕ) (d : TapeStore R B) :
    (shiftStore src quotient parity count n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => simp [shiftStore, TapeStore.setReg, hc]
  | succ n ih =>
    rw [shiftStore, ih]
    simp [halfStepStore, TapeStore.setReg, hs, hq, hp, hc]

theorem reg_set_layout (r : Fin 7 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i j : Fin 7) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j; simp
  · simp [TapeStore.setReg, h, show r j ≠ r i from fun he => h (hr he)]

/-- Registers 0 and 1 contain the preserved input and bit index; register 4 is
the output bit. Registers 2,3,5,6 are unary scratch, never packed arrays. -/
def testBit (r : Fin 7 → Fin R) : TapeProgram R B 45 :=
  TapeProgram.seq
    (TapeProgram.seq
      (TapeProgram.seq (TapeMacros.copy (r 0) (r 2) (r 6)) (TapeMacros.copy (r 1) (r 5) (r 6)))
      (shiftRight (r 2) (r 3) (r 4) (r 5)))
    (halve (r 2) (r 3) (r 4))

def bitPrepare (r : Fin 7 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let d₁ := (d.setReg (r 2) (d.reg (r 0))).setReg (r 6) 0
  (d₁.setReg (r 5) (d₁.reg (r 1))).setReg (r 6) 0

def testBitStore (r : Fin 7 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  halfStore
    (shiftStore (r 2) (r 3) (r 4) (r 5) (d.reg (r 1)) (bitPrepare r d))
    (r 2) (r 3) (r 4)

theorem testBitStore_bit (r : Fin 7 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) :
    (testBitStore r d).reg (r 4) = if Nat.testBit (d.reg (r 0)) (d.reg (r 1)) then 1 else 0 := by
  have hs := shiftStore_src (r 2) (r 3) (r 4) (r 5)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (d.reg (r 1)) (bitPrepare r d)
  have hprep : (bitPrepare r d).reg (r 2) = d.reg (r 0) := by
    simp [bitPrepare, reg_set_layout r hr]
  rw [hprep] at hs
  have hbit : (testBitStore r d).reg (r 4) = d.reg (r 0)/2^d.reg (r 1)%2 := by
    simp only [testBitStore, halfStore, reg_set_layout r hr, ite_true]
    exact congrArg (· % 2) hs
  rw [hbit, Nat.testBit_eq_decide_div_mod_eq]
  by_cases hb : d.reg (r 0)/2^d.reg (r 1)%2 = 1
  · simp [hb]
  · have hz : d.reg (r 0)/2^d.reg (r 1)%2 = 0 := by omega
    simp [hb, hz]

theorem testBitStore_preserves (r : Fin 7 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (j : Fin 7) (hj : j = 0 ∨ j = 1) :
    (testBitStore r d).reg (r j) = d.reg (r j) := by
  rcases hj with rfl | rfl
  all_goals
    simp only [testBitStore, halfStore, reg_set_layout r hr]
    simp only [show (0 : Fin 7) ≠ 4 from by decide, show (0 : Fin 7) ≠ 3 from by decide,
      show (0 : Fin 7) ≠ 2 from by decide, show (1 : Fin 7) ≠ 4 from by decide,
      show (1 : Fin 7) ≠ 3 from by decide, show (1 : Fin 7) ≠ 2 from by decide, ite_false]
    rw [shiftStore_fresh _ _ _ _ _ (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) (hr.ne (by decide))]
    simp [bitPrepare, reg_set_layout r hr]

theorem testBit_stops (r : Fin 7 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 64*(M+1)^2 ∧
      (testBit r).Stops inp (d.toCfg (testBit (B := B) r).entry) t e ∧
      e.store = testBitStore r d := by
  obtain ⟨c₁, h₁, hcs₁⟩ := TapeMacros.copy_stops (r 0) (r 2) (r 6)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d
  have hbound₁ : ∀ j, c₁.reg j ≤ M := by
    change ∀ j, c₁.store.reg j ≤ M
    rw [hcs₁]
    exact setReg_bound _ _ 0 M (setReg_bound d _ _ M hd (hd (r 0))) (by omega)
  obtain ⟨c₂, h₂, hcs₂⟩ := TapeMacros.copy_stops (r 1) (r 5) (r 6)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₁.store
  rw [hcs₁] at hcs₂
  change c₂.store = bitPrepare r d at hcs₂
  have hbound₂ : ∀ j, c₂.reg j ≤ M := by
    change ∀ j, c₂.store.reg j ≤ M
    rw [hcs₂]
    dsimp [bitPrepare]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M
    · exact setReg_bound _ _ 0 M (setReg_bound d _ _ M hd (hd (r 0))) (by omega)
    · simp [reg_set_layout r hr]
      exact hd (r 1)
  have hcount : c₂.reg (r 5) = d.reg (r 1) := by
    change c₂.store.reg (r 5) = _
    rw [hcs₂]
    simp [bitPrepare, reg_set_layout r hr]
  obtain ⟨t, ht, h₃⟩ := shiftRight_stops (r 2) (r 3) (r 4) (r 5)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M (d.reg (r 1)) hM
    c₂.store hcount (hbound₂ (r 2)) (hbound₂ (r 3)) (hbound₂ (r 4))
  let d₃ := shiftStore (r 2) (r 3) (r 4) (r 5) (d.reg (r 1)) c₂.store
  have hbound₃ : ∀ j, d₃.reg j ≤ M :=
    shiftStore_bound _ _ _ _ M hM _ _ hbound₂ (hd (r 1))
  obtain ⟨c₄, h₄, hcs₄⟩ := halve_stops (r 2) (r 3) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d₃
  have hall := ((h₁.seq h₂).seq h₃).seq h₄
  have hpost : c₄.store = testBitStore r d := by
    rw [hcs₄]
    simp only [d₃, hcs₂, testBitStore]
  refine ⟨_, _, ?_, hall, hpost⟩
  have htime₁ : d.reg (r 2)+d.reg (r 6)+5*d.reg (r 0)+7 ≤ 7*M+7 := by
    have := hd (r 2); have := hd (r 6); have := hd (r 0); omega
  have htime₂ : c₁.reg (r 5)+c₁.reg (r 6)+5*c₁.reg (r 1)+7 ≤ 7*M+7 := by
    have := hbound₁ (r 5); have := hbound₁ (r 6); have := hbound₁ (r 1); omega
  have htime₄ : d₃.reg (r 3)+d₃.reg (r 4)+3*(d₃.reg (r 2)/2)+2*(d₃.reg (r 2)%2)+5 ≤ 4*M+5 := by
    have := hbound₃ (r 3); have := hbound₃ (r 4); have := hbound₃ (r 2)
    have := halveLoop_time_le (d₃.reg (r 2)); omega
  have ht' := ht.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right (5*M+9) (hd (r 1))) 1)
  simp only [TapeCfg.store]
  nlinarith

#print axioms halve_stops
#print axioms halfStep_stops
#print axioms shiftRight_stops
#print axioms shiftStore_src
#print axioms testBit_stops
#print axioms testBitStore_bit
end FieldPrograms
end ExpandingCodes.Computation
