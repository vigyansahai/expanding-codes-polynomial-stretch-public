import ExpandingCodes.Computation.FieldCoefficients
import ExpandingCodes.Computation.BinaryField

set_option autoImplicit false

namespace ExpandingCodes.Computation.FieldConvolution
open NKtLB FieldPrograms
open ExpandingCodes.PolynomialStretch
open BinaryPolynomial
variable {R B : ℕ}

/-- A five-label bit-product parity update. The two tested bits are disposable.
It uses only decrement/zero branches and one increment. -/
def toggle (x y p : Fin R) : TapeProgram R B 5 where
  entry := 0
  code i := if i = 0 then .dec x 4 1 else if i = 1 then .dec y 4 2
    else if i = 2 then .dec p 3 4 else if i = 3 then .inc p 4 else .halt

def toggleStore (x y p : Fin R) (d : TapeStore R B) : TapeStore R B :=
  if d.reg x = 0 then d else
    let d₁ := d.setReg x (d.reg x-1)
    if d.reg y = 0 then d₁ else
      let d₂ := d₁.setReg y (d.reg y-1)
      d₂.setReg p (if d.reg p = 0 then 1 else d.reg p-1)

theorem toggle_stops (x y p : Fin R) (hxy : x ≠ y) (hxp : x ≠ p) (hyp : y ≠ p)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ t, t ≤ 4 ∧ (toggle x y p).Stops inp (d.toCfg 0) t
      ((toggleStore x y p d).toCfg 4) := by
  have ha (i : Fin 5) (hi : i ≠ 4) : ¬ (toggle (B := B) x y p).halted (d.toCfg i) := by
    fin_cases i <;> simp_all [TapeProgram.halted, toggle]
  have hh (e : TapeStore R B) : (toggle x y p).halted (e.toCfg (4 : Fin 5)) := by
    simp [TapeProgram.halted, toggle]
  by_cases hx : d.reg x = 0
  · refine ⟨1, by omega, ⟨?_, hh _⟩⟩
    apply TapeProgram.Exec.one (ha 0 (by decide))
    simp [TapeProgram.step, toggle, toggleStore, hx]
  · let d₁ := d.setReg x (d.reg x-1)
    have hs₁ : (toggle x y p).step inp (d.toCfg 0) = d₁.toCfg 1 := by
      simp [TapeProgram.step, toggle, hx, d₁, TapeStore.setReg]
    have ha₁ : ¬ (toggle x y p).halted (d₁.toCfg (1 : Fin 5)) := by
      simp [TapeProgram.halted, toggle]
    by_cases hy : d.reg y = 0
    · refine ⟨2, by omega, ⟨?_, hh _⟩⟩
      apply TapeProgram.Exec.step (ha 0 (by decide)) hs₁
      apply TapeProgram.Exec.one ha₁
      simp [TapeProgram.step, toggle, toggleStore, hx, hy, d₁, TapeStore.setReg, Ne.symm hxy]
    · let d₂ := d₁.setReg y (d.reg y-1)
      have hs₂ : (toggle x y p).step inp (d₁.toCfg 1) = d₂.toCfg 2 := by
        simp [TapeProgram.step, toggle, d₂, d₁, TapeStore.setReg, Ne.symm hxy, hy]
      have ha₂ : ¬ (toggle x y p).halted (d₂.toCfg (2 : Fin 5)) := by
        simp [TapeProgram.halted, toggle]
      by_cases hp : d.reg p = 0
      · let d₃ := d₂.setReg p 0
        have hs₃ : (toggle x y p).step inp (d₂.toCfg 2) = d₃.toCfg 3 := by
          simp [TapeProgram.step, toggle, d₃, d₂, d₁, TapeStore.setReg,
            Ne.symm hxp, Ne.symm hyp, hp]
        refine ⟨4, by omega, ⟨?_, hh _⟩⟩
        apply TapeProgram.Exec.step (ha 0 (by decide)) hs₁
        apply TapeProgram.Exec.step ha₁ hs₂
        apply TapeProgram.Exec.step ha₂ hs₃
        apply TapeProgram.Exec.one
        · simp [TapeProgram.halted, toggle]
        · simp [TapeProgram.step, toggle, toggleStore, hx, hy, hp, d₃, d₂, d₁,
            TapeStore.setReg, Ne.symm hxp, Ne.symm hyp]
      · refine ⟨3, by omega, ⟨?_, hh _⟩⟩
        apply TapeProgram.Exec.step (ha 0 (by decide)) hs₁
        apply TapeProgram.Exec.step ha₁ hs₂
        apply TapeProgram.Exec.one ha₂
        simp [TapeProgram.step, toggle, toggleStore, hx, hy, hp, d₂, d₁,
          TapeStore.setReg, Ne.symm hxp, Ne.symm hyp]

theorem toggleStore_fresh (x y p j : Fin R) (d : TapeStore R B)
    (hjx : j ≠ x) (hjy : j ≠ y) (hjp : j ≠ p) :
    (toggleStore x y p d).reg j = d.reg j := by
  simp only [toggleStore]
  split <;> simp_all [TapeStore.setReg]
  split <;> simp_all [TapeStore.setReg]

theorem toggleStore_bound (x y p : Fin R) (d : TapeStore R B)
    (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (toggleStore x y p d).reg j ≤ M := by
  unfold toggleStore
  split
  · exact hd
  · split
    · exact setReg_bound _ _ _ M hd ((Nat.sub_le _ _).trans (hd x))
    · apply setReg_bound _ _ _ M
      · apply setReg_bound _ _ _ M
        · exact setReg_bound _ _ _ M hd ((Nat.sub_le _ _).trans (hd x))
        · exact (Nat.sub_le _ _).trans (hd y)
      · have := hd p
        split <;> omega

theorem toggleStore_parity (x y p : Fin R) (hxp : x ≠ p) (hyp : y ≠ p)
    (d : TapeStore R B) (hx : d.reg x ≤ 1) (hy : d.reg y ≤ 1) (hp : d.reg p ≤ 1) :
    (toggleStore x y p d).reg p = (d.reg p + d.reg x*d.reg y)%2 := by
  by_cases hx0 : d.reg x = 0
  · simp [toggleStore, hx0, Nat.mod_eq_of_lt (show d.reg p < 2 by omega)]
  · have hx1 : d.reg x = 1 := by omega
    by_cases hy0 : d.reg y = 0
    · simp [toggleStore, hx0, hy0, TapeStore.setReg, Ne.symm hxp,
        Nat.mod_eq_of_lt (show d.reg p < 2 by omega)]
    · have hy1 : d.reg y = 1 := by omega
      by_cases hp0 : d.reg p = 0
      · simp [toggleStore, hx1, hy1, hp0, TapeStore.setReg]
      · have hp1 : d.reg p = 1 := by omega
        simp [toggleStore, hx1, hy1, hp1, TapeStore.setReg]

/-- Shared scratch for the two actual coefficient extractions. -/
def leftLayout (r : Fin 12 → Fin R) : Fin 7 → Fin R :=
  fun i => r (![0,4,8,9,6,10,11] i)
def rightLayout (r : Fin 12 → Fin R) : Fin 7 → Fin R :=
  fun i => r (![1,5,8,9,7,10,11] i)

theorem leftLayout_injective (r : Fin 12 → Fin R) (hr : Function.Injective r) :
    Function.Injective (leftLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [leftLayout]

theorem rightLayout_injective (r : Fin 12 → Fin R) (hr : Function.Injective r) :
    Function.Injective (rightLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [rightLayout]

/-- One convolution summand: read both bits, conditionally toggle parity, and
advance the first index. The second index is the runtime loop counter. -/
def body (r : Fin 12 → Fin R) : TapeProgram R B 97 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (testBit (leftLayout r)) (testBit (rightLayout r)))
    (toggle (r 6) (r 7) (r 3))) (TapeMacros.increment (r 4))

def bodyStore (r : Fin 12 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let d₁ := testBitStore (leftLayout r) d
  let d₂ := testBitStore (rightLayout r) d₁
  let d₃ := toggleStore (r 6) (r 7) (r 3) d₂
  d₃.setReg (r 4) (d₃.reg (r 4)+1)

theorem testBitStore_bound (r : Fin 7 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (testBitStore r d).reg j ≤ M := by
  have hprep : ∀ j, (bitPrepare r d).reg j ≤ M := by
    unfold bitPrepare
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M
    · exact setReg_bound _ _ 0 M (setReg_bound d _ _ M hd (hd (r 0))) (by omega)
    · simp [reg_set_layout r hr]
      exact hd (r 1)
  have hs := shiftStore_bound (r 2) (r 3) (r 4) (r 5) M hM (d.reg (r 1))
    (bitPrepare r d) hprep (hd (r 1))
  unfold testBitStore halfStore
  apply setReg_bound _ _ _ M
  · apply setReg_bound _ _ _ M
    · exact setReg_bound _ _ 0 M hs (by omega)
    · exact (Nat.div_le_self _ _).trans (hs (r 2))
  · omega

theorem testBitStore_fresh (r : Fin 7 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₂ : j ≠ r 2) (h₃ : j ≠ r 3) (h₄ : j ≠ r 4)
    (h₅ : j ≠ r 5) (h₆ : j ≠ r 6) :
    (testBitStore r d).reg j = d.reg j := by
  simp only [testBitStore, halfStore, TapeStore.setReg, Function.update_of_ne h₂,
    Function.update_of_ne h₃, Function.update_of_ne h₄]
  rw [shiftStore_fresh _ _ _ _ _ h₂ h₃ h₄ h₅]
  simp [bitPrepare, TapeStore.setReg, h₂, h₅, h₆]

theorem reg_set (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i j : Fin 12) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j; simp
  · simp [TapeStore.setReg, h, hr.ne h]

theorem bodyStore_fresh (r : Fin 12 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₃ : j ≠ r 3) (h₄ : j ≠ r 4) (h₆ : j ≠ r 6) (h₇ : j ≠ r 7)
    (h₈ : j ≠ r 8) (h₉ : j ≠ r 9) (h₁₀ : j ≠ r 10) (h₁₁ : j ≠ r 11) :
    (bodyStore r d).reg j = d.reg j := by
  unfold bodyStore
  simp only [TapeStore.setReg, Function.update_of_ne h₄]
  rw [toggleStore_fresh _ _ _ _ _ h₆ h₇ h₃]
  rw [testBitStore_fresh _ _ _ h₈ h₉ h₇ h₁₀ h₁₁]
  exact testBitStore_fresh _ _ _ h₈ h₉ h₆ h₁₀ h₁₁

theorem bodyStore_index (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (bodyStore r d).reg (r 4) = d.reg (r 4)+1 := by
  unfold bodyStore
  simp only [TapeStore.setReg, Function.update_self]
  rw [toggleStore_fresh _ _ _ _ _ (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))]
  rw [testBitStore_fresh _ _ _ (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))]
  rw [testBitStore_fresh _ _ _ (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))]

/-- Ordinary raw binary convolution. This is only the specification of the
finite source program and is never an instruction or oracle. -/
def rawConvolution (a b k : ℕ) : ZMod 2 :=
  ∑ j ∈ Finset.range (k+1), bitEquiv (Nat.testBit a j) * bitEquiv (Nat.testBit b (k-j))

def bitValue (a j : ℕ) : ℕ := if Nat.testBit a j then 1 else 0

theorem bitValue_le (a j : ℕ) : bitValue a j ≤ 1 := by
  unfold bitValue; split <;> omega

theorem bodyStore_parity (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (hp : d.reg (r 3) ≤ 1) :
    (bodyStore r d).reg (r 3) =
      (d.reg (r 3) + bitValue (d.reg (r 0)) (d.reg (r 4)) *
        bitValue (d.reg (r 1)) (d.reg (r 5)))%2 := by
  let d₁ := testBitStore (leftLayout r) d
  let d₂ := testBitStore (rightLayout r) d₁
  have hf₁ (i : Fin 12) (h₂ : i ≠ 8) (h₃ : i ≠ 9) (h₄ : i ≠ 6)
      (h₅ : i ≠ 10) (h₆ : i ≠ 11) : d₁.reg (r i) = d.reg (r i) :=
    testBitStore_fresh _ _ _ (hr.ne h₂) (hr.ne h₃) (hr.ne h₄) (hr.ne h₅) (hr.ne h₆)
  have hf₂ (i : Fin 12) (h₂ : i ≠ 8) (h₃ : i ≠ 9) (h₄ : i ≠ 7)
      (h₅ : i ≠ 10) (h₆ : i ≠ 11) : d₂.reg (r i) = d₁.reg (r i) :=
    testBitStore_fresh _ _ _ (hr.ne h₂) (hr.ne h₃) (hr.ne h₄) (hr.ne h₅) (hr.ne h₆)
  have hp₂ : d₂.reg (r 3) = d.reg (r 3) := by
    rw [hf₂ 3 (by decide) (by decide) (by decide) (by decide) (by decide),
      hf₁ 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  have hx : d₂.reg (r 6) = bitValue (d.reg (r 0)) (d.reg (r 4)) := by
    rw [hf₂ 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact testBitStore_bit (leftLayout r) (leftLayout_injective r hr) d
  have hy : d₂.reg (r 7) = bitValue (d.reg (r 1)) (d.reg (r 5)) := by
    have h := testBitStore_bit (rightLayout r) (rightLayout_injective r hr) d₁
    change d₂.reg (r 7) = bitValue (d₁.reg (r 1)) (d₁.reg (r 5)) at h
    rw [h, hf₁ 1 (by decide) (by decide) (by decide) (by decide) (by decide),
      hf₁ 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  change ((toggleStore (r 6) (r 7) (r 3) d₂).setReg (r 4) _).reg (r 3) = _
  rw [reg_set r hr]
  simp only [show (3 : Fin 12) ≠ 4 from by decide, ite_false]
  rw [toggleStore_parity _ _ _ (hr.ne (by decide)) (hr.ne (by decide)) _
    (by rw [hx]; exact bitValue_le _ _) (by rw [hy]; exact bitValue_le _ _)
    (by rw [hp₂]; exact hp), hp₂, hx, hy]

theorem body_stops (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 128*(M+1)^2+8 ∧
      (body r).Stops inp (d.toCfg (body (B := B) r).entry) t e ∧
      e.store = bodyStore r d := by
  obtain ⟨t₁, c₁, ht₁, h₁, hs₁⟩ := testBit_stops (leftLayout r)
    (leftLayout_injective r hr) inp M hM d hd
  have hb₁ : ∀ j, c₁.store.reg j ≤ M := by
    rw [hs₁]; exact testBitStore_bound _ (leftLayout_injective r hr) _ M hM hd
  obtain ⟨t₂, c₂, ht₂, h₂, hs₂⟩ := testBit_stops (rightLayout r)
    (rightLayout_injective r hr) inp M hM c₁.store hb₁
  obtain ⟨t₃, ht₃, h₃⟩ := toggle_stops (r 6) (r 7) (r 3)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₂.store
  have h₄ := TapeMacros.increment_stops (r 4) inp (toggleStore (r 6) (r 7) (r 3) c₂.store)
  have hall := ((h₁.seq h₂).seq h₃).seq h₄
  refine ⟨_, _, by omega, hall, ?_⟩
  change (toggleStore (r 6) (r 7) (r 3) c₂.store).setReg (r 4) _ = _
  rw [hs₂, hs₁]
  rfl

theorem bodyStore_bound (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M)
    (hj : d.reg (r 4)+1 ≤ M) : ∀ j, (bodyStore r d).reg j ≤ M := by
  have h₁ := testBitStore_bound (leftLayout r) (leftLayout_injective r hr) d M hM hd
  have h₂ := testBitStore_bound (rightLayout r) (rightLayout_injective r hr) _ M hM h₁
  have h₃ := toggleStore_bound (r 6) (r 7) (r 3) _ M hM h₂
  apply setReg_bound _ _ _ M h₃
  have he := bodyStore_index r hr d
  have he' : (toggleStore (r 6) (r 7) (r 3)
      (testBitStore (rightLayout r) (testBitStore (leftLayout r) d))).reg (r 4)+1 =
      d.reg (r 4)+1 := by
    simpa only [bodyStore, TapeStore.setReg, Function.update_self] using he
  rw [he']
  exact hj

/-- The finite runtime counted loop. It has ninety-nine labels for every
input and every field size. -/
def loop (r : Fin 12 → Fin R) : TapeProgram R B 99 :=
  TapeProgram.countedLoop (body r) (r 5)

def loopStore (r : Fin 12 → Fin R) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d
  | n+1, d => loopStore r n (bodyStore r (d.setReg (r 5) n))

theorem loop_stops (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hn : d.reg (r 5) = n) (hd : ∀ j, d.reg j ≤ M)
    (hj : d.reg (r 4)+n ≤ M) :
    ∃ t, t ≤ n*(128*(M+1)^2+10)+1 ∧
      (loop r).Stops inp (d.toCfg (TapeProgram.loopHeader 97)) t
        ((loopStore r n d).toCfg (TapeProgram.loopExit 97)) := by
  induction n generalizing d with
  | zero => exact ⟨1, by omega, TapeProgram.loop_zero (body r) (r 5) inp d hn⟩
  | succ n ih =>
    let d₁ := d.setReg (r 5) n
    have hb₁ : ∀ j, d₁.reg j ≤ M :=
      setReg_bound d _ n M hd (by have := hd (r 5); omega)
    obtain ⟨s, c, hs, hc, hcs⟩ := body_stops r hr inp M hM d₁ hb₁
    have hcn : c.reg (r 5) = n := by
      change c.store.reg (r 5) = _
      rw [hcs, bodyStore_fresh r d₁ (r 5) (hr.ne (by decide)) (hr.ne (by decide))
        (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
        (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))]
      simp [d₁]
    have hcj : c.reg (r 4) = d.reg (r 4)+1 := by
      change c.store.reg (r 4) = _
      rw [hcs, bodyStore_index r hr]
      simp [d₁, reg_set r hr]
    have hcb : ∀ j, c.store.reg j ≤ M := by
      rw [hcs]
      apply bodyStore_bound r hr d₁ M hM hb₁
      simp only [d₁, reg_set r hr, show (4 : Fin 12) ≠ 5 from by decide, ite_false]
      omega
    obtain ⟨t, ht, htail⟩ := ih c.store hcn hcb (by change c.reg (r 4)+n ≤ M; omega)
    have hhead := TapeProgram.loop_positive_header (body r) (r 5) inp d (by omega)
    have hdec : TapeProgram.decStore (r 5) d = d₁ := by
      simp [TapeProgram.decStore, d₁, TapeStore.setReg, hn]
    rw [hdec] at hhead
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (body r) (r 5))
    have hreturn := TapeProgram.loop_body_return (body r) (r 5) inp c hc.halted
    have hpost : loopStore r n c.store = loopStore r (n+1) d := by rw [loopStore, hcs]
    have hall := ((hhead.trans hrun).trans hreturn).trans htail.exec
    rw [hpost] at hall
    refine ⟨_, ?_, ⟨hall, TapeProgram.loop_code_exit (body r) (r 5)⟩⟩
    change 1+s+1+t ≤ (n+1)*(128*(M+1)^2+10)+1
    calc
      1+s+1+t ≤ 1+(128*(M+1)^2+8)+1+(n*(128*(M+1)^2+10)+1) := by omega
      _ = (n+1)*(128*(M+1)^2+10)+1 := by ring

theorem loopStore_fresh (r : Fin 12 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₃ : j ≠ r 3) (h₄ : j ≠ r 4) (h₅ : j ≠ r 5)
    (h₆ : j ≠ r 6) (h₇ : j ≠ r 7) (h₈ : j ≠ r 8) (h₉ : j ≠ r 9)
    (h₁₀ : j ≠ r 10) (h₁₁ : j ≠ r 11) (n : ℕ) :
    (loopStore r n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [loopStore, ih, bodyStore_fresh r _ j h₃ h₄ h₆ h₇ h₈ h₉ h₁₀ h₁₁]
    simp [TapeStore.setReg, h₅]

theorem loopStore_count (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) (hn : d.reg (r 5) = n) :
    (loopStore r n d).reg (r 5) = 0 := by
  induction n generalizing d with
  | zero => exact hn
  | succ n ih =>
    rw [loopStore]
    apply ih
    rw [bodyStore_fresh r _ (r 5) (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))]
    simp

theorem bitValue_cast (a j : ℕ) : (bitValue a j : ZMod 2) = bitEquiv (Nat.testBit a j) := by
  cases h : Nat.testBit a j <;> simp [bitValue, h, bitEquiv]

theorem bodyStore_parity_cast (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (hp : d.reg (r 3) ≤ 1) :
    ((bodyStore r d).reg (r 3) : ZMod 2) = (d.reg (r 3) : ZMod 2) +
      bitEquiv (Nat.testBit (d.reg (r 0)) (d.reg (r 4))) *
      bitEquiv (Nat.testBit (d.reg (r 1)) (d.reg (r 5))) := by
  rw [bodyStore_parity r hr d hp, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul,
    bitValue_cast, bitValue_cast]

theorem loopStore_parity (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (a b k n : ℕ) (d : TapeStore R B) (ha : d.reg (r 0) = a) (hb : d.reg (r 1) = b)
    (hp : d.reg (r 3) ≤ 1) (hj : d.reg (r 4)+n = k+1)
    (hpar : (d.reg (r 3) : ZMod 2) = ∑ j ∈ Finset.range (d.reg (r 4)),
      bitEquiv (Nat.testBit a j)*bitEquiv (Nat.testBit b (k-j))) :
    ((loopStore r n d).reg (r 3) : ZMod 2) = rawConvolution a b k := by
  induction n generalizing d with
  | zero => simpa [loopStore, rawConvolution, show d.reg (r 4) = k+1 by omega] using hpar
  | succ n ih =>
    let d₁ := d.setReg (r 5) n
    have hframe (i : Fin 12) (hi : i = 0 ∨ i = 1) :
        (bodyStore r d₁).reg (r i) = d.reg (r i) := by
      rcases hi with rfl | rfl
      all_goals
        rw [bodyStore_fresh r _ _ (hr.ne (by decide)) (hr.ne (by decide))
          (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
          (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))]
        simp [d₁, reg_set r hr]
    have hp₁ : d₁.reg (r 3) = d.reg (r 3) := by simp [d₁, reg_set r hr]
    have hj₁ : d₁.reg (r 4) = d.reg (r 4) := by simp [d₁, reg_set r hr]
    have hnextj : (bodyStore r d₁).reg (r 4) = d.reg (r 4)+1 := by
      rw [bodyStore_index r hr, hj₁]
    rw [loopStore]
    apply ih (bodyStore r d₁) ((hframe 0 (Or.inl rfl)).trans ha)
      ((hframe 1 (Or.inr rfl)).trans hb)
    · rw [bodyStore_parity r hr d₁ (by rw [hp₁]; exact hp)]
      omega
    · omega
    · rw [bodyStore_parity_cast r hr d₁ (by rw [hp₁]; exact hp), hp₁, hpar,
        hnextj, Finset.sum_range_succ]
      have ha₁ : d₁.reg (r 0) = a := by simp [d₁, reg_set r hr, ha]
      have hb₁ : d₁.reg (r 1) = b := by simp [d₁, reg_set r hr, hb]
      have hc₁ : d₁.reg (r 5) = k-d.reg (r 4) := by simp [d₁]; omega
      rw [ha₁, hb₁, hj₁, hc₁]

/-- Initialization uses only actual unary counter macros. -/
def prepare (r : Fin 12 → Fin R) : TapeProgram R B 17 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeMacros.clear (r 3))
    (TapeMacros.clear (r 4))) (TapeMacros.copy (r 2) (r 5) (r 11)))
    (TapeMacros.increment (r 5))

def prepareStore (r : Fin 12 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let d₁ := (d.setReg (r 3) 0).setReg (r 4) 0
  let d₂ := (d₁.setReg (r 5) (d₁.reg (r 2))).setReg (r 11) 0
  d₂.setReg (r 5) (d₂.reg (r 5)+1)

theorem prepare_stops (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (prepare r).Stops inp (d.toCfg (prepare (B := B) r).entry)
      (d.reg (r 3)+d.reg (r 4)+d.reg (r 5)+d.reg (r 11)+5*d.reg (r 2)+13) e ∧
      e.store = prepareStore r d := by
  have h₁ := TapeMacros.clear_stops (r 3) inp (d.reg (r 3)) d rfl
  have h₂ := TapeMacros.clear_stops (r 4) inp (d.reg (r 4)) (d.setReg (r 3) 0)
    (by simp [reg_set r hr])
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops (r 2) (r 5) (r 11)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp
    ((d.setReg (r 3) 0).setReg (r 4) 0)
  have h₄ := TapeMacros.increment_stops (r 5) inp c.store
  have hall := ((h₁.seq h₂).seq hc).seq h₄
  refine ⟨((c.store.setReg (r 5) (c.store.reg (r 5)+1)).toCfg (1 : Fin 2)).mapPC
    (TapeProgram.rightLabel 15), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | (simp [reg_set r hr]; omega)
  · change c.store.setReg (r 5) _ = _
    rw [hcs]
    rfl

theorem prepareStore_reg (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 12) :
    (prepareStore r d).reg (r i) =
      if i = 5 then d.reg (r 2)+1 else if i = 3 ∨ i = 4 ∨ i = 11 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [prepareStore, reg_set r hr]

theorem prepareStore_bound (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (M : ℕ) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (prepareStore r d).reg j ≤ M+1 := by
  unfold prepareStore
  apply setReg_bound _ _ _ (M+1)
  · apply setReg_bound _ _ 0 (M+1) _ (by omega)
    apply setReg_bound _ _ _ (M+1)
    · apply setReg_bound _ _ 0 (M+1) _ (by omega)
      exact setReg_bound d _ 0 (M+1) (fun j => (hd j).trans (by omega)) (by omega)
    · simp only [reg_set r hr]
      simp
      have := hd (r 2); omega
  · simp [reg_set r hr]
    exact hd (r 2)

/-- Fixed 116-label convolution coefficient source program. Its field-size
parameters are data in runtime registers, never source-code indices. -/
def convolution (r : Fin 12 → Fin R) : TapeProgram R B 116 :=
  TapeProgram.seq (prepare r) (loop r)

def convolutionStore (r : Fin 12 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  loopStore r (d.reg (r 2)+1) (prepareStore r d)

theorem convolution_stops_exact (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 1000*(M+1)^3 ∧
      (convolution r).Stops inp (d.toCfg (convolution (B := B) r).entry) t e ∧
      e.store = convolutionStore r d := by
  obtain ⟨c, hc, hcs⟩ := prepare_stops r hr inp d
  have hcb : ∀ j, c.store.reg j ≤ M+1 := by rw [hcs]; exact prepareStore_bound r hr d M hd
  have hcn : c.reg (r 5) = d.reg (r 2)+1 := by
    change c.store.reg (r 5) = _
    rw [hcs, prepareStore_reg r hr]; simp
  have hcj : c.reg (r 4) = 0 := by
    change c.store.reg (r 4) = _
    rw [hcs, prepareStore_reg r hr]; simp
  obtain ⟨t, ht, he⟩ := loop_stops r hr inp (M+1) (by omega)
    (d.reg (r 2)+1) c.store hcn hcb (by simp only [TapeCfg.store, hcj]; have := hd (r 2); omega)
  have hall := hc.seq he
  refine ⟨_, _, ?_, hall, ?_⟩
  · have hp : d.reg (r 3)+d.reg (r 4)+d.reg (r 5)+d.reg (r 11)+5*d.reg (r 2)+13 ≤ 9*M+13 := by
      have := hd (r 3); have := hd (r 4); have := hd (r 5)
      have := hd (r 11); have := hd (r 2); omega
    have hb : 128*(M+1+1)^2+10 ≤ 522*(M+1)^2 := by nlinarith
    have hm := Nat.mul_le_mul (Nat.add_le_add_right (hd (r 2)) 1) hb
    have heq : (M+1)*(522*(M+1)^2) = 522*(M+1)^3 := by ring
    rw [heq] at hm
    have ht' : t ≤ 522*(M+1)^3+1 := ht.trans (Nat.add_le_add_right hm 1)
    have hcub : M+1 ≤ (M+1)^3 := by nlinarith
    change d.reg (r 3)+d.reg (r 4)+d.reg (r 5)+d.reg (r 11)+5*d.reg (r 2)+13+1+t ≤ _
    omega
  · change loopStore r (d.reg (r 2)+1) c.store = _
    rw [hcs]
    rfl

theorem loopStore_parity_le (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) (hp : d.reg (r 3) ≤ 1) :
    (loopStore r n d).reg (r 3) ≤ 1 := by
  induction n generalizing d with
  | zero => exact hp
  | succ n ih =>
    rw [loopStore]
    apply ih
    rw [bodyStore_parity r hr _ (by simpa [reg_set r hr] using hp)]
    omega

theorem convolutionStore_parity (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) :
    ((convolutionStore r d).reg (r 3) : ZMod 2) =
      rawConvolution (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 2)) := by
  apply loopStore_parity r hr _ _ _ _ (prepareStore r d)
  · simp [prepareStore_reg r hr]
  · simp [prepareStore_reg r hr]
  · simp [prepareStore_reg r hr]
  · simp [prepareStore_reg r hr]
  · simp [prepareStore_reg r hr]

theorem convolutionStore_bit (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (convolutionStore r d).reg (r 3) ≤ 1 := by
  apply loopStore_parity_le r hr
  simp [prepareStore_reg r hr]

theorem convolutionStore_input (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 12) (hi : i = 0 ∨ i = 1 ∨ i = 2) :
    (convolutionStore r d).reg (r i) = d.reg (r i) := by
  rcases hi with rfl | rfl | rfl
  all_goals
    rw [convolutionStore, loopStore_fresh r _ _ (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))]
    simp [prepareStore_reg r hr]

/-- All read-only heads, output bits, explicit buffer contents and heads. -/
def tapeData (d : TapeStore R B) :
    (Fin 4 → ℕ) × List Bool × (Fin B → List Sym) × (Fin B → ℕ) :=
  (d.roHead, d.output, d.bufferTape, d.bufferHead)

@[simp] theorem tapeData_setReg (d : TapeStore R B) (i : Fin R) (n : ℕ) :
    tapeData (d.setReg i n) = tapeData d := rfl

theorem shiftStore_tapeData (s q p c : Fin R) (n : ℕ) (d : TapeStore R B) :
    tapeData (shiftStore s q p c n d) = tapeData d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [shiftStore, ih]
    rfl

theorem testBitStore_tapeData (r : Fin 7 → Fin R) (d : TapeStore R B) :
    tapeData (testBitStore r d) = tapeData d := by
  unfold testBitStore halfStore
  simp only [tapeData_setReg, shiftStore_tapeData]
  rfl

theorem toggleStore_tapeData (x y p : Fin R) (d : TapeStore R B) :
    tapeData (toggleStore x y p d) = tapeData d := by
  unfold toggleStore
  split
  · rfl
  · split <;> rfl

theorem bodyStore_tapeData (r : Fin 12 → Fin R) (d : TapeStore R B) :
    tapeData (bodyStore r d) = tapeData d := by
  simp only [bodyStore, tapeData_setReg, toggleStore_tapeData, testBitStore_tapeData]

theorem loopStore_tapeData (r : Fin 12 → Fin R) (n : ℕ) (d : TapeStore R B) :
    tapeData (loopStore r n d) = tapeData d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [loopStore, ih, bodyStore_tapeData, tapeData_setReg]

theorem convolutionStore_tapeData (r : Fin 12 → Fin R) (d : TapeStore R B) :
    tapeData (convolutionStore r d) = tapeData d := by
  rw [convolutionStore, loopStore_tapeData]
  rfl

/-- Runtime bounds for every working counter, including the final position. -/
theorem loopStore_bound (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) (hj : d.reg (r 4)+n ≤ M) (hn : n ≤ M) :
    ∀ j, (loopStore r n d).reg j ≤ M := by
  induction n generalizing d with
  | zero => exact hd
  | succ n ih =>
    rw [loopStore]
    have hb := setReg_bound d (r 5) n M hd (by omega)
    apply ih _ (bodyStore_bound r hr _ M hM hb (by simp [reg_set r hr]; omega))
    · rw [bodyStore_index r hr]
      simp only [reg_set r hr, show (4 : Fin 12) ≠ 5 from by decide, ite_false]
      omega
    · omega

theorem convolutionStore_bound (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (convolutionStore r d).reg j ≤ M+1 := by
  apply loopStore_bound r hr (M+1) (by omega) _ _ (prepareStore_bound r hr d M hd)
  · simp [prepareStore_reg r hr]
    exact hd (r 2)
  · exact Nat.add_le_add_right (hd (r 2)) 1

theorem convolutionStore_fresh (r : Fin 12 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₃ : j ≠ r 3) (h₄ : j ≠ r 4) (h₅ : j ≠ r 5)
    (h₆ : j ≠ r 6) (h₇ : j ≠ r 7) (h₈ : j ≠ r 8) (h₉ : j ≠ r 9)
    (h₁₀ : j ≠ r 10) (h₁₁ : j ≠ r 11) :
    (convolutionStore r d).reg j = d.reg j := by
  rw [convolutionStore, loopStore_fresh r _ j h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁]
  simp [prepareStore, TapeStore.setReg, h₃, h₄, h₅, h₁₁]

theorem prepareStore_bound_of (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (M : ℕ) (hd : ∀ j, d.reg j ≤ M) (hk : d.reg (r 2)+1 ≤ M) :
    ∀ j, (prepareStore r d).reg j ≤ M := by
  unfold prepareStore
  apply setReg_bound _ _ _ M
  · apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M
    · exact setReg_bound _ _ 0 M (setReg_bound d _ 0 M hd (by omega)) (by omega)
    · simp [reg_set r hr]
      exact hd (r 2)
  · simpa [reg_set r hr] using hk

theorem convolutionStore_bound_of (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hk : d.reg (r 2)+1 ≤ M) : ∀ j, (convolutionStore r d).reg j ≤ M := by
  apply loopStore_bound r hr M hM _ _ (prepareStore_bound_of r hr d M hd hk)
  · simpa [prepareStore_reg r hr] using hk
  · exact hk

/-- Exact coefficient encoding, including high zero padding. -/
theorem bufferCoefficient_bit (ell : ℕ) (a : Fin (2^ell)) (j : ℕ) :
    BinaryField.bufferCoefficient (indexEquiv ell a) j = bitEquiv (Nat.testBit a.val j) := by
  unfold BinaryField.bufferCoefficient
  split_ifs with hj
  · exact indexEquiv_bit ell a ⟨j, hj⟩
  · rw [Nat.testBit_lt_two_pow (a.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
    rfl

theorem rawConvolution_eq_convolution (ell₁ ell₂ : ℕ) (a : Fin (2^ell₁))
    (b : Fin (2^ell₂)) (k : ℕ) :
    rawConvolution a.val b.val k =
      BinaryField.convolution (indexEquiv ell₁ a) (indexEquiv ell₂ b) k := by
  simp only [rawConvolution, BinaryField.convolution, bufferCoefficient_bit]

theorem rawConvolution_eq_productCoefficient (ell₁ ell₂ : ℕ)
    (a : Fin (2^ell₁)) (b : Fin (2^ell₂)) (k : ℕ) :
    rawConvolution (2^ell₁+a.val) (2^ell₂+b.val) k =
      productCoefficient ell₁ ell₂ a b k := by
  simp only [rawConvolution, productCoefficient, candidateCoefficient_bit]

/-- Complete source contract: actual fixed code, polynomial source time, exact
coefficient, bit-valued result, preserved operands, and untouched tapes. -/
theorem convolution_stops (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 1000*(M+1)^3 ∧
      (convolution r).Stops inp (d.toCfg (convolution (B := B) r).entry) t e ∧
      (e.reg (r 3) : ZMod 2) = rawConvolution (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 2)) ∧
      e.reg (r 3) ≤ 1 ∧
      (∀ i, i = 0 ∨ i = 1 ∨ i = 2 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j, e.reg j ≤ M+1) ∧ tapeData e.store = tapeData d := by
  obtain ⟨t, e, ht, he, hs⟩ := convolution_stops_exact r hr inp M hM d hd
  refine ⟨t, e, ht, he, ?_, ?_, ?_, ?_, ?_⟩
  · change (e.store.reg (r 3) : ZMod 2) = _
    rw [hs]; exact convolutionStore_parity r hr d
  · change e.store.reg (r 3) ≤ 1
    rw [hs]; exact convolutionStore_bit r hr d
  · intro i hi
    change e.store.reg (r i) = _
    rw [hs]; exact convolutionStore_input r hr d i hi
  · change ∀ j, e.store.reg j ≤ M+1
    rw [hs]; exact convolutionStore_bound r hr M d hd
  · rw [hs]; exact convolutionStore_tapeData r d

#print axioms convolution_stops_exact
#print axioms convolution_stops
#print axioms rawConvolution_eq_convolution
#print axioms rawConvolution_eq_productCoefficient
end ExpandingCodes.Computation.FieldConvolution
