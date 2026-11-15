import ExpandingCodes.Computation.FieldConvolution

set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.FieldCertificates
open NKtLB FieldPrograms FieldConvolution
open ExpandingCodes.PolynomialStretch
open BinaryPolynomial
variable {R B : ℕ}

/-- Exclusive-or into a bit register, using a disposable unit scratch and the
checked actual conditional toggle. The code has nine labels. -/
def xorInto (x unit p : Fin R) : TapeProgram R B 9 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.clear unit) (TapeMacros.increment unit))
    (toggle x unit p)

def xorStore (x unit p : Fin R) (d : TapeStore R B) : TapeStore R B :=
  toggleStore x unit p (d.setReg unit 1)

theorem xorInto_stops (x unit p : Fin R) (hxu : x ≠ unit) (hxp : x ≠ p) (hup : unit ≠ p)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ t e, t ≤ d.reg unit+8 ∧
      (xorInto x unit p).Stops inp (d.toCfg (xorInto (B := B) x unit p).entry) t e ∧
      e.store = xorStore x unit p d := by
  have h₁ := TapeMacros.clear_stops unit inp (d.reg unit) d rfl
  have h₂ := TapeMacros.increment_stops unit inp (d.setReg unit 0)
  have hz : (d.setReg unit 0).reg unit = 0 := by simp [TapeStore.setReg]
  rw [hz, zero_add] at h₂
  obtain ⟨t, ht, h₃⟩ := toggle_stops x unit p hxu hxp hup inp ((d.setReg unit 0).setReg unit 1)
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_, _, by omega, hall, ?_⟩
  change toggleStore x unit p ((d.setReg unit 0).setReg unit 1) = _
  simp only [TapeStore.setReg_same]
  rfl

theorem xorStore_parity (x unit p : Fin R) (hxu : x ≠ unit) (hxp : x ≠ p) (hup : unit ≠ p)
    (d : TapeStore R B) (hx : d.reg x ≤ 1) (hp : d.reg p ≤ 1) :
    (xorStore x unit p d).reg p = (d.reg p+d.reg x)%2 := by
  unfold xorStore
  rw [toggleStore_parity x unit p hxp hup]
  · simp [TapeStore.setReg, hxu, Ne.symm hup]
  · simpa [TapeStore.setReg, hxu] using hx
  · simp [TapeStore.setReg]
  · simpa [TapeStore.setReg, Ne.symm hup] using hp

theorem xorStore_fresh (x unit p j : Fin R) (d : TapeStore R B)
    (hjx : j ≠ x) (hju : j ≠ unit) (hjp : j ≠ p) :
    (xorStore x unit p d).reg j = d.reg j := by
  rw [xorStore, toggleStore_fresh x unit p j _ hjx hju hjp]
  simp [TapeStore.setReg, hju]

theorem xorStore_bound (x unit p : Fin R) (d : TapeStore R B)
    (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (xorStore x unit p d).reg j ≤ M :=
  toggleStore_bound x unit p _ M hM (setReg_bound d unit 1 M hd hM)

theorem xorStore_tapeData (x unit p : Fin R) (d : TapeStore R B) :
    tapeData (xorStore x unit p d) = tapeData d := by
  rw [xorStore, toggleStore_tapeData, tapeData_setReg]

/-- Clear a success bit if a disposable parity bit is nonzero. -/
def requireZero (x flag : Fin R) : TapeProgram R B 3 where
  entry := 0
  code i := if i = 0 then .dec x 2 1 else if i = 1 then .dec flag 2 2 else .halt

def requireStore (x flag : Fin R) (d : TapeStore R B) : TapeStore R B :=
  if d.reg x = 0 then d else (d.setReg x (d.reg x-1)).setReg flag (d.reg flag-1)

theorem requireZero_stops (x flag : Fin R) (hxf : x ≠ flag)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ t, t ≤ 2 ∧ (requireZero x flag).Stops inp (d.toCfg 0) t
      ((requireStore x flag d).toCfg 2) := by
  by_cases hx : d.reg x = 0
  · refine ⟨1, by omega, ⟨?_, ?_⟩⟩
    · apply TapeProgram.Exec.one
      · simp [TapeProgram.halted, requireZero]
      · simp [TapeProgram.step, requireZero, requireStore, hx]
    · simp [TapeProgram.halted, requireZero]
  · refine ⟨2, by omega, ⟨?_, ?_⟩⟩
    · apply TapeProgram.Exec.step (d := (d.setReg x (d.reg x-1)).toCfg 1)
      · simp [TapeProgram.halted, requireZero]
      · simp [TapeProgram.step, requireZero, hx, TapeStore.setReg]
      · apply TapeProgram.Exec.one
        · simp [TapeProgram.halted, requireZero]
        · by_cases hf : d.reg flag = 0
          · simp [TapeProgram.step, requireZero, requireStore, hx, hf, TapeStore.setReg, Ne.symm hxf]
          · simp [TapeProgram.step, requireZero, requireStore, hx, hf, TapeStore.setReg, Ne.symm hxf]
    · simp [TapeProgram.halted, requireZero]

theorem requireStore_flag (x flag : Fin R) (hxf : x ≠ flag)
    (d : TapeStore R B) (hf : d.reg flag ≤ 1) :
    (requireStore x flag d).reg flag = if d.reg x = 0 then d.reg flag else 0 := by
  by_cases hx : d.reg x = 0
  · simp [requireStore, hx]
  · simp [requireStore, hx, TapeStore.setReg]
    omega

theorem requireStore_fresh (x flag j : Fin R) (d : TapeStore R B)
    (hjx : j ≠ x) (hjf : j ≠ flag) : (requireStore x flag d).reg j = d.reg j := by
  unfold requireStore
  split <;> simp_all [TapeStore.setReg]

theorem requireStore_bound (x flag : Fin R) (d : TapeStore R B)
    (M : ℕ) (hd : ∀ j, d.reg j ≤ M) : ∀ j, (requireStore x flag d).reg j ≤ M := by
  unfold requireStore
  split
  · exact hd
  · apply setReg_bound _ _ _ M
    · exact setReg_bound d x _ M hd ((Nat.sub_le _ _).trans (hd x))
    · exact (Nat.sub_le _ _).trans (hd flag)

theorem requireStore_tapeData (x flag : Fin R) (d : TapeStore R B) :
    tapeData (requireStore x flag d) = tapeData d := by
  unfold requireStore
  split <;> rfl

/-- Runtime register layout: inputs a,b,r,monic(m),s,k; success flag; three
coefficient bits; and eight shared convolution scratch counters. -/
def leftLayout (r : Fin 18 → Fin R) : Fin 12 → Fin R :=
  fun i => r (![0,1,5,7,10,11,12,13,14,15,16,17] i)
def rightLayout (r : Fin 18 → Fin R) : Fin 12 → Fin R :=
  fun i => r (![3,4,5,8,10,11,12,13,14,15,16,17] i)
def remainderLayout (r : Fin 18 → Fin R) : Fin 7 → Fin R :=
  fun i => r (![2,5,14,15,9,16,17] i)

theorem leftLayout_injective (r : Fin 18 → Fin R) (hr : Function.Injective r) :
    Function.Injective (leftLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [leftLayout]

theorem rightLayout_injective (r : Fin 18 → Fin R) (hr : Function.Injective r) :
    Function.Injective (rightLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [rightLayout]

theorem remainderLayout_injective (r : Fin 18 → Fin R) (hr : Function.Injective r) :
    Function.Injective (remainderLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [remainderLayout]

/-- One actual coefficient equation test, accumulating its answer in a bit
flag. Neither Polynomial nor arithmetic oracles occur in this finite source. -/
def coefficient (r : Fin 18 → Fin R) : TapeProgram R B 298 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeProgram.seq (convolution (leftLayout r)) (convolution (rightLayout r)))
    (testBit (remainderLayout r))) (xorInto (r 8) (r 16) (r 7)))
    (xorInto (r 9) (r 16) (r 7))) (requireZero (r 7) (r 6))

def coefficientStore (r : Fin 18 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let d₁ := convolutionStore (leftLayout r) d
  let d₂ := convolutionStore (rightLayout r) d₁
  let d₃ := testBitStore (remainderLayout r) d₂
  let d₄ := xorStore (r 8) (r 16) (r 7) d₃
  let d₅ := xorStore (r 9) (r 16) (r 7) d₄
  requireStore (r 7) (r 6) d₅

theorem reg_set (r : Fin 18 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i j : Fin 18) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j; simp
  · simp [TapeStore.setReg, h, hr.ne h]

theorem leftStore_fresh (r : Fin 18 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 18) (hi : i ≠ 7) (hlt : i < 10) :
    (convolutionStore (leftLayout r) d).reg (r i) = d.reg (r i) := by
  exact convolutionStore_fresh _ _ _
    (hr.ne hi)
    (hr.ne (show i ≠ (10:Fin 18) from by omega))
    (hr.ne (show i ≠ (11:Fin 18) from by omega))
    (hr.ne (show i ≠ (12:Fin 18) from by omega))
    (hr.ne (show i ≠ (13:Fin 18) from by omega))
    (hr.ne (show i ≠ (14:Fin 18) from by omega))
    (hr.ne (show i ≠ (15:Fin 18) from by omega))
    (hr.ne (show i ≠ (16:Fin 18) from by omega))
    (hr.ne (show i ≠ (17:Fin 18) from by omega))


theorem rightStore_fresh (r : Fin 18 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 18) (hi : i ≠ 8) (hlt : i < 10) :
    (convolutionStore (rightLayout r) d).reg (r i) = d.reg (r i) := by
  exact convolutionStore_fresh _ _ _
    (hr.ne hi)
    (hr.ne (show i ≠ (10:Fin 18) from by omega))
    (hr.ne (show i ≠ (11:Fin 18) from by omega))
    (hr.ne (show i ≠ (12:Fin 18) from by omega))
    (hr.ne (show i ≠ (13:Fin 18) from by omega))
    (hr.ne (show i ≠ (14:Fin 18) from by omega))
    (hr.ne (show i ≠ (15:Fin 18) from by omega))
    (hr.ne (show i ≠ (16:Fin 18) from by omega))
    (hr.ne (show i ≠ (17:Fin 18) from by omega))


theorem remainderStore_fresh (r : Fin 18 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 18) (hi : i ≠ 9) (hlt : i < 14) :
    (testBitStore (remainderLayout r) d).reg (r i) = d.reg (r i) := by
  exact testBitStore_fresh _ _ _
    (hr.ne (show i ≠ (14:Fin 18) from by omega))
    (hr.ne (show i ≠ (15:Fin 18) from by omega)) (hr.ne hi)
    (hr.ne (show i ≠ (16:Fin 18) from by omega))
    (hr.ne (show i ≠ (17:Fin 18) from by omega))

theorem coefficient_stops_exact (r : Fin 18 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) (hk : d.reg (r 5)+1 ≤ M) :
    ∃ t e, t ≤ 2200*(M+1)^3 ∧
      (coefficient r).Stops inp (d.toCfg (coefficient (B := B) r).entry) t e ∧
      e.store = coefficientStore r d := by
  obtain ⟨t₁, c₁, ht₁, h₁, hs₁⟩ := convolution_stops_exact (leftLayout r)
    (leftLayout_injective r hr) inp M hM d hd
  have hb₁ : ∀ j, c₁.store.reg j ≤ M := by
    rw [hs₁]; exact convolutionStore_bound_of _ (leftLayout_injective r hr) M hM d hd hk
  have hk₁ : c₁.reg (r 5)+1 ≤ M := by
    change c₁.store.reg (r 5)+1 ≤ M
    rw [hs₁, leftStore_fresh r hr _ 5 (by decide) (by decide)]
    exact hk
  obtain ⟨t₂, c₂, ht₂, h₂, hs₂⟩ := convolution_stops_exact (rightLayout r)
    (rightLayout_injective r hr) inp M hM c₁.store hb₁
  have hb₂ : ∀ j, c₂.store.reg j ≤ M := by
    rw [hs₂]; exact convolutionStore_bound_of _ (rightLayout_injective r hr) M hM _ hb₁ hk₁
  obtain ⟨t₃, c₃, ht₃, h₃, hs₃⟩ := testBit_stops (remainderLayout r)
    (remainderLayout_injective r hr) inp M hM c₂.store hb₂
  have hb₃ : ∀ j, c₃.store.reg j ≤ M := by
    rw [hs₃]; exact testBitStore_bound _ (remainderLayout_injective r hr) _ M hM hb₂
  obtain ⟨t₄, c₄, ht₄, h₄, hs₄⟩ := xorInto_stops (r 8) (r 16) (r 7)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₃.store
  have hb₄ : ∀ j, c₄.store.reg j ≤ M := by
    rw [hs₄]; exact xorStore_bound _ _ _ _ M hM hb₃
  obtain ⟨t₅, c₅, ht₅, h₅, hs₅⟩ := xorInto_stops (r 9) (r 16) (r 7)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₄.store
  obtain ⟨t₆, ht₆, h₆⟩ := requireZero_stops (r 7) (r 6) (hr.ne (by decide)) inp c₅.store
  have hall := ((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆
  refine ⟨_, _, ?_, hall, ?_⟩
  · have h₄' : t₄ ≤ M+8 := ht₄.trans (Nat.add_le_add_right (hb₃ (r 16)) 8)
    have h₅' : t₅ ≤ M+8 := ht₅.trans (Nat.add_le_add_right (hb₄ (r 16)) 8)
    have hpow : (M+1)^2 ≤ (M+1)^3 := by nlinarith
    have hM' : M+1 ≤ (M+1)^3 := by nlinarith
    omega
  · change requireStore (r 7) (r 6) c₅.store = _
    rw [hs₅, hs₄, hs₃, hs₂, hs₁]
    rfl

theorem coefficientStore_fresh (r : Fin 18 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 18) (hi : i < 6) :
    (coefficientStore r d).reg (r i) = d.reg (r i) := by
  unfold coefficientStore
  rw [requireStore_fresh _ _ _ _ (hr.ne (by omega)) (hr.ne (by omega)),
    xorStore_fresh _ _ _ _ _ (hr.ne (by omega)) (hr.ne (by omega)) (hr.ne (by omega)),
    xorStore_fresh _ _ _ _ _ (hr.ne (by omega)) (hr.ne (by omega)) (hr.ne (by omega)),
    remainderStore_fresh r hr _ i (by omega) (by omega),
    rightStore_fresh r hr _ i (by omega) (by omega), leftStore_fresh r hr _ i (by omega) (by omega)]

theorem coefficientStore_bound (r : Fin 18 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hk : d.reg (r 5)+1 ≤ M) : ∀ j, (coefficientStore r d).reg j ≤ M := by
  have h₁ := convolutionStore_bound_of (leftLayout r) (leftLayout_injective r hr) M hM d hd hk
  have h₂ := convolutionStore_bound_of (rightLayout r) (rightLayout_injective r hr) M hM _ h₁
    (by change (convolutionStore (leftLayout r) d).reg (r 5)+1 ≤ M
        rw [leftStore_fresh r hr _ 5 (by decide) (by decide)]; exact hk)
  exact requireStore_bound _ _ _ M (xorStore_bound _ _ _ _ M hM
    (xorStore_bound _ _ _ _ M hM (testBitStore_bound _ (remainderLayout_injective r hr) _ M hM h₂)))

theorem coefficientStore_tapeData (r : Fin 18 → Fin R) (d : TapeStore R B) :
    tapeData (coefficientStore r d) = tapeData d := by
  simp only [coefficientStore, requireStore_tapeData, xorStore_tapeData,
    testBitStore_tapeData, convolutionStore_tapeData]

/-- The coefficient equation checked by the finite code, for ordinary binary
indices of all five polynomial buffers. -/
def CoefficientMatches (a b rem monic quotient k : ℕ) : Prop :=
  rawConvolution a b k = bitEquiv (Nat.testBit rem k) + rawConvolution monic quotient k

instance (a b rem monic quotient k : ℕ) : Decidable (CoefficientMatches a b rem monic quotient k) :=
  inferInstanceAs (Decidable (rawConvolution a b k = bitEquiv (Nat.testBit rem k) + rawConvolution monic quotient k))

theorem xorStore_parity_cast (x unit p : Fin R) (hxu : x ≠ unit) (hxp : x ≠ p) (hup : unit ≠ p)
    (d : TapeStore R B) (hx : d.reg x ≤ 1) (hp : d.reg p ≤ 1) :
    ((xorStore x unit p d).reg p : ZMod 2) = (d.reg p : ZMod 2) + (d.reg x : ZMod 2) := by
  rw [xorStore_parity x unit p hxu hxp hup d hx hp, ZMod.natCast_mod, Nat.cast_add]

theorem coefficientStore_flag (r : Fin 18 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (hf : d.reg (r 6) ≤ 1) :
    (coefficientStore r d).reg (r 6) =
      if CoefficientMatches (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 2))
        (d.reg (r 3)) (d.reg (r 4)) (d.reg (r 5)) then d.reg (r 6) else 0 := by
  let d₁ := convolutionStore (leftLayout r) d
  let d₂ := convolutionStore (rightLayout r) d₁
  let d₃ := testBitStore (remainderLayout r) d₂
  let d₄ := xorStore (r 8) (r 16) (r 7) d₃
  let d₅ := xorStore (r 9) (r 16) (r 7) d₄
  have f₁ (i : Fin 18) (hi : i ≠ 7) (hlt : i < 10) : d₁.reg (r i) = d.reg (r i) :=
    leftStore_fresh r hr d i hi hlt
  have f₂ (i : Fin 18) (hi : i ≠ 8) (hlt : i < 10) : d₂.reg (r i) = d₁.reg (r i) :=
    rightStore_fresh r hr d₁ i hi hlt
  have f₃ (i : Fin 18) (hi : i ≠ 9) (hlt : i < 14) : d₃.reg (r i) = d₂.reg (r i) :=
    remainderStore_fresh r hr d₂ i hi hlt
  have f₄ (i : Fin 18) (hx : i ≠ 8) (hu : i ≠ 16) (hp : i ≠ 7) :
      d₄.reg (r i) = d₃.reg (r i) :=
    xorStore_fresh _ _ _ _ _ (hr.ne hx) (hr.ne hu) (hr.ne hp)
  have f₅ (i : Fin 18) (hx : i ≠ 9) (hu : i ≠ 16) (hp : i ≠ 7) :
      d₅.reg (r i) = d₄.reg (r i) :=
    xorStore_fresh _ _ _ _ _ (hr.ne hx) (hr.ne hu) (hr.ne hp)
  have hp₃ : d₃.reg (r 7) ≤ 1 := by
    rw [f₃ 7 (by decide) (by decide), f₂ 7 (by decide) (by decide)]
    exact convolutionStore_bit (leftLayout r) (leftLayout_injective r hr) d
  have hx₃ : d₃.reg (r 8) ≤ 1 := by
    rw [f₃ 8 (by decide) (by decide)]
    exact convolutionStore_bit (rightLayout r) (rightLayout_injective r hr) d₁
  have hy₃ : d₃.reg (r 9) ≤ 1 := by
    have h := testBitStore_bit (remainderLayout r) (remainderLayout_injective r hr) d₂
    change d₃.reg (r 9) = _ at h
    rw [h]
    split <;> omega
  have hp₄ : d₄.reg (r 7) ≤ 1 := by
    rw [xorStore_parity _ _ _ (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) _ hx₃ hp₃]
    omega
  have hy₄ : d₄.reg (r 9) ≤ 1 := by
    rw [f₄ 9 (by decide) (by decide) (by decide)]; exact hy₃
  have hp₅ : d₅.reg (r 7) ≤ 1 := by
    rw [xorStore_parity _ _ _ (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) _ hy₄ hp₄]
    omega
  have hflag : d₅.reg (r 6) = d.reg (r 6) := by
    rw [f₅ 6 (by decide) (by decide) (by decide), f₄ 6 (by decide) (by decide) (by decide),
      f₃ 6 (by decide) (by decide), f₂ 6 (by decide) (by decide), f₁ 6 (by decide) (by decide)]
  have hpval : (d₃.reg (r 7) : ZMod 2) = rawConvolution (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 5)) := by
    rw [f₃ 7 (by decide) (by decide), f₂ 7 (by decide) (by decide)]
    exact convolutionStore_parity (leftLayout r) (leftLayout_injective r hr) d
  have hxval : (d₃.reg (r 8) : ZMod 2) = rawConvolution (d.reg (r 3)) (d.reg (r 4)) (d.reg (r 5)) := by
    rw [f₃ 8 (by decide) (by decide)]
    have h := convolutionStore_parity (rightLayout r) (rightLayout_injective r hr) d₁
    change (d₂.reg (r 8) : ZMod 2) = rawConvolution (d₁.reg (r 3)) (d₁.reg (r 4)) (d₁.reg (r 5)) at h
    rw [h, f₁ 3 (by decide) (by decide), f₁ 4 (by decide) (by decide), f₁ 5 (by decide) (by decide)]
  have hyval : (d₃.reg (r 9) : ZMod 2) = bitEquiv (Nat.testBit (d.reg (r 2)) (d.reg (r 5))) := by
    have h := testBitStore_bit (remainderLayout r) (remainderLayout_injective r hr) d₂
    change d₃.reg (r 9) = bitValue (d₂.reg (r 2)) (d₂.reg (r 5)) at h
    rw [h, bitValue_cast, f₂ 2 (by decide) (by decide), f₁ 2 (by decide) (by decide),
      f₂ 5 (by decide) (by decide), f₁ 5 (by decide) (by decide)]
  have hv : (d₅.reg (r 7) : ZMod 2) =
      rawConvolution (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 5)) +
      rawConvolution (d.reg (r 3)) (d.reg (r 4)) (d.reg (r 5)) +
      bitEquiv (Nat.testBit (d.reg (r 2)) (d.reg (r 5))) := by
    rw [xorStore_parity_cast _ _ _ (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
      _ hy₄ hp₄, xorStore_parity_cast _ _ _ (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
      _ hx₃ hp₃, f₄ 9 (by decide) (by decide) (by decide), hpval, hxval, hyval]
  have hz : d₅.reg (r 7) = 0 ↔ CoefficientMatches (d.reg (r 0)) (d.reg (r 1))
      (d.reg (r 2)) (d.reg (r 3)) (d.reg (r 4)) (d.reg (r 5)) := by
    have hc : d₅.reg (r 7) = 0 ↔ (d₅.reg (r 7) : ZMod 2) = 0 := by
      by_cases hh : d₅.reg (r 7) = 0
      · simp [hh]
      · have h1 : d₅.reg (r 7) = 1 := by omega
        simp [h1]
    rw [hc, hv, add_assoc, add_eq_zero_iff_eq_neg, ZMod.neg_eq_self_mod_two]
    change _ = _ ↔ _ = _
    rw [add_comm (rawConvolution (d.reg (r 3)) (d.reg (r 4)) (d.reg (r 5)))]
  change (requireStore (r 7) (r 6) d₅).reg (r 6) = _
  rw [requireStore_flag _ _ (hr.ne (by decide)) _ (by rw [hflag]; exact hf), hflag]
  simp only [hz]

theorem coefficientStore_register (r : Fin 18 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₆ : j ≠ r 6) (h₇ : j ≠ r 7) (h₈ : j ≠ r 8) (h₉ : j ≠ r 9)
    (h₁₀ : j ≠ r 10) (h₁₁ : j ≠ r 11) (h₁₂ : j ≠ r 12) (h₁₃ : j ≠ r 13)
    (h₁₄ : j ≠ r 14) (h₁₅ : j ≠ r 15) (h₁₆ : j ≠ r 16) (h₁₇ : j ≠ r 17) :
    (coefficientStore r d).reg j = d.reg j := by
  unfold coefficientStore
  rw [requireStore_fresh _ _ _ _ h₇ h₆,
    xorStore_fresh _ _ _ _ _ h₉ h₁₆ h₇, xorStore_fresh _ _ _ _ _ h₈ h₁₆ h₇,
    testBitStore_fresh _ _ _ h₁₄ h₁₅ h₉ h₁₆ h₁₇,
    convolutionStore_fresh _ _ _ h₈ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆ h₁₇,
    convolutionStore_fresh _ _ _ h₇ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆ h₁₇]

theorem rawConvolution_eq_modulusConvolution (ell : ℕ) (m : Fin (2^ell))
    (s : Fin (2^(2*ell))) (k : ℕ) :
    rawConvolution (2^ell+m.val) s.val k =
      BinaryField.modulusConvolution ell m (indexEquiv (2*ell) s) k := by
  simp only [rawConvolution, BinaryField.modulusConvolution, candidateCoefficient_bit, bufferCoefficient_bit]

theorem coefficientMatches_iff (ell : ℕ) (m a b rem : Fin (2^ell))
    (s : Fin (2^(2*ell))) (k : ℕ) :
    CoefficientMatches a.val b.val rem.val (2^ell+m.val) s.val k ↔
      BinaryField.convolution (indexEquiv ell a) (indexEquiv ell b) k =
        BinaryField.bufferCoefficient (indexEquiv ell rem) k +
          BinaryField.modulusConvolution ell m (indexEquiv (2*ell) s) k := by
  simp only [CoefficientMatches, rawConvolution_eq_convolution, rawConvolution_eq_modulusConvolution,
    bufferCoefficient_bit]

/-- The nineteenth register is an outer runtime coefficient count. -/
def restrict (r : Fin 19 → Fin R) : Fin 18 → Fin R := fun i => r i.castSucc

theorem restrict_injective (r : Fin 19 → Fin R) (hr : Function.Injective r) :
    Function.Injective (restrict r) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin 19 => z.val) (hr h)

theorem reg_set19 (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i j : Fin 19) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j; simp
  · simp [TapeStore.setReg, h, hr.ne h]

/-- One actual coefficient certificate check followed by one unit position
increment. It has three hundred labels independently of the runtime bound. -/
def step (r : Fin 19 → Fin R) : TapeProgram R B 300 :=
  TapeProgram.seq (coefficient (restrict r)) (TapeMacros.increment (r 5))

def stepStore (r : Fin 19 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := coefficientStore (restrict r) d
  c.setReg (r 5) (c.reg (r 5)+1)

theorem step_stops (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) (hk : d.reg (r 5)+1 ≤ M) :
    ∃ t e, t ≤ 2200*(M+1)^3+2 ∧
      (step r).Stops inp (d.toCfg (step (B := B) r).entry) t e ∧ e.store = stepStore r d := by
  obtain ⟨t, c, ht, hc, hcs⟩ := coefficient_stops_exact (restrict r)
    (restrict_injective r hr) inp M hM d hd hk
  have hinc := TapeMacros.increment_stops (r 5) inp c.store
  have hall := hc.seq hinc
  refine ⟨_, _, by omega, hall, ?_⟩
  change c.store.setReg (r 5) _ = _
  rw [hcs]
  rfl

theorem stepStore_index (r : Fin 19 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    (stepStore r d).reg (r 5) = d.reg (r 5)+1 := by
  simp only [stepStore, TapeStore.setReg, Function.update_self]
  have h := coefficientStore_fresh (restrict r) (restrict_injective r hr) d 5 (by decide)
  change (coefficientStore (restrict r) d).reg (r 5) = d.reg (r 5) at h
  rw [h]

theorem stepStore_count (r : Fin 19 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    (stepStore r d).reg (r 18) = d.reg (r 18) := by
  unfold stepStore
  simp only [reg_set19 r hr, show (18 : Fin 19) ≠ 5 from by decide, ite_false]
  exact coefficientStore_register _ d _
    (hr.ne (show (18:Fin 19) ≠ 6 from by decide)) (hr.ne (show (18:Fin 19) ≠ 7 from by decide))
    (hr.ne (show (18:Fin 19) ≠ 8 from by decide)) (hr.ne (show (18:Fin 19) ≠ 9 from by decide))
    (hr.ne (show (18:Fin 19) ≠ 10 from by decide)) (hr.ne (show (18:Fin 19) ≠ 11 from by decide))
    (hr.ne (show (18:Fin 19) ≠ 12 from by decide)) (hr.ne (show (18:Fin 19) ≠ 13 from by decide))
    (hr.ne (show (18:Fin 19) ≠ 14 from by decide)) (hr.ne (show (18:Fin 19) ≠ 15 from by decide))
    (hr.ne (show (18:Fin 19) ≠ 16 from by decide)) (hr.ne (show (18:Fin 19) ≠ 17 from by decide))

theorem stepStore_input (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 18) (hi : i < 5) :
    (stepStore r d).reg (restrict r i) = d.reg (restrict r i) := by
  unfold stepStore
  have hne : restrict r i ≠ r 5 := hr.ne (show i.castSucc ≠ (5:Fin 19) from by
    intro h
    have he := congrArg (fun z : Fin 19 => z.val) h
    change i.val = 5 at he
    change i.val < 5 at hi
    omega)
  simp only [TapeStore.setReg, Function.update_of_ne hne]
  exact coefficientStore_fresh (restrict r) (restrict_injective r hr) d i (by omega)

theorem stepStore_flag (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (hf : d.reg (r 6) ≤ 1) :
    (stepStore r d).reg (r 6) =
      if CoefficientMatches (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 2))
        (d.reg (r 3)) (d.reg (r 4)) (d.reg (r 5)) then d.reg (r 6) else 0 := by
  unfold stepStore
  simp only [reg_set19 r hr, show (6:Fin 19) ≠ 5 from by decide, ite_false]
  exact coefficientStore_flag (restrict r) (restrict_injective r hr) d hf

theorem stepStore_bound (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hk : d.reg (r 5)+1 ≤ M) : ∀ j, (stepStore r d).reg j ≤ M := by
  apply setReg_bound _ _ _ M (coefficientStore_bound (restrict r) (restrict_injective r hr) M hM d hd hk)
  have h := coefficientStore_fresh (restrict r) (restrict_injective r hr) d 5 (by decide)
  change (coefficientStore (restrict r) d).reg (r 5) = d.reg (r 5) at h
  rw [h]; exact hk

theorem stepStore_tapeData (r : Fin 19 → Fin R) (d : TapeStore R B) :
    tapeData (stepStore r d) = tapeData d := by
  rw [stepStore, tapeData_setReg, coefficientStore_tapeData]

/-- Actual bounded coefficient certificate loop. The caller initializes
position=0, success=1, and the outer counter to its runtime bound. -/
def certificateLoop (r : Fin 19 → Fin R) : TapeProgram R B 302 :=
  TapeProgram.countedLoop (step r) (r 18)

def certificateStore (r : Fin 19 → Fin R) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d
  | n+1, d => certificateStore r n (stepStore r (d.setReg (r 18) n))

theorem certificateLoop_stops_exact (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hn : d.reg (r 18) = n) (hd : ∀ j, d.reg j ≤ M) (hk : d.reg (r 5)+n ≤ M) :
    ∃ t, t ≤ n*(2200*(M+1)^3+4)+1 ∧
      (certificateLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 300)) t
        ((certificateStore r n d).toCfg (TapeProgram.loopExit 300)) := by
  induction n generalizing d with
  | zero => exact ⟨1, by omega, TapeProgram.loop_zero (step r) (r 18) inp d hn⟩
  | succ n ih =>
    let d₁ := d.setReg (r 18) n
    have hb₁ : ∀ j, d₁.reg j ≤ M := setReg_bound d _ n M hd (by have := hd (r 18); omega)
    have hk₁ : d₁.reg (r 5)+1 ≤ M := by simp only [d₁, reg_set19 r hr]; simp; omega
    obtain ⟨s, c, hs, hc, hcs⟩ := step_stops r hr inp M hM d₁ hb₁ hk₁
    have hcn : c.reg (r 18) = n := by
      change c.store.reg (r 18) = _
      rw [hcs, stepStore_count r hr]
      simp [d₁]
    have hck : c.reg (r 5) = d.reg (r 5)+1 := by
      change c.store.reg (r 5) = _
      rw [hcs, stepStore_index r hr]
      simp [d₁, reg_set19 r hr]
    have hcb : ∀ j, c.store.reg j ≤ M := by
      rw [hcs]; exact stepStore_bound r hr M hM d₁ hb₁ hk₁
    obtain ⟨t, ht, htail⟩ := ih c.store hcn hcb (by change c.reg (r 5)+n ≤ M; omega)
    have hhead := TapeProgram.loop_positive_header (step r) (r 18) inp d (by omega)
    have hdec : TapeProgram.decStore (r 18) d = d₁ := by
      simp [TapeProgram.decStore, d₁, TapeStore.setReg, hn]
    rw [hdec] at hhead
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (step r) (r 18))
    have hreturn := TapeProgram.loop_body_return (step r) (r 18) inp c hc.halted
    have hpost : certificateStore r n c.store = certificateStore r (n+1) d := by
      rw [certificateStore, hcs]
    have hall := ((hhead.trans hrun).trans hreturn).trans htail.exec
    rw [hpost] at hall
    refine ⟨_, ?_, ⟨hall, TapeProgram.loop_code_exit (step r) (r 18)⟩⟩
    calc
      1+s+1+t ≤ 1+(2200*(M+1)^3+2)+1+(n*(2200*(M+1)^3+4)+1) := by omega
      _ = (n+1)*(2200*(M+1)^3+4)+1 := by ring

theorem certificateStore_tapeData (r : Fin 19 → Fin R) (n : ℕ) (d : TapeStore R B) :
    tapeData (certificateStore r n d) = tapeData d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [certificateStore, ih, stepStore_tapeData, tapeData_setReg]

theorem certificateStore_input (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) (i : Fin 18) (hi : i < 5) :
    (certificateStore r n d).reg (restrict r i) = d.reg (restrict r i) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [certificateStore, ih, stepStore_input r hr _ i hi]
    have hne : restrict r i ≠ r 18 := hr.ne (show i.castSucc ≠ (18:Fin 19) from by
      intro h
      have he := congrArg (fun z : Fin 19 => z.val) h
      change i.val = 18 at he
      have := i.isLt
      omega)
    simp [TapeStore.setReg, hne]

theorem certificateStore_count (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) (hn : d.reg (r 18) = n) :
    (certificateStore r n d).reg (r 18) = 0 := by
  induction n generalizing d with
  | zero => exact hn
  | succ n ih =>
    rw [certificateStore]
    apply ih
    rw [stepStore_count r hr]
    simp [TapeStore.setReg]

theorem certificateStore_index (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) :
    (certificateStore r n d).reg (r 5) = d.reg (r 5)+n := by
  induction n generalizing d with
  | zero => simp [certificateStore]
  | succ n ih =>
    rw [certificateStore, ih, stepStore_index r hr]
    simp only [reg_set19 r hr, show (5:Fin 19) ≠ 18 from by decide, ite_false]
    omega

theorem certificateStore_flag_le (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) (hf : d.reg (r 6) ≤ 1) :
    (certificateStore r n d).reg (r 6) ≤ 1 := by
  induction n generalizing d with
  | zero => exact hf
  | succ n ih =>
    rw [certificateStore]
    apply ih
    rw [stepStore_flag r hr _ (by simpa [reg_set19 r hr] using hf)]
    split <;> simp [reg_set19 r hr] <;> omega

theorem certificateStore_bound (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) (hk : d.reg (r 5)+n ≤ M) (hn : n ≤ M) :
    ∀ j, (certificateStore r n d).reg j ≤ M := by
  induction n generalizing d with
  | zero => exact hd
  | succ n ih =>
    rw [certificateStore]
    have hb := setReg_bound d (r 18) n M hd (by omega)
    apply ih _ (stepStore_bound r hr M hM _ hb (by simp [reg_set19 r hr]; omega))
    · rw [stepStore_index r hr]
      simp only [reg_set19 r hr, show (5:Fin 19) ≠ 18 from by decide, ite_false]
      omega
    · omega

/-- An accumulator invariant: success exactly means all positions already
visited satisfy the coefficient equation. -/
theorem certificateStore_flag_correct (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (a b rem monic quotient N n : ℕ) (d : TapeStore R B)
    (ha : d.reg (r 0) = a) (hb : d.reg (r 1) = b) (hrm : d.reg (r 2) = rem)
    (hm : d.reg (r 3) = monic) (hs : d.reg (r 4) = quotient)
    (hf : d.reg (r 6) ≤ 1) (hk : d.reg (r 5)+n = N)
    (hInv : d.reg (r 6) = 1 ↔ ∀ j < d.reg (r 5), CoefficientMatches a b rem monic quotient j) :
    (certificateStore r n d).reg (r 6) = 1 ↔
      ∀ j < N, CoefficientMatches a b rem monic quotient j := by
  induction n generalizing d with
  | zero => simpa only [certificateStore, show d.reg (r 5) = N by omega] using hInv
  | succ n ih =>
    let d₁ := d.setReg (r 18) n
    let d₂ := stepStore r d₁
    have hinput (i : Fin 18) (hi : i < 5) : d₂.reg (restrict r i) = d.reg (restrict r i) := by
      rw [stepStore_input r hr _ i hi]
      have hne : restrict r i ≠ r 18 := hr.ne (show i.castSucc ≠ (18:Fin 19) from by
        intro h
        have he := congrArg (fun z : Fin 19 => z.val) h
        change i.val = 18 at he
        have := i.isLt
        omega)
      simp [d₁, TapeStore.setReg, hne]
    have hf₁ : d₁.reg (r 6) = d.reg (r 6) := by simp [d₁, reg_set19 r hr]
    have hk₁ : d₁.reg (r 5) = d.reg (r 5) := by simp [d₁, reg_set19 r hr]
    have hk₂ : d₂.reg (r 5) = d.reg (r 5)+1 := by rw [stepStore_index r hr, hk₁]
    have hflag : d₂.reg (r 6) =
        if CoefficientMatches a b rem monic quotient (d.reg (r 5)) then d.reg (r 6) else 0 := by
      rw [stepStore_flag r hr d₁ (by rw [hf₁]; exact hf)]
      simp only [d₁, reg_set19 r hr]
      simp [ha, hb, hrm, hm, hs]
    have hflag_le : d₂.reg (r 6) ≤ 1 := by rw [hflag]; split <;> omega
    have hnext : d₂.reg (r 6) = 1 ↔
        d.reg (r 6) = 1 ∧ CoefficientMatches a b rem monic quotient (d.reg (r 5)) := by
      rw [hflag]
      by_cases h : CoefficientMatches a b rem monic quotient (d.reg (r 5)) <;> simp [h]
    have hnextInv : d₂.reg (r 6) = 1 ↔
        ∀ j < d₂.reg (r 5), CoefficientMatches a b rem monic quotient j := by
      rw [hnext, hInv, hk₂]
      constructor
      · rintro ⟨hbefore, hcurrent⟩ j hj
        by_cases hj' : j < d.reg (r 5)
        · exact hbefore j hj'
        · have he : j = d.reg (r 5) := by omega
          simpa [he] using hcurrent
      · intro h
        exact ⟨fun j hj => h j (by omega), h (d.reg (r 5)) (by omega)⟩
    rw [certificateStore]
    apply ih d₂ ((hinput 0 (by decide)).trans ha) ((hinput 1 (by decide)).trans hb)
      ((hinput 2 (by decide)).trans hrm) ((hinput 3 (by decide)).trans hm)
      ((hinput 4 (by decide)).trans hs) hflag_le (by omega) hnextInv

theorem coefficientMatches_all_iff (ell : ℕ) (m a b rem : Fin (2^ell))
    (s : Fin (2^(2*ell))) :
    (∀ j < 3*ell+1, CoefficientMatches a.val b.val rem.val (2^ell+m.val) s.val j) ↔
      BinaryField.DivMatches ell m (indexEquiv ell a) (indexEquiv ell b)
        (indexEquiv ell rem) (indexEquiv (2*ell) s) := by
  constructor
  · intro h j
    exact (coefficientMatches_iff ell m a b rem s j.val).mp (h j.val j.isLt)
  · intro h j hj
    exact (coefficientMatches_iff ell m a b rem s j).mpr (h ⟨j,hj⟩)

/-- A complete uniform source loop contract. The runtime bound, success bit
and coefficient position are ordinary unary registers, initialized by its caller. -/
theorem certificateLoop_stops (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M N : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) (hn : d.reg (r 18) = N)
    (hk : d.reg (r 5) = 0) (hf : d.reg (r 6) = 1) :
    ∃ t e, t ≤ 2210*(M+1)^4 ∧
      (certificateLoop r).Stops inp (d.toCfg (certificateLoop (B := B) r).entry) t e ∧
      e.reg (r 6) ≤ 1 ∧
      (e.reg (r 6) = 1 ↔ ∀ j < N,
        CoefficientMatches (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 2))
          (d.reg (r 3)) (d.reg (r 4)) j) ∧
      (∀ i : Fin 18, i < 5 → e.reg (restrict r i) = d.reg (restrict r i)) ∧
      e.reg (r 5) = N ∧ e.reg (r 18) = 0 ∧
      (∀ j, e.reg j ≤ M) ∧ tapeData e.store = tapeData d := by
  have hN : N ≤ M := by rw [← hn]; exact hd (r 18)
  obtain ⟨t, ht, he⟩ := certificateLoop_stops_exact r hr inp M hM N d hn hd (by omega)
  refine ⟨t, (certificateStore r N d).toCfg (TapeProgram.loopExit 300), ?_, he,
    certificateStore_flag_le r hr N d (by omega), ?_, ?_, ?_, certificateStore_count r hr N d hn,
    certificateStore_bound r hr M hM N d hd (by omega) hN, certificateStore_tapeData r N d⟩
  · have hm := Nat.mul_le_mul_right (2200*(M+1)^3+4) hN
    have hb : M*(2200*(M+1)^3+4)+1 ≤ 2210*(M+1)^4 := by
      have hpow := Nat.le_self_pow (by decide : (4:ℕ) ≠ 0) (M+1)
      have hM4 : M ≤ (M+1)^4 := (by omega : M ≤ M+1).trans hpow
      have h14 : 1 ≤ (M+1)^4 := by omega
      have hmul : 2200*M*(M+1)^3 ≤ 2200*(M+1)^4 := by
        calc
          2200*M*(M+1)^3 ≤ 2200*(M+1)*(M+1)^3 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2200 (by omega : M ≤ M+1))
          _ = 2200*(M+1)^4 := by ring
      have heq : M*(2200*(M+1)^3+4)+1 = 2200*M*(M+1)^3+4*M+1 := by ring
      rw [heq]
      omega
    exact (ht.trans (Nat.add_le_add_right hm 1)).trans hb
  · apply certificateStore_flag_correct r hr _ _ _ _ _ N N d rfl rfl rfl rfl rfl (by omega) (by omega)
    simp [hk, hf]
  · exact certificateStore_input r hr N d
  · simpa [hk] using certificateStore_index r hr N d

theorem certificateStore_outside (r : Fin 19 → Fin R) (n : ℕ) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 19, j ≠ r i) :
    (certificateStore r n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [certificateStore, ih]
    unfold stepStore
    simp only [TapeStore.setReg, Function.update_of_ne (hne 5)]
    rw [coefficientStore_register _ _ _ (hne 6) (hne 7) (hne 8) (hne 9) (hne 10) (hne 11)
      (hne 12) (hne 13) (hne 14) (hne 15) (hne 16) (hne 17)]
    simp [TapeStore.setReg, hne 18]

/-- Add one preserved runtime bound register to the coefficient loop. -/
def restrict19 (r : Fin 20 → Fin R) : Fin 19 → Fin R := fun i => r i.castSucc

theorem restrict19_injective (r : Fin 20 → Fin R) (hr : Function.Injective r) :
    Function.Injective (restrict19 r) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin 20 => z.val) (hr h)

theorem reg_set20 (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i j : Fin 20) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j; simp
  · simp [TapeStore.setReg, h, hr.ne h]

/-- Clear the coefficient position, initialize success to one and copy the
preserved runtime bound into the actual loop counter. -/
def prepare (r : Fin 20 → Fin R) : TapeProgram R B 17 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeMacros.clear (r 5))
    (TapeMacros.clear (r 6))) (TapeMacros.increment (r 6)))
      (TapeMacros.copy (r 19) (r 18) (r 17))

def prepareStore (r : Fin 20 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let d₁ := (d.setReg (r 5) 0).setReg (r 6) 1
  (d₁.setReg (r 18) (d₁.reg (r 19))).setReg (r 17) 0

theorem prepare_stops (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (prepare r).Stops inp (d.toCfg (prepare (B := B) r).entry)
      (d.reg (r 5)+d.reg (r 6)+d.reg (r 18)+d.reg (r 17)+5*d.reg (r 19)+13) e ∧
      e.store = prepareStore r d := by
  have h₁ := TapeMacros.clear_stops (r 5) inp (d.reg (r 5)) d rfl
  have h₂ := TapeMacros.clear_stops (r 6) inp (d.reg (r 6)) (d.setReg (r 5) 0)
    (by simp [reg_set20 r hr])
  have h₃ := TapeMacros.increment_stops (r 6) inp ((d.setReg (r 5) 0).setReg (r 6) 0)
  have hz : ((d.setReg (r 5) 0).setReg (r 6) 0).reg (r 6) = 0 := by simp [TapeStore.setReg]
  rw [hz, zero_add] at h₃
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops (r 19) (r 18) (r 17)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp
    (((d.setReg (r 5) 0).setReg (r 6) 0).setReg (r 6) 1)
  have hall := ((h₁.seq h₂).seq h₃).seq hc
  refine ⟨c.mapPC (TapeProgram.rightLabel 6), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | (simp [reg_set20 r hr]; omega)
  · change c.store = _
    rw [hcs, TapeStore.setReg_same]
    rfl

theorem prepareStore_reg (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 20) :
    (prepareStore r d).reg (r i) =
      if i = 5 then 0 else if i = 6 then 1 else if i = 18 then d.reg (r 19)
      else if i = 17 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [prepareStore, reg_set20 r hr]

theorem prepareStore_bound (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (prepareStore r d).reg j ≤ M := by
  unfold prepareStore
  apply setReg_bound _ _ 0 M _ (by omega)
  apply setReg_bound _ _ _ M
  · exact setReg_bound _ _ 1 M (setReg_bound d _ 0 M hd (by omega)) hM
  · simp only [reg_set20 r hr]
    simpa using hd (r 19)

/-- Fully initialized 319-label source certificate. Five runtime input words
are preserved; register 19 contains a preserved runtime coefficient bound. -/
def certificate (r : Fin 20 → Fin R) : TapeProgram R B 319 :=
  TapeProgram.seq (prepare r) (certificateLoop (restrict19 r))

def certificateResult (r : Fin 20 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  certificateStore (restrict19 r) (d.reg (r 19)) (prepareStore r d)

theorem certificate_stops_exact (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 2300*(M+1)^4 ∧
      (certificate r).Stops inp (d.toCfg (certificate (B := B) r).entry) t e ∧
      e.store = certificateResult r d := by
  obtain ⟨c, hc, hcs⟩ := prepare_stops r hr inp d
  have hcb : ∀ j, c.store.reg j ≤ M := by rw [hcs]; exact prepareStore_bound r hr M hM d hd
  have hcn : c.reg (r 18) = d.reg (r 19) := by
    change c.store.reg (r 18) = _
    rw [hcs, prepareStore_reg r hr]; simp
  have hck : c.reg (r 5) = 0 := by
    change c.store.reg (r 5) = _
    rw [hcs, prepareStore_reg r hr]; simp
  obtain ⟨t, ht, he⟩ := certificateLoop_stops_exact (restrict19 r) (restrict19_injective r hr)
    inp M hM (d.reg (r 19)) c.store hcn hcb (by change c.reg (r 5)+d.reg (r 19) ≤ M; rw [hck]; simpa using hd (r 19))
  have hall := hc.seq he
  refine ⟨_, _, ?_, hall, ?_⟩
  · have hp : d.reg (r 5)+d.reg (r 6)+d.reg (r 18)+d.reg (r 17)+5*d.reg (r 19)+13 ≤ 9*M+13 := by
      have := hd (r 5); have := hd (r 6); have := hd (r 18)
      have := hd (r 17); have := hd (r 19); omega
    have hpow := Nat.le_self_pow (by decide : (4:ℕ) ≠ 0) (M+1)
    have hM4 : M ≤ (M+1)^4 := (by omega : M ≤ M+1).trans hpow
    have h14 : 1 ≤ (M+1)^4 := by omega
    have hmul : 2200*M*(M+1)^3 ≤ 2200*(M+1)^4 := by
      calc
        2200*M*(M+1)^3 ≤ 2200*(M+1)*(M+1)^3 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2200 (by omega : M ≤ M+1))
        _ = 2200*(M+1)^4 := by ring
    have hmul' := Nat.mul_le_mul_right (2200*(M+1)^3+4) (hd (r 19))
    have heq : M*(2200*(M+1)^3+4) = 2200*M*(M+1)^3+4*M := by ring
    rw [heq] at hmul'
    change d.reg (r 5)+d.reg (r 6)+d.reg (r 18)+d.reg (r 17)+5*d.reg (r 19)+13+1+t ≤ _
    omega
  · change certificateStore (restrict19 r) (d.reg (r 19)) c.store = _
    rw [hcs]
    rfl

theorem certificateResult_flag_le (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (certificateResult r d).reg (r 6) ≤ 1 := by
  apply certificateStore_flag_le (restrict19 r) (restrict19_injective r hr)
  change (prepareStore r d).reg (r 6) ≤ 1
  simp [prepareStore_reg r hr]

theorem certificateResult_correct (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) :
    (certificateResult r d).reg (r 6) = 1 ↔ ∀ j < d.reg (r 19),
      CoefficientMatches (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 2))
        (d.reg (r 3)) (d.reg (r 4)) j := by
  apply certificateStore_flag_correct (restrict19 r) (restrict19_injective r hr)
    (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 2)) (d.reg (r 3)) (d.reg (r 4))
    (d.reg (r 19)) (d.reg (r 19)) (prepareStore r d)
  all_goals simp [restrict19, Fin.castSucc, prepareStore, reg_set20 r hr]

theorem certificateResult_tapeData (r : Fin 20 → Fin R) (d : TapeStore R B) :
    tapeData (certificateResult r d) = tapeData d := by
  rw [certificateResult, certificateStore_tapeData]
  rfl

theorem certificateResult_bound (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (certificateResult r d).reg j ≤ M := by
  apply certificateStore_bound (restrict19 r) (restrict19_injective r hr) M hM _ _
    (prepareStore_bound r hr M hM d hd)
  · change (prepareStore r d).reg (r 5)+d.reg (r 19) ≤ M
    simpa [prepareStore_reg r hr] using hd (r 19)
  · exact hd (r 19)

theorem certificateResult_input (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 18) (hi : i < 5) :
    (certificateResult r d).reg (r i.castSucc.castSucc) = d.reg (r i.castSucc.castSucc) := by
  change (certificateStore (restrict19 r) (d.reg (r 19)) (prepareStore r d)).reg
    (restrict (restrict19 r) i) = _
  rw [certificateStore_input (restrict19 r) (restrict19_injective r hr) _ _ i hi]
  fin_cases i <;> simp_all [restrict, restrict19, Fin.castSucc, prepareStore, reg_set20 r hr]

theorem certificateResult_runtimeBound (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (certificateResult r d).reg (r 19) = d.reg (r 19) := by
  rw [certificateResult, certificateStore_outside]
  · simp [prepareStore_reg r hr]
  · intro i
    apply hr.ne
    intro h
    have hv := congrArg (fun z : Fin 20 => z.val) h
    change 19 = i.val at hv
    have := i.isLt
    omega

/-- Source implementation of the exact existing BinaryField quotient/remainder
certificate. The modulus is supplied as its ordinary monic word `2^ell+m`;
its runtime bound is `3ell+1`. -/
theorem certificate_divMatches_stops (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (m a b rem : Fin (2^ell)) (s : Fin (2^(2*ell)))
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (ha : d.reg (r 0) = a.val) (hb : d.reg (r 1) = b.val) (hrm : d.reg (r 2) = rem.val)
    (hm : d.reg (r 3) = 2^ell+m.val) (hs : d.reg (r 4) = s.val)
    (hN : d.reg (r 19) = 3*ell+1) :
    ∃ t e, t ≤ 2300*(M+1)^4 ∧
      (certificate r).Stops inp (d.toCfg (certificate (B := B) r).entry) t e ∧
      e.store = certificateResult r d ∧ e.reg (r 6) ≤ 1 ∧
      (e.reg (r 6) = 1 ↔ BinaryField.DivMatches ell m (indexEquiv ell a) (indexEquiv ell b)
        (indexEquiv ell rem) (indexEquiv (2*ell) s)) := by
  obtain ⟨t, e, ht, he, hstore⟩ := certificate_stops_exact r hr inp M hM d hd
  refine ⟨t, e, ht, he, hstore, ?_, ?_⟩
  · change e.store.reg (r 6) ≤ 1
    rw [hstore]; exact certificateResult_flag_le r hr d
  · change e.store.reg (r 6) = 1 ↔ _
    rw [hstore]
    have h := certificateResult_correct r hr d
    rw [ha, hb, hrm, hm, hs, hN] at h
    exact h.trans (coefficientMatches_all_iff ell m a b rem s)

#print axioms certificate_divMatches_stops
#print axioms certificate_stops_exact
#print axioms certificateResult_correct
#print axioms certificateLoop_stops
#print axioms coefficient_stops_exact
#print axioms coefficientStore_flag
end ExpandingCodes.Computation.FieldCertificates
