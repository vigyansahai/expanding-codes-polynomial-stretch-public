import ExpandingCodes.Computation.SourceModulus

set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.SourceFieldSetup
open NKtLB FieldPrograms FieldConvolution SourceFieldArithmetic
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B : ℕ}

/-- Runtime ell is preserved in register20, and q in register23. -/
def coefficientBound (r : Fin 32 → Fin R) : TapeProgram R B 31 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeMacros.clear (r 19))
    (TapeMacros.addPreserving (r 20) (r 19) (r 28))) (TapeMacros.addPreserving (r 20) (r 19) (r 28)))
    (TapeMacros.addPreserving (r 20) (r 19) (r 28))) (TapeMacros.increment (r 19))
def boundStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c₀ := d.setReg (r 19) 0
  let c₁ := (c₀.setReg (r 19) (c₀.reg (r 19)+c₀.reg (r 20))).setReg (r 28) 0
  let c₂ := (c₁.setReg (r 19) (c₁.reg (r 19)+c₁.reg (r 20))).setReg (r 28) 0
  let c₃ := (c₂.setReg (r 19) (c₂.reg (r 19)+c₂.reg (r 20))).setReg (r 28) 0
  c₃.setReg (r 19) (c₃.reg (r 19)+1)

theorem coefficientBound_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hN : 3*d.reg (r 20)+1 ≤ M) :
    ∃ t e,t ≤ 100*M+100 ∧ (coefficientBound r).Stops inp (d.toCfg (coefficientBound (B:=B) r).entry) t e ∧
      e.store = boundStore r d ∧ (∀ j,e.reg j ≤ M) := by
  have h₀ := TapeMacros.clear_stops (r 19) inp (d.reg (r 19)) d rfl
  let c₀ := d.setReg (r 19) 0
  have hb₀ : ∀ j,c₀.reg j ≤ M := setReg_bound _ _ 0 M hd (by omega)
  obtain ⟨c₁,h₁,hs₁⟩ := TapeMacros.addPreserving_stops (r 20) (r 19) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₀
  have hb₁ : ∀ j,c₁.store.reg j ≤ M := by
    rw [hs₁]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M hb₀
    simp [c₀,SourceModulus.reg_set r hr]
    omega
  obtain ⟨c₂,h₂,hs₂⟩ := TapeMacros.addPreserving_stops (r 20) (r 19) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₁.store
  have hb₂ : ∀ j,c₂.store.reg j ≤ M := by
    rw [hs₂]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M hb₁
    rw [hs₁]
    simp [c₀,SourceModulus.reg_set r hr]
    omega
  obtain ⟨c₃,h₃,hs₃⟩ := TapeMacros.addPreserving_stops (r 20) (r 19) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₂.store
  have hb₃ : ∀ j,c₃.store.reg j ≤ M := by
    rw [hs₃]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M hb₂
    rw [hs₂,hs₁]
    simp [c₀,SourceModulus.reg_set r hr]
    omega
  have hi := TapeMacros.increment_stops (r 19) inp c₃.store
  have hsum : c₃.store.reg (r 19)+1 ≤ M := by
    rw [hs₃,hs₂,hs₁]
    simp [c₀,SourceModulus.reg_set r hr]
    omega
  have hall := (((h₀.seq h₁).seq h₂).seq h₃).seq hi
  refine ⟨_,_,?_,hall,?_,setReg_bound _ _ _ M hb₃ hsum⟩
  · have := hd (r 19);have := hb₀ (r 28);have := hb₀ (r 20)
    have := hb₁ (r 28);have := hb₁ (r 20);have := hb₂ (r 28);have := hb₂ (r 20);omega
  · change c₃.store.setReg (r 19) _ = _
    rw [hs₃,hs₂,hs₁]
    rfl

theorem boundStore_reg (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i : Fin 32) :
    (boundStore r d).reg (r i) = if i = 19 then 3*d.reg (r 20)+1 else if i = 28 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [boundStore,SourceModulus.reg_set r hr] <;> omega

/-- Convert the selected index into the actual ordinary monic bit-word q+p. -/
def monicWord (r : Fin 32 → Fin R) : TapeProgram R B 20 :=
  TapeProgram.seq (TapeMacros.copy (r 23) (r 3) (r 28)) (TapeMacros.addPreserving (r 27) (r 3) (r 28))
def monicStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := (d.setReg (r 3) (d.reg (r 23))).setReg (r 28) 0
  (c.setReg (r 3) (c.reg (r 3)+c.reg (r 27))).setReg (r 28) 0

theorem monicWord_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hsum : d.reg (r 23)+d.reg (r 27) ≤ M) :
    ∃ t e,t ≤ 20*M+20 ∧ (monicWord r).Stops inp (d.toCfg (monicWord (B:=B) r).entry) t e ∧
      e.store = monicStore r d ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨c₁,h₁,hs₁⟩ := TapeMacros.copy_stops (r 23) (r 3) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d
  have hb₁ : ∀ j,c₁.store.reg j ≤ M := by
    rw [hs₁];exact setReg_bound _ _ 0 M (setReg_bound d _ _ M hd (hd (r 23))) (by omega)
  obtain ⟨c₂,h₂,hs₂⟩ := TapeMacros.addPreserving_stops (r 27) (r 3) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₁.store
  have hb₂ : ∀ j,c₂.store.reg j ≤ M := by
    rw [hs₂]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M hb₁
    rw [hs₁]
    simpa [SourceModulus.reg_set r hr] using hsum
  have hall := h₁.seq h₂
  refine ⟨_,_,?_,hall,?_,hb₂⟩
  · have := hd (r 3);have := hd (r 28);have := hd (r 23);have := hb₁ (r 28);have := hb₁ (r 27);omega
  · change c₂.store = _
    rw [hs₂,hs₁];rfl

theorem monicStore_reg (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i : Fin 32) :
    (monicStore r d).reg (r i) = if i = 3 then d.reg (r 23)+d.reg (r 27) else if i = 28 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [monicStore,SourceModulus.reg_set r hr]

/-- Fully actual uniform setup for the shared source arithmetic environment. -/
def setup (r : Fin 32 → Fin R) : TapeProgram R B 516 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (coefficientBound r) (SourceModulus.construct r))
    (monicWord r)) (UnaryArithmetic.multiply (r 23) (r 23) (r 24) (r 28) (r 30))
def setupStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  UnaryArithmetic.multiplyStore (monicStore r (SourceModulus.constructResult r (boundStore r d)))
    (r 23) (r 23) (r 24) (r 28) (r 30)

theorem squareStore_reg (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i : Fin 32) :
    (UnaryArithmetic.multiplyStore d (r 23) (r 23) (r 24) (r 28) (r 30)).reg (r i) =
      if i = 30 ∨ i = 28 then 0 else if i = 24 then d.reg (r 23)*d.reg (r 23) else d.reg (r i) := by
  fin_cases i <;> simp [UnaryArithmetic.multiplyStore,SourceModulus.reg_set r hr]

def Environment (r : Fin 32 → Fin R) (ell : ℕ) (h : 0 < ell) (d : TapeStore R B) : Prop :=
  d.reg (r 20) = ell ∧ d.reg (r 23) = 2^ell ∧ d.reg (r 19) = 3*ell+1 ∧
    d.reg (r 3) = 2^ell+(selectedIndex ell h).val ∧ d.reg (r 24) = 2^(2*ell) ∧ d.reg (r 27) = (selectedIndex ell h).val

theorem setupStore_environment (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (d : TapeStore R B) (hell : d.reg (r 20) = ell) (hq : d.reg (r 23) = 2^ell) :
    Environment r ell h (setupStore r d) := by
  let c₁ := boundStore r d
  let c₂ := SourceModulus.constructResult r c₁
  let c₃ := monicStore r c₂
  have hq₁ : c₁.reg (r 23) = 2^ell := by simp [c₁,boundStore_reg r hr,hq]
  have hN₁ : c₁.reg (r 19) = 3*ell+1 := by simp [c₁,boundStore_reg r hr,hell]
  have hell₁ : c₁.reg (r 20) = ell := by simp [c₁,boundStore_reg r hr,hell]
  have hp₂ : c₂.reg (r 27) = (selectedIndex ell h).val := SourceModulus.constructResult_index r hr ell h c₁ hq₁ hN₁
  have hq₂ : c₂.reg (r 23) = 2^ell :=
    (SourceModulus.constructResult_input r hr c₁ 23 (by decide)).trans hq₁
  have hN₂ : c₂.reg (r 19) = 3*ell+1 :=
    (SourceModulus.constructResult_input r hr c₁ 19 (by decide)).trans hN₁
  have hell₂ : c₂.reg (r 20) = ell :=
    (SourceModulus.constructResult_input r hr c₁ 20 (by decide)).trans hell₁
  have hfinal (i : Fin 32) : (setupStore r d).reg (r i) =
      if i = 30 ∨ i = 28 then 0 else if i = 24 then c₃.reg (r 23)*c₃.reg (r 23) else c₃.reg (r i) :=
    squareStore_reg r hr c₃ i
  have hp : (2^ell)*(2^ell) = 2^(2*ell) := by rw [← pow_add];congr 1;omega
  simp [Environment,hfinal,c₃,monicStore_reg r hr,hq₂,hN₂,hell₂,hp₂,hp]

theorem setup_stops_exact (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (ell : ℕ) (h : 0 < ell) (M : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M)
    (hell : d.reg (r 20) = ell) (hq : d.reg (r 23) = 2^ell)
    (hN : 3*ell+1 ≤ M) (h2q : 2*(2^ell) ≤ M) (hQ : 2^(2*ell) ≤ M) :
    ∃ t e,t ≤ 40000*(M+1)^7 ∧ (setup r).Stops inp (d.toCfg (setup (B:=B) r).entry) t e ∧
      e.store = setupStore r d ∧ (∀ j,e.reg j ≤ M) := by
  have hM : 1 ≤ M := by have : 0 < 2^ell := Nat.two_pow_pos ell;omega
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := coefficientBound_stops r hr inp M d hd (by simpa only [hell] using hN)
  have hq₁ : c₁.reg (r 23) = 2^ell := by change c₁.store.reg (r 23) = _;rw [hs₁,boundStore_reg r hr];simp [hq]
  have hN₁ : c₁.reg (r 19) = 3*ell+1 := by change c₁.store.reg (r 19) = _;rw [hs₁,boundStore_reg r hr];simp [hell]
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂,hp₂,hpres₂,_,hb₂,_⟩ := SourceModulus.construct_stops r hr inp ell h M c₁.store hb₁ hq₁ hN₁ h2q
  have hq₂ : c₂.reg (r 23) = 2^ell := (hpres₂ 23 (by decide)).trans hq₁
  have hsum : c₂.reg (r 23)+c₂.reg (r 27) ≤ M := by
    rw [hq₂,hp₂]
    have := (selectedIndex ell h).isLt
    omega
  obtain ⟨t₃,c₃,ht₃,h₃,hs₃,hb₃⟩ := monicWord_stops r hr inp M c₂.store hb₂ hsum
  have hq₃ : c₃.reg (r 23) = 2^ell := by
    change c₃.store.reg (r 23) = _
    rw [hs₃,monicStore_reg r hr];simpa using hq₂
  obtain ⟨t₄,c₄,ht₄,h₄,hs₄⟩ := UnaryArithmetic.multiply_stops_polynomial
    (r 23) (r 23) (r 24) (r 28) (r 30)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₃.store M
    (hb₃ (r 23)) (hb₃ (r 23)) (hb₃ (r 24)) (hb₃ (r 28)) (hb₃ (r 30))
  have hb₄ : ∀ j,c₄.store.reg j ≤ M := by
    rw [hs₄]
    unfold UnaryArithmetic.multiplyStore
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M hb₃
    change c₃.reg (r 23)*c₃.reg (r 23) ≤ M
    rw [hq₃,← pow_add]
    have he : ell+ell = 2*ell := by omega
    simpa only [he] using hQ
  have hall := ((h₁.seq h₂).seq h₃).seq h₄
  refine ⟨_,_,?_,hall,?_,hb₄⟩
  · have hp7 := Nat.le_self_pow (by decide : (7:ℕ) ≠ 0) (M+1)
    have hM7 : M ≤ (M+1)^7 := (by omega : M ≤ M+1).trans hp7
    have h17 : 1 ≤ (M+1)^7 := by omega
    have h27 : (M+1)^2 ≤ (M+1)^7 := Nat.pow_le_pow_right (by omega) (by decide)
    omega
  · change c₄.store = _
    rw [hs₄,hs₃,hs₂,hs₁]
    rfl

theorem setupStore_tapeData (r : Fin 32 → Fin R) (d : TapeStore R B) : tapeData (setupStore r d) = tapeData d := by
  simp only [setupStore,UnaryArithmetic.multiplyStore,tapeData_setReg]
  unfold monicStore
  simp only [tapeData_setReg]
  rw [SourceModulus.constructResult_tapeData]
  rfl

theorem setupStore_outside (r : Fin 32 → Fin R) (d : TapeStore R B) (j : Fin R) (hne : ∀ i : Fin 32,j ≠ r i) :
    (setupStore r d).reg j = d.reg j := by
  simp only [setupStore,UnaryArithmetic.multiplyStore,TapeStore.setReg,
    Function.update_of_ne (hne 24),Function.update_of_ne (hne 28),Function.update_of_ne (hne 30)]
  unfold monicStore
  simp only [TapeStore.setReg,Function.update_of_ne (hne 3),Function.update_of_ne (hne 28)]
  rw [SourceModulus.constructResult_outside r _ j hne]
  simp [boundStore,TapeStore.setReg,hne 19,hne 28]

/-- Complete source setup from preserved runtime ell/q, with the exact
canonical field environment needed by all arithmetic routines. -/
theorem setup_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (ell : ℕ) (h : 0 < ell) (M : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M)
    (hell : d.reg (r 20) = ell) (hq : d.reg (r 23) = 2^ell)
    (hN : 3*ell+1 ≤ M) (h2q : 2*(2^ell) ≤ M) (hQ : 2^(2*ell) ≤ M) :
    ∃ t e,t ≤ 40000*(M+1)^7 ∧ (setup r).Stops inp (d.toCfg (setup (B:=B) r).entry) t e ∧
      e.store = setupStore r d ∧ Environment r ell h e.store ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ tapeData e.store = tapeData d := by
  obtain ⟨t,e,ht,he,hes,hbound⟩ := setup_stops_exact r hr inp ell h M d hd hell hq hN h2q hQ
  refine ⟨t,e,ht,he,hes,?_,?_,hbound,?_⟩
  · rw [hes];exact setupStore_environment r hr ell h d hell hq
  · intro j hj
    change e.store.reg j = _
    rw [hes];exact setupStore_outside r d j hj
  · rw [hes];exact setupStore_tapeData r d

#print axioms setup_stops
#print axioms setupStore_environment
#print axioms coefficientBound_stops
#print axioms monicWord_stops
end ExpandingCodes.Computation.SourceFieldSetup
