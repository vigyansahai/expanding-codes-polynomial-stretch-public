import ExpandingCodes.Computation.ParameterPower
import ExpandingCodes.Computation.ParameterRounding
import ExpandingCodes.Computation.ParameterDivision
import ExpandingCodes.Computation.ParameterFloor

set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

/-- Exact physical frame needed when appending setup to an input parser or
following it with random-table fills. In particular random-tape heads are fixed. -/
def SamePayload (d e : TapeStore R B) : Prop :=
  e.roHead=d.roHead ∧ e.output=d.output ∧ e.bufferTape=d.bufferTape ∧ e.bufferHead=d.bufferHead

theorem SamePayload.refl (d : TapeStore R B) : SamePayload d d := ⟨rfl,rfl,rfl,rfl⟩
theorem SamePayload.trans {d e f : TapeStore R B} (h : SamePayload d e) (k : SamePayload e f) :
    SamePayload d f := ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,k.2.2.2.trans h.2.2.2⟩
theorem SamePayload.setReg (d : TapeStore R B) (r : Fin R) (n : ℕ) :
    SamePayload d (d.setReg r n) := ⟨rfl,rfl,rfl,rfl⟩

theorem powerStepStore_fresh (r : Fin 6 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₁ : j≠r 1) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4) :
    (powerStepStore r d).reg j=d.reg j := by
  simp [powerStepStore,multiplyStore,TapeStore.setReg,h₁,h₂,h₃,h₄]

theorem powerLoopStore_fresh (r : Fin 6 → Fin R) (t : ℕ) (d : TapeStore R B) (j : Fin R)
    (h₁ : j≠r 1) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4) (h₅ : j≠r 5) :
    (powerLoopStore r t d).reg j=d.reg j := by
  induction t generalizing d with
  | zero => simp [powerLoopStore,TapeStore.setReg,h₅]
  | succ t ih =>
    rw [powerLoopStore,ih,powerStepStore_fresh r _ j h₁ h₂ h₃ h₄]
    simp [TapeStore.setReg,h₅]

theorem fixedPowerStore_fresh (r : Fin 6 → Fin R) (t : ℕ) (d : TapeStore R B) (j : Fin R)
    (h₁ : j≠r 1) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4) (h₅ : j≠r 5) :
    (fixedPowerStore r t d).reg j=d.reg j := by
  rw [fixedPowerStore,powerLoopStore_fresh r t _ j h₁ h₂ h₃ h₄ h₅]
  simp [powerPrepare,TapeStore.setReg,h₁,h₅]

theorem powerStepStore_payload (r : Fin 6 → Fin R) (d : TapeStore R B) :
    SamePayload d (powerStepStore r d) := ⟨rfl,rfl,rfl,rfl⟩

theorem powerLoopStore_payload (r : Fin 6 → Fin R) (t : ℕ) (d : TapeStore R B) :
    SamePayload d (powerLoopStore r t d) := by
  induction t generalizing d with
  | zero => exact SamePayload.setReg d _ 0
  | succ t ih => exact ((SamePayload.setReg d _ t).trans (powerStepStore_payload r _)).trans (ih _)

theorem fixedPowerStore_payload (r : Fin 6 → Fin R) (t : ℕ) (d : TapeStore R B) :
    SamePayload d (fixedPowerStore r t d) := by
  exact ((SamePayload.setReg d _ 1).trans (SamePayload.setReg _ _ t)).trans (powerLoopStore_payload r t _)

theorem ceilingStepStore_fresh (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (j : Fin R)
    (h₀ : j≠r 0) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4)
    (h₅ : j≠r 5) (h₆ : j≠r 6) : (ceilingStepStore r d).reg j=d.reg j := by
  rw [ceilingStepStore_flat r hr]
  unfold ceilingStepFlatStore
  split <;> simp [TapeStore.setReg,h₀,h₂,h₃,h₄,h₅,h₆]

theorem ceilingLoopStore_fresh (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (t : ℕ) (d : TapeStore R B) (j : Fin R)
    (h₀ : j≠r 0) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4)
    (h₅ : j≠r 5) (h₆ : j≠r 6) (h₇ : j≠r 7) :
    (ceilingLoopStore r t d).reg j=d.reg j := by
  induction t generalizing d with
  | zero => simp [ceilingLoopStore,TapeStore.setReg,h₇]
  | succ t ih =>
    rw [ceilingLoopStore,ih,ceilingStepStore_fresh r hr _ j h₀ h₂ h₃ h₄ h₅ h₆]
    simp [TapeStore.setReg,h₇]

theorem ceilingPowerStore_fresh (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (j : Fin R)
    (h₀ : j≠r 0) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4)
    (h₅ : j≠r 5) (h₆ : j≠r 6) (h₇ : j≠r 7) :
    (ceilingPowerStore r d).reg j=d.reg j := by
  rw [ceilingPowerStore,ceilingLoopStore_fresh r hr _ _ j h₀ h₂ h₃ h₄ h₅ h₆ h₇]
  simp [ceilingPrepare,TapeStore.setReg,h₀,h₅,h₆,h₇]

theorem ceilingStepStore_payload (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : SamePayload d (ceilingStepStore r d) := by
  rw [ceilingStepStore_flat r hr]
  unfold ceilingStepFlatStore
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem ceilingLoopStore_payload (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (t : ℕ) (d : TapeStore R B) : SamePayload d (ceilingLoopStore r t d) := by
  induction t generalizing d with
  | zero => exact SamePayload.setReg d _ 0
  | succ t ih => exact ((SamePayload.setReg d _ t).trans (ceilingStepStore_payload r hr _)).trans (ih _)

theorem ceilingPowerStore_payload (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : SamePayload d (ceilingPowerStore r d) := by
  have hp : SamePayload d (ceilingPrepare r d) := ⟨rfl,rfl,rfl,rfl⟩
  exact hp.trans (ceilingLoopStore_payload r hr _ _)

theorem divideConstantStore_fresh (r : Fin 4 → Fin R) (k : ℕ)
    (d : TapeStore R B) (j : Fin R) (h₁ : j≠r 1) (h₂ : j≠r 2) (h₃ : j≠r 3) :
    (divideConstantStore r k d).reg j=d.reg j := by
  simp [divideConstantStore,divideLoopStore,dividePrepare,TapeStore.setReg,h₁,h₂,h₃]

theorem divideConstantStore_payload (r : Fin 4 → Fin R) (k : ℕ)
    (d : TapeStore R B) : SamePayload d (divideConstantStore r k d) := ⟨rfl,rfl,rfl,rfl⟩

theorem floorPowerStore_fresh (r : Fin 9 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (j : Fin R)
    (h₀ : j≠r 0) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4)
    (h₅ : j≠r 5) (h₆ : j≠r 6) (h₇ : j≠r 7) (h₈ : j≠r 8) :
    (floorPowerStore r d).reg j=d.reg j := by
  have hcfresh := ceilingPowerStore_fresh (floorCeilLayout r) (floorCeilLayout_injective r hr)
    (floorPrepare r d) j
    (by simpa [floorCeilLayout,floorCeilIndex] using h₀)
    (by simpa [floorCeilLayout,floorCeilIndex] using h₂)
    (by simpa [floorCeilLayout,floorCeilIndex] using h₃)
    (by simpa [floorCeilLayout,floorCeilIndex] using h₄)
    (by simpa [floorCeilLayout,floorCeilIndex] using h₅)
    (by simpa [floorCeilLayout,floorCeilIndex] using h₆)
    (by simpa [floorCeilLayout,floorCeilIndex] using h₇)
  simp only [floorPowerStore,halfStepStore,TapeStore.setReg,
    Function.update_of_ne h₀,Function.update_of_ne h₃,Function.update_of_ne h₄,Function.update_of_ne h₆]
  rw [hcfresh]
  simp [floorPrepare,TapeStore.setReg,h₅,h₈]

theorem floorPowerStore_payload (r : Fin 9 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : SamePayload d (floorPowerStore r d) := by
  have hp : SamePayload d (floorPrepare r d) := ⟨rfl,rfl,rfl,rfl⟩
  have hc := ceilingPowerStore_payload (floorCeilLayout r) (floorCeilLayout_injective r hr)
    (floorPrepare r d)
  have hh : SamePayload (ceilingPowerStore (floorCeilLayout r) (floorPrepare r d))
      (halfStepStore (ceilingPowerStore (floorCeilLayout r) (floorPrepare r d)) (r 0) (r 3) (r 4)) :=
    ⟨rfl,rfl,rfl,rfl⟩
  exact ((hp.trans hc).trans hh).trans (SamePayload.setReg _ _ _)

#print axioms fixedPowerStore_fresh
#print axioms fixedPowerStore_payload
#print axioms ceilingPowerStore_fresh
#print axioms ceilingPowerStore_payload
#print axioms floorPowerStore_fresh
#print axioms floorPowerStore_payload
end ParameterPrograms
end ExpandingCodes.Computation
