import ExpandingCodes.Computation.ParameterPrograms

set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

/-- One actual multiplication and copy. Registers: base 0, accumulator 1,
product 2, unary arithmetic scratch 3 and 4, outer loop count 5. -/
def powerStep (r : Fin 6 → Fin R) : TapeProgram R B 35 :=
  TapeProgram.seq (multiply (r 0) (r 1) (r 2) (r 3) (r 4))
    (TapeMacros.copy (r 2) (r 1) (r 3))

def powerStepStore (r : Fin 6 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let dm := multiplyStore d (r 0) (r 1) (r 2) (r 3) (r 4)
  (dm.setReg (r 1) (dm.reg (r 2))).setReg (r 3) 0

theorem powerStepStore_value (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) :
    (powerStepStore r d).reg (r 1) = d.reg (r 0)*d.reg (r 1) := by
  simp [powerStepStore, multiplyStore, reg_layout r hr]

theorem powerStepStore_base (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (powerStepStore r d).reg (r 0) = d.reg (r 0) := by
  simp [powerStepStore, multiplyStore, reg_layout r hr]

theorem powerStepStore_count (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (powerStepStore r d).reg (r 5) = d.reg (r 5) := by
  simp [powerStepStore, multiplyStore, reg_layout r hr]

theorem powerStepStore_bound (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (M : ℕ) (hd : ∀ j, d.reg j ≤ M)
    (hp : d.reg (r 0)*d.reg (r 1) ≤ M) :
    ∀ j, (powerStepStore r d).reg j ≤ M := by
  dsimp [powerStepStore, multiplyStore]
  apply setReg_bound _ _ 0 M
  · apply setReg_bound
    · apply setReg_bound _ _ 0 M
      · apply setReg_bound _ _ 0 M
        · exact setReg_bound d _ _ M hd hp
        · omega
      · omega
    · simpa [multiplyStore, reg_layout r hr] using hp
  · omega

theorem powerStep_stops (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hp : d.reg (r 0)*d.reg (r 1) ≤ M) :
    ∃ t e, t ≤ 64*(M+1)^2 ∧
      (powerStep r).Stops inp (d.toCfg (powerStep (B := B) r).entry) t e ∧
      e.store = powerStepStore r d := by
  obtain ⟨t, c, ht, hc, hcs⟩ := multiply_stops_polynomial (r 0) (r 1) (r 2) (r 3) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    inp d M (hd _) (hd _) (hd _) (hd _) (hd _)
  have hcb : ∀ j, c.reg j ≤ M := by
    change ∀ j, c.store.reg j ≤ M
    rw [hcs]
    exact setReg_bound _ _ 0 M
      (setReg_bound _ _ 0 M (setReg_bound d _ _ M hd hp) (by omega)) (by omega)
  obtain ⟨e, he, hes⟩ := TapeMacros.copy_stops (r 2) (r 1) (r 3)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c.store
  have hall := hc.seq he
  refine ⟨_, _, ?_, hall, ?_⟩
  · have hcopy : c.reg (r 1)+c.reg (r 3)+5*c.reg (r 2)+7 ≤ 7*M+7 := by
      have := hcb (r 1); have := hcb (r 3); have := hcb (r 2); omega
    simp only [TapeCfg.store]
    nlinarith
  · change e.store = _
    rw [hes, hcs]
    rfl

/-- The exponent is a unary runtime counter loaded from a fixed program
constant. This loop has 37 labels regardless of input size or exponent value. -/
def powerLoop (r : Fin 6 → Fin R) : TapeProgram R B 37 :=
  TapeProgram.countedLoop (powerStep r) (r 5)

def powerLoopStore (r : Fin 6 → Fin R) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d.setReg (r 5) 0
  | n+1, d => powerLoopStore r n (powerStepStore r (d.setReg (r 5) n))

theorem powerLoopStore_base (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) :
    (powerLoopStore r n d).reg (r 0) = d.reg (r 0) := by
  induction n generalizing d with
  | zero => simp [powerLoopStore, reg_layout r hr]
  | succ n ih =>
    rw [powerLoopStore, ih, powerStepStore_base r hr]
    simp [reg_layout r hr]

theorem powerLoopStore_value (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) :
    (powerLoopStore r n d).reg (r 1) = d.reg (r 0)^n*d.reg (r 1) := by
  induction n generalizing d with
  | zero => simp [powerLoopStore, reg_layout r hr]
  | succ n ih =>
    rw [powerLoopStore, ih, powerStepStore_base r hr, powerStepStore_value r hr]
    simp [reg_layout r hr, pow_succ]
    ring

theorem powerLoopStore_count (r : Fin 6 → Fin R) (n : ℕ) (d : TapeStore R B) :
    (powerLoopStore r n d).reg (r 5) = 0 := by
  induction n generalizing d with
  | zero => simp [powerLoopStore]
  | succ n ih => exact ih _

/-- Bound each intermediate unary multiplication result by its eventual power.
The base positivity assumption is satisfied by both mission bases n and q. -/
theorem powerLoop_stops (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M n : ℕ) (d : TapeStore R B)
    (hn : d.reg (r 5) = n) (ha : 1 ≤ d.reg (r 0))
    (hd : ∀ j, d.reg j ≤ M) (hp : d.reg (r 0)^n*d.reg (r 1) ≤ M) :
    ∃ t, t ≤ n*(64*(M+1)^2+2)+1 ∧
      (powerLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 35)) t
        ((powerLoopStore r n d).toCfg (TapeProgram.loopExit 35)) ∧
      ∀ j, (powerLoopStore r n d).reg j ≤ M := by
  induction n generalizing d with
  | zero =>
    have he : d.setReg (r 5) 0 = d := by simp [TapeStore.setReg, ← hn]
    exact ⟨1, by omega, by simpa [powerLoop, powerLoopStore, he] using
      TapeProgram.loop_zero (powerStep r) (r 5) inp d hn,
      by simpa [powerLoopStore, he] using hd⟩
  | succ n ih =>
    let d₁ := d.setReg (r 5) n
    have hd₁ : ∀ j, d₁.reg j ≤ M := setReg_bound d _ n M hd (by have := hd (r 5); omega)
    have hprod : d₁.reg (r 0)*d₁.reg (r 1) ≤ M := by
      have hpw : 1 ≤ d.reg (r 0)^n := Nat.one_le_pow n _ ha
      have hle : d.reg (r 0)*d.reg (r 1) ≤ d.reg (r 0)^(n+1)*d.reg (r 1) := by
        rw [pow_succ]
        simpa using Nat.mul_le_mul_right (d.reg (r 1))
          (Nat.mul_le_mul_right (d.reg (r 0)) hpw)
      simpa [d₁, reg_layout r hr] using hle.trans hp
    obtain ⟨s, c, hs, hc, hcs⟩ := powerStep_stops r hr inp M d₁ hd₁ hprod
    have hcb : ∀ j, c.reg j ≤ M := by
      change ∀ j, c.store.reg j ≤ M
      rw [hcs]
      exact powerStepStore_bound r hr d₁ M hd₁ hprod
    have hcn : c.reg (r 5) = n := by
      change c.store.reg (r 5) = n
      rw [hcs, powerStepStore_count r hr]
      simp [d₁]
    have hca : 1 ≤ c.reg (r 0) := by
      change 1 ≤ c.store.reg (r 0)
      rw [hcs, powerStepStore_base r hr]
      simpa [d₁, reg_layout r hr] using ha
    have hcp : c.reg (r 0)^n*c.reg (r 1) ≤ M := by
      change c.store.reg (r 0)^n*c.store.reg (r 1) ≤ M
      rw [hcs, powerStepStore_base r hr, powerStepStore_value r hr]
      simpa [d₁, reg_layout r hr, pow_succ, Nat.mul_assoc] using hp
    obtain ⟨t, ht, htail, htb⟩ := ih c.store hcn hca hcb hcp
    have hhead := TapeProgram.loop_positive_header (powerStep r) (r 5) inp d (by omega)
    have hdec : TapeProgram.decStore (r 5) d = d₁ := by
      simp [TapeProgram.decStore, d₁, TapeStore.setReg, hn]
    rw [hdec] at hhead
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2) (TapeProgram.loop_code_body_active (powerStep r) (r 5))
    have hreturn := TapeProgram.loop_body_return (powerStep r) (r 5) inp c hc.halted
    have hpost : powerLoopStore r n c.store = powerLoopStore r (n+1) d := by
      rw [powerLoopStore, hcs]
    have hall := ((hhead.trans hrun).trans hreturn).trans htail.exec
    rw [hpost] at hall
    refine ⟨_, ?_, ⟨hall, TapeProgram.loop_code_exit (powerStep r) (r 5)⟩, ?_⟩
    · nlinarith
    · rwa [hpost] at htb

/-- Load the fixed exponent into the outer loop counter before executing a
uniform multiplication loop. Only this fixed exponent affects the code size. -/
def fixedPowerLabels (e : ℕ) : ℕ := (2+raiseLabels 1)+(2+raiseLabels e)+37

def fixedPower (r : Fin 6 → Fin R) (e : ℕ) : TapeProgram R B (fixedPowerLabels e) :=
  TapeProgram.seq (TapeProgram.seq (loadConstant (r 1) 1) (loadConstant (r 5) e))
    (powerLoop r)

def powerPrepare (r : Fin 6 → Fin R) (e : ℕ) (d : TapeStore R B) : TapeStore R B :=
  (d.setReg (r 1) 1).setReg (r 5) e

def fixedPowerStore (r : Fin 6 → Fin R) (e : ℕ) (d : TapeStore R B) : TapeStore R B :=
  powerLoopStore r e (powerPrepare r e d)

theorem fixedPowerStore_value (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (e : ℕ) (d : TapeStore R B) :
    (fixedPowerStore r e d).reg (r 1) = d.reg (r 0)^e := by
  simp [fixedPowerStore, powerLoopStore_value r hr, powerPrepare, reg_layout r hr]

theorem fixedPowerStore_base (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (e : ℕ) (d : TapeStore R B) :
    (fixedPowerStore r e d).reg (r 0) = d.reg (r 0) := by
  simp [fixedPowerStore, powerLoopStore_base r hr, powerPrepare, reg_layout r hr]

theorem fixedPower_stops (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (e : ℕ) (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) (ha : 1 ≤ d.reg (r 0)) :
    ∃ t z, t ≤ 512*(e+1)^3*(M+1)^(2*(e+1)) ∧
      (fixedPower r e).Stops inp (d.toCfg (fixedPower (B := B) r e).entry) t z ∧
      z.store = fixedPowerStore r e d ∧
      ∀ j, z.reg j ≤ (e+1)*(M+1)^(e+1) := by
  let K := (e+1)*(M+1)^(e+1)
  have hpow₁ : M+1 ≤ (M+1)^(e+1) := by
    simpa using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1≤e+1 by omega)
  have hpowpos : 1 ≤ (M+1)^(e+1) := Nat.one_le_pow _ _ (by omega)
  have hKM : M ≤ K := by dsimp [K]; nlinarith
  have hKe : e ≤ K := by dsimp [K]; nlinarith
  obtain ⟨c, hc, hcs⟩ := loadConstant_stops (r 1) 1 inp d
  obtain ⟨f, hf, hfs⟩ := loadConstant_stops (r 5) e inp c.store
  have hpre : f.store = powerPrepare r e d := by rw [hfs, hcs]; rfl
  have hbd : ∀ j, f.reg j ≤ K := by
    change ∀ j, f.store.reg j ≤ K
    rw [hpre]
    exact setReg_bound _ _ e K
      (setReg_bound d _ 1 K (fun j => (hd j).trans hKM) (by omega)) hKe
  have hn : f.reg (r 5) = e := by change f.store.reg (r 5) = _; rw [hpre]; simp [powerPrepare]
  have hbase : f.reg (r 0) = d.reg (r 0) := by
    change f.store.reg (r 0) = _; rw [hpre]; simp [powerPrepare, reg_layout r hr]
  have hp : f.reg (r 0)^e*f.reg (r 1) ≤ K := by
    have hpw : d.reg (r 0)^e ≤ (M+1)^(e+1) :=
      (Nat.pow_le_pow_left (by have := hd (r 0); omega) e).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
    change f.store.reg (r 0)^e*f.store.reg (r 1) ≤ K
    rw [hpre]
    simp only [powerPrepare, reg_layout r hr]
    simp only [show (0 : Fin 6) ≠ 5 from by decide, show (0 : Fin 6) ≠ 1 from by decide,
      show (1 : Fin 6) ≠ 5 from by decide, ite_false, ite_true, Nat.mul_one]
    dsimp [K]
    nlinarith
  obtain ⟨t, ht, hloop, hzb⟩ := powerLoop_stops r hr inp K e f.store hn
    (by simpa [TapeCfg.store, hbase] using ha) hbd hp
  have hall := (hc.seq hf).seq hloop
  refine ⟨_, _, ?_, hall, ?_, ?_⟩
  · have hct : c.reg (r 5) = d.reg (r 5) := by
      change c.store.reg (r 5) = _; rw [hcs]; simp [reg_layout r hr]
    have h₁ := hd (r 1)
    have h₅ := hd (r 5)
    have hKpos : 1 ≤ K := by omega
    have hKP : K^2 = (e+1)^2*(M+1)^(2*(e+1)) := by
      dsimp [K]
      rw [mul_pow, ← pow_mul]
      congr 2
      omega
    have hsq : (K+1)^2 ≤ 4*K^2 := by nlinarith
    have hKsq : K ≤ K^2 := by nlinarith
    have hbody : 64*(K+1)^2+2 ≤ 258*K^2 := by nlinarith
    have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left e hbody) 1)
    have hsmall : 2*M+2*e+9 ≤ 13*(e+1)*K^2 := by nlinarith
    have hgoal : 512*(e+1)^3*(M+1)^(2*(e+1)) = 512*(e+1)*K^2 := by
      rw [hKP]
      ring
    rw [hgoal]
    simp only [TapeCfg.store, hct]
    nlinarith
  · change powerLoopStore r e f.store = fixedPowerStore r e d
    rw [hpre]
    rfl
  · change ∀ j, (powerLoopStore r e f.store).reg j ≤ K
    exact hzb

#print axioms powerStep_stops
#print axioms powerLoopStore_value
#print axioms powerLoop_stops
#print axioms fixedPower_stops
end ParameterPrograms
end ExpandingCodes.Computation
