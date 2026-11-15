import ExpandingCodes.Computation.ParameterPrograms

set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

/-- The finite control remembers the remainder modulo the fixed positive k.
No instruction divides a runtime integer. Each consumed source unit executes
one decrement; each group of k units executes one quotient increment. -/
def divideLoop (src quotient : Fin R) (k : ℕ) : TapeProgram R B (k+2) where
  entry := ⟨0,by omega⟩
  code j := if hj : j.val<k then .dec src ⟨k+1,by omega⟩
    (if hnext : j.val+1<k then ⟨j.val+1,by omega⟩ else ⟨k,by omega⟩)
    else if j.val=k then .inc quotient ⟨0,by omega⟩ else .halt

def divideLoopStore (src quotient : Fin R) (k j n : ℕ) (d : TapeStore R B) : TapeStore R B :=
  (d.setReg src 0).setReg quotient (d.reg quotient+(n+j)/k)

theorem divideLoop_stops (src quotient : Fin R) (hsq : src≠quotient)
    (k : ℕ) (hk : 0<k) (inp : Inputs) (n j : ℕ) (hj : j<k)
    (d : TapeStore R B) (hn : d.reg src=n) :
    (divideLoop src quotient k).Stops inp (d.toCfg ⟨j,by omega⟩)
      (n+(n+j)/k+1) ((divideLoopStore src quotient k j n d).toCfg ⟨k+1,by omega⟩) := by
  induction n generalizing j d with
  | zero =>
    have hdiv : (0+j)/k=0 := by simpa using Nat.div_eq_of_lt hj
    have he : divideLoopStore src quotient k j 0 d=d := by
      have hs : d.setReg src 0=d := by simp [TapeStore.setReg,← hn]
      simp [divideLoopStore,Nat.div_eq_of_lt hj,hs]
    rw [hdiv]
    constructor
    · apply TapeProgram.Exec.one
      · simp [TapeProgram.halted,divideLoop,hj]
      · simp [TapeProgram.step,divideLoop,hj,TapeStore.toCfg,hn,he]
    · simp [TapeProgram.halted,divideLoop]
  | succ n ih =>
    let d₁ := d.setReg src n
    by_cases hnext : j+1<k
    · have h₁ : (divideLoop src quotient k).step inp (d.toCfg ⟨j,by omega⟩)=
          d₁.toCfg ⟨j+1,by omega⟩ := by
        simp [TapeProgram.step,divideLoop,hj,hnext,TapeStore.toCfg,hn,d₁,TapeStore.setReg]
      have htail := ih (j+1) hnext d₁ (by simp [d₁])
      have hpost : divideLoopStore src quotient k (j+1) n d₁=
          divideLoopStore src quotient k j (n+1) d := by
        simp [divideLoopStore,d₁,TapeStore.setReg,Ne.symm hsq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      constructor
      · have hall := TapeProgram.Exec.step (by simp [TapeProgram.halted,divideLoop,hj]) h₁ htail.exec
        rw [hpost] at hall
        have hdivsum : (n+1+j)/k=(n+(j+1))/k := congrArg (· / k) (by omega)
        convert hall using 1 <;> first | rfl | omega
      · simp [TapeProgram.halted,divideLoop]
    · have hjk : j+1=k := by omega
      let d₂ := d₁.setReg quotient (d.reg quotient+1)
      have h₁ : (divideLoop src quotient k).step inp (d.toCfg ⟨j,by omega⟩)=
          d₁.toCfg ⟨k,by omega⟩ := by
        simp [TapeProgram.step,divideLoop,hj,hnext,TapeStore.toCfg,hn,d₁,TapeStore.setReg]
      have h₂ : (divideLoop src quotient k).step inp (d₁.toCfg ⟨k,by omega⟩)=
          d₂.toCfg ⟨0,by omega⟩ := by
        simp [TapeProgram.step,divideLoop,TapeStore.toCfg,d₂,d₁,TapeStore.setReg,Ne.symm hsq]
      have htail := ih 0 hk d₂ (by simp [d₂,d₁,TapeStore.setReg,hsq])
      have hdiv : (n+1+j)/k=n/k+1 := by
        have he : n+1+j=n+k := by omega
        rw [he,Nat.add_div_right n hk]
      have hdiv' : (n+(j+1))/k=n/k+1 :=
        (congrArg (· / k) (show n+(j+1)=n+1+j by omega)).trans hdiv
      have hpost : divideLoopStore src quotient k 0 n d₂=
          divideLoopStore src quotient k j (n+1) d := by
        simp only [divideLoopStore,d₂,d₁,TapeStore.setReg]
        congr 1
        funext l
        by_cases hq : l=quotient
        · subst l; simp [Function.update,hdiv,hdiv',hsq,Ne.symm hsq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        · by_cases hs : l=src
          · subst l; simp [Function.update,hsq,hq]
          · simp [Function.update,hq,hs]
      constructor
      · have hall := TapeProgram.Exec.step (by simp [TapeProgram.halted,divideLoop,hj]) h₁
          (TapeProgram.Exec.step (by simp [TapeProgram.halted,divideLoop]) h₂ htail.exec)
        rw [hpost] at hall
        convert hall using 1 <;> first | rfl | simp [hdiv]; omega
      · simp [TapeProgram.halted,divideLoop]

/-- Preserve the dividend in register 0, place its quotient by fixed k in 1,
and use two ordinary unary scratch registers 2,3. -/
def divideConstant (r : Fin 4 → Fin R) (k : ℕ) : TapeProgram R B (13+(k+2)) :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.copy (r 0) (r 2) (r 3))
    (TapeMacros.clear (r 1))) (divideLoop (r 2) (r 1) k)

def dividePrepare (r : Fin 4 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  ((d.setReg (r 2) (d.reg (r 0))).setReg (r 3) 0).setReg (r 1) 0

def divideConstantStore (r : Fin 4 → Fin R) (k : ℕ) (d : TapeStore R B) : TapeStore R B :=
  divideLoopStore (r 2) (r 1) k 0 (d.reg (r 0)) (dividePrepare r d)

theorem divideConstantStore_value (r : Fin 4 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (d : TapeStore R B) :
    (divideConstantStore r k d).reg (r 1)=d.reg (r 0)/k := by
  simp [divideConstantStore,divideLoopStore,dividePrepare,reg_layout r hr]

theorem divideConstantStore_input (r : Fin 4 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (d : TapeStore R B) :
    (divideConstantStore r k d).reg (r 0)=d.reg (r 0) := by
  simp [divideConstantStore,divideLoopStore,dividePrepare,reg_layout r hr]

theorem divideConstant_stops (r : Fin 4 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (hk : 0<k) (inp : Inputs) (M : ℕ) (d : TapeStore R B)
    (hd : ∀ j, d.reg j≤M) :
    ∃ t z, t≤16*(M+1) ∧
      (divideConstant r k).Stops inp (d.toCfg (divideConstant (B := B) r k).entry) t z ∧
      z.store=divideConstantStore r k d ∧ ∀ j, z.reg j≤M := by
  obtain ⟨c,hc,hcs⟩ := TapeMacros.copy_stops (r 0) (r 2) (r 3)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d
  have hf := TapeMacros.clear_stops (r 1) inp (c.reg (r 1)) c.store rfl
  have hpre : c.store.setReg (r 1) 0=dividePrepare r d := by rw [hcs]; rfl
  have hloop := divideLoop_stops (r 2) (r 1) (hr.ne (by decide)) k hk inp
    (d.reg (r 0)) 0 hk (dividePrepare r d) (by simp [dividePrepare,reg_layout r hr])
  have hpost : divideLoopStore (r 2) (r 1) k 0 (d.reg (r 0)) (dividePrepare r d)=
      divideConstantStore r k d := rfl
  rw [← hpre] at hloop
  have hall := (hc.seq hf).seq hloop
  refine ⟨_,_,?_,hall,?_,?_⟩
  · have hct : c.reg (r 1)=d.reg (r 1) := by
      change c.store.reg (r 1)=_; rw [hcs]; simp [reg_layout r hr]
    have h₀ := hd (r 0); have h₁ := hd (r 1); have h₂ := hd (r 2); have h₃ := hd (r 3)
    have hdiv := Nat.div_le_self (d.reg (r 0)) k
    simp only [TapeCfg.store,hct,Nat.add_zero]
    omega
  · change divideLoopStore (r 2) (r 1) k 0 (d.reg (r 0)) (c.store.setReg (r 1) 0)=_
    rw [hpre]
    rfl
  · change ∀ j, (divideLoopStore (r 2) (r 1) k 0 (d.reg (r 0))
        (c.store.setReg (r 1) 0)).reg j≤M
    rw [hpre]
    unfold divideLoopStore dividePrepare
    apply setReg_bound
    · apply setReg_bound _ _ 0 M
      · exact setReg_bound _ _ 0 M
          (setReg_bound _ _ 0 M (setReg_bound d _ _ M hd (hd (r 0))) (by omega)) (by omega)
      · omega
    · simp [reg_layout r hr]
      exact (Nat.div_le_self _ _).trans (hd (r 0))

#print axioms divideLoop_stops
#print axioms divideConstant_stops
end ParameterPrograms
end ExpandingCodes.Computation
