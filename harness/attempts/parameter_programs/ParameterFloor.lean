import ExpandingCodes.Computation.ParameterRounding

set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

/-- A single actual decrement/test, joining both branches at halt. -/
def decrement (r : Fin R) : TapeProgram R B 2 where
  entry := 0
  code j := if j=0 then .dec r 1 1 else .halt

theorem decrement_stops (r : Fin R) (inp : Inputs) (d : TapeStore R B) :
    (decrement r).Stops inp (d.toCfg 0) 1 ((d.setReg r (d.reg r-1)).toCfg 1) := by
  constructor
  · apply TapeProgram.Exec.one
    · simp [TapeProgram.halted,decrement]
    · by_cases h : d.reg r=0
      · have he : d.setReg r (d.reg r-1)=d := by simpa [h] using setReg_self d r
        rw [he]
        simp [TapeProgram.step,decrement,TapeStore.toCfg,h]
      · simp [TapeProgram.step,decrement,TapeStore.toCfg,h,TapeStore.setReg]
  · simp [TapeProgram.halted,decrement]

def floorCeilIndex : Fin 8 → Fin 9 := ![0,8,2,3,4,5,6,7]

theorem floorCeilIndex_injective : Function.Injective floorCeilIndex := by decide

def floorCeilLayout (r : Fin 9 → Fin R) : Fin 8 → Fin R := r ∘ floorCeilIndex

theorem floorCeilLayout_injective (r : Fin 9 → Fin R) (hr : Function.Injective r) :
    Function.Injective (floorCeilLayout r) := hr.comp floorCeilIndex_injective

/-- Reuse ceiling(u+1), halve its power, and decrement its exponent. All three
operations are actual unary source routines. Registers 0,6 are outputs b,beta;
1 is the preserved positive input u; 8 holds a unary copy u+1. -/
def floorPowerTwo (r : Fin 9 → Fin R) : TapeProgram R B 104 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeMacros.copy (r 1) (r 8) (r 5)) (TapeMacros.increment (r 8)))
    (ceilingPowerTwo (floorCeilLayout r))) (halfStep (r 0) (r 3) (r 4)))
    (decrement (r 6))

def floorPrepare (r : Fin 9 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  ((d.setReg (r 8) (d.reg (r 1))).setReg (r 5) 0).setReg (r 8) (d.reg (r 1)+1)

def floorPowerStore (r : Fin 9 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let dc := ceilingPowerStore (floorCeilLayout r) (floorPrepare r d)
  let dh := halfStepStore dc (r 0) (r 3) (r 4)
  dh.setReg (r 6) (dh.reg (r 6)-1)

theorem clog_succ_eq_log_succ (u : ℕ) (hu : 1≤u) :
    Nat.clog 2 (u+1)=Nat.log 2 u+1 := by
  have hlo : 2^Nat.log 2 u<u+1 := by
    have h := Nat.pow_log_le_self 2 (by omega : u≠0)
    omega
  have hup : u+1≤2^(Nat.log 2 u+1) := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1<2) u
    omega
  have hclo := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mpr hlo
  have hcup := (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr hup
  omega

theorem floorPowerStore_exact (r : Fin 9 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (hu : 1≤d.reg (r 1)) :
    ((floorPowerStore r d).reg (r 0),(floorPowerStore r d).reg (r 6)) =
      (2^Nat.log 2 (d.reg (r 1)),Nat.log 2 (d.reg (r 1))) := by
  have hce := ceilingPowerStore_exact (floorCeilLayout r) (floorCeilLayout_injective r hr)
    (floorPrepare r d) (by simp [floorPrepare,floorCeilLayout,floorCeilIndex,reg_layout r hr])
  have hcq : (ceilingPowerStore (floorCeilLayout r) (floorPrepare r d)).reg (r 0)=
      2^(Nat.log 2 (d.reg (r 1))+1) := by
    have h := congrArg Prod.fst hce
    simpa [floorPrepare,floorCeilLayout,floorCeilIndex,reg_layout r hr,
      clog_succ_eq_log_succ _ hu] using h
  have hcb : (ceilingPowerStore (floorCeilLayout r) (floorPrepare r d)).reg (r 6)=
      Nat.log 2 (d.reg (r 1))+1 := by
    have h := congrArg Prod.snd hce
    simpa [floorPrepare,floorCeilLayout,floorCeilIndex,reg_layout r hr,
      clog_succ_eq_log_succ _ hu] using h
  apply Prod.ext
  · simp [floorPowerStore,halfStepStore,reg_layout r hr,hcq,pow_succ]
  · simp [floorPowerStore,halfStepStore,reg_layout r hr,hcb]

theorem floorPowerTwo_stops (r : Fin 9 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1≤M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j≤M) (hu : 1≤d.reg (r 1)) :
    ∃ t z, t≤4096*(M+1)^2 ∧
      (floorPowerTwo r).Stops inp (d.toCfg (floorPowerTwo (B := B) r).entry) t z ∧
      z.store=floorPowerStore r d ∧ ∀ j, z.reg j≤2*M+4 := by
  obtain ⟨c,hc,hcs⟩ := TapeMacros.copy_stops (r 1) (r 8) (r 5)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d
  have hf := TapeMacros.increment_stops (r 8) inp c.store
  let df := c.store.setReg (r 8) (c.reg (r 8)+1)
  have hpre : df=floorPrepare r d := by
    dsimp [df]
    change c.store.setReg (r 8) (c.store.reg (r 8)+1)=_
    rw [hcs]
    simp [floorPrepare,reg_layout r hr]
  have hfb : ∀ j, df.reg j≤M+1 := by
    rw [hpre]
    unfold floorPrepare
    exact setReg_bound _ _ _ (M+1)
      (setReg_bound _ _ 0 (M+1)
        (setReg_bound d _ _ (M+1) (fun j => (hd j).trans (by omega)) ((hd (r 1)).trans (by omega)))
        (by omega)) (by have := hd (r 1); omega)
  obtain ⟨s,g,hs,hg,hgs,hgb⟩ := ceilingPowerTwo_stops (floorCeilLayout r)
    (floorCeilLayout_injective r hr) inp (M+1) (by omega) df hfb
    (by rw [hpre]; simp [floorPrepare,floorCeilLayout,floorCeilIndex,reg_layout r hr])
  obtain ⟨h,hh,hhs⟩ := halfStep_stops (r 0) (r 3) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp g.store
  have hhb : ∀ j, h.reg j≤2*M+4 := by
    change ∀ j, h.store.reg j≤2*M+4
    rw [hhs]
    exact halfStepStore_bound _ _ _ _ _ (by omega) (by intro j; have := hgb j; omega)
  have hi := decrement_stops (r 6) inp h.store
  have hall := (((hc.seq hf).seq hg).seq hh).seq hi
  refine ⟨_,_,?_,hall,?_,?_⟩
  · have hcopy : d.reg (r 8)+d.reg (r 5)+5*d.reg (r 1)+7≤7*M+7 := by
      have := hd (r 8); have := hd (r 5); have := hd (r 1); omega
    have hhalf := halfStep_time_le (g.reg (r 0)) (g.reg (r 3)) (g.reg (r 4))
    have h₀ := hgb (r 0); have h₃ := hgb (r 3); have h₄ := hgb (r 4)
    simp only [TapeCfg.store]
    nlinarith
  · change h.store.setReg (r 6) (h.store.reg (r 6)-1)=floorPowerStore r d
    rw [hhs,hgs,hpre]
    rfl
  · change ∀ j, (h.store.setReg (r 6) (h.reg (r 6)-1)).reg j≤2*M+4
    exact setReg_bound _ _ _ _ hhb ((Nat.sub_le _ _).trans (hhb (r 6)))

#print axioms floorPowerStore_exact
#print axioms floorPowerTwo_stops
end ParameterPrograms
end ExpandingCodes.Computation
