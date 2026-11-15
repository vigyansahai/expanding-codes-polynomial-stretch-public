import ExpandingCodes.Computation.ParameterPrograms
import ExpandingCodes.Computation.SizeParameters

set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

/-- Runtime q is doubled by a preserving copy and unary addition; ell receives
one actual increment. The other registers remain ordinary unary scratch. -/
def doubleBody (q ell copy tmp : Fin R) : TapeProgram R B 22 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.copy q copy tmp)
    (TapeMacros.addPreserving copy q tmp)) (TapeMacros.increment ell)

def doubleBodyStore (q ell copy tmp : Fin R) (d : TapeStore R B) : TapeStore R B :=
  let d₁ := (d.setReg copy (d.reg q)).setReg tmp 0
  let d₂ := (d₁.setReg q (d₁.reg q+d₁.reg copy)).setReg tmp 0
  d₂.setReg ell (d₂.reg ell+1)

theorem doubleBody_stops (q ell copy tmp : Fin R)
    (hqe : q≠ell) (hqc : q≠copy) (hqt : q≠tmp)
    (hec : ell≠copy) (het : ell≠tmp) (hct : copy≠tmp)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (doubleBody q ell copy tmp).Stops inp
      (d.toCfg (doubleBody (B := B) q ell copy tmp).entry)
      (d.reg copy+d.reg tmp+10*d.reg q+15) e ∧
      e.store=doubleBodyStore q ell copy tmp d := by
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops q copy tmp hqc hqt hct inp d
  obtain ⟨f, hf, hfs⟩ := TapeMacros.addPreserving_stops copy q tmp
    (Ne.symm hqc) hct hqt inp c.store
  have hg := TapeMacros.increment_stops ell inp f.store
  have hall := (hc.seq hf).seq hg
  refine ⟨((f.store.setReg ell (f.reg ell+1)).toCfg (1 : Fin 2)).mapPC (TapeProgram.rightLabel 20), ?_, ?_⟩
  · have htmp : c.reg tmp=0 := by change c.store.reg tmp=0; rw [hcs]; simp
    have hcopy : c.reg copy=d.reg q := by
      change c.store.reg copy=_; rw [hcs]; simp [TapeStore.setReg, hct]
    convert hall using 1 <;> first | rfl | simp only [TapeCfg.store, htmp, hcopy]; omega
  · change (f.store.setReg ell (f.store.reg ell+1)) = _
    rw [hfs, hcs]
    rfl

def ceilCompareLayout (r : Fin 8 → Fin R) (j : Fin 6) : Fin R :=
  r ⟨j.val, by omega⟩

theorem ceilCompareLayout_injective (r : Fin 8 → Fin R) (hr : Function.Injective r) :
    Function.Injective (ceilCompareLayout r) := by
  intro i j hij
  have hv := congrArg Fin.val (hr hij)
  exact Fin.ext hv

/-- The comparison result is either zero or one, so a counted loop gives a
real conditional instruction sequence without testing an entire unary value. -/
def ceilConditional (r : Fin 8 → Fin R) : TapeProgram R B 24 :=
  TapeProgram.countedLoop (doubleBody (r 0) (r 6) (r 3) (r 5)) (r 2)

def ceilConditionalStore (r : Fin 8 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  if d.reg (r 2)=0 then d else
    doubleBodyStore (r 0) (r 6) (r 3) (r 5) (d.setReg (r 2) 0)

theorem ceilConditional_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) (hflag : d.reg (r 2) ≤ 1) :
    ∃ t, t ≤ 12*M+18 ∧
      (ceilConditional r).Stops inp (d.toCfg (TapeProgram.loopHeader 22)) t
        ((ceilConditionalStore r d).toCfg (TapeProgram.loopExit 22)) := by
  by_cases hz : d.reg (r 2)=0
  · exact ⟨1, by omega, by simpa [ceilConditional, ceilConditionalStore, hz] using
      TapeProgram.loop_zero (doubleBody (r 0) (r 6) (r 3) (r 5)) (r 2) inp d hz⟩
  · have hone : d.reg (r 2)=1 := by omega
    let d₁ := d.setReg (r 2) 0
    obtain ⟨c, hc, hcs⟩ := doubleBody_stops (r 0) (r 6) (r 3) (r 5)
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d₁
    have hcz : c.reg (r 2)=0 := by
      change c.store.reg (r 2)=0
      rw [hcs]
      simp [doubleBodyStore, d₁, reg_layout r hr]
    have hhead := TapeProgram.loop_positive_header
      (doubleBody (r 0) (r 6) (r 3) (r 5)) (r 2) inp d hz
    have hdec : TapeProgram.decStore (r 2) d=d₁ := by
      simp [TapeProgram.decStore, d₁, TapeStore.setReg, hone]
    rw [hdec] at hhead
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (doubleBody (r 0) (r 6) (r 3) (r 5)) (r 2))
    have hreturn := TapeProgram.loop_body_return
      (doubleBody (r 0) (r 6) (r 3) (r 5)) (r 2) inp c hc.halted
    have htail := TapeProgram.loop_zero
      (doubleBody (r 0) (r 6) (r 3) (r 5)) (r 2) inp c.store hcz
    have hall := ((hhead.trans hrun).trans hreturn).trans htail.exec
    have hpost : c.store=ceilConditionalStore r d := by
      simp only [ceilConditionalStore, hz, ↓reduceIte]
      exact hcs
    rw [hpost] at hall
    refine ⟨_, ?_, ⟨hall, TapeProgram.loop_code_exit _ _⟩⟩
    have hq := hd (r 0); have hcopy := hd (r 3); have htmp := hd (r 5)
    simp [d₁, reg_layout r hr]
    omega

/-- Registers 0,1,6 hold runtime q,p,ell; 2--5 are scratch and 7 is the
fresh outer count. Neither p nor q contributes any labels to this code table. -/
def ceilingStep (r : Fin 8 → Fin R) : TapeProgram R B 57 :=
  TapeProgram.seq (lessThan (ceilCompareLayout r)) (ceilConditional r)

def ceilingStepStore (r : Fin 8 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  ceilConditionalStore r (lessThanStore (ceilCompareLayout r) d)

theorem ceilingStep_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 128*(M+1) ∧
      (ceilingStep r).Stops inp (d.toCfg (ceilingStep (B := B) r).entry) t e ∧
      e.store=ceilingStepStore r d := by
  have hr' := ceilCompareLayout_injective r hr
  obtain ⟨t, c, ht, hc, hcs⟩ := lessThan_stops (ceilCompareLayout r) hr' inp M hM d hd
  have hcb : ∀ j, c.reg j ≤ M := by
    change ∀ j, c.store.reg j ≤ M
    rw [hcs]
    exact lessThanStore_bound _ hr' d M hM hd
  have hf : c.reg (r 2) ≤ 1 := by
    change c.store.reg (ceilCompareLayout r 2) ≤ 1
    rw [hcs, lessThanStore_value _ hr']
    split <;> omega
  obtain ⟨s, hs, he⟩ := ceilConditional_stops r hr inp M c.store hcb hf
  have hall := hc.seq he
  refine ⟨_, _, ?_, hall, ?_⟩
  · omega
  · change ceilConditionalStore r c.store=ceilingStepStore r d
    rw [hcs]
    rfl

def ceilingStepFlatStore (r : Fin 8 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let z := (((d.setReg (r 2) 0).setReg (r 3) 0).setReg (r 4) 0).setReg (r 5) 0
  if d.reg (r 0)<d.reg (r 1) then
    (((z.setReg (r 0) (2*d.reg (r 0))).setReg (r 3) (d.reg (r 0))).setReg (r 6) (d.reg (r 6)+1))
  else z

theorem tapeStore_ext (d e : TapeStore R B)
    (hr : d.reg=e.reg) (hh : d.roHead=e.roHead) (ho : d.output=e.output)
    (hb : d.bufferTape=e.bufferTape) (hbh : d.bufferHead=e.bufferHead) : d=e := by
  cases d
  cases e
  cases hr
  cases hh
  cases ho
  cases hb
  cases hbh
  rfl

theorem ceilingStepStore_flat (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : ceilingStepStore r d=ceilingStepFlatStore r d := by
  have hv : (lessThanStore (ceilCompareLayout r) d).reg (r 2) =
      if d.reg (r 0)<d.reg (r 1) then 1 else 0 :=
    lessThanStore_value _ (ceilCompareLayout_injective r hr) d
  unfold ceilingStepStore ceilConditionalStore
  rw [hv]
  by_cases hlt : d.reg (r 0)<d.reg (r 1)
  all_goals
    simp only [hlt, if_true, if_false, Nat.one_ne_zero]
    apply tapeStore_ext
    · funext j
      by_cases h₀ : j=r 0
      · subst j; simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
          doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
          ceilCompareLayout, reg_layout r hr, hlt, two_mul]
      · by_cases h₂ : j=r 2
        · subst j; simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
            doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
            ceilCompareLayout, reg_layout r hr, hlt]
        · by_cases h₃ : j=r 3
          · subst j; simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
              doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
              ceilCompareLayout, reg_layout r hr, hlt]
          · by_cases h₄ : j=r 4
            · subst j; simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
                doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
                ceilCompareLayout, reg_layout r hr, hlt]
            · by_cases h₅ : j=r 5
              · subst j; simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
                  doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
                  ceilCompareLayout, reg_layout r hr, hlt]
              · by_cases h₆ : j=r 6
                · subst j; simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
                    doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
                    ceilCompareLayout, reg_layout r hr, hlt]
                · simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
                    doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
                    ceilCompareLayout, reg_layout r hr, hlt, TapeStore.setReg,
                    h₀, h₂, h₃, h₄, h₅, h₆]
  
    all_goals simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
      doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
      ceilCompareLayout, reg_layout r hr, hlt, TapeStore.setReg]

theorem ceilingStepStore_q (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (ceilingStepStore r d).reg (r 0) =
      if d.reg (r 0)<d.reg (r 1) then 2*d.reg (r 0) else d.reg (r 0) := by
  rw [ceilingStepStore_flat r hr]
  by_cases hlt : d.reg (r 0)<d.reg (r 1)
  all_goals simp [ceilingStepFlatStore, reg_layout r hr, hlt]

theorem ceilingStepStore_ell (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (ceilingStepStore r d).reg (r 6) =
      if d.reg (r 0)<d.reg (r 1) then d.reg (r 6)+1 else d.reg (r 6) := by
  rw [ceilingStepStore_flat r hr]
  by_cases hlt : d.reg (r 0)<d.reg (r 1)
  all_goals simp [ceilingStepFlatStore, reg_layout r hr, hlt]

theorem ceilingStepStore_p (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (ceilingStepStore r d).reg (r 1)=d.reg (r 1) := by
  rw [ceilingStepStore_flat r hr]
  by_cases hlt : d.reg (r 0)<d.reg (r 1)
  all_goals simp [ceilingStepFlatStore, reg_layout r hr, hlt]

theorem ceilingStepStore_count (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (ceilingStepStore r d).reg (r 7)=d.reg (r 7) := by
  rw [ceilingStepStore_flat r hr]
  by_cases hlt : d.reg (r 0)<d.reg (r 1)
  all_goals simp [ceilingStepFlatStore, reg_layout r hr, hlt]

theorem ceilingStepStore_bound (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (M : ℕ) (hd : ∀ j, d.reg j≤M)
    (hactive : d.reg (r 0)<d.reg (r 1) →
      2*d.reg (r 0)≤M ∧ d.reg (r 6)+1≤M) :
    ∀ j, (ceilingStepStore r d).reg j≤M := by
  rw [ceilingStepStore_flat r hr]
  unfold ceilingStepFlatStore
  split
  · rename_i hlt
    exact setReg_bound _ _ _ M
      (setReg_bound _ _ _ M
        (setReg_bound _ _ _ M
          (setReg_bound _ _ 0 M
            (setReg_bound _ _ 0 M
              (setReg_bound _ _ 0 M (setReg_bound d _ 0 M hd (by omega)) (by omega))
              (by omega)) (by omega)) (hactive hlt).1)
          (hd (r 0))) (hactive hlt).2
  · repeat' apply setReg_bound
    all_goals first | exact hd _ | omega

/-- The fixed p-step outer loop. Its counter is separate from all comparison
and unary arithmetic scratch, and the code has exactly 59 labels. -/
def ceilingLoop (r : Fin 8 → Fin R) : TapeProgram R B 59 :=
  TapeProgram.countedLoop (ceilingStep r) (r 7)

def ceilingLoopStore (r : Fin 8 → Fin R) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d.setReg (r 7) 0
  | t+1, d => ceilingLoopStore r t (ceilingStepStore r (d.setReg (r 7) t))

theorem ceilingLoopStore_pair (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (t : ℕ) (d : TapeStore R B) :
    ((ceilingLoopStore r t d).reg (r 0),(ceilingLoopStore r t d).reg (r 6)) =
      SizeParameters.ceilIter (d.reg (r 1)) t (d.reg (r 0),d.reg (r 6)) := by
  induction t generalizing d with
  | zero => simp [ceilingLoopStore, SizeParameters.ceilIter, reg_layout r hr]
  | succ t ih =>
    rw [ceilingLoopStore, ih, ceilingStepStore_p r hr,
      ceilingStepStore_q r hr, ceilingStepStore_ell r hr]
    by_cases hlt : d.reg (r 0)<d.reg (r 1)
    all_goals simp [SizeParameters.ceilIter, SizeParameters.ceilStep, reg_layout r hr, hlt]

theorem ceilingLoop_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M t : ℕ) (hM : 1≤M) (d : TapeStore R B)
    (ht : d.reg (r 7)=t) (hd : ∀ j, d.reg j≤M)
    (hp : 1≤d.reg (r 1)) (hpM : 2*d.reg (r 1)≤M)
    (hq : 1≤d.reg (r 0)) (hqb : d.reg (r 0)<2*d.reg (r 1))
    (hbudget : d.reg (r 1)≤d.reg (r 0)+t) (hell : d.reg (r 6)+t≤d.reg (r 1)) :
    ∃ s, s≤t*(128*(M+1)+2)+1 ∧
      (ceilingLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 57)) s
        ((ceilingLoopStore r t d).toCfg (TapeProgram.loopExit 57)) ∧
      ∀ j, (ceilingLoopStore r t d).reg j≤M := by
  induction t generalizing d with
  | zero =>
    have he : d.setReg (r 7) 0=d := by simp [TapeStore.setReg, ← ht]
    exact ⟨1, by omega, by simpa [ceilingLoop, ceilingLoopStore, he] using
      TapeProgram.loop_zero (ceilingStep r) (r 7) inp d ht,
      by simpa [ceilingLoopStore, he] using hd⟩
  | succ t ih =>
    let d₁ := d.setReg (r 7) t
    have hdb : ∀ j, d₁.reg j≤M :=
      setReg_bound d _ _ M hd (by have := hd (r 7); omega)
    obtain ⟨s, c, hs, hc, hcs⟩ := ceilingStep_stops r hr inp M hM d₁ hdb
    have hcb : ∀ j, c.reg j≤M := by
      change ∀ j, c.store.reg j≤M
      rw [hcs]
      apply ceilingStepStore_bound r hr _ M hdb
      intro hlt
      simp [d₁, reg_layout r hr] at hlt ⊢
      omega
    have hcp : c.reg (r 1)=d.reg (r 1) := by
      change c.store.reg (r 1)=_
      rw [hcs, ceilingStepStore_p r hr]
      simp [d₁, reg_layout r hr]
    have hcq : c.reg (r 0)=if d.reg (r 0)<d.reg (r 1) then
        2*d.reg (r 0) else d.reg (r 0) := by
      change c.store.reg (r 0)=_
      rw [hcs, ceilingStepStore_q r hr]
      simp [d₁, reg_layout r hr]
    have hce : c.reg (r 6)=if d.reg (r 0)<d.reg (r 1) then
        d.reg (r 6)+1 else d.reg (r 6) := by
      change c.store.reg (r 6)=_
      rw [hcs, ceilingStepStore_ell r hr]
      simp [d₁, reg_layout r hr]
    have hct : c.reg (r 7)=t := by
      change c.store.reg (r 7)=_
      rw [hcs, ceilingStepStore_count r hr]
      simp [d₁]
    have hcqpos : 1≤c.reg (r 0) := by rw [hcq]; split <;> omega
    have hcqb : c.reg (r 0)<2*c.reg (r 1) := by rw [hcq,hcp]; split <;> omega
    have hcbudget : c.reg (r 1)≤c.reg (r 0)+t := by rw [hcq,hcp]; split <;> omega
    have hcell : c.reg (r 6)+t≤c.reg (r 1) := by rw [hce,hcp]; split <;> omega
    obtain ⟨u, hu, htail, hub⟩ := ih c.store hct hcb (by simpa only [TapeCfg.store,hcp] using hp)
      (by simpa only [TapeCfg.store,hcp] using hpM) hcqpos hcqb hcbudget hcell
    have hhead := TapeProgram.loop_positive_header (ceilingStep r) (r 7) inp d (by omega)
    have hdec : TapeProgram.decStore (r 7) d=d₁ := by
      simp [TapeProgram.decStore, d₁, TapeStore.setReg, ht]
    rw [hdec] at hhead
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (ceilingStep r) (r 7))
    have hreturn := TapeProgram.loop_body_return (ceilingStep r) (r 7) inp c hc.halted
    have hpost : ceilingLoopStore r t c.store=ceilingLoopStore r (t+1) d := by
      rw [ceilingLoopStore, hcs]
    have hall := ((hhead.trans hrun).trans hreturn).trans htail.exec
    rw [hpost] at hall
    refine ⟨_, ?_, ⟨hall,TapeProgram.loop_code_exit _ _⟩, ?_⟩
    · nlinarith
    · rwa [hpost] at hub

/-- Compute the least power of two at least p. Static initialization is joined
to a p-counted runtime loop; there are 77 labels for every runtime p. -/
def ceilingPowerTwo (r : Fin 8 → Fin R) : TapeProgram R B 77 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (loadConstant (r 0) 1)
    (TapeMacros.clear (r 6))) (TapeMacros.copy (r 1) (r 7) (r 5))) (ceilingLoop r)

def ceilingPrepare (r : Fin 8 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let d₁ := (d.setReg (r 0) 1).setReg (r 6) 0
  (d₁.setReg (r 7) (d₁.reg (r 1))).setReg (r 5) 0

def ceilingPowerStore (r : Fin 8 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  ceilingLoopStore r (d.reg (r 1)) (ceilingPrepare r d)

theorem ceilingPowerStore_exact (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (hp : 1≤d.reg (r 1)) :
    ((ceilingPowerStore r d).reg (r 0),(ceilingPowerStore r d).reg (r 6)) =
      (2^Nat.clog 2 (d.reg (r 1)),Nat.clog 2 (d.reg (r 1))) := by
  unfold ceilingPowerStore
  rw [ceilingLoopStore_pair r hr]
  simpa [ceilingPrepare, reg_layout r hr] using SizeParameters.ceilIter_exact (d.reg (r 1)) hp

theorem ceilingPowerTwo_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1≤M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j≤M) (hp : 1≤d.reg (r 1)) :
    ∃ t z, t≤512*(M+1)^2 ∧
      (ceilingPowerTwo r).Stops inp (d.toCfg (ceilingPowerTwo (B := B) r).entry) t z ∧
      z.store=ceilingPowerStore r d ∧ ∀ j, z.reg j≤2*M+2 := by
  obtain ⟨c, hc, hcs⟩ := loadConstant_stops (r 0) 1 inp d
  have hce : c.reg (r 6)=d.reg (r 6) := by
    change c.store.reg (r 6)=_; rw [hcs]; simp [reg_layout r hr]
  have hf := TapeMacros.clear_stops (r 6) inp (d.reg (r 6)) c.store hce
  obtain ⟨g, hg, hgs⟩ := TapeMacros.copy_stops (r 1) (r 7) (r 5)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp (c.store.setReg (r 6) 0)
  have hpre : g.store=ceilingPrepare r d := by rw [hgs,hcs]; rfl
  have hgb : ∀ j, g.reg j≤2*M+2 := by
    change ∀ j, g.store.reg j≤2*M+2
    rw [hpre]
    dsimp [ceilingPrepare]
    apply setReg_bound _ _ 0 (2*M+2)
    · apply setReg_bound
      · exact setReg_bound _ _ 0 (2*M+2)
          (setReg_bound d _ 1 (2*M+2) (fun j => (hd j).trans (by omega)) (by omega)) (by omega)
      · simp [reg_layout r hr]
        have := hd (r 1); omega
    · omega
  have hgn : g.reg (r 7)=d.reg (r 1) := by
    change g.store.reg (r 7)=_; rw [hpre]; simp [ceilingPrepare,reg_layout r hr]
  have hgp : g.reg (r 1)=d.reg (r 1) := by
    change g.store.reg (r 1)=_; rw [hpre]; simp [ceilingPrepare,reg_layout r hr]
  have hgq : g.reg (r 0)=1 := by
    change g.store.reg (r 0)=_; rw [hpre]; simp [ceilingPrepare,reg_layout r hr]
  have hge : g.reg (r 6)=0 := by
    change g.store.reg (r 6)=_; rw [hpre]; simp [ceilingPrepare,reg_layout r hr]
  obtain ⟨t, ht, hloop, hzb⟩ := ceilingLoop_stops r hr inp (2*M+2) (d.reg (r 1)) (by omega)
    g.store hgn hgb (by simpa only [TapeCfg.store,hgp] using hp)
    (by simp only [TapeCfg.store,hgp]; have := hd (r 1); omega)
    (by simp only [TapeCfg.store,hgq]; omega)
    (by simp only [TapeCfg.store,hgq,hgp]; omega)
    (by simp only [TapeCfg.store,hgq,hgp]; omega)
    (by simp only [TapeCfg.store,hge,hgp]; omega)
  have hall := ((hc.seq hf).seq hg).seq hloop
  refine ⟨_, _, ?_, hall, ?_, hzb⟩
  · have h₀ := hd (r 0); have h₁ := hd (r 1); have h₅ := hd (r 5)
    have h₆ := hd (r 6); have h₇ := hd (r 7)
    have hcost : (c.store.setReg (r 6) 0).reg (r 7)+
        (c.store.setReg (r 6) 0).reg (r 5)+5*(c.store.setReg (r 6) 0).reg (r 1)+7 ≤ 7*M+7 := by
      rw [hcs]
      simp [reg_layout r hr]
      omega
    have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ h₁) 1)
    simp only [TapeCfg.store]
    nlinarith
  · change ceilingLoopStore r (d.reg (r 1)) g.store=ceilingPowerStore r d
    rw [hpre]
    rfl

#print axioms doubleBody_stops
#print axioms ceilConditional_stops
#print axioms ceilingStep_stops
#print axioms ceilingStepStore_flat
#print axioms ceilingLoopStore_pair
#print axioms ceilingLoop_stops
#print axioms ceilingPowerStore_exact
#print axioms ceilingPowerTwo_stops
end ParameterPrograms
end ExpandingCodes.Computation
