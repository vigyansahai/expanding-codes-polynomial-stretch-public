import ExpandingCodes.Computation.SourceFieldArithmetic
import ExpandingCodes.Computation.RawIrreducibility

set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.SourceModulus
open NKtLB FieldPrograms FieldConvolution FieldCertificates SourceFieldArithmetic
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B : ℕ}

/-- Static modulus-search layout, independent of runtime ell,q. Certificate
registers0..19; q23; q-2 in24; valid25; factorcount26; answer27;
copy scratch28; found29; inner factorcount30; descending moduluscount31. -/
def certificateLayout (r : Fin 32 → Fin R) : Fin 20 → Fin R :=
  fun i => r ⟨i.val,by have := i.isLt;omega⟩
def commitLayout (r : Fin 32 → Fin R) : Fin 5 → Fin R := fun i => r (![31,27,28,29,25] i)

theorem certificateLayout_injective (r : Fin 32 → Fin R) (hr : Function.Injective r) :
    Function.Injective (certificateLayout r) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin 32 => z.val) (hr h)

theorem commitLayout_injective (r : Fin 32 → Fin R) (hr : Function.Injective r) :
    Function.Injective (commitLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [commitLayout]

theorem reg_set (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i j : Fin 32) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j;simp
  · simp [TapeStore.setReg,h,hr.ne h]

def decrement (x : Fin R) : TapeProgram R B 2 where
  entry := 0
  code i := if i = 0 then .dec x 1 1 else .halt

theorem decrement_stops (x : Fin R) (inp : Inputs) (d : TapeStore R B) :
    (decrement x).Stops inp (d.toCfg 0) 1 ((d.setReg x (d.reg x-1)).toCfg 1) := by
  constructor
  · apply TapeProgram.Exec.one
    · simp [TapeProgram.halted,decrement]
    · by_cases hx : d.reg x = 0
      · have he : d.setReg x 0 = d := by
          unfold TapeStore.setReg
          rw [← hx]
          simp
        simp [TapeProgram.step,decrement,hx,he]
      · simp [TapeProgram.step,decrement,hx,TapeStore.setReg]
  · simp [TapeProgram.halted,decrement]

def subtractTwo (x : Fin R) : TapeProgram R B 4 := TapeProgram.seq (decrement x) (decrement x)
theorem subtractTwo_stops (x : Fin R) (inp : Inputs) (d : TapeStore R B) :
    ∃ e,(subtractTwo x).Stops inp (d.toCfg (subtractTwo (B:=B) x).entry) 3 e ∧ e.store = d.setReg x (d.reg x-2) := by
  have h₁ := decrement_stops x inp d
  have h₂ := decrement_stops x inp (d.setReg x (d.reg x-1))
  have hall := h₁.seq h₂
  refine ⟨_,hall,?_⟩
  change (d.setReg x (d.reg x-1)).setReg x _ = _
  simp [TapeStore.setReg_same,TapeStore.setReg,Nat.sub_sub]

def setTwo (x : Fin R) : TapeProgram R B 6 := TapeProgram.seq (setOne x) (TapeMacros.increment x)
theorem setTwo_stops (x : Fin R) (inp : Inputs) (d : TapeStore R B) :
    ∃ e,(setTwo x).Stops inp (d.toCfg (setTwo (B:=B) x).entry) (d.reg x+5) e ∧ e.store = d.setReg x 2 := by
  obtain ⟨c,hc,hcs⟩ := setOne_stops x inp d
  have hi := TapeMacros.increment_stops x inp c.store
  have hall := hc.seq hi
  refine ⟨((c.store.setReg x (c.store.reg x+1)).toCfg (1:Fin 2)).mapPC (TapeProgram.rightLabel 4),?_,?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change c.store.setReg x _ = _
    rw [hcs]
    simp [TapeStore.setReg_same,TapeStore.setReg]

theorem certificate_preserves (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 32) (hi : i < 5 ∨ i = 19 ∨ 20 ≤ i) :
    (certificateResult (certificateLayout r) d).reg (r i) = d.reg (r i) := by
  rcases hi with hi|rfl|hi
  · let j : Fin 18 := ⟨i.val,by change i.val < 5 at hi;omega⟩
    have h := certificateResult_input (certificateLayout r) (certificateLayout_injective r hr) d j (by change i.val < 5;exact hi)
    simpa [certificateLayout,j] using h
  · exact certificateResult_runtimeBound (certificateLayout r) (certificateLayout_injective r hr) d
  · apply certificateResult_outside
    intro j
    apply hr.ne
    intro h
    have hv := congrArg (fun z : Fin 32 => z.val) h
    change i.val = j.val at hv
    change 20 ≤ i.val at hi
    have := j.isLt;omega

/-- Check a raw factor pair and clear validity if it succeeds. -/
def factorBody (r : Fin 32 → Fin R) : TapeProgram R B 324 :=
  TapeProgram.seq (TapeProgram.seq (certificate (certificateLayout r)) (requireZero (r 6) (r 25)))
    (TapeMacros.increment (r 1))
def factorBodyStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := requireStore (r 6) (r 25) (certificateResult (certificateLayout r) d)
  c.setReg (r 1) (c.reg (r 1)+1)

theorem factorBodyStore_fresh (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 32) (hi : i < 5 ∨ i = 19 ∨ 20 ≤ i) (h1 : i ≠ 1) (h25 : i ≠ 25) :
    (factorBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold factorBodyStore
  simp only [reg_set r hr,if_neg h1]
  rw [requireStore_fresh _ _ _ _
    (hr.ne (show i ≠ (6:Fin 32) from by rcases hi with h|h|h <;> omega)) (hr.ne h25)]
  exact certificate_preserves r hr d i hi

theorem factorBodyStore_index (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    (factorBodyStore r d).reg (r 1) = d.reg (r 1)+1 := by
  unfold factorBodyStore
  simp only [TapeStore.setReg,Function.update_self]
  rw [requireStore_fresh _ _ _ _ (hr.ne (by decide)) (hr.ne (by decide)),
    certificate_preserves r hr d 1 (Or.inl (by decide))]

theorem factorBodyStore_tapeData (r : Fin 32 → Fin R) (d : TapeStore R B) :
    tapeData (factorBodyStore r d) = tapeData d := by
  rw [factorBodyStore,tapeData_setReg,requireStore_tapeData,certificateResult_tapeData]

theorem factorBodyStore_bound (r : Fin 32 → Fin R) (hr : Function.Injective r) (M : ℕ) (hM : 1 ≤ M)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 1)+1 ≤ M) :
    ∀ j,(factorBodyStore r d).reg j ≤ M := by
  apply setReg_bound _ _ _ M (requireStore_bound _ _ _ M
    (certificateResult_bound _ (certificateLayout_injective r hr) M hM d hd))
  have he := factorBodyStore_index r hr d
  have he' : (requireStore (r 6) (r 25) (certificateResult (certificateLayout r) d)).reg (r 1)+1 = d.reg (r 1)+1 := by
    simpa only [factorBodyStore,TapeStore.setReg,Function.update_self] using he
  rw [he'];exact hc

theorem factorBody_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∃ t e,t ≤ 2400*(M+1)^4 ∧ (factorBody r).Stops inp (d.toCfg (factorBody (B:=B) r).entry) t e ∧ e.store = factorBodyStore r d := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁⟩ := certificate_stops_exact (certificateLayout r) (certificateLayout_injective r hr) inp M hM d hd
  obtain ⟨t₂,ht₂,h₂⟩ := requireZero_stops (r 6) (r 25) (hr.ne (by decide)) inp c₁.store
  have h₃ := TapeMacros.increment_stops (r 1) inp (requireStore (r 6) (r 25) c₁.store)
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_,_,?_,hall,?_⟩
  · have hp := Nat.le_self_pow (by decide : (4:ℕ) ≠ 0) (M+1)
    omega
  · change (requireStore (r 6) (r 25) c₁.store).setReg (r 1) _ = _
    rw [hs₁];rfl

def innerLoop (r : Fin 32 → Fin R) : TapeProgram R B 326 := TapeProgram.countedLoop (factorBody r) (r 30)
def innerResult (r : Fin 32 → Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B := loopResult (r 30) (factorBodyStore r) n d

theorem innerLoop_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B) (hn : d.reg (r 30) = n)
    (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 1)+n ≤ M) :
    ∃ t,t ≤ n*(2400*(M+1)^4+2)+1 ∧ (innerLoop r).Stops inp
      (d.toCfg (TapeProgram.loopHeader 324)) t ((innerResult r n d).toCfg (TapeProgram.loopExit 324)) ∧
      (∀ j,(innerResult r n d).reg j ≤ M) :=
  singleLoop_stops (factorBody r) (r 30) (r 1) (hr.ne (by decide)) (factorBodyStore r) inp M _
    (fun c => factorBodyStore_fresh r hr c 30 (Or.inr (Or.inr (by decide))) (by decide) (by decide))
    (factorBodyStore_index r hr) (factorBodyStore_bound r hr M hM) (factorBody_stops r hr inp M hM) n d hn hd hc

theorem innerResult_frame (r : Fin 32 → Fin R) (hr : Function.Injective r) (n : ℕ) (d : TapeStore R B)
    (i : Fin 32) (hi : i < 5 ∨ i = 19 ∨ 20 ≤ i) (h1 : i ≠ 1) (h25 : i ≠ 25) (h30 : i ≠ 30) :
    (innerResult r n d).reg (r i) = d.reg (r i) :=
  loopResult_frame (r 30) (factorBodyStore r) (r i) (hr.ne h30)
    (fun c => factorBodyStore_fresh r hr c i hi h1 h25) n d

theorem innerResult_bound (r : Fin 32 → Fin R) (hr : Function.Injective r) (M : ℕ) (hM : 1 ≤ M)
    (n : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 1)+n ≤ M) :
    ∀ j,(innerResult r n d).reg j ≤ M := by
  induction n generalizing d with
  | zero => exact hd
  | succ n ih =>
    change ∀ j,(innerResult r n (factorBodyStore r (d.setReg (r 30) n))).reg j ≤ M
    have hb := setReg_bound d (r 30) n M hd (by omega)
    apply ih _ (factorBodyStore_bound r hr M hM _ hb (by simp [reg_set r hr];omega))
    rw [factorBodyStore_index r hr]
    simp only [reg_set r hr,show (1:Fin 32) ≠ 30 from by decide,ite_false]
    omega

theorem innerResult_tapeData (r : Fin 32 → Fin R) (n : ℕ) (d : TapeStore R B) :
    tapeData (innerResult r n d) = tapeData d :=
  loopResult_tapeData (r 30) (factorBodyStore r) (factorBodyStore_tapeData r) n d

def innerPrepare (r : Fin 32 → Fin R) : TapeProgram R B 17 :=
  TapeProgram.seq (setTwo (r 1)) (TapeMacros.copy (r 24) (r 30) (r 28))
def innerPrepareStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := d.setReg (r 1) 2
  (c.setReg (r 30) (c.reg (r 24))).setReg (r 28) 0

theorem innerPrepare_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs) (d : TapeStore R B) :
    ∃ e,(innerPrepare r).Stops inp (d.toCfg (innerPrepare (B:=B) r).entry)
      (d.reg (r 1)+d.reg (r 30)+d.reg (r 28)+5*d.reg (r 24)+13) e ∧ e.store = innerPrepareStore r d := by
  obtain ⟨c,hc,hcs⟩ := setTwo_stops (r 1) inp d
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops (r 24) (r 30) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c.store
  have hcreg (i : Fin 32) (hi : i ≠ 1) : c.store.reg (r i) = d.reg (r i) := by
    rw [hcs];simp [reg_set r hr,hi]
  have h30 := hcreg 30 (by decide)
  have h28 := hcreg 28 (by decide)
  have h24 := hcreg 24 (by decide)
  have hall := hc.seq he
  refine ⟨e.mapPC (TapeProgram.rightLabel 6),?_,?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change e.store = _
    rw [hes,hcs];rfl

theorem innerPrepareStore_reg (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i : Fin 32) :
    (innerPrepareStore r d).reg (r i) = if i = 28 then 0 else if i = 30 then d.reg (r 24)
      else if i = 1 then 2 else d.reg (r i) := by
  fin_cases i <;> simp [innerPrepareStore,reg_set r hr]

theorem innerPrepareStore_bound (r : Fin 32 → Fin R) (hr : Function.Injective r) (M : ℕ) (hM : 2 ≤ M)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) : ∀ j,(innerPrepareStore r d).reg j ≤ M := by
  unfold innerPrepareStore
  apply setReg_bound _ _ 0 M _ (by omega)
  apply setReg_bound _ _ _ M
  · exact setReg_bound d _ 2 M hd hM
  · simpa [reg_set r hr] using hd (r 24)

def outerBody (r : Fin 32 → Fin R) : TapeProgram R B 345 :=
  TapeProgram.seq (TapeProgram.seq (innerPrepare r) (innerLoop r)) (TapeMacros.increment (r 0))
def outerBodyStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := innerResult r (d.reg (r 24)) (innerPrepareStore r d)
  c.setReg (r 0) (c.reg (r 0)+1)

theorem outerBodyStore_index (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    (outerBodyStore r d).reg (r 0) = d.reg (r 0)+1 := by
  unfold outerBodyStore
  simp only [TapeStore.setReg,Function.update_self]
  rw [innerResult_frame r hr _ _ 0 (Or.inl (by decide)) (by decide) (by decide) (by decide),innerPrepareStore_reg r hr]
  simp

theorem outerBodyStore_fresh (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 32) (hi : i < 5 ∨ i = 19 ∨ 20 ≤ i)
    (h0 : i ≠ 0) (h1 : i ≠ 1) (h25 : i ≠ 25) (h28 : i ≠ 28) (h30 : i ≠ 30) :
    (outerBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold outerBodyStore
  simp only [reg_set r hr,if_neg h0]
  rw [innerResult_frame r hr _ _ i hi h1 h25 h30,innerPrepareStore_reg r hr]
  simp [h28,h30,h1]

theorem outerBodyStore_bound (r : Fin 32 → Fin R) (hr : Function.Injective r) (M : ℕ) (hM : 2 ≤ M)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hQ : 2+d.reg (r 24) ≤ M) (hc : d.reg (r 0)+1 ≤ M) :
    ∀ j,(outerBodyStore r d).reg j ≤ M := by
  have hb := innerResult_bound r hr M (by omega) (d.reg (r 24)) (innerPrepareStore r d)
    (innerPrepareStore_bound r hr M hM d hd) (by simpa [innerPrepareStore_reg r hr] using hQ)
  apply setReg_bound _ _ _ M hb
  have he := outerBodyStore_index r hr d
  have he' : (innerResult r (d.reg (r 24)) (innerPrepareStore r d)).reg (r 0)+1 = d.reg (r 0)+1 := by
    simpa only [outerBodyStore,TapeStore.setReg,Function.update_self] using he
  rw [he'];exact hc

theorem outerBodyStore_tapeData (r : Fin 32 → Fin R) (d : TapeStore R B) :
    tapeData (outerBodyStore r d) = tapeData d := by
  rw [outerBodyStore,tapeData_setReg,innerResult_tapeData]
  rfl

theorem outerBody_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 2 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hQ : 2+d.reg (r 24) ≤ M) :
    ∃ t e,t ≤ 2500*(M+1)^5 ∧ (outerBody r).Stops inp (d.toCfg (outerBody (B:=B) r).entry) t e ∧ e.store = outerBodyStore r d := by
  obtain ⟨c₁,h₁,hs₁⟩ := innerPrepare_stops r hr inp d
  have hb₁ : ∀ j,c₁.store.reg j ≤ M := by rw [hs₁];exact innerPrepareStore_bound r hr M hM d hd
  have hn : c₁.reg (r 30) = d.reg (r 24) := by change c₁.store.reg (r 30) = _;rw [hs₁,innerPrepareStore_reg r hr];simp
  have hc : c₁.reg (r 1) = 2 := by change c₁.store.reg (r 1) = _;rw [hs₁,innerPrepareStore_reg r hr];simp
  obtain ⟨t,ht,h₂,_⟩ := innerLoop_stops r hr inp M (by omega) (d.reg (r 24)) c₁.store hn hb₁
    (by change c₁.reg (r 1)+d.reg (r 24) ≤ M;rw [hc];exact hQ)
  have h₃ := TapeMacros.increment_stops (r 0) inp (innerResult r (d.reg (r 24)) c₁.store)
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_,_,?_,hall,?_⟩
  · have hp : d.reg (r 1)+d.reg (r 30)+d.reg (r 28)+5*d.reg (r 24)+13 ≤ 8*M+13 := by
      have := hd (r 1);have := hd (r 30);have := hd (r 28);have := hd (r 24);omega
    have hpow := Nat.le_self_pow (by decide : (5:ℕ) ≠ 0) (M+1)
    have hM5 : M ≤ (M+1)^5 := (by omega : M ≤ M+1).trans hpow
    have h15 : 1 ≤ (M+1)^5 := by omega
    have hm : 2400*M*(M+1)^4 ≤ 2400*(M+1)^5 := by
      calc
        2400*M*(M+1)^4 ≤ 2400*(M+1)*(M+1)^4 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega : M ≤ M+1))
        _ = 2400*(M+1)^5 := by ring
    have ht' := Nat.mul_le_mul_right (2400*(M+1)^4+2) (hd (r 24))
    have heq : M*(2400*(M+1)^4+2) = 2400*M*(M+1)^4+2*M := by ring
    rw [heq] at ht'
    omega
  · change (innerResult r (d.reg (r 24)) c₁.store).setReg (r 0) _ = _
    rw [hs₁];rfl

def outerLoop (r : Fin 32 → Fin R) : TapeProgram R B 347 := TapeProgram.countedLoop (outerBody r) (r 26)
def outerResult (r : Fin 32 → Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B := loopResult (r 26) (outerBodyStore r) n d

theorem outerLoop_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 2 ≤ M) (n : ℕ) (d : TapeStore R B) (hn : d.reg (r 26) = n)
    (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 0)+n ≤ M) (hQ : 2+d.reg (r 24) ≤ M) :
    ∃ t,t ≤ n*(2500*(M+1)^5+2)+1 ∧ (outerLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 345)) t
      ((outerResult r n d).toCfg (TapeProgram.loopExit 345)) ∧ (∀ j,(outerResult r n d).reg j ≤ M) := by
  let Inv : ℕ → TapeStore R B → Prop := fun n c => (∀ j,c.reg j ≤ M) ∧ c.reg (r 0)+n ≤ M ∧ 2+c.reg (r 24) ≤ M
  have hf (c : TapeStore R B) : (outerBodyStore r c).reg (r 26) = c.reg (r 26) :=
    outerBodyStore_fresh r hr c 26 (Or.inr (Or.inr (by decide))) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hb : ∀ n c,c.reg (r 26) = n+1 → Inv (n+1) c → ∃ t e,t ≤ 2500*(M+1)^5 ∧
      (outerBody r).Stops inp ((c.setReg (r 26) n).toCfg (outerBody (B:=B) r).entry) t e ∧
      e.store = outerBodyStore r (c.setReg (r 26) n) ∧ Inv n e.store := by
    intro n c hcn hi
    have hcb := setReg_bound c (r 26) n M hi.1 (by have := hi.1 (r 26);omega)
    have hQ' : 2+(c.setReg (r 26) n).reg (r 24) ≤ M := by simpa [reg_set r hr] using hi.2.2
    have hci : (c.setReg (r 26) n).reg (r 0)+1 ≤ M := by simp [reg_set r hr];have := hi.2.1;omega
    obtain ⟨t,e,ht,he,hs⟩ := outerBody_stops r hr inp M hM _ hcb hQ'
    refine ⟨t,e,ht,he,hs,?_⟩
    rw [hs]
    refine ⟨outerBodyStore_bound r hr M hM _ hcb hQ' hci,?_,?_⟩
    · rw [outerBodyStore_index r hr]
      simp only [reg_set r hr,show (0:Fin 32) ≠ 26 from by decide,ite_false]
      have := hi.2.1;omega
    · rw [outerBodyStore_fresh r hr _ 24 (Or.inr (Or.inr (by decide))) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hQ'
  obtain ⟨t,ht,he,hi⟩ := loop_stops (outerBody r) (r 26) (outerBodyStore r) inp (2500*(M+1)^5) Inv hf hb n d hn ⟨hd,hc,hQ⟩
  exact ⟨t,ht,he,hi.1⟩

theorem outerResult_frame (r : Fin 32 → Fin R) (hr : Function.Injective r) (n : ℕ) (d : TapeStore R B)
    (i : Fin 32) (hi : i < 5 ∨ i = 19 ∨ 20 ≤ i)
    (h0 : i ≠ 0) (h1 : i ≠ 1) (h25 : i ≠ 25) (h26 : i ≠ 26) (h28 : i ≠ 28) (h30 : i ≠ 30) :
    (outerResult r n d).reg (r i) = d.reg (r i) :=
  loopResult_frame (r 26) (outerBodyStore r) (r i) (hr.ne h26)
    (fun c => outerBodyStore_fresh r hr c i hi h0 h1 h25 h28 h30) n d

theorem outerResult_tapeData (r : Fin 32 → Fin R) (n : ℕ) (d : TapeStore R B) :
    tapeData (outerResult r n d) = tapeData d :=
  loopResult_tapeData (r 26) (outerBodyStore r) (outerBodyStore_tapeData r) n d

def candidatePrepare (r : Fin 32 → Fin R) : TapeProgram R B 45 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeProgram.seq (TapeMacros.copy (r 23) (r 2) (r 28)) (TapeMacros.addPreserving (r 31) (r 2) (r 28)))
    (TapeMacros.clear (r 3))) (TapeMacros.clear (r 4))) (setTwo (r 0))) (setOne (r 25)))
    (TapeMacros.copy (r 24) (r 26) (r 28))
def candidatePrepareStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c₁ := (d.setReg (r 2) (d.reg (r 23))).setReg (r 28) 0
  let c₂ := (c₁.setReg (r 2) (c₁.reg (r 2)+c₁.reg (r 31))).setReg (r 28) 0
  let c₃ := (((c₂.setReg (r 3) 0).setReg (r 4) 0).setReg (r 0) 2).setReg (r 25) 1
  (c₃.setReg (r 26) (c₃.reg (r 24))).setReg (r 28) 0

theorem candidatePrepare_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 2 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M)
    (hsum : d.reg (r 23)+d.reg (r 31) ≤ M) :
    ∃ t e,t ≤ 100*M+100 ∧ (candidatePrepare r).Stops inp (d.toCfg (candidatePrepare (B:=B) r).entry) t e ∧
      e.store = candidatePrepareStore r d ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨c₁,h₁,hs₁⟩ := TapeMacros.copy_stops (r 23) (r 2) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d
  have hb₁ : ∀ j,c₁.store.reg j ≤ M := by
    rw [hs₁]
    exact setReg_bound _ _ 0 M (setReg_bound d _ _ M hd (hd (r 23))) (by omega)
  obtain ⟨c₂,h₂,hs₂⟩ := TapeMacros.addPreserving_stops (r 31) (r 2) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₁.store
  have hsum₁ : c₁.reg (r 2)+c₁.reg (r 31) ≤ M := by
    change c₁.store.reg (r 2)+c₁.store.reg (r 31) ≤ M
    rw [hs₁];simpa [reg_set r hr] using hsum
  have hb₂ : ∀ j,c₂.store.reg j ≤ M := by
    rw [hs₂]
    exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hb₁ hsum₁) (by omega)
  have h₃ := TapeMacros.clear_stops (r 3) inp (c₂.reg (r 3)) c₂.store rfl
  let c₃ := c₂.store.setReg (r 3) 0
  have hb₃ : ∀ j,c₃.reg j ≤ M := setReg_bound _ _ 0 M hb₂ (by omega)
  have h₄ := TapeMacros.clear_stops (r 4) inp (c₂.reg (r 4)) c₃ (by simp [c₃,reg_set r hr])
  let c₄ := c₃.setReg (r 4) 0
  have hb₄ : ∀ j,c₄.reg j ≤ M := setReg_bound _ _ 0 M hb₃ (by omega)
  obtain ⟨c₅,h₅,hs₅⟩ := setTwo_stops (r 0) inp c₄
  have hb₅ : ∀ j,c₅.store.reg j ≤ M := by rw [hs₅];exact setReg_bound _ _ 2 M hb₄ hM
  obtain ⟨c₆,h₆,hs₆⟩ := setOne_stops (r 25) inp c₅.store
  have hb₆ : ∀ j,c₆.store.reg j ≤ M := by rw [hs₆];exact setReg_bound _ _ 1 M hb₅ (by omega)
  obtain ⟨c₇,h₇,hs₇⟩ := TapeMacros.copy_stops (r 24) (r 26) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₆.store
  have hb₇ : ∀ j,c₇.store.reg j ≤ M := by
    rw [hs₇]
    exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hb₆ (hb₆ (r 24))) (by omega)
  have hall := (((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆).seq h₇
  refine ⟨_,_,?_,hall,?_,hb₇⟩
  · have hc₂3 : c₂.reg (r 3) ≤ M := hb₂ (r 3)
    have hc₂4 : c₂.reg (r 4) ≤ M := hb₂ (r 4)
    have := hd (r 2);have := hd (r 28);have := hd (r 23)
    have := hb₁ (r 28);have := hb₁ (r 31);have := hb₂ (r 3);have := hb₂ (r 4)
    have := hb₄ (r 0);have := hb₅ (r 25);have := hb₆ (r 26);have := hb₆ (r 28);have := hb₆ (r 24)
    omega
  · change c₇.store = _
    rw [hs₇,hs₆,hs₅]
    simp only [c₄,c₃]
    rw [hs₂,hs₁]
    rfl

theorem candidatePrepareStore_reg (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i : Fin 32) :
    (candidatePrepareStore r d).reg (r i) = if i = 2 then d.reg (r 23)+d.reg (r 31)
      else if i = 28 ∨ i = 3 ∨ i = 4 then 0 else if i = 0 then 2 else if i = 25 then 1
      else if i = 26 then d.reg (r 24) else d.reg (r i) := by
  fin_cases i <;> simp [candidatePrepareStore,reg_set r hr]

def candidateBody (r : Fin 32 → Fin R) : TapeProgram R B 409 :=
  TapeProgram.seq (TapeProgram.seq (candidatePrepare r) (outerLoop r)) (commit (commitLayout r))
def candidateBodyStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  commitStore (commitLayout r) (outerResult r (d.reg (r 24)) (candidatePrepareStore r d))

theorem candidateBodyStore_fresh (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 32) (hi : i = 19 ∨ i = 23 ∨ i = 24 ∨ i = 31) :
    (candidateBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold candidateBodyStore
  rw [commitStore_fresh _ _ _
    (hr.ne (show i ≠ (27:Fin 32) from by rcases hi with h|h|h|h <;> omega))
    (hr.ne (show i ≠ (28:Fin 32) from by rcases hi with h|h|h|h <;> omega))
    (hr.ne (show i ≠ (29:Fin 32) from by rcases hi with h|h|h|h <;> omega))
    (hr.ne (show i ≠ (25:Fin 32) from by rcases hi with h|h|h|h <;> omega)),
    outerResult_frame r hr _ _ i (by rcases hi with h|h|h|h <;> simp_all)
      (by rcases hi with h|h|h|h <;> omega) (by rcases hi with h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h <;> omega) (by rcases hi with h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h <;> omega) (by rcases hi with h|h|h|h <;> omega),
    candidatePrepareStore_reg r hr]
  rcases hi with rfl|rfl|rfl|rfl <;> simp

theorem candidateBody_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 2 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M)
    (hQ : 2+d.reg (r 24) ≤ M) (hsum : d.reg (r 23)+d.reg (r 31) ≤ M) :
    ∃ t e,t ≤ 10000*(M+1)^6 ∧ (candidateBody r).Stops inp (d.toCfg (candidateBody (B:=B) r).entry) t e ∧
      e.store = candidateBodyStore r d ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := candidatePrepare_stops r hr inp M hM d hd hsum
  have hn : c₁.reg (r 26) = d.reg (r 24) := by change c₁.store.reg (r 26) = _;rw [hs₁,candidatePrepareStore_reg r hr];simp
  have hc : c₁.reg (r 0) = 2 := by change c₁.store.reg (r 0) = _;rw [hs₁,candidatePrepareStore_reg r hr];simp
  have hQ₁ : 2+c₁.reg (r 24) ≤ M := by change 2+c₁.store.reg (r 24) ≤ M;rw [hs₁,candidatePrepareStore_reg r hr];simpa using hQ
  obtain ⟨t₂,ht₂,h₂,hb₂⟩ := outerLoop_stops r hr inp M hM (d.reg (r 24)) c₁.store hn hb₁
    (by change c₁.reg (r 0)+d.reg (r 24) ≤ M;rw [hc];exact hQ) hQ₁
  obtain ⟨t₃,c₃,ht₃,h₃,hs₃⟩ := commit_stops (commitLayout r) (commitLayout_injective r hr) inp M
    (outerResult r (d.reg (r 24)) c₁.store) hb₂
  have hb₃ : ∀ j,c₃.store.reg j ≤ M := by
    rw [hs₃];exact commitStore_bound _ (commitLayout_injective r hr) M (by omega) _ hb₂
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_,_,?_,hall,?_,hb₃⟩
  · have hpow := Nat.le_self_pow (by decide : (6:ℕ) ≠ 0) (M+1)
    have hM6 : M ≤ (M+1)^6 := (by omega : M ≤ M+1).trans hpow
    have h16 : 1 ≤ (M+1)^6 := by omega
    have hm : 2500*M*(M+1)^5 ≤ 2500*(M+1)^6 := by
      calc
        2500*M*(M+1)^5 ≤ 2500*(M+1)*(M+1)^5 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega : M ≤ M+1))
        _ = 2500*(M+1)^6 := by ring
    have ht' := Nat.mul_le_mul_right (2500*(M+1)^5+2) (hd (r 24))
    have heq : M*(2500*(M+1)^5+2) = 2500*M*(M+1)^5+2*M := by ring
    rw [heq] at ht'
    omega
  · change c₃.store = _
    rw [hs₃,hs₁];rfl

def candidateLoop (r : Fin 32 → Fin R) : TapeProgram R B 411 := TapeProgram.countedLoop (candidateBody r) (r 31)
def candidateResult (r : Fin 32 → Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B := loopResult (r 31) (candidateBodyStore r) n d

theorem candidateLoop_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 2 ≤ M) (n : ℕ) (d : TapeStore R B) (hn : d.reg (r 31) = n)
    (hd : ∀ j,d.reg j ≤ M) (hQ : 2+d.reg (r 24) ≤ M) (hq : 2*d.reg (r 23) ≤ M) (hnq : n ≤ d.reg (r 23)) :
    ∃ t,t ≤ n*(10000*(M+1)^6+2)+1 ∧ (candidateLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 409)) t
      ((candidateResult r n d).toCfg (TapeProgram.loopExit 409)) ∧ (∀ j,(candidateResult r n d).reg j ≤ M) := by
  let Inv : ℕ → TapeStore R B → Prop := fun n c =>
    (∀ j,c.reg j ≤ M) ∧ 2+c.reg (r 24) ≤ M ∧ 2*c.reg (r 23) ≤ M ∧ n ≤ c.reg (r 23)
  have hf (c : TapeStore R B) : (candidateBodyStore r c).reg (r 31) = c.reg (r 31) :=
    candidateBodyStore_fresh r hr c 31 (Or.inr (Or.inr (Or.inr rfl)))
  have hb : ∀ n c,c.reg (r 31) = n+1 → Inv (n+1) c → ∃ t e,t ≤ 10000*(M+1)^6 ∧
      (candidateBody r).Stops inp ((c.setReg (r 31) n).toCfg (candidateBody (B:=B) r).entry) t e ∧
      e.store = candidateBodyStore r (c.setReg (r 31) n) ∧ Inv n e.store := by
    intro n c hcn hi
    have hcb := setReg_bound c (r 31) n M hi.1 (by have := hi.1 (r 31);omega)
    have hQ' : 2+(c.setReg (r 31) n).reg (r 24) ≤ M := by simpa [reg_set r hr] using hi.2.1
    have hsum : (c.setReg (r 31) n).reg (r 23)+(c.setReg (r 31) n).reg (r 31) ≤ M := by
      simp [reg_set r hr]
      have := hi.2.2.1;have := hi.2.2.2;omega
    obtain ⟨t,e,ht,he,hs,hbound⟩ := candidateBody_stops r hr inp M hM _ hcb hQ' hsum
    refine ⟨t,e,ht,he,hs,hbound,?_,?_,?_⟩
    · rw [hs,candidateBodyStore_fresh r hr _ 24 (Or.inr (Or.inr (Or.inl rfl)))]
      exact hQ'
    · rw [hs,candidateBodyStore_fresh r hr _ 23 (Or.inr (Or.inl rfl))]
      simpa [reg_set r hr] using hi.2.2.1
    · rw [hs,candidateBodyStore_fresh r hr _ 23 (Or.inr (Or.inl rfl))]
      simp only [reg_set r hr,show (23:Fin 32) ≠ 31 from by decide,ite_false]
      have := hi.2.2.2;omega
  obtain ⟨t,ht,he,hi⟩ := loop_stops (candidateBody r) (r 31) (candidateBodyStore r) inp (10000*(M+1)^6)
    Inv hf hb n d hn ⟨hd,hQ,hq,hnq⟩
  exact ⟨t,ht,he,hi.1⟩

def prepare (r : Fin 32 → Fin R) : TapeProgram R B 30 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeMacros.copy (r 23) (r 24) (r 28)) (subtractTwo (r 24)))
    (TapeMacros.copy (r 23) (r 31) (r 28))) (TapeMacros.clear (r 27))) (TapeMacros.clear (r 29))
def prepareStore (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c₁ := (d.setReg (r 24) (d.reg (r 23))).setReg (r 28) 0
  let c₂ := c₁.setReg (r 24) (c₁.reg (r 24)-2)
  let c₃ := (c₂.setReg (r 31) (c₂.reg (r 23))).setReg (r 28) 0
  (c₃.setReg (r 27) 0).setReg (r 29) 0

theorem prepare_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∃ t e,t ≤ 20*M+30 ∧ (prepare r).Stops inp (d.toCfg (prepare (B:=B) r).entry) t e ∧
      e.store = prepareStore r d ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨c₁,h₁,hs₁⟩ := TapeMacros.copy_stops (r 23) (r 24) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d
  have hb₁ : ∀ j,c₁.store.reg j ≤ M := by
    rw [hs₁];exact setReg_bound _ _ 0 M (setReg_bound d _ _ M hd (hd (r 23))) (by omega)
  obtain ⟨c₂,h₂,hs₂⟩ := subtractTwo_stops (r 24) inp c₁.store
  have hb₂ : ∀ j,c₂.store.reg j ≤ M := by rw [hs₂];exact setReg_bound _ _ _ M hb₁ ((Nat.sub_le _ _).trans (hb₁ (r 24)))
  obtain ⟨c₃,h₃,hs₃⟩ := TapeMacros.copy_stops (r 23) (r 31) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₂.store
  have hb₃ : ∀ j,c₃.store.reg j ≤ M := by
    rw [hs₃];exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hb₂ (hb₂ (r 23))) (by omega)
  have h₄ := TapeMacros.clear_stops (r 27) inp (c₃.reg (r 27)) c₃.store rfl
  let c₄ := c₃.store.setReg (r 27) 0
  have hb₄ : ∀ j,c₄.reg j ≤ M := setReg_bound _ _ 0 M hb₃ (by omega)
  have h₅ := TapeMacros.clear_stops (r 29) inp (c₃.reg (r 29)) c₄ (by simp [c₄,reg_set r hr])
  have hall := (((h₁.seq h₂).seq h₃).seq h₄).seq h₅
  refine ⟨_,_,?_,hall,?_,setReg_bound _ _ 0 M hb₄ (by omega)⟩
  · have hc₃27 : c₃.reg (r 27) ≤ M := hb₃ (r 27)
    have hc₃29 : c₃.reg (r 29) ≤ M := hb₃ (r 29)
    have := hd (r 24);have := hd (r 28);have := hd (r 23)
    have := hb₂ (r 31);have := hb₂ (r 28);have := hb₂ (r 23)
    have := hb₃ (r 27);have := hb₃ (r 29);omega
  · change (c₃.store.setReg (r 27) 0).setReg (r 29) 0 = _
    rw [hs₃,hs₂,hs₁];rfl

theorem prepareStore_reg (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i : Fin 32) :
    (prepareStore r d).reg (r i) = if i = 29 ∨ i = 27 ∨ i = 28 then 0
      else if i = 24 then d.reg (r 23)-2 else if i = 31 then d.reg (r 23) else d.reg (r i) := by
  fin_cases i <;> simp [prepareStore,reg_set r hr]

/-- Fixed441-label canonical modulus constructor. Candidate moduli are visited
in descending order; every accepted index overwrites the previous answer. -/
def construct (r : Fin 32 → Fin R) : TapeProgram R B 441 := TapeProgram.seq (prepare r) (candidateLoop r)
def constructResult (r : Fin 32 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  candidateResult r (d.reg (r 23)) (prepareStore r d)

theorem construct_stops_exact (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hq : 2 ≤ d.reg (r 23)) (h2q : 2*d.reg (r 23) ≤ M) :
    ∃ t e,t ≤ 30000*(M+1)^7 ∧ (construct r).Stops inp (d.toCfg (construct (B:=B) r).entry) t e ∧
      e.store = constructResult r d ∧ (∀ j,e.reg j ≤ M) := by
  have hM : 2 ≤ M := by omega
  obtain ⟨t₁,c,ht₁,hc,hcs,hbound⟩ := prepare_stops r hr inp M d hd
  have hn : c.reg (r 31) = d.reg (r 23) := by change c.store.reg (r 31) = _;rw [hcs,prepareStore_reg r hr];simp
  have hQ : 2+c.reg (r 24) ≤ M := by
    change 2+c.store.reg (r 24) ≤ M
    rw [hcs,prepareStore_reg r hr]
    simp
    have := hd (r 23);omega
  have hq' : c.reg (r 23) = d.reg (r 23) := by change c.store.reg (r 23) = _;rw [hcs,prepareStore_reg r hr];simp
  obtain ⟨t₂,ht₂,h₂,hb₂⟩ := candidateLoop_stops r hr inp M hM (d.reg (r 23)) c.store hn hbound hQ
    (by change 2*c.reg (r 23) ≤ M;rw [hq'];exact h2q) (by change d.reg (r 23) ≤ c.reg (r 23);omega)
  have hall := hc.seq h₂
  refine ⟨_,_,?_,hall,?_,hb₂⟩
  · have hpow := Nat.le_self_pow (by decide : (7:ℕ) ≠ 0) (M+1)
    have hM7 : M ≤ (M+1)^7 := (by omega : M ≤ M+1).trans hpow
    have h17 : 1 ≤ (M+1)^7 := by omega
    have hm : 10000*M*(M+1)^6 ≤ 10000*(M+1)^7 := by
      calc
        10000*M*(M+1)^6 ≤ 10000*(M+1)*(M+1)^6 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega : M ≤ M+1))
        _ = 10000*(M+1)^7 := by ring
    have ht' := Nat.mul_le_mul_right (10000*(M+1)^6+2) (hd (r 23))
    have heq : M*(10000*(M+1)^6+2) = 10000*M*(M+1)^6+2*M := by ring
    rw [heq] at ht'
    omega
  · change candidateResult r (d.reg (r 23)) c.store = _
    rw [hcs];rfl

def FactorTest (N target a b : ℕ) : Prop := ∀ j < N,FieldCertificates.CoefficientMatches a b target 0 0 j
instance (N target a b : ℕ) : Decidable (FactorTest N target a b) := by unfold FactorTest;infer_instance

def FactorSetup (r : Fin 32 → Fin R) (N target : ℕ) (d : TapeStore R B) : Prop :=
  d.reg (r 2) = target ∧ d.reg (r 3) = 0 ∧ d.reg (r 4) = 0 ∧ d.reg (r 19) = N

theorem factorSetup_setReg (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target n : ℕ)
    (d : TapeStore R B) (i : Fin 32) (h2 : i ≠ 2) (h3 : i ≠ 3) (h4 : i ≠ 4) (h19 : i ≠ 19)
    (hs : FactorSetup r N target d) : FactorSetup r N target (d.setReg (r i) n) := by
  simpa [FactorSetup,reg_set r hr,Ne.symm h2,Ne.symm h3,Ne.symm h4,Ne.symm h19] using hs

theorem factorBodyStore_setup (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) : FactorSetup r N target (factorBodyStore r d) := by
  rcases hs with ⟨h2,h3,h4,h19⟩
  exact ⟨(factorBodyStore_fresh r hr d 2 (Or.inl (by decide)) (by decide) (by decide)).trans h2,
    (factorBodyStore_fresh r hr d 3 (Or.inl (by decide)) (by decide) (by decide)).trans h3,
    (factorBodyStore_fresh r hr d 4 (Or.inl (by decide)) (by decide) (by decide)).trans h4,
    (factorBodyStore_fresh r hr d 19 (Or.inr (Or.inl rfl)) (by decide) (by decide)).trans h19⟩

theorem factorBodyStore_valid (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) (hv : d.reg (r 25) ≤ 1) :
    (factorBodyStore r d).reg (r 25) =
      if FactorTest N target (d.reg (r 0)) (d.reg (r 1)) then 0 else d.reg (r 25) := by
  let c := certificateResult (certificateLayout r) d
  have hflag : c.reg (r 6) ≤ 1 := certificateResult_flag_le _ (certificateLayout_injective r hr) d
  have hsuccess : c.reg (r 6) = 1 ↔ FactorTest N target (d.reg (r 0)) (d.reg (r 1)) := by
    have h := certificateResult_correct (certificateLayout r) (certificateLayout_injective r hr) d
    rcases hs with ⟨h2,h3,h4,h19⟩
    change c.reg (r 6) = 1 ↔ ∀ j < d.reg (r 19),CoefficientMatches (d.reg (r 0)) (d.reg (r 1))
      (d.reg (r 2)) (d.reg (r 3)) (d.reg (r 4)) j at h
    simpa only [h2,h3,h4,h19,FactorTest] using h
  have hvalid : c.reg (r 25) = d.reg (r 25) := certificate_preserves r hr d 25 (Or.inr (Or.inr (by decide)))
  change ((requireStore (r 6) (r 25) c).setReg (r 1) _).reg (r 25) = _
  rw [reg_set r hr]
  simp only [show (25:Fin 32) ≠ 1 from by decide,ite_false]
  rw [requireStore_flag _ _ (hr.ne (by decide)) c (by rw [hvalid];exact hv),hvalid]
  by_cases ht : FactorTest N target (d.reg (r 0)) (d.reg (r 1))
  · have hf := hsuccess.mpr ht
    simp [ht,hf]
  · have hf : c.reg (r 6) = 0 := by
      have hn : c.reg (r 6) ≠ 1 := fun h => ht (hsuccess.mp h)
      omega
    simp [ht,hf]

theorem forall_lt_succ_shift (P : ℕ → Prop) (n start : ℕ) :
    (P start ∧ ∀ i < n,P (start+1+i)) ↔ ∀ i < n+1,P (start+i) := by
  constructor
  · rintro ⟨h0,ht⟩ i hi
    by_cases hz : i = 0
    · subst i;simpa using h0
    · have h := ht (i-1) (by omega)
      have he : start+1+(i-1) = start+i := by omega
      simpa only [he] using h
  · intro h
    refine ⟨by simpa using h 0 (by omega),?_⟩
    intro i hi
    have he : start+(i+1) = start+1+i := by omega
    simpa only [he] using h (i+1) (by omega)

theorem innerResult_setup (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target n : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) : FactorSetup r N target (innerResult r n d) := by
  rcases hs with ⟨h2,h3,h4,h19⟩
  exact ⟨(innerResult_frame r hr n d 2 (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans h2,
    (innerResult_frame r hr n d 3 (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans h3,
    (innerResult_frame r hr n d 4 (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans h4,
    (innerResult_frame r hr n d 19 (Or.inr (Or.inl rfl)) (by decide) (by decide) (by decide)).trans h19⟩

theorem innerResult_valid (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target n : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) (hv : d.reg (r 25) ≤ 1) :
    (innerResult r n d).reg (r 25) ≤ 1 ∧
      ((innerResult r n d).reg (r 25) = 1 ↔ d.reg (r 25) = 1 ∧
        ∀ i < n,¬ FactorTest N target (d.reg (r 0)) (d.reg (r 1)+i)) := by
  induction n generalizing d with
  | zero => exact ⟨hv,by simp [innerResult,loopResult]⟩
  | succ n ih =>
    let c := d.setReg (r 30) n
    have hsetup := factorSetup_setReg r hr N target n d 30 (by decide) (by decide) (by decide) (by decide) hs
    have hcv : c.reg (r 25) = d.reg (r 25) := by simp [c,reg_set r hr]
    have hc0 : c.reg (r 0) = d.reg (r 0) := by simp [c,reg_set r hr]
    have hc1 : c.reg (r 1) = d.reg (r 1) := by simp [c,reg_set r hr]
    have hfv : (factorBodyStore r c).reg (r 25) ≤ 1 := by
      rw [factorBodyStore_valid r hr N target c hsetup (by omega)]
      split <;> omega
    have ihc := ih (factorBodyStore r c) (factorBodyStore_setup r hr N target c hsetup) hfv
    have hstep : (factorBodyStore r c).reg (r 25) = 1 ↔ d.reg (r 25) = 1 ∧
        ¬ FactorTest N target (d.reg (r 0)) (d.reg (r 1)) := by
      rw [factorBodyStore_valid r hr N target c hsetup (by omega),hcv,hc0,hc1]
      by_cases ht : FactorTest N target (d.reg (r 0)) (d.reg (r 1)) <;> simp [ht]
    change (innerResult r n (factorBodyStore r c)).reg (r 25) ≤ 1 ∧ _
    refine ⟨ihc.1,?_⟩
    change (innerResult r n (factorBodyStore r c)).reg (r 25) = 1 ↔ _
    rw [ihc.2,hstep,factorBodyStore_fresh r hr c 0 (Or.inl (by decide)) (by decide) (by decide),hc0,
      factorBodyStore_index r hr c,hc1,and_assoc]
    exact and_congr_right (fun _ => forall_lt_succ_shift
      (fun b => ¬ FactorTest N target (d.reg (r 0)) b) n (d.reg (r 1)))

theorem innerPrepareStore_setup (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) : FactorSetup r N target (innerPrepareStore r d) := by
  simpa [FactorSetup,innerPrepareStore_reg r hr] using hs

theorem outerBodyStore_setup (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) : FactorSetup r N target (outerBodyStore r d) := by
  have hi := innerResult_setup r hr N target (d.reg (r 24)) (innerPrepareStore r d) (innerPrepareStore_setup r hr N target d hs)
  simpa [FactorSetup,outerBodyStore,reg_set r hr] using hi

theorem outerBodyStore_valid (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) (hv : d.reg (r 25) ≤ 1) :
    (outerBodyStore r d).reg (r 25) ≤ 1 ∧
      ((outerBodyStore r d).reg (r 25) = 1 ↔ d.reg (r 25) = 1 ∧
        ∀ b < d.reg (r 24),¬ FactorTest N target (d.reg (r 0)) (2+b)) := by
  have hi := innerResult_valid r hr N target (d.reg (r 24)) (innerPrepareStore r d)
    (innerPrepareStore_setup r hr N target d hs) (by simpa [innerPrepareStore_reg r hr] using hv)
  simpa [outerBodyStore,reg_set r hr,innerPrepareStore_reg r hr] using hi

theorem outerResult_valid (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target n : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) (hv : d.reg (r 25) ≤ 1) :
    (outerResult r n d).reg (r 25) ≤ 1 ∧
      ((outerResult r n d).reg (r 25) = 1 ↔ d.reg (r 25) = 1 ∧
        ∀ a < n,∀ b < d.reg (r 24),¬ FactorTest N target (d.reg (r 0)+a) (2+b)) := by
  induction n generalizing d with
  | zero => exact ⟨hv,by simp [outerResult,loopResult]⟩
  | succ n ih =>
    let c := d.setReg (r 26) n
    have hsetup := factorSetup_setReg r hr N target n d 26 (by decide) (by decide) (by decide) (by decide) hs
    have hcv : c.reg (r 25) = d.reg (r 25) := by simp [c,reg_set r hr]
    have hc0 : c.reg (r 0) = d.reg (r 0) := by simp [c,reg_set r hr]
    have hc24 : c.reg (r 24) = d.reg (r 24) := by simp [c,reg_set r hr]
    have hf := outerBodyStore_valid r hr N target c hsetup (by omega)
    have ihc := ih (outerBodyStore r c) (outerBodyStore_setup r hr N target c hsetup) hf.1
    have hstep : (outerBodyStore r c).reg (r 25) = 1 ↔ d.reg (r 25) = 1 ∧
        ∀ b < d.reg (r 24),¬ FactorTest N target (d.reg (r 0)) (2+b) := by simpa only [hcv,hc0,hc24] using hf.2
    change (outerResult r n (outerBodyStore r c)).reg (r 25) ≤ 1 ∧ _
    refine ⟨ihc.1,?_⟩
    change (outerResult r n (outerBodyStore r c)).reg (r 25) = 1 ↔ _
    rw [ihc.2,hstep,outerBodyStore_fresh r hr c 24 (Or.inr (Or.inr (by decide)))
      (by decide) (by decide) (by decide) (by decide) (by decide),hc24,outerBodyStore_index r hr c,hc0,
      and_assoc]
    exact and_congr_right (fun _ => forall_lt_succ_shift
      (fun a => ∀ b < d.reg (r 24),¬ FactorTest N target a (2+b)) n (d.reg (r 0)))

def OffsetFactorFree (ell : ℕ) (p : Fin (2^ell)) : Prop :=
  ∀ a < 2^ell-2,∀ b < 2^ell-2,¬ FactorTest (3*ell+1) (2^ell+p.val) (2+a) (2+b)

theorem offsetFactorFree_iff (ell : ℕ) (h : 0 < ell) (p : Fin (2^ell)) :
    OffsetFactorFree ell p ↔ RawIrreducibility.FactorFree ell p := by
  have hq : 2 ≤ 2^ell := Nat.one_lt_two_pow (by omega)
  constructor
  · intro hfree a b ha hb
    have hia : a.val-2 < 2^ell-2 := by have := a.isLt;omega
    have hib : b.val-2 < 2^ell-2 := by have := b.isLt;omega
    have hf := hfree (a.val-2) hia (b.val-2) hib
    change ¬ FactorTest (3*ell+1) (2^ell+p.val) a.val b.val
    have hea : 2+(a.val-2) = a.val := by omega
    have heb : 2+(b.val-2) = b.val := by omega
    simpa only [hea,heb] using hf
  · intro hfree a ha b hb
    have hia : 2+a < 2^ell := by omega
    have hib : 2+b < 2^ell := by omega
    exact hfree ⟨2+a,hia⟩ ⟨2+b,hib⟩ (by change 1 < 2+a;omega) (by change 1 < 2+b;omega)

def ModulusSetup (r : Fin 32 → Fin R) (ell : ℕ) (d : TapeStore R B) : Prop :=
  d.reg (r 23) = 2^ell ∧ d.reg (r 24) = 2^ell-2 ∧ d.reg (r 19) = 3*ell+1

theorem modulusSetup_setReg (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell n : ℕ)
    (d : TapeStore R B) (hs : ModulusSetup r ell d) : ModulusSetup r ell (d.setReg (r 31) n) := by
  simpa [ModulusSetup,reg_set r hr] using hs

theorem candidateBodyStore_setup (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell : ℕ)
    (d : TapeStore R B) (hs : ModulusSetup r ell d) : ModulusSetup r ell (candidateBodyStore r d) := by
  rcases hs with ⟨hq,hQ,hN⟩
  exact ⟨(candidateBodyStore_fresh r hr d 23 (Or.inr (Or.inl rfl))).trans hq,
    (candidateBodyStore_fresh r hr d 24 (Or.inr (Or.inr (Or.inl rfl)))).trans hQ,
    (candidateBodyStore_fresh r hr d 19 (Or.inl rfl)).trans hN⟩

theorem candidateValid_correct (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (d : TapeStore R B) (hs : ModulusSetup r ell d) (hc : d.reg (r 31) < 2^ell) :
    let c := outerResult r (d.reg (r 24)) (candidatePrepareStore r d)
    c.reg (r 25) ≤ 1 ∧ (c.reg (r 25) = 1 ↔ RawIrreducibility.FactorFree ell ⟨d.reg (r 31),hc⟩) := by
  have hp : FactorSetup r (3*ell+1) (2^ell+d.reg (r 31)) (candidatePrepareStore r d) := by
    rcases hs with ⟨hq,hQ,hN⟩
    simp [FactorSetup,candidatePrepareStore_reg r hr,hq,hN]
  have hi := outerResult_valid r hr (3*ell+1) (2^ell+d.reg (r 31)) (d.reg (r 24))
    (candidatePrepareStore r d) hp (by simp [candidatePrepareStore_reg r hr])
  refine ⟨hi.1,?_⟩
  have hiff : (outerResult r (d.reg (r 24)) (candidatePrepareStore r d)).reg (r 25) = 1 ↔
      OffsetFactorFree ell ⟨d.reg (r 31),hc⟩ := by
    simpa [OffsetFactorFree,candidatePrepareStore_reg r hr,hs.2.1] using hi.2
  exact hiff.trans (offsetFactorFree_iff ell h _)

def modulusTest (ell p : ℕ) : Bool :=
  if hp : p < 2^ell then decide (RawIrreducibility.FactorFree ell ⟨p,hp⟩) else false

def modulusAnswer (r : Fin 32 → Fin R) (d : TapeStore R B) : Option ℕ :=
  if d.reg (r 29) = 0 then none else some (d.reg (r 27))

theorem modulusAnswer_setReg (r : Fin 32 → Fin R) (d : TapeStore R B) (j : Fin R) (n : ℕ)
    (h27 : r 27 ≠ j) (h29 : r 29 ≠ j) : modulusAnswer r (d.setReg j n) = modulusAnswer r d := by
  simp [modulusAnswer,TapeStore.setReg,h27,h29]

theorem candidateBodyStore_answer (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (d : TapeStore R B) (hs : ModulusSetup r ell d) (hc : d.reg (r 31) < 2^ell) :
    modulusAnswer r (candidateBodyStore r d) =
      if modulusTest ell (d.reg (r 31)) then some (d.reg (r 31)) else modulusAnswer r d := by
  let c := outerResult r (d.reg (r 24)) (candidatePrepareStore r d)
  have hv := candidateValid_correct r hr ell h d hs hc
  have hbit : c.reg (r 25) ≤ 1 := hv.1
  have htest : modulusTest ell (d.reg (r 31)) = true ↔ RawIrreducibility.FactorFree ell ⟨d.reg (r 31),hc⟩ := by
    simp [modulusTest,hc]
  have hsuccess : c.reg (r 25) = 1 ↔ modulusTest ell (d.reg (r 31)) = true := hv.2.trans htest.symm
  have hreg (i : Fin 32) (hi : i = 27 ∨ i = 29 ∨ i = 31) : c.reg (r i) = d.reg (r i) := by
    rw [outerResult_frame r hr _ _ i (by rcases hi with h|h|h <;> simp_all)
      (by rcases hi with h|h|h <;> omega) (by rcases hi with h|h|h <;> omega)
      (by rcases hi with h|h|h <;> omega) (by rcases hi with h|h|h <;> omega)
      (by rcases hi with h|h|h <;> omega) (by rcases hi with h|h|h <;> omega),candidatePrepareStore_reg r hr]
    rcases hi with rfl|rfl|rfl <;> simp
  have h27 := hreg 27 (Or.inl rfl)
  have h29 := hreg 29 (Or.inr (Or.inl rfl))
  have h31 := hreg 31 (Or.inr (Or.inr rfl))
  change modulusAnswer r (commitStore (commitLayout r) c) = _
  by_cases hf : c.reg (r 25) = 0
  · have hac : modulusTest ell (d.reg (r 31)) ≠ true := by
      intro hacc
      have := hsuccess.mpr hacc
      omega
    simp [modulusAnswer,commitStore,commitLayout,hf,hac,h27,h29]
  · have hf1 : c.reg (r 25) = 1 := by omega
    have hac := hsuccess.mp hf1
    simp [modulusAnswer,commitStore,commitBodyStore,commitLayout,reg_set r hr,hf,hac,h31]

/-- Mathematical projection of the descending candidate-source scan. -/
def descend (test : ℕ → Bool) : ℕ → Option ℕ → Option ℕ
  | 0,state => state
  | n+1,state => descend test n (if test n then some n else state)

theorem descend_skip (test : ℕ → Bool) (n : ℕ) (state : Option ℕ) (hs : ∀ i < n,test i = false) :
    descend test n state = state := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
    rw [descend,hs n (by omega)]
    simp only [Bool.false_eq_true,reduceIte]
    exact ih state (fun i hi => hs i (by omega))

theorem descend_least (test : ℕ → Bool) (n target : ℕ) (state : Option ℕ)
    (ht : target < n) (hp : test target = true) (hm : ∀ i < n,test i = true → target ≤ i) :
    descend test n state = some target := by
  induction n generalizing state with
  | zero => omega
  | succ n ih =>
    rw [descend]
    by_cases he : target = n
    · subst target
      rw [hp,if_pos rfl]
      apply descend_skip
      intro i hi
      apply Bool.eq_false_iff.mpr
      intro hh
      have := hm i (by omega) hh
      omega
    · apply ih _ (by omega) (fun i hi => hm i (by omega))

theorem candidateResult_answer (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (n : ℕ) (d : TapeStore R B) (hs : ModulusSetup r ell d) (hn : n ≤ 2^ell) :
    modulusAnswer r (candidateResult r n d) = descend (modulusTest ell) n (modulusAnswer r d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    let c := d.setReg (r 31) n
    have hsetup := modulusSetup_setReg r hr ell n d hs
    have hc : c.reg (r 31) = n := by simp [c,reg_set r hr]
    have ha : modulusAnswer r c = modulusAnswer r d := modulusAnswer_setReg r d _ n (hr.ne (by decide)) (hr.ne (by decide))
    change modulusAnswer r (candidateResult r n (candidateBodyStore r c)) = _
    rw [ih (candidateBodyStore r c) (candidateBodyStore_setup r hr ell c hsetup) (by omega),
      candidateBodyStore_answer r hr ell h c hsetup (by omega),hc,ha]
    rfl

theorem constructResult_answer (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (d : TapeStore R B) (hq : d.reg (r 23) = 2^ell) (hN : d.reg (r 19) = 3*ell+1) :
    modulusAnswer r (constructResult r d) = descend (modulusTest ell) (2^ell) none := by
  have hs : ModulusSetup r ell (prepareStore r d) := by simp [ModulusSetup,prepareStore_reg r hr,hq,hN]
  rw [constructResult,hq,candidateResult_answer r hr ell h _ _ hs (by omega)]
  simp [modulusAnswer,prepareStore_reg r hr]

/-- The actual descending source search returns the exact canonical minimum
irreducible modulus index, not an alternate field representation. -/
theorem constructResult_index (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (d : TapeStore R B) (hq : d.reg (r 23) = 2^ell) (hN : d.reg (r 19) = 3*ell+1) :
    (constructResult r d).reg (r 27) = (selectedIndex ell h).val := by
  have hp : modulusTest ell (selectedIndex ell h).val = true := by
    simp [modulusTest,(selectedIndex ell h).isLt,RawIrreducibility.selectedIndex_factorFree ell h]
  have hm : ∀ i < 2^ell,modulusTest ell i = true → (selectedIndex ell h).val ≤ i := by
    intro i hi ht
    have hfree : RawIrreducibility.FactorFree ell ⟨i,hi⟩ := by simpa [modulusTest,hi] using ht
    exact RawIrreducibility.selectedIndex_le ell h ⟨i,hi⟩ hfree
  have han : modulusAnswer r (constructResult r d) = some (selectedIndex ell h).val := by
    rw [constructResult_answer r hr ell h d hq hN]
    exact descend_least (modulusTest ell) (2^ell) (selectedIndex ell h).val none (selectedIndex ell h).isLt hp hm
  unfold modulusAnswer at han
  split at han
  · contradiction
  · exact Option.some.inj han

theorem candidateBodyStore_input (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 32) (hi : i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23) :
    (candidateBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold candidateBodyStore
  rw [commitStore_fresh _ _ _
    (hr.ne (show i ≠ (27:Fin 32) from by rcases hi with h|h|h|h|h <;> omega))
    (hr.ne (show i ≠ (28:Fin 32) from by rcases hi with h|h|h|h|h <;> omega))
    (hr.ne (show i ≠ (29:Fin 32) from by rcases hi with h|h|h|h|h <;> omega))
    (hr.ne (show i ≠ (25:Fin 32) from by rcases hi with h|h|h|h|h <;> omega)),
    outerResult_frame r hr _ _ i (by rcases hi with h|h|h|h|h <;> simp_all)
      (by rcases hi with h|h|h|h|h <;> omega) (by rcases hi with h|h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h|h <;> omega) (by rcases hi with h|h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h|h <;> omega) (by rcases hi with h|h|h|h|h <;> omega),
    candidatePrepareStore_reg r hr]
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> simp

theorem constructResult_input (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 32) (hi : i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23) :
    (constructResult r d).reg (r i) = d.reg (r i) := by
  rw [constructResult,candidateResult,loopResult_frame (r 31) (candidateBodyStore r) (r i)
    (hr.ne (show i ≠ (31:Fin 32) from by rcases hi with h|h|h|h|h <;> omega))
    (fun c => candidateBodyStore_input r hr c i hi),prepareStore_reg r hr]
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> simp

theorem candidateBodyStore_tapeData (r : Fin 32 → Fin R) (d : TapeStore R B) :
    tapeData (candidateBodyStore r d) = tapeData d := by
  rw [candidateBodyStore,commitStore_tapeData,outerResult_tapeData]
  rfl

theorem constructResult_tapeData (r : Fin 32 → Fin R) (d : TapeStore R B) :
    tapeData (constructResult r d) = tapeData d := by
  rw [constructResult,candidateResult,loopResult_tapeData (r 31) (candidateBodyStore r) (candidateBodyStore_tapeData r)]
  rfl

theorem factorBodyStore_outside (r : Fin 32 → Fin R) (d : TapeStore R B) (j : Fin R) (hne : ∀ i : Fin 32,j ≠ r i) :
    (factorBodyStore r d).reg j = d.reg j := by
  unfold factorBodyStore
  simp only [TapeStore.setReg,Function.update_of_ne (hne 1)]
  rw [requireStore_fresh _ _ _ _ (hne 6) (hne 25)]
  apply certificateResult_outside
  intro i
  exact hne ⟨i.val,by have := i.isLt;omega⟩

theorem innerResult_outside (r : Fin 32 → Fin R) (n : ℕ) (d : TapeStore R B) (j : Fin R) (hne : ∀ i : Fin 32,j ≠ r i) :
    (innerResult r n d).reg j = d.reg j :=
  loopResult_frame (r 30) (factorBodyStore r) j (hne 30) (fun c => factorBodyStore_outside r c j hne) n d

theorem outerBodyStore_outside (r : Fin 32 → Fin R) (d : TapeStore R B) (j : Fin R) (hne : ∀ i : Fin 32,j ≠ r i) :
    (outerBodyStore r d).reg j = d.reg j := by
  unfold outerBodyStore
  simp only [TapeStore.setReg,Function.update_of_ne (hne 0)]
  rw [innerResult_outside r _ _ j hne]
  simp [innerPrepareStore,TapeStore.setReg,hne 1,hne 28,hne 30]

theorem outerResult_outside (r : Fin 32 → Fin R) (n : ℕ) (d : TapeStore R B) (j : Fin R) (hne : ∀ i : Fin 32,j ≠ r i) :
    (outerResult r n d).reg j = d.reg j :=
  loopResult_frame (r 26) (outerBodyStore r) j (hne 26) (fun c => outerBodyStore_outside r c j hne) n d

theorem candidateBodyStore_outside (r : Fin 32 → Fin R) (d : TapeStore R B) (j : Fin R) (hne : ∀ i : Fin 32,j ≠ r i) :
    (candidateBodyStore r d).reg j = d.reg j := by
  rw [candidateBodyStore,commitStore_fresh _ _ _ (hne 27) (hne 28) (hne 29) (hne 25),outerResult_outside r _ _ j hne]
  simp [candidatePrepareStore,TapeStore.setReg,hne 0,hne 2,hne 3,hne 4,hne 25,hne 26,hne 28]

theorem constructResult_outside (r : Fin 32 → Fin R) (d : TapeStore R B) (j : Fin R) (hne : ∀ i : Fin 32,j ≠ r i) :
    (constructResult r d).reg j = d.reg j := by
  rw [constructResult,candidateResult,loopResult_frame (r 31) (candidateBodyStore r) j (hne 31)
    (fun c => candidateBodyStore_outside r c j hne)]
  simp [prepareStore,TapeStore.setReg,hne 24,hne 27,hne 28,hne 29,hne 31]

/-- Complete canonical modulus source contract, including every caller/tape
frame and the polynomial source-step bound. -/
theorem construct_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (ell : ℕ) (h : 0 < ell) (M : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M)
    (hq : d.reg (r 23) = 2^ell) (hN : d.reg (r 19) = 3*ell+1) (h2q : 2*(2^ell) ≤ M) :
    ∃ t e,t ≤ 30000*(M+1)^7 ∧ (construct r).Stops inp (d.toCfg (construct (B:=B) r).entry) t e ∧
      e.store = constructResult r d ∧ e.reg (r 27) = (selectedIndex ell h).val ∧
      (∀ i,i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ tapeData e.store = tapeData d := by
  obtain ⟨t,e,ht,he,hes,hbound⟩ := construct_stops_exact r hr inp M d hd
    (by rw [hq];exact Nat.one_lt_two_pow (by omega)) (by rw [hq];exact h2q)
  refine ⟨t,e,ht,he,hes,?_,?_,?_,hbound,?_⟩
  · change e.store.reg (r 27) = _
    rw [hes];exact constructResult_index r hr ell h d hq hN
  · intro i hi
    change e.store.reg (r i) = _
    rw [hes];exact constructResult_input r hr d i hi
  · intro j hj
    change e.store.reg j = _
    rw [hes];exact constructResult_outside r d j hj
  · rw [hes];exact constructResult_tapeData r d

#print axioms construct_stops
#print axioms constructResult_index
#print axioms construct_stops_exact
#print axioms candidateLoop_stops
#print axioms outerLoop_stops
#print axioms innerLoop_stops
end ExpandingCodes.Computation.SourceModulus
