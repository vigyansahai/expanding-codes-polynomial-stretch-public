import ExpandingCodes.Computation.FieldCertificates

set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.SourceFieldArithmetic
open NKtLB FieldPrograms FieldConvolution FieldCertificates
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B L : ℕ}

/-- Execute a finite source fragment only when a disposable runtime flag is
positive. The zero branch halts in one actual instruction. -/
def onPositive (P : TapeProgram R B L) (flag : Fin R) : TapeProgram R B (L+2) where
  entry := TapeProgram.loopHeader L
  code j := match finSumFinEquiv.symm j with
    | .inl i => (P.code i).relabel (TapeProgram.leftLabel 2)
    | .inr i => if i = 0 then .dec flag (TapeProgram.loopExit L)
        (TapeProgram.leftLabel 2 P.entry) else .halt

theorem onPositive_code_left (P : TapeProgram R B L) (flag : Fin R) (i : Fin L) :
    (onPositive P flag).code (TapeProgram.leftLabel 2 i) =
      (P.code i).relabel (TapeProgram.leftLabel 2) := by
  simp [onPositive, TapeProgram.leftLabel]

theorem onPositive_zero (P : TapeProgram R B L) (flag : Fin R) (inp : Inputs)
    (d : TapeStore R B) (hf : d.reg flag = 0) :
    (onPositive P flag).Stops inp (d.toCfg (TapeProgram.loopHeader L)) 1
      (d.toCfg (TapeProgram.loopExit L)) := by
  constructor
  · apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, onPositive, TapeProgram.loopHeader, TapeProgram.rightLabel]
    · simp [TapeProgram.step, onPositive, TapeProgram.loopHeader, TapeProgram.loopExit,
        TapeProgram.rightLabel, hf]
  · simp [TapeProgram.halted, onPositive, TapeProgram.loopExit, TapeProgram.rightLabel]

theorem onPositive_positive (P : TapeProgram R B L) (flag : Fin R) (inp : Inputs)
    (d : TapeStore R B) (hf : d.reg flag ≠ 0) (t : ℕ) (e : TapeCfg R B L)
    (he : P.Stops inp ((d.setReg flag (d.reg flag-1)).toCfg P.entry) t e) :
    (onPositive P flag).Stops inp (d.toCfg (TapeProgram.loopHeader L)) (1+t)
      (e.mapPC (TapeProgram.leftLabel 2)) := by
  have hhead : (onPositive P flag).Exec inp (d.toCfg (TapeProgram.loopHeader L)) 1
      (((d.setReg flag (d.reg flag-1)).toCfg P.entry).mapPC (TapeProgram.leftLabel 2)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, onPositive, TapeProgram.loopHeader, TapeProgram.rightLabel]
    · simp [TapeProgram.step, onPositive, TapeProgram.loopHeader, TapeProgram.loopExit,
        TapeProgram.rightLabel, hf, TapeStore.setReg]
  constructor
  · exact hhead.trans (he.exec.relabel (TapeProgram.leftLabel 2)
      (fun i _ => onPositive_code_left P flag i))
  · change (onPositive P flag).code (TapeProgram.leftLabel 2 e.pc) = .halt
    rw [onPositive_code_left, he.halted]
    rfl

/-- Conditional search commit: copy an accepted candidate into the answer
counter and set a found bit to one. Its five registers are pairwise distinct. -/
def commitBody (r : Fin 5 → Fin R) : TapeProgram R B 15 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.copy (r 0) (r 1) (r 2))
    (TapeMacros.clear (r 3))) (TapeMacros.increment (r 3))

def commitBodyStore (r : Fin 5 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  ((d.setReg (r 1) (d.reg (r 0))).setReg (r 2) 0).setReg (r 3) 1

theorem reg_set (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i j : Fin 5) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j; simp
  · simp [TapeStore.setReg, h, hr.ne h]

theorem commitBody_stops (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (commitBody r).Stops inp (d.toCfg (commitBody (B := B) r).entry)
      (d.reg (r 1)+d.reg (r 2)+5*d.reg (r 0)+d.reg (r 3)+11) e ∧
      e.store = commitBodyStore r d := by
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops (r 0) (r 1) (r 2)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d
  have hcf : c.reg (r 3) = d.reg (r 3) := by
    change c.store.reg (r 3) = _
    rw [hcs]; simp [reg_set r hr]
  have hclear := TapeMacros.clear_stops (r 3) inp (d.reg (r 3)) c.store hcf
  have hinc := TapeMacros.increment_stops (r 3) inp (c.store.setReg (r 3) 0)
  have hz : (c.store.setReg (r 3) 0).reg (r 3) = 0 := by simp [TapeStore.setReg]
  rw [hz, zero_add] at hinc
  have hall := (hc.seq hclear).seq hinc
  refine ⟨((c.store.setReg (r 3) 0).setReg (r 3) 1).toCfg (1:Fin 2) |>.mapPC
    (TapeProgram.rightLabel 13), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change (c.store.setReg (r 3) 0).setReg (r 3) 1 = _
    rw [TapeStore.setReg_same, hcs]
    rfl

def commit (r : Fin 5 → Fin R) : TapeProgram R B 17 :=
  onPositive (commitBody r) (r 4)

def commitStore (r : Fin 5 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  if d.reg (r 4) = 0 then d else
    commitBodyStore r (d.setReg (r 4) (d.reg (r 4)-1))

theorem commit_stops (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 8*M+12 ∧
      (commit r).Stops inp (d.toCfg (commit (B := B) r).entry) t e ∧
      e.store = commitStore r d := by
  by_cases hf : d.reg (r 4) = 0
  · refine ⟨1, d.toCfg (TapeProgram.loopExit 15), by omega,
      onPositive_zero (commitBody r) (r 4) inp d hf, ?_⟩
    simp [commitStore, hf]
  · obtain ⟨c, hc, hcs⟩ := commitBody_stops r hr inp (d.setReg (r 4) (d.reg (r 4)-1))
    have hall := onPositive_positive (commitBody r) (r 4) inp d hf _ c hc
    refine ⟨_, _, ?_, hall, ?_⟩
    · simp only [reg_set r hr]
      simp
      have := hd (r 0); have := hd (r 1); have := hd (r 2); have := hd (r 3)
      omega
    · change c.store = _
      rw [hcs]
      simp only [commitStore, if_neg hf]

/-- Every accepted bounded remainder is the exact existing field multiplication
index. Polynomial division appears only in this semantic uniqueness proof. -/
theorem accepted_remainder_unique (ell : ℕ) (h : 0 < ell) (m a b rem : Fin (2^ell))
    (s : Fin (2^(2*ell)))
    (hmatch : BinaryField.DivMatches ell m (indexEquiv ell a) (indexEquiv ell b)
      (indexEquiv ell rem) (indexEquiv (2*ell) s)) :
    rem = BinaryField.multiplyIndex ell h m (indexEquiv ell a) (indexEquiv ell b) := by
  have he := (BinaryField.divMatches_iff ell h m _ _ _ _).mp hmatch
  have hdeg : (polynomial (indexEquiv ell rem)).degree < (candidate ell m).degree := by
    simpa only [Polynomial.degree_eq_natDegree (candidate_monic ell m).ne_zero,
      candidate_natDegree] using degree_polynomial_lt (indexEquiv ell rem)
  have hrem := ((Polynomial.div_modByMonic_unique (polynomial (indexEquiv (2*ell) s))
    (polynomial (indexEquiv ell rem)) (candidate_monic ell m) ⟨he.symm,hdeg⟩).2).symm
  have hmul := BinaryField.multiply_remainder ell h m (indexEquiv ell a) (indexEquiv ell b)
  apply (indexEquiv ell).injective
  funext i
  have hp := hrem.trans hmul.symm
  have hc := congrArg (fun p : Polynomial (ZMod 2) => p.coeff i.val) hp
  simpa only [BinaryField.multiply, coefficient_polynomial] using hc

theorem commitStore_reg (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 5) :
    (commitStore r d).reg (r i) =
      if d.reg (r 4) = 0 then d.reg (r i) else
        if i = 1 then d.reg (r 0) else if i = 2 then 0 else if i = 3 then 1
        else if i = 4 then d.reg (r 4)-1 else d.reg (r i) := by
  by_cases hf : d.reg (r 4) = 0 <;> fin_cases i <;>
    simp [commitStore, commitBodyStore, hf, reg_set r hr]

theorem commitStore_fresh (r : Fin 5 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₁ : j ≠ r 1) (h₂ : j ≠ r 2) (h₃ : j ≠ r 3) (h₄ : j ≠ r 4) :
    (commitStore r d).reg j = d.reg j := by
  unfold commitStore
  split <;> simp_all [commitBodyStore, TapeStore.setReg]

theorem commitStore_bound (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (commitStore r d).reg j ≤ M := by
  unfold commitStore commitBodyStore
  split
  · exact hd
  · apply setReg_bound _ _ 1 M _ hM
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M
    · exact setReg_bound _ _ _ M hd ((Nat.sub_le _ _).trans (hd (r 4)))
    · simp only [reg_set r hr]
      simpa using hd (r 0)

theorem commitStore_tapeData (r : Fin 5 → Fin R) (d : TapeStore R B) :
    tapeData (commitStore r d) = tapeData d := by
  unfold commitStore
  split <;> rfl

theorem certificateResult_outside (r : Fin 20 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 20, j ≠ r i) :
    (certificateResult r d).reg j = d.reg j := by
  rw [certificateResult, certificateStore_outside]
  · simp [FieldCertificates.prepareStore, TapeStore.setReg, hne 5, hne 6, hne 17, hne 18]
  · intro i
    exact hne i.castSucc

/-- A semantic fold of a finite loop body. This records post-stores only; the
source program is always the separate finite `countedLoop P counter`. -/
def loopResult (counter : Fin R) (F : TapeStore R B → TapeStore R B) :
    ℕ → TapeStore R B → TapeStore R B
  | 0, d => d
  | n+1, d => loopResult counter F n (F (d.setReg counter n))

/-- Modular exact loop execution allowing a body temporarily to use its loop
counter, provided that it restores the counter before returning. -/
theorem loop_stops (P : TapeProgram R B L) (counter : Fin R)
    (F : TapeStore R B → TapeStore R B) (inp : Inputs) (C : ℕ)
    (Inv : ℕ → TapeStore R B → Prop)
    (hcounter : ∀ d, (F d).reg counter = d.reg counter)
    (hbody : ∀ n d, d.reg counter = n+1 → Inv (n+1) d →
      ∃ t c, t ≤ C ∧ P.Stops inp ((d.setReg counter n).toCfg P.entry) t c ∧
        c.store = F (d.setReg counter n) ∧ Inv n c.store)
    (n : ℕ) (d : TapeStore R B) (hn : d.reg counter = n) (hi : Inv n d) :
    ∃ t, t ≤ n*(C+2)+1 ∧
      (TapeProgram.countedLoop P counter).Stops inp (d.toCfg (TapeProgram.loopHeader L)) t
        ((loopResult counter F n d).toCfg (TapeProgram.loopExit L)) ∧
      Inv 0 (loopResult counter F n d) := by
  induction n generalizing d with
  | zero => exact ⟨1, by omega, TapeProgram.loop_zero P counter inp d hn, hi⟩
  | succ n ih =>
    obtain ⟨s, c, hs, hc, hcs, hci⟩ := hbody n d hn hi
    have hcn : c.reg counter = n := by
      change c.store.reg counter = _
      rw [hcs, hcounter]
      simp [TapeStore.setReg]
    obtain ⟨t, ht, he, hei⟩ := ih c.store hcn hci
    have hhead := TapeProgram.loop_positive_header P counter inp d (by omega)
    have hdec : TapeProgram.decStore counter d = d.setReg counter n := by
      simp [TapeProgram.decStore, TapeStore.setReg, hn]
    rw [hdec] at hhead
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2) (TapeProgram.loop_code_body_active P counter)
    have hreturn := TapeProgram.loop_body_return P counter inp c hc.halted
    have hpost : loopResult counter F n c.store = loopResult counter F (n+1) d := by
      rw [loopResult, hcs]
    have hall := ((hhead.trans hrun).trans hreturn).trans he.exec
    rw [hpost] at hall hei
    refine ⟨_, ?_, ⟨hall, TapeProgram.loop_code_exit P counter⟩, hei⟩
    calc
      1+s+1+t ≤ 1+C+1+(n*(C+2)+1) := by omega
      _ = (n+1)*(C+2)+1 := by ring

theorem loopResult_frame (counter : Fin R) (F : TapeStore R B → TapeStore R B)
    (j : Fin R) (hj : j ≠ counter) (hF : ∀ d, (F d).reg j = d.reg j)
    (n : ℕ) (d : TapeStore R B) : (loopResult counter F n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [loopResult, ih, hF]
    simp [TapeStore.setReg, hj]

theorem loopResult_index (counter : Fin R) (F : TapeStore R B → TapeStore R B)
    (j : Fin R) (hj : j ≠ counter) (hF : ∀ d, (F d).reg j = d.reg j+1)
    (n : ℕ) (d : TapeStore R B) : (loopResult counter F n d).reg j = d.reg j+n := by
  induction n generalizing d with
  | zero => simp [loopResult]
  | succ n ih =>
    rw [loopResult, ih, hF]
    simp only [TapeStore.setReg, Function.update_of_ne hj]
    omega

theorem loopResult_count (counter : Fin R) (F : TapeStore R B → TapeStore R B)
    (hF : ∀ d, (F d).reg counter = d.reg counter) (n : ℕ) (d : TapeStore R B)
    (hn : d.reg counter = n) : (loopResult counter F n d).reg counter = 0 := by
  induction n generalizing d with
  | zero => exact hn
  | succ n ih =>
    rw [loopResult]
    apply ih
    rw [hF]
    simp [TapeStore.setReg]

theorem loopResult_tapeData (counter : Fin R) (F : TapeStore R B → TapeStore R B)
    (hF : ∀ d, tapeData (F d) = tapeData d) (n : ℕ) (d : TapeStore R B) :
    tapeData (loopResult counter F n d) = tapeData d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [loopResult, ih, hF, tapeData_setReg]

/-- Static multiplication-search register layout. Registers 0..19 are the
certificate interface; 20=answer,21=copy scratch,22=found,23=q,24=q²,
25=outer counter and26=inner counter. -/
def certificateLayout (r : Fin 27 → Fin R) : Fin 20 → Fin R :=
  fun i => r ⟨i.val, by have := i.isLt; omega⟩
def commitLayout (r : Fin 27 → Fin R) : Fin 5 → Fin R :=
  fun i => r (![2,20,21,22,6] i)

theorem certificateLayout_injective (r : Fin 27 → Fin R) (hr : Function.Injective r) :
    Function.Injective (certificateLayout r) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin 27 => z.val) (hr h)

theorem commitLayout_injective (r : Fin 27 → Fin R) (hr : Function.Injective r) :
    Function.Injective (commitLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [commitLayout]

theorem reg_set27 (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i j : Fin 27) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j; simp
  · simp [TapeStore.setReg, h, hr.ne h]

theorem certificate_preserves (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) (hi : i < 5 ∨ i = 19 ∨ 20 ≤ i) :
    (certificateResult (certificateLayout r) d).reg (r i) = d.reg (r i) := by
  rcases hi with hi | rfl | hi
  · let j : Fin 18 := ⟨i.val, by change i.val < 5 at hi; omega⟩
    have h := certificateResult_input (certificateLayout r) (certificateLayout_injective r hr)
      d j (by change i.val < 5; exact hi)
    simpa [certificateLayout, j] using h
  · exact certificateResult_runtimeBound (certificateLayout r) (certificateLayout_injective r hr) d
  · apply certificateResult_outside
    intro j
    apply hr.ne
    intro h
    have hv := congrArg (fun z : Fin 27 => z.val) h
    change i.val = j.val at hv
    change 20 ≤ i.val at hi
    have := j.isLt
    omega

/-- One successful-pair scan step. This invokes the actual319-label certificate,
conditionally commits its remainder, and increments the quotient candidate. -/
def innerBody (r : Fin 27 → Fin R) : TapeProgram R B 338 :=
  TapeProgram.seq (TapeProgram.seq (certificate (certificateLayout r))
    (commit (commitLayout r))) (TapeMacros.increment (r 4))

def innerBodyStore (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := commitStore (commitLayout r) (certificateResult (certificateLayout r) d)
  c.setReg (r 4) (c.reg (r 4)+1)

theorem innerBodyStore_fresh (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) (hi : i < 4 ∨ i = 19 ∨ 23 ≤ i) :
    (innerBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold innerBodyStore
  simp only [reg_set27 r hr, show i ≠ (4:Fin 27) from by rcases hi with h|h|h <;> omega, ite_false]
  rw [commitStore_fresh _ _ _
    (hr.ne (show i ≠ (20:Fin 27) from by rcases hi with h|h|h <;> omega))
    (hr.ne (show i ≠ (21:Fin 27) from by rcases hi with h|h|h <;> omega))
    (hr.ne (show i ≠ (22:Fin 27) from by rcases hi with h|h|h <;> omega))
    (hr.ne (show i ≠ (6:Fin 27) from by rcases hi with h|h|h <;> omega))]
  apply certificate_preserves r hr d i
  rcases hi with h|h|h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by omega))

theorem innerBodyStore_quotient (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (innerBodyStore r d).reg (r 4) = d.reg (r 4)+1 := by
  unfold innerBodyStore
  simp only [TapeStore.setReg, Function.update_self]
  rw [commitStore_fresh _ _ _
    (hr.ne (show (4:Fin 27) ≠ 20 from by decide)) (hr.ne (show (4:Fin 27) ≠ 21 from by decide))
    (hr.ne (show (4:Fin 27) ≠ 22 from by decide)) (hr.ne (show (4:Fin 27) ≠ 6 from by decide)),
    certificate_preserves r hr d 4 (Or.inl (by decide))]

theorem innerBodyStore_tapeData (r : Fin 27 → Fin R) (d : TapeStore R B) :
    tapeData (innerBodyStore r d) = tapeData d := by
  rw [innerBodyStore, tapeData_setReg, commitStore_tapeData, certificateResult_tapeData]

theorem innerBodyStore_bound (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hq : d.reg (r 4)+1 ≤ M) : ∀ j, (innerBodyStore r d).reg j ≤ M := by
  apply setReg_bound _ _ _ M
    (commitStore_bound _ (commitLayout_injective r hr) M hM _
      (certificateResult_bound _ (certificateLayout_injective r hr) M hM d hd))
  have he := innerBodyStore_quotient r hr d
  have he' : (commitStore (commitLayout r) (certificateResult (certificateLayout r) d)).reg (r 4)+1 =
      d.reg (r 4)+1 := by simpa only [innerBodyStore, TapeStore.setReg, Function.update_self] using he
  rw [he']; exact hq

theorem innerBody_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 2400*(M+1)^4 ∧
      (innerBody r).Stops inp (d.toCfg (innerBody (B := B) r).entry) t e ∧
      e.store = innerBodyStore r d := by
  obtain ⟨t₁, c₁, ht₁, h₁, hs₁⟩ := certificate_stops_exact (certificateLayout r)
    (certificateLayout_injective r hr) inp M hM d hd
  have hb₁ : ∀ j, c₁.store.reg j ≤ M := by
    rw [hs₁]; exact certificateResult_bound _ (certificateLayout_injective r hr) M hM d hd
  obtain ⟨t₂, c₂, ht₂, h₂, hs₂⟩ := commit_stops (commitLayout r)
    (commitLayout_injective r hr) inp M c₁.store hb₁
  have h₃ := TapeMacros.increment_stops (r 4) inp c₂.store
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_, _, ?_, hall, ?_⟩
  · have hpow := Nat.le_self_pow (by decide : (4:ℕ) ≠ 0) (M+1)
    omega
  · change c₂.store.setReg (r 4) _ = _
    rw [hs₂, hs₁]
    rfl

def innerLoop (r : Fin 27 → Fin R) : TapeProgram R B 340 :=
  TapeProgram.countedLoop (innerBody r) (r 26)
def innerResult (r : Fin 27 → Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B :=
  loopResult (r 26) (innerBodyStore r) n d

theorem innerLoop_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hn : d.reg (r 26) = n) (hd : ∀ j, d.reg j ≤ M) (hq : d.reg (r 4)+n ≤ M) :
    ∃ t, t ≤ n*(2400*(M+1)^4+2)+1 ∧
      (innerLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 338)) t
        ((innerResult r n d).toCfg (TapeProgram.loopExit 338)) ∧
      (∀ j, (innerResult r n d).reg j ≤ M) := by
  let Inv : ℕ → TapeStore R B → Prop := fun n c => (∀ j, c.reg j ≤ M) ∧ c.reg (r 4)+n ≤ M
  have hc (c : TapeStore R B) : (innerBodyStore r c).reg (r 26) = c.reg (r 26) :=
    innerBodyStore_fresh r hr c 26 (Or.inr (Or.inr (by decide)))
  have hb : ∀ n c, c.reg (r 26) = n+1 → Inv (n+1) c →
      ∃ t e, t ≤ 2400*(M+1)^4 ∧
        (innerBody r).Stops inp ((c.setReg (r 26) n).toCfg (innerBody (B := B) r).entry) t e ∧
        e.store = innerBodyStore r (c.setReg (r 26) n) ∧ Inv n e.store := by
    intro n c hcn hi
    have hcb := setReg_bound c (r 26) n M hi.1 (by have := hi.1 (r 26); omega)
    have hcq : (c.setReg (r 26) n).reg (r 4)+1 ≤ M := by
      simp [reg_set27 r hr]
      exact (by have := hi.2; omega)
    obtain ⟨t, e, ht, he, hs⟩ := innerBody_stops r hr inp M hM _ hcb
    refine ⟨t, e, ht, he, hs, ?_⟩
    rw [hs]
    refine ⟨innerBodyStore_bound r hr M hM _ hcb hcq, ?_⟩
    rw [innerBodyStore_quotient r hr]
    simp only [reg_set27 r hr, show (4:Fin 27) ≠ 26 from by decide, ite_false]
    have := hi.2
    omega
  obtain ⟨t, ht, he, hi⟩ := loop_stops (innerBody r) (r 26) (innerBodyStore r) inp
    (2400*(M+1)^4) Inv hc hb n d hn ⟨hd,hq⟩
  exact ⟨t, ht, he, hi.1⟩

theorem innerResult_frame (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) (i : Fin 27) (hi : i < 4 ∨ i = 19 ∨ 23 ≤ i)
    (hne : i ≠ 26) : (innerResult r n d).reg (r i) = d.reg (r i) :=
  loopResult_frame (r 26) (innerBodyStore r) (r i) (hr.ne hne)
    (fun c => innerBodyStore_fresh r hr c i hi) n d

theorem innerResult_quotient (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) : (innerResult r n d).reg (r 4) = d.reg (r 4)+n :=
  loopResult_index (r 26) (innerBodyStore r) (r 4) (hr.ne (by decide))
    (innerBodyStore_quotient r hr) n d

theorem innerResult_tapeData (r : Fin 27 → Fin R) (n : ℕ) (d : TapeStore R B) :
    tapeData (innerResult r n d) = tapeData d :=
  loopResult_tapeData (r 26) (innerBodyStore r) (innerBodyStore_tapeData r) n d

theorem innerResult_bound (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hq : d.reg (r 4)+n ≤ M) : ∀ j, (innerResult r n d).reg j ≤ M := by
  induction n generalizing d with
  | zero => exact hd
  | succ n ih =>
    change ∀ j, (innerResult r n (innerBodyStore r (d.setReg (r 26) n))).reg j ≤ M
    have hb := setReg_bound d (r 26) n M hd (by omega)
    apply ih _ (innerBodyStore_bound r hr M hM _ hb (by simp [reg_set27 r hr]; omega))
    rw [innerBodyStore_quotient r hr]
    simp only [reg_set27 r hr, show (4:Fin 27) ≠ 26 from by decide, ite_false]
    omega

def innerPrepare (r : Fin 27 → Fin R) : TapeProgram R B 13 :=
  TapeProgram.seq (TapeMacros.clear (r 4)) (TapeMacros.copy (r 24) (r 26) (r 21))
def innerPrepareStore (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := d.setReg (r 4) 0
  (c.setReg (r 26) (c.reg (r 24))).setReg (r 21) 0

theorem innerPrepare_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (innerPrepare r).Stops inp (d.toCfg (innerPrepare (B := B) r).entry)
      (d.reg (r 4)+d.reg (r 26)+d.reg (r 21)+5*d.reg (r 24)+9) e ∧
      e.store = innerPrepareStore r d := by
  have hclear := TapeMacros.clear_stops (r 4) inp (d.reg (r 4)) d rfl
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops (r 24) (r 26) (r 21)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp (d.setReg (r 4) 0)
  have hall := hclear.seq hc
  refine ⟨c.mapPC (TapeProgram.rightLabel 2), ?_, hcs⟩
  convert hall using 1 <;> first | rfl | (simp [reg_set27 r hr]; omega)

theorem innerPrepareStore_reg (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) :
    (innerPrepareStore r d).reg (r i) =
      if i = 21 then 0 else if i = 26 then d.reg (r 24) else if i = 4 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [innerPrepareStore, reg_set27 r hr]

theorem innerPrepareStore_bound (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (innerPrepareStore r d).reg j ≤ M := by
  unfold innerPrepareStore
  apply setReg_bound _ _ 0 M _ (by omega)
  apply setReg_bound _ _ _ M
  · exact setReg_bound d _ 0 M hd (by omega)
  · simpa [reg_set27 r hr] using hd (r 24)

def outerBody (r : Fin 27 → Fin R) : TapeProgram R B 355 :=
  TapeProgram.seq (TapeProgram.seq (innerPrepare r) (innerLoop r)) (TapeMacros.increment (r 2))
def outerBodyStore (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := innerResult r (d.reg (r 24)) (innerPrepareStore r d)
  c.setReg (r 2) (c.reg (r 2)+1)

theorem outerBodyStore_remainder (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (outerBodyStore r d).reg (r 2) = d.reg (r 2)+1 := by
  unfold outerBodyStore
  simp only [TapeStore.setReg, Function.update_self]
  rw [innerResult_frame r hr _ _ 2 (Or.inl (by decide)) (by decide), innerPrepareStore_reg r hr]
  simp

theorem outerBodyStore_fresh (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) (hi : i < 2 ∨ i = 3 ∨ i = 19 ∨ 23 ≤ i)
    (hne : i ≠ 26) : (outerBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold outerBodyStore
  simp only [reg_set27 r hr, show i ≠ (2:Fin 27) from by rcases hi with h|h|h|h <;> omega, ite_false]
  rw [innerResult_frame r hr _ _ i (by
    rcases hi with h|h|h|h
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)) hne, innerPrepareStore_reg r hr]
  have h21 : i ≠ (21:Fin 27) := by rcases hi with h|h|h|h <;> omega
  have h4 : i ≠ (4:Fin 27) := by rcases hi with h|h|h|h <;> omega
  simp [h21, hne, h4]

theorem outerBodyStore_tapeData (r : Fin 27 → Fin R) (d : TapeStore R B) :
    tapeData (outerBodyStore r d) = tapeData d := by
  rw [outerBodyStore, tapeData_setReg, innerResult_tapeData]
  rfl

theorem outerBodyStore_bound (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hrem : d.reg (r 2)+1 ≤ M) : ∀ j, (outerBodyStore r d).reg j ≤ M := by
  have hb := innerResult_bound r hr M hM (d.reg (r 24)) (innerPrepareStore r d)
    (innerPrepareStore_bound r hr M d hd) (by simpa [innerPrepareStore_reg r hr] using hd (r 24))
  apply setReg_bound _ _ _ M hb
  have he := outerBodyStore_remainder r hr d
  have he' : (innerResult r (d.reg (r 24)) (innerPrepareStore r d)).reg (r 2)+1 = d.reg (r 2)+1 := by
    simpa only [outerBodyStore, TapeStore.setReg, Function.update_self] using he
  rw [he']; exact hrem

theorem outerBody_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 2500*(M+1)^5 ∧
      (outerBody r).Stops inp (d.toCfg (outerBody (B := B) r).entry) t e ∧
      e.store = outerBodyStore r d := by
  obtain ⟨c₁, h₁, hs₁⟩ := innerPrepare_stops r hr inp d
  have hb₁ : ∀ j, c₁.store.reg j ≤ M := by rw [hs₁]; exact innerPrepareStore_bound r hr M d hd
  have hn : c₁.reg (r 26) = d.reg (r 24) := by
    change c₁.store.reg (r 26) = _
    rw [hs₁, innerPrepareStore_reg r hr]; simp
  have hq : c₁.reg (r 4) = 0 := by
    change c₁.store.reg (r 4) = _
    rw [hs₁, innerPrepareStore_reg r hr]; simp
  obtain ⟨t, ht, h₂, _⟩ := innerLoop_stops r hr inp M hM (d.reg (r 24)) c₁.store hn hb₁
    (by change c₁.reg (r 4)+d.reg (r 24) ≤ M; rw [hq]; simpa using hd (r 24))
  have h₃ := TapeMacros.increment_stops (r 2) inp (innerResult r (d.reg (r 24)) c₁.store)
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_, _, ?_, hall, ?_⟩
  · have hp : d.reg (r 4)+d.reg (r 26)+d.reg (r 21)+5*d.reg (r 24)+9 ≤ 8*M+9 := by
      have := hd (r 4); have := hd (r 26); have := hd (r 21); have := hd (r 24); omega
    have hpow := Nat.le_self_pow (by decide : (5:ℕ) ≠ 0) (M+1)
    have hM5 : M ≤ (M+1)^5 := (by omega : M ≤ M+1).trans hpow
    have h15 : 1 ≤ (M+1)^5 := by omega
    have hmul : 2400*M*(M+1)^4 ≤ 2400*(M+1)^5 := by
      calc
        2400*M*(M+1)^4 ≤ 2400*(M+1)*(M+1)^4 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2400 (by omega : M ≤ M+1))
        _ = 2400*(M+1)^5 := by ring
    have ht' := Nat.mul_le_mul_right (2400*(M+1)^4+2) (hd (r 24))
    have heq : M*(2400*(M+1)^4+2) = 2400*M*(M+1)^4+2*M := by ring
    rw [heq] at ht'
    omega
  · change (innerResult r (d.reg (r 24)) c₁.store).setReg (r 2) _ = _
    rw [hs₁]
    rfl

def outerLoop (r : Fin 27 → Fin R) : TapeProgram R B 357 :=
  TapeProgram.countedLoop (outerBody r) (r 25)
def outerResult (r : Fin 27 → Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B :=
  loopResult (r 25) (outerBodyStore r) n d

theorem outerLoop_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hn : d.reg (r 25) = n) (hd : ∀ j, d.reg j ≤ M) (hrem : d.reg (r 2)+n ≤ M) :
    ∃ t, t ≤ n*(2500*(M+1)^5+2)+1 ∧
      (outerLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 355)) t
        ((outerResult r n d).toCfg (TapeProgram.loopExit 355)) ∧
      (∀ j, (outerResult r n d).reg j ≤ M) := by
  let Inv : ℕ → TapeStore R B → Prop := fun n c => (∀ j, c.reg j ≤ M) ∧ c.reg (r 2)+n ≤ M
  have hc (c : TapeStore R B) : (outerBodyStore r c).reg (r 25) = c.reg (r 25) :=
    outerBodyStore_fresh r hr c 25 (Or.inr (Or.inr (Or.inr (by decide)))) (by decide)
  have hb : ∀ n c, c.reg (r 25) = n+1 → Inv (n+1) c →
      ∃ t e, t ≤ 2500*(M+1)^5 ∧
        (outerBody r).Stops inp ((c.setReg (r 25) n).toCfg (outerBody (B := B) r).entry) t e ∧
        e.store = outerBodyStore r (c.setReg (r 25) n) ∧ Inv n e.store := by
    intro n c hcn hi
    have hcb := setReg_bound c (r 25) n M hi.1 (by have := hi.1 (r 25); omega)
    have hcr : (c.setReg (r 25) n).reg (r 2)+1 ≤ M := by simp [reg_set27 r hr]; have := hi.2; omega
    obtain ⟨t, e, ht, he, hs⟩ := outerBody_stops r hr inp M hM _ hcb
    refine ⟨t, e, ht, he, hs, ?_⟩
    rw [hs]
    refine ⟨outerBodyStore_bound r hr M hM _ hcb hcr, ?_⟩
    rw [outerBodyStore_remainder r hr]
    simp only [reg_set27 r hr, show (2:Fin 27) ≠ 25 from by decide, ite_false]
    have := hi.2
    omega
  obtain ⟨t, ht, he, hi⟩ := loop_stops (outerBody r) (r 25) (outerBodyStore r) inp
    (2500*(M+1)^5) Inv hc hb n d hn ⟨hd,hrem⟩
  exact ⟨t, ht, he, hi.1⟩

theorem outerResult_frame (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) (i : Fin 27) (hi : i < 2 ∨ i = 3 ∨ i = 19 ∨ 23 ≤ i)
    (h25 : i ≠ 25) (h26 : i ≠ 26) : (outerResult r n d).reg (r i) = d.reg (r i) :=
  loopResult_frame (r 25) (outerBodyStore r) (r i) (hr.ne h25)
    (fun c => outerBodyStore_fresh r hr c i hi h26) n d

theorem outerResult_remainder (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) : (outerResult r n d).reg (r 2) = d.reg (r 2)+n :=
  loopResult_index (r 25) (outerBodyStore r) (r 2) (hr.ne (by decide))
    (outerBodyStore_remainder r hr) n d

theorem outerResult_tapeData (r : Fin 27 → Fin R) (n : ℕ) (d : TapeStore R B) :
    tapeData (outerResult r n d) = tapeData d :=
  loopResult_tapeData (r 25) (outerBodyStore r) (outerBodyStore_tapeData r) n d

def multiplyPrepare (r : Fin 27 → Fin R) : TapeProgram R B 17 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeMacros.clear (r 20))
    (TapeMacros.clear (r 22))) (TapeMacros.clear (r 2))) (TapeMacros.copy (r 23) (r 25) (r 21))
def multiplyPrepareStore (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := ((d.setReg (r 20) 0).setReg (r 22) 0).setReg (r 2) 0
  (c.setReg (r 25) (c.reg (r 23))).setReg (r 21) 0

theorem multiplyPrepare_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (multiplyPrepare r).Stops inp (d.toCfg (multiplyPrepare (B := B) r).entry)
      (d.reg (r 20)+d.reg (r 22)+d.reg (r 2)+d.reg (r 25)+d.reg (r 21)+5*d.reg (r 23)+13) e ∧
      e.store = multiplyPrepareStore r d := by
  have h₁ := TapeMacros.clear_stops (r 20) inp (d.reg (r 20)) d rfl
  have h₂ := TapeMacros.clear_stops (r 22) inp (d.reg (r 22)) (d.setReg (r 20) 0)
    (by simp [reg_set27 r hr])
  have h₃ := TapeMacros.clear_stops (r 2) inp (d.reg (r 2)) ((d.setReg (r 20) 0).setReg (r 22) 0)
    (by simp [reg_set27 r hr])
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops (r 23) (r 25) (r 21)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp
    (((d.setReg (r 20) 0).setReg (r 22) 0).setReg (r 2) 0)
  have hall := ((h₁.seq h₂).seq h₃).seq hc
  refine ⟨c.mapPC (TapeProgram.rightLabel 6), ?_, hcs⟩
  convert hall using 1 <;> first | rfl | (simp [reg_set27 r hr]; omega)

theorem multiplyPrepareStore_reg (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) :
    (multiplyPrepareStore r d).reg (r i) =
      if i = 21 then 0 else if i = 25 then d.reg (r 23)
      else if i = 20 ∨ i = 22 ∨ i = 2 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [multiplyPrepareStore, reg_set27 r hr]

theorem multiplyPrepareStore_bound (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (multiplyPrepareStore r d).reg j ≤ M := by
  unfold multiplyPrepareStore
  apply setReg_bound _ _ 0 M _ (by omega)
  apply setReg_bound _ _ _ M
  · exact setReg_bound _ _ 0 M (setReg_bound _ _ 0 M (setReg_bound d _ 0 M hd (by omega)) (by omega)) (by omega)
  · simpa [reg_set27 r hr] using hd (r 23)

/-- Uniform actual finite multiplication search: every runtime remainder below
q is paired with every runtime quotient below q². No code depends on q or ell. -/
def multiply (r : Fin 27 → Fin R) : TapeProgram R B 374 :=
  TapeProgram.seq (multiplyPrepare r) (outerLoop r)

def multiplyResult (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  outerResult r (d.reg (r 23)) (multiplyPrepareStore r d)

theorem multiply_stops_exact (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 10000*(M+1)^6 ∧
      (multiply r).Stops inp (d.toCfg (multiply (B := B) r).entry) t e ∧
      e.store = multiplyResult r d ∧ (∀ j, e.reg j ≤ M) := by
  obtain ⟨c, hc, hcs⟩ := multiplyPrepare_stops r hr inp d
  have hcb : ∀ j, c.store.reg j ≤ M := by rw [hcs]; exact multiplyPrepareStore_bound r hr M d hd
  have hcn : c.reg (r 25) = d.reg (r 23) := by
    change c.store.reg (r 25) = _
    rw [hcs, multiplyPrepareStore_reg r hr]; simp
  have hcr : c.reg (r 2) = 0 := by
    change c.store.reg (r 2) = _
    rw [hcs, multiplyPrepareStore_reg r hr]; simp
  obtain ⟨t, ht, he, heb⟩ := outerLoop_stops r hr inp M hM (d.reg (r 23)) c.store hcn hcb
    (by change c.reg (r 2)+d.reg (r 23) ≤ M; rw [hcr]; simpa using hd (r 23))
  have hall := hc.seq he
  refine ⟨_, _, ?_, hall, ?_, heb⟩
  · have hp : d.reg (r 20)+d.reg (r 22)+d.reg (r 2)+d.reg (r 25)+d.reg (r 21)+5*d.reg (r 23)+13 ≤ 10*M+13 := by
      have := hd (r 20); have := hd (r 22); have := hd (r 2); have := hd (r 25)
      have := hd (r 21); have := hd (r 23); omega
    have hpow := Nat.le_self_pow (by decide : (6:ℕ) ≠ 0) (M+1)
    have hM6 : M ≤ (M+1)^6 := (by omega : M ≤ M+1).trans hpow
    have h16 : 1 ≤ (M+1)^6 := by omega
    have hmul : 2500*M*(M+1)^5 ≤ 2500*(M+1)^6 := by
      calc
        2500*M*(M+1)^5 ≤ 2500*(M+1)*(M+1)^5 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2500 (by omega : M ≤ M+1))
        _ = 2500*(M+1)^6 := by ring
    have ht' := Nat.mul_le_mul_right (2500*(M+1)^5+2) (hd (r 23))
    have heq : M*(2500*(M+1)^5+2) = 2500*M*(M+1)^5+2*M := by ring
    rw [heq] at ht'
    change d.reg (r 20)+d.reg (r 22)+d.reg (r 2)+d.reg (r 25)+d.reg (r 21)+5*d.reg (r 23)+13+1+t ≤ _
    omega
  · change outerResult r (d.reg (r 23)) c.store = _
    rw [hcs]
    rfl

theorem multiplyResult_tapeData (r : Fin 27 → Fin R) (d : TapeStore R B) :
    tapeData (multiplyResult r d) = tapeData d := by
  rw [multiplyResult, outerResult_tapeData]
  rfl

/-- Projection used only to prove the source search's semantics. -/
def environment (r : Fin 27 → Fin R) (d : TapeStore R B) : Fin 4 → ℕ :=
  ![d.reg (r 0),d.reg (r 1),d.reg (r 3),d.reg (r 19)]
def accept (env : Fin 4 → ℕ) (rem quotient : ℕ) : Bool :=
  decide (∀ j : Fin (env 3), CoefficientMatches (env 0) (env 1) rem (env 2) quotient j.val)
def answer (r : Fin 27 → Fin R) (d : TapeStore R B) : Option ℕ :=
  if d.reg (r 22) = 0 then none else some (d.reg (r 20))

theorem accept_iff (env : Fin 4 → ℕ) (rem quotient : ℕ) :
    accept env rem quotient = true ↔
      ∀ j < env 3, CoefficientMatches (env 0) (env 1) rem (env 2) quotient j := by
  simp only [accept, decide_eq_true_eq]
  constructor
  · intro h j hj
    exact h ⟨j,hj⟩
  · intro h j
    exact h j.val j.isLt

theorem environment_setReg (r : Fin 27 → Fin R) (d : TapeStore R B) (j : Fin R) (n : ℕ)
    (h₀ : r 0 ≠ j) (h₁ : r 1 ≠ j) (h₃ : r 3 ≠ j) (h₁₉ : r 19 ≠ j) :
    environment r (d.setReg j n) = environment r d := by
  funext i
  fin_cases i <;> simp [environment, TapeStore.setReg, h₀, h₁, h₃, h₁₉]

theorem answer_setReg (r : Fin 27 → Fin R) (d : TapeStore R B) (j : Fin R) (n : ℕ)
    (h₂₀ : r 20 ≠ j) (h₂₂ : r 22 ≠ j) : answer r (d.setReg j n) = answer r d := by
  simp [answer, TapeStore.setReg, h₂₀, h₂₂]

theorem innerBodyStore_environment (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    environment r (innerBodyStore r d) = environment r d := by
  funext i
  fin_cases i
  · exact innerBodyStore_fresh r hr d 0 (Or.inl (by decide))
  · exact innerBodyStore_fresh r hr d 1 (Or.inl (by decide))
  · exact innerBodyStore_fresh r hr d 3 (Or.inl (by decide))
  · exact innerBodyStore_fresh r hr d 19 (Or.inr (Or.inl rfl))

theorem innerBodyStore_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    answer r (innerBodyStore r d) =
      if accept (environment r d) (d.reg (r 2)) (d.reg (r 4)) then some (d.reg (r 2)) else answer r d := by
  let c := certificateResult (certificateLayout r) d
  have hbit : c.reg (r 6) ≤ 1 := certificateResult_flag_le _ (certificateLayout_injective r hr) d
  have hc : c.reg (r 6) = 1 ↔ accept (environment r d) (d.reg (r 2)) (d.reg (r 4)) = true := by
    rw [accept_iff]
    exact certificateResult_correct _ (certificateLayout_injective r hr) d
  have h20 : c.reg (r 20) = d.reg (r 20) := certificate_preserves r hr d 20 (Or.inr (Or.inr (by decide)))
  have h22 : c.reg (r 22) = d.reg (r 22) := certificate_preserves r hr d 22 (Or.inr (Or.inr (by decide)))
  have h2 : c.reg (r 2) = d.reg (r 2) := certificate_preserves r hr d 2 (Or.inl (by decide))
  change answer r ((commitStore (commitLayout r) c).setReg (r 4) _) = _
  rw [answer_setReg r _ _ _ (hr.ne (by decide)) (hr.ne (by decide))]
  by_cases hf : c.reg (r 6) = 0
  · have hac : accept (environment r d) (d.reg (r 2)) (d.reg (r 4)) ≠ true := by
      intro h
      have := hc.mpr h
      omega
    simp [answer, commitStore, commitLayout, hf, hac, h20, h22]
  · have hf1 : c.reg (r 6) = 1 := by omega
    have hac := hc.mp hf1
    simp [answer, commitStore, commitBodyStore, commitLayout, hf, hac, reg_set27 r hr, h2]

/-- A mathematical scan model used only after the actual source execution has
been proved. Each Boolean test is refined by the319-label source certificate. -/
def scanRow (test : ℕ → ℕ → Bool) (rem : ℕ) : ℕ → ℕ → Option ℕ → Option ℕ
  | 0, _, state => state
  | n+1, s, state => scanRow test rem n (s+1) (if test rem s then some rem else state)
def scanRect (test : ℕ → ℕ → Bool) (Q : ℕ) : ℕ → ℕ → Option ℕ → Option ℕ
  | 0, _, state => state
  | n+1, r, state => scanRect test Q n (r+1) (scanRow test r Q 0 state)

theorem innerResult_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (n : ℕ) (d : TapeStore R B) :
    answer r (innerResult r n d) =
      scanRow (accept (environment r d)) (d.reg (r 2)) n (d.reg (r 4)) (answer r d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    let c := d.setReg (r 26) n
    have henv : environment r c = environment r d :=
      environment_setReg r d _ n (hr.ne (by decide)) (hr.ne (by decide))
        (hr.ne (by decide)) (hr.ne (by decide))
    have h2 : c.reg (r 2) = d.reg (r 2) := by simp [c, reg_set27 r hr]
    have h4 : c.reg (r 4) = d.reg (r 4) := by simp [c, reg_set27 r hr]
    have ha : answer r c = answer r d := answer_setReg r d _ n (hr.ne (by decide)) (hr.ne (by decide))
    change answer r (innerResult r n (innerBodyStore r c)) = _
    rw [ih, innerBodyStore_environment r hr c, henv,
      innerBodyStore_fresh r hr c 2 (Or.inl (by decide)), h2, innerBodyStore_quotient r hr c,
      h4, innerBodyStore_answer r hr c, henv, h2, h4, ha]
    rfl

theorem outerBodyStore_environment (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    environment r (outerBodyStore r d) = environment r d := by
  funext i
  fin_cases i
  · exact outerBodyStore_fresh r hr d 0 (Or.inl (by decide)) (by decide)
  · exact outerBodyStore_fresh r hr d 1 (Or.inl (by decide)) (by decide)
  · exact outerBodyStore_fresh r hr d 3 (Or.inr (Or.inl rfl)) (by decide)
  · exact outerBodyStore_fresh r hr d 19 (Or.inr (Or.inr (Or.inl rfl))) (by decide)

theorem outerBodyStore_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    answer r (outerBodyStore r d) =
      scanRow (accept (environment r d)) (d.reg (r 2)) (d.reg (r 24)) 0 (answer r d) := by
  have henv : environment r (innerPrepareStore r d) = environment r d := by
    funext i
    fin_cases i <;> simp [environment, innerPrepareStore_reg r hr]
  have ha : answer r (innerPrepareStore r d) = answer r d := by
    simp [answer, innerPrepareStore_reg r hr]
  unfold outerBodyStore
  rw [answer_setReg r _ _ _ (hr.ne (by decide)) (hr.ne (by decide)), innerResult_answer r hr,
    henv, ha, innerPrepareStore_reg r hr, innerPrepareStore_reg r hr]
  simp

theorem outerResult_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (n : ℕ) (d : TapeStore R B) :
    answer r (outerResult r n d) =
      scanRect (accept (environment r d)) (d.reg (r 24)) n (d.reg (r 2)) (answer r d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    let c := d.setReg (r 25) n
    have henv : environment r c = environment r d :=
      environment_setReg r d _ n (hr.ne (by decide)) (hr.ne (by decide))
        (hr.ne (by decide)) (hr.ne (by decide))
    have h2 : c.reg (r 2) = d.reg (r 2) := by simp [c, reg_set27 r hr]
    have h24 : c.reg (r 24) = d.reg (r 24) := by simp [c, reg_set27 r hr]
    have ha : answer r c = answer r d := answer_setReg r d _ n (hr.ne (by decide)) (hr.ne (by decide))
    change answer r (outerResult r n (outerBodyStore r c)) = _
    rw [ih, outerBodyStore_environment r hr c, henv,
      outerBodyStore_fresh r hr c 24 (Or.inr (Or.inr (Or.inr (by decide)))) (by decide), h24,
      outerBodyStore_remainder r hr c, h2, outerBodyStore_answer r hr c, henv, h2, h24, ha]
    rfl

theorem multiplyResult_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    answer r (multiplyResult r d) =
      scanRect (accept (environment r d)) (d.reg (r 24)) (d.reg (r 23)) 0 none := by
  have henv : environment r (multiplyPrepareStore r d) = environment r d := by
    funext i
    fin_cases i <;> simp [environment, multiplyPrepareStore_reg r hr]
  rw [multiplyResult, outerResult_answer r hr, henv, multiplyPrepareStore_reg r hr, multiplyPrepareStore_reg r hr]
  simp [answer, multiplyPrepareStore_reg r hr]

def Correct (target : ℕ) (state : Option ℕ) : Prop := ∀ v, state = some v → v = target

theorem scanRow_same (test : ℕ → ℕ → Bool) (rem n s : ℕ) :
    scanRow test rem n s (some rem) = some rem := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [scanRow]
    split <;> exact ih _

theorem scanRow_hit (test : ℕ → ℕ → Bool) (rem n s : ℕ) (state : Option ℕ)
    (hit : ∃ i < n, test rem (s+i) = true) : scanRow test rem n s state = some rem := by
  induction n generalizing s state with
  | zero => rcases hit with ⟨i,hi,_⟩; omega
  | succ n ih =>
    rcases hit with ⟨i,hi,hp⟩
    by_cases hz : i = 0
    · subst i
      have hc : test rem s = true := by simpa using hp
      rw [scanRow, if_pos hc]
      exact scanRow_same test rem n (s+1)
    · rw [scanRow]
      apply ih
      refine ⟨i-1, by omega, ?_⟩
      have he : s+1+(i-1) = s+i := by omega
      rw [he]; exact hp

theorem scanRow_nonempty (test : ℕ → ℕ → Bool) (rem n s : ℕ) (state : Option ℕ)
    (hs : state ≠ none) : scanRow test rem n s state ≠ none := by
  induction n generalizing s state with
  | zero => exact hs
  | succ n ih =>
    rw [scanRow]
    apply ih
    split <;> simp_all

theorem scanRow_correct (test : ℕ → ℕ → Bool) (rem n s target : ℕ) (state : Option ℕ)
    (hs : Correct target state) (hg : ∀ i < n, test rem (s+i) = true → rem = target) :
    Correct target (scanRow test rem n s state) := by
  induction n generalizing s state with
  | zero => exact hs
  | succ n ih =>
    rw [scanRow]
    apply ih
    · split
      · have he : rem = target := hg 0 (by omega) (by simpa using ‹test rem s = true›)
        simpa [Correct] using he
      · exact hs
    · intro i hi ht
      apply hg (i+1) (by omega)
      have he : s+(i+1) = s+1+i := by omega
      rw [he]; exact ht

theorem scanRect_nonempty (test : ℕ → ℕ → Bool) (Q n r : ℕ) (state : Option ℕ)
    (hs : state ≠ none) : scanRect test Q n r state ≠ none := by
  induction n generalizing r state with
  | zero => exact hs
  | succ n ih =>
    rw [scanRect]
    exact ih _ _ (scanRow_nonempty test r Q 0 state hs)

theorem scanRect_hit (test : ℕ → ℕ → Bool) (Q n r : ℕ) (state : Option ℕ)
    (hit : ∃ i < n, ∃ s < Q, test (r+i) s = true) : scanRect test Q n r state ≠ none := by
  induction n generalizing r state with
  | zero => rcases hit with ⟨i,hi,_⟩; omega
  | succ n ih =>
    rcases hit with ⟨i,hi,s,hs,hp⟩
    rw [scanRect]
    by_cases hz : i = 0
    · subst i
      have hrow := scanRow_hit test r Q 0 state ⟨s,hs,by simpa using hp⟩
      apply scanRect_nonempty
      rw [hrow]
      simp
    · apply ih
      refine ⟨i-1,by omega,s,hs,?_⟩
      have he : r+1+(i-1) = r+i := by omega
      rw [he]; exact hp

theorem scanRect_correct (test : ℕ → ℕ → Bool) (Q n r target : ℕ) (state : Option ℕ)
    (hs : Correct target state)
    (hg : ∀ i < n, ∀ s < Q, test (r+i) s = true → r+i = target) :
    Correct target (scanRect test Q n r state) := by
  induction n generalizing r state with
  | zero => exact hs
  | succ n ih =>
    rw [scanRect]
    apply ih
    · apply scanRow_correct test r Q 0 target state hs
      intro s hs hp
      have h := hg 0 (by omega) s hs (by simpa using hp)
      simpa using h
    · intro i hi s hs hp
      have he : r+(i+1) = r+1+i := by omega
      have h := hg (i+1) (by omega) s hs (by simpa only [he] using hp)
      simpa only [he] using h

theorem scanRect_complete (test : ℕ → ℕ → Bool) (Q n target : ℕ)
    (hg : ∀ i < n, ∀ s < Q, test i s = true → i = target)
    (hit : ∃ i < n, ∃ s < Q, test i s = true) :
    scanRect test Q n 0 none = some target := by
  have hc := scanRect_correct test Q n 0 target none (by simp [Correct])
    (by simpa using hg)
  have hn := scanRect_hit test Q n 0 none (by simpa using hit)
  cases he : scanRect test Q n 0 none with
  | none => exact False.elim (hn he)
  | some v =>
    have hv : v = target := hc v he
    simpa only [hv] using he

/-- Semantic correctness of the actual374-label bounded source multiplication
search, for the exact BinaryField quotient/remainder index operations. -/
theorem multiplyResult_index (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (ell : ℕ) (h : 0 < ell) (m a b : Fin (2^ell)) (d : TapeStore R B)
    (ha : d.reg (r 0) = a.val) (hb : d.reg (r 1) = b.val)
    (hm : d.reg (r 3) = 2^ell+m.val) (hN : d.reg (r 19) = 3*ell+1)
    (hq : d.reg (r 23) = 2^ell) (hQ : d.reg (r 24) = 2^(2*ell)) :
    (multiplyResult r d).reg (r 20) =
      (BinaryField.multiplyIndex ell h m (indexEquiv ell a) (indexEquiv ell b)).val := by
  let test := accept (environment r d)
  let target := (BinaryField.multiplyIndex ell h m (indexEquiv ell a) (indexEquiv ell b)).val
  have htest (i : Fin (2^ell)) (s : Fin (2^(2*ell))) : test i.val s.val = true ↔
      BinaryField.DivMatches ell m (indexEquiv ell a) (indexEquiv ell b)
        (indexEquiv ell i) (indexEquiv (2*ell) s) := by
    rw [accept_iff]
    change (∀ j < d.reg (r 19), CoefficientMatches (d.reg (r 0)) (d.reg (r 1)) i.val
      (d.reg (r 3)) s.val j) ↔ _
    rw [ha,hb,hm,hN]
    exact coefficientMatches_all_iff ell m a b i s
  have hg : ∀ i < 2^ell, ∀ s < 2^(2*ell), test i s = true → i = target := by
    intro i hi s hs hp
    have hu := accepted_remainder_unique ell h m a b ⟨i,hi⟩ ⟨s,hs⟩ ((htest ⟨i,hi⟩ ⟨s,hs⟩).mp hp)
    exact congrArg Fin.val hu
  have hit : ∃ i < 2^ell, ∃ s < 2^(2*ell), test i s = true := by
    obtain ⟨i,s,hs⟩ := BinaryField.exists_divMatches ell h m (indexEquiv ell a) (indexEquiv ell b)
    exact ⟨i.val,i.isLt,s.val,s.isLt,(htest i s).mpr hs⟩
  have hanswer : answer r (multiplyResult r d) = some target := by
    rw [multiplyResult_answer r hr d,hq,hQ]
    exact scanRect_complete test _ _ target hg hit
  unfold answer at hanswer
  split at hanswer
  · contradiction
  · exact Option.some.inj hanswer

theorem multiplyResult_input (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) (hi : i < 2 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24) :
    (multiplyResult r d).reg (r i) = d.reg (r i) := by
  rw [multiplyResult, outerResult_frame r hr _ _ i (by
    rcases hi with h|h|h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega))))
    (by rcases hi with h|h|h|h|h <;> omega) (by rcases hi with h|h|h|h|h <;> omega),
    multiplyPrepareStore_reg r hr]
  have h21 : i ≠ (21:Fin 27) := by rcases hi with h|h|h|h|h <;> omega
  have h25 : i ≠ (25:Fin 27) := by rcases hi with h|h|h|h|h <;> omega
  have h20 : i ≠ (20:Fin 27) := by rcases hi with h|h|h|h|h <;> omega
  have h22 : i ≠ (22:Fin 27) := by rcases hi with h|h|h|h|h <;> omega
  have h2 : i ≠ (2:Fin 27) := by rcases hi with h|h|h|h|h <;> omega
  simp [h21,h25,h20,h22,h2]

theorem innerBodyStore_outside (r : Fin 27 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 27, j ≠ r i) :
    (innerBodyStore r d).reg j = d.reg j := by
  unfold innerBodyStore
  simp only [TapeStore.setReg, Function.update_of_ne (hne 4)]
  rw [commitStore_fresh _ _ _ (hne 20) (hne 21) (hne 22) (hne 6)]
  apply certificateResult_outside
  intro i
  exact hne ⟨i.val,by have := i.isLt; omega⟩

theorem innerResult_outside (r : Fin 27 → Fin R) (n : ℕ) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 27, j ≠ r i) :
    (innerResult r n d).reg j = d.reg j :=
  loopResult_frame (r 26) (innerBodyStore r) j (hne 26)
    (fun c => innerBodyStore_outside r c j hne) n d

theorem outerBodyStore_outside (r : Fin 27 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 27, j ≠ r i) :
    (outerBodyStore r d).reg j = d.reg j := by
  unfold outerBodyStore
  simp only [TapeStore.setReg, Function.update_of_ne (hne 2)]
  rw [innerResult_outside r _ _ j hne]
  simp [innerPrepareStore, TapeStore.setReg, hne 4,hne 21,hne 26]

theorem outerResult_outside (r : Fin 27 → Fin R) (n : ℕ) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 27, j ≠ r i) :
    (outerResult r n d).reg j = d.reg j :=
  loopResult_frame (r 25) (outerBodyStore r) j (hne 25)
    (fun c => outerBodyStore_outside r c j hne) n d

theorem multiplyResult_outside (r : Fin 27 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 27, j ≠ r i) :
    (multiplyResult r d).reg j = d.reg j := by
  rw [multiplyResult, outerResult_outside r _ _ j hne]
  simp [multiplyPrepareStore, TapeStore.setReg, hne 2,hne 20,hne 21,hne 22,hne 25]

/-- Complete physical-source multiplication contract. Inputs, all caller
registers outside the static layout, read-only heads/output and buffers are
preserved. The executable result is exactly BinaryField.multiplyIndex. -/
theorem multiply_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (h : 0 < ell) (m a b : Fin (2^ell))
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (ha : d.reg (r 0) = a.val) (hb : d.reg (r 1) = b.val)
    (hm : d.reg (r 3) = 2^ell+m.val) (hN : d.reg (r 19) = 3*ell+1)
    (hq : d.reg (r 23) = 2^ell) (hQ : d.reg (r 24) = 2^(2*ell)) :
    ∃ t e, t ≤ 10000*(M+1)^6 ∧
      (multiply r).Stops inp (d.toCfg (multiply (B := B) r).entry) t e ∧
      e.store = multiplyResult r d ∧
      e.reg (r 20) = (BinaryField.multiplyIndex ell h m (indexEquiv ell a) (indexEquiv ell b)).val ∧
      (∀ i, i < 2 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j, (∀ i, j ≠ r i) → e.reg j = d.reg j) ∧
      (∀ j, e.reg j ≤ M) ∧ tapeData e.store = tapeData d := by
  obtain ⟨t,e,ht,he,hstore,hbound⟩ := multiply_stops_exact r hr inp M hM d hd
  refine ⟨t,e,ht,he,hstore,?_,?_,?_,hbound,?_⟩
  · change e.store.reg (r 20) = _
    rw [hstore]
    exact multiplyResult_index r hr ell h m a b d ha hb hm hN hq hQ
  · intro i hi
    change e.store.reg (r i) = _
    rw [hstore]; exact multiplyResult_input r hr d i hi
  · intro j hj
    change e.store.reg j = _
    rw [hstore]; exact multiplyResult_outside r d j hj
  · rw [hstore]; exact multiplyResult_tapeData r d

/-- Initialize one unary register to one by actual clear/increment code. -/
def setOne (x : Fin R) : TapeProgram R B 4 := TapeProgram.seq (TapeMacros.clear x) (TapeMacros.increment x)
theorem setOne_stops (x : Fin R) (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (setOne x).Stops inp (d.toCfg (setOne (B := B) x).entry) (d.reg x+3) e ∧ e.store = d.setReg x 1 := by
  have hc := TapeMacros.clear_stops x inp (d.reg x) d rfl
  have hi := TapeMacros.increment_stops x inp (d.setReg x 0)
  have hz : (d.setReg x 0).reg x = 0 := by simp [TapeStore.setReg]
  rw [hz,zero_add] at hi
  have hall := hc.seq hi
  refine ⟨((d.setReg x 0).setReg x 1).toCfg (1:Fin 2) |>.mapPC (TapeProgram.rightLabel 2),?_,?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · exact TapeStore.setReg_same d x 0 1

/-- Addition checks `a*1 = r+b*1` using the same actual coefficient certificate.
Only the candidate remainder is incremented after each check. -/
def additionBody (r : Fin 27 → Fin R) : TapeProgram R B 338 :=
  TapeProgram.seq (TapeProgram.seq (certificate (certificateLayout r)) (commit (commitLayout r)))
    (TapeMacros.increment (r 2))
def additionBodyStore (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := commitStore (commitLayout r) (certificateResult (certificateLayout r) d)
  c.setReg (r 2) (c.reg (r 2)+1)

theorem additionBodyStore_fresh (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) (hi : i < 5 ∨ i = 19 ∨ 23 ≤ i) (h2 : i ≠ 2) :
    (additionBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold additionBodyStore
  simp only [reg_set27 r hr,if_neg h2]
  rw [commitStore_fresh _ _ _
    (hr.ne (show i ≠ (20:Fin 27) from by rcases hi with h|h|h <;> omega))
    (hr.ne (show i ≠ (21:Fin 27) from by rcases hi with h|h|h <;> omega))
    (hr.ne (show i ≠ (22:Fin 27) from by rcases hi with h|h|h <;> omega))
    (hr.ne (show i ≠ (6:Fin 27) from by rcases hi with h|h|h <;> omega))]
  apply certificate_preserves r hr d i
  rcases hi with h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by omega))

theorem additionBodyStore_index (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (additionBodyStore r d).reg (r 2) = d.reg (r 2)+1 := by
  unfold additionBodyStore
  simp only [TapeStore.setReg,Function.update_self]
  rw [commitStore_fresh _ _ _
    (hr.ne (show (2:Fin 27) ≠ 20 from by decide)) (hr.ne (show (2:Fin 27) ≠ 21 from by decide))
    (hr.ne (show (2:Fin 27) ≠ 22 from by decide)) (hr.ne (show (2:Fin 27) ≠ 6 from by decide)),
    certificate_preserves r hr d 2 (Or.inl (by decide))]

theorem additionBodyStore_bound (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 2)+1 ≤ M) :
    ∀ j,(additionBodyStore r d).reg j ≤ M := by
  apply setReg_bound _ _ _ M (commitStore_bound _ (commitLayout_injective r hr) M hM _
    (certificateResult_bound _ (certificateLayout_injective r hr) M hM d hd))
  have he := additionBodyStore_index r hr d
  have he' : (commitStore (commitLayout r) (certificateResult (certificateLayout r) d)).reg (r 2)+1 = d.reg (r 2)+1 := by
    simpa only [additionBodyStore,TapeStore.setReg,Function.update_self] using he
  rw [he'];exact hc

theorem additionBody_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∃ t e,t ≤ 2400*(M+1)^4 ∧
      (additionBody r).Stops inp (d.toCfg (additionBody (B:=B) r).entry) t e ∧ e.store = additionBodyStore r d := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁⟩ := certificate_stops_exact (certificateLayout r) (certificateLayout_injective r hr) inp M hM d hd
  have hb₁ : ∀ j,c₁.store.reg j ≤ M := by rw [hs₁];exact certificateResult_bound _ (certificateLayout_injective r hr) M hM d hd
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂⟩ := commit_stops (commitLayout r) (commitLayout_injective r hr) inp M c₁.store hb₁
  have h₃ := TapeMacros.increment_stops (r 2) inp c₂.store
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_,_,?_,hall,?_⟩
  · have hpow := Nat.le_self_pow (by decide : (4:ℕ) ≠ 0) (M+1)
    omega
  · change c₂.store.setReg (r 2) _ = _
    rw [hs₂,hs₁];rfl

def additionLoop (r : Fin 27 → Fin R) : TapeProgram R B 340 := TapeProgram.countedLoop (additionBody r) (r 25)
def additionFold (r : Fin 27 → Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B := loopResult (r 25) (additionBodyStore r) n d

theorem additionLoop_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hn : d.reg (r 25) = n) (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 2)+n ≤ M) :
    ∃ t,t ≤ n*(2400*(M+1)^4+2)+1 ∧
      (additionLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 338)) t
        ((additionFold r n d).toCfg (TapeProgram.loopExit 338)) ∧ (∀ j,(additionFold r n d).reg j ≤ M) := by
  let Inv : ℕ → TapeStore R B → Prop := fun n c => (∀ j,c.reg j ≤ M) ∧ c.reg (r 2)+n ≤ M
  have hf (c : TapeStore R B) : (additionBodyStore r c).reg (r 25) = c.reg (r 25) :=
    additionBodyStore_fresh r hr c 25 (Or.inr (Or.inr (by decide))) (by decide)
  have hb : ∀ n c,c.reg (r 25) = n+1 → Inv (n+1) c → ∃ t e,t ≤ 2400*(M+1)^4 ∧
      (additionBody r).Stops inp ((c.setReg (r 25) n).toCfg (additionBody (B:=B) r).entry) t e ∧
      e.store = additionBodyStore r (c.setReg (r 25) n) ∧ Inv n e.store := by
    intro n c hcn hi
    have hcb := setReg_bound c (r 25) n M hi.1 (by have := hi.1 (r 25);omega)
    have hci : (c.setReg (r 25) n).reg (r 2)+1 ≤ M := by simp [reg_set27 r hr];have := hi.2;omega
    obtain ⟨t,e,ht,he,hs⟩ := additionBody_stops r hr inp M hM _ hcb
    refine ⟨t,e,ht,he,hs,?_⟩
    rw [hs]
    refine ⟨additionBodyStore_bound r hr M hM _ hcb hci,?_⟩
    rw [additionBodyStore_index r hr]
    simp only [reg_set27 r hr,show (2:Fin 27) ≠ 25 from by decide,ite_false]
    have := hi.2;omega
  obtain ⟨t,ht,he,hi⟩ := loop_stops (additionBody r) (r 25) (additionBodyStore r) inp (2400*(M+1)^4) Inv hf hb n d hn ⟨hd,hc⟩
  exact ⟨t,ht,he,hi.1⟩

def additionPrepare (r : Fin 27 → Fin R) : TapeProgram R B 25 :=
  TapeProgram.seq (TapeProgram.seq (multiplyPrepare r) (setOne (r 1))) (setOne (r 4))
def additionPrepareStore (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  ((multiplyPrepareStore r d).setReg (r 1) 1).setReg (r 4) 1

theorem additionPrepare_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∃ t e,t ≤ 12*M+21 ∧
      (additionPrepare r).Stops inp (d.toCfg (additionPrepare (B:=B) r).entry) t e ∧ e.store = additionPrepareStore r d := by
  obtain ⟨c₁,h₁,hs₁⟩ := multiplyPrepare_stops r hr inp d
  have hb₁ : ∀ j,c₁.store.reg j ≤ M := by rw [hs₁];exact multiplyPrepareStore_bound r hr M d hd
  obtain ⟨c₂,h₂,hs₂⟩ := setOne_stops (r 1) inp c₁.store
  have hb₂ : ∀ j,c₂.store.reg j ≤ M := by rw [hs₂];exact setReg_bound _ _ 1 M hb₁ hM
  obtain ⟨c₃,h₃,hs₃⟩ := setOne_stops (r 4) inp c₂.store
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_,_,?_,hall,?_⟩
  · have := hd (r 20);have := hd (r 22);have := hd (r 2);have := hd (r 25)
    have := hd (r 21);have := hd (r 23);have := hb₁ (r 1);have := hb₂ (r 4);omega
  · change c₃.store = _
    rw [hs₃,hs₂,hs₁];rfl

theorem additionPrepareStore_reg (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) : (additionPrepareStore r d).reg (r i) =
      if i = 1 ∨ i = 4 then 1 else if i = 21 then 0 else if i = 25 then d.reg (r 23)
      else if i = 20 ∨ i = 22 ∨ i = 2 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [additionPrepareStore,reg_set27 r hr,multiplyPrepareStore_reg r hr]

theorem additionPrepareStore_bound (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∀ j,(additionPrepareStore r d).reg j ≤ M :=
  setReg_bound _ _ 1 M (setReg_bound _ _ 1 M (multiplyPrepareStore_bound r hr M d hd) hM) hM

def addition (r : Fin 27 → Fin R) : TapeProgram R B 365 := TapeProgram.seq (additionPrepare r) (additionLoop r)
def additionResult (r : Fin 27 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  additionFold r (d.reg (r 23)) (additionPrepareStore r d)

theorem addition_stops_exact (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∃ t e,t ≤ 3000*(M+1)^5 ∧
      (addition r).Stops inp (d.toCfg (addition (B:=B) r).entry) t e ∧
      e.store = additionResult r d ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,c,ht₁,hc,hcs⟩ := additionPrepare_stops r hr inp M hM d hd
  have hcb : ∀ j,c.store.reg j ≤ M := by rw [hcs];exact additionPrepareStore_bound r hr M hM d hd
  have hcn : c.reg (r 25) = d.reg (r 23) := by change c.store.reg (r 25) = _;rw [hcs,additionPrepareStore_reg r hr];simp
  have hcc : c.reg (r 2) = 0 := by change c.store.reg (r 2) = _;rw [hcs,additionPrepareStore_reg r hr];simp
  obtain ⟨t₂,ht₂,h₂,hb₂⟩ := additionLoop_stops r hr inp M hM (d.reg (r 23)) c.store hcn hcb
    (by change c.reg (r 2)+d.reg (r 23) ≤ M;rw [hcc];simpa using hd (r 23))
  have hall := hc.seq h₂
  refine ⟨_,_,?_,hall,?_,hb₂⟩
  · have hpow := Nat.le_self_pow (by decide : (5:ℕ) ≠ 0) (M+1)
    have hM5 : M ≤ (M+1)^5 := (by omega : M ≤ M+1).trans hpow
    have h15 : 1 ≤ (M+1)^5 := by omega
    have hm : 2400*M*(M+1)^4 ≤ 2400*(M+1)^5 := by
      calc
        2400*M*(M+1)^4 ≤ 2400*(M+1)*(M+1)^4 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega : M ≤ M+1))
        _ = 2400*(M+1)^5 := by ring
    have ht' := Nat.mul_le_mul_right (2400*(M+1)^4+2) (hd (r 23))
    have heq : M*(2400*(M+1)^4+2) = 2400*M*(M+1)^4+2*M := by ring
    rw [heq] at ht'
    omega
  · change additionFold r (d.reg (r 23)) c.store = _
    rw [hcs];rfl

theorem rawConvolution_one (a k : ℕ) : rawConvolution a 1 k = bitEquiv (Nat.testBit a k) := by
  unfold rawConvolution
  rw [Finset.sum_eq_single k]
  · rw [Nat.sub_self, Nat.testBit_one_zero]
    simp [bitEquiv_true]
  · intro j hj hne
    have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
    have hsub : k-j ≠ 0 := by omega
    have hb : Nat.testBit 1 (k-j) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact hsub (Nat.testBit_one_eq_true_iff_self_eq_zero.mp ht)
    rw [hb,bitEquiv_false,mul_zero]
  · simp

theorem add_matches_iff (ell : ℕ) (a b rem : Fin (2^ell)) :
    (∀ j < 3*ell+1, CoefficientMatches a.val 1 rem.val b.val 1 j) ↔
      rem = BinaryField.addIndex ell a b := by
  constructor
  · intro hmatch
    apply (indexEquiv ell).injective
    funext j
    have hj := hmatch j.val (by have := j.isLt; omega)
    unfold CoefficientMatches at hj
    rw [rawConvolution_one,rawConvolution_one] at hj
    change indexEquiv ell rem j = indexEquiv ell ((indexEquiv ell).symm
      (BinaryField.add (indexEquiv ell a) (indexEquiv ell b))) j
    rw [Equiv.apply_symm_apply]
    change indexEquiv ell rem j = indexEquiv ell a j+indexEquiv ell b j
    rw [indexEquiv_bit,indexEquiv_bit,indexEquiv_bit]
    calc
      bitEquiv (Nat.testBit rem.val j.val) =
          (bitEquiv (Nat.testBit rem.val j.val)+bitEquiv (Nat.testBit b.val j.val))+
            bitEquiv (Nat.testBit b.val j.val) := (CharTwo.add_cancel_right _ _).symm
      _ = bitEquiv (Nat.testBit a.val j.val)+bitEquiv (Nat.testBit b.val j.val) := by rw [← hj]
  · intro heq
    subst rem
    intro j hj
    unfold CoefficientMatches
    rw [rawConvolution_one,rawConvolution_one]
    have he : bitEquiv (Nat.testBit (BinaryField.addIndex ell a b).val j) =
        bitEquiv (Nat.testBit a.val j)+bitEquiv (Nat.testBit b.val j) := by
      rw [← bufferCoefficient_bit,← bufferCoefficient_bit,← bufferCoefficient_bit]
      unfold BinaryField.addIndex
      rw [Equiv.apply_symm_apply]
      unfold BinaryField.bufferCoefficient
      split_ifs <;> rfl
    rw [he]
    have hc : bitEquiv (Nat.testBit b.val j)+bitEquiv (Nat.testBit b.val j) = 0 := by
      exact CharTwo.add_self_eq_zero _
    rw [add_assoc,hc,add_zero]
theorem additionBodyStore_environment (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    environment r (additionBodyStore r d) = environment r d := by
  funext i
  fin_cases i
  · exact additionBodyStore_fresh r hr d 0 (Or.inl (by decide)) (by decide)
  · exact additionBodyStore_fresh r hr d 1 (Or.inl (by decide)) (by decide)
  · exact additionBodyStore_fresh r hr d 3 (Or.inl (by decide)) (by decide)
  · exact additionBodyStore_fresh r hr d 19 (Or.inr (Or.inl rfl)) (by decide)

theorem additionBodyStore_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    answer r (additionBodyStore r d) =
      if accept (environment r d) (d.reg (r 2)) (d.reg (r 4)) then some (d.reg (r 2)) else answer r d := by
  have h := innerBodyStore_answer r hr d
  unfold innerBodyStore at h
  rw [answer_setReg r _ _ _ (hr.ne (by decide)) (hr.ne (by decide))] at h
  unfold additionBodyStore
  rw [answer_setReg r _ _ _ (hr.ne (by decide)) (hr.ne (by decide))]
  exact h

theorem additionFold_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (n : ℕ) (d : TapeStore R B) :
    answer r (additionFold r n d) =
      scanRect (fun c _ => accept (environment r d) c (d.reg (r 4))) 1 n (d.reg (r 2)) (answer r d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    let c := d.setReg (r 25) n
    have henv : environment r c = environment r d := environment_setReg r d _ n
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    have h2 : c.reg (r 2) = d.reg (r 2) := by simp [c,reg_set27 r hr]
    have h4 : c.reg (r 4) = d.reg (r 4) := by simp [c,reg_set27 r hr]
    have ha : answer r c = answer r d := answer_setReg r d _ n (hr.ne (by decide)) (hr.ne (by decide))
    change answer r (additionFold r n (additionBodyStore r c)) = _
    rw [ih,additionBodyStore_environment r hr c,henv,
      additionBodyStore_fresh r hr c 4 (Or.inl (by decide)) (by decide),h4,
      additionBodyStore_index r hr c,h2,additionBodyStore_answer r hr c,henv,h2,h4,ha]
    rfl

theorem additionResult_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    answer r (additionResult r d) =
      scanRect (fun c _ => accept (environment r (additionPrepareStore r d)) c 1) 1 (d.reg (r 23)) 0 none := by
  rw [additionResult,additionFold_answer r hr]
  simp [additionPrepareStore_reg r hr,answer]

theorem additionResult_index (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (ell : ℕ) (a b : Fin (2^ell)) (d : TapeStore R B)
    (ha : d.reg (r 0) = a.val) (hb : d.reg (r 3) = b.val)
    (hN : d.reg (r 19) = 3*ell+1) (hq : d.reg (r 23) = 2^ell) :
    (additionResult r d).reg (r 20) = (BinaryField.addIndex ell a b).val := by
  let p := additionPrepareStore r d
  let test := fun c (_ : ℕ) => accept (environment r p) c 1
  let target := (BinaryField.addIndex ell a b).val
  have htest (i : Fin (2^ell)) : test i.val 0 = true ↔ i = BinaryField.addIndex ell a b := by
    rw [accept_iff]
    change (∀ j < p.reg (r 19),CoefficientMatches (p.reg (r 0)) (p.reg (r 1)) i.val (p.reg (r 3)) 1 j) ↔ _
    simpa [p,additionPrepareStore_reg r hr,ha,hb,hN] using add_matches_iff ell a b i
  have hg : ∀ i < 2^ell,∀ s < 1,test i s = true → i = target := by
    intro i hi s hs hp
    have he : (⟨i,hi⟩ : Fin (2^ell)) = BinaryField.addIndex ell a b := (htest ⟨i,hi⟩).mp hp
    exact congrArg Fin.val he
  have hit : ∃ i < 2^ell,∃ s < 1,test i s = true := by
    exact ⟨(BinaryField.addIndex ell a b).val,(BinaryField.addIndex ell a b).isLt,0,by omega,
      (htest (BinaryField.addIndex ell a b)).mpr rfl⟩
  have hanswer : answer r (additionResult r d) = some target := by
    rw [additionResult_answer r hr d,hq]
    exact scanRect_complete test _ _ target hg hit
  unfold answer at hanswer
  split at hanswer
  · contradiction
  · exact Option.some.inj hanswer

theorem additionBodyStore_tapeData (r : Fin 27 → Fin R) (d : TapeStore R B) :
    tapeData (additionBodyStore r d) = tapeData d := by
  rw [additionBodyStore,tapeData_setReg,commitStore_tapeData,certificateResult_tapeData]

theorem additionResult_tapeData (r : Fin 27 → Fin R) (d : TapeStore R B) :
    tapeData (additionResult r d) = tapeData d := by
  rw [additionResult,additionFold,
    loopResult_tapeData (r 25) (additionBodyStore r) (additionBodyStore_tapeData r)]
  rfl

theorem additionResult_input (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) (hi : i = 0 ∨ i = 3 ∨ i = 19 ∨ 23 ≤ i)
    (h25 : i ≠ 25) : (additionResult r d).reg (r i) = d.reg (r i) := by
  rw [additionResult,additionFold,loopResult_frame (r 25) (additionBodyStore r) (r i) (hr.ne h25)
    (fun c => additionBodyStore_fresh r hr c i (by
      rcases hi with h|h|h|h
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)) (by rcases hi with h|h|h|h <;> omega)),
    additionPrepareStore_reg r hr]
  have h1 : i ≠ (1:Fin 27) := by rcases hi with h|h|h|h <;> omega
  have h4 : i ≠ (4:Fin 27) := by rcases hi with h|h|h|h <;> omega
  have h21 : i ≠ (21:Fin 27) := by rcases hi with h|h|h|h <;> omega
  have h20 : i ≠ (20:Fin 27) := by rcases hi with h|h|h|h <;> omega
  have h22 : i ≠ (22:Fin 27) := by rcases hi with h|h|h|h <;> omega
  have h2 : i ≠ (2:Fin 27) := by rcases hi with h|h|h|h <;> omega
  simp [h1,h4,h21,h25,h20,h22,h2]

theorem additionBodyStore_outside (r : Fin 27 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 27,j ≠ r i) : (additionBodyStore r d).reg j = d.reg j := by
  unfold additionBodyStore
  simp only [TapeStore.setReg,Function.update_of_ne (hne 2)]
  rw [commitStore_fresh _ _ _ (hne 20) (hne 21) (hne 22) (hne 6)]
  apply certificateResult_outside
  intro i
  exact hne ⟨i.val,by have := i.isLt;omega⟩

theorem additionResult_outside (r : Fin 27 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 27,j ≠ r i) : (additionResult r d).reg j = d.reg j := by
  rw [additionResult,additionFold,loopResult_frame (r 25) (additionBodyStore r) j (hne 25)
    (fun c => additionBodyStore_outside r c j hne)]
  simp only [additionPrepareStore,TapeStore.setReg,Function.update_of_ne (hne 1),Function.update_of_ne (hne 4)]
  unfold multiplyPrepareStore
  simp [TapeStore.setReg,hne 2,hne 20,hne 21,hne 22,hne 25]

theorem addition_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (a b : Fin (2^ell)) (M : ℕ) (hM : 1 ≤ M)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (ha : d.reg (r 0) = a.val) (hb : d.reg (r 3) = b.val)
    (hN : d.reg (r 19) = 3*ell+1) (hq : d.reg (r 23) = 2^ell) :
    ∃ t e,t ≤ 3000*(M+1)^5 ∧
      (addition r).Stops inp (d.toCfg (addition (B:=B) r).entry) t e ∧ e.store = additionResult r d ∧
      e.reg (r 20) = (BinaryField.addIndex ell a b).val ∧
      (∀ i,i = 0 ∨ i = 3 ∨ i = 19 ∨ 23 ≤ i → i ≠ 25 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ tapeData e.store = tapeData d := by
  obtain ⟨t,e,ht,he,hs,hbound⟩ := addition_stops_exact r hr inp M hM d hd
  refine ⟨t,e,ht,he,hs,?_,?_,?_,hbound,?_⟩
  · change e.store.reg (r 20) = _
    rw [hs];exact additionResult_index r hr ell a b d ha hb hN hq
  · intro i hi h25
    change e.store.reg (r i) = _
    rw [hs];exact additionResult_input r hr d i hi h25
  · intro j hj
    change e.store.reg j = _
    rw [hs];exact additionResult_outside r d j hj
  · rw [hs];exact additionResult_tapeData r d

/-- Four-label destructive test for the unary constant one. -/
def oneTest (x flag : Fin R) : TapeProgram R B 4 where
  entry := 0
  code i := if i = 0 then .dec x 3 1 else if i = 1 then .dec x 2 3
    else if i = 2 then .inc flag 3 else .halt

def oneTestStore (x flag : Fin R) (d : TapeStore R B) : TapeStore R B :=
  if d.reg x = 0 then d else if d.reg x = 1 then (d.setReg x 0).setReg flag (d.reg flag+1)
  else d.setReg x (d.reg x-2)

theorem oneTest_stops (x flag : Fin R) (hxf : x ≠ flag) (inp : Inputs) (d : TapeStore R B) :
    ∃ t,t ≤ 3 ∧ (oneTest x flag).Stops inp (d.toCfg 0) t ((oneTestStore x flag d).toCfg 3) := by
  by_cases hx : d.reg x = 0
  · refine ⟨1,by omega,⟨?_,?_⟩⟩
    · apply TapeProgram.Exec.one
      · simp [TapeProgram.halted,oneTest]
      · simp [TapeProgram.step,oneTest,oneTestStore,hx]
    · simp [TapeProgram.halted,oneTest]
  · let c := d.setReg x (d.reg x-1)
    have hhead : (oneTest x flag).step inp (d.toCfg 0) = c.toCfg 1 := by
      simp [TapeProgram.step,oneTest,hx,c,TapeStore.setReg]
    by_cases h1 : d.reg x = 1
    · have hc0 : c.reg x = 0 := by simp [c,h1,TapeStore.setReg]
      refine ⟨3,by omega,⟨?_,?_⟩⟩
      · apply TapeProgram.Exec.step (by simp [TapeProgram.halted,oneTest]) hhead
        apply TapeProgram.Exec.step (d:=c.toCfg 2) (by simp [TapeProgram.halted,oneTest])
        · simp [TapeProgram.step,oneTest,hc0]
        · apply TapeProgram.Exec.one
          · simp [TapeProgram.halted,oneTest]
          · simp [TapeProgram.step,oneTest,oneTestStore,hx,h1,c,TapeStore.setReg,Ne.symm hxf]
      · simp [TapeProgram.halted,oneTest]
    · have hcpos : c.reg x ≠ 0 := by simp [c,TapeStore.setReg];omega
      have hnpos : d.reg x-1 ≠ 0 := by omega
      refine ⟨2,by omega,⟨?_,?_⟩⟩
      · apply TapeProgram.Exec.step (by simp [TapeProgram.halted,oneTest]) hhead
        apply TapeProgram.Exec.one
        · simp [TapeProgram.halted,oneTest]
        · simp [TapeProgram.step,oneTest,oneTestStore,hx,h1,c,hcpos,hnpos,TapeStore.setReg,
            Function.update_idem,Nat.sub_sub]
      · simp [TapeProgram.halted,oneTest]

def isOne (x flag : Fin R) : TapeProgram R B 6 := TapeProgram.seq (TapeMacros.clear flag) (oneTest x flag)
def isOneStore (x flag : Fin R) (d : TapeStore R B) : TapeStore R B := oneTestStore x flag (d.setReg flag 0)

theorem isOne_stops (x flag : Fin R) (hxf : x ≠ flag) (inp : Inputs) (d : TapeStore R B) :
    ∃ t e,t ≤ d.reg flag+5 ∧ (isOne x flag).Stops inp (d.toCfg (isOne (B:=B) x flag).entry) t e ∧
      e.store = isOneStore x flag d := by
  have hclear := TapeMacros.clear_stops flag inp (d.reg flag) d rfl
  obtain ⟨t,ht,hstop⟩ := oneTest_stops x flag hxf inp (d.setReg flag 0)
  have hall := hclear.seq hstop
  exact ⟨_,_,by omega,hall,rfl⟩

theorem isOneStore_flag (x flag : Fin R) (hxf : x ≠ flag) (d : TapeStore R B) :
    (isOneStore x flag d).reg flag = if d.reg x = 1 then 1 else 0 := by
  unfold isOneStore oneTestStore
  simp only [TapeStore.setReg,Function.update_self,Function.update_of_ne hxf]
  split <;> simp_all [Function.update,Ne.symm hxf]
  split <;> simp_all [Function.update,Ne.symm hxf]

theorem isOneStore_fresh (x flag j : Fin R) (d : TapeStore R B) (hjx : j ≠ x) (hjf : j ≠ flag) :
    (isOneStore x flag d).reg j = d.reg j := by
  unfold isOneStore oneTestStore
  split <;> simp_all [TapeStore.setReg]
  split <;> simp_all [TapeStore.setReg]

theorem isOneStore_tapeData (x flag : Fin R) (d : TapeStore R B) :
    tapeData (isOneStore x flag d) = tapeData d := by
  unfold isOneStore oneTestStore
  split <;> try rfl
  split <;> rfl

theorem isOneStore_bound (x flag : Fin R) (hxf : x ≠ flag) (M : ℕ) (hM : 1 ≤ M)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) : ∀ j,(isOneStore x flag d).reg j ≤ M := by
  unfold isOneStore oneTestStore
  have hb := setReg_bound d flag 0 M hd (by omega)
  split
  · exact hb
  · split
    · apply setReg_bound _ _ _ M (setReg_bound _ _ 0 M hb (by omega))
      simp [TapeStore.setReg];omega
    · apply setReg_bound _ _ _ M hb
      have := hb x
      omega

/-- Generic bounded one-counter source scan with an incrementing candidate. -/
theorem singleLoop_stops (P : TapeProgram R B L) (counter candidate : Fin R) (hne : candidate ≠ counter)
    (F : TapeStore R B → TapeStore R B) (inp : Inputs) (M C : ℕ)
    (hf : ∀ d,(F d).reg counter = d.reg counter)
    (hc : ∀ d,(F d).reg candidate = d.reg candidate+1)
    (hb : ∀ d,(∀ j,d.reg j ≤ M) → d.reg candidate+1 ≤ M → ∀ j,(F d).reg j ≤ M)
    (hs : ∀ d,(∀ j,d.reg j ≤ M) → ∃ t e,t ≤ C ∧ P.Stops inp (d.toCfg P.entry) t e ∧ e.store = F d)
    (n : ℕ) (d : TapeStore R B) (hn : d.reg counter = n) (hd : ∀ j,d.reg j ≤ M) (hi : d.reg candidate+n ≤ M) :
    ∃ t,t ≤ n*(C+2)+1 ∧ (TapeProgram.countedLoop P counter).Stops inp
      (d.toCfg (TapeProgram.loopHeader L)) t ((loopResult counter F n d).toCfg (TapeProgram.loopExit L)) ∧
      (∀ j,(loopResult counter F n d).reg j ≤ M) := by
  let Inv : ℕ → TapeStore R B → Prop := fun n c => (∀ j,c.reg j ≤ M) ∧ c.reg candidate+n ≤ M
  have hbody : ∀ n c,c.reg counter = n+1 → Inv (n+1) c → ∃ t e,t ≤ C ∧
      P.Stops inp ((c.setReg counter n).toCfg P.entry) t e ∧ e.store = F (c.setReg counter n) ∧ Inv n e.store := by
    intro n c hcn hInv
    have hcb := setReg_bound c counter n M hInv.1 (by have := hInv.1 counter;omega)
    have hci : (c.setReg counter n).reg candidate+1 ≤ M := by
      simp only [TapeStore.setReg,Function.update_of_ne hne]
      have := hInv.2;omega
    obtain ⟨t,e,ht,he,hes⟩ := hs _ hcb
    refine ⟨t,e,ht,he,hes,?_⟩
    rw [hes]
    refine ⟨hb _ hcb hci,?_⟩
    rw [hc]
    simp only [TapeStore.setReg,Function.update_of_ne hne]
    have := hInv.2;omega
  obtain ⟨t,ht,he,hInv⟩ := loop_stops P counter F inp C Inv hf hbody n d hn ⟨hd,hi⟩
  exact ⟨t,ht,he,hInv.1⟩

def inverseMultiplyLayout (r : Fin 31 → Fin R) : Fin 27 → Fin R :=
  fun i => r ⟨i.val,by have := i.isLt;omega⟩
def inverseCommitLayout (r : Fin 31 → Fin R) : Fin 5 → Fin R := fun i => r (![1,27,28,29,6] i)

theorem inverseMultiplyLayout_injective (r : Fin 31 → Fin R) (hr : Function.Injective r) :
    Function.Injective (inverseMultiplyLayout r) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin 31 => z.val) (hr h)

theorem inverseCommitLayout_injective (r : Fin 31 → Fin R) (hr : Function.Injective r) :
    Function.Injective (inverseCommitLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [inverseCommitLayout]

theorem reg_set31 (r : Fin 31 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i j : Fin 31) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j;simp
  · simp [TapeStore.setReg,h,hr.ne h]

theorem inverseMultiply_preserves (r : Fin 31 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 31) (hi : i < 2 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24 ∨ 27 ≤ i) :
    (multiplyResult (inverseMultiplyLayout r) d).reg (r i) = d.reg (r i) := by
  by_cases hlt : i.val < 27
  · let j : Fin 27 := ⟨i.val,hlt⟩
    have h := multiplyResult_input (inverseMultiplyLayout r) (inverseMultiplyLayout_injective r hr) d j (by
      rcases hi with hi|hi|hi|hi|hi|hi
      · left
        change i.val < 2
        change i.val < 2 at hi
        exact hi
      · subst i;exact Or.inr (Or.inl rfl)
      · subst i;exact Or.inr (Or.inr (Or.inl rfl))
      · subst i;exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · subst i;exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · change 27 ≤ i.val at hi;omega)
    simpa [inverseMultiplyLayout,j] using h
  · apply multiplyResult_outside
    intro j
    apply hr.ne
    intro h
    have hv := congrArg (fun z : Fin 31 => z.val) h
    change i.val = j.val at hv
    have := j.isLt;omega

def inverseBody (r : Fin 31 → Fin R) : TapeProgram R B 399 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (multiply (inverseMultiplyLayout r)) (isOne (r 20) (r 6)))
    (commit (inverseCommitLayout r))) (TapeMacros.increment (r 1))
def inverseBodyStore (r : Fin 31 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c₁ := multiplyResult (inverseMultiplyLayout r) d
  let c₂ := isOneStore (r 20) (r 6) c₁
  let c₃ := commitStore (inverseCommitLayout r) c₂
  c₃.setReg (r 1) (c₃.reg (r 1)+1)

theorem inverseBodyStore_fresh (r : Fin 31 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 31) (hi : i = 0 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24 ∨ i = 30) :
    (inverseBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold inverseBodyStore
  simp only [reg_set31 r hr,show i ≠ (1:Fin 31) from by rcases hi with h|h|h|h|h|h <;> omega,ite_false]
  rw [commitStore_fresh _ _ _
    (hr.ne (show i ≠ (27:Fin 31) from by rcases hi with h|h|h|h|h|h <;> omega))
    (hr.ne (show i ≠ (28:Fin 31) from by rcases hi with h|h|h|h|h|h <;> omega))
    (hr.ne (show i ≠ (29:Fin 31) from by rcases hi with h|h|h|h|h|h <;> omega))
    (hr.ne (show i ≠ (6:Fin 31) from by rcases hi with h|h|h|h|h|h <;> omega)),
    isOneStore_fresh _ _ _ _
      (hr.ne (show i ≠ (20:Fin 31) from by rcases hi with h|h|h|h|h|h <;> omega))
      (hr.ne (show i ≠ (6:Fin 31) from by rcases hi with h|h|h|h|h|h <;> omega))]
  apply inverseMultiply_preserves r hr d i
  rcases hi with h|h|h|h|h|h <;> simp_all

theorem inverseBodyStore_index (r : Fin 31 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    (inverseBodyStore r d).reg (r 1) = d.reg (r 1)+1 := by
  unfold inverseBodyStore
  simp only [TapeStore.setReg,Function.update_self]
  rw [commitStore_fresh _ _ _
    (hr.ne (show (1:Fin 31) ≠ 27 from by decide)) (hr.ne (show (1:Fin 31) ≠ 28 from by decide))
    (hr.ne (show (1:Fin 31) ≠ 29 from by decide)) (hr.ne (show (1:Fin 31) ≠ 6 from by decide)),
    isOneStore_fresh _ _ _ _ (hr.ne (by decide)) (hr.ne (by decide)),
    inverseMultiply_preserves r hr d 1 (Or.inl (by decide))]

theorem inverseBodyStore_bound (r : Fin 31 → Fin R) (hr : Function.Injective r) (M : ℕ) (hM : 1 ≤ M)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 1)+1 ≤ M) :
    ∀ j,(inverseBodyStore r d).reg j ≤ M := by
  have hb₁ : ∀ j,(multiplyResult (inverseMultiplyLayout r) d).reg j ≤ M := by
    obtain ⟨_,_,_,_,hs,hb⟩ := multiply_stops_exact (inverseMultiplyLayout r) (inverseMultiplyLayout_injective r hr) ⟨[],[],[],[]⟩ M hM d hd
    simpa only [← hs,TapeCfg.store] using hb
  have hb₂ := isOneStore_bound (r 20) (r 6) (hr.ne (by decide)) M hM _ hb₁
  have hb₃ := commitStore_bound (inverseCommitLayout r) (inverseCommitLayout_injective r hr) M hM _ hb₂
  apply setReg_bound _ _ _ M hb₃
  have he := inverseBodyStore_index r hr d
  have he' : (commitStore (inverseCommitLayout r) (isOneStore (r 20) (r 6)
    (multiplyResult (inverseMultiplyLayout r) d))).reg (r 1)+1 = d.reg (r 1)+1 := by
    simpa only [inverseBodyStore,TapeStore.setReg,Function.update_self] using he
  rw [he'];exact hc

theorem inverseBody_stops (r : Fin 31 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∃ t e,t ≤ 11000*(M+1)^6 ∧ (inverseBody r).Stops inp (d.toCfg (inverseBody (B:=B) r).entry) t e ∧
      e.store = inverseBodyStore r d := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := multiply_stops_exact (inverseMultiplyLayout r) (inverseMultiplyLayout_injective r hr) inp M hM d hd
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂⟩ := isOne_stops (r 20) (r 6) (hr.ne (by decide)) inp c₁.store
  have hb₂ : ∀ j,c₂.store.reg j ≤ M := by rw [hs₂];exact isOneStore_bound _ _ (hr.ne (by decide)) M hM _ hb₁
  obtain ⟨t₃,c₃,ht₃,h₃,hs₃⟩ := commit_stops (inverseCommitLayout r) (inverseCommitLayout_injective r hr) inp M c₂.store hb₂
  have h₄ := TapeMacros.increment_stops (r 1) inp c₃.store
  have hall := ((h₁.seq h₂).seq h₃).seq h₄
  refine ⟨_,_,?_,hall,?_⟩
  · have ht₂' : t₂ ≤ M+5 := ht₂.trans (Nat.add_le_add_right (hb₁ (r 6)) 5)
    have hpow := Nat.le_self_pow (by decide : (6:ℕ) ≠ 0) (M+1)
    omega
  · change c₃.store.setReg (r 1) _ = _
    rw [hs₃,hs₂,hs₁];rfl

def inverseLoop (r : Fin 31 → Fin R) : TapeProgram R B 401 := TapeProgram.countedLoop (inverseBody r) (r 30)
def inverseFold (r : Fin 31 → Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B := loopResult (r 30) (inverseBodyStore r) n d

theorem inverseLoop_stops (r : Fin 31 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B) (hn : d.reg (r 30) = n)
    (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 1)+n ≤ M) :
    ∃ t,t ≤ n*(11000*(M+1)^6+2)+1 ∧ (inverseLoop r).Stops inp
      (d.toCfg (TapeProgram.loopHeader 399)) t ((inverseFold r n d).toCfg (TapeProgram.loopExit 399)) ∧
      (∀ j,(inverseFold r n d).reg j ≤ M) := by
  exact singleLoop_stops (inverseBody r) (r 30) (r 1) (hr.ne (by decide)) (inverseBodyStore r) inp M _
    (fun c => inverseBodyStore_fresh r hr c 30 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
    (inverseBodyStore_index r hr) (inverseBodyStore_bound r hr M hM) (inverseBody_stops r hr inp M hM) n d hn hd hc

def inversePrepare (r : Fin 31 → Fin R) : TapeProgram R B 17 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeMacros.clear (r 27)) (TapeMacros.clear (r 29)))
    (TapeMacros.clear (r 1))) (TapeMacros.copy (r 23) (r 30) (r 28))
def inversePrepareStore (r : Fin 31 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := ((d.setReg (r 27) 0).setReg (r 29) 0).setReg (r 1) 0
  (c.setReg (r 30) (c.reg (r 23))).setReg (r 28) 0

theorem inversePrepare_stops (r : Fin 31 → Fin R) (hr : Function.Injective r) (inp : Inputs) (d : TapeStore R B) :
    ∃ e,(inversePrepare r).Stops inp (d.toCfg (inversePrepare (B:=B) r).entry)
      (d.reg (r 27)+d.reg (r 29)+d.reg (r 1)+d.reg (r 30)+d.reg (r 28)+5*d.reg (r 23)+13) e ∧
      e.store = inversePrepareStore r d := by
  have h₁ := TapeMacros.clear_stops (r 27) inp (d.reg (r 27)) d rfl
  have h₂ := TapeMacros.clear_stops (r 29) inp (d.reg (r 29)) (d.setReg (r 27) 0) (by simp [reg_set31 r hr])
  have h₃ := TapeMacros.clear_stops (r 1) inp (d.reg (r 1)) ((d.setReg (r 27) 0).setReg (r 29) 0) (by simp [reg_set31 r hr])
  obtain ⟨c,hc,hcs⟩ := TapeMacros.copy_stops (r 23) (r 30) (r 28) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) inp (((d.setReg (r 27) 0).setReg (r 29) 0).setReg (r 1) 0)
  have hall := ((h₁.seq h₂).seq h₃).seq hc
  refine ⟨c.mapPC (TapeProgram.rightLabel 6),?_,hcs⟩
  convert hall using 1 <;> first | rfl | (simp [reg_set31 r hr];omega)

theorem inversePrepareStore_reg (r : Fin 31 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i : Fin 31) :
    (inversePrepareStore r d).reg (r i) = if i = 28 then 0 else if i = 30 then d.reg (r 23)
      else if i = 27 ∨ i = 29 ∨ i = 1 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [inversePrepareStore,reg_set31 r hr]

theorem inversePrepareStore_bound (r : Fin 31 → Fin R) (hr : Function.Injective r) (M : ℕ)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) : ∀ j,(inversePrepareStore r d).reg j ≤ M := by
  unfold inversePrepareStore
  apply setReg_bound _ _ 0 M _ (by omega)
  apply setReg_bound _ _ _ M
  · exact setReg_bound _ _ 0 M (setReg_bound _ _ 0 M (setReg_bound d _ 0 M hd (by omega)) (by omega)) (by omega)
  · simpa [reg_set31 r hr] using hd (r 23)

/-- Actual fixed418-label q-candidate inverse scan. -/
def inverse (r : Fin 31 → Fin R) : TapeProgram R B 418 := TapeProgram.seq (inversePrepare r) (inverseLoop r)
def inverseResult (r : Fin 31 → Fin R) (d : TapeStore R B) : TapeStore R B :=
  inverseFold r (d.reg (r 23)) (inversePrepareStore r d)

theorem inverse_stops_exact (r : Fin 31 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∃ t e,t ≤ 20000*(M+1)^7 ∧ (inverse r).Stops inp (d.toCfg (inverse (B:=B) r).entry) t e ∧
      e.store = inverseResult r d ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨c,hc,hcs⟩ := inversePrepare_stops r hr inp d
  have hcb : ∀ j,c.store.reg j ≤ M := by rw [hcs];exact inversePrepareStore_bound r hr M d hd
  have hcn : c.reg (r 30) = d.reg (r 23) := by change c.store.reg (r 30) = _;rw [hcs,inversePrepareStore_reg r hr];simp
  have hcc : c.reg (r 1) = 0 := by change c.store.reg (r 1) = _;rw [hcs,inversePrepareStore_reg r hr];simp
  obtain ⟨t,ht,he,hbound⟩ := inverseLoop_stops r hr inp M hM (d.reg (r 23)) c.store hcn hcb
    (by change c.reg (r 1)+d.reg (r 23) ≤ M;rw [hcc];simpa using hd (r 23))
  have hall := hc.seq he
  refine ⟨_,_,?_,hall,?_,hbound⟩
  · have hp : d.reg (r 27)+d.reg (r 29)+d.reg (r 1)+d.reg (r 30)+d.reg (r 28)+5*d.reg (r 23)+13 ≤ 10*M+13 := by
      have := hd (r 27);have := hd (r 29);have := hd (r 1);have := hd (r 30);have := hd (r 28);have := hd (r 23);omega
    have hpow := Nat.le_self_pow (by decide : (7:ℕ) ≠ 0) (M+1)
    have hM7 : M ≤ (M+1)^7 := (by omega : M ≤ M+1).trans hpow
    have h17 : 1 ≤ (M+1)^7 := by omega
    have hm : 11000*M*(M+1)^6 ≤ 11000*(M+1)^7 := by
      calc
        11000*M*(M+1)^6 ≤ 11000*(M+1)*(M+1)^6 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega : M ≤ M+1))
        _ = 11000*(M+1)^7 := by ring
    have ht' := Nat.mul_le_mul_right (11000*(M+1)^6+2) (hd (r 23))
    have heq : M*(11000*(M+1)^6+2) = 11000*M*(M+1)^6+2*M := by ring
    rw [heq] at ht'
    change d.reg (r 27)+d.reg (r 29)+d.reg (r 1)+d.reg (r 30)+d.reg (r 28)+5*d.reg (r 23)+13+1+t ≤ _
    omega
  · change inverseFold r (d.reg (r 23)) c.store = _
    rw [hcs];rfl

theorem indexEquiv_one (ell : ℕ) (h : 0 < ell) :
    indexEquiv ell ⟨1,Nat.one_lt_two_pow (by omega)⟩ = BinaryField.one ell := by
  funext j
  rw [indexEquiv_bit]
  have hb : Nat.testBit 1 j.val = decide (0 = j.val) := by simpa using (Nat.testBit_two_pow (n:=0) (m:=j.val))
  rw [hb]
  simp [BinaryField.one,bitEquiv,eq_comm]

theorem multiplyIndex_one_iff (ell : ℕ) (h : 0 < ell) (a b : Fin (2^ell)) :
    (BinaryField.multiplyIndex ell h (selectedIndex ell h) (indexEquiv ell a) (indexEquiv ell b)).val = 1 ↔
      BinaryField.multiply ell h (selectedIndex ell h) (indexEquiv ell a) (indexEquiv ell b) = BinaryField.one ell := by
  constructor
  · intro hv
    have he : BinaryField.multiplyIndex ell h (selectedIndex ell h) (indexEquiv ell a) (indexEquiv ell b) =
        ⟨1,Nat.one_lt_two_pow (by omega)⟩ := Fin.ext hv
    rw [BinaryField.multiply,he,indexEquiv_one ell h]
  · intro he
    have hv := (indexEquiv ell).injective (he.trans (indexEquiv_one ell h).symm)
    exact congrArg Fin.val hv

theorem inverse_candidate_unique (ell : ℕ) (h : 0 < ell) (a b : Fin (2^ell))
    (hb : (BinaryField.multiplyIndex ell h (selectedIndex ell h) (indexEquiv ell a) (indexEquiv ell b)).val = 1) :
    b = BinaryField.inverseIndex ell h a := by
  have he := (multiplyIndex_one_iff ell h a b).mp hb
  have hd := congrArg (BinaryField.decode ell h) he
  rw [BinaryField.decode_multiply,BinaryField.decode_one] at hd
  apply (BinaryField.elements ell h).injective
  rw [BinaryField.elements_inverseIndex]
  change BinaryField.decode ell h (indexEquiv ell b) = (BinaryField.decode ell h (indexEquiv ell a))⁻¹
  exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hd)

def inverseTest (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell)) (b : ℕ) : Bool :=
  if hb : b < 2^ell then decide ((BinaryField.multiplyIndex ell h (selectedIndex ell h)
    (indexEquiv ell a) (indexEquiv ell ⟨b,hb⟩)).val = 1) else false

def InverseSetup (r : Fin 31 → Fin R) (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell)) (d : TapeStore R B) : Prop :=
  d.reg (r 0) = a.val ∧ d.reg (r 3) = 2^ell+(selectedIndex ell h).val ∧
    d.reg (r 19) = 3*ell+1 ∧ d.reg (r 23) = 2^ell ∧ d.reg (r 24) = 2^(2*ell)
def inverseAnswer (r : Fin 31 → Fin R) (d : TapeStore R B) : Option ℕ :=
  if d.reg (r 29) = 0 then none else some (d.reg (r 27))

theorem inverseAnswer_setReg (r : Fin 31 → Fin R) (d : TapeStore R B) (j : Fin R) (n : ℕ)
    (h27 : r 27 ≠ j) (h29 : r 29 ≠ j) : inverseAnswer r (d.setReg j n) = inverseAnswer r d := by
  simp [inverseAnswer,TapeStore.setReg,h27,h29]

theorem inverseSetup_setReg (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (d : TapeStore R B) (n : ℕ) (hs : InverseSetup r ell h a d) :
    InverseSetup r ell h a (d.setReg (r 30) n) := by simpa [InverseSetup,reg_set31 r hr] using hs

theorem inverseBodyStore_setup (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (d : TapeStore R B) (hs : InverseSetup r ell h a d) :
    InverseSetup r ell h a (inverseBodyStore r d) := by
  rcases hs with ⟨h0,h3,h19,h23,h24⟩
  exact ⟨(inverseBodyStore_fresh r hr d 0 (Or.inl rfl)).trans h0,
    (inverseBodyStore_fresh r hr d 3 (Or.inr (Or.inl rfl))).trans h3,
    (inverseBodyStore_fresh r hr d 19 (Or.inr (Or.inr (Or.inl rfl)))).trans h19,
    (inverseBodyStore_fresh r hr d 23 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans h23,
    (inverseBodyStore_fresh r hr d 24 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).trans h24⟩

theorem inverseBodyStore_answer (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (d : TapeStore R B) (hs : InverseSetup r ell h a d) (hc : d.reg (r 1) < 2^ell) :
    inverseAnswer r (inverseBodyStore r d) =
      if inverseTest ell h a (d.reg (r 1)) then some (d.reg (r 1)) else inverseAnswer r d := by
  let c₁ := multiplyResult (inverseMultiplyLayout r) d
  let c₂ := isOneStore (r 20) (r 6) c₁
  rcases hs with ⟨ha,hm,hN,hq,hQ⟩
  have hp : c₁.reg (r 20) = (BinaryField.multiplyIndex ell h (selectedIndex ell h)
      (indexEquiv ell a) (indexEquiv ell ⟨d.reg (r 1),hc⟩)).val :=
    multiplyResult_index (inverseMultiplyLayout r) (inverseMultiplyLayout_injective r hr) ell h
      (selectedIndex ell h) a ⟨d.reg (r 1),hc⟩ d ha rfl hm hN hq hQ
  have hf : c₂.reg (r 6) = if c₁.reg (r 20) = 1 then 1 else 0 :=
    isOneStore_flag _ _ (hr.ne (by decide)) c₁
  have hcan : c₂.reg (r 1) = d.reg (r 1) := by
    rw [isOneStore_fresh _ _ _ _ (hr.ne (by decide)) (hr.ne (by decide))]
    exact inverseMultiply_preserves r hr d 1 (Or.inl (by decide))
  have h27 : c₂.reg (r 27) = d.reg (r 27) := by
    rw [isOneStore_fresh _ _ _ _ (hr.ne (by decide)) (hr.ne (by decide))]
    exact inverseMultiply_preserves r hr d 27 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))
  have h29 : c₂.reg (r 29) = d.reg (r 29) := by
    rw [isOneStore_fresh _ _ _ _ (hr.ne (by decide)) (hr.ne (by decide))]
    exact inverseMultiply_preserves r hr d 29 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))
  change inverseAnswer r ((commitStore (inverseCommitLayout r) c₂).setReg (r 1) _) = _
  rw [inverseAnswer_setReg r _ _ _ (hr.ne (by decide)) (hr.ne (by decide))]
  by_cases ht : c₁.reg (r 20) = 1
  · have hf1 : c₂.reg (r 6) = 1 := by simp [hf,ht]
    have hac : inverseTest ell h a (d.reg (r 1)) = true := by simp [inverseTest,hc,← hp,ht]
    simp [inverseAnswer,commitStore,commitBodyStore,inverseCommitLayout,reg_set31 r hr,hf1,hcan,hac]
  · have hf0 : c₂.reg (r 6) = 0 := by simp [hf,ht]
    have hac : inverseTest ell h a (d.reg (r 1)) = false := by simp [inverseTest,hc,← hp,ht]
    simp [inverseAnswer,commitStore,inverseCommitLayout,hf0,hac,h27,h29]

theorem inverseFold_answer (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (n : ℕ) (d : TapeStore R B) (hs : InverseSetup r ell h a d)
    (hc : d.reg (r 1)+n ≤ 2^ell) :
    inverseAnswer r (inverseFold r n d) =
      scanRect (fun c _ => inverseTest ell h a c) 1 n (d.reg (r 1)) (inverseAnswer r d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    let c := d.setReg (r 30) n
    have hsetup := inverseSetup_setReg r hr ell h a d n hs
    have hc1 : c.reg (r 1) = d.reg (r 1) := by simp [c,reg_set31 r hr]
    have hcan : c.reg (r 1) < 2^ell := by omega
    have ha : inverseAnswer r c = inverseAnswer r d := inverseAnswer_setReg r d _ n (hr.ne (by decide)) (hr.ne (by decide))
    change inverseAnswer r (inverseFold r n (inverseBodyStore r c)) = _
    rw [ih (inverseBodyStore r c) (inverseBodyStore_setup r hr ell h a c hsetup)
      (by rw [inverseBodyStore_index r hr c,hc1];omega),inverseBodyStore_index r hr c,hc1,
      inverseBodyStore_answer r hr ell h a c hsetup hcan,hc1,ha]
    rfl

theorem inverseResult_answer (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (d : TapeStore R B) (hs : InverseSetup r ell h a d) :
    inverseAnswer r (inverseResult r d) = scanRect (fun c _ => inverseTest ell h a c) 1 (2^ell) 0 none := by
  have hp : InverseSetup r ell h a (inversePrepareStore r d) := by
    simpa [InverseSetup,inversePrepareStore_reg r hr] using hs
  rw [inverseResult,hs.2.2.2.1,inverseFold_answer r hr ell h a _ _ hp
    (by simp [inversePrepareStore_reg r hr])]
  simp [inversePrepareStore_reg r hr,inverseAnswer]

theorem indexEquiv_zero (ell : ℕ) : indexEquiv ell ⟨0,Nat.two_pow_pos ell⟩ = BinaryField.zero ell := by
  funext j
  rw [indexEquiv_bit]
  simp [BinaryField.zero,bitEquiv]

theorem inverseResult_index_nonzero (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (d : TapeStore R B) (hs : InverseSetup r ell h a d) (ha0 : a.val ≠ 0) :
    (inverseResult r d).reg (r 27) = (BinaryField.inverseIndex ell h a).val := by
  let test := fun c (_ : ℕ) => inverseTest ell h a c
  let target := (BinaryField.inverseIndex ell h a).val
  have hg : ∀ i < 2^ell,∀ s < 1,test i s = true → i = target := by
    intro i hi s hs ht
    have hp : (BinaryField.multiplyIndex ell h (selectedIndex ell h) (indexEquiv ell a) (indexEquiv ell ⟨i,hi⟩)).val = 1 := by
      simpa [test,inverseTest,hi] using ht
    exact congrArg Fin.val (inverse_candidate_unique ell h a ⟨i,hi⟩ hp)
  have hx : indexEquiv ell a ≠ BinaryField.zero ell := by
    intro hz
    have he := (indexEquiv ell).injective (hz.trans (indexEquiv_zero ell).symm)
    exact ha0 (congrArg Fin.val he)
  obtain ⟨i,hi⟩ := BinaryField.exists_inverseIndex ell h (indexEquiv ell a) hx
  have hp := (multiplyIndex_one_iff ell h a i).mpr hi
  have hit : ∃ i < 2^ell,∃ s < 1,test i s = true :=
    ⟨i.val,i.isLt,0,by omega,by simp [test,inverseTest,i.isLt,hp]⟩
  have han : inverseAnswer r (inverseResult r d) = some target := by
    rw [inverseResult_answer r hr ell h a d hs]
    exact scanRect_complete test _ _ target hg hit
  unfold inverseAnswer at han
  split at han
  · contradiction
  · exact Option.some.inj han

theorem inverseBodyStore_tapeData (r : Fin 31 → Fin R) (d : TapeStore R B) :
    tapeData (inverseBodyStore r d) = tapeData d := by
  rw [inverseBodyStore,tapeData_setReg,commitStore_tapeData,isOneStore_tapeData,multiplyResult_tapeData]

theorem inverseResult_tapeData (r : Fin 31 → Fin R) (d : TapeStore R B) :
    tapeData (inverseResult r d) = tapeData d := by
  rw [inverseResult,inverseFold,loopResult_tapeData (r 30) (inverseBodyStore r) (inverseBodyStore_tapeData r)]
  rfl

theorem inverseResult_input (r : Fin 31 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 31) (hi : i = 0 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24) :
    (inverseResult r d).reg (r i) = d.reg (r i) := by
  rw [inverseResult,inverseFold,loopResult_frame (r 30) (inverseBodyStore r) (r i)
    (hr.ne (show i ≠ (30:Fin 31) from by rcases hi with h|h|h|h|h <;> omega))
    (fun c => inverseBodyStore_fresh r hr c i (by rcases hi with h|h|h|h|h <;> simp_all)),
    inversePrepareStore_reg r hr]
  have h28 : i ≠ (28:Fin 31) := by rcases hi with h|h|h|h|h <;> omega
  have h30 : i ≠ (30:Fin 31) := by rcases hi with h|h|h|h|h <;> omega
  have h27 : i ≠ (27:Fin 31) := by rcases hi with h|h|h|h|h <;> omega
  have h29 : i ≠ (29:Fin 31) := by rcases hi with h|h|h|h|h <;> omega
  have h1 : i ≠ (1:Fin 31) := by rcases hi with h|h|h|h|h <;> omega
  simp [h28,h30,h27,h29,h1]

theorem inverseBodyStore_outside (r : Fin 31 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 31,j ≠ r i) : (inverseBodyStore r d).reg j = d.reg j := by
  unfold inverseBodyStore
  simp only [TapeStore.setReg,Function.update_of_ne (hne 1)]
  rw [commitStore_fresh _ _ _ (hne 27) (hne 28) (hne 29) (hne 6),
    isOneStore_fresh _ _ _ _ (hne 20) (hne 6)]
  apply multiplyResult_outside
  intro i
  exact hne ⟨i.val,by have := i.isLt;omega⟩

theorem inverseResult_outside (r : Fin 31 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 31,j ≠ r i) : (inverseResult r d).reg j = d.reg j := by
  rw [inverseResult,inverseFold,loopResult_frame (r 30) (inverseBodyStore r) j (hne 30)
    (fun c => inverseBodyStore_outside r c j hne)]
  simp [inversePrepareStore,TapeStore.setReg,hne 1,hne 27,hne 28,hne 29,hne 30]

/-- Complete nonzero-input source inverse contract, suitable for Gaussian
pivots. The result is the exact BinaryField inverse index. -/
theorem inverse_stops_nonzero (r : Fin 31 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell)) (M : ℕ) (hM : 1 ≤ M)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hs : InverseSetup r ell h a d) (ha0 : a.val ≠ 0) :
    ∃ t e,t ≤ 20000*(M+1)^7 ∧ (inverse r).Stops inp (d.toCfg (inverse (B:=B) r).entry) t e ∧
      e.store = inverseResult r d ∧ e.reg (r 27) = (BinaryField.inverseIndex ell h a).val ∧
      (∀ i,i = 0 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ tapeData e.store = tapeData d := by
  obtain ⟨t,e,ht,he,hes,hbound⟩ := inverse_stops_exact r hr inp M hM d hd
  refine ⟨t,e,ht,he,hes,?_,?_,?_,hbound,?_⟩
  · change e.store.reg (r 27) = _
    rw [hes];exact inverseResult_index_nonzero r hr ell h a d hs ha0
  · intro i hi
    change e.store.reg (r i) = _
    rw [hes];exact inverseResult_input r hr d i hi
  · intro j hj
    change e.store.reg j = _
    rw [hes];exact inverseResult_outside r d j hj
  · rw [hes];exact inverseResult_tapeData r d

theorem inverseIndex_zero (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell)) (ha0 : a.val = 0) :
    (BinaryField.inverseIndex ell h a).val = 0 := by
  have ha : a = ⟨0,Nat.two_pow_pos ell⟩ := Fin.ext ha0
  rw [ha,BinaryField.inverseIndex,indexEquiv_zero]
  unfold BinaryField.inverse
  rw [dif_pos rfl,← indexEquiv_zero ell,Equiv.symm_apply_apply]

theorem inverseTest_zero (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell)) (ha0 : a.val = 0) (b : ℕ) :
    inverseTest ell h a b = false := by
  unfold inverseTest
  split
  · rename_i hb
    apply decide_eq_false
    intro hp
    have he := (multiplyIndex_one_iff ell h a ⟨b,hb⟩).mp hp
    have hd := congrArg (BinaryField.decode ell h) he
    rw [BinaryField.decode_multiply,BinaryField.decode_one] at hd
    have ha : a = ⟨0,Nat.two_pow_pos ell⟩ := Fin.ext ha0
    rw [ha,indexEquiv_zero,BinaryField.decode_zero,zero_mul] at hd
    exact zero_ne_one hd
  · rfl

theorem inverseBodyStore_output_zero (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (d : TapeStore R B) (hs : InverseSetup r ell h a d) (hc : d.reg (r 1) < 2^ell)
    (ha0 : a.val = 0) : (inverseBodyStore r d).reg (r 27) = d.reg (r 27) := by
  let c₁ := multiplyResult (inverseMultiplyLayout r) d
  let c₂ := isOneStore (r 20) (r 6) c₁
  rcases hs with ⟨ha,hm,hN,hq,hQ⟩
  have hp : c₁.reg (r 20) = (BinaryField.multiplyIndex ell h (selectedIndex ell h)
      (indexEquiv ell a) (indexEquiv ell ⟨d.reg (r 1),hc⟩)).val :=
    multiplyResult_index (inverseMultiplyLayout r) (inverseMultiplyLayout_injective r hr) ell h
      (selectedIndex ell h) a ⟨d.reg (r 1),hc⟩ d ha rfl hm hN hq hQ
  have hn : c₁.reg (r 20) ≠ 1 := by
    intro hh
    have ht : inverseTest ell h a (d.reg (r 1)) = true := by simp [inverseTest,hc,← hp,hh]
    rw [inverseTest_zero ell h a ha0] at ht
    contradiction
  have hf : c₂.reg (r 6) = 0 := by rw [isOneStore_flag _ _ (hr.ne (by decide))];simp [hn]
  change ((commitStore (inverseCommitLayout r) c₂).setReg (r 1) _).reg (r 27) = _
  simp only [reg_set31 r hr,show (27:Fin 31) ≠ 1 from by decide,ite_false]
  simp only [commitStore,show inverseCommitLayout r 4 = r 6 from rfl,hf,if_pos rfl,ite_true]
  rw [isOneStore_fresh _ _ _ _ (hr.ne (by decide)) (hr.ne (by decide))]
  exact inverseMultiply_preserves r hr d 27 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))

theorem inverseFold_output_zero (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (n : ℕ) (d : TapeStore R B) (hs : InverseSetup r ell h a d)
    (hc : d.reg (r 1)+n ≤ 2^ell) (ha0 : a.val = 0) :
    (inverseFold r n d).reg (r 27) = d.reg (r 27) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    let c := d.setReg (r 30) n
    have hsetup := inverseSetup_setReg r hr ell h a d n hs
    have hc1 : c.reg (r 1) = d.reg (r 1) := by simp [c,reg_set31 r hr]
    change (inverseFold r n (inverseBodyStore r c)).reg (r 27) = _
    rw [ih (inverseBodyStore r c) (inverseBodyStore_setup r hr ell h a c hsetup)
      (by rw [inverseBodyStore_index r hr c,hc1];omega),
      inverseBodyStore_output_zero r hr ell h a c hsetup (by omega) ha0]
    simp [c,reg_set31 r hr]

theorem inverseResult_index (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (d : TapeStore R B) (hs : InverseSetup r ell h a d) :
    (inverseResult r d).reg (r 27) = (BinaryField.inverseIndex ell h a).val := by
  by_cases ha0 : a.val = 0
  · have hp : InverseSetup r ell h a (inversePrepareStore r d) := by
      simpa [InverseSetup,inversePrepareStore_reg r hr] using hs
    rw [inverseIndex_zero ell h a ha0,inverseResult,hs.2.2.2.1,
      inverseFold_output_zero r hr ell h a _ _ hp (by simp [inversePrepareStore_reg r hr]) ha0,
      inversePrepareStore_reg r hr]
    simp
  · exact inverseResult_index_nonzero r hr ell h a d hs ha0

/-- Total physical-source inverse, including the canonical zero-to-zero case. -/
theorem inverse_stops (r : Fin 31 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell)) (M : ℕ) (hM : 1 ≤ M)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hs : InverseSetup r ell h a d) :
    ∃ t e,t ≤ 20000*(M+1)^7 ∧ (inverse r).Stops inp (d.toCfg (inverse (B:=B) r).entry) t e ∧
      e.store = inverseResult r d ∧ e.reg (r 27) = (BinaryField.inverseIndex ell h a).val ∧
      (∀ i,i = 0 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ tapeData e.store = tapeData d := by
  obtain ⟨t,e,ht,he,hes,hbound⟩ := inverse_stops_exact r hr inp M hM d hd
  refine ⟨t,e,ht,he,hes,?_,?_,?_,hbound,?_⟩
  · change e.store.reg (r 27) = _
    rw [hes];exact inverseResult_index r hr ell h a d hs
  · intro i hi
    change e.store.reg (r i) = _
    rw [hes];exact inverseResult_input r hr d i hi
  · intro j hj
    change e.store.reg j = _
    rw [hes];exact inverseResult_outside r d j hj
  · rw [hes];exact inverseResult_tapeData r d

#print axioms inverse_stops
#print axioms inverseResult_index
#print axioms inverse_stops_nonzero
#print axioms inverseResult_index_nonzero
#print axioms inverse_stops_exact
#print axioms addition_stops
#print axioms addition_stops_exact
#print axioms multiply_stops
#print axioms multiplyResult_index
#print axioms multiplyResult_answer
#print axioms multiply_stops_exact
#print axioms outerLoop_stops
#print axioms innerLoop_stops
#print axioms loop_stops
#print axioms commit_stops
#print axioms accepted_remainder_unique
end ExpandingCodes.Computation.SourceFieldArithmetic
