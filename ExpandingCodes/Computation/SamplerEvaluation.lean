import ExpandingCodes.Computation.TapeArrays
import ExpandingCodes.Computation.TapeControl
import ExpandingCodes.Computation.ParameterPrograms
import ExpandingCodes.Computation.PolynomialBounds
import ExpandingCodes.Computation.FieldPrograms
import ExpandingCodes.Computation.SourceFieldArithmetic

set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace SamplerEvaluation
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

theorem reg_layout {L : ℕ} (r : Fin L → Fin R) (hr : Function.Injective r)
    (s : TapeStore R B) (i j : Fin L) (v : ℕ) :
    (s.setReg (r i) v).reg (r j)=if j=i then v else s.reg (r j) := by
  simp [TapeStore.setReg,Function.update,hr.eq_iff]

/-- A physical copy with its caller-counter bound. This does not touch any
buffer, head, output, or register outside destination/scratch. -/
theorem copy_stops_bound (src dst tmp : Fin R)
    (hsd : src≠dst) (hst : src≠tmp) (hdt : dst≠tmp)
    (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j       ≤       M) :
    ∃ t e, t       ≤       7*M+7 ∧
      (TapeMacros.copy src dst tmp).Stops inp
        (s.toCfg (TapeMacros.copy (B := B) src dst tmp).entry) t e ∧
      e.store=(s.setReg dst (s.reg src)).setReg tmp 0 ∧ ∀ j,e.reg j       ≤       M := by
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops src dst tmp hsd hst hdt inp s
  refine ⟨_,e,?_,he,hes,?_⟩
  · have h₁ := hs src; have h₂ := hs dst; have h₃ := hs tmp; omega
  · change ∀ j,e.store.reg j       ≤       M
    rw [hes]
    exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hs (hs src)) (by omega)

/-- Indexed field/hash table read preserving the caller's runtime width.
Layout: index0, width1, consumed-width2, offset3, tmp4, count5, value6,
copy-scratch7. All operations are the physical TapeArrays routines. -/
def lookup (r : Fin 8 → Fin R) (b : Fin B) : TapeProgram R B 48 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.copy (r 1) (r 2) (r 7))
    (TapeMacros.clear (r 6))) (TapeArrays.readEntry (r 0) (r 2) (r 3) (r 4) (r 5) (r 6) b)

def lookupPrepare (r : Fin 8 → Fin R) (s : TapeStore R B) : TapeStore R B :=
  ((s.setReg (r 2) (s.reg (r 1))).setReg (r 7) 0).setReg (r 6) 0

def lookupRegisters (r : Fin 8 → Fin R) (v : ℕ) (s : TapeStore R B) : Fin R → ℕ :=
  ((((((s.setReg (r 2) 0).setReg (r 3) 0).setReg (r 4) 0).setReg (r 5) 0).setReg (r 6) v).setReg (r 7) 0).reg

theorem lookupPrepare_bound (r : Fin 8 → Fin R) (s : TapeStore R B)
    (M : ℕ) (hs : ∀ j,s.reg j       ≤       M) : ∀ j,(lookupPrepare r s).reg j       ≤       M := by
  apply setReg_bound
  · exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hs (hs (r 1))) (by omega)
  · omega

/-- Actual 48-label source lookup. The index and original width counters remain
available to the caller; the physical buffer head ends after the selected block. -/
theorem lookup_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ j,s.reg j       ≤       M) (hh : s.bufferHead b       ≤       M)
    (hm : TapeArrays.Marked s b) (v : ℕ)
    (hv : TapeArrays.ThermometerAt s b
      (TapeArrays.entryOffset (s.reg (r 0)) (s.reg (r 1))) (s.reg (r 1)) v) :
    ∃ t e, t       ≤       64*(M+1)^2 ∧
      (lookup r b).Stops inp (s.toCfg (lookup (B := B) r b).entry) t e ∧
      e.reg=lookupRegisters r v s ∧
      e.reg (r 6)=v ∧ e.reg (r 0)=s.reg (r 0) ∧ e.reg (r 1)=s.reg (r 1) ∧
      (∀ j,(∀ i : Fin 8,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j       ≤       M) ∧
      e.bufferHead=Function.update s.bufferHead b
        (TapeArrays.entryOffset (s.reg (r 0)) (s.reg (r 1))+s.reg (r 1)) ∧
      TapeStore.SamePayload e.store s := by
  obtain ⟨a,c,ha,hc,hcs,hcb⟩ := copy_stops_bound (r 1) (r 2) (r 7)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M s hs
  have hclear := TapeMacros.clear_stops (r 6) inp (c.reg (r 6)) c.store rfl
  have hpre : c.store.setReg (r 6) 0=lookupPrepare r s := by rw [hcs]; rfl
  have hpb := lookupPrepare_bound r s M hs
  have hpm : TapeArrays.Marked (lookupPrepare r s) b := hm
  have hpv : (lookupPrepare r s).reg (r 6)=0 := by simp [lookupPrepare]
  have hidx : (lookupPrepare r s).reg (r 0)=s.reg (r 0) := by
    simp [lookupPrepare,reg_layout r hr]
  have hwidth : (lookupPrepare r s).reg (r 2)=s.reg (r 1) := by
    simp [lookupPrepare,reg_layout r hr]
  have hpblock : TapeArrays.ThermometerAt (lookupPrepare r s) b
      (TapeArrays.entryOffset ((lookupPrepare r s).reg (r 0)) ((lookupPrepare r s).reg (r 2)))
      ((lookupPrepare r s).reg (r 2)) v := by rw [hidx,hwidth]; exact hv
  obtain ⟨btime,e,hbt,he,her,heh,hep⟩ := TapeArrays.readEntry_stops
    (r 0) (r 2) (r 3) (r 4) (r 5) (r 6)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    b inp (lookupPrepare r s) hpm hpv v hpblock
  have hlarge := TapeArrays.entryAccessBound_le (lookupPrepare r s)
    (r 0) (r 2) (r 3) (r 4) (r 5) b M
    (hpb _) (hpb _) (hpb _) (hpb _) (hpb _) hh
  have hreg : e.reg=lookupRegisters r v s := by
    rw [her]
    unfold lookupPrepare lookupRegisters
    funext j
    simp only [TapeStore.setReg]
    by_cases h₂ : j=r 2
    · subst j; simp [Function.update,hr.eq_iff]
    by_cases h₃ : j=r 3
    · subst j; simp [Function.update,hr.eq_iff]
    by_cases h₄ : j=r 4
    · subst j; simp [Function.update,hr.eq_iff]
    by_cases h₅ : j=r 5
    · subst j; simp [Function.update,hr.eq_iff]
    by_cases h₆ : j=r 6
    · subst j; simp [Function.update,hr.eq_iff]
    by_cases h₇ : j=r 7
    · subst j; simp [Function.update,hr.eq_iff]
    simp [Function.update,h₂,h₃,h₄,h₅,h₆,h₇]
  rw [← hpre] at he
  have hall := (hc.seq hclear).seq he
  refine ⟨a+1+(c.reg (r 6)+1)+1+btime,_,?_,hall,hreg,?_,?_,?_,?_,?_,?_,?_⟩
  · have hc₆ := hcb (r 6)
    nlinarith
  · rw [hreg]; simp [lookupRegisters,reg_layout r hr]
  · rw [hreg]; simp [lookupRegisters,reg_layout r hr]
  · rw [hreg]; simp [lookupRegisters,reg_layout r hr]
  · intro j hj; rw [hreg]; simp [lookupRegisters,TapeStore.setReg,hj]
  · intro j
    rw [hreg]
    unfold lookupRegisters
    apply setReg_bound
    · apply setReg_bound
      · apply setReg_bound
        · apply setReg_bound
          · apply setReg_bound
            · exact setReg_bound s _ 0 M hs (by omega)
            · omega
          · omega
        · omega
      · exact hv.1.trans (hs (r 1))
    · omega
  · rw [hidx,hwidth] at heh
    exact heh
  · exact hep.trans ⟨rfl,rfl,fun _ _ => rfl⟩

/-- Shared physical field workspace occupies 0..26. External operands are27,28
and output29. Addition remaps its preserved second-input register directly to
external operand28, leaving the multiplication modulus in register3 untouched. -/
def fieldLayout (r : Fin 30 → Fin R) (i : Fin 27) : Fin R :=
  r ⟨i.val,by omega⟩

def additionLayout (r : Fin 30 → Fin R) (i : Fin 27) : Fin R :=
  if i=3 then r 28 else fieldLayout r i

theorem fieldLayout_injective (r : Fin 30 → Fin R) (hr : Function.Injective r) :
    Function.Injective (fieldLayout r) := by
  intro i j h
  have hh := congrArg Fin.val (hr h)
  exact Fin.ext hh

theorem additionLayout_injective (r : Fin 30 → Fin R) (hr : Function.Injective r) :
    Function.Injective (additionLayout r) := by
  intro i j h
  by_cases hi : i=3 <;> by_cases hj : j=3
  · exact hi.trans hj.symm
  · simp only [additionLayout,if_pos hi,if_neg hj] at h
    have hh := congrArg Fin.val (hr h)
    simp only [fieldLayout,Fin.val_mk] at hh
    have := j.isLt
    omega
  · simp only [additionLayout,if_neg hi,if_pos hj] at h
    have hh := congrArg Fin.val (hr h)
    simp only [fieldLayout,Fin.val_mk] at hh
    have := i.isLt
    omega
  · simp only [additionLayout,if_neg hi,if_neg hj] at h
    exact fieldLayout_injective r hr h

/-- Actual finite field addition into an external register. Runtime field size,
bit length and polynomial modulus never occur in this source code table. -/
def addFrom (r : Fin 30 → Fin R) : TapeProgram R B 387 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.copy (r 27) (r 0) (r 2))
    (SourceFieldArithmetic.addition (additionLayout r))) (TapeMacros.copy (r 20) (r 29) (r 2))

theorem addFrom_stops (r : Fin 30 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (a b : Fin (2^ell))
    (M : ℕ) (hM : 1       ≤       M) (s : TapeStore R B) (hs : ∀ j,s.reg j       ≤       M)
    (ha : s.reg (r 27)=a.val) (hb : s.reg (r 28)=b.val)
    (hN : s.reg (r 19)=3*ell+1) (hq : s.reg (r 23)=2^ell) :
    ∃ t e, t       ≤       3100*(M+1)^5 ∧
      (addFrom r).Stops inp (s.toCfg (addFrom (B := B) r).entry) t e ∧
      e.reg (r 29)=(ExpandingCodes.PolynomialStretch.BinaryField.addIndex ell a b).val ∧
      (∀ i : Fin 30,i=3 ∨ i=19 ∨ i=23 ∨ i=24 ∨ i=27 ∨ i=28 → e.reg (r i)=s.reg (r i)) ∧
      (∀ j,(∀ i : Fin 30,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j       ≤       M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨u,c,hu,hc,hcs,hcb⟩ := copy_stops_bound (r 27) (r 0) (r 2)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M s hs
  have hcval (i : Fin 30) : c.reg (r i)=if i=0 then s.reg (r 27) else if i=2 then 0 else s.reg (r i) := by
    change c.store.reg (r i)=_
    rw [hcs]
    simp [reg_layout r hr]
    split <;> split <;> simp_all
  obtain ⟨v,d,hv,hd,hds,hdv,hdi,hdo,hdb,hdt⟩ := SourceFieldArithmetic.addition_stops
    (additionLayout r) (additionLayout_injective r hr) inp ell a b M hM c.store hcb
    (by simpa [additionLayout,fieldLayout,hcval] using ha)
    (by simpa [additionLayout,fieldLayout,hcval] using hb)
    (by simpa [additionLayout,fieldLayout,hcval] using hN)
    (by simpa [additionLayout,fieldLayout,hcval] using hq)
  obtain ⟨w,e,hw,he,hes,heb⟩ := copy_stops_bound (r 20) (r 29) (r 2)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M d.store hdb
  have hall := (hc.seq hd).seq he
  have hd20 : d.reg (r 20)=(ExpandingCodes.PolynomialStretch.BinaryField.addIndex ell a b).val := by
    simpa [additionLayout,fieldLayout] using hdv
  have heval (i : Fin 30) : e.reg (r i)=if i=29 then d.reg (r 20) else if i=2 then 0 else d.reg (r i) := by
    change e.store.reg (r i)=_
    rw [hes]
    simp [reg_layout r hr]
    split <;> split <;> simp_all
  have houtside (i : Fin 30) (hi : i=3 ∨ i=27) :
      ∀ j : Fin 27,r i≠additionLayout r j := by
    intro j hj
    by_cases h3 : j=3
    · rw [additionLayout,if_pos h3] at hj
      have hval := congrArg Fin.val (hr hj)
      rcases hi with rfl|rfl <;> simp at hval
    · rw [additionLayout,if_neg h3] at hj
      have hval := congrArg Fin.val (hr hj)
      rcases hi with rfl|rfl
      · have heq : j=3 := Fin.ext (by simpa [fieldLayout] using hval.symm)
        exact h3 heq
      · have := j.isLt
        simp only [fieldLayout,Fin.val_mk] at hval
        omega
  refine ⟨u+1+v+1+w,_,?_,hall,?_,?_,?_,heb,?_⟩
  · have hp : M+1       ≤       (M+1)^5 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1       ≤       5 by decide)
    omega
  · rw [heval]; simp [hd20]
  · intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · rw [heval]; simp only [show (3:Fin 30)≠29 by decide,show (3:Fin 30)≠2 by decide,if_false]
      rw [hdo (r 3) (houtside 3 (Or.inl rfl))]
      change c.reg (r 3)=_
      simp [hcval]
    · have hh := hdi 19 (by decide) (by decide)
      simpa [heval,additionLayout,fieldLayout,hcval] using hh
    · have hh := hdi 23 (by decide) (by decide)
      simpa [heval,additionLayout,fieldLayout,hcval] using hh
    · have hh := hdi 24 (by decide) (by decide)
      simpa [heval,additionLayout,fieldLayout,hcval] using hh
    · rw [heval]; simp only [show (27:Fin 30)≠29 by decide,show (27:Fin 30)≠2 by decide,if_false]
      rw [hdo (r 27) (houtside 27 (Or.inr rfl))]
      change c.reg (r 27)=_
      simp [hcval]
    · have hh := hdi 3 (by decide) (by decide)
      simpa [heval,additionLayout,fieldLayout,hcval] using hh
  · intro j hj
    change e.store.reg j=_
    rw [hes]
    simp only [TapeStore.setReg,Function.update_of_ne (hj 2),Function.update_of_ne (hj 29)]
    have hjadd : ∀ i : Fin 27,j≠additionLayout r i := by
      intro i
      by_cases hi : i=3
      · simpa [additionLayout,hi] using hj 28
      · simpa [additionLayout,hi,fieldLayout] using hj ⟨i.val,by omega⟩
    rw [hdo j hjadd]
    change c.store.reg j=_
    rw [hcs]
    simp [TapeStore.setReg,hj]
  · change FieldConvolution.tapeData e.store=_
    rw [hes]
    simpa only [FieldConvolution.tapeData_setReg,hcs,FieldConvolution.tapeData_setReg] using hdt

/-- Actual finite field multiplication into an external register. -/
def multiplyFrom (r : Fin 30 → Fin R) : TapeProgram R B 407 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeMacros.copy (r 27) (r 0) (r 2)) (TapeMacros.copy (r 28) (r 1) (r 2)))
      (SourceFieldArithmetic.multiply (fieldLayout r))) (TapeMacros.copy (r 20) (r 29) (r 2))

theorem multiplyFrom_stops (r : Fin 30 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (m a b : Fin (2^ell))
    (M : ℕ) (hM : 1       ≤       M) (s : TapeStore R B) (hs : ∀ j,s.reg j       ≤       M)
    (ha : s.reg (r 27)=a.val) (hb : s.reg (r 28)=b.val)
    (hm : s.reg (r 3)=2^ell+m.val) (hN : s.reg (r 19)=3*ell+1)
    (hq : s.reg (r 23)=2^ell) (hQ : s.reg (r 24)=2^(2*ell)) :
    ∃ t e, t       ≤       10100*(M+1)^6 ∧
      (multiplyFrom r).Stops inp (s.toCfg (multiplyFrom (B := B) r).entry) t e ∧
      e.reg (r 29)=(ExpandingCodes.PolynomialStretch.BinaryField.multiplyIndex ell h m
        (ExpandingCodes.PolynomialStretch.BinaryPolynomial.indexEquiv ell a)
        (ExpandingCodes.PolynomialStretch.BinaryPolynomial.indexEquiv ell b)).val ∧
      (∀ i : Fin 30,i=3 ∨ i=19 ∨ i=23 ∨ i=24 ∨ i=27 ∨ i=28 → e.reg (r i)=s.reg (r i)) ∧
      (∀ j,(∀ i : Fin 30,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j       ≤       M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨u,c,hu,hc,hcs,hcb⟩ := copy_stops_bound (r 27) (r 0) (r 2)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M s hs
  obtain ⟨v,f,hv,hf,hfs,hfb⟩ := copy_stops_bound (r 28) (r 1) (r 2)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M c.store hcb
  have hfval (i : Fin 30) : f.reg (r i)=
      if i=1 then s.reg (r 28) else if i=2 then 0 else if i=0 then s.reg (r 27) else s.reg (r i) := by
    change f.store.reg (r i)=_
    rw [hfs,hcs]
    by_cases h₁ : i=1 <;> by_cases h₂ : i=2 <;> by_cases h₀ : i=0 <;>
      simp_all [reg_layout r hr]
  obtain ⟨vtime,d,hvt,hd,hds,hdv,hdi,hdo,hdb,hdt⟩ := SourceFieldArithmetic.multiply_stops
    (fieldLayout r) (fieldLayout_injective r hr) inp ell h m a b M hM f.store hfb
    (by simpa [fieldLayout,hfval] using ha)
    (by simpa [fieldLayout,hfval] using hb)
    (by simpa [fieldLayout,hfval] using hm)
    (by simpa [fieldLayout,hfval] using hN)
    (by simpa [fieldLayout,hfval] using hq)
    (by simpa [fieldLayout,hfval] using hQ)
  obtain ⟨w,e,hw,he,hes,heb⟩ := copy_stops_bound (r 20) (r 29) (r 2)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M d.store hdb
  have hall := ((hc.seq hf).seq hd).seq he
  have hd20 : d.reg (r 20)=(ExpandingCodes.PolynomialStretch.BinaryField.multiplyIndex ell h m
        (ExpandingCodes.PolynomialStretch.BinaryPolynomial.indexEquiv ell a)
        (ExpandingCodes.PolynomialStretch.BinaryPolynomial.indexEquiv ell b)).val := by
    simpa [fieldLayout] using hdv
  have heval (i : Fin 30) : e.reg (r i)=if i=29 then d.reg (r 20) else if i=2 then 0 else d.reg (r i) := by
    change e.store.reg (r i)=_
    rw [hes]
    simp [reg_layout r hr]
    split <;> split <;> simp_all
  have houtside (i : Fin 30) (hi : 27        ≤        i.val) : ∀ j : Fin 27,r i≠fieldLayout r j := by
    intro j hj
    have hval := congrArg Fin.val (hr hj)
    have := j.isLt
    simp only [fieldLayout,Fin.val_mk] at hval
    omega
  refine ⟨u+1+v+1+vtime+1+w,_,?_,hall,?_,?_,?_,heb,?_⟩
  · have hp : M+1       ≤       (M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1       ≤       6 by decide)
    omega
  · rw [heval]; simp [hd20]
  · intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · have hh := hdi 3 (by decide)
      simpa [heval,fieldLayout,hfval] using hh
    · have hh := hdi 19 (by decide)
      simpa [heval,fieldLayout,hfval] using hh
    · have hh := hdi 23 (by decide)
      simpa [heval,fieldLayout,hfval] using hh
    · have hh := hdi 24 (by decide)
      simpa [heval,fieldLayout,hfval] using hh
    · rw [heval]; simp only [show (27:Fin 30)≠29 by decide,show (27:Fin 30)≠2 by decide,if_false]
      rw [hdo (r 27) (houtside 27 (by decide))]
      change f.reg (r 27)=_
      simp [hfval]
    · rw [heval]; simp only [show (28:Fin 30)≠29 by decide,show (28:Fin 30)≠2 by decide,if_false]
      rw [hdo (r 28) (houtside 28 (by decide))]
      change f.reg (r 28)=_
      simp [hfval]
  · intro j hj
    change e.store.reg j=_
    rw [hes]
    simp only [TapeStore.setReg,Function.update_of_ne (hj 2),Function.update_of_ne (hj 29)]
    have hjfield : ∀ i : Fin 27,j≠fieldLayout r i := by
      intro i
      exact hj ⟨i.val,by omega⟩
    rw [hdo j hjfield]
    change f.store.reg j=_
    rw [hfs,hcs]
    simp [TapeStore.setReg,hj]
  · change FieldConvolution.tapeData e.store=_
    rw [hes]
    simpa only [FieldConvolution.tapeData_setReg,hfs,hcs,FieldConvolution.tapeData_setReg] using hdt

def scaleLabels : ℕ → ℕ
  | 0 => 1
  | c+1 => 9+scaleLabels c

/-- A statically fixed number of preserving unary additions. Runtime radix or
address values never occur in this finite code table. -/
def scaleAdd (src dst tmp : Fin R) : (c : ℕ) → TapeProgram R B (scaleLabels c)
  | 0 => TapeProgram.skip
  | c+1 => TapeProgram.seq (TapeMacros.addPreserving src dst tmp) (scaleAdd src dst tmp c)

def scaleStore (src dst tmp : Fin R) (c : ℕ) (s : TapeStore R B) : TapeStore R B :=
  (s.setReg dst (s.reg dst+c*s.reg src)).setReg tmp 0

theorem scaleAdd_stops (src dst tmp : Fin R) (hsd : src≠dst) (hst : src≠tmp) (hdt : dst≠tmp)
    (c : ℕ) (inp : Inputs) (s : TapeStore R B) (htmp : s.reg tmp=0) :
    ∃ e, (scaleAdd src dst tmp c).Stops inp
      (s.toCfg (scaleAdd (B := B) src dst tmp c).entry) (c*(5*s.reg src+6)) e ∧
      e.store=scaleStore src dst tmp c s := by
  induction c generalizing s with
  | zero =>
    refine ⟨s.toCfg ⟨0,by simp [scaleLabels]⟩,?_,?_⟩
    · simp only [Nat.zero_mul]
      exact ⟨TapeProgram.Exec.refl _,rfl⟩
    rw [scaleStore,Nat.zero_mul,Nat.add_zero,setReg_self]
    simpa [htmp] using (setReg_self s tmp).symm
  | succ c ih =>
    obtain ⟨d,hd,hds⟩ := TapeMacros.addPreserving_stops src dst tmp hsd hst hdt inp s
    have hda : d.reg src=s.reg src := by
      change d.store.reg src=_; rw [hds]; simp [TapeStore.setReg,hsd,hst]
    have hdtm : d.reg tmp=0 := by
      change d.store.reg tmp=_; rw [hds]; simp
    obtain ⟨e,he,hes⟩ := ih d.store hdtm
    have hall := hd.seq he
    refine ⟨e.mapPC (TapeProgram.rightLabel 9),?_,?_⟩
    · have htime : s.reg tmp+5*s.reg src+5+1+c*(5*d.store.reg src+6)=
          (c+1)*(5*s.reg src+6) := by
        simp only [TapeCfg.store,hda,htmp]
        ring
      rw [htime] at hall
      exact hall
    · change e.store=_
      rw [hes,hds]
      unfold scaleStore
      simp only [TapeStore.setReg]
      congr 1
      funext j
      by_cases htmpj : j=tmp
      · subst j; simp
      by_cases hdstj : j=dst
      · subst j
        simp [Function.update,hdt,Ne.symm hdt,hsd,hst]
        ring
      · simp [Function.update,htmpj,hdstj]

theorem scaleLabels_eq (c : ℕ) : scaleLabels c=9*c+1 := by
  induction c with
  | zero => rfl
  | succ c ih => simp only [scaleLabels,ih]; omega

#print axioms scaleAdd_stops

def formIndexLabels (c d j : ℕ) : ℕ :=
  (((11+scaleLabels c)+2)+scaleLabels d)+ParameterPrograms.raiseLabels j

/-- Physical flat-form address j+d*(a+q*c), with c=i+k*row statically fixed.
Only preserving unary additions and static increments are executed. -/
def formIndex (r : Fin 5 → Fin R) (c d j : ℕ) : TapeProgram R B (formIndexLabels c d j) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeMacros.copy (r 0) (r 2) (r 4)) (scaleAdd (r 1) (r 2) (r 4) c))
      (TapeMacros.clear (r 3))) (scaleAdd (r 2) (r 3) (r 4) d)) (ParameterPrograms.raise (r 3) j)

def formIndexStore (r : Fin 5 → Fin R) (c d j : ℕ) (s : TapeStore R B) : TapeStore R B :=
  ((s.setReg (r 2) (s.reg (r 0)+c*s.reg (r 1))).setReg (r 3)
    (d*(s.reg (r 0)+c*s.reg (r 1))+j)).setReg (r 4) 0

def formIndexTime (r : Fin 5 → Fin R) (c d j : ℕ) (s : TapeStore R B) : ℕ :=
  s.reg (r 2)+s.reg (r 4)+5*s.reg (r 0)+c*(5*s.reg (r 1)+6)+s.reg (r 3)+
    d*(5*(s.reg (r 0)+c*s.reg (r 1))+6)+2*j+12

theorem formIndex_stops (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (c d j : ℕ) (inp : Inputs) (s : TapeStore R B) :
    ∃ t e, t=formIndexTime r c d j s ∧
      (formIndex r c d j).Stops inp (s.toCfg (formIndex (B := B) r c d j).entry) t e ∧
      e.store=formIndexStore r c d j s := by
  obtain ⟨e₁,h₁,hs₁⟩ := TapeMacros.copy_stops (r 0) (r 2) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp s
  have he₁ (i : Fin 5) : e₁.reg (r i)=if i=4 then 0 else if i=2 then s.reg (r 0) else s.reg (r i) := by
    change e₁.store.reg (r i)=_; rw [hs₁]; simp [reg_layout r hr]
  obtain ⟨e₂,h₂,hs₂⟩ := scaleAdd_stops (r 1) (r 2) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) c inp e₁.store (by simp [he₁])
  have he₂ (i : Fin 5) : e₂.reg (r i)=
      if i=4 then 0 else if i=2 then s.reg (r 0)+c*s.reg (r 1) else s.reg (r i) := by
    change e₂.store.reg (r i)=_; rw [hs₂]
    simp [scaleStore,reg_layout r hr,he₁]
    by_cases h₄ : i=4 <;> by_cases h₂ : i=2 <;> simp_all
  have h₃ := TapeMacros.clear_stops (r 3) inp (e₂.reg (r 3)) e₂.store rfl
  obtain ⟨e₄,h₄,hs₄⟩ := scaleAdd_stops (r 2) (r 3) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) d inp (e₂.store.setReg (r 3) 0)
    (by simp [reg_layout r hr,he₂])
  have he₄ (i : Fin 5) : e₄.reg (r i)=if i=4 then 0 else if i=3 then d*(s.reg (r 0)+c*s.reg (r 1))
      else if i=2 then s.reg (r 0)+c*s.reg (r 1) else s.reg (r i) := by
    change e₄.store.reg (r i)=_; rw [hs₄]
    simp [scaleStore,reg_layout r hr,he₂]
    by_cases h₃ : i=3 <;> by_cases h₂ : i=2 <;> by_cases h₄ : i=4 <;> simp_all
  obtain ⟨e₅,h₅,hs₅⟩ := ParameterPrograms.raise_stops (r 3) j inp e₄.store
  have hall := (((h₁.seq h₂).seq h₃).seq h₄).seq h₅
  refine ⟨_,_,?_,hall,?_⟩
  · simp [TapeCfg.store,he₁,he₂,reg_layout r hr]
    unfold formIndexTime
    omega
  · change e₅.store=_
    rw [hs₅,hs₄,hs₂,hs₁]
    unfold scaleStore formIndexStore
    simp only [TapeStore.setReg]
    congr 1
    funext i
    by_cases h₂ : i=r 2
    · subst i; simp [Function.update,hr.eq_iff]
    by_cases h₃ : i=r 3
    · subst i; simp [Function.update,hr.eq_iff]
    by_cases h₄ : i=r 4
    · subst i; simp [Function.update,hr.eq_iff]
    simp [Function.update,h₂,h₃,h₄]

theorem formIndexTime_bound (r : Fin 5 → Fin R) (c d j M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i      ≤      M) :
    formIndexTime r c d j s      ≤      (32+6*c+6*d*(c+1)+2*j)*(M+1) := by
  have h₀ := hs (r 0); have h₁ := hs (r 1); have h₂ := hs (r 2)
  have h₃ := hs (r 3); have h₄ := hs (r 4)
  have hmid : s.reg (r 0)+c*s.reg (r 1)      ≤      (c+1)*M := by
    have hc := Nat.mul_le_mul_left c h₁
    nlinarith
  have hfirst := Nat.mul_le_mul_left c (show 5*s.reg (r 1)+6      ≤      6*(M+1) by omega)
  have hsecond := Nat.mul_le_mul_left d
    (show 5*(s.reg (r 0)+c*s.reg (r 1))+6      ≤      6*(c+1)*(M+1) by nlinarith)
  unfold formIndexTime
  nlinarith

/-- Runtime unary Horner arithmetic acc := radix*acc+digit. Layout radix0,
acc1,digit2,product3,tmp4,count5. All work is explicit unary multiplication,
preserving copy and preserving addition. -/
def hornerStep (r : Fin 6 → Fin R) : TapeProgram R B 44 :=
  TapeProgram.seq (TapeProgram.seq (UnaryArithmetic.multiply (r 1) (r 0) (r 3) (r 4) (r 5))
    (TapeMacros.copy (r 3) (r 1) (r 4))) (TapeMacros.addPreserving (r 2) (r 1) (r 4))

def hornerStore (r : Fin 6 → Fin R) (s : TapeStore R B) : TapeStore R B :=
  ((((s.setReg (r 3) (s.reg (r 1)*s.reg (r 0))).setReg (r 4) 0).setReg (r 5) 0).setReg (r 1) (s.reg (r 1)*s.reg (r 0)+s.reg (r 2)))

def hornerTime (r : Fin 6 → Fin R) (s : TapeStore R B) : ℕ :=
  s.reg (r 3)+s.reg (r 5)+s.reg (r 4)+10*s.reg (r 1)*s.reg (r 0)+12*s.reg (r 0)+
    s.reg (r 1)+5*s.reg (r 2)+25

theorem hornerStep_stops (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (s : TapeStore R B) :
    ∃ t e, t     ≤     hornerTime r s ∧
      (hornerStep r).Stops inp (s.toCfg (hornerStep (B := B) r).entry) t e ∧
      e.store=hornerStore r s := by
  obtain ⟨a,c,ha,hc,hcs⟩ := UnaryArithmetic.multiply_stops (r 1) (r 0) (r 3) (r 4) (r 5)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp s
  have hcv (i : Fin 6) : c.reg (r i)=if i=5 then 0 else if i=4 then 0
      else if i=3 then s.reg (r 1)*s.reg (r 0) else s.reg (r i) := by
    change c.store.reg (r i)=_; rw [hcs]; simp [multiplyStore,reg_layout r hr]
  obtain ⟨d,hd,hds⟩ := TapeMacros.copy_stops (r 3) (r 1) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c.store
  have hdv (i : Fin 6) : d.reg (r i)=if i=4 then 0 else if i=1 then s.reg (r 1)*s.reg (r 0)
      else if i=5 then 0 else if i=3 then s.reg (r 1)*s.reg (r 0) else s.reg (r i) := by
    change d.store.reg (r i)=_; rw [hds]
    simp [reg_layout r hr,hcv]
    by_cases h₁ : i=1 <;> by_cases h₃ : i=3 <;> by_cases h₄ : i=4 <;> by_cases h₅ : i=5 <;> simp_all
  obtain ⟨e,he,hes⟩ := TapeMacros.addPreserving_stops (r 2) (r 1) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d.store
  have hall := (hc.seq hd).seq he
  refine ⟨_,_,?_,hall,?_⟩
  · simp [TapeCfg.store,hcv,hdv]
    unfold hornerTime
    nlinarith
  · change e.store=_
    rw [hes,hds,hcs]
    unfold multiplyStore hornerStore
    simp only [TapeStore.setReg]
    congr 1
    funext i
    by_cases h₁ : i=r 1
    · subst i; simp [Function.update,hr.eq_iff]
    by_cases h₃ : i=r 3
    · subst i; simp [Function.update,hr.eq_iff]
    by_cases h₄ : i=r 4
    · subst i; simp [Function.update,hr.eq_iff]
    by_cases h₅ : i=r 5
    · subst i; simp [Function.update,hr.eq_iff]
    simp [Function.update,h₁,h₃,h₄,h₅]

theorem hornerTime_bound (r : Fin 6 → Fin R) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i     ≤     M) : hornerTime r s     ≤     32*(M+1)^2 := by
  have h₀ := hs (r 0); have h₁ := hs (r 1); have h₂ := hs (r 2)
  have h₃ := hs (r 3); have h₄ := hs (r 4); have h₅ := hs (r 5)
  have hm := Nat.mul_le_mul h₁ h₀
  unfold hornerTime
  nlinarith

theorem hornerStore_bound (r : Fin 6 → Fin R) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i     ≤     M) : ∀ i,(hornerStore r s).reg i     ≤     (M+1)^2 := by
  have hm := Nat.mul_le_mul (hs (r 1)) (hs (r 0))
  unfold hornerStore
  apply FieldPrograms.setReg_bound
  · apply FieldPrograms.setReg_bound
    · apply FieldPrograms.setReg_bound
      · apply FieldPrograms.setReg_bound
        · exact fun i => (hs i).trans (by nlinarith)
        · nlinarith
      · omega
    · omega
  · have h₂ := hs (r 2); nlinarith

def hashLayout (r : Fin 8 → Fin R) (t : Fin 3) : Fin 6 → Fin R :=
  ![r 0,r 4,r ⟨t.val+1,by omega⟩,r 5,r 6,r 7]

theorem hashLayout_injective (r : Fin 8 → Fin R) (hr : Function.Injective r) (t : Fin 3) :
    Function.Injective (hashLayout r t) := by
  fin_cases t <;> intro i j hij <;> fin_cases i <;> fin_cases j <;>
    simp_all [hashLayout,hr.eq_iff]

def hashIndexLabels (i : ℕ) : ℕ := (((2+ParameterPrograms.raiseLabels i)+44)+44)+44

/-- Exact physical base-q flattening v+q*(u+q*(a+q*i)), with layer i a static
program parameter. The runtime q multiplications are all actual unary loops. -/
def hashIndex (r : Fin 8 → Fin R) (i : ℕ) : TapeProgram R B (hashIndexLabels i) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (ParameterPrograms.loadConstant (r 4) i)
    (hornerStep (hashLayout r 0))) (hornerStep (hashLayout r 1))) (hornerStep (hashLayout r 2))

def hashIndexStore (r : Fin 8 → Fin R) (i : ℕ) (s : TapeStore R B) : TapeStore R B :=
  hornerStore (hashLayout r 2) (hornerStore (hashLayout r 1)
    (hornerStore (hashLayout r 0) (s.setReg (r 4) i)))

def hashEnvelope (i M : ℕ) : ℕ → ℕ
  | 0 => M+i+1
  | t+1 => (hashEnvelope i M t+1)^2

def hashIndexTimeBound (i M : ℕ) : ℕ :=
  M+2*i+5+32*hashEnvelope i M 1+32*hashEnvelope i M 2+32*hashEnvelope i M 3

theorem hashIndexStore_value (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (i : ℕ) (s : TapeStore R B) :
    (hashIndexStore r i s).reg (r 4)=s.reg (r 3)+s.reg (r 0)*
      (s.reg (r 2)+s.reg (r 0)*(s.reg (r 1)+s.reg (r 0)*i)) := by
  simp [hashIndexStore,hornerStore,hashLayout,reg_layout r hr]
  ring

theorem hashIndexStore_input (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (i : ℕ) (s : TapeStore R B) (j : Fin 8) (hj : j.val<4) :
    (hashIndexStore r i s).reg (r j)=s.reg (r j) := by
  have h₄ : j≠4 := by intro he; subst j; omega
  have h₅ : j≠5 := by intro he; subst j; omega
  have h₆ : j≠6 := by intro he; subst j; omega
  have h₇ : j≠7 := by intro he; subst j; omega
  simp [hashIndexStore,hornerStore,hashLayout,reg_layout r hr,h₄,h₅,h₆,h₇]

theorem hashIndex_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (i : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j    ≤    M) :
    ∃ t e, t    ≤    hashIndexTimeBound i M ∧
      (hashIndex r i).Stops inp (s.toCfg (hashIndex (B := B) r i).entry) t e ∧
      e.store=hashIndexStore r i s ∧ ∀ j,e.reg j    ≤    hashEnvelope i M 3 := by
  obtain ⟨e₀,h₀,hs₀⟩ := ParameterPrograms.loadConstant_stops (r 4) i inp s
  have hb₀ : ∀ j,e₀.reg j    ≤    hashEnvelope i M 0 := by
    change ∀ j,e₀.store.reg j    ≤    _
    rw [hs₀]
    exact setReg_bound s _ i _ (fun j => (hs j).trans (by simp [hashEnvelope]; omega)) (by simp [hashEnvelope]; omega)
  obtain ⟨t₁,e₁,ht₁,h₁,hs₁⟩ := hornerStep_stops (hashLayout r 0) (hashLayout_injective r hr 0) inp e₀.store
  have hb₁ : ∀ j,e₁.reg j    ≤    hashEnvelope i M 1 := by
    change ∀ j,e₁.store.reg j    ≤    _
    rw [hs₁]
    exact hornerStore_bound _ (hashEnvelope i M 0) e₀.store hb₀
  have hbt₁ : t₁    ≤    32*hashEnvelope i M 1 := ht₁.trans (hornerTime_bound _ _ _ hb₀)
  obtain ⟨t₂,e₂,ht₂,h₂,hs₂⟩ := hornerStep_stops (hashLayout r 1) (hashLayout_injective r hr 1) inp e₁.store
  have hb₂ : ∀ j,e₂.reg j    ≤    hashEnvelope i M 2 := by
    change ∀ j,e₂.store.reg j    ≤    _
    rw [hs₂]
    exact hornerStore_bound _ (hashEnvelope i M 1) e₁.store hb₁
  have hbt₂ : t₂    ≤    32*hashEnvelope i M 2 := ht₂.trans (hornerTime_bound _ _ _ hb₁)
  obtain ⟨t₃,e₃,ht₃,h₃,hs₃⟩ := hornerStep_stops (hashLayout r 2) (hashLayout_injective r hr 2) inp e₂.store
  have hb₃ : ∀ j,e₃.reg j    ≤    hashEnvelope i M 3 := by
    change ∀ j,e₃.store.reg j    ≤    _
    rw [hs₃]
    exact hornerStore_bound _ (hashEnvelope i M 2) e₂.store hb₂
  have hbt₃ : t₃    ≤    32*hashEnvelope i M 3 := ht₃.trans (hornerTime_bound _ _ _ hb₂)
  have hall := ((h₀.seq h₁).seq h₂).seq h₃
  refine ⟨s.reg (r 4)+2*i+2+1+t₁+1+t₂+1+t₃,_,?_,hall,?_,hb₃⟩
  · have hcounter := hs (r 4)
    unfold hashIndexTimeBound
    omega
  · change e₃.store=_
    rw [hs₃,hs₂,hs₁,hs₀]
    rfl

theorem scaleStore_bound_exact (src dst tmp : Fin R) (c M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i   ≤   M) (hresult : s.reg dst+c*s.reg src   ≤   M) :
    ∀ i,(scaleStore src dst tmp c s).reg i   ≤   M := by
  exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hs hresult) (by omega)

theorem formIndexStore_bound_exact (r : Fin 5 → Fin R) (c d j M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i   ≤   M) (hmid : s.reg (r 0)+c*s.reg (r 1)   ≤   M)
    (hresult : d*(s.reg (r 0)+c*s.reg (r 1))+j   ≤   M) :
    ∀ i,(formIndexStore r c d j s).reg i   ≤   M := by
  exact setReg_bound _ _ 0 M
    (setReg_bound _ _ _ M (setReg_bound _ _ _ M hs hmid) hresult) (by omega)

theorem hornerStore_bound_exact (r : Fin 6 → Fin R) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i   ≤   M) (hresult : s.reg (r 1)*s.reg (r 0)+s.reg (r 2)   ≤   M) :
    ∀ i,(hornerStore r s).reg i   ≤   M := by
  unfold hornerStore
  apply setReg_bound
  · apply setReg_bound
    · apply setReg_bound
      · exact setReg_bound _ _ _ M hs (by omega)
      · omega
    · omega
  · exact hresult

theorem hashIndexStore_flat (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (i : ℕ) (s : TapeStore R B) :
    hashIndexStore r i s=
      ((((s.setReg (r 4) (s.reg (r 3)+s.reg (r 0)*(s.reg (r 2)+s.reg (r 0)*
        (s.reg (r 1)+s.reg (r 0)*i)))).setReg (r 5) (s.reg (r 0)*(s.reg (r 2)+s.reg (r 0)*
          (s.reg (r 1)+s.reg (r 0)*i)))).setReg (r 6) 0).setReg (r 7) 0) := by
  unfold hashIndexStore hornerStore hashLayout
  simp only [TapeStore.setReg]
  congr 1
  funext x
  by_cases h₄ : x=r 4
  · subst x; simp [Function.update,hr.eq_iff]; ring
  by_cases h₅ : x=r 5
  · subst x; simp [Function.update,hr.eq_iff]; ring
  by_cases h₆ : x=r 6
  · subst x; simp [Function.update,hr.eq_iff]
  by_cases h₇ : x=r 7
  · subst x; simp [Function.update,hr.eq_iff]
  simp [Function.update,h₄,h₅,h₆,h₇]

theorem hashIndexStore_bound_exact (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (i M : ℕ) (s : TapeStore R B) (hs : ∀ x,s.reg x   ≤   M)
    (hresult : s.reg (r 3)+s.reg (r 0)*(s.reg (r 2)+s.reg (r 0)*
      (s.reg (r 1)+s.reg (r 0)*i))   ≤   M) :
    ∀ x,(hashIndexStore r i s).reg x   ≤   M := by
  rw [hashIndexStore_flat r hr]
  exact setReg_bound _ _ 0 M (setReg_bound _ _ 0 M
    (setReg_bound _ _ _ M (setReg_bound _ _ _ M hs hresult) (by omega)) (by omega)) (by omega)

theorem hashEnvelope_polynomial (i t : ℕ) : PolynomialBound (fun M => hashEnvelope i M t) := by
  induction t with
  | zero =>
    simpa only [hashEnvelope] using (PolynomialBound.identity.add (PolynomialBound.const i)).add (PolynomialBound.const 1)
  | succ t ih =>
    simpa only [hashEnvelope] using (ih.add (PolynomialBound.const 1)).pow 2

theorem hashIndexTimeBound_polynomial (i : ℕ) : PolynomialBound (hashIndexTimeBound i) := by
  exact (((((PolynomialBound.identity.add (PolynomialBound.const (2*i))).add (PolynomialBound.const 5)).add
    ((PolynomialBound.const 32).mul (hashEnvelope_polynomial i 1))).add
      ((PolynomialBound.const 32).mul (hashEnvelope_polynomial i 2))).add
        ((PolynomialBound.const 32).mul (hashEnvelope_polynomial i 3)))

#print axioms hashIndexTimeBound_polynomial

#print axioms hashIndexStore_bound_exact
#print axioms hornerStore_bound_exact

def coefficientIndexLayout (r : Fin 12 → Fin R) : Fin 5 → Fin R := ![r 0,r 1,r 2,r 3,r 4]
def coefficientReadLayout (r : Fin 12 → Fin R) : Fin 8 → Fin R :=
  ![r 3,r 1,r 5,r 6,r 7,r 8,r 9,r 10]

theorem coefficientIndexLayout_injective (r : Fin 12 → Fin R) (hr : Function.Injective r) :
    Function.Injective (coefficientIndexLayout r) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [coefficientIndexLayout,hr.eq_iff]

theorem coefficientReadLayout_injective (r : Fin 12 → Fin R) (hr : Function.Injective r) :
    Function.Injective (coefficientReadLayout r) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [coefficientReadLayout,hr.eq_iff]

def coefficientLoadLabels (c d j : ℕ) : ℕ := (formIndexLabels c d j+48)+11

/-- Actual form-table coefficient load, including physical address arithmetic,
indexed seek/read, and copying the scalar coefficient into its caller register.
Layout a0,q1,scratch2..10,coefficient destination11. -/
def coefficientLoad (r : Fin 12 → Fin R) (b : Fin B) (c d j : ℕ) :
    TapeProgram R B (coefficientLoadLabels c d j) :=
  TapeProgram.seq (TapeProgram.seq (formIndex (coefficientIndexLayout r) c d j)
    (lookup (coefficientReadLayout r) b)) (TapeMacros.copy (r 9) (r 11) (r 10))

def coefficientAddress (r : Fin 12 → Fin R) (c d j : ℕ) (s : TapeStore R B) : ℕ :=
  d*(s.reg (r 0)+c*s.reg (r 1))+j

theorem coefficientLoad_stops (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (c d j : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i   ≤   M) (hhead : s.bufferHead b   ≤   M) (hm : TapeArrays.BottomMarked s b)
    (hmid : s.reg (r 0)+c*s.reg (r 1)   ≤   M) (hindex : coefficientAddress r c d j s   ≤   M)
    (v : ℕ) (hv : TapeArrays.ThermometerAt s b
      (TapeArrays.entryOffset (coefficientAddress r c d j s) (s.reg (r 1))) (s.reg (r 1)) v) :
    ∃ t e, t   ≤   (112+6*c+6*d*(c+1)+2*j)*(M+1)^2 ∧
      (coefficientLoad r b c d j).Stops inp (s.toCfg (coefficientLoad (B := B) r b c d j).entry) t e ∧
      e.reg (r 11)=v ∧ e.reg (r 0)=s.reg (r 0) ∧ e.reg (r 1)=s.reg (r 1) ∧
      (∀ x,(∀ i,x≠r i) → e.reg x=s.reg x) ∧ (∀ x,e.reg x   ≤   M) ∧
      e.bufferHead=Function.update s.bufferHead b
        (TapeArrays.entryOffset (coefficientAddress r c d j s) (s.reg (r 1))+s.reg (r 1)) ∧
      TapeStore.SamePayload e.store s ∧ TapeArrays.BottomMarked e.store b := by
  have hir := coefficientIndexLayout_injective r hr
  have hrr := coefficientReadLayout_injective r hr
  obtain ⟨u,e₁,hu,h₁,hs₁⟩ := formIndex_stops (coefficientIndexLayout r) hir c d j inp s
  have hv₁ (i : Fin 12) : e₁.reg (r i)=if i=4 then 0 else if i=3 then coefficientAddress r c d j s
      else if i=2 then s.reg (r 0)+c*s.reg (r 1) else s.reg (r i) := by
    change e₁.store.reg (r i)=_
    rw [hs₁]
    simp [formIndexStore,coefficientIndexLayout,reg_layout r hr,coefficientAddress]
  have hb₁ : ∀ x,e₁.reg x   ≤   M := by
    change ∀ x,e₁.store.reg x   ≤   M
    rw [hs₁]
    unfold formIndexStore
    apply setReg_bound
    · apply setReg_bound
      · apply setReg_bound
        · exact hs
        · exact hmid
      · exact hindex
    · omega
  have hp₁ : TapeStore.SamePayload e₁.store s := by rw [hs₁]; exact ⟨rfl,rfl,fun _ _ => rfl⟩
  have hh₁ : e₁.bufferHead b   ≤   M := by change e₁.store.bufferHead b   ≤   M; rw [hs₁]; exact hhead
  have hm₁ : TapeArrays.BottomMarked e₁.store b := hm.of_payload hp₁
  have hidx : e₁.store.reg ((coefficientReadLayout r) 0)=coefficientAddress r c d j s := by change e₁.reg ((coefficientReadLayout r) 0)=_; simp [coefficientReadLayout,hv₁]
  have hwidth : e₁.store.reg ((coefficientReadLayout r) 1)=s.reg (r 1) := by
    change e₁.reg ((coefficientReadLayout r) 1)=_; simp [coefficientReadLayout,hv₁]
  have hblock : TapeArrays.ThermometerAt e₁.store b
      (TapeArrays.entryOffset (e₁.store.reg ((coefficientReadLayout r) 0)) (e₁.store.reg ((coefficientReadLayout r) 1)))
      (e₁.store.reg ((coefficientReadLayout r) 1)) v := by
    rw [hidx,hwidth]
    exact hv.of_payload hp₁
  obtain ⟨w,e₂,hw,h₂,hs₂,hvalue,hidx₂,hwidth₂,hout₂,hb₂,hh₂,hp₂⟩ := lookup_stops
    (coefficientReadLayout r) hrr b inp M e₁.store hb₁ hh₁ hm₁.marked v hblock
  obtain ⟨z,e,hz,he,hes,heb⟩ := copy_stops_bound (r 9) (r 11) (r 10)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M e₂.store hb₂
  have hall := (h₁.seq h₂).seq he
  have hp : TapeStore.SamePayload e.store s := by
    have hh : TapeStore.SamePayload e.store e₂.store := by rw [hes]; exact ⟨rfl,rfl,fun _ _ => rfl⟩
    exact (hh.trans hp₂).trans hp₁
  refine ⟨u+1+w+1+z,_,?_,hall,?_,?_,?_,?_,heb,?_,hp,hm.of_payload hp⟩
  · have hpw : M+1   ≤   (M+1)^2 := by nlinarith
    have hti := formIndexTime_bound (coefficientIndexLayout r) c d j M s hs
    have hti' := hti.trans (Nat.mul_le_mul_left (32+6*c+6*d*(c+1)+2*j) hpw)
    rw [hu] at *
    nlinarith
  · change e.store.reg (r 11)=_
    rw [hes]
    simpa [reg_layout r hr,coefficientReadLayout] using hvalue
  · change e.store.reg (r 0)=_
    rw [hes]
    simp only [reg_layout r hr,show (0:Fin 12)≠10 by decide,show (0:Fin 12)≠11 by decide,if_false]
    have hne : ∀ i : Fin 8,r 0≠coefficientReadLayout r i := by
      intro i; fin_cases i <;> simp [coefficientReadLayout,hr.eq_iff]
    rw [hout₂ (r 0) hne]
    change e₁.reg (r 0)=_
    simp [hv₁]
  · change e.store.reg (r 1)=_
    rw [hes]
    simp only [reg_layout r hr,show (1:Fin 12)≠10 by decide,show (1:Fin 12)≠11 by decide,if_false]
    simpa [coefficientReadLayout,hv₁] using hwidth₂
  · intro x hx
    change e.store.reg x=_
    rw [hes]
    simp only [TapeStore.setReg,Function.update_of_ne (hx 10),Function.update_of_ne (hx 11)]
    have hne : ∀ i : Fin 8,x≠coefficientReadLayout r i := by
      intro i; fin_cases i <;> simp [coefficientReadLayout,hx]
    rw [hout₂ x hne]
    change e₁.store.reg x=_
    rw [hs₁]
    simp [formIndexStore,coefficientIndexLayout,TapeStore.setReg,hx]
  · change e.store.bufferHead=_
    rw [hes]
    change e₂.bufferHead=_
    rw [hh₂,hidx,hwidth]
    change Function.update e₁.store.bufferHead b _=_
    rw [hs₁]
    rfl

theorem hashIndexStore_fresh_write (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (i : ℕ) (s : TapeStore R B) (x : Fin R) (hx : ∀ j : Fin 8,4 ≤ j.val → x≠r j) :
    (hashIndexStore r i s).reg x=s.reg x := by
  rw [hashIndexStore_flat r hr]
  simp [TapeStore.setReg,hx 4 (by decide),hx 5 (by decide),hx 6 (by decide),hx 7 (by decide)]

theorem lookupRegisters_fresh_write (r : Fin 8 → Fin R) (v : ℕ) (s : TapeStore R B)
    (x : Fin R) (hx : ∀ j : Fin 8,2 ≤ j.val → x≠r j) : lookupRegisters r v s x=s.reg x := by
  simp [lookupRegisters,TapeStore.setReg,hx 2 (by decide),hx 3 (by decide),hx 4 (by decide),
    hx 5 (by decide),hx 6 (by decide),hx 7 (by decide)]

def hashAddress (r : Fin 8 → Fin R) (i : ℕ) (s : TapeStore R B) : ℕ :=
  s.reg (r 3)+s.reg (r 0)*(s.reg (r 2)+s.reg (r 0)*(s.reg (r 1)+s.reg (r 0)*i))

def hashedColumnLabels (i : ℕ) : ℕ := ((hashIndexLabels i+48)+11)+scaleLabels i

/-- Actual hash-table read and block-column offset. The layer number i is
static, while field size, bucket width, address digits and bucket are runtime
counter/buffer data. -/
def hashedColumn (h r : Fin 8 → Fin R) (column tmp : Fin R) (b : Fin B) (i : ℕ) :
    TapeProgram R B (hashedColumnLabels i) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (hashIndex h i) (lookup r b))
    (TapeMacros.copy (r 6) column tmp)) (scaleAdd (r 1) column tmp i)

def hashedColumnTimeBound (i M : ℕ) : ℕ :=
  hashIndexTimeBound i M+64*(M+1)^2+7*M+10+i*(5*M+6)

theorem hashedColumn_stops (h r : Fin 8 → Fin R) (hh : Function.Injective h) (hr : Function.Injective r)
    (column tmp : Fin R) (hindex : r 0=h 4)
    (hwidth : ∀ j : Fin 8,4 ≤ j.val → r 1≠h j)
    (hcv : r 6≠column) (hct : r 6≠tmp) (hcoltmp : column≠tmp)
    (hwc : r 1≠column) (hwt : r 1≠tmp)
    (b : Fin B) (i : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ x,s.reg x ≤ M) (hhead : s.bufferHead b ≤ M) (hm : TapeArrays.BottomMarked s b)
    (haddr : hashAddress h i s ≤ M) (v : ℕ) (hcolumn : v+i*s.reg (r 1) ≤ M)
    (hend : TapeArrays.entryOffset (hashAddress h i s) (s.reg (r 1))+s.reg (r 1) ≤ M)
    (hblock : TapeArrays.ThermometerAt s b (TapeArrays.entryOffset (hashAddress h i s) (s.reg (r 1))) (s.reg (r 1)) v) :
    ∃ t e, t ≤ hashedColumnTimeBound i M ∧
      (hashedColumn h r column tmp b i).Stops inp (s.toCfg (hashedColumn (B := B) h r column tmp b i).entry) t e ∧
      e.reg column=i*s.reg (r 1)+v ∧
      (∀ x,(∀ j : Fin 8,4 ≤ j.val → x≠h j) → (∀ j : Fin 8,2 ≤ j.val → x≠r j) →
        x≠column → x≠tmp → e.reg x=s.reg x) ∧
      (∀ x,e.reg x ≤ M) ∧
      e.bufferHead=Function.update s.bufferHead b
        (TapeArrays.entryOffset (hashAddress h i s) (s.reg (r 1))+s.reg (r 1)) ∧
      e.bufferHead b ≤ M ∧ TapeStore.SamePayload e.store s ∧ TapeArrays.BottomMarked e.store b := by
  obtain ⟨a,z₁,ha,h₁,hs₁,hb₁old⟩ := hashIndex_stops h hh i inp M s hs
  have hb₁ : ∀ x,z₁.reg x ≤ M := by
    change ∀ x,z₁.store.reg x ≤ M
    rw [hs₁]
    exact hashIndexStore_bound_exact h hh i M s hs haddr
  have hp₁ : TapeStore.SamePayload z₁.store s := by rw [hs₁]; exact ⟨rfl,rfl,fun _ _ => rfl⟩
  have hh₁ : z₁.bufferHead b ≤ M := by change z₁.store.bufferHead b ≤ M; rw [hs₁]; exact hhead
  have hidx₁ : z₁.store.reg (r 0)=hashAddress h i s := by
    rw [hindex,hs₁]
    exact hashIndexStore_value h hh i s
  have hw₁ : z₁.store.reg (r 1)=s.reg (r 1) := by
    rw [hs₁]
    exact hashIndexStore_fresh_write h hh i s _ hwidth
  have hblock₁ : TapeArrays.ThermometerAt z₁.store b
      (TapeArrays.entryOffset (z₁.store.reg (r 0)) (z₁.store.reg (r 1))) (z₁.store.reg (r 1)) v := by
    rw [hidx₁,hw₁]
    exact hblock.of_payload hp₁
  obtain ⟨w,z₂,hw,h₂,hs₂,hvalue,hidx₂,hwidth₂,hout₂,hb₂,hh₂,hp₂⟩ := lookup_stops r hr b inp M z₁.store
    hb₁ hh₁ (hm.of_payload hp₁).marked v hblock₁
  obtain ⟨u,z₃,hu,h₃,hs₃,hb₃⟩ := copy_stops_bound (r 6) column tmp hcv hct hcoltmp inp M z₂.store hb₂
  have hv₃ : z₃.reg column=v := by
    change z₃.store.reg column=_
    rw [hs₃]
    simpa only [TapeStore.setReg,Function.update_of_ne hcoltmp,Function.update_self] using hvalue
  have hw₃ : z₃.reg (r 1)=s.reg (r 1) := by
    change z₃.store.reg (r 1)=_
    rw [hs₃]
    simp only [TapeStore.setReg,Function.update_of_ne hwt,Function.update_of_ne hwc]
    exact hwidth₂.trans hw₁
  have ht₃ : z₃.reg tmp=0 := by change z₃.store.reg tmp=0; rw [hs₃]; simp
  obtain ⟨e,he,hes⟩ := scaleAdd_stops (r 1) column tmp hwc hwt hcoltmp i inp z₃.store ht₃
  have hall := ((h₁.seq h₂).seq h₃).seq he
  have hp : TapeStore.SamePayload e.store s := by
    have hc : TapeStore.SamePayload e.store z₂.store := by rw [hes,hs₃]; exact ⟨rfl,rfl,fun _ _ => rfl⟩
    exact (hc.trans hp₂).trans hp₁
  have hheads : e.bufferHead=Function.update s.bufferHead b
      (TapeArrays.entryOffset (hashAddress h i s) (s.reg (r 1))+s.reg (r 1)) := by
    change e.store.bufferHead=_
    rw [hes]
    change z₃.store.bufferHead=_
    rw [hs₃]
    change z₂.bufferHead=_
    rw [hh₂,hidx₁,hw₁]
    change Function.update z₁.store.bufferHead b _=_
    rw [hs₁]
    rfl
  refine ⟨a+1+w+1+u+1+i*(5*z₃.store.reg (r 1)+6),_,?_,hall,?_,?_,?_,hheads,?_,hp,hm.of_payload hp⟩
  · have hscale := Nat.mul_le_mul_left i (show 5*s.reg (r 1)+6 ≤ 5*M+6 by have := hs (r 1); omega)
    unfold hashedColumnTimeBound
    change a+1+w+1+u+1+i*(5*z₃.reg (r 1)+6) ≤ _
    rw [hw₃]
    omega
  · change e.store.reg column=_
    rw [hes]
    simp only [scaleStore,TapeStore.setReg,Function.update_of_ne hcoltmp,Function.update_self]
    change z₃.reg column+i*z₃.reg (r 1)=_
    rw [hv₃,hw₃]
    omega
  · intro x hxh hxr hxc hxt
    change e.store.reg x=_
    rw [hes]
    simp only [scaleStore,TapeStore.setReg,Function.update_of_ne hxt,Function.update_of_ne hxc]
    change z₃.store.reg x=_
    rw [hs₃]
    simp only [TapeStore.setReg,Function.update_of_ne hxt,Function.update_of_ne hxc]
    change z₂.reg x=_
    rw [hs₂,lookupRegisters_fresh_write r v z₁.store x hxr]
    change z₁.store.reg x=_
    rw [hs₁]
    exact hashIndexStore_fresh_write h hh i s x hxh
  · change ∀ x,e.store.reg x ≤ M
    rw [hes]
    apply scaleStore_bound_exact _ _ _ _ M z₃.store hb₃
    change z₃.reg column+i*z₃.reg (r 1) ≤ M
    rw [hv₃,hw₃]
    exact hcolumn
  · rw [hheads]
    simpa using hend

theorem hashedColumnTimeBound_polynomial (i : ℕ) : PolynomialBound (hashedColumnTimeBound i) := by
  exact ((((hashIndexTimeBound_polynomial i).add
    ((PolynomialBound.const 64).mul ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 2))).add
      ((PolynomialBound.const 7).mul PolynomialBound.identity)).add (PolynomialBound.const 10)).add
        ((PolynomialBound.const i).mul ((PolynomialBound.const 5).mul PolynomialBound.identity |>.add (PolynomialBound.const 6)))

#print axioms hashedColumnTimeBound_polynomial

#print axioms hashedColumn_stops

#print axioms coefficientLoad_stops

#print axioms hashIndex_stops
#print axioms hashIndexStore_value

#print axioms hornerStep_stops
#print axioms hornerTime_bound

#print axioms formIndexTime_bound

#print axioms formIndex_stops

#print axioms multiplyFrom_stops

#print axioms addFrom_stops

#print axioms lookup_stops
end SamplerEvaluation
end ExpandingCodes.Computation
