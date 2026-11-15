import ExpandingCodes.Computation.SamplerEvaluation
import ExpandingCodes.Computation.TapeControl
import ExpandingCodes.Computation.SamplerOdometer
import ExpandingCodes.Computation.SamplerLayerBounds
import ExpandingCodes.Computation.EncodedSampler

set_option autoImplicit false
namespace ExpandingCodes.Computation.SamplerProgram
open NKtLB SamplerEvaluation
open ExpandingCodes.PolynomialStretch BinaryPolynomial
open FieldPrograms UnaryArithmetic
variable {R B : ℕ}

def workspace (r : Fin 31 → Fin R) (i : Fin 30) : Fin R := r ⟨i.val,by omega⟩

theorem workspace_injective (r : Fin 31 → Fin R) (hr : Function.Injective r) :
    Function.Injective (workspace r) := by
  intro i j h
  have hh := congrArg Fin.val (hr h)
  exact Fin.ext hh

structure Environment (r : Fin 31 → Fin R) (ell : ℕ) (m : Fin (2^ell))
    (s : TapeStore R B) : Prop where
  modulus : s.reg (r 3)=2^ell+m.val
  length : s.reg (r 19)=3*ell+1
  cardinal : s.reg (r 23)=2^ell
  square : s.reg (r 24)=2^(2*ell)

theorem Environment.frame {r : Fin 31 → Fin R} {ell : ℕ} {m : Fin (2^ell)}
    {s e : TapeStore R B} (h : Environment r ell m s)
    (hf : ∀ i : Fin 31,i=3 ∨ i=19 ∨ i=23 ∨ i=24 → e.reg (r i)=s.reg (r i)) :
    Environment r ell m e := by
  constructor
  · rw [hf 3 (by decide)]; exact h.modulus
  · rw [hf 19 (by decide)]; exact h.length
  · rw [hf 23 (by decide)]; exact h.cardinal
  · rw [hf 24 (by decide)]; exact h.square

theorem Environment.setReg {r : Fin 31 → Fin R} (hr : Function.Injective r)
    {ell : ℕ} {m : Fin (2^ell)} {s : TapeStore R B} (h : Environment r ell m s)
    (j : Fin 31) (n : ℕ) (hj : j≠3 ∧ j≠19 ∧ j≠23 ∧ j≠24) :
    Environment r ell m (s.setReg (r j) n) := by
  apply h.frame
  intro i hi
  rcases hi with rfl|rfl|rfl|rfl <;> simp [reg_layout r hr,hj.1,hj.2.1,hj.2.2.1,hj.2.2.2,Ne.symm]

/-- Caller-friendly preserving copy into an arithmetic temporary. -/
theorem copy_environment (r : Fin 31 → Fin R) (hr : Function.Injective r)
    (src : Fin R) (dst : Fin 31) (hsd : src≠r dst) (hst : src≠r 2)
    (hd : dst≠2) (hdenv : dst≠3 ∧ dst≠19 ∧ dst≠23 ∧ dst≠24)
    (inp : Inputs) (ell : ℕ) (m : Fin (2^ell)) (M : ℕ)
    (s : TapeStore R B) (hs : ∀ j,s.reg j              ≤              M) (henv : Environment r ell m s) :
    ∃ t e, t              ≤              7*M+7 ∧
      (TapeMacros.copy src (r dst) (r 2)).Stops inp
        (s.toCfg (TapeMacros.copy (B := B) src (r dst) (r 2)).entry) t e ∧
      e.store=(s.setReg (r dst) (s.reg src)).setReg (r 2) 0 ∧
      (∀ j,e.reg j              ≤              M) ∧ Environment r ell m e.store := by
  obtain ⟨t,e,ht,he,hes,heb⟩ := copy_stops_bound src (r dst) (r 2)
    hsd hst (hr.ne hd) inp M s hs
  refine ⟨t,e,ht,he,hes,heb,?_⟩
  rw [hes]
  exact (henv.setReg hr dst _ hdenv).setReg hr 2 0 (by decide)

/-- A real multiply/add step of a dot product. Coefficient and point input
registers are caller data; the 31-register workspace contains only scalar
field values and bounded scratch counters. -/
def term (r : Fin 31 → Fin R) (x y : Fin R) : TapeProgram R B 849 :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeProgram.seq (TapeMacros.copy x (r 27) (r 2)) (TapeMacros.copy y (r 28) (r 2)))
      (multiplyFrom (workspace r))) (TapeMacros.copy (r 29) (r 27) (r 2)))
        (TapeMacros.copy (r 30) (r 28) (r 2))) (addFrom (workspace r)))
          (TapeMacros.copy (r 29) (r 30) (r 2))

theorem term_stops (r : Fin 31 → Fin R) (hr : Function.Injective r)
    (x y : Fin R) (hx : ∀ i,x≠r i) (hy : ∀ i,y≠r i)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (m a b c : Fin (2^ell))
    (M : ℕ) (hM : 1              ≤              M) (s : TapeStore R B) (hs : ∀ j,s.reg j              ≤              M)
    (henv : Environment r ell m s) (ha : s.reg x=a.val) (hb : s.reg y=b.val)
    (hc : s.reg (r 30)=c.val) :
    ∃ t e, t              ≤              13300*(M+1)^6 ∧
      (term r x y).Stops inp (s.toCfg (term (B := B) r x y).entry) t e ∧
      e.reg (r 30)=(BinaryField.addIndex ell
        (BinaryField.multiplyIndex ell h m (indexEquiv ell a) (indexEquiv ell b)) c).val ∧
      Environment r ell m e.store ∧
      (∀ j,(∀ i,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j              ≤              M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁,he₁⟩ := copy_environment r hr x 27 (hx _) (hx _)
    (by decide) (by decide) inp ell m M s hs henv
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂,hb₂,he₂⟩ := copy_environment r hr y 28 (hy _) (hy _)
    (by decide) (by decide) inp ell m M c₁.store hb₁ he₁
  have hv₂ (i : Fin 31) : c₂.reg (r i)=
      if i=28 then s.reg y else if i=2 then 0 else if i=27 then s.reg x else s.reg (r i) := by
    change c₂.store.reg (r i)=_
    rw [hs₂,hs₁]
    simp [TapeStore.setReg,hy 27,hy 2]
    by_cases h₂₈ : i=28 <;> by_cases h₂ : i=2 <;> by_cases h₂₇ : i=27 <;>
      simp_all [reg_layout r hr,TapeStore.setReg,Function.update,hr.eq_iff]
  have hwr := workspace_injective r hr
  obtain ⟨t₃,c₃,ht₃,h₃,ha₃,hf₃,ho₃,hb₃,hd₃⟩ := multiplyFrom_stops (workspace r) hwr
    inp ell h m a b M hM c₂.store hb₂
    (by simpa [workspace,hv₂] using ha) (by simpa [workspace,hv₂] using hb)
    he₂.modulus he₂.length he₂.cardinal he₂.square
  have he₃ : Environment r ell m c₃.store := he₂.frame (by
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact hf₃ 3 (by decide)
    · exact hf₃ 19 (by decide)
    · exact hf₃ 23 (by decide)
    · exact hf₃ 24 (by decide))
  have hc₃ : c₃.reg (r 30)=c.val := by
    rw [ho₃ (r 30) (by
      intro i heq
      have hh := congrArg Fin.val (hr heq)
      have := i.isLt
      simp only [workspace,Fin.val_mk] at hh
      omega)]
    simpa [hv₂] using hc
  obtain ⟨t₄,c₄,ht₄,h₄,hs₄,hb₄,he₄⟩ := copy_environment r hr (r 29) 27
    (hr.ne (by decide)) (hr.ne (by decide)) (by decide) (by decide) inp ell m M c₃.store hb₃ he₃
  obtain ⟨t₅,c₅,ht₅,h₅,hs₅,hb₅,he₅⟩ := copy_environment r hr (r 30) 28
    (hr.ne (by decide)) (hr.ne (by decide)) (by decide) (by decide) inp ell m M c₄.store hb₄ he₄
  have hv₅a : c₅.reg (r 27)=(BinaryField.multiplyIndex ell h m (indexEquiv ell a) (indexEquiv ell b)).val := by
    change c₅.store.reg (r 27)=_
    rw [hs₅,hs₄]
    simpa [reg_layout r hr,workspace] using ha₃
  have hv₅b : c₅.reg (r 28)=c.val := by
    change c₅.store.reg (r 28)=_
    rw [hs₅,hs₄]
    simpa [reg_layout r hr] using hc₃
  obtain ⟨t₆,c₆,ht₆,h₆,ha₆,hf₆,ho₆,hb₆,hd₆⟩ := addFrom_stops (workspace r) hwr
    inp ell (BinaryField.multiplyIndex ell h m (indexEquiv ell a) (indexEquiv ell b)) c
    M hM c₅.store hb₅ hv₅a hv₅b he₅.length he₅.cardinal
  have he₆ : Environment r ell m c₆.store := he₅.frame (by
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact hf₆ 3 (by decide)
    · exact hf₆ 19 (by decide)
    · exact hf₆ 23 (by decide)
    · exact hf₆ 24 (by decide))
  obtain ⟨t₇,e,ht₇,h₇,hs₇,hb₇,he₇⟩ := copy_environment r hr (r 29) 30
    (hr.ne (by decide)) (hr.ne (by decide)) (by decide) (by decide) inp ell m M c₆.store hb₆ he₆
  have hall := (((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆).seq h₇
  refine ⟨t₁+1+t₂+1+t₃+1+t₄+1+t₅+1+t₆+1+t₇,_,?_,hall,?_,he₇,?_,hb₇,?_⟩
  · have hp₁ : M+1              ≤              (M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1              ≤              6 by decide)
    have hp₅ : (M+1)^5              ≤              (M+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
    omega
  · change e.store.reg (r 30)=_
    rw [hs₇]
    simpa [reg_layout r hr,workspace] using ha₆
  · intro j hj
    change e.store.reg j=_
    rw [hs₇]
    simp only [TapeStore.setReg,Function.update_of_ne (hj 2),Function.update_of_ne (hj 30)]
    have hjw : ∀ i : Fin 30,j≠workspace r i := fun i => hj ⟨i.val,by omega⟩
    rw [ho₆ j hjw]
    change c₅.store.reg j=_
    rw [hs₅,hs₄]
    simp only [TapeStore.setReg,Function.update_of_ne (hj 2),Function.update_of_ne (hj 28),
      Function.update_of_ne (hj 27)]
    rw [ho₃ j hjw]
    change c₂.store.reg j=_
    rw [hs₂,hs₁]
    simp [TapeStore.setReg,hj]
  · change FieldConvolution.tapeData e.store=_
    rw [hs₇]
    simp only [FieldConvolution.tapeData_setReg]
    rw [hd₆,hs₅,hs₄]
    simp only [FieldConvolution.tapeData_setReg]
    rw [hd₃,hs₂,hs₁]
    simp only [FieldConvolution.tapeData_setReg]

def dotLabels : List (Fin R × Fin R) → ℕ
  | [] => 1
  | _::ps => dotLabels ps+849

/-- A finite, statically unrolled dot product. Tail-first execution agrees
exactly with the right-associated encoded sum, avoiding reassociation assumptions. -/
def dot (r : Fin 31 → Fin R) : (ps : List (Fin R × Fin R)) → TapeProgram R B (dotLabels ps)
  | [] => TapeProgram.skip
  | p::ps => TapeProgram.seq (dot r ps) (term r p.1 p.2)

def dotValue (ell : ℕ) (h : 0<ell) (m : Fin (2^ell)) (values : Fin R → Fin (2^ell)) :
    List (Fin R × Fin R) → Fin (2^ell) → Fin (2^ell)
  | [],c => c
  | p::ps,c => BinaryField.addIndex ell
      (BinaryField.multiplyIndex ell h m (indexEquiv ell (values p.1)) (indexEquiv ell (values p.2)))
      (dotValue ell h m values ps c)

theorem dotLabels_eq (ps : List (Fin R × Fin R)) : dotLabels ps=849*ps.length+1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [dotLabels,List.length_cons,ih]; omega

/-- Actual bounded source execution of every fixed-dimensional dot product.
The caller's inputs remain on their individual counters throughout the run. -/
theorem dot_stops (r : Fin 31 → Fin R) (hr : Function.Injective r)
    (ps : List (Fin R × Fin R)) (hp : ∀ p∈ps,(∀ i,p.1≠r i) ∧ (∀ i,p.2≠r i))
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (m c : Fin (2^ell))
    (values : Fin R → Fin (2^ell)) (M : ℕ) (hM : 1             ≤             M)
    (s : TapeStore R B) (hs : ∀ j,s.reg j             ≤             M) (henv : Environment r ell m s)
    (hv : ∀ p∈ps,s.reg p.1=(values p.1).val ∧ s.reg p.2=(values p.2).val)
    (hc : s.reg (r 30)=c.val) :
    ∃ t e, t             ≤             ps.length*(13300*(M+1)^6+1) ∧
      (dot r ps).Stops inp (s.toCfg (dot (B := B) r ps).entry) t e ∧
      e.reg (r 30)=(dotValue ell h m values ps c).val ∧ Environment r ell m e.store ∧
      (∀ j,(∀ i,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j             ≤             M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  induction ps generalizing s with
  | nil =>
    exact ⟨0,s.toCfg ⟨0,by simp [dotLabels]⟩,by simp,TapeProgram.skip_stops inp s,hc,
      henv,fun _ _ => rfl,hs,rfl⟩
  | cons p ps ih =>
    have hps : ∀ a∈ps,(∀ i,a.1≠r i) ∧ (∀ i,a.2≠r i) := fun a ha => hp a (by simp [ha])
    have hvs : ∀ a∈ps,s.reg a.1=(values a.1).val ∧ s.reg a.2=(values a.2).val :=
      fun a ha => hv a (by simp [ha])
    obtain ⟨t,d,ht,hd,hdv,hde,hdo,hdb,hdt⟩ := ih hps s hs henv hvs hc
    have hpp := hp p (by simp)
    have hvp := hv p (by simp)
    obtain ⟨u,e,hu,he,hev,hee,heo,heb,het⟩ := term_stops r hr p.1 p.2 hpp.1 hpp.2
      inp ell h m (values p.1) (values p.2) (dotValue ell h m values ps c) M hM d.store hdb hde
      (by change d.reg p.1=_; rw [hdo p.1 hpp.1]; exact hvp.1)
      (by change d.reg p.2=_; rw [hdo p.2 hpp.2]; exact hvp.2) hdv
    have hall := hd.seq he
    refine ⟨t+1+u,_,?_,hall,hev,hee,?_,heb,het.trans hdt⟩
    · change t+1+u             ≤             (ps.length+1)*(13300*(M+1)^6+1)
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · intro j hj
      exact (heo j hj).trans (hdo j hj)

#print axioms dot_stops

theorem zeroIndex_value (ell : ℕ) : (BinaryField.zeroIndex ell).val=0 := by
  rw [BinaryField.zeroIndex,BinaryPolynomial.indexEquiv_inverse_value]
  simp [BinaryField.zero]

theorem dotValue_sum (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell))
    (ps : List (Fin R × Fin R)) :
    dotValue ell h (BinaryPolynomial.selectedIndex ell h) values ps (BinaryField.zeroIndex ell)=
      (EncodedTester.sum (BinaryField.indexOperations ell h) (ps.map fun p =>
        ((BinaryField.indexOperations ell h).mul (values p.1) (values p.2),1))).1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [dotValue,List.map_cons,EncodedTester.sum,BinaryField.indexOperations,ih]

def dotFromZero (r : Fin 31 → Fin R) (ps : List (Fin R × Fin R)) :
    TapeProgram R B (2+dotLabels ps) := TapeProgram.seq (TapeMacros.clear (r 30)) (dot r ps)

/-- Actual source evaluation of the exact canonical encoded sum of products. -/
theorem dotFromZero_stops (r : Fin 31 → Fin R) (hr : Function.Injective r)
    (ps : List (Fin R × Fin R)) (hp : ∀ p∈ps,(∀ i,p.1≠r i) ∧ (∀ i,p.2≠r i))
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell))
    (M : ℕ) (hM : 1             ≤             M) (s : TapeStore R B) (hs : ∀ j,s.reg j             ≤             M)
    (henv : Environment r ell (BinaryPolynomial.selectedIndex ell h) s)
    (hv : ∀ p∈ps,s.reg p.1=(values p.1).val ∧ s.reg p.2=(values p.2).val) :
    ∃ t e, t             ≤             (ps.length+1)*(13320*(M+1)^6) ∧
      (dotFromZero r ps).Stops inp (s.toCfg (dotFromZero (B := B) r ps).entry) t e ∧
      e.reg (r 30)=(EncodedTester.sum (BinaryField.indexOperations ell h) (ps.map fun p =>
        ((BinaryField.indexOperations ell h).mul (values p.1) (values p.2),1))).1.val ∧
      Environment r ell (BinaryPolynomial.selectedIndex ell h) e.store ∧
      (∀ j,(∀ i,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j             ≤             M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  have hclear := TapeMacros.clear_stops (r 30) inp (s.reg (r 30)) s rfl
  have hb : ∀ j,(s.setReg (r 30) 0).reg j             ≤             M := setReg_bound s _ 0 M hs (by omega)
  have he := henv.setReg hr 30 0 (by decide)
  have hv' : ∀ p∈ps,(s.setReg (r 30) 0).reg p.1=(values p.1).val ∧
      (s.setReg (r 30) 0).reg p.2=(values p.2).val := by
    intro p hp'
    simpa [TapeStore.setReg,(hp p hp').1 30,(hp p hp').2 30] using hv p hp'
  obtain ⟨t,e,ht,hstop,hev,henv',hframe,heb,het⟩ := dot_stops r hr ps hp inp ell h
    (BinaryPolynomial.selectedIndex ell h) (BinaryField.zeroIndex ell) values M hM
    (s.setReg (r 30) 0) hb he hv' (by simp [zeroIndex_value])
  have hall := hclear.seq hstop
  refine ⟨s.reg (r 30)+1+1+t,_,?_,hall,?_,henv',?_,heb,het⟩
  · have hp₁ : M+1             ≤             (M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1             ≤             6 by decide)
    have hcounter := hs (r 30)
    have hfactor : 13300*(M+1)^6+1             ≤             13320*(M+1)^6 := by
      have hpos : 1             ≤             (M+1)^6 := by omega
      omega
    have htime := ht.trans (Nat.mul_le_mul_left ps.length hfactor)
    rw [Nat.add_mul,Nat.one_mul]
    omega
  · rw [← dotValue_sum ell h values ps]
    exact hev
  · intro j hj
    exact (hframe j hj).trans (by simp [TapeStore.setReg,hj 30])

/-- Actual source program for a fixed-dimensional encoded linear form. -/
def linear {d : ℕ} (r : Fin 31 → Fin R) (coeff point : Fin d → Fin R) :
    TapeProgram R B (2+dotLabels (List.ofFn (fun i => (coeff i,point i)))) :=
  dotFromZero r (List.ofFn (fun i => (coeff i,point i)))

theorem linear_stops {d : ℕ} (r : Fin 31 → Fin R) (hr : Function.Injective r)
    (coeff point : Fin d → Fin R) (hc : ∀ j i,coeff j≠r i) (hp : ∀ j i,point j≠r i)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell))
    (M : ℕ) (hM : 1            ≤            M) (s : TapeStore R B) (hs : ∀ i,s.reg i            ≤            M)
    (henv : Environment r ell (selectedIndex ell h) s)
    (hvc : ∀ j,s.reg (coeff j)=(values (coeff j)).val)
    (hvp : ∀ j,s.reg (point j)=(values (point j)).val) :
    ∃ t e, t            ≤            (d+1)*(13320*(M+1)^6) ∧
      (linear r coeff point).Stops inp (s.toCfg (linear (B := B) r coeff point).entry) t e ∧
      e.reg (r 30)=(EncodedSampler.linear (BinaryField.indexOperations ell h)
        (fun j => values (coeff j)) (fun j => values (point j))).1.val ∧
      Environment r ell (selectedIndex ell h) e.store ∧
      (∀ j,(∀ i,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j            ≤            M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  have hlist : ∀ p∈List.ofFn (fun i => (coeff i,point i)),(∀ i,p.1≠r i) ∧ (∀ i,p.2≠r i) := by
    intro p hpm
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hpm
    exact ⟨hc j,hp j⟩
  have hvlist : ∀ p∈List.ofFn (fun i => (coeff i,point i)),
      s.reg p.1=(values p.1).val ∧ s.reg p.2=(values p.2).val := by
    intro p hpm
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hpm
    exact ⟨hvc j,hvp j⟩
  have hrun := dotFromZero_stops r hr _ hlist inp ell h values M hM s hs henv hvlist
  simpa only [linear,List.length_ofFn,List.map_ofFn,Function.comp_def,EncodedSampler.linear] using hrun

#print axioms linear_stops

theorem Environment.setExternal {r : Fin 31 → Fin R} {ell : ℕ} {m : Fin (2^ell)}
    {s : TapeStore R B} (h : Environment r ell m s) (j : Fin R) (n : ℕ)
    (hj : ∀ i,j≠r i) : Environment r ell m (s.setReg j n) := by
  apply h.frame
  intro i hi
  simp [TapeStore.setReg,Ne.symm (hj i)]

def powerWorkspace (r : Fin 32 → Fin R) (i : Fin 31) : Fin R := r ⟨i.val,by omega⟩

theorem powerWorkspace_injective (r : Fin 32 → Fin R) (hr : Function.Injective r) :
    Function.Injective (powerWorkspace r) := by
  intro i j h
  have hh := congrArg Fin.val (hr h)
  exact Fin.ext hh

theorem powerOutside (r : Fin 32 → Fin R) (hr : Function.Injective r) :
    ∀ i : Fin 31,r 31≠powerWorkspace r i := by
  intro i heq
  change r (31 : Fin 32)=r ⟨i.val,by omega⟩ at heq
  have hh := congrArg (Fin.val : Fin 32 → ℕ) (hr heq)
  have := i.isLt
  simp only [Fin.val_mk] at hh
  omega

theorem add_zeroIndex_right (ell : ℕ) (h : 0<ell) (a : Fin (2^ell)) :
    BinaryField.addIndex ell a (BinaryField.zeroIndex ell)=a := by
  have hi := BinaryField.indexOperations_interpretation ell h
  apply hi.injective
  change BinaryField.elements ell h ((BinaryField.indexOperations ell h).add a
    (BinaryField.indexOperations ell h).zero)=_
  rw [hi.add,hi.zero,add_zero]

/-- One actual power multiplication. Register31 keeps the successive power;
all runtime arithmetic still executes the shared physical field routines. -/
def powerStep (r : Fin 32 → Fin R) (x : Fin R) : TapeProgram R B 862 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.clear (r 30))
    (term (powerWorkspace r) (r 31) x)) (TapeMacros.copy (r 30) (r 31) (r 2))

theorem powerStep_stops (r : Fin 32 → Fin R) (hr : Function.Injective r)
    (x : Fin R) (hx : ∀ i,x≠r i) (inp : Inputs) (ell : ℕ) (h : 0<ell)
    (a alpha : Fin (2^ell)) (M : ℕ) (hM : 1            ≤            M) (s : TapeStore R B)
    (hs : ∀ j,s.reg j            ≤            M) (henv : Environment (powerWorkspace r) ell (selectedIndex ell h) s)
    (ha : s.reg (r 31)=a.val) (hxv : s.reg x=alpha.val) :
    ∃ t e, t            ≤            13400*(M+1)^6 ∧
      (powerStep r x).Stops inp (s.toCfg (powerStep (B := B) r x).entry) t e ∧
      e.reg (r 31)=((BinaryField.indexOperations ell h).mul a alpha).val ∧
      Environment (powerWorkspace r) ell (selectedIndex ell h) e.store ∧
      (∀ j,(∀ i,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j            ≤            M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  have hwr := powerWorkspace_injective r hr
  have hclear := TapeMacros.clear_stops (r 30) inp (s.reg (r 30)) s rfl
  have hs₁ : ∀ j,(s.setReg (r 30) 0).reg j            ≤            M := setReg_bound s _ 0 M hs (by omega)
  have he₁ : Environment (powerWorkspace r) ell (selectedIndex ell h) (s.setReg (r 30) 0) :=
    henv.setReg hwr 30 0 (by decide)
  obtain ⟨t,d,ht,hd,hdv,hde,hdo,hdb,hdt⟩ := term_stops (powerWorkspace r) hwr (r 31) x
    (powerOutside r hr) (fun i => hx ⟨i.val,by omega⟩) inp ell h (selectedIndex ell h)
    a alpha (BinaryField.zeroIndex ell) M hM (s.setReg (r 30) 0) hs₁ he₁
    (by simpa [reg_layout r hr] using ha)
    (by simpa [TapeStore.setReg,hx 30] using hxv)
    (by simp [powerWorkspace,zeroIndex_value])
  obtain ⟨u,e,hu,he,hes,heb⟩ := copy_stops_bound (r 30) (r 31) (r 2)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M d.store hdb
  have hall := (hclear.seq hd).seq he
  refine ⟨s.reg (r 30)+1+1+t+1+u,_,?_,hall,?_,?_,?_,heb,?_⟩
  · have hp : M+1            ≤            (M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1            ≤            6 by decide)
    have hcounter := hs (r 30)
    omega
  · change e.store.reg (r 31)=_
    rw [hes]
    simp only [reg_layout r hr,show (31:Fin 32)≠2 by decide,if_false,if_true]
    rw [add_zeroIndex_right ell h] at hdv
    exact hdv
  · rw [hes]
    exact (hde.setExternal (r 31) _ (powerOutside r hr)).setReg hwr 2 0 (by decide)
  · intro j hj
    change e.store.reg j=_
    rw [hes]
    simp only [TapeStore.setReg,Function.update_of_ne (hj 2),Function.update_of_ne (hj 31)]
    rw [hdo j (fun i => hj ⟨i.val,by omega⟩)]
    simp [TapeStore.setReg,hj 30]
  · change FieldConvolution.tapeData e.store=_
    rw [hes]
    simpa only [FieldConvolution.tapeData_setReg] using hdt

#print axioms powerStep_stops

def powerLabels : ℕ → ℕ
  | 0 => 1
  | j+1 => 862+powerLabels j

def powerCore (r : Fin 32 → Fin R) (x : Fin R) : (j : ℕ) → TapeProgram R B (powerLabels j)
  | 0 => TapeProgram.skip
  | j+1 => TapeProgram.seq (powerStep r x) (powerCore r x j)

theorem powerCore_stops (r : Fin 32 → Fin R) (hr : Function.Injective r)
    (x : Fin R) (hx : ∀ i,x≠r i) (inp : Inputs) (ell : ℕ) (h : 0<ell)
    (alpha : Fin (2^ell)) (M : ℕ) (hM : 1            ≤            M) (j : ℕ)
    (s : TapeStore R B) (hs : ∀ i,s.reg i            ≤            M)
    (henv : Environment (powerWorkspace r) ell (selectedIndex ell h) s)
    (a : Fin (2^ell)) (ha : s.reg (r 31)=a.val) (hxv : s.reg x=alpha.val) :
    ∃ t e, t            ≤            j*(13400*(M+1)^6+1) ∧
      (powerCore r x j).Stops inp (s.toCfg (powerCore (B := B) r x j).entry) t e ∧
      e.reg (r 31)=((fun z => (BinaryField.indexOperations ell h).mul z alpha)^[j] a).val ∧
      Environment (powerWorkspace r) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → e.reg i=s.reg i) ∧
      (∀ i,e.reg i            ≤            M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  induction j generalizing s a with
  | zero =>
    exact ⟨0,s.toCfg ⟨0,by simp [powerLabels]⟩,by simp,TapeProgram.skip_stops inp s,ha,
      henv,fun _ _ => rfl,hs,rfl⟩
  | succ j ih =>
    obtain ⟨u,d,hu,hd,hdv,hde,hdo,hdb,hdt⟩ := powerStep_stops r hr x hx inp ell h a alpha M hM s hs henv ha hxv
    obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := ih d.store hdb hde
      ((BinaryField.indexOperations ell h).mul a alpha) hdv (by
        change d.reg x=_; rw [hdo x hx]; exact hxv)
    have hall := hd.seq he
    refine ⟨u+1+t,_,?_,hall,?_,hee,?_,heb,het.trans hdt⟩
    · change u+1+t            ≤            (j+1)*(13400*(M+1)^6+1)
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · simpa only [Function.iterate_succ_apply] using hev
    · intro i hi
      exact (heo i hi).trans (hdo i hi)

theorem oneIndex_value (ell : ℕ) (h : 0<ell) : (BinaryField.oneIndex ell).val=1 := by
  rw [BinaryField.oneIndex,indexEquiv_inverse_value]
  rw [Finset.sum_eq_single (⟨0,h⟩ : Fin ell)]
  · simp [BinaryField.one,ZMod.val_one_eq_one_mod]
  · intro i hi hne
    have hiz : i.val≠0 := fun he => hne (Fin.ext he)
    simp [BinaryField.one,hiz]
  · simp

theorem power_iterate (ell : ℕ) (h : 0<ell) (alpha : Fin (2^ell)) (j : ℕ) :
    (fun z => (BinaryField.indexOperations ell h).mul z alpha)^[j] (BinaryField.oneIndex ell)=
      (EncodedTester.power (BinaryField.indexOperations ell h) alpha j).1 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih]; rfl

/-- Actual fixed-exponent field power; exponent j affects finite control only. -/
def powerFromOne (r : Fin 32 → Fin R) (x : Fin R) (j : ℕ) :
    TapeProgram R B (4+powerLabels j) :=
  TapeProgram.seq (SourceFieldArithmetic.setOne (r 31)) (powerCore r x j)

theorem powerFromOne_stops (r : Fin 32 → Fin R) (hr : Function.Injective r)
    (x : Fin R) (hx : ∀ i,x≠r i) (inp : Inputs) (ell : ℕ) (h : 0<ell)
    (alpha : Fin (2^ell)) (M : ℕ) (hM : 1            ≤            M) (j : ℕ)
    (s : TapeStore R B) (hs : ∀ i,s.reg i            ≤            M)
    (henv : Environment (powerWorkspace r) ell (selectedIndex ell h) s) (hxv : s.reg x=alpha.val) :
    ∃ t e, t            ≤            (j+1)*(13420*(M+1)^6) ∧
      (powerFromOne r x j).Stops inp (s.toCfg (powerFromOne (B := B) r x j).entry) t e ∧
      e.reg (r 31)=(EncodedTester.power (BinaryField.indexOperations ell h) alpha j).1.val ∧
      Environment (powerWorkspace r) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → e.reg i=s.reg i) ∧
      (∀ i,e.reg i            ≤            M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨c,hc,hcs⟩ := SourceFieldArithmetic.setOne_stops (r 31) inp s
  have hb : ∀ i,c.reg i            ≤            M := by
    change ∀ i,c.store.reg i            ≤            M
    rw [hcs]
    exact setReg_bound s _ 1 M hs hM
  have he : Environment (powerWorkspace r) ell (selectedIndex ell h) c.store := by
    rw [hcs]
    exact henv.setExternal (r 31) 1 (powerOutside r hr)
  obtain ⟨t,e,ht,hstop,hev,henv',hframe,heb,het⟩ := powerCore_stops r hr x hx inp ell h alpha M hM j
    c.store hb he (BinaryField.oneIndex ell)
    (by rw [hcs]; simp [oneIndex_value ell h])
    (by rw [hcs]; simpa [TapeStore.setReg,hx 31] using hxv)
  have hall := hc.seq hstop
  refine ⟨s.reg (r 31)+3+1+t,_,?_,hall,?_,henv',?_,heb,?_⟩
  · have hp₁ : M+1            ≤            (M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1            ≤            6 by decide)
    have hcounter := hs (r 31)
    have hfactor : 13400*(M+1)^6+1            ≤            13420*(M+1)^6 := by omega
    have htime := ht.trans (Nat.mul_le_mul_left j hfactor)
    rw [Nat.add_mul,Nat.one_mul]
    omega
  · simpa only [power_iterate ell h alpha j] using hev
  · intro i hi
    exact (hframe i hi).trans (by rw [hcs]; simp [TapeStore.setReg,hi 31])
  · simpa only [hcs,FieldConvolution.tapeData_setReg] using het

def vectorIndex {d : ℕ} (j : Fin d) (i : Fin 12) : Fin 11 ⊕ Fin d :=
  if hi : i.val<11 then .inl ⟨i.val,hi⟩ else .inr j

def vectorLayout {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R) (j : Fin d) : Fin 12 → Fin R :=
  r ∘ vectorIndex j

theorem vectorLayout_injective {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R)
    (hr : Function.Injective r) (j : Fin d) : Function.Injective (vectorLayout r j) := by
  intro u v huv
  have heq : vectorIndex j u=vectorIndex j v := hr huv
  by_cases hu : u.val<11 <;> by_cases hv : v.val<11
  · simp only [vectorIndex,dif_pos hu,dif_pos hv] at heq
    have hvv := congrArg Fin.val (Sum.inl.inj heq)
    exact Fin.ext hvv
  · simp only [vectorIndex,dif_pos hu,dif_neg hv] at heq
    cases heq
  · simp only [vectorIndex,dif_neg hu,dif_pos hv] at heq
    cases heq
  · exact Fin.ext (by have := u.isLt; have := v.isLt; omega)

theorem vectorLayout_coefficient_fresh {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R)
    (hr : Function.Injective r) (j a : Fin d) (haj : a≠j) :
    ∀ i,r (.inr a)≠vectorLayout r j i := by
  intro i heq
  have hi : Sum.inr a=vectorIndex j i := hr heq
  unfold vectorIndex at hi
  split at hi
  · cases hi
  · exact haj (Sum.inr.inj hi)

def vectorLabels {d : ℕ} (c : ℕ) : List (Fin d) → ℕ
  | [] => 1
  | j::js => coefficientLoadLabels c d j.val+vectorLabels c js

/-- Static coefficient-vector loader. A separate caller counter stores each
coordinate, while each coefficient is found by a real physical table lookup. -/
def vectorLoad {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R) (b : Fin B) (c : ℕ) :
    (js : List (Fin d)) → TapeProgram R B (vectorLabels c js)
  | [] => TapeProgram.skip
  | j::js => TapeProgram.seq (coefficientLoad (vectorLayout r j) b c d j.val) (vectorLoad r b c js)

def vectorAddress {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R) (c : ℕ) (j : Fin d)
    (s : TapeStore R B) : ℕ := d*(s.reg (r (.inl 0))+c*s.reg (r (.inl 1)))+j.val

def vectorTimeBound (c d M : ℕ) : ℕ := (112+6*c+6*d*(c+1)+2*d)*(M+1)^2

theorem vectorLoad_stops {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R) (hr : Function.Injective r)
    (b : Fin B) (c : ℕ) (js : List (Fin d)) (hjs : js.Nodup)
    (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ i,s.reg i           ≤           M)
    (hhead : s.bufferHead b           ≤           M) (hm : TapeArrays.BottomMarked s b)
    (hmid : s.reg (r (.inl 0))+c*s.reg (r (.inl 1))           ≤           M)
    (hindex : ∀ j∈js,vectorAddress r c j s           ≤           M)
    (hend : ∀ j∈js,TapeArrays.entryOffset (vectorAddress r c j s) (s.reg (r (.inl 1)))+s.reg (r (.inl 1))           ≤           M)
    (values : Fin d → ℕ) (hvalues : ∀ j∈js,TapeArrays.ThermometerAt s b
      (TapeArrays.entryOffset (vectorAddress r c j s) (s.reg (r (.inl 1)))) (s.reg (r (.inl 1))) (values j)) :
    ∃ t e, t           ≤           js.length*(vectorTimeBound c d M+1) ∧
      (vectorLoad r b c js).Stops inp (s.toCfg (vectorLoad (B := B) r b c js).entry) t e ∧
      (∀ j∈js,e.reg (r (.inr j))=values j) ∧
      (∀ j,j∉js → e.reg (r (.inr j))=s.reg (r (.inr j))) ∧
      e.reg (r (.inl 0))=s.reg (r (.inl 0)) ∧ e.reg (r (.inl 1))=s.reg (r (.inl 1)) ∧
      (∀ x,(∀ i,x≠r i) → e.reg x=s.reg x) ∧ (∀ x,e.reg x           ≤           M) ∧ e.bufferHead b         ≤         M ∧
      (∀ b',b'≠b → e.bufferHead b'=s.bufferHead b') ∧
      TapeStore.SamePayload e.store s ∧ TapeArrays.BottomMarked e.store b := by
  induction js generalizing s with
  | nil =>
    exact ⟨0,s.toCfg ⟨0,by simp [vectorLabels]⟩,by simp,TapeProgram.skip_stops inp s,
      by simp,fun _ _ => rfl,rfl,rfl,fun _ _ => rfl,hs,hhead,(fun _ _ => rfl),TapeStore.SamePayload.refl s,hm⟩
  | cons j js ih =>
    have hjtail : j∉js := (List.nodup_cons.mp hjs).1
    have htail : js.Nodup := (List.nodup_cons.mp hjs).2
    have haddr (a : Fin d) (z : TapeStore R B) : coefficientAddress (vectorLayout r a) c d a.val z=vectorAddress r c a z := by
      simp [coefficientAddress,vectorAddress,vectorLayout,vectorIndex]
    obtain ⟨u,z,hu,hz,hzv,hza,hzq,hzo,hzb,hzh,hzp,hzm⟩ := coefficientLoad_stops
      (vectorLayout r j) (vectorLayout_injective r hr j) b c d j.val inp M s hs hhead hm hmid
      (by rw [haddr]; exact hindex j (by simp)) (values j)
      (by rw [haddr]; exact hvalues j (by simp))
    have hza' : z.reg (r (.inl 0))=s.reg (r (.inl 0)) := hza
    have hzq' : z.reg (r (.inl 1))=s.reg (r (.inl 1)) := hzq
    have hzv' : z.reg (r (.inr j))=values j := hzv
    have hzhead : z.bufferHead b           ≤           M := by
      rw [hzh]
      simpa [coefficientAddress,vectorAddress,vectorLayout,vectorIndex,Function.comp_def] using hend j (by simp)
    have hmidz : z.store.reg (r (.inl 0))+c*z.store.reg (r (.inl 1))           ≤           M := by
      change z.reg (r (.inl 0))+c*z.reg (r (.inl 1))           ≤           M
      rw [hza',hzq']; exact hmid
    have hindexz : ∀ a∈js,vectorAddress r c a z.store           ≤           M := by
      intro a ha
      simpa [vectorAddress,hza',hzq'] using hindex a (by simp [ha])
    have hendz : ∀ a∈js,TapeArrays.entryOffset (vectorAddress r c a z.store)
        (z.store.reg (r (.inl 1)))+z.store.reg (r (.inl 1))           ≤           M := by
      intro a ha
      simpa [vectorAddress,hza',hzq'] using hend a (by simp [ha])
    have hvaluesz : ∀ a∈js,TapeArrays.ThermometerAt z.store b
        (TapeArrays.entryOffset (vectorAddress r c a z.store) (z.store.reg (r (.inl 1))))
        (z.store.reg (r (.inl 1))) (values a) := by
      intro a ha
      have hh := (hvalues a (by simp [ha])).of_payload hzp
      simpa [vectorAddress,hza',hzq'] using hh
    obtain ⟨t,e,ht,he,hev,hef,hea,heq,heo,heb,heh,heheads,hep,hem⟩ := ih htail z.store hzb hzhead hzm
      hmidz hindexz hendz hvaluesz
    have hall := hz.seq he
    refine ⟨u+1+t,_,?_,hall,?_,?_,hea.trans hza',heq.trans hzq',?_,heb,heh,?_,hep.trans hzp,hem⟩
    · have htj : u           ≤           vectorTimeBound c d M := hu.trans (by
        unfold vectorTimeBound
        apply Nat.mul_le_mul_right
        have hj := j.isLt
        omega)
      change u+1+t           ≤           (js.length+1)*(vectorTimeBound c d M+1)
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl|ha
      · exact (hef _ hjtail).trans hzv'
      · exact hev a ha
    · intro a ha
      have haj : a≠j := fun he => ha (by simp [he])
      have hat : a∉js := fun he => ha (by simp [he])
      exact (hef a hat).trans (hzo (r (.inr a)) (vectorLayout_coefficient_fresh r hr j a haj))
    · intro x hx
      exact (heo x hx).trans (hzo x (fun i => hx (vectorIndex j i)))
    · intro b' hne
      exact (heheads b' hne).trans (by
        change z.bufferHead b'=s.bufferHead b'
        rw [hzh]; simp [hne])

def allCoefficients {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R) (b : Fin B) (c : ℕ) :
    TapeProgram R B (vectorLabels c (List.finRange d)) := vectorLoad r b c (List.finRange d)

theorem allCoefficients_stops {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R) (hr : Function.Injective r)
    (b : Fin B) (c : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ i,s.reg i          ≤          M)
    (hhead : s.bufferHead b          ≤          M) (hm : TapeArrays.BottomMarked s b)
    (hmid : s.reg (r (.inl 0))+c*s.reg (r (.inl 1))          ≤          M)
    (hindex : ∀ j,vectorAddress r c j s          ≤          M)
    (hend : ∀ j,TapeArrays.entryOffset (vectorAddress r c j s) (s.reg (r (.inl 1)))+s.reg (r (.inl 1))          ≤          M)
    (values : Fin d → ℕ) (hvalues : ∀ j,TapeArrays.ThermometerAt s b
      (TapeArrays.entryOffset (vectorAddress r c j s) (s.reg (r (.inl 1)))) (s.reg (r (.inl 1))) (values j)) :
    ∃ t e, t          ≤          d*(vectorTimeBound c d M+1) ∧
      (allCoefficients r b c).Stops inp (s.toCfg (allCoefficients (B := B) r b c).entry) t e ∧
      (∀ j,e.reg (r (.inr j))=values j) ∧
      e.reg (r (.inl 0))=s.reg (r (.inl 0)) ∧ e.reg (r (.inl 1))=s.reg (r (.inl 1)) ∧
      (∀ x,(∀ i,x≠r i) → e.reg x=s.reg x) ∧ (∀ x,e.reg x          ≤          M) ∧ e.bufferHead b         ≤         M ∧
      (∀ b',b'≠b → e.bufferHead b'=s.bufferHead b') ∧
      TapeStore.SamePayload e.store s ∧ TapeArrays.BottomMarked e.store b := by
  obtain ⟨t,e,ht,he,hev,hef,hea,heq,heo,heb,heh,heheads,hep,hem⟩ := vectorLoad_stops r hr b c (List.finRange d)
    (List.nodup_finRange d) inp M s hs hhead hm hmid (fun j _ => hindex j) (fun j _ => hend j) values (fun j _ => hvalues j)
  exact ⟨t,e,by simpa using ht,he,fun j => hev j (by simp),hea,heq,heo,heb,heh,heheads,hep,hem⟩

/-- Semantic interpretation of one scalar caller counter, used only in proofs;
the physical evaluator still consists solely of the finite source routines. -/
def scalarValue (ell : ℕ) (s : TapeStore R B) (i : Fin R) : Fin (2^ell) :=
  if h : s.reg i<2^ell then ⟨s.reg i,h⟩ else ⟨0,Nat.two_pow_pos ell⟩

theorem scalarValue_eq (ell : ℕ) (s : TapeStore R B) (i : Fin R) (a : Fin (2^ell))
    (ha : s.reg i=a.val) : scalarValue ell s i=a := by
  apply Fin.ext
  simp [scalarValue,ha,a.isLt]

/-- Typed caller interface for the same actual linear-form source. -/
theorem linear_stops_values {d : ℕ} (r : Fin 31 → Fin R) (hr : Function.Injective r)
    (coeff point : Fin d → Fin R) (hc : ∀ j i,coeff j≠r i) (hp : ∀ j i,point j≠r i)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (a z : Fin d → Fin (2^ell))
    (M : ℕ) (hM : 1         ≤         M) (s : TapeStore R B) (hs : ∀ i,s.reg i         ≤         M)
    (henv : Environment r ell (selectedIndex ell h) s)
    (hvc : ∀ j,s.reg (coeff j)=(a j).val) (hvp : ∀ j,s.reg (point j)=(z j).val) :
    ∃ t e, t         ≤         (d+1)*(13320*(M+1)^6) ∧
      (linear r coeff point).Stops inp (s.toCfg (linear (B := B) r coeff point).entry) t e ∧
      e.reg (r 30)=(EncodedSampler.linear (BinaryField.indexOperations ell h) a z).1.val ∧
      Environment r ell (selectedIndex ell h) e.store ∧
      (∀ j,(∀ i,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j         ≤         M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  have hac : ∀ j,scalarValue ell s (coeff j)=a j := fun j => scalarValue_eq ell s _ _ (hvc j)
  have haz : ∀ j,scalarValue ell s (point j)=z j := fun j => scalarValue_eq ell s _ _ (hvp j)
  obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := linear_stops r hr coeff point hc hp inp ell h
    (scalarValue ell s) M hM s hs henv (by intro j; rw [hac j]; exact hvc j)
    (by intro j; rw [haz j]; exact hvp j)
  refine ⟨t,e,ht,he,?_,hee,heo,heb,het⟩
  simpa only [hac,haz] using hev

#print axioms linear_stops_values

def powerField {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (i : Fin 32) : Fin R :=
  r (.inl ⟨i.val,by omega⟩)

theorem powerField_injective {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (hr : Function.Injective r) :
    Function.Injective (powerField r) := by
  intro i j heq
  have hh := Sum.inl.inj (hr heq)
  have hv := congrArg Fin.val hh
  exact Fin.ext hv

theorem powerAlpha_fresh {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (hr : Function.Injective r) :
    ∀ i,r (.inl 32)≠powerField r i := by
  intro i heq
  have hh : (32 : Fin 33)=⟨i.val,by omega⟩ := Sum.inl.inj (hr heq)
  have hv := congrArg Fin.val hh
  change (32 : ℕ)=i.val at hv
  have := i.isLt
  omega

theorem powerCoefficient_fresh {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (hr : Function.Injective r)
    (j : Fin d) : ∀ i,r (.inr j)≠powerField r i := by
  intro i heq
  have hh := hr heq
  cases hh

def powerCoefficientLabels (j : ℕ) : ℕ := (4+powerLabels j)+11

def powerCoefficient {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (j : Fin d) :
    TapeProgram R B (powerCoefficientLabels j.val) :=
  TapeProgram.seq (powerFromOne (powerField r) (r (.inl 32)) j.val)
    (TapeMacros.copy (powerField r 31) (r (.inr j)) (powerField r 2))

def powerCoefficientTimeBound (d M : ℕ) : ℕ := (d+2)*(13440*(M+1)^6)

theorem powerCoefficient_stops {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (hr : Function.Injective r)
    (j : Fin d) (inp : Inputs) (ell : ℕ) (h : 0<ell) (alpha : Fin (2^ell))
    (M : ℕ) (hM : 1         ≤         M) (s : TapeStore R B) (hs : ∀ i,s.reg i         ≤         M)
    (henv : Environment (powerWorkspace (powerField r)) ell (selectedIndex ell h) s)
    (halpha : s.reg (r (.inl 32))=alpha.val) :
    ∃ t e, t         ≤         powerCoefficientTimeBound d M ∧
      (powerCoefficient r j).Stops inp (s.toCfg (powerCoefficient (B := B) r j).entry) t e ∧
      e.reg (r (.inr j))=(EncodedTester.power (BinaryField.indexOperations ell h) alpha j.val).1.val ∧
      Environment (powerWorkspace (powerField r)) ell (selectedIndex ell h) e.store ∧
      e.reg (r (.inl 32))=s.reg (r (.inl 32)) ∧
      (∀ a,a≠j → e.reg (r (.inr a))=s.reg (r (.inr a))) ∧
      (∀ x,(∀ i,x≠r i) → e.reg x=s.reg x) ∧
      (∀ x,e.reg x         ≤         M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  have hrf := powerField_injective r hr
  obtain ⟨t,z,ht,hz,hzv,hze,hzo,hzb,hzt⟩ := powerFromOne_stops (powerField r) hrf
    (r (.inl 32)) (powerAlpha_fresh r hr) inp ell h alpha M hM j.val s hs henv halpha
  obtain ⟨u,e,hu,he,hes,heb⟩ := copy_stops_bound (powerField r 31) (r (.inr j)) (powerField r 2)
    (Ne.symm (powerCoefficient_fresh r hr j 31)) (hrf.ne (by decide)) (powerCoefficient_fresh r hr j 2)
    inp M z.store hzb
  have hall := hz.seq he
  refine ⟨t+1+u,_,?_,hall,?_,?_,?_,?_,?_,heb,?_⟩
  · have hp : M+1         ≤         (M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1         ≤         6 by decide)
    have hj : j.val+1         ≤         d+1 := by have := j.isLt; omega
    have ht' := ht.trans (Nat.mul_le_mul_right (13420*(M+1)^6) hj)
    have hfac : 13420*(M+1)^6         ≤         13440*(M+1)^6 := by omega
    have ht'' := ht'.trans (Nat.mul_le_mul_left (d+1) hfac)
    have hu' : 1+u         ≤         13440*(M+1)^6 := by omega
    unfold powerCoefficientTimeBound
    calc
      t+1+u         ≤         (d+1)*(13440*(M+1)^6)+13440*(M+1)^6 := by omega
      _=(d+2)*(13440*(M+1)^6) := by ring
  · change e.store.reg (r (.inr j))=_
    rw [hes]
    simpa only [TapeStore.setReg,Function.update_of_ne (powerCoefficient_fresh r hr j 2),Function.update_self] using hzv
  · rw [hes]
    have hf : ∀ i : Fin 31,r (.inr j)≠powerWorkspace (powerField r) i := fun i =>
      powerCoefficient_fresh r hr j ⟨i.val,by omega⟩
    exact (hze.setExternal _ _ hf).setReg (powerWorkspace_injective _ hrf) 2 0 (by decide)
  · change e.store.reg (r (.inl 32))=_
    rw [hes]
    have hcoef : r (.inl 32)≠r (.inr j) := by intro hh; have := hr hh; cases this
    simp only [TapeStore.setReg,Function.update_of_ne (powerAlpha_fresh r hr 2),Function.update_of_ne hcoef]
    exact hzo _ (powerAlpha_fresh r hr)
  · intro a haj
    change e.store.reg (r (.inr a))=_
    rw [hes]
    have hcoef : r (.inr a)≠r (.inr j) := fun hh => haj (Sum.inr.inj (hr hh))
    simp only [TapeStore.setReg,Function.update_of_ne (powerCoefficient_fresh r hr a 2),Function.update_of_ne hcoef]
    exact hzo _ (powerCoefficient_fresh r hr a)
  · intro x hx
    change e.store.reg x=_
    rw [hes]
    have htmp : x≠powerField r 2 := hx (.inl ⟨(2 : Fin 32).val,by omega⟩)
    simp only [TapeStore.setReg,Function.update_of_ne htmp,Function.update_of_ne (hx (.inr j))]
    exact hzo x (fun i => hx (.inl ⟨i.val,by omega⟩))
  · change FieldConvolution.tapeData e.store=_
    rw [hes]
    simpa only [FieldConvolution.tapeData_setReg] using hzt

#print axioms powerCoefficient_stops

def powerVectorLabels {d : ℕ} : List (Fin d) → ℕ
  | [] => 1
  | j::js => powerCoefficientLabels j.val+powerVectorLabels js

def powerVector {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) :
    (js : List (Fin d)) → TapeProgram R B (powerVectorLabels js)
  | [] => TapeProgram.skip
  | j::js => TapeProgram.seq (powerCoefficient r j) (powerVector r js)

theorem powerVector_stops {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (hr : Function.Injective r)
    (js : List (Fin d)) (hjs : js.Nodup) (inp : Inputs) (ell : ℕ) (h : 0<ell) (alpha : Fin (2^ell))
    (M : ℕ) (hM : 1         ≤         M) (s : TapeStore R B) (hs : ∀ i,s.reg i         ≤         M)
    (henv : Environment (powerWorkspace (powerField r)) ell (selectedIndex ell h) s)
    (halpha : s.reg (r (.inl 32))=alpha.val) :
    ∃ t e, t         ≤         js.length*(powerCoefficientTimeBound d M+1) ∧
      (powerVector r js).Stops inp (s.toCfg (powerVector (B := B) r js).entry) t e ∧
      (∀ j∈js,e.reg (r (.inr j))=(EncodedTester.power (BinaryField.indexOperations ell h) alpha j.val).1.val) ∧
      (∀ j,j∉js → e.reg (r (.inr j))=s.reg (r (.inr j))) ∧
      Environment (powerWorkspace (powerField r)) ell (selectedIndex ell h) e.store ∧
      e.reg (r (.inl 32))=s.reg (r (.inl 32)) ∧
      (∀ x,(∀ i,x≠r i) → e.reg x=s.reg x) ∧
      (∀ x,e.reg x         ≤         M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  induction js generalizing s with
  | nil =>
    exact ⟨0,s.toCfg ⟨0,by simp [powerVectorLabels]⟩,by simp,TapeProgram.skip_stops inp s,
      by simp,fun _ _ => rfl,henv,rfl,fun _ _ => rfl,hs,rfl⟩
  | cons j js ih =>
    have hjtail := (List.nodup_cons.mp hjs).1
    have htail := (List.nodup_cons.mp hjs).2
    obtain ⟨u,z,hu,hz,hzv,hze,hza,hzf,hzo,hzb,hzt⟩ := powerCoefficient_stops r hr j inp ell h alpha M hM s hs henv halpha
    obtain ⟨t,e,ht,he,hev,hef,hee,hea,heo,heb,het⟩ := ih htail z.store hzb hze (by
      change z.reg (r (.inl 32))=_; rw [hza]; exact halpha)
    have hall := hz.seq he
    refine ⟨u+1+t,_,?_,hall,?_,?_,hee,hea.trans hza,?_,heb,het.trans hzt⟩
    · change u+1+t         ≤         (js.length+1)*(powerCoefficientTimeBound d M+1)
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl|ha
      · exact (hef _ hjtail).trans hzv
      · exact hev a ha
    · intro a ha
      have haj : a≠j := fun he => ha (by simp [he])
      have hat : a∉js := fun he => ha (by simp [he])
      exact (hef a hat).trans (hzf a haj)
    · intro x hx
      exact (heo x hx).trans (hzo x hx)

def allPowers {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) :
    TapeProgram R B (powerVectorLabels (List.finRange d)) := powerVector r (List.finRange d)

theorem allPowers_stops {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (alpha : Fin (2^ell))
    (M : ℕ) (hM : 1         ≤         M) (s : TapeStore R B) (hs : ∀ i,s.reg i         ≤         M)
    (henv : Environment (powerWorkspace (powerField r)) ell (selectedIndex ell h) s)
    (halpha : s.reg (r (.inl 32))=alpha.val) :
    ∃ t e, t         ≤         d*(powerCoefficientTimeBound d M+1) ∧
      (allPowers r).Stops inp (s.toCfg (allPowers (B := B) r).entry) t e ∧
      (∀ j,e.reg (r (.inr j))=(EncodedTester.power (BinaryField.indexOperations ell h) alpha j.val).1.val) ∧
      Environment (powerWorkspace (powerField r)) ell (selectedIndex ell h) e.store ∧
      e.reg (r (.inl 32))=s.reg (r (.inl 32)) ∧
      (∀ x,(∀ i,x≠r i) → e.reg x=s.reg x) ∧
      (∀ x,e.reg x         ≤         M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨t,e,ht,he,hev,hef,hee,hea,heo,heb,het⟩ := powerVector_stops r hr (List.finRange d) (List.nodup_finRange d)
    inp ell h alpha M hM s hs henv halpha
  exact ⟨t,e,by simpa using ht,he,fun j => hev j (by simp),hee,hea,heo,heb,het⟩

def fixedPowerIndex {d : ℕ} : Fin 33 ⊕ Fin d → Fin 33 ⊕ (Fin d ⊕ Fin d)
  | .inl i => .inl i
  | .inr j => .inr (.inl j)

def fixedPowerLayout {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R) : Fin 33 ⊕ Fin d → Fin R :=
  r ∘ fixedPowerIndex

def fixedFieldLayout {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R) : Fin 31 → Fin R :=
  powerWorkspace (powerField (fixedPowerLayout r))

def fixedCoeff {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R) (j : Fin d) : Fin R := r (.inr (.inl j))
def fixedPoint {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R) (j : Fin d) : Fin R := r (.inr (.inr j))

theorem fixedPowerLayout_injective {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R)
    (hr : Function.Injective r) : Function.Injective (fixedPowerLayout r) := by
  intro a b hab
  have hh : fixedPowerIndex a=fixedPowerIndex b := hr hab
  cases a <;> cases b <;> simp_all [fixedPowerIndex]

theorem fixedFieldLayout_injective {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R)
    (hr : Function.Injective r) : Function.Injective (fixedFieldLayout r) :=
  powerWorkspace_injective _ (powerField_injective _ (fixedPowerLayout_injective r hr))

theorem fixedCoeff_fresh {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R)
    (hr : Function.Injective r) : ∀ j i,fixedCoeff r j≠fixedFieldLayout r i := by
  intro j i hij
  have hh := hr hij
  cases hh

theorem fixedPoint_fresh {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R)
    (hr : Function.Injective r) : ∀ j i,fixedPoint r j≠fixedFieldLayout r i := by
  intro j i hij
  have hh := hr hij
  cases hh

theorem fixedPoint_power_fresh {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R)
    (hr : Function.Injective r) : ∀ j i,fixedPoint r j≠fixedPowerLayout r i := by
  intro j i hij
  cases i with
  | inl i =>
    have hh : Sum.inr (Sum.inr j)=Sum.inl i := hr hij
    cases hh
  | inr i =>
    have hh : Sum.inr (Sum.inr j)=Sum.inr (Sum.inl i) := hr hij
    cases Sum.inr.inj hh

theorem power_linear_eq_fixed (ell : ℕ) (h : 0<ell) {d : ℕ} (alpha : Fin (2^ell)) (z : Fin d → Fin (2^ell)) :
    (EncodedSampler.linear (BinaryField.indexOperations ell h)
      (fun j => (EncodedTester.power (BinaryField.indexOperations ell h) alpha j.val).1) z).1=
        (EncodedSampler.fixed (BinaryField.indexOperations ell h) alpha z).1 := by
  have hi := BinaryField.indexOperations_interpretation ell h
  apply hi.injective
  rw [EncodedSampler.linear_decode hi,EncodedSampler.fixed_decode hi]
  simp only [EncodedTester.power_decode hi]

def fixedLabels {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R) : ℕ :=
  powerVectorLabels (List.finRange d)+(2+dotLabels (List.ofFn (fun i => (fixedCoeff r i,fixedPoint r i))))

/-- Actual fixed-form evaluator: compute the statically many powers of the
runtime layer element, then evaluate the exact encoded sum of scalar products. -/
def fixed {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R) : TapeProgram R B (fixedLabels r) :=
  TapeProgram.seq (allPowers (fixedPowerLayout r)) (linear (fixedFieldLayout r) (fixedCoeff r) (fixedPoint r))

def fixedTimeBound (d M : ℕ) : ℕ := d*(powerCoefficientTimeBound d M+1)+1+(d+1)*(13320*(M+1)^6)

theorem fixed_stops {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (alpha : Fin (2^ell)) (z : Fin d → Fin (2^ell))
    (M : ℕ) (hM : 1        ≤        M) (s : TapeStore R B) (hs : ∀ i,s.reg i        ≤        M)
    (henv : Environment (fixedFieldLayout r) ell (selectedIndex ell h) s)
    (halpha : s.reg (r (.inl 32))=alpha.val) (hz : ∀ j,s.reg (fixedPoint r j)=(z j).val) :
    ∃ t e, t        ≤        fixedTimeBound d M ∧
      (fixed r).Stops inp (s.toCfg (fixed (B := B) r).entry) t e ∧
      e.reg (r (.inl 30))=(EncodedSampler.fixed (BinaryField.indexOperations ell h) alpha z).1.val ∧
      Environment (fixedFieldLayout r) ell (selectedIndex ell h) e.store ∧
      (∀ j,e.reg (fixedPoint r j)=s.reg (fixedPoint r j)) ∧
      (∀ x,(∀ i,x≠r i) → e.reg x=s.reg x) ∧
      (∀ x,e.reg x        ≤        M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  have hpr := fixedPowerLayout_injective r hr
  have hfr := fixedFieldLayout_injective r hr
  obtain ⟨u,c,hu,hc,hcv,hce,hca,hco,hcb,hct⟩ := allPowers_stops (fixedPowerLayout r) hpr inp ell h alpha M hM s hs henv halpha
  have hpoints : ∀ j,c.reg (fixedPoint r j)=(z j).val := by
    intro j
    rw [hco _ (fixedPoint_power_fresh r hr j)]
    exact hz j
  obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := linear_stops_values (fixedFieldLayout r) hfr
    (fixedCoeff r) (fixedPoint r) (fixedCoeff_fresh r hr) (fixedPoint_fresh r hr) inp ell h
    (fun j => (EncodedTester.power (BinaryField.indexOperations ell h) alpha j.val).1) z
    M hM c.store hcb hce hcv hpoints
  have hall := hc.seq he
  refine ⟨u+1+t,_,?_,hall,?_,hee,?_,?_,heb,het.trans hct⟩
  · unfold fixedTimeBound
    omega
  · rw [power_linear_eq_fixed ell h alpha z] at hev
    exact hev
  · intro j
    exact (heo _ (fixedPoint_fresh r hr j)).trans (hco _ (fixedPoint_power_fresh r hr j))
  · intro x hx
    have hxf : ∀ i : Fin 31,x≠fixedFieldLayout r i := fun i => hx (.inl ⟨i.val,by omega⟩)
    have hxp : ∀ i : Fin 33 ⊕ Fin d,x≠fixedPowerLayout r i := fun i => hx (fixedPowerIndex i)
    exact (heo x hxf).trans (hco x hxp)

theorem tapeData_components {s e : TapeStore R B} (h : FieldConvolution.tapeData e=FieldConvolution.tapeData s) :
    e.roHead=s.roHead ∧ e.output=s.output ∧ e.bufferTape=s.bufferTape ∧ e.bufferHead=s.bufferHead := by
  simpa only [FieldConvolution.tapeData,Prod.mk.injEq] using h

theorem tapeData_payload {s e : TapeStore R B} (h : FieldConvolution.tapeData e=FieldConvolution.tapeData s) :
    TapeStore.SamePayload e s := by
  have hh := tapeData_components h
  exact ⟨hh.1,hh.2.1,fun b k => by rw [hh.2.2.1]⟩

def randomLinearLabels {d : ℕ} (v : Fin 11 ⊕ Fin d → Fin R) (point : Fin d → Fin R) (c : ℕ) : ℕ :=
  vectorLabels c (List.finRange d)+(2+dotLabels (List.ofFn (fun j => (v (.inr j),point j))))

/-- Actual runtime-addressed random linear form: load all d coefficients from
physical tape cells, then execute the finite scalar linear-form evaluator. -/
def randomLinear {d : ℕ} (v : Fin 11 ⊕ Fin d → Fin R) (f : Fin 31 → Fin R)
    (point : Fin d → Fin R) (b : Fin B) (c : ℕ) : TapeProgram R B (randomLinearLabels v point c) :=
  TapeProgram.seq (allCoefficients v b c) (linear f (fun j => v (.inr j)) point)

def randomLinearTimeBound (c d M : ℕ) : ℕ := d*(vectorTimeBound c d M+1)+1+(d+1)*(13320*(M+1)^6)

theorem randomLinear_stops {d : ℕ} (v : Fin 11 ⊕ Fin d → Fin R) (hv : Function.Injective v)
    (f : Fin 31 → Fin R) (hf : Function.Injective f) (point : Fin d → Fin R)
    (hcf : ∀ j i,v (.inr j)≠f i) (hpf : ∀ j i,point j≠f i) (hpv : ∀ j i,point j≠v i)
    (haddr : ∀ i,v (.inl 0)≠f i) (hq : f 23=v (.inl 1))
    (hmod : ∀ i,f 3≠v i) (hN : ∀ i,f 19≠v i) (hQ : ∀ i,f 24≠v i)
    (b : Fin B) (c : ℕ) (inp : Inputs) (ell : ℕ) (h : 0<ell) (a z : Fin d → Fin (2^ell))
    (M : ℕ) (hM : 1      ≤      M) (s : TapeStore R B) (hs : ∀ i,s.reg i      ≤      M)
    (henv : Environment f ell (selectedIndex ell h) s) (hz : ∀ j,s.reg (point j)=(z j).val)
    (hhead : s.bufferHead b      ≤      M) (hm : TapeArrays.BottomMarked s b)
    (hmid : s.reg (v (.inl 0))+c*s.reg (v (.inl 1))      ≤      M)
    (hindex : ∀ j,vectorAddress v c j s      ≤      M)
    (hend : ∀ j,TapeArrays.entryOffset (vectorAddress v c j s) (s.reg (v (.inl 1)))+s.reg (v (.inl 1))      ≤      M)
    (hvalues : ∀ j,TapeArrays.ThermometerAt s b
      (TapeArrays.entryOffset (vectorAddress v c j s) (s.reg (v (.inl 1)))) (s.reg (v (.inl 1))) (a j).val) :
    ∃ t e, t      ≤      randomLinearTimeBound c d M ∧
      (randomLinear v f point b c).Stops inp (s.toCfg (randomLinear (B := B) v f point b c).entry) t e ∧
      e.reg (f 30)=(EncodedSampler.linear (BinaryField.indexOperations ell h) a z).1.val ∧
      Environment f ell (selectedIndex ell h) e.store ∧
      e.reg (v (.inl 0))=s.reg (v (.inl 0)) ∧ e.reg (v (.inl 1))=s.reg (v (.inl 1)) ∧
      (∀ j,e.reg (point j)=s.reg (point j)) ∧
      (∀ x,(∀ i,x≠f i) → (∀ i,x≠v i) → e.reg x=s.reg x) ∧
      (∀ x,e.reg x      ≤      M) ∧ e.bufferHead b      ≤      M ∧
      (∀ b',b'≠b → e.bufferHead b'=s.bufferHead b') ∧
      TapeStore.SamePayload e.store s ∧ TapeArrays.BottomMarked e.store b := by
  obtain ⟨u,cfg,hu,hc,hcv,hca,hcq,hco,hcb,hch,hchd,hcp,hcm⟩ := allCoefficients_stops v hv b c inp M s hs
    hhead hm hmid hindex hend (fun j => (a j).val) hvalues
  have hce : Environment f ell (selectedIndex ell h) cfg.store := henv.frame (by
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact hco _ hmod
    · exact hco _ hN
    · simpa only [hq] using hcq
    · exact hco _ hQ)
  have hcz : ∀ j,cfg.reg (point j)=(z j).val := by
    intro j; rw [hco _ (hpv j)]; exact hz j
  obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := linear_stops_values f hf (fun j => v (.inr j)) point hcf hpf
    inp ell h a z M hM cfg.store hcb hce hcv hcz
  have hall := hc.seq he
  have hh : e.bufferHead=cfg.bufferHead := (tapeData_components het).2.2.2
  have hp : TapeStore.SamePayload e.store s := (tapeData_payload het).trans hcp
  refine ⟨u+1+t,_,?_,hall,hev,hee,?_,?_,?_,?_,heb,?_,?_,hp,hm.of_payload hp⟩
  · unfold randomLinearTimeBound; omega
  · exact (heo _ haddr).trans hca
  · have hqs : e.reg (f 23)=s.reg (f 23) := hee.cardinal.trans henv.cardinal.symm
    simpa only [hq] using hqs
  · intro j; exact (heo _ (hpf j)).trans (hco _ (hpv j))
  · intro x hxf hxv; exact (heo x hxf).trans (hco x hxv)
  · rw [hh]; exact hch
  · intro b' hne; rw [hh]; exact hchd b' hne

#print axioms randomLinear_stops

namespace Storage
/-- Concrete finite sampler storage; dimensions and arity are static program
parameters. All input-dependent quantities remain counter or buffer data. -/
def registers (d k : ℕ) : ℕ := 80+4*d+k

def low (d k : ℕ) (i : Fin 80) : Fin (registers d k) := ⟨i.val,by unfold registers; omega⟩
def point (d k : ℕ) (j : Fin d) : Fin (registers d k) := ⟨80+j.val,by unfold registers; have := j.isLt; omega⟩
def countdown (d k : ℕ) (j : Fin d) : Fin (registers d k) := ⟨80+d+j.val,by unfold registers; have := j.isLt; omega⟩
def coefficient (d k : ℕ) (j : Fin d) : Fin (registers d k) := ⟨80+2*d+j.val,by unfold registers; have := j.isLt; omega⟩
def neighbor (d k : ℕ) (i : Fin k) : Fin (registers d k) := ⟨80+4*d+i.val,by unfold registers; have := i.isLt; omega⟩

def field (d k : ℕ) (i : Fin 31) : Fin (registers d k) := low d k ⟨i.val,by have := i.isLt; omega⟩
def power (d k : ℕ) (i : Fin 32) : Fin (registers d k) := low d k ⟨i.val,by have := i.isLt; omega⟩
def alpha (d k : ℕ) : Fin (registers d k) := low d k 69
def address (d k : ℕ) : Fin (registers d k) := low d k 70
def u (d k : ℕ) : Fin (registers d k) := low d k 71
def v (d k : ℕ) : Fin (registers d k) := low d k 72
def hashIndex (d k : ℕ) : Fin (registers d k) := low d k 73
def bucket (d k : ℕ) : Fin (registers d k) := low d k 74

def pointPairs (d k : ℕ) : List (Fin (registers d k) × Fin (registers d k)) :=
  (List.finRange d).map (fun j => (point d k j,countdown d k j))

theorem low_injective (d k : ℕ) : Function.Injective (low d k) := by
  intro i j hij
  have hh := congrArg Fin.val hij
  exact Fin.ext hh

theorem field_injective (d k : ℕ) : Function.Injective (field d k) := by
  intro i j hij
  have hh := congrArg Fin.val hij
  exact Fin.ext hh

theorem power_injective (d k : ℕ) : Function.Injective (power d k) := by
  intro i j hij
  have hh := congrArg Fin.val hij
  exact Fin.ext hh

@[simp] theorem low_val (d k : ℕ) (i : Fin 80) : (low d k i).val=i.val := rfl
@[simp] theorem point_val (d k : ℕ) (j : Fin d) : (point d k j).val=80+j.val := rfl
@[simp] theorem countdown_val (d k : ℕ) (j : Fin d) : (countdown d k j).val=80+d+j.val := rfl
@[simp] theorem coefficient_val (d k : ℕ) (j : Fin d) : (coefficient d k j).val=80+2*d+j.val := rfl
@[simp] theorem neighbor_val (d k : ℕ) (i : Fin k) : (neighbor d k i).val=80+4*d+i.val := rfl
end Storage

namespace Storage

def fixedCommon (d k : ℕ) (i : Fin 33) : Fin (registers d k) :=
  if hi : i.val<32 then low d k ⟨i.val,by omega⟩ else alpha d k

def fixedLayout (d k : ℕ) : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin (registers d k)
  | .inl i => fixedCommon d k i
  | .inr (.inl j) => coefficient d k j
  | .inr (.inr j) => point d k j

def formCommon (d k : ℕ) : Fin 11 → Fin (registers d k) :=
  ![address d k,low d k 23,low d k 0,low d k 1,low d k 2,low d k 4,
    low d k 5,low d k 6,low d k 7,low d k 8,low d k 9]

def formLayout (d k : ℕ) : Fin 11 ⊕ Fin d → Fin (registers d k)
  | .inl i => formCommon d k i
  | .inr j => coefficient d k j

def hashLayout (d k : ℕ) : Fin 8 → Fin (registers d k) :=
  ![low d k 23,address d k,u d k,v d k,hashIndex d k,low d k 53,low d k 54,low d k 55]

def hashReadLayout (d k : ℕ) : Fin 8 → Fin (registers d k) :=
  ![hashIndex d k,low d k 39,low d k 56,low d k 57,low d k 58,low d k 59,bucket d k,low d k 53]
end Storage

def saveField (d k : ℕ) (dst : Fin 80) : TapeProgram (Storage.registers d k) 2 11 :=
  TapeMacros.copy (Storage.low d k 30) (Storage.low d k dst) (Storage.low d k 53)

def layerLabels (d k : ℕ) (i : Fin k) : ℕ :=
  (((((((2+ParameterPrograms.raiseLabels i.val)+fixedLabels (Storage.fixedLayout d k))+11)+
    randomLinearLabels (Storage.formLayout d k) (Storage.point d k) i.val)+11)+
      randomLinearLabels (Storage.formLayout d k) (Storage.point d k) (i.val+k))+11)+hashedColumnLabels i.val

/-- Concrete finite sampler layer. All labels and register locations depend
only on fixed d,k,i. Runtime n,q,ell,b and table values are data throughout. -/
def layer (d k : ℕ) (i : Fin k) : TapeProgram (Storage.registers d k) 2 (layerLabels d k i) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeProgram.seq (ParameterPrograms.loadConstant (Storage.alpha d k) i.val)
      (fixed (Storage.fixedLayout d k))) (saveField d k 70))
        (randomLinear (Storage.formLayout d k) (Storage.field d k) (Storage.point d k) (0 : Fin 2) i.val))
          (saveField d k 71))
            (randomLinear (Storage.formLayout d k) (Storage.field d k) (Storage.point d k) (0 : Fin 2) (i.val+k)))
              (saveField d k 72))
                (hashedColumn (Storage.hashLayout d k) (Storage.hashReadLayout d k)
                  (Storage.neighbor d k i) (Storage.low d k 53) (1 : Fin 2) i.val)

def layerTimeBound (d k : ℕ) (i : Fin k) (M : ℕ) : ℕ :=
  fixedTimeBound d M+randomLinearTimeBound i.val d M+randomLinearTimeBound (i.val+k) d M+
    hashedColumnTimeBound i.val M+22*M+2*i.val+30

theorem powerCoefficientTimeBound_polynomial (d : ℕ) : PolynomialBound (powerCoefficientTimeBound d) := by
  exact (PolynomialBound.const (d+2)).mul
    ((PolynomialBound.const 13440).mul ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 6))

theorem fixedTimeBound_polynomial (d : ℕ) : PolynomialBound (fixedTimeBound d) := by
  exact (((PolynomialBound.const d).mul ((powerCoefficientTimeBound_polynomial d).add (PolynomialBound.const 1))).add
    (PolynomialBound.const 1)).add
      ((PolynomialBound.const (d+1)).mul ((PolynomialBound.const 13320).mul
        ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 6)))

theorem vectorTimeBound_polynomial (c d : ℕ) : PolynomialBound (vectorTimeBound c d) := by
  exact (PolynomialBound.const (112+6*c+6*d*(c+1)+2*d)).mul
    ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 2)

theorem randomLinearTimeBound_polynomial (c d : ℕ) : PolynomialBound (randomLinearTimeBound c d) := by
  exact (((PolynomialBound.const d).mul ((vectorTimeBound_polynomial c d).add (PolynomialBound.const 1))).add
    (PolynomialBound.const 1)).add
      ((PolynomialBound.const (d+1)).mul ((PolynomialBound.const 13320).mul
        ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 6)))

theorem layerTimeBound_polynomial (d k : ℕ) (i : Fin k) : PolynomialBound (layerTimeBound d k i) := by
  exact ((((((fixedTimeBound_polynomial d).add (randomLinearTimeBound_polynomial i.val d)).add
    (randomLinearTimeBound_polynomial (i.val+k) d)).add (hashedColumnTimeBound_polynomial i.val)).add
      ((PolynomialBound.const 22).mul PolynomialBound.identity)).add (PolynomialBound.const (2*i.val))).add
        (PolynomialBound.const 30)

/-- One clock for every statically unrolled layer. -/
def layerTimeUniform (d k M : ℕ) : ℕ := Finset.univ.sum (fun i : Fin k => layerTimeBound d k i M)

theorem layerTimeBound_le_uniform (d k M : ℕ) (i : Fin k) :
    layerTimeBound d k i M    ≤    layerTimeUniform d k M := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (layerTimeBound d k j M)) (Finset.mem_univ i)

theorem layerTimeUniform_polynomial (d k : ℕ) : PolynomialBound (layerTimeUniform d k) := by
  classical
  have hs : ∀ s : Finset (Fin k),PolynomialBound (fun M => s.sum (fun i => layerTimeBound d k i M)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using PolynomialBound.const 0
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using (layerTimeBound_polynomial d k i).add ih
  exact hs Finset.univ

namespace Storage

theorem point_injective (d k : ℕ) : Function.Injective (point d k) := by
  intro i j hij; apply Fin.ext
  have hh := congrArg Fin.val hij
  simp only [point_val] at hh
  omega

theorem coefficient_injective (d k : ℕ) : Function.Injective (coefficient d k) := by
  intro i j hij; apply Fin.ext
  have hh := congrArg Fin.val hij
  simp only [coefficient_val] at hh
  omega

theorem neighbor_injective (d k : ℕ) : Function.Injective (neighbor d k) := by
  intro i j hij; apply Fin.ext
  have hh := congrArg Fin.val hij
  simp only [neighbor_val] at hh
  omega

theorem fixedCommon_cases (d k : ℕ) (i : Fin 33) :
    (fixedCommon d k i).val<32 ∨ (fixedCommon d k i).val=69 := by
  by_cases hi : i.val<32
  · left; simpa [fixedCommon,hi,low] using hi
  · right; simp [fixedCommon,hi,alpha,low]

theorem fixedCommon_lt (d k : ℕ) (i : Fin 33) : (fixedCommon d k i).val<80 := by
  rcases fixedCommon_cases d k i with hi|hi <;> omega

theorem fixedCommon_injective (d k : ℕ) : Function.Injective (fixedCommon d k) := by
  intro a b hab; apply Fin.ext
  have hh := congrArg Fin.val hab
  have ha := a.isLt; have hb := b.isLt
  by_cases h₁ : a.val<32 <;> by_cases h₂ : b.val<32 <;>
    simp [fixedCommon,h₁,h₂,alpha,low] at hh <;> omega

theorem fixedLayout_injective (d k : ℕ) : Function.Injective (fixedLayout d k) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (fixedCommon_injective d k hab)
    | inr b =>
      have hs := fixedCommon_lt d k a
      cases b with
      | inl b =>
        have hh := congrArg Fin.val hab
        change (fixedCommon d k a).val=80+2*d+b.val at hh
        omega
      | inr b =>
        have hh := congrArg Fin.val hab
        change (fixedCommon d k a).val=80+b.val at hh
        omega
  | inr a =>
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have hs := fixedCommon_lt d k b
        have hh := congrArg Fin.val hab
        change 80+2*d+a.val=(fixedCommon d k b).val at hh
        omega
      | inr b =>
        cases b with
        | inl b =>
          congr 1; congr 1
          exact coefficient_injective d k hab
        | inr b =>
          have hh := congrArg Fin.val hab
          change 80+2*d+a.val=80+b.val at hh
          have := b.isLt
          omega
    | inr a =>
      cases b with
      | inl b =>
        have hs := fixedCommon_lt d k b
        have hh := congrArg Fin.val hab
        change 80+a.val=(fixedCommon d k b).val at hh
        omega
      | inr b =>
        cases b with
        | inl b =>
          have hh := congrArg Fin.val hab
          change 80+a.val=80+2*d+b.val at hh
          have := a.isLt
          omega
        | inr b =>
          congr 1; congr 1
          exact point_injective d k hab

theorem formCommon_lt (d k : ℕ) (i : Fin 11) : (formCommon d k i).val<80 := by
  fin_cases i <;> simp [formCommon,address,low]

theorem formCommon_injective (d k : ℕ) : Function.Injective (formCommon d k) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [formCommon,address,(low_injective d k).eq_iff]

theorem formLayout_injective (d k : ℕ) : Function.Injective (formLayout d k) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (formCommon_injective d k hab)
    | inr b =>
      have hs := formCommon_lt d k a
      have hh := congrArg Fin.val hab
      change (formCommon d k a).val=80+2*d+b.val at hh
      omega
  | inr a =>
    cases b with
    | inl b =>
      have hs := formCommon_lt d k b
      have hh := congrArg Fin.val hab
      change 80+2*d+a.val=(formCommon d k b).val at hh
      omega
    | inr b => exact congrArg Sum.inr (coefficient_injective d k hab)

theorem hashLayout_injective (d k : ℕ) : Function.Injective (hashLayout d k) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [hashLayout,address,u,v,hashIndex,(low_injective d k).eq_iff]

theorem hashReadLayout_injective (d k : ℕ) : Function.Injective (hashReadLayout d k) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [hashReadLayout,bucket,hashIndex,(low_injective d k).eq_iff]

theorem coefficient_field_fresh (d k : ℕ) : ∀ j i,coefficient d k j≠field d k i := by
  intro j i hij
  have hh := congrArg Fin.val hij
  have hi := i.isLt
  simp [coefficient,field,low] at hh
  omega

theorem point_field_fresh (d k : ℕ) : ∀ j i,point d k j≠field d k i := by
  intro j i hij
  have hh := congrArg Fin.val hij
  have hi := i.isLt
  simp [point,field,low] at hh
  omega

theorem point_form_fresh (d k : ℕ) : ∀ j i,point d k j≠formLayout d k i := by
  intro j i hij
  cases i with
  | inl i =>
    have hs := formCommon_lt d k i
    have hh := congrArg Fin.val hij
    change 80+j.val=(formCommon d k i).val at hh
    omega
  | inr i =>
    have hh := congrArg Fin.val hij
    change 80+j.val=80+2*d+i.val at hh
    have := j.isLt
    omega

theorem address_field_fresh (d k : ℕ) : ∀ i,address d k≠field d k i := by
  intro i hij
  have hh := congrArg Fin.val hij
  have hi := i.isLt
  simp [address,field,low] at hh
  omega

theorem field_form_fresh (d k : ℕ) (a : Fin 31) (ha : a=3 ∨ a=19 ∨ a=24) :
    ∀ i,field d k a≠formLayout d k i := by
  intro i
  cases i with
  | inl i =>
    rcases ha with rfl|rfl|rfl <;> fin_cases i <;>
      simp [field,formLayout,formCommon,address,low,Fin.ext_iff]
  | inr j => exact Ne.symm (coefficient_field_fresh d k j a)

theorem field_form_q (d k : ℕ) : field d k 23=formLayout d k (.inl 1) := rfl

theorem fixedField_eq (d k : ℕ) : SamplerProgram.fixedFieldLayout (fixedLayout d k)=field d k := by
  funext i
  apply Fin.ext
  have hi : i.val<32 := by have := i.isLt; omega
  simp [SamplerProgram.fixedFieldLayout,SamplerProgram.powerWorkspace,SamplerProgram.powerField,
    SamplerProgram.fixedPowerLayout,SamplerProgram.fixedPowerIndex,fixedLayout,fixedCommon,hi,field,low,
    Function.comp_def]
end Storage

#print axioms Storage.fixedLayout_injective
#print axioms Storage.formLayout_injective

namespace Storage

theorem countdown_injective (d k : ℕ) : Function.Injective (countdown d k) := by
  intro i j hij; apply Fin.ext
  have hh := congrArg Fin.val hij
  simp only [countdown_val] at hh
  omega

theorem point_ne_countdown (d k : ℕ) (j a : Fin d) : point d k j≠countdown d k a := by
  intro hij
  have hh := congrArg Fin.val hij
  simp only [point_val,countdown_val] at hh
  have := j.isLt
  omega

theorem used_map_pairs (d k : ℕ) (js : List (Fin d)) :
    SamplerOdometer.used (js.map (fun j => (point d k j,countdown d k j)))=
      js.flatMap (fun j => [point d k j,countdown d k j]) := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [SamplerOdometer.used,ih]

@[simp] theorem pointPairs_length (d k : ℕ) : (pointPairs d k).length=d := by simp [pointPairs]

theorem pointPairs_readings (d k : ℕ) (s : TapeStore (registers d k) B) :
    SamplerOdometer.readings (pointPairs d k) s=List.ofFn (fun j => s.reg (point d k j)) := by
  rw [SamplerOdometer.readings,pointPairs,List.map_map]
  change (List.finRange d).map (fun j => s.reg (point d k j))=_
  exact List.ofFn_eq_map.symm

theorem used_pointPairs_nodup (d k : ℕ) : (SamplerOdometer.used (pointPairs d k)).Nodup := by
  rw [pointPairs,used_map_pairs]
  apply List.nodup_flatMap.mpr
  constructor
  · intro j hj
    simp [point_ne_countdown d k j j]
  · apply (List.nodup_finRange d).imp
    intro a b hab
    apply List.disjoint_left.mpr
    intro x hx hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx hy
    rcases hx with rfl|rfl
    · rcases hy with hp|hc
      · exact hab (point_injective d k hp)
      · exact point_ne_countdown d k a b hc
    · rcases hy with hp|hc
      · exact point_ne_countdown d k b a hp.symm
      · exact hab (countdown_injective d k hc)

theorem used_pointPairs_high (d k : ℕ) :
    ∀ x∈SamplerOdometer.used (pointPairs d k),80   ≤   x.val := by
  rw [pointPairs,used_map_pairs]
  intro x hx
  obtain ⟨j,hj,hx⟩ := List.mem_flatMap.mp hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl <;> simp only [point_val,countdown_val] <;> omega

theorem pointPairs_nodup (d k : ℕ) :
    (low d k 35::low d k 61::SamplerOdometer.used (pointPairs d k)).Nodup := by
  simp only [List.nodup_cons,List.mem_cons,not_or]
  refine ⟨⟨(low_injective d k).ne (by decide),?_⟩,?_,used_pointPairs_nodup d k⟩
  · intro hx
    have hh := used_pointPairs_high d k _ hx
    simp [low] at hh
  · intro hx
    have hh := used_pointPairs_high d k _ hx
    simp [low] at hh
end Storage

#print axioms Storage.pointPairs_nodup

#print axioms layerTimeUniform_polynomial

/-- The two sampler tables as actual explicit thermometer-buffer cells. -/
structure PhysicalTables (d k ell b : ℕ)
    (forms : Fin (2*k*(2^ell)*d) → Fin (2^ell))
    (hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b) (s : TapeStore R 2) : Prop where
  formMarked : TapeArrays.BottomMarked s 0
  hashMarked : TapeArrays.BottomMarked s 1
  formTable : TapeArrays.ThermometerTable s 0 (2^ell) (fun i => (forms i).val)
  hashTable : TapeArrays.ThermometerTable s 1 b (fun i => (hashes i).val)

theorem PhysicalTables.of_payload {d k ell b : ℕ}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {s e : TapeStore R 2}
    (h : PhysicalTables d k ell b forms hashes s) (hp : TapeStore.SamePayload e s) :
    PhysicalTables d k ell b forms hashes e := by
  exact ⟨h.formMarked.of_payload hp,h.hashMarked.of_payload hp,
    fun i => (h.formTable i).of_payload hp,fun i => (h.hashTable i).of_payload hp⟩

/-- Stable phase invariant for the concrete sampler layer. All input-dependent
quantities here are semantic counter/buffer values, not finite-code parameters. -/
structure LayerInvariant (d k ell b : ℕ) (h : 0<ell)
    (forms : Fin (2*k*(2^ell)*d) → Fin (2^ell))
    (hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b) (z : Fin d → Fin (2^ell))
    (M : ℕ) (s : TapeStore (Storage.registers d k) 2) : Prop where
  field : Environment (Storage.field d k) ell (selectedIndex ell h) s
  buckets : s.reg (Storage.low d k 39)=b
  points : ∀ j,s.reg (Storage.point d k j)=(z j).val
  counters : ∀ r,s.reg r     ≤     M
  heads : ∀ t,s.bufferHead t     ≤     M
  tables : PhysicalTables d k ell b forms hashes s

/-- Uniform scalar/table caps sufficient for all accesses in any one layer. -/
structure LayerCaps (d k ell b M : ℕ) : Prop where
  formHead : 1+(2*k*(2^ell)*d)*(2^ell)     ≤     M
  hashHead : 1+(k*(2^ell)*(2^ell)*(2^ell))*b     ≤     M
  middle : 2*k*(2^ell)     ≤     M
  columns : k*b     ≤     M

/-- Conservative finite write footprint of one layer. Point data, countdowns,
setup counters, row controls and every other neighbor lie outside it. -/
def LayerWritable (d k : ℕ) (i : Fin k) (x : Fin (Storage.registers d k)) : Prop :=
  x.val<32 ∨ (53  ≤  x.val ∧ x.val<60) ∨ (69  ≤  x.val ∧ x.val<75) ∨
    (80+2*d  ≤  x.val ∧ x.val<80+3*d) ∨ x=Storage.neighbor d k i

def LayerFrame (d k : ℕ) (i : Fin k) (s e : TapeStore (Storage.registers d k) 2) : Prop :=
  ∀ x,¬LayerWritable d k i x → e.reg x=s.reg x

theorem LayerFrame.trans {d k : ℕ} {i : Fin k} {s e z : TapeStore (Storage.registers d k) 2}
    (h : LayerFrame d k i s e) (g : LayerFrame d k i e z) : LayerFrame d k i s z :=
  fun x hx => (g x hx).trans (h x hx)

theorem writable_field (d k : ℕ) (i : Fin k) (a : Fin 31) : LayerWritable d k i (Storage.field d k a) := by
  left
  change a.val<32
  have := a.isLt
  omega

theorem writable_low (d k : ℕ) (i : Fin k) (a : Fin 80)
    (ha : a.val<32 ∨ (53  ≤  a.val ∧ a.val<60) ∨ (69  ≤  a.val ∧ a.val<75)) :
    LayerWritable d k i (Storage.low d k a) := by
  unfold LayerWritable
  rcases ha with ha|ha|ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))

theorem writable_coefficient (d k : ℕ) (i : Fin k) (j : Fin d) :
    LayerWritable d k i (Storage.coefficient d k j) := by
  right; right; right; left
  simp only [Storage.coefficient_val]
  have := j.isLt
  omega

theorem writable_fixedCommon (d k : ℕ) (i : Fin k) (j : Fin 33) :
    LayerWritable d k i (Storage.fixedCommon d k j) := by
  rcases Storage.fixedCommon_cases d k j with hj|hj
  · exact Or.inl hj
  · right; right; left; omega

theorem writable_formLayout (d k : ℕ) (i : Fin k) :
    ∀ a,LayerWritable d k i (Storage.formLayout d k a) := by
  intro a
  cases a with
  | inl a =>
    fin_cases a <;> first
      | exact writable_low d k i _ (by decide)
      | simpa only [Storage.formLayout,Storage.formCommon,Storage.address] using writable_low d k i (70 : Fin 80) (by decide)
  | inr j => exact writable_coefficient d k i j

theorem point_not_writable (d k : ℕ) (i : Fin k) (j : Fin d) :
    ¬LayerWritable d k i (Storage.point d k j) := by
  have hj := j.isLt
  simp only [LayerWritable,Storage.point_val,Fin.ext_iff,Storage.neighbor_val]
  omega

theorem countdown_not_writable (d k : ℕ) (i : Fin k) (j : Fin d) :
    ¬LayerWritable d k i (Storage.countdown d k j) := by
  have hj := j.isLt
  simp only [LayerWritable,Storage.countdown_val,Fin.ext_iff,Storage.neighbor_val]
  omega

theorem protected_low_not_writable (d k : ℕ) (i : Fin k) (a : Fin 80)
    (ha : (32  ≤  a.val ∧ a.val<46) ∨ (60  ≤  a.val ∧ a.val<69)) :
    ¬LayerWritable d k i (Storage.low d k a) := by
  simp only [LayerWritable,Storage.low_val,Fin.ext_iff,Storage.neighbor_val]
  omega

theorem other_neighbor_not_writable (d k : ℕ) (i a : Fin k) (ha : a≠i) :
    ¬LayerWritable d k i (Storage.neighbor d k a) := by
  have hn : Storage.neighbor d k a≠Storage.neighbor d k i := (Storage.neighbor_injective d k).ne ha
  simp only [LayerWritable,Storage.neighbor_val,hn,or_false]
  omega

theorem LayerInvariant.transport {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    {i : Fin k} {s e : TapeStore (Storage.registers d k) 2}
    (hs : LayerInvariant d k ell b h forms hashes z M s) (hf : LayerFrame d k i s e)
    (he : Environment (Storage.field d k) ell (selectedIndex ell h) e)
    (hc : ∀ x,e.reg x  ≤  M) (hh : ∀ t,e.bufferHead t  ≤  M) (hp : TapeStore.SamePayload e s) :
    LayerInvariant d k ell b h forms hashes z M e := by
  refine ⟨he,?_,?_,hc,hh,hs.tables.of_payload hp⟩
  · rw [hf _ (protected_low_not_writable d k i 39 (by decide))]
    exact hs.buckets
  · intro j
    rw [hf _ (point_not_writable d k i j)]
    exact hs.points j

theorem LayerFrame.setReg {d k : ℕ} {i : Fin k} (s : TapeStore (Storage.registers d k) 2)
    (r : Fin (Storage.registers d k)) (v : ℕ) (hr : LayerWritable d k i r) :
    LayerFrame d k i s (s.setReg r v) := by
  intro x hx
  have hne : x≠r := by intro heq; subst x; exact hx hr
  simp [TapeStore.setReg,hne]

theorem Storage.low_field_fresh (d k : ℕ) (a : Fin 80) (ha : 31  ≤  a.val) :
    ∀ j,Storage.low d k a≠Storage.field d k j := by
  intro j hij
  have hh := congrArg Fin.val hij
  have hj := j.isLt
  simp [Storage.field,Storage.low] at hh
  omega

theorem copy_phase_stops {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (src dst tmp : Fin (Storage.registers d k))
    (hsd : src≠dst) (hst : src≠tmp) (hdt : dst≠tmp)
    (hd : LayerWritable d k i dst) (ht : LayerWritable d k i tmp)
    (hdf : ∀ j,dst≠Storage.field d k j) (htf : ∀ j,tmp≠Storage.field d k j)
    (inp : Inputs) (s : TapeStore (Storage.registers d k) 2)
    (hs : LayerInvariant d k ell b h forms hashes z M s) :
    ∃ t e,t  ≤  7*M+7 ∧ (TapeMacros.copy src dst tmp).Stops inp
      (s.toCfg (TapeMacros.copy (B := 2) src dst tmp).entry) t e ∧
      LayerInvariant d k ell b h forms hashes z M e.store ∧ LayerFrame d k i s e.store ∧
      TapeStore.SamePayload e.store s ∧
      (∀ x,x≠dst → x≠tmp → e.reg x=s.reg x) ∧ e.reg dst=s.reg src := by
  obtain ⟨t,e,htime,he,hes,heb⟩ := copy_stops_bound src dst tmp hsd hst hdt inp M s hs.counters
  have hframe : LayerFrame d k i s e.store := by
    rw [hes]
    exact (LayerFrame.setReg s dst _ hd).trans (LayerFrame.setReg _ tmp 0 ht)
  have henv : Environment (Storage.field d k) ell (selectedIndex ell h) e.store := by
    rw [hes]
    exact (hs.field.setExternal dst _ hdf).setExternal tmp 0 htf
  have hheads : ∀ a,e.bufferHead a  ≤  M := by
    change ∀ a,e.store.bufferHead a  ≤  M
    rw [hes]
    exact hs.heads
  have hp : TapeStore.SamePayload e.store s := by rw [hes]; exact ⟨rfl,rfl,fun _ _ => rfl⟩
  have hprec : ∀ x,x≠dst → x≠tmp → e.reg x=s.reg x := by
    intro x hxd hxt
    change e.store.reg x=_
    rw [hes]
    simp [TapeStore.setReg,hxd,hxt]
  refine ⟨t,e,htime,he,hs.transport hframe henv heb hheads hp,hframe,hp,hprec,?_⟩
  change e.store.reg dst=_
  rw [hes]
  simp [TapeStore.setReg,hdt]

theorem alpha_phase_stops {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (hk : k  ≤  2^ell) (inp : Inputs) (s : TapeStore (Storage.registers d k) 2)
    (hs : LayerInvariant d k ell b h forms hashes z M s) :
    ∃ t e,t  ≤  M+2*i.val+2 ∧ (ParameterPrograms.loadConstant (Storage.alpha d k) i.val).Stops inp
      (s.toCfg (ParameterPrograms.loadConstant (B := 2) (Storage.alpha d k) i.val).entry) t e ∧
      LayerInvariant d k ell b h forms hashes z M e.store ∧ LayerFrame d k i s e.store ∧
      TapeStore.SamePayload e.store s ∧ e.reg (Storage.alpha d k)=i.val := by
  obtain ⟨e,he,hes⟩ := ParameterPrograms.loadConstant_stops (Storage.alpha d k) i.val inp s
  have hi : i.val  ≤  M := by
    have hq := hs.counters (Storage.field d k 23)
    rw [hs.field.cardinal] at hq
    exact (le_trans (le_of_lt i.isLt) hk).trans hq
  have hframe : LayerFrame d k i s e.store := by
    rw [hes]
    exact LayerFrame.setReg s _ _ (writable_low d k i 69 (by decide))
  have henv : Environment (Storage.field d k) ell (selectedIndex ell h) e.store := by
    rw [hes]
    exact hs.field.setExternal _ _ (Storage.low_field_fresh d k 69 (by decide))
  have hb : ∀ x,e.reg x  ≤  M := by change ∀ x,e.store.reg x  ≤  M; rw [hes]; exact setReg_bound _ _ _ M hs.counters hi
  have hh : ∀ a,e.bufferHead a  ≤  M := by change ∀ a,e.store.bufferHead a  ≤  M; rw [hes]; exact hs.heads
  have hp : TapeStore.SamePayload e.store s := by rw [hes]; exact ⟨rfl,rfl,fun _ _ => rfl⟩
  refine ⟨_,e,?_,he,hs.transport hframe henv hb hh hp,hframe,hp,?_⟩
  · have hα := hs.counters (Storage.alpha d k); omega
  · change e.store.reg (Storage.alpha d k)=_; rw [hes]; simp

theorem fixed_phase_stops {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (alpha : Fin (2^ell)) (inp : Inputs) (hM : 1  ≤  M)
    (s : TapeStore (Storage.registers d k) 2) (hs : LayerInvariant d k ell b h forms hashes z M s)
    (ha : s.reg (Storage.alpha d k)=alpha.val) :
    ∃ t e,t  ≤  fixedTimeBound d M ∧ (fixed (Storage.fixedLayout d k)).Stops inp
      (s.toCfg (fixed (B := 2) (Storage.fixedLayout d k)).entry) t e ∧
      LayerInvariant d k ell b h forms hashes z M e.store ∧ LayerFrame d k i s e.store ∧
      TapeStore.SamePayload e.store s ∧
      e.reg (Storage.field d k 30)=(EncodedSampler.fixed (BinaryField.indexOperations ell h) alpha z).1.val := by
  have henv : Environment (fixedFieldLayout (Storage.fixedLayout d k)) ell (selectedIndex ell h) s := by
    rw [Storage.fixedField_eq]
    exact hs.field
  obtain ⟨t,e,ht,he,hev,hee,hep,hef,heb,het⟩ := fixed_stops (Storage.fixedLayout d k)
    (Storage.fixedLayout_injective d k) inp ell h alpha z M hM s hs.counters henv ha hs.points
  have hframe : LayerFrame d k i s e.store := by
    intro x hx
    by_cases hp : ∃ j,x=Storage.point d k j
    · obtain ⟨j,rfl⟩ := hp
      exact hep j
    · apply hef x
      intro a hxa
      cases a with
      | inl a =>
        apply hx
        rw [hxa]
        exact writable_fixedCommon d k i a
      | inr a =>
        cases a with
        | inl j =>
          apply hx
          rw [hxa]
          exact writable_coefficient d k i j
        | inr j => exact hp ⟨j,hxa⟩
  have hee' : Environment (Storage.field d k) ell (selectedIndex ell h) e.store := by
    simpa only [Storage.fixedField_eq] using hee
  have hh : ∀ a,e.bufferHead a  ≤  M := by
    change ∀ a,e.store.bufferHead a  ≤  M
    rw [(tapeData_components het).2.2.2]
    exact hs.heads
  have hp : TapeStore.SamePayload e.store s := tapeData_payload het
  exact ⟨t,e,ht,he,hs.transport hframe hee' heb hh hp,hframe,hp,hev⟩

#print axioms fixed_phase_stops

def formSlice {d k ell : ℕ} (forms : Fin (2*k*(2^ell)*d) → Fin (2^ell))
    (r : Fin 2) (i : Fin k) (a : Fin (2^ell)) (j : Fin d) : Fin (2^ell) :=
  forms (SamplerTables.flatFour 2 k (2^ell) d (((r,i),a),j))

theorem Storage.saved_form_fresh (d k : ℕ) (a : Fin 80) (ha : a=71 ∨ a=72) :
    ∀ j,Storage.low d k a≠Storage.formLayout d k j := by
  intro j
  cases j with
  | inl j =>
    rcases ha with rfl|rfl <;> fin_cases j <;>
      simp [Storage.formLayout,Storage.formCommon,Storage.address,Storage.low,Fin.ext_iff]
  | inr j =>
    intro heq
    have hh := congrArg Fin.val heq
    have hi := a.isLt
    simp [Storage.formLayout,Storage.coefficient,Storage.low] at hh
    omega

theorem save_phase_stops {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (dst : Fin 80) (hdst : dst=70 ∨ dst=71 ∨ dst=72)
    (inp : Inputs) (s : TapeStore (Storage.registers d k) 2)
    (hs : LayerInvariant d k ell b h forms hashes z M s) :
    ∃ t e,t ≤ 7*M+7 ∧ (saveField d k dst).Stops inp (s.toCfg (saveField d k dst).entry) t e ∧
      LayerInvariant d k ell b h forms hashes z M e.store ∧ LayerFrame d k i s e.store ∧
      TapeStore.SamePayload e.store s ∧
      (∀ a : Fin 80,a≠dst → a≠53 → e.reg (Storage.low d k a)=s.reg (Storage.low d k a)) ∧
      e.reg (Storage.low d k dst)=s.reg (Storage.field d k 30) := by
  obtain ⟨t,e,ht,he,hee,hef,hep,heprec,hev⟩ := copy_phase_stops i
    (Storage.low d k 30) (Storage.low d k dst) (Storage.low d k 53)
    ((Storage.low_injective d k).ne (by rcases hdst with rfl|rfl|rfl <;> decide))
    ((Storage.low_injective d k).ne (by decide))
    ((Storage.low_injective d k).ne (by rcases hdst with rfl|rfl|rfl <;> decide))
    (writable_low d k i dst (by rcases hdst with rfl|rfl|rfl <;> decide))
    (writable_low d k i 53 (by decide))
    (Storage.low_field_fresh d k dst (by rcases hdst with rfl|rfl|rfl <;> decide))
    (Storage.low_field_fresh d k 53 (by decide)) inp s hs
  exact ⟨t,e,ht,he,hee,hef,hep,
    fun a had hat => heprec _ ((Storage.low_injective d k).ne had) ((Storage.low_injective d k).ne hat),hev⟩

theorem random_phase_stops {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (r : Fin 2) (a : Fin (2^ell)) (inp : Inputs) (hM : 1  ≤  M)
    (s : TapeStore (Storage.registers d k) 2) (hs : LayerInvariant d k ell b h forms hashes z M s)
    (caps : LayerCaps d k ell b M) (ha : s.reg (Storage.address d k)=a.val) :
    ∃ t e,t  ≤  randomLinearTimeBound (i.val+k*r.val) d M ∧
      (randomLinear (Storage.formLayout d k) (Storage.field d k) (Storage.point d k) (0 : Fin 2) (i.val+k*r.val)).Stops inp
        (s.toCfg (randomLinear (B := 2) (Storage.formLayout d k) (Storage.field d k) (Storage.point d k) (0 : Fin 2) (i.val+k*r.val)).entry) t e ∧
      LayerInvariant d k ell b h forms hashes z M e.store ∧ LayerFrame d k i s e.store ∧
      TapeStore.SamePayload e.store s ∧
      e.reg (Storage.address d k)=s.reg (Storage.address d k) ∧
      e.reg (Storage.u d k)=s.reg (Storage.u d k) ∧
      e.reg (Storage.field d k 30)=(EncodedSampler.linear (BinaryField.indexOperations ell h) (formSlice forms r i a) z).1.val := by
  have hsa : s.reg (Storage.formLayout d k (.inl 0))=a.val := ha
  have hsq : s.reg (Storage.formLayout d k (.inl 1))=2^ell := hs.field.cardinal
  have hflat (j : Fin d) : vectorAddress (Storage.formLayout d k) (i.val+k*r.val) j s=
      (SamplerTables.flatFour 2 k (2^ell) d (((r,i),a),j)).val := by
    rw [SamplerLayerBounds.form_index_val]
    unfold vectorAddress
    rw [hsa,hsq]
    ring
  have hN : 2*k*(2^ell)*d  ≤  M := by
    have hmul := Nat.le_mul_of_pos_right (2*k*(2^ell)*d) (Nat.two_pow_pos ell)
    have hbound := caps.formHead
    omega
  have hmid : s.reg (Storage.formLayout d k (.inl 0))+(i.val+k*r.val)*s.reg (Storage.formLayout d k (.inl 1))  ≤  M := by
    rw [hsa,hsq]
    exact (SamplerLayerBounds.form_middle_lt r i a).le.trans caps.middle
  have hindex : ∀ j,vectorAddress (Storage.formLayout d k) (i.val+k*r.val) j s  ≤  M := by
    intro j; rw [hflat]
    exact (SamplerTables.flatFour 2 k (2^ell) d (((r,i),a),j)).isLt.le.trans hN
  have hend : ∀ j,TapeArrays.entryOffset (vectorAddress (Storage.formLayout d k) (i.val+k*r.val) j s)
      (s.reg (Storage.formLayout d k (.inl 1)))+s.reg (Storage.formLayout d k (.inl 1))  ≤  M := by
    intro j
    rw [hflat,hsq]
    have hb := (SamplerLayerBounds.table_end (2^ell) (SamplerTables.flatFour 2 k (2^ell) d (((r,i),a),j))).trans caps.formHead
    unfold TapeArrays.entryOffset
    nlinarith
  have hvalues : ∀ j,TapeArrays.ThermometerAt s 0
      (TapeArrays.entryOffset (vectorAddress (Storage.formLayout d k) (i.val+k*r.val) j s) (s.reg (Storage.formLayout d k (.inl 1))))
      (s.reg (Storage.formLayout d k (.inl 1))) (formSlice forms r i a j).val := by
    intro j; rw [hflat,hsq]
    exact hs.tables.formTable _
  obtain ⟨t,e,ht,he,hev,hee,hea,heq,hepoints,heframe,heb,hehead,heheads,hep,hem⟩ := randomLinear_stops
    (Storage.formLayout d k) (Storage.formLayout_injective d k) (Storage.field d k) (Storage.field_injective d k)
    (Storage.point d k) (Storage.coefficient_field_fresh d k) (Storage.point_field_fresh d k)
    (Storage.point_form_fresh d k) (Storage.address_field_fresh d k) (Storage.field_form_q d k)
    (Storage.field_form_fresh d k 3 (by decide)) (Storage.field_form_fresh d k 19 (by decide))
    (Storage.field_form_fresh d k 24 (by decide)) 0 (i.val+k*r.val) inp ell h (formSlice forms r i a) z
    M hM s hs.counters hs.field hs.points (hs.heads 0) hs.tables.formMarked hmid hindex hend hvalues
  have hframe : LayerFrame d k i s e.store := by
    intro x hx
    apply heframe x
    · intro j hxj
      apply hx
      rw [hxj]
      exact writable_field d k i j
    · intro j hxj
      apply hx
      rw [hxj]
      exact writable_formLayout d k i j
  have hheads : ∀ a,e.bufferHead a  ≤  M := by
    intro a
    by_cases ha : a=0
    · subst a; exact hehead
    · rw [heheads a ha]
      exact hs.heads a
  have hU : e.reg (Storage.u d k)=s.reg (Storage.u d k) :=
    heframe _ (Storage.low_field_fresh d k 71 (by decide)) (Storage.saved_form_fresh d k 71 (Or.inl rfl))
  exact ⟨t,e,ht,he,hs.transport hframe hee heb hheads hep,hframe,hep,hea,hU,hev⟩

#print axioms random_phase_stops

theorem Storage.low_ne_neighbor (d k : ℕ) (a : Fin 80) (i : Fin k) :
    Storage.low d k a≠Storage.neighbor d k i := by
  intro heq
  have hh := congrArg Fin.val heq
  have ha := a.isLt
  simp only [Storage.low_val,Storage.neighbor_val] at hh
  omega

theorem Storage.hash_scratch_fresh (d k : ℕ) (x : Fin (Storage.registers d k)) (hx : x.val<53) :
    ∀ j : Fin 8,4 ≤ j.val → x≠Storage.hashLayout d k j := by
  intro j hj heq
  have hh := congrArg Fin.val heq
  fin_cases j <;> simp [Storage.hashLayout,Storage.address,Storage.u,Storage.v,Storage.hashIndex,Storage.low] at hh hj <;> omega

theorem Storage.read_scratch_fresh (d k : ℕ) (x : Fin (Storage.registers d k)) (hx : x.val<53) :
    ∀ j : Fin 8,2 ≤ j.val → x≠Storage.hashReadLayout d k j := by
  intro j hj heq
  have hh := congrArg Fin.val heq
  fin_cases j <;> simp [Storage.hashReadLayout,Storage.hashIndex,Storage.bucket,Storage.low] at hh hj <;> omega

theorem writable_hashScratch (d k : ℕ) (i : Fin k) (j : Fin 8) (hj : 4 ≤ j.val) :
    LayerWritable d k i (Storage.hashLayout d k j) := by
  fin_cases j <;> first | omega | exact writable_low d k i _ (by decide)

theorem writable_readScratch (d k : ℕ) (i : Fin k) (j : Fin 8) (hj : 2 ≤ j.val) :
    LayerWritable d k i (Storage.hashReadLayout d k j) := by
  fin_cases j <;> norm_num at hj <;> exact writable_low d k i _ (by decide)

theorem writable_neighbor (d k : ℕ) (i : Fin k) : LayerWritable d k i (Storage.neighbor d k i) :=
  Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem hash_phase_stops {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (a u v : Fin (2^ell)) (inp : Inputs) (hb : 0<b)
    (s : TapeStore (Storage.registers d k) 2) (hs : LayerInvariant d k ell b h forms hashes z M s)
    (caps : LayerCaps d k ell b M)
    (ha : s.reg (Storage.address d k)=a.val) (hu : s.reg (Storage.u d k)=u.val) (hv : s.reg (Storage.v d k)=v.val) :
    let index := SamplerTables.flatFour k (2^ell) (2^ell) (2^ell) (((i,a),u),v)
    ∃ t e,t ≤ hashedColumnTimeBound i.val M ∧
      (hashedColumn (Storage.hashLayout d k) (Storage.hashReadLayout d k) (Storage.neighbor d k i)
        (Storage.low d k 53) (1 : Fin 2) i.val).Stops inp
        (s.toCfg (hashedColumn (B := 2) (Storage.hashLayout d k) (Storage.hashReadLayout d k) (Storage.neighbor d k i)
          (Storage.low d k 53) (1 : Fin 2) i.val).entry) t e ∧
      LayerInvariant d k ell b h forms hashes z M e.store ∧ LayerFrame d k i s e.store ∧
      TapeStore.SamePayload e.store s ∧ e.reg (Storage.neighbor d k i)=i.val*b+(hashes index).val := by
  dsimp only
  let index := SamplerTables.flatFour k (2^ell) (2^ell) (2^ell) (((i,a),u),v)
  have hidx : hashAddress (Storage.hashLayout d k) i.val s=index.val := by
    rw [SamplerLayerBounds.hash_index_val]
    unfold hashAddress
    change s.reg (Storage.v d k)+s.reg (Storage.field d k 23)*
      (s.reg (Storage.u d k)+s.reg (Storage.field d k 23)*(s.reg (Storage.address d k)+s.reg (Storage.field d k 23)*i.val))=_
    rw [hs.field.cardinal,ha,hu,hv]
  have hB : s.reg (Storage.hashReadLayout d k 1)=b := hs.buckets
  have hN : k*(2^ell)*(2^ell)*(2^ell) ≤ M := by
    have hmul := Nat.le_mul_of_pos_right (k*(2^ell)*(2^ell)*(2^ell)) hb
    have hbound := caps.hashHead
    omega
  have haddr : hashAddress (Storage.hashLayout d k) i.val s ≤ M := by
    rw [hidx]; exact index.isLt.le.trans hN
  have hcolumn : (hashes index).val+i.val*s.reg (Storage.hashReadLayout d k 1) ≤ M := by
    rw [hB]
    simpa [Nat.add_comm] using (SamplerLayerBounds.column_lt i (hashes index)).le.trans caps.columns
  have hend : TapeArrays.entryOffset (hashAddress (Storage.hashLayout d k) i.val s)
      (s.reg (Storage.hashReadLayout d k 1))+s.reg (Storage.hashReadLayout d k 1) ≤ M := by
    rw [hidx,hB]
    have hend := (SamplerLayerBounds.table_end b index).trans caps.hashHead
    unfold TapeArrays.entryOffset
    nlinarith
  have hblock : TapeArrays.ThermometerAt s 1
      (TapeArrays.entryOffset (hashAddress (Storage.hashLayout d k) i.val s) (s.reg (Storage.hashReadLayout d k 1)))
      (s.reg (Storage.hashReadLayout d k 1)) (hashes index).val := by
    rw [hidx,hB]
    exact hs.tables.hashTable index
  obtain ⟨t,e,ht,he,hev,hef,hec,heheads,hehead,hep,hem⟩ := hashedColumn_stops
    (Storage.hashLayout d k) (Storage.hashReadLayout d k) (Storage.hashLayout_injective d k) (Storage.hashReadLayout_injective d k)
    (Storage.neighbor d k i) (Storage.low d k 53) rfl
    (Storage.hash_scratch_fresh d k (Storage.low d k 39) (by change (39 : ℕ)<53; decide))
    (Storage.low_ne_neighbor d k 74 i)
    ((Storage.low_injective d k).ne (by decide : (74 : Fin 80)≠53))
    (Ne.symm (Storage.low_ne_neighbor d k 53 i)) (Storage.low_ne_neighbor d k 39 i)
    ((Storage.low_injective d k).ne (by decide : (39 : Fin 80)≠53))
    1 i.val inp M s hs.counters (hs.heads 1) hs.tables.hashMarked haddr (hashes index).val hcolumn hend hblock
  have hframe : LayerFrame d k i s e.store := by
    intro x hx
    apply hef x
    · intro j hj hxj
      apply hx; rw [hxj]; exact writable_hashScratch d k i j hj
    · intro j hj hxj
      apply hx; rw [hxj]; exact writable_readScratch d k i j hj
    · intro hxj; apply hx; rw [hxj]; exact writable_neighbor d k i
    · intro hxj; apply hx; rw [hxj]; exact writable_low d k i 53 (by decide)
  have hfield (j : Fin 31) : e.reg (Storage.field d k j)=s.reg (Storage.field d k j) := by
    have hj : (Storage.field d k j).val<53 := by change j.val<53; have := j.isLt; omega
    exact hef _ (Storage.hash_scratch_fresh d k _ hj) (Storage.read_scratch_fresh d k _ hj)
      (Storage.low_ne_neighbor d k ⟨j.val,by have := j.isLt; omega⟩ i)
      (Ne.symm (Storage.low_field_fresh d k 53 (by decide) j))
  have hee : Environment (Storage.field d k) ell (selectedIndex ell h) e.store := hs.field.frame (fun j _ => hfield j)
  have hh : ∀ j,e.bufferHead j ≤ M := by
    intro j
    by_cases hj : j=1
    · subst j; exact hehead
    · rw [heheads]
      simpa [hj] using hs.heads j
  rw [hB] at hev
  exact ⟨t,e,ht,he,hs.transport hframe hee hec hh hep,hframe,hep,hev⟩

#print axioms hash_phase_stops

theorem layer_stops {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (hk : k≤2^ell) (hb : 0<b) (hM : 1≤M) (caps : LayerCaps d k ell b M)
    (inp : Inputs) (s : TapeStore (Storage.registers d k) 2)
    (hs : LayerInvariant d k ell b h forms hashes z M s) :
    ∃ t e,t≤layerTimeBound d k i M ∧
      (layer d k i).Stops inp (s.toCfg (layer d k i).entry) t e ∧
      LayerInvariant d k ell b h forms hashes z M e.store ∧ TapeStore.SamePayload e.store s ∧
      e.reg (Storage.neighbor d k i)=i.val*b+
        (EncodedSampler.neighbor (BinaryField.indexOperations ell h) forms hashes i z).val ∧
      (∀ j,e.reg (Storage.point d k j)=s.reg (Storage.point d k j)) ∧
      (∀ j,e.reg (Storage.countdown d k j)=s.reg (Storage.countdown d k j)) ∧
      (∀ a : Fin 80,(32≤a.val ∧ a.val<46) ∨ (60≤a.val ∧ a.val<69) →
        e.reg (Storage.low d k a)=s.reg (Storage.low d k a)) ∧
      e.output=s.output ∧
      (∀ a : Fin k,a≠i → e.reg (Storage.neighbor d k a)=s.reg (Storage.neighbor d k a)) ∧
      LayerFrame d k i s e.store := by
  let alpha : Fin (2^ell) := ⟨i.val,lt_of_lt_of_le i.isLt hk⟩
  let a := (EncodedSampler.fixed (BinaryField.indexOperations ell h) alpha z).1
  let u := (EncodedSampler.linear (BinaryField.indexOperations ell h) (formSlice forms 0 i a) z).1
  let v := (EncodedSampler.linear (BinaryField.indexOperations ell h) (formSlice forms 1 i a) z).1
  obtain ⟨t₁,c₁,ht₁,h₁,hi₁,hf₁,hp₁,hα₁⟩ := alpha_phase_stops i hk inp s hs
  obtain ⟨t₂,c₂,ht₂,h₂,hi₂,hf₂,hp₂,ha₂⟩ := fixed_phase_stops i alpha inp hM c₁.store hi₁ hα₁
  obtain ⟨t₃,c₃,ht₃,h₃,hi₃,hf₃,hp₃,hcf₃,hv₃⟩ := save_phase_stops i 70 (Or.inl rfl) inp c₂.store hi₂
  have ha₃ : c₃.reg (Storage.address d k)=a.val := hv₃.trans ha₂
  obtain ⟨t₄,c₄,ht₄,h₄,hi₄,hf₄,hp₄,hca₄,hcu₄,hu₄⟩ := random_phase_stops i 0 a inp hM c₃.store hi₃ caps ha₃
  have ha₄ : c₄.reg (Storage.address d k)=a.val := hca₄.trans ha₃
  obtain ⟨t₅,c₅,ht₅,h₅,hi₅,hf₅,hp₅,hcf₅,hv₅⟩ := save_phase_stops i 71 (Or.inr (Or.inl rfl)) inp c₄.store hi₄
  have hu₅ : c₅.reg (Storage.u d k)=u.val := hv₅.trans hu₄
  have ha₅ : c₅.reg (Storage.address d k)=a.val := (hcf₅ 70 (by decide) (by decide)).trans ha₄
  obtain ⟨t₆,c₆,ht₆,h₆,hi₆,hf₆,hp₆,hca₆,hcu₆,hv₆⟩ := random_phase_stops i 1 a inp hM c₅.store hi₅ caps ha₅
  have ha₆ : c₆.reg (Storage.address d k)=a.val := hca₆.trans ha₅
  have hu₆ : c₆.reg (Storage.u d k)=u.val := hcu₆.trans hu₅
  obtain ⟨t₇,c₇,ht₇,h₇,hi₇,hf₇,hp₇,hcf₇,hv₇⟩ := save_phase_stops i 72 (Or.inr (Or.inr rfl)) inp c₆.store hi₆
  have ha₇ : c₇.reg (Storage.address d k)=a.val := (hcf₇ 70 (by decide) (by decide)).trans ha₆
  have hu₇ : c₇.reg (Storage.u d k)=u.val := (hcf₇ 71 (by decide) (by decide)).trans hu₆
  have hv₇' : c₇.reg (Storage.v d k)=v.val := hv₇.trans hv₆
  obtain ⟨t₈,c₈,ht₈,h₈,hi₈,hf₈,hp₈,hv₈⟩ := hash_phase_stops i a u v inp hb c₇.store hi₇ caps ha₇ hu₇ hv₇'
  have hall := ((((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆).seq h₇).seq h₈
  have hzero : i.val+k*(0 : Fin 2).val=i.val := by change i.val+k*0=i.val; omega
  have hone : i.val+k*(1 : Fin 2).val=i.val+k := by change i.val+k*1=i.val+k; omega
  rw [hzero,hone] at hall
  rw [hzero] at ht₄
  rw [hone] at ht₆
  have hframe : LayerFrame d k i s c₈.store := ((((((hf₁.trans hf₂).trans hf₃).trans hf₄).trans hf₅).trans hf₆).trans hf₇).trans hf₈
  have hpay : TapeStore.SamePayload c₈.store s := hp₈.trans (hp₇.trans (hp₆.trans (hp₅.trans (hp₄.trans (hp₃.trans (hp₂.trans hp₁))))))
  have hi : i.val<2^ell := lt_of_lt_of_le i.isLt hk
  have hneighbor : EncodedSampler.neighbor (BinaryField.indexOperations ell h) forms hashes i z=
      hashes (SamplerTables.flatFour k (2^ell) (2^ell) (2^ell) (((i,a),u),v)) := by
    exact SamplerLayerBounds.neighbor_cached (BinaryField.indexOperations ell h) forms hashes hk i z
  have hresult : c₈.reg (Storage.neighbor d k i)=i.val*b+
      (EncodedSampler.neighbor (BinaryField.indexOperations ell h) forms hashes i z).val := by
    rw [hneighbor]
    exact hv₈
  let e := c₈.mapPC (TapeProgram.rightLabel
    ((((((2+ParameterPrograms.raiseLabels i.val)+fixedLabels (Storage.fixedLayout d k))+11)+
      randomLinearLabels (Storage.formLayout d k) (Storage.point d k) i.val)+11)+
      randomLinearLabels (Storage.formLayout d k) (Storage.point d k) (i.val+k)+11))
  have hstop : (layer d k i).Stops inp (s.toCfg (layer d k i).entry)
      (t₁+1+t₂+1+t₃+1+t₄+1+t₅+1+t₆+1+t₇+1+t₈) e := by
    exact hall
  refine ⟨_,e,?_,hstop,hi₈,hpay,hresult,?_,?_,?_,hpay.output,?_,hframe⟩
  · unfold layerTimeBound
    omega
  · intro j; exact hframe _ (point_not_writable d k i j)
  · intro j; exact hframe _ (countdown_not_writable d k i j)
  · intro a ha; exact hframe _ (protected_low_not_writable d k i a ha)
  · intro a ha; exact hframe _ (other_neighbor_not_writable d k i a ha)

#print axioms layer_stops


#print axioms fixed_stops

#print axioms allPowers_stops

#print axioms allCoefficients_stops

#print axioms vectorLoad_stops

#print axioms powerCore_stops
#print axioms powerFromOne_stops

#print axioms dotFromZero_stops
#print axioms dotValue_sum

#print axioms term_stops
end ExpandingCodes.Computation.SamplerProgram
