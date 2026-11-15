import ExpandingCodes.Computation.SamplerProgram

set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterPowers
open NKtLB SamplerEvaluation SamplerProgram
open ExpandingCodes.PolynomialStretch BinaryPolynomial
open FieldPrograms UnaryArithmetic
variable {R B : ℕ}

/-- Fixed scalar workspace plus one runtime exponent countdown. -/
def scalar (r : Fin 33 → Fin R) (i : Fin 32) : Fin R := r ⟨i.val,by omega⟩

theorem scalar_injective (r : Fin 33 → Fin R) (hr : Function.Injective r) :
    Function.Injective (scalar r) := by
  intro i j hij
  have hh := congrArg (Fin.val : Fin 33 → ℕ) (hr hij)
  exact Fin.ext hh

theorem count_outside (r : Fin 33 → Fin R) (hr : Function.Injective r) :
    ∀ i : Fin 32,r 32≠scalar r i := by
  intro i heq
  have hh := congrArg Fin.val (hr heq)
  have hi := i.isLt
  simp only [scalar,Fin.val_mk] at hh
  omega

/-- The transition table is independent of the exponent, field size and input.
Every multiplication runs the physical binary-field source program. -/
def powerLoop (r : Fin 33 → Fin R) (x : Fin R) : TapeProgram R B 864 :=
  TapeProgram.countedLoop (powerStep (scalar r) x) (r 32)

theorem powerLoop_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (x : Fin R) (hx : ∀ i,x≠r i) (inp : Inputs) (ell : ℕ) (h : 0<ell)
    (alpha : Fin (2^ell)) (M : ℕ) (hM : 1≤M) (n : ℕ)
    (s : TapeStore R B) (hs : ∀ i,s.reg i≤M)
    (henv : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) s)
    (a : Fin (2^ell)) (ha : s.reg (r 31)=a.val) (hxv : s.reg x=alpha.val)
    (hn : s.reg (r 32)=n) :
    ∃ t e, t≤n*(13400*(M+1)^6+2)+1 ∧
      (powerLoop r x).Stops inp (s.toCfg (powerLoop (B := B) r x).entry) t e ∧
      e.reg (r 31)=((fun z => (BinaryField.indexOperations ell h).mul z alpha)^[n] a).val ∧
      e.reg (r 32)=0 ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → e.reg i=s.reg i) ∧
      (∀ i,e.reg i≤M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  induction n generalizing s a with
  | zero =>
    refine ⟨1,s.toCfg (TapeProgram.loopExit 862),by simp,?_,ha,hn,henv,fun _ _ => rfl,hs,rfl⟩
    exact TapeProgram.loop_zero (powerStep (scalar r) x) (r 32) inp s hn
  | succ n ih =>
    let d := s.setReg (r 32) n
    have hd : ∀ i,d.reg i≤M := setReg_bound s _ n M hs (by have := hs (r 32); omega)
    have hde : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) d :=
      henv.setExternal (r 32) n (fun i => count_outside r hr ⟨i.val,by omega⟩)
    have hda : d.reg (r 31)=a.val := by simpa [d,reg_layout r hr] using ha
    have hdx : d.reg x=alpha.val := by simpa [d,TapeStore.setReg,hx 32] using hxv
    obtain ⟨u,c,hu,hc,hcv,hce,hco,hcb,hct⟩ := powerStep_stops (scalar r)
      (scalar_injective r hr) x (fun i => hx ⟨i.val,by omega⟩) inp ell h a alpha M hM d hd hde hda hdx
    have hcn : c.reg (r 32)=n := by
      rw [hco (r 32) (count_outside r hr)]
      simp [d]
    obtain ⟨t,e,ht,he,hev,hen,hee,heo,heb,het⟩ := ih c.store hcb hce
      ((BinaryField.indexOperations ell h).mul a alpha) (by simpa [scalar] using hcv)
      (by change c.reg x=_; rw [hco x (fun i => hx ⟨i.val,by omega⟩)]; exact hdx) hcn
    have hheader := TapeProgram.loop_positive_header (powerStep (scalar r) x) (r 32) inp s (by omega)
    have hdstore : TapeProgram.decStore (r 32) s=d := by
      simp [TapeProgram.decStore,d,TapeStore.setReg,hn]
    rw [hdstore] at hheader
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (powerStep (scalar r) x) (r 32))
    have hreturn := TapeProgram.loop_body_return (powerStep (scalar r) x) (r 32) inp c hc.halted
    have hall := ((hheader.trans hrun).trans hreturn).trans he.exec
    refine ⟨1+u+1+t,e,?_,⟨hall,he.halted⟩,?_,hen,hee,?_,heb,?_⟩
    · rw [Nat.succ_mul]; omega
    · simpa only [Function.iterate_succ_apply] using hev
    · intro i hi
      rw [heo i hi]
      change c.reg i=_
      rw [hco i (fun v => hi ⟨v.val,by omega⟩)]
      simp [d,TapeStore.setReg,hi 32]
    · simpa only [d,FieldConvolution.tapeData_setReg] using het.trans hct

/-- Preserve the runtime exponent while loading a fresh countdown, initialize
one, then execute the actual counted field-power loop. -/
def power (r : Fin 33 → Fin R) (x exponent : Fin R) : TapeProgram R B 879 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.copy exponent (r 32) (r 2))
    (SourceFieldArithmetic.setOne (r 31))) (powerLoop r x)

theorem power_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (x exponent : Fin R) (hx : ∀ i,x≠r i) (he : ∀ i,exponent≠r i)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (alpha : Fin (2^ell))
    (M : ℕ) (hM : 1≤M) (s : TapeStore R B) (hs : ∀ i,s.reg i≤M)
    (henv : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) s)
    (hxv : s.reg x=alpha.val) :
    ∃ t e, t≤(s.reg exponent+1)*(13420*(M+1)^6) ∧
      (power r x exponent).Stops inp (s.toCfg (power (B := B) r x exponent).entry) t e ∧
      e.reg (r 31)=(EncodedTester.power (BinaryField.indexOperations ell h) alpha (s.reg exponent)).1.val ∧
      e.reg (r 32)=0 ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → e.reg i=s.reg i) ∧
      (∀ i,e.reg i≤M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨u,c,hu,hc,hcs,hcb⟩ := copy_stops_bound exponent (r 32) (r 2)
    (he _) (he _) (hr.ne (by decide)) inp M s hs
  obtain ⟨d,hd,hds⟩ := SourceFieldArithmetic.setOne_stops (r 31) inp c.store
  have hdstore : d.store=((s.setReg (r 32) (s.reg exponent)).setReg (r 2) 0).setReg (r 31) 1 := by
    rw [hds,hcs]
  have hdb : ∀ i,d.reg i≤M := by
    change ∀ i,d.store.reg i≤M
    rw [hds]; exact setReg_bound c.store _ 1 M hcb hM
  have hde : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) d.store := by
    rw [hdstore]
    exact ((henv.setExternal (r 32) _ (fun i => count_outside r hr ⟨i.val,by omega⟩)).setReg
      (powerWorkspace_injective _ (scalar_injective r hr)) 2 0 (by decide)).setExternal
      (r 31) 1 (powerOutside _ (scalar_injective r hr))
  obtain ⟨t,e,ht,hloop,hev,hen,hee,heo,heb,het⟩ := powerLoop_stops r hr x hx inp ell h alpha M hM
    (s.reg exponent) d.store hdb hde (BinaryField.oneIndex ell)
    (by rw [hdstore]; simp [oneIndex_value ell h])
    (by rw [hdstore]; simpa [TapeStore.setReg,hx] using hxv)
    (by rw [hdstore]; simp [reg_layout r hr])
  have hall := (hc.seq hd).seq hloop
  refine ⟨u+1+(c.reg (r 31)+3)+1+t,_,?_,hall,?_,hen,hee,?_,heb,?_⟩
  · have hp : M+1≤(M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1≤6 by decide)
    have hb31 := hcb (r 31)
    have hp0 : 1≤(M+1)^6 := by omega
    have hfactor : 13400*(M+1)^6+2≤13420*(M+1)^6 := by omega
    have htime := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (s.reg exponent) hfactor) 1)
    rw [Nat.add_mul,Nat.one_mul]
    omega
  · simpa only [power_iterate ell h alpha (s.reg exponent)] using hev
  · intro i hi
    rw [heo i hi,hdstore]
    simp [TapeStore.setReg,hi]
  · simpa only [hdstore,FieldConvolution.tapeData_setReg] using het

#print axioms powerLoop_stops
#print axioms power_stops

/-- Append one monomial factor. Its exponent is a runtime caller counter;
the product accumulator is outside the shared scalar workspace. -/
def factor (r : Fin 33 → Fin R) (out exponent x : Fin R) : TapeProgram R B 1752 :=
  TapeProgram.seq (TapeProgram.seq (power r x exponent) (powerStep (scalar r) out))
    (TapeMacros.copy (r 31) out (r 2))

theorem factor_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (out exponent x : Fin R) (hout : ∀ i,out≠r i) (he : ∀ i,exponent≠r i)
    (hx : ∀ i,x≠r i) (inp : Inputs) (ell : ℕ) (h : 0<ell) (alpha a : Fin (2^ell))
    (M : ℕ) (hM : 1≤M) (s : TapeStore R B) (hs : ∀ i,s.reg i≤M)
    (henv : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) s)
    (hxv : s.reg x=alpha.val) (ha : s.reg out=a.val) :
    ∃ t e,t≤27000*(M+1)^7 ∧
      (factor r out exponent x).Stops inp (s.toCfg (factor (B := B) r out exponent x).entry) t e ∧
      e.reg out=((BinaryField.indexOperations ell h).mul
        (EncodedTester.power (BinaryField.indexOperations ell h) alpha (s.reg exponent)).1 a).val ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → i≠out → e.reg i=s.reg i) ∧
      (∀ i,e.reg i≤M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨t,c,ht,hc,hcv,hcn,hce,hco,hcb,hct⟩ := power_stops r hr x exponent hx he inp ell h alpha M hM s hs henv hxv
  obtain ⟨u,d,hu,hd,hdv,hde,hdo,hdb,hdt⟩ := powerStep_stops (scalar r) (scalar_injective r hr)
    out (fun i => hout ⟨i.val,by omega⟩) inp ell h
    (EncodedTester.power (BinaryField.indexOperations ell h) alpha (s.reg exponent)).1 a M hM c.store hcb hce
    (by simpa [scalar] using hcv) (by change c.reg out=_; rw [hco out hout]; exact ha)
  obtain ⟨v,e,hv,he',hes,heb⟩ := copy_stops_bound (r 31) out (r 2)
    (Ne.symm (hout _)) (hr.ne (by decide)) (hout _) inp M d.store hdb
  have hall := (hc.seq hd).seq he'
  refine ⟨t+1+u+1+v,_,?_,hall,?_,?_,?_,heb,?_⟩
  · have hp : M+1≤(M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1≤6 by decide)
    have hp₆ : (M+1)^6≤(M+1)^7 := Nat.pow_le_pow_right (by omega) (by decide)
    have hpow : (s.reg exponent+1)*(M+1)^6≤(M+1)^7 := by
      calc
        _ ≤ (M+1)*(M+1)^6 := Nat.mul_le_mul_right _ (by have := hs exponent; omega)
        _ = (M+1)^7 := by ring
    have ht' : t≤13420*(M+1)^7 := by nlinarith [ht]
    omega
  · change e.store.reg out=_
    rw [hes]
    simpa [TapeStore.setReg,hout,scalar] using hdv
  · rw [hes]
    exact (hde.setExternal out _ (fun i => hout ⟨i.val,by omega⟩)).setReg
      (powerWorkspace_injective _ (scalar_injective r hr)) 2 0 (by decide)
  · intro i hi hio
    change e.store.reg i=_
    rw [hes]
    simp only [TapeStore.setReg,Function.update_of_ne (hi 2),Function.update_of_ne hio]
    rw [hdo i (fun j => hi ⟨j.val,by omega⟩)]
    change c.reg i=_
    exact hco i hi
  · change FieldConvolution.tapeData e.store=_
    rw [hes]
    simpa only [FieldConvolution.tapeData_setReg] using hdt.trans hct

def productLabels : List (Fin R × Fin R) → ℕ
  | [] => 1
  | _::ps => productLabels ps+1752

/-- A statically unrolled dimension, with independently bounded runtime powers. -/
def productCore (r : Fin 33 → Fin R) (out : Fin R) :
    (ps : List (Fin R × Fin R)) → TapeProgram R B (productLabels ps)
  | [] => TapeProgram.skip
  | p::ps => TapeProgram.seq (productCore r out ps) (factor r out p.1 p.2)

def productValue (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell))
    (exponents : Fin R → ℕ) : List (Fin R × Fin R) → Fin (2^ell)
  | [] => BinaryField.oneIndex ell
  | p::ps => (BinaryField.indexOperations ell h).mul
      (EncodedTester.power (BinaryField.indexOperations ell h) (values p.2) (exponents p.1)).1
      (productValue ell h values exponents ps)

theorem productValue_eq (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell))
    (exponents : Fin R → ℕ) (ps : List (Fin R × Fin R)) :
    productValue ell h values exponents ps=(EncodedTester.product (BinaryField.indexOperations ell h)
      (ps.map fun p => EncodedTester.power (BinaryField.indexOperations ell h) (values p.2) (exponents p.1))).1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [productValue,List.map_cons,EncodedTester.product,ih]

theorem productCore_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (out : Fin R) (hout : ∀ i,out≠r i) (ps : List (Fin R × Fin R))
    (hp : ∀ p∈ps,(∀ i,p.1≠r i) ∧ (∀ i,p.2≠r i) ∧ p.1≠out ∧ p.2≠out)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell)) (exponents : Fin R → ℕ)
    (M : ℕ) (hM : 1≤M) (s : TapeStore R B) (hs : ∀ i,s.reg i≤M)
    (henv : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) s)
    (hv : ∀ p∈ps,s.reg p.2=(values p.2).val ∧ s.reg p.1=exponents p.1)
    (ha : s.reg out=1) :
    ∃ t e,t≤ps.length*(27000*(M+1)^7+1) ∧
      (productCore r out ps).Stops inp (s.toCfg (productCore (B := B) r out ps).entry) t e ∧
      e.reg out=(productValue ell h values exponents ps).val ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → i≠out → e.reg i=s.reg i) ∧
      (∀ i,e.reg i≤M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  induction ps generalizing s with
  | nil =>
    refine ⟨0,s.toCfg ⟨0,by simp [productLabels]⟩,by simp,TapeProgram.skip_stops inp s,?_,henv,fun _ _ _ => rfl,hs,rfl⟩
    simpa [productValue,oneIndex_value ell h] using ha
  | cons p ps ih =>
    obtain ⟨t,c,ht,hc,hcv,hce,hco,hcb,hct⟩ := ih
      (fun a ha => hp a (by simp [ha])) s hs henv (fun a ha => hv a (by simp [ha])) ha
    have hpp := hp p (by simp)
    have hvp := hv p (by simp)
    have hcexp : c.reg p.1=exponents p.1 := (hco p.1 hpp.1 hpp.2.2.1).trans hvp.2
    obtain ⟨u,e,hu,he,hev,hee,heo,heb,het⟩ := factor_stops r hr out p.1 p.2 hout hpp.1 hpp.2.1
      inp ell h (values p.2) (productValue ell h values exponents ps) M hM c.store hcb hce
      ((hco p.2 hpp.2.1 hpp.2.2.2).trans hvp.1) hcv
    have hall := hc.seq he
    refine ⟨t+1+u,_,?_,hall,?_,hee,?_,heb,het.trans hct⟩
    · change t+1+u≤(ps.length+1)*(27000*(M+1)^7+1)
      rw [Nat.add_mul,Nat.one_mul]; omega
    · simpa only [productValue,hcexp] using hev
    · intro i hi hio
      exact (heo i hi hio).trans (hco i hi hio)

/-- Initialize the accumulator to the canonical field one before the finite
product code. Exponents remain runtime values throughout. -/
def product (r : Fin 33 → Fin R) (out : Fin R) (ps : List (Fin R × Fin R)) :
    TapeProgram R B (4+productLabels ps) :=
  TapeProgram.seq (SourceFieldArithmetic.setOne out) (productCore r out ps)

theorem product_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (out : Fin R) (hout : ∀ i,out≠r i) (ps : List (Fin R × Fin R))
    (hp : ∀ p∈ps,(∀ i,p.1≠r i) ∧ (∀ i,p.2≠r i) ∧ p.1≠out ∧ p.2≠out)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell)) (exponents : Fin R → ℕ)
    (M : ℕ) (hM : 1≤M) (s : TapeStore R B) (hs : ∀ i,s.reg i≤M)
    (henv : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) s)
    (hv : ∀ p∈ps,s.reg p.2=(values p.2).val ∧ s.reg p.1=exponents p.1) :
    ∃ t e,t≤(ps.length+1)*(27020*(M+1)^7) ∧
      (product r out ps).Stops inp (s.toCfg (product (B := B) r out ps).entry) t e ∧
      e.reg out=(productValue ell h values exponents ps).val ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → i≠out → e.reg i=s.reg i) ∧
      (∀ i,e.reg i≤M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨c,hc,hcs⟩ := SourceFieldArithmetic.setOne_stops out inp s
  have hcb : ∀ i,c.reg i≤M := by
    change ∀ i,c.store.reg i≤M
    rw [hcs]; exact setReg_bound s _ 1 M hs hM
  have hce : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) c.store := by
    rw [hcs]; exact henv.setExternal out 1 (fun i => hout ⟨i.val,by omega⟩)
  have hcv : ∀ p∈ps,c.store.reg p.2=(values p.2).val ∧ c.store.reg p.1=exponents p.1 := by
    intro p hpm
    have hh := hp p hpm
    rw [hcs]
    simpa [TapeStore.setReg,hh.2.2.1,hh.2.2.2] using hv p hpm
  obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := productCore_stops r hr out hout ps hp inp ell h values exponents M hM
    c.store hcb hce hcv (by rw [hcs]; simp)
  have hall := hc.seq he
  refine ⟨s.reg out+3+1+t,_,?_,hall,hev,hee,?_,heb,?_⟩
  · have hp₁ : M+1≤(M+1)^7 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1≤7 by decide)
    have hbout := hs out
    have hfactor : 27000*(M+1)^7+1≤27020*(M+1)^7 := by omega
    have htime := ht.trans (Nat.mul_le_mul_left ps.length hfactor)
    rw [Nat.add_mul,Nat.one_mul]; omega
  · intro i hi hio
    rw [heo i hi hio,hcs]
    simp [TapeStore.setReg,hio]
  · simpa only [hcs,FieldConvolution.tapeData_setReg] using het

#print axioms factor_stops
#print axioms product_stops
end ExpandingCodes.Computation.TesterPowers
