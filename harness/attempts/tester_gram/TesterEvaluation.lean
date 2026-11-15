import ExpandingCodes.Computation.TesterPowers
import ExpandingCodes.Computation.SamplerOdometer

set_option autoImplicit false
open scoped BigOperators
namespace ExpandingCodes.Computation.TesterEvaluation
open NKtLB SamplerEvaluation SamplerProgram TesterPowers
open FieldPrograms UnaryArithmetic
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B : ℕ}

def sumLabels : List (Fin R) → ℕ
  | [] => 1
  | _::ps => sumLabels ps+9

def sumCore (dst tmp : Fin R) : (ps : List (Fin R)) → TapeProgram R B (sumLabels ps)
  | [] => TapeProgram.skip
  | p::ps => TapeProgram.seq (sumCore dst tmp ps) (TapeMacros.addPreserving p dst tmp)

def sumValue (values : Fin R → ℕ) (ps : List (Fin R)) : ℕ := (ps.map values).sum

theorem sumCore_stops (dst tmp : Fin R) (hdt : dst≠tmp) (ps : List (Fin R))
    (hp : ∀ p∈ps,p≠dst ∧ p≠tmp) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i  ≤  M) (htmp : s.reg tmp=0) (hresult : s.reg dst+sumValue s.reg ps  ≤  M) :
    ∃ t e,t  ≤  ps.length*(6*M+6) ∧
      (sumCore dst tmp ps).Stops inp (s.toCfg (sumCore (B := B) dst tmp ps).entry) t e ∧
      e.store=(s.setReg dst (s.reg dst+sumValue s.reg ps)).setReg tmp 0 ∧ ∀ i,e.reg i  ≤  M := by
  induction ps generalizing s with
  | nil =>
    refine ⟨0,s.toCfg ⟨0,by simp [sumLabels]⟩,by simp,TapeProgram.skip_stops inp s,?_,hs⟩
    change s=(s.setReg dst (s.reg dst+sumValue s.reg [])).setReg tmp 0
    simp only [sumValue,List.map_nil,List.sum_nil,Nat.add_zero,setReg_self]
    rw [← htmp,setReg_self]
  | cons p ps ih =>
    have hpp := hp p (by simp)
    have htail : s.reg dst+sumValue s.reg ps  ≤  M := by
      simpa [sumValue] using (show s.reg dst+(ps.map s.reg).sum  ≤  M by
        have hh := hresult
        simp only [sumValue,List.map_cons,List.sum_cons] at hh
        omega)
    obtain ⟨t,c,ht,hc,hcs,hcb⟩ := ih (fun a ha => hp a (by simp [ha])) s hs htmp htail
    obtain ⟨e,he,hes⟩ := TapeMacros.addPreserving_stops p dst tmp hpp.1 hpp.2 hdt inp c.store
    have hcv : c.reg p=s.reg p := by
      change c.store.reg p=_
      rw [hcs]; simp [TapeStore.setReg,hpp]
    have hct : c.reg tmp=0 := by change c.store.reg tmp=_; rw [hcs]; simp
    have hcd : c.reg dst=s.reg dst+sumValue s.reg ps := by
      change c.store.reg dst=_; rw [hcs]; simp [TapeStore.setReg,hdt]
    have hall := hc.seq he
    have hpost : e.store=(s.setReg dst (s.reg dst+sumValue s.reg (p::ps))).setReg tmp 0 := by
      rw [hes,hcs]
      simp only [TapeStore.setReg]
      congr 1
      funext i
      by_cases hit : i=tmp <;> by_cases hid : i=dst <;>
        simp_all [Function.update,sumValue,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    refine ⟨t+1+(c.reg tmp+5*c.reg p+5),_,?_,hall,hpost,?_⟩
    · rw [hct,hcv]
      have hsp := hs p
      change t+1+(0+5*s.reg p+5)  ≤  (ps.length+1)*(6*M+6)
      rw [Nat.add_mul,Nat.one_mul]; omega
    · intro i
      change e.store.reg i  ≤  M
      rw [hpost]
      exact setReg_bound _ _ 0 M (setReg_bound s _ _ M hs hresult) (by omega) i

/-- The finite sum routine preserves every digit counter. -/
def sumDigits (dst tmp : Fin R) (ps : List (Fin R)) : TapeProgram R B (4+sumLabels ps) :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.clear dst) (TapeMacros.clear tmp)) (sumCore dst tmp ps)

theorem sumDigits_stops (dst tmp : Fin R) (hdt : dst≠tmp) (ps : List (Fin R))
    (hp : ∀ p∈ps,p≠dst ∧ p≠tmp) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i  ≤  M) (hresult : sumValue s.reg ps  ≤  M) :
    ∃ t e,t  ≤  (ps.length+1)*(8*M+10) ∧
      (sumDigits dst tmp ps).Stops inp (s.toCfg (sumDigits (B := B) dst tmp ps).entry) t e ∧
      e.store=(s.setReg dst (sumValue s.reg ps)).setReg tmp 0 ∧ ∀ i,e.reg i  ≤  M := by
  have h₁ := TapeMacros.clear_stops dst inp (s.reg dst) s rfl
  have h₂ := TapeMacros.clear_stops tmp inp ((s.setReg dst 0).reg tmp) (s.setReg dst 0) rfl
  let p := (s.setReg dst 0).setReg tmp 0
  have hpbound : ∀ i,p.reg i  ≤  M := setReg_bound _ _ 0 M (setReg_bound s _ 0 M hs (by omega)) (by omega)
  have hvalues : sumValue p.reg ps=sumValue s.reg ps := by
    unfold sumValue
    congr 1
    apply List.map_congr_left
    intro a ha
    simp [p,TapeStore.setReg,hp a ha]
  obtain ⟨t,e,ht,he,hes,heb⟩ := sumCore_stops dst tmp hdt ps hp inp M p hpbound (by simp [p])
    (by
      have hz : p.reg dst=0 := by simp [p,TapeStore.setReg,hdt]
      rw [hz,hvalues]
      simpa using hresult)
  have hall := (h₁.seq h₂).seq he
  refine ⟨s.reg dst+1+1+((s.setReg dst 0).reg tmp+1)+1+t,_,?_,hall,?_,heb⟩
  · have hb₁ := hs dst; have hb₂ := hs tmp
    have htmp : (s.setReg dst 0).reg tmp=s.reg tmp := by simp [TapeStore.setReg,Ne.symm hdt]
    have ht' := ht.trans (Nat.mul_le_mul_left ps.length (show 6*M+6  ≤  8*M+10 by omega))
    rw [htmp,Nat.add_mul,Nat.one_mul]
    omega
  · change e.store=_
    rw [hes,hvalues]
    simp only [p,TapeStore.setReg]
    congr 1
    funext i
    by_cases hit : i=tmp <;> by_cases hid : i=dst <;> simp_all [Function.update]

/-- Caller locations: result0, degree1, exponent-sum2, comparison flag3. -/
def comparison (r : Fin 33 → Fin R) (c : Fin 4 → Fin R) : Fin 6 → Fin R :=
  ![c 1,c 2,c 3,r 0,r 1,r 2]

theorem comparison_injective (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (c : Fin 4 → Fin R) (hc : Function.Injective c) (hcr : ∀ i j,c i≠r j) :
    Function.Injective (comparison r c) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [comparison,hr.eq_iff,hc.eq_iff,hcr,Ne.symm]

/-- Total-degree guard around the physical monomial evaluator. It has a finite
code table determined by the static digit-register list, not its contents. -/
def evaluate (r : Fin 33 → Fin R) (c : Fin 4 → Fin R) (ps : List (Fin R × Fin R)) :
    TapeProgram R B (((4+sumLabels (ps.map Prod.fst))+33)+((4+productLabels ps)+2+2)) :=
  TapeProgram.seq (TapeProgram.seq (sumDigits (c 2) (r 2) (ps.map Prod.fst))
    (ParameterPrograms.lessThan (comparison r c)))
      (TapeProgram.branchZero (c 3) (TesterPowers.product r (c 0) ps) (TapeMacros.clear (c 0)))

/-- Exact frame of the preserving comparison, convenient for composing a field
workspace without unfolding the scalar comparison's internal source. -/
theorem lessThanStore_frame (r : Fin 6 → Fin R) (s : TapeStore R B) (j : Fin R)
    (hj : j≠r 2 ∧ j≠r 3 ∧ j≠r 4 ∧ j≠r 5) :
    (ParameterPrograms.lessThanStore r s).reg j=s.reg j := by
  simp [ParameterPrograms.lessThanStore,ParameterPrograms.lessCore,ParameterPrograms.lessPrepare,
    ParameterPrograms.ltLoopStore,TapeStore.setReg,hj]

/-- The exact encoded list semantics; canonical odometer digits instantiate the
list in the full eager Gram construction. -/
def value (ell : ℕ) (h : 0<ell) (degree : ℕ)
    (values : Fin R → Fin (2^ell)) (exponents : Fin R → ℕ) (ps : List (Fin R × Fin R)) : Fin (2^ell) :=
  if sumValue exponents (ps.map Prod.fst)  ≤  degree then productValue ell h values exponents ps
  else BinaryField.zeroIndex ell


def timeBound (d M : ℕ) : ℕ :=
  (d+1)*(8*M+10)+64*(M+1)+max ((d+1)*(27020*(M+1)^7)) (M+1)+4

theorem evaluate_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (c : Fin 4 → Fin R) (hc : Function.Injective c) (hcr : ∀ i j,c i≠r j)
    (ps : List (Fin R × Fin R))
    (hp : ∀ p∈ps,(∀ i,p.1≠r i) ∧ (∀ i,p.2≠r i) ∧ (∀ i,p.1≠c i) ∧ (∀ i,p.2≠c i))
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell)) (exponents : Fin R → ℕ)
    (M : ℕ) (hM : 1  ≤  M) (s : TapeStore R B) (hs : ∀ i,s.reg i  ≤  M)
    (henv : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) s)
    (hv : ∀ p∈ps,s.reg p.2=(values p.2).val ∧ s.reg p.1=exponents p.1)
    (hsum : sumValue exponents (ps.map Prod.fst)  ≤  M) :
    ∃ t e,t  ≤  timeBound ps.length M ∧
      (evaluate r c ps).Stops inp (s.toCfg (evaluate (B := B) r c ps).entry) t e ∧
      e.reg (c 0)=(value ell h (s.reg (c 1)) values exponents ps).val ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → i≠c 0 → i≠c 2 → i≠c 3 → e.reg i=s.reg i) ∧
      (∀ i,e.reg i  ≤  M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  have hpsum : ∀ p∈ps.map Prod.fst,p≠c 2 ∧ p≠r 2 := by
    intro p hpm
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hpm
    exact ⟨(hp a ha).2.2.1 2,(hp a ha).1 2⟩
  have hsumval : sumValue s.reg (ps.map Prod.fst)=sumValue exponents (ps.map Prod.fst) := by
    unfold sumValue
    congr 1
    apply List.map_congr_left
    intro p hpm
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hpm
    exact (hv a ha).2
  obtain ⟨u,d,hu,hd,hds,hdb⟩ := sumDigits_stops (c 2) (r 2) (hcr 2 2)
    (ps.map Prod.fst) hpsum inp M s hs (by rw [hsumval]; exact hsum)
  have hde : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) d.store := by
    rw [hds]
    exact (henv.setExternal (c 2) _ (fun i => hcr 2 ⟨i.val,by omega⟩)).setReg
      (powerWorkspace_injective _ (scalar_injective r hr)) 2 0 (by decide)
  have hdframe (j : Fin R) (hj : j≠c 2) (hjr : j≠r 2) : d.reg j=s.reg j := by
    change d.store.reg j=_
    rw [hds]; simp [TapeStore.setReg,hj,hjr]
  have hddegree : d.reg (c 1)=s.reg (c 1) := hdframe _ (hc.ne (by decide)) (hcr 1 2)
  have hdsum : d.reg (c 2)=sumValue exponents (ps.map Prod.fst) := by
    change d.store.reg (c 2)=_
    rw [hds]; simp [TapeStore.setReg,hcr,hsumval]
  have hdvalues : ∀ p∈ps,d.store.reg p.2=(values p.2).val ∧ d.store.reg p.1=exponents p.1 := by
    intro p hpm
    have hh := hp p hpm
    exact ⟨(hdframe p.2 (hh.2.2.2 2) (hh.2.1 2)).trans (hv p hpm).1,
      (hdframe p.1 (hh.2.2.1 2) (hh.1 2)).trans (hv p hpm).2⟩
  obtain ⟨v,f,hvtime,hf,hfs⟩ := ParameterPrograms.lessThan_stops (comparison r c)
    (comparison_injective r hr c hc hcr) inp M hM d.store hdb
  have hfb : ∀ j,f.reg j  ≤  M := by
    change ∀ j,f.store.reg j  ≤  M
    rw [hfs]
    exact ParameterPrograms.lessThanStore_bound _ (comparison_injective r hr c hc hcr) d.store M hM hdb
  have hfframe (j : Fin R) (hj : j≠c 3) (hjr : ∀ i : Fin 3,j≠r ⟨i.val,by omega⟩) : f.reg j=d.reg j := by
    change f.store.reg j=_
    rw [hfs]
    exact lessThanStore_frame _ _ _ (by simpa [comparison] using
      (show j≠c 3 ∧ j≠r 0 ∧ j≠r 1 ∧ j≠r 2 from ⟨hj,hjr 0,hjr 1,hjr 2⟩))
  have hfe : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) f.store := by
    apply hde.frame
    intro i hi
    change f.reg (powerWorkspace (scalar r) i)=d.reg (powerWorkspace (scalar r) i)
    exact hfframe _ (Ne.symm (hcr 3 ⟨i.val,by omega⟩)) (by
      intro j heq
      have hval := congrArg Fin.val (hr heq)
      simp only [powerWorkspace,scalar,Fin.val_mk] at hval
      have hjlt := j.isLt
      rcases hi with rfl|rfl|rfl|rfl <;> norm_num at hval <;> omega)
  have hflag : f.reg (c 3)=if s.reg (c 1)<sumValue exponents (ps.map Prod.fst) then 1 else 0 := by
    change f.store.reg ((comparison r c) 2)=_
    rw [hfs,ParameterPrograms.lessThanStore_value _ (comparison_injective r hr c hc hcr)]
    change (if d.reg (c 1)<d.reg (c 2) then 1 else 0)=_
    rw [hddegree,hdsum]
  have hfvalues : ∀ p∈ps,f.store.reg p.2=(values p.2).val ∧ f.store.reg p.1=exponents p.1 := by
    intro p hpm
    have hh := hp p hpm
    exact ⟨(hfframe p.2 (hh.2.2.2 3) (fun i => hh.2.1 ⟨i.val,by omega⟩)).trans (hdvalues p hpm).1,
      (hfframe p.1 (hh.2.2.1 3) (fun i => hh.1 ⟨i.val,by omega⟩)).trans (hdvalues p hpm).2⟩
  have hprefixdata : FieldConvolution.tapeData f.store=FieldConvolution.tapeData s := by
    rw [hfs,hds]
    rfl
  have hprefixframe (i : Fin R) (hi : ∀ v,i≠r v) (hi₂ : i≠c 2) (hi₃ : i≠c 3) : f.reg i=s.reg i :=
    (hfframe i hi₃ (fun j => hi ⟨j.val,by omega⟩)).trans (hdframe i hi₂ (hi 2))
  have hbranch : ∃ t e,t  ≤  max ((ps.length+1)*(27020*(M+1)^7)) (M+1)+2 ∧
      (TapeProgram.branchZero (c 3) (TesterPowers.product r (c 0) ps) (TapeMacros.clear (c 0))).Stops inp
        (f.store.toCfg (TapeProgram.branchZero (c 3) (TesterPowers.product (B := B) r (c 0) ps) (TapeMacros.clear (c 0))).entry) t e ∧
      e.reg (c 0)=(value ell h (s.reg (c 1)) values exponents ps).val ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → i≠c 0 → e.reg i=f.reg i) ∧
      (∀ i,e.reg i  ≤  M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData f.store := by
    by_cases hle : sumValue exponents (ps.map Prod.fst)  ≤  s.reg (c 1)
    · obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := TesterPowers.product_stops r hr (c 0) (hcr 0) ps
        (fun p hpm => ⟨(hp p hpm).1,(hp p hpm).2.1,(hp p hpm).2.2.1 0,(hp p hpm).2.2.2 0⟩)
        inp ell h values exponents M hM f.store hfb hfe hfvalues
      have hz : f.reg (c 3)=0 := by rw [hflag]; simp [show ¬s.reg (c 1)<sumValue exponents (ps.map Prod.fst) by omega]
      have hbr := TapeProgram.branchZero_stops_zero (c 3) (TesterPowers.product r (c 0) ps)
        (TapeMacros.clear (c 0)) inp f.store hz he
      refine ⟨1+t,e.mapPC (TapeProgram.branchLeft 2),?_,hbr,?_,hee,heo,heb,het⟩
      · have hh := le_max_left ((ps.length+1)*(27020*(M+1)^7)) (M+1); omega
      · simpa [value,hle] using hev
    · have hpflag : f.reg (c 3)≠0 := by rw [hflag]; simp [show s.reg (c 1)<sumValue exponents (ps.map Prod.fst) by omega]
      have hclear := TapeMacros.clear_stops (c 0) inp (f.reg (c 0)) f.store rfl
      have hbr := TapeProgram.branchZero_stops_positive (c 3) (TesterPowers.product r (c 0) ps)
        (TapeMacros.clear (c 0)) inp f.store hpflag hclear
      refine ⟨2+(f.reg (c 0)+1),_,?_,hbr,?_,?_,?_,?_,rfl⟩
      · have hh := le_max_right ((ps.length+1)*(27020*(M+1)^7)) (M+1)
        have hbout := hfb (c 0); omega
      · simp [value,hle,TapeCfg.mapPC,TapeStore.toCfg,zeroIndex_value]
      · exact hfe.setExternal (c 0) 0 (fun i => hcr 0 ⟨i.val,by omega⟩)
      · intro i hi hio
        simp [TapeCfg.mapPC,TapeStore.toCfg,TapeStore.setReg,hio]
      · exact setReg_bound f.store _ 0 M hfb (by omega)
  obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := hbranch
  have hall := (hd.seq hf).seq he
  refine ⟨u+1+v+1+t,_,?_,hall,hev,hee,?_,heb,het.trans hprefixdata⟩
  · have hlen : (ps.map Prod.fst).length=ps.length := by simp
    unfold timeBound
    rw [hlen] at hu
    omega
  · intro i hi hi₀ hi₂ hi₃
    exact (heo i hi hi₀).trans (hprefixframe i hi hi₂ hi₃)


theorem value_canonical {d : ℕ} (ell : ℕ) (h : 0<ell) (degree : ℕ)
    (exp point : Fin d → Fin R) (values : Fin R → Fin (2^ell)) (exponents : Fin R → ℕ)
    (a z : Fin ((2^ell)^d))
    (ha : ∀ i,exponents (exp i)=(EncodedTester.digits (2^ell) d a i).val)
    (hz : ∀ i,values (point i)=EncodedTester.digits (2^ell) d z i) :
    value ell h degree values exponents (List.ofFn fun i => (exp i,point i))=
      (EncodedTester.evaluation (BinaryField.indexOperations ell h) degree a z).1 := by
  have hsum : sumValue exponents ((List.ofFn fun i => (exp i,point i)).map Prod.fst)=
      ∑ i,(EncodedTester.digits (2^ell) d a i).val := by
    simp [sumValue,List.map_ofFn,Function.comp_def,ha,List.sum_ofFn]
  have hprod : productValue ell h values exponents (List.ofFn fun i => (exp i,point i))=
      (EncodedTester.product (BinaryField.indexOperations ell h)
        (List.ofFn fun i => EncodedTester.power (BinaryField.indexOperations ell h)
          (EncodedTester.digits (2^ell) d z i) (EncodedTester.digits (2^ell) d a i).val)).1 := by
    rw [productValue_eq]
    simp [List.map_ofFn,Function.comp_def,ha,hz]
  unfold value EncodedTester.evaluation
  rw [hsum]
  split_ifs
  · exact hprod
  · rfl

/-- Direct canonical evaluation contract for physical digit counters. The finite
source is selected by fixed register maps before the runtime digits are known. -/
theorem evaluate_canonical_stops {d : ℕ} (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (c : Fin 4 → Fin R) (hc : Function.Injective c) (hcr : ∀ i j,c i≠r j)
    (exp point : Fin d → Fin R)
    (hexp : ∀ j,(∀ i,exp j≠r i) ∧ (∀ i,exp j≠c i))
    (hpoint : ∀ j,(∀ i,point j≠r i) ∧ (∀ i,point j≠c i))
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (a z : Fin ((2^ell)^d))
    (M : ℕ) (hM : 1  ≤  M) (s : TapeStore R B) (hs : ∀ i,s.reg i  ≤  M)
    (henv : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) s)
    (ha : ∀ i,s.reg (exp i)=(EncodedTester.digits (2^ell) d a i).val)
    (hz : ∀ i,s.reg (point i)=(EncodedTester.digits (2^ell) d z i).val)
    (hdM : d*((2^ell)-1)  ≤  M) :
    ∃ t e,t  ≤  timeBound d M ∧
      (evaluate r c (List.ofFn fun i => (exp i,point i))).Stops inp
        (s.toCfg (evaluate (B := B) r c (List.ofFn fun i => (exp i,point i))).entry) t e ∧
      e.reg (c 0)=(EncodedTester.evaluation (BinaryField.indexOperations ell h) (s.reg (c 1)) a z).1.val ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → i≠c 0 → i≠c 2 → i≠c 3 → e.reg i=s.reg i) ∧
      (∀ i,e.reg i  ≤  M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  let values (j : Fin R) : Fin (2^ell) := if hj : s.reg j<2^ell then ⟨s.reg j,hj⟩ else BinaryField.zeroIndex ell
  have hvalues (i : Fin d) : values (point i)=EncodedTester.digits (2^ell) d z i := by
    have hj : s.reg (point i)<2^ell := by rw [hz]; exact (EncodedTester.digits (2^ell) d z i).isLt
    apply Fin.ext
    simpa [values,hj] using hz i
  have hp : ∀ p∈List.ofFn (fun i => (exp i,point i)),
      (∀ i,p.1≠r i) ∧ (∀ i,p.2≠r i) ∧ (∀ i,p.1≠c i) ∧ (∀ i,p.2≠c i) := by
    intro p hpm
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hpm
    exact ⟨(hexp i).1,(hpoint i).1,(hexp i).2,(hpoint i).2⟩
  have hv : ∀ p∈List.ofFn (fun i => (exp i,point i)),s.reg p.2=(values p.2).val ∧ s.reg p.1=s.reg p.1 := by
    intro p hpm
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hpm
    exact ⟨by rw [hvalues]; exact hz i,rfl⟩
  have hsum : sumValue s.reg ((List.ofFn fun i => (exp i,point i)).map Prod.fst)  ≤  M := by
    have hle : (∑ i : Fin d,(EncodedTester.digits (2^ell) d a i).val)  ≤  d*((2^ell)-1) := by
      calc
        _  ≤  ∑ _i : Fin d,((2^ell)-1) := Finset.sum_le_sum (by
          intro i hi
          have hh := (EncodedTester.digits (2^ell) d a i).isLt
          omega)
        _ = d*((2^ell)-1) := by simp
    simpa [sumValue,List.map_ofFn,Function.comp_def,ha,List.sum_ofFn] using hle.trans hdM
  obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := evaluate_stops r hr c hc hcr
    (List.ofFn fun i => (exp i,point i)) hp inp ell h values s.reg M hM s hs henv hv hsum
  refine ⟨t,e,by simpa using ht,he,?_,hee,heo,heb,het⟩
  rw [value_canonical ell h (s.reg (c 1)) exp point values s.reg a z ha hvalues] at hev
  exact hev

#print axioms sumCore_stops
#print axioms sumDigits_stops
#print axioms evaluate_stops
#print axioms evaluate_canonical_stops

/-- Frozen integer-floor cutoff agrees with its nonnegative unary formula
for the construction parameter range. -/
theorem auxiliaryDegree_nat (q d : ℕ) (hd : 4 ≤ d) (hq : 2 ≤ q) :
    auxiliaryDegree q d=((d-3)*(q-1)-1)/2 := by
  have hdcast : ((d-3 : ℕ) : ℤ)=(d : ℤ)-3 := by omega
  have hqcast : ((q-1 : ℕ) : ℤ)=(q : ℤ)-1 := by omega
  have hprod : 1 ≤ (d-3)*(q-1) := by
    have hh := Nat.mul_le_mul (show 1 ≤ d-3 by omega) (show 1 ≤ q-1 by omega)
    simpa using hh
  have hnum : (((d-3)*(q-1)-1 : ℕ) : ℤ)=((d : ℤ)-3)*((q : ℤ)-1)-1 := by
    rw [Nat.cast_sub hprod,Nat.cast_mul,hdcast,hqcast]
    norm_num
  unfold auxiliaryDegree
  rw [← hnum]
  rfl

/-- Five scalar counters: q0 is preserved; result4 receives the degree cutoff.
The dimension affects only a finite static number of unary additions. -/
def degree (r : Fin 5 → Fin R) (d : ℕ) : TapeProgram R B (((((11+2)+2)+SamplerEvaluation.scaleLabels (d-3))+2)+9) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeMacros.copy (r 0) (r 1) (r 3)) (SamplerOdometer.decrement (r 1)))
    (TapeMacros.clear (r 2))) (SamplerEvaluation.scaleAdd (r 1) (r 2) (r 3) (d-3)))
    (SamplerOdometer.decrement (r 2))) (FieldPrograms.halve (r 2) (r 4) (r 3))

def degreePrepare (r : Fin 5 → Fin R) (s : TapeStore R B) : TapeStore R B :=
  ((s.setReg (r 1) (s.reg (r 0)-1)).setReg (r 3) 0).setReg (r 2) 0

def degreeScaled (r : Fin 5 → Fin R) (d : ℕ) (s : TapeStore R B) : TapeStore R B :=
  SamplerEvaluation.scaleStore (r 1) (r 2) (r 3) (d-3) (degreePrepare r s)

def degreeStore (r : Fin 5 → Fin R) (d : ℕ) (s : TapeStore R B) : TapeStore R B :=
  FieldPrograms.halfStore ((degreeScaled r d s).setReg (r 2) ((d-3)*(s.reg (r 0)-1)-1)) (r 2) (r 4) (r 3)

theorem degree_stops (r : Fin 5 → Fin R) (hr : Function.Injective r) (d : ℕ)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (s : TapeStore R B) (hs : ∀ i,s.reg i ≤ M)
    (hprod : (d-3)*(s.reg (r 0)-1) ≤ M) :
    ∃ t e,t ≤ (d+1)*(30*(M+1)) ∧
      (degree r d).Stops inp (s.toCfg (degree (B := B) r d).entry) t e ∧
      e.store=degreeStore r d s ∧
      e.reg (r 4)=((d-3)*(s.reg (r 0)-1)-1)/2 ∧
      (∀ i,(∀ j,i≠r j) → e.reg i=s.reg i) ∧
      (∀ i,e.reg i ≤ M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := copy_stops_bound (r 0) (r 1) (r 3)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M s hs
  have h₂ := SamplerOdometer.decrement_stops (r 1) inp c₁.store
  have hpred : c₁.store.setReg (r 1) (c₁.reg (r 1)-1)=
      (s.setReg (r 1) (s.reg (r 0)-1)).setReg (r 3) 0 := by
    rw [show c₁.reg (r 1)=s.reg (r 0) by rw [show c₁.reg (r 1)=c₁.store.reg (r 1) from rfl,hs₁]; simp [reg_layout r hr]]
    rw [hs₁]
    simp only [TapeStore.setReg]
    congr 1
    funext i
    by_cases h₁ : i=r 1 <;> by_cases h₃ : i=r 3 <;> simp_all [Function.update,hr.eq_iff]
  have h₃ := TapeMacros.clear_stops (r 2) inp ((c₁.store.setReg (r 1) (c₁.reg (r 1)-1)).reg (r 2))
    (c₁.store.setReg (r 1) (c₁.reg (r 1)-1)) rfl
  have hprepare : (c₁.store.setReg (r 1) (c₁.reg (r 1)-1)).setReg (r 2) 0=degreePrepare r s := by rw [hpred]; rfl
  obtain ⟨c₄,h₄,hs₄⟩ := SamplerEvaluation.scaleAdd_stops (r 1) (r 2) (r 3)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) (d-3) inp (degreePrepare r s)
    (by simp [degreePrepare,reg_layout r hr])
  have hscaled : c₄.store=degreeScaled r d s := hs₄
  have hv₄ : c₄.reg (r 2)=(d-3)*(s.reg (r 0)-1) := by
    change c₄.store.reg (r 2)=_
    rw [hscaled]
    simp [degreeScaled,scaleStore,degreePrepare,reg_layout r hr]
  have h₅ := SamplerOdometer.decrement_stops (r 2) inp c₄.store
  obtain ⟨e,h₆,hs₆⟩ := FieldPrograms.halve_stops (r 2) (r 4) (r 3)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp (c₄.store.setReg (r 2) (c₄.reg (r 2)-1))
  rw [← hprepare] at h₄
  have hall := ((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆
  have hpost : e.store=degreeStore r d s := by rw [hs₆,hv₄,hscaled]; rfl
  have hpb : ∀ i,(degreePrepare r s).reg i ≤ M := by
    unfold degreePrepare
    exact setReg_bound _ _ 0 M (setReg_bound _ _ 0 M
      (setReg_bound s _ _ M hs ((Nat.sub_le _ _).trans (hs (r 0)))) (by omega)) (by omega)
  have hsb : ∀ i,(degreeScaled r d s).reg i ≤ M := by
    apply SamplerEvaluation.scaleStore_bound_exact _ _ _ _ M _ hpb
    simpa [degreePrepare,reg_layout r hr] using hprod
  have hfinal : ∀ i,(degreeStore r d s).reg i ≤ M := by
    unfold degreeStore FieldPrograms.halfStore
    apply setReg_bound
    · apply setReg_bound
      · exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hsb ((Nat.sub_le _ _).trans hprod)) (by omega)
      · simpa [reg_layout r hr] using (Nat.div_le_self ((d-3)*(s.reg (r 0)-1)-1) 2).trans ((Nat.sub_le _ _).trans hprod)
    · simp only [reg_layout r hr,ite_true]
      have hh := Nat.mod_lt ((d-3)*(s.reg (r 0)-1)-1) (by omega : 0<2)
      omega
  refine ⟨_,_,?_,hall,hpost,?_,?_,?_,?_⟩
  · have hq := hs (r 0)
    have hb₂ := hs (r 2)
    have hb₄ : c₄.reg (r 4) ≤ M := by
      change c₄.store.reg (r 4) ≤ M
      rw [hscaled]; exact hsb (r 4)
    have hzero : c₄.reg (r 3)=0 := by
      change c₄.store.reg (r 3)=_
      rw [hscaled]; simp [degreeScaled,scaleStore]
    have hc₁₂ : c₁.reg (r 2)=s.reg (r 2) := by
      change c₁.store.reg (r 2)=_
      rw [hs₁]; simp [reg_layout r hr]
    have hc₁₁ : c₁.reg (r 1)=s.reg (r 0) := by
      change c₁.store.reg (r 1)=_
      rw [hs₁]; simp [reg_layout r hr]
    have hpredbound : (d-3)*(s.reg (r 0)-1)-1 ≤ M := (Nat.sub_le _ _).trans hprod
    have htime : 3*(((d-3)*(s.reg (r 0)-1)-1)/2)+2*(((d-3)*(s.reg (r 0)-1)-1)%2)+1 ≤ 2*((d-3)*(s.reg (r 0)-1)-1)+1 :=
      UnaryArithmetic.halveLoop_time_le _
    have hscale : (d-3)*(5*(s.reg (r 0)-1)+6) ≤ d*(5*M+6) :=
      Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
    change _ ≤ (d+1)*(30*(M+1))
    simp only [reg_layout r hr,show (2:Fin 5)≠1 by decide,show (4:Fin 5)≠2 by decide,
      show (3:Fin 5)≠2 by decide,show (1:Fin 5)≠2 by decide,if_false,if_true,hv₄,hzero,hc₁₂,hc₁₁]
    nlinarith
  · change e.store.reg (r 4)=_
    rw [hpost]
    simp [degreeStore,FieldPrograms.halfStore,reg_layout r hr]
  · intro i hi
    change e.store.reg i=_
    rw [hpost]
    simp [degreeStore,FieldPrograms.halfStore,degreeScaled,scaleStore,degreePrepare,TapeStore.setReg,hi]
  · change ∀ i,e.store.reg i ≤ M
    rw [hpost]; exact hfinal
  · change FieldConvolution.tapeData e.store=_
    rw [hpost]; rfl

#print axioms degree_stops

end ExpandingCodes.Computation.TesterEvaluation
