import ExpandingCodes.Computation.TesterGram
import ExpandingCodes.Computation.TapeRename
import ExpandingCodes.Computation.GaussianProgram

set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterGram
open NKtLB
open ExpandingCodes.PolynomialStretch

def tuple (d : ℕ) (g : Fin 3) : List (SamplerOdometer.Digit (80+6*d)) :=
  List.ofFn (fun i : Fin d => (digit d ⟨2*g.val,by omega⟩ i,digit d ⟨2*g.val+1,by omega⟩ i))

@[simp] theorem tuple_zero (d : ℕ) : tuple d 0=aDigits d := rfl
@[simp] theorem tuple_one (d : ℕ) : tuple d 1=bDigits d := rfl
@[simp] theorem tuple_two (d : ℕ) : tuple d 2=zDigits d := rfl

theorem digit_injective (d : ℕ) {g h : Fin 6} {i j : Fin d}
    (he : digit d g i=digit d h j) : g=h ∧ i=j := by
  have hv := congrArg (Fin.val : Registers d → ℕ) he
  simp only [digit,Fin.val_mk] at hv
  have hi := i.isLt
  have hj := j.isLt
  have hg : g.val=h.val := by
    rcases lt_trichotomy g.val h.val with hl|he|hl
    · have hm := Nat.mul_le_mul_right d (show g.val+1 ≤ h.val by omega)
      rw [Nat.add_mul,Nat.one_mul] at hm
      omega
    · exact he
    · have hm := Nat.mul_le_mul_right d (show h.val+1 ≤ g.val by omega)
      rw [Nat.add_mul,Nat.one_mul] at hm
      omega
  exact ⟨Fin.ext hg,Fin.ext (by rw [hg] at hv; omega)⟩

theorem tuple_used (d : ℕ) (g : Fin 3) (j : Registers d) :
    j∈SamplerOdometer.used (tuple d g) ↔
      ∃ i : Fin d,j=digit d ⟨2*g.val,by omega⟩ i ∨ j=digit d ⟨2*g.val+1,by omega⟩ i := by
  rw [SamplerOdometer.used_mem_iff]
  simp only [tuple,List.mem_ofFn]
  constructor
  · rintro ⟨p,⟨i,rfl⟩,hi⟩
    exact ⟨i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨_,⟨i,rfl⟩,hi⟩

theorem low_not_tuple (d : ℕ) (g : Fin 3) (j : Fin 80) :
    low d j∉SamplerOdometer.used (tuple d g) := by
  rw [tuple_used]
  rintro ⟨i,he|he⟩ <;> exact digit_ne_low d _ i j he.symm

theorem tuple_nodup (d : ℕ) (g : Fin 3) :
    (SamplerOdometer.used (tuple d g)).Nodup := by
  have hgen (ps : List (SamplerOdometer.Digit (80+6*d)))
      (hl : ps.Pairwise (fun p q => p.1≠q.1 ∧ p.1≠q.2 ∧ p.2≠q.1 ∧ p.2≠q.2))
      (hp : ∀ p∈ps,p.1≠p.2) : (SamplerOdometer.used ps).Nodup := by
    induction ps with
    | nil => simp [SamplerOdometer.used]
    | cons p ps ih =>
      rw [List.pairwise_cons] at hl
      simp only [SamplerOdometer.used,List.nodup_cons,List.mem_cons,not_or]
      refine ⟨⟨hp p (by simp),?_⟩,?_,ih hl.2 (fun q hq => hp q (by simp [hq]))⟩
      · rw [SamplerOdometer.used_mem_iff]
        rintro ⟨q,hq,he|he⟩
        · exact (hl.1 q hq).1 he
        · exact (hl.1 q hq).2.1 he
      · rw [SamplerOdometer.used_mem_iff]
        rintro ⟨q,hq,he|he⟩
        · exact (hl.1 q hq).2.2.1 he
        · exact (hl.1 q hq).2.2.2 he
  apply hgen
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    have hne : i≠j := Fin.ne_of_lt hij
    refine ⟨?_,?_,?_,?_⟩
    · intro he; exact hne (digit_injective d he).2
    · intro he; have hh := congrArg Fin.val (digit_injective d he).1; simp at hh
    · intro he; have hh := congrArg Fin.val (digit_injective d he).1; simp at hh
    · intro he; exact hne (digit_injective d he).2
  · intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    intro he
    have hh := congrArg Fin.val (digit_injective d he).1
    simp at hh

theorem tuple_unique (d : ℕ) (g : Fin 3) :
    (low d 23::low d 2::SamplerOdometer.used (tuple d g)).Nodup := by
  simp only [List.nodup_cons,List.mem_cons,not_or]
  exact ⟨⟨by simp,low_not_tuple d g 23⟩,low_not_tuple d g 2,tuple_nodup d g⟩

def Numbered (d : ℕ) (g : Fin 3) (q k : ℕ) (s : TapeStore (80+6*d) 3) : Prop :=
  s.reg (low d 23)=q ∧ SamplerOdometer.Valid (low d 23) (tuple d g) s ∧
    Nat.ofDigits q (SamplerOdometer.readings (tuple d g) s)=k%q^d

theorem numbered_digits (d : ℕ) (g : Fin 3) (q k : ℕ) (hq : 1<q)
    (s : TapeStore (80+6*d) 3) (hn : Numbered d g q k s) (hk : k<q^d) :
    ∀ i,s.reg (digit d ⟨2*g.val,by omega⟩ i)=(EncodedTester.digits q d ⟨k,hk⟩ i).val := by
  let f : Fin d → Fin q := fun i => ⟨s.reg (digit d ⟨2*g.val,by omega⟩ i),by
    have hh := hn.2.1 _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simp only [Prod.fst,Prod.snd] at hh
    rw [hn.1] at hh
    omega⟩
  have hnum : Nat.ofDigits q (List.ofFn (fun i => (f i).val))=k := by
    have hh := hn.2.2
    simpa [SamplerOdometer.readings,tuple,List.map_ofFn,Nat.mod_eq_of_lt hk,f,Function.comp_def] using hh
  have hcanon := SamplerOdometer.canonical_digits q d f ⟨k,hk⟩ hnum
  intro i
  exact congrArg Fin.val (congrFun hcanon i)

theorem numbered_next (d : ℕ) (g : Fin 3) (q k : ℕ) (hq : 1<q)
    (s : TapeStore (80+6*d) 3) (hn : Numbered d g q k s) :
    Numbered d g q (k+1) (SamplerOdometer.nextStore (low d 23) (low d 2) (tuple d g) s) := by
  have hu := tuple_unique d g
  refine ⟨?_,SamplerOdometer.program_valid _ _ _ hu s hn.2.1,?_⟩
  · rw [SamplerOdometer.nextStore_fresh _ _ _ _ _ (by simp) (low_not_tuple d g 23)]
    exact hn.1
  · have hh := SamplerOdometer.program_number _ _ _ hu s hn.2.1 (by rw [hn.1]; exact hq)
    rw [hn.1,hn.2.2] at hh
    simpa [tuple,SamplerOdometer.readings,Nat.mod_add_mod] using hh

theorem numbered_initialize (d : ℕ) (g : Fin 3) (q : ℕ) (hq : 1<q)
    (s : TapeStore (80+6*d) 3) (hs : s.reg (low d 23)=q) :
    Numbered d g q 0 (SamplerOdometer.initializeStore (low d 23) (low d 2) (tuple d g) s) := by
  have hu := tuple_unique d g
  refine ⟨?_,SamplerOdometer.initializeStore_valid _ _ _ hu s (by omega),?_⟩
  · rw [SamplerOdometer.initializeStore_fresh _ _ _ _ _ (by simp) (low_not_tuple d g 23)]
    exact hs
  · have hv := SamplerOdometer.initializeStore_values _ _ _ hu s
    have hr : SamplerOdometer.readings (tuple d g)
        (SamplerOdometer.initializeStore (low d 23) (low d 2) (tuple d g) s)=List.replicate d 0 := by
      simp only [SamplerOdometer.readings,tuple,List.map_ofFn]
      rw [← List.ofFn_const]
      congr 1
      funext i
      exact (hv _ (List.mem_ofFn.mpr ⟨i,rfl⟩)).1
    rw [hr]
    simp

theorem Numbered.frame {d : ℕ} {g : Fin 3} {q k : ℕ}
    {s e : TapeStore (80+6*d) 3} (hn : Numbered d g q k s)
    (hq : e.reg (low d 23)=s.reg (low d 23))
    (hf : ∀ j,j∈SamplerOdometer.used (tuple d g) → e.reg j=s.reg j) :
    Numbered d g q k e := by
  refine ⟨hq.trans hn.1,?_,?_⟩
  · intro p hp
    rw [hf _ (SamplerOdometer.used_mem_left _ _ hp),
      hf _ (SamplerOdometer.used_mem_right _ _ hp),hq]
    exact hn.2.1 p hp
  · rw [SamplerOdometer.readings_congr _ e s
      (fun p hp => hf _ (SamplerOdometer.used_mem_left _ _ hp))]
    exact hn.2.2

theorem tuple_other (d : ℕ) (g h : Fin 3) (hgh : g≠h) (j : Registers d)
    (hj : j∈SamplerOdometer.used (tuple d g)) : j∉SamplerOdometer.used (tuple d h) := by
  rw [tuple_used] at hj ⊢
  obtain ⟨i,rfl|rfl⟩ := hj
  all_goals rintro ⟨k,hk|hk⟩
  all_goals have hh := congrArg Fin.val (digit_injective d hk).1
  all_goals apply hgh; apply Fin.ext; simp only [Fin.val_mk] at hh; omega

theorem numbered_next_other (d : ℕ) (g h : Fin 3) (hgh : g≠h) (q k : ℕ)
    (s : TapeStore (80+6*d) 3) (hn : Numbered d g q k s) :
    Numbered d g q k (SamplerOdometer.nextStore (low d 23) (low d 2) (tuple d h) s) := by
  apply hn.frame
  · exact SamplerOdometer.nextStore_fresh _ _ _ _ _ (by simp) (low_not_tuple d h 23)
  · intro j hj
    apply SamplerOdometer.nextStore_fresh
    · obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj
      all_goals exact digit_ne_low d _ i 2
    · exact tuple_other d g h hgh j hj

theorem inputLookup_injective (d : ℕ) : Function.Injective (inputLookup d) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [inputLookup]

theorem inputLookup_outside (d : ℕ) (j : Fin 80)
    (hj : j≠0 ∧ j≠1 ∧ j≠2 ∧ j≠4 ∧ j≠5 ∧ j≠23 ∧ j≠73 ∧ j≠78) :
    ∀ i,low d j ≠ inputLookup d i := by
  intro i
  fin_cases i <;> simp_all [inputLookup]

theorem tapeData_payload {R B : ℕ} {s e : TapeStore R B}
    (h : FieldConvolution.tapeData e=FieldConvolution.tapeData s) : TapeStore.SamePayload e s := by
  have hr := congrArg Prod.fst h
  have ho := congrArg (fun x => x.2.1) h
  have ht := congrArg (fun x => x.2.2.1) h
  exact ⟨hr,ho,fun c k => congrArg (fun t => (t c).getD k .blank) ht⟩

theorem tapeData_head {R B : ℕ} {s e : TapeStore R B}
    (h : FieldConvolution.tapeData e=FieldConvolution.tapeData s) : e.bufferHead=s.bufferHead :=
  congrArg (fun x => x.2.2.2) h

/-- Exactly the accumulator update performed by the positive/zero source branch. -/
def pointValue (d ell : ℕ) (h : 0<ell) (D : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b z : Fin ((2^ell)^d)) (acc : Fin (2^ell)) : Fin (2^ell) :=
  if y z then (BinaryField.indexOperations ell h).add
    ((BinaryField.indexOperations ell h).mul
      (EncodedTester.evaluation (BinaryField.indexOperations ell h) D a z).1
      (EncodedTester.evaluation (BinaryField.indexOperations ell h) D b z).1) acc
  else acc

def pointTime (d M : ℕ) :=
  64*(M+1)^2+(2*TesterEvaluation.timeBound d M+13300*(M+1)^6+28*M+32)+d*(8*M+20)+6

structure Core (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (s : TapeStore (80+6*d) 3) : Prop where
  bounded : ∀ j,s.reg j ≤ M
  environment : SamplerProgram.Environment (termWorkspace d) ell (BinaryPolynomial.selectedIndex ell h) s
  degree : s.reg (low d 65)=D
  size : s.reg (low d 70)=(2^ell)^d
  inputMarked : TapeArrays.BottomMarked s 2
  inputTable : TapeArrays.ThermometerTable s 2 (2^ell) (fun z => if y z then 1 else 0)
  inputHead : s.bufferHead 2 ≤ M

theorem pointBody_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
    (y : Fin ((2^ell)^d) → Bool) (a b z : Fin ((2^ell)^d)) (acc : Fin (2^ell))
    (inp : Inputs) (s : TapeStore (80+6*d) 3) (hc : Core d ell h D M y s)
    (ha : Numbered d 0 (2^ell) a.val s) (hb : Numbered d 1 (2^ell) b.val s)
    (hz : Numbered d 2 (2^ell) z.val s) (hzi : s.reg (low d 73)=z.val)
    (hacc : s.reg (low d 69)=acc.val) (hdM : d*((2^ell)-1) ≤ M)
    (hhead : 1+(2^ell)^d*(2^ell) ≤ M) :
    ∃ t e,t ≤ pointTime d M ∧ (pointBody d).Stops inp (s.toCfg (pointBody d).entry) t e ∧
      Core d ell h D M y e.store ∧
      e.reg (low d 69)=(pointValue d ell h D y a b z acc).val ∧
      Numbered d 0 (2^ell) a.val e.store ∧ Numbered d 1 (2^ell) b.val e.store ∧
      Numbered d 2 (2^ell) (z.val+1) e.store ∧ e.reg (low d 73)=z.val+1 ∧
      (∀ j : Fin 80,70 ≤ j.val → j≠73 → j≠78 → e.reg (low d j)=s.reg (low d j)) ∧
      TapeStore.SamePayload e.store s ∧ (∀ c : Fin 3,c≠2 → e.bufferHead c=s.bufferHead c) := by
  have hq : 1<2^ell := Nat.one_lt_pow h.ne' (by decide)
  have hq0 : s.reg (low d 23)=2^ell := hc.environment.cardinal
  have hv : TapeArrays.ThermometerAt s 2
      (TapeArrays.entryOffset (s.reg (low d 73)) (s.reg (low d 23))) (s.reg (low d 23))
      (if y z then 1 else 0) := by
    rw [hzi,hq0]
    exact hc.inputTable z
  obtain ⟨t₁,c₁,ht₁,h₁,hr₁,hv₁,hi₁,hq₁,hf₁,hb₁,hh₁,hp₁⟩ :=
    SamplerEvaluation.lookup_stops (inputLookup d) (inputLookup_injective d) 2 inp M s hc.bounded
      hc.inputHead hc.inputMarked.marked (if y z then 1 else 0) hv
  have hf₁low (i : Fin 80) (hi : i≠0 ∧ i≠1 ∧ i≠2 ∧ i≠4 ∧ i≠5 ∧ i≠23 ∧ i≠73 ∧ i≠78) :
      c₁.reg (low d i)=s.reg (low d i) := hf₁ _ (inputLookup_outside d i hi)
  have hf₁dig g i : c₁.reg (digit d g i)=s.reg (digit d g i) := by
    apply hf₁
    intro j
    fin_cases j <;> exact digit_ne_low d g i _
  have he₁ : SamplerProgram.Environment (termWorkspace d) ell (BinaryPolynomial.selectedIndex ell h) c₁.store := by
    apply hc.environment.frame
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact hf₁low 3 (by decide)
    · exact hf₁low 19 (by decide)
    · exact hq₁
    · exact hf₁low 24 (by decide)
  have hD₁ : c₁.reg (low d 65)=D := (hf₁low 65 (by decide)).trans hc.degree
  have hA₁ : c₁.reg (low d 69)=acc.val := (hf₁low 69 (by decide)).trans hacc
  have hdigits (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k s) :
      Numbered d g (2^ell) k c₁.store := by
    apply hn.frame hq₁
    intro j hj
    obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj <;> exact hf₁dig _ i
  obtain ⟨t₂,c₂,ht₂,h₂,hv₂,he₂,hf₂,hd₂,hb₂,hp₂,hh₂,hD₂⟩ :
      ∃ t c,t ≤ 2*TesterEvaluation.timeBound d M+13300*(M+1)^6+28*M+34 ∧
        (TapeProgram.branchZero (low d 78) TapeProgram.skip (maskedTerm d)).Stops inp
          (c₁.store.toCfg (TapeProgram.branchZero (low d 78) TapeProgram.skip (maskedTerm d)).entry) t c ∧
        c.reg (low d 69)=(pointValue d ell h D y a b z acc).val ∧
        SamplerProgram.Environment (termWorkspace d) ell (BinaryPolynomial.selectedIndex ell h) c.store ∧
        (∀ i : Fin 80,70 ≤ i.val → c.reg (low d i)=c₁.reg (low d i)) ∧
        (∀ g i,c.reg (digit d g i)=c₁.reg (digit d g i)) ∧ (∀ j,c.reg j ≤ M) ∧
        TapeStore.SamePayload c.store c₁.store ∧ c.bufferHead=c₁.bufferHead ∧ c.reg (low d 65)=D := by
    cases hy : y z with
    | false =>
      have hz₁ : c₁.reg (low d 78)=0 := by simpa [inputLookup,hy] using hv₁
      have hskip := TapeProgram.skip_stops inp c₁.store
      have hs := TapeProgram.branchZero_stops_zero (low d 78) TapeProgram.skip (maskedTerm d) inp c₁.store hz₁ hskip
      refine ⟨1,_,by omega,hs,?_,he₁,?_,?_,hb₁,TapeStore.SamePayload.refl _,rfl,hD₁⟩
      · simpa [pointValue,hy] using hA₁
      · intro i hi; rfl
      · intro g i; rfl
    | true =>
      obtain ⟨u,c,hu,hc',hcv,hce,hcf,hcd,hcb,hct,hcD⟩ := maskedTerm_stops d ell h a b z acc inp M hM c₁.store hb₁ he₁
        (numbered_digits d 0 _ _ hq _ (hdigits 0 _ ha) a.isLt)
        (numbered_digits d 1 _ _ hq _ (hdigits 1 _ hb) b.isLt)
        (numbered_digits d 2 _ _ hq _ (hdigits 2 _ hz) z.isLt) hA₁ hdM
      have hz₁ : c₁.reg (low d 78)≠0 := by
        have hvv : c₁.reg (low d 78)=1 := by simpa [inputLookup,hy] using hv₁
        omega
      have hs := TapeProgram.branchZero_stops_positive (low d 78) TapeProgram.skip (maskedTerm d) inp c₁.store hz₁ hc'
      refine ⟨2+u,_,by omega,hs,?_,hce,hcf,hcd,hcb,tapeData_payload hct,tapeData_head hct,hcD.trans hD₁⟩
      simpa [pointValue,hy,hD₁] using hcv
  have hq₂ : c₂.reg (low d 23)=s.reg (low d 23) := he₂.cardinal.trans hc.environment.cardinal.symm
  have hn₂ (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k s) :
      Numbered d g (2^ell) k c₂.store := by
    apply hn.frame hq₂
    intro j hj
    obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj
    all_goals exact (hd₂ _ i).trans (hf₁dig _ i)
  obtain ⟨t₃,c₃,ht₃,h₃,hs₃,hb₃⟩ := SamplerOdometer.program_stops_valid
    (low d 23) (low d 2) (tuple d 2) (tuple_unique d 2) inp M c₂.store hb₂ (hn₂ 2 _ hz).2.1
  have hf₃low (i : Fin 80) (hi : i≠2) : c₃.reg (low d i)=c₂.reg (low d i) := by
    change c₃.store.reg (low d i)=_
    rw [hs₃]
    exact SamplerOdometer.nextStore_fresh _ _ _ _ _ ((low_eq_iff d _ _).not.mpr hi) (low_not_tuple d 2 i)
  have hzi₂ : c₂.reg (low d 73)=z.val := (hf₂ 73 (by decide)).trans (hi₁.trans hzi)
  have hzi₃ : c₃.reg (low d 73)=z.val := (hf₃low 73 (by decide)).trans hzi₂
  have h₄ := TapeMacros.increment_stops (low d 73) inp c₃.store
  let e := (c₃.store.setReg (low d 73) (c₃.reg (low d 73)+1)).toCfg (1 : Fin 2)
  have hall := ((h₁.seq h₂).seq h₃).seq h₄
  have hbound : ∀ j,e.reg j ≤ M := by
    apply FieldPrograms.setReg_bound _ _ _ M hb₃
    rw [hzi₃]
    have hm := hc.bounded (low d 70)
    rw [hc.size] at hm
    omega
  have heq (j : Registers d) (hj : j≠low d 73) : e.reg j=c₃.reg j := by
    simp [e,TapeStore.setReg,hj]
  have henv₃ : SamplerProgram.Environment (termWorkspace d) ell (BinaryPolynomial.selectedIndex ell h) c₃.store := by
    apply he₂.frame
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl <;> exact hf₃low _ (by decide)
  have henv : SamplerProgram.Environment (termWorkspace d) ell (BinaryPolynomial.selectedIndex ell h) e.store := by
    apply henv₃.frame
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact heq (low d 3) (by simp)
    · exact heq (low d 19) (by simp)
    · exact heq (low d 23) (by simp)
    · exact heq (low d 24) (by simp)
  have hq₃ : c₃.reg (low d 23)=c₂.reg (low d 23) := hf₃low 23 (by decide)
  have hn₃ (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k c₃.store) :
      Numbered d g (2^ell) k e.store := by
    apply hn.frame (heq (low d 23) (by simp))
    intro j hj
    obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj <;> exact heq _ (digit_ne_low d _ i _)
  have hp₃ : TapeStore.SamePayload c₃.store c₂.store := by
    rw [hs₃]
    have hh := SamplerOdometer.nextStore_payload (low d 23) (low d 2) (tuple d 2) c₂.store
    exact ⟨hh.1,hh.2.1,fun c k => congrArg (fun t => (t c).getD k .blank) hh.2.2.1⟩
  have hh₃ : c₃.bufferHead=c₂.bufferHead := by
    change c₃.store.bufferHead=_
    rw [hs₃]
    exact (SamplerOdometer.nextStore_payload (low d 23) (low d 2) (tuple d 2) c₂.store).2.2.2
  have hp : TapeStore.SamePayload e.store s :=
    (TapeStore.setReg_payload _ _ _).trans (hp₃.trans (hp₂.trans hp₁))
  have hhigh (i : Fin 80) (hi : 70 ≤ i.val) (hi73 : i≠73) (hi78 : i≠78) :
      e.reg (low d i)=s.reg (low d i) := by
    rw [heq _ ((low_eq_iff d _ _).not.mpr hi73),hf₃low i (by intro he; subst i; norm_num at hi),hf₂ i hi]
    apply hf₁low
    have hne (k : Fin 80) (hk : k.val<70) : i≠k := by
      intro he
      subst i
      omega
    exact ⟨hne 0 (by decide),hne 1 (by decide),hne 2 (by decide),hne 4 (by decide),
      hne 5 (by decide),hne 23 (by decide),hi73,hi78⟩
  refine ⟨t₁+1+t₂+1+t₃+1+1,_,?_,hall,?_,?_,?_,?_,?_,?_,hhigh,hp,?_⟩
  · simp only [tuple,List.length_ofFn] at ht₃
    unfold pointTime
    omega
  · refine ⟨hbound,henv,?_,hhigh 70 (by decide) (by decide) (by decide) |>.trans hc.size,
        hc.inputMarked.of_payload hp,?_,?_⟩
    · change e.reg (low d 65)=D
      rw [heq (low d 65) (by simp),hf₃low 65 (by decide),hD₂]
    · intro z
      exact (hc.inputTable z).of_payload hp
    · change c₃.bufferHead 2 ≤ M
      rw [hh₃,hh₂,hh₁]
      simp only [Function.update_self]
      have hzlt := z.isLt
      change TapeArrays.entryOffset (s.reg (low d 73)) (s.reg (low d 23))+s.reg (low d 23) ≤ M
      rw [hzi,hq0]
      unfold TapeArrays.entryOffset
      have hm := Nat.mul_le_mul_right (2^ell) (show z.val+1 ≤ (2^ell)^d by omega)
      rw [Nat.add_mul,Nat.one_mul] at hm
      omega
  · rw [heq (low d 69) (by simp),hf₃low 69 (by decide),hv₂]
  · apply hn₃
    rw [hs₃]
    exact numbered_next_other d 0 2 (by decide) _ _ c₂.store (hn₂ 0 _ ha)
  · apply hn₃
    rw [hs₃]
    exact numbered_next_other d 1 2 (by decide) _ _ c₂.store (hn₂ 1 _ hb)
  · apply hn₃
    rw [hs₃]
    exact numbered_next d 2 _ _ hq c₂.store (hn₂ 2 _ hz)
  · simp [e,TapeStore.setReg,hzi₃]
  · intro c hc2
    change c₃.bufferHead c=s.bufferHead c
    rw [hh₃,hh₂,hh₁,Function.update_of_ne hc2]

#print axioms pointBody_stops

end ExpandingCodes.Computation.TesterGram
