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

def pointPrefix (d ell : ℕ) (h : 0<ell) (D : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) (k : ℕ) : Fin (2^ell) :=
  (EncodedTester.sum (BinaryField.indexOperations ell h)
    ((List.ofFn fun z : Fin ((2^ell)^d) => EncodedTester.term
      (BinaryField.indexOperations ell h) D y a b z).take k)).1

@[simp] theorem pointPrefix_zero (d ell : ℕ) (h : 0<ell) (D : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) :
    pointPrefix d ell h D y a b 0=BinaryField.zeroIndex ell := rfl

theorem pointPrefix_step (d ell : ℕ) (h : 0<ell) (D : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) (k : ℕ) (hk : k<(2^ell)^d) :
    pointValue d ell h D y a b ⟨k,hk⟩ (pointPrefix d ell h D y a b k)=
      pointPrefix d ell h D y a b (k+1) := by
  let O := BinaryField.indexOperations ell h
  let xs := List.ofFn (fun z : Fin ((2^ell)^d) => EncodedTester.term O D y a b z)
  have hi := BinaryField.indexOperations_interpretation ell h
  have hx : xs.take (k+1)=xs.take k++[EncodedTester.term O D y a b ⟨k,hk⟩] := by
    rw [List.take_succ_eq_append_getElem (by simpa [xs] using hk)]
    simp [xs]
  apply hi.injective
  change BinaryField.elements ell h (pointValue d ell h D y a b ⟨k,hk⟩ (EncodedTester.sum O (xs.take k)).1)=
    BinaryField.elements ell h (EncodedTester.sum O (xs.take (k+1))).1
  rw [hx,EncodedTester.sum_decode hi,List.map_append,List.sum_append]
  cases hy : y ⟨k,hk⟩ <;>
    simp [pointValue,EncodedTester.term,hy,hi.add,hi.mul,hi.zero,EncodedTester.sum_decode hi,O,add_comm]

@[simp] theorem pointPrefix_full (d ell : ℕ) (h : 0<ell) (D : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) :
    pointPrefix d ell h D y a b ((2^ell)^d)=
      (EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1 := by
  unfold pointPrefix EncodedTester.entry
  rw [List.take_of_length_le (by simp)]

theorem Core.setReg {d ell : ℕ} {h : 0<ell} {D M : ℕ}
    {y : Fin ((2^ell)^d) → Bool} {s : TapeStore (80+6*d) 3}
    (hc : Core d ell h D M y s) (i : Fin 80) (hi : 70 ≤ i.val) (hi70 : i≠70)
    (v : ℕ) (hv : v ≤ M) : Core d ell h D M y (s.setReg (low d i) v) := by
  have hne (j : Fin 80) (hj : j.val<70) : low d j≠low d i := by
    rw [ne_eq,low_eq_iff]
    intro he
    have hh := congrArg Fin.val he
    omega
  refine ⟨FieldPrograms.setReg_bound _ _ _ _ hc.bounded hv,?_,?_,?_,hc.inputMarked,hc.inputTable,hc.inputHead⟩
  · apply hc.environment.frame
    intro j hj
    rcases hj with rfl|rfl|rfl|rfl
    · exact Function.update_of_ne (hne 3 (by decide)) _ _
    · exact Function.update_of_ne (hne 19 (by decide)) _ _
    · exact Function.update_of_ne (hne 23 (by decide)) _ _
    · exact Function.update_of_ne (hne 24 (by decide)) _ _
  · simpa [TapeStore.setReg,Function.update_of_ne (hne 65 (by decide))] using hc.degree
  · simpa [TapeStore.setReg,Function.update_of_ne ((low_eq_iff d 70 i).not.mpr (Ne.symm hi70))] using hc.size

theorem Numbered.setReg {d : ℕ} {g : Fin 3} {q k : ℕ}
    {s : TapeStore (80+6*d) 3} (hn : Numbered d g q k s)
    (i : Fin 80) (hi : i≠23) (v : ℕ) : Numbered d g q k (s.setReg (low d i) v) := by
  apply hn.frame
  · simp [TapeStore.setReg,((low_eq_iff d 23 i).not.mpr (Ne.symm hi))]
  · intro j hj
    obtain ⟨k,rfl|rfl⟩ := (tuple_used d g j).mp hj
    all_goals simp [TapeStore.setReg,Function.update_of_ne (digit_ne_low d _ k i)]

/-- The semantic loop rule consumes the actual checked body's preserved countdown. -/
theorem loop_stops {R B L : ℕ} (P : TapeProgram R B L) (r : Fin R)
    (inp : Inputs) (C : ℕ) (Inv : ℕ → TapeStore R B → Prop)
    (hbody : ∀ n s,s.reg r=n+1 → Inv (n+1) s →
      ∃ t c,t ≤ C ∧ P.Stops inp ((TapeProgram.decStore r s).toCfg P.entry) t c ∧
        Inv n c.store ∧ c.reg r=n)
    (n : ℕ) (s : TapeStore R B) (hn : s.reg r=n) (hi : Inv n s) :
    ∃ t e,t ≤ n*(C+2)+1 ∧
      (TapeProgram.countedLoop P r).Stops inp (s.toCfg (TapeProgram.loopHeader L)) t
        (e.toCfg (TapeProgram.loopExit L)) ∧ Inv 0 e ∧ e.reg r=0 := by
  induction n generalizing s with
  | zero => exact ⟨1,s,by omega,TapeProgram.loop_zero P r inp s hn,hi,hn⟩
  | succ n ih =>
    obtain ⟨t,c,ht,hc,hIc,hcr⟩ := hbody n s hn hi
    obtain ⟨u,e,hu,he,hIe,her⟩ := ih c.store hcr hIc
    have hheader := TapeProgram.loop_positive_header P r inp s (by omega)
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2) (TapeProgram.loop_code_body_active P r)
    have hreturn := TapeProgram.loop_body_return P r inp c hc.halted
    refine ⟨1+t+1+u,e,?_,⟨((hheader.trans hrun).trans hreturn).trans he.exec,he.halted⟩,hIe,her⟩
    simp only [Nat.succ_mul]
    omega

structure PointLoopInv (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d))
    (origin : TapeStore (80+6*d) 3) (remaining : ℕ) (s : TapeStore (80+6*d) 3) : Prop where
  le : remaining ≤ (2^ell)^d
  core : Core d ell h D M y s
  aTuple : Numbered d 0 (2^ell) a.val s
  bTuple : Numbered d 1 (2^ell) b.val s
  zTuple : Numbered d 2 (2^ell) ((2^ell)^d-remaining) s
  index : s.reg (low d 73)=(2^ell)^d-remaining
  accumulator : s.reg (low d 69)=(pointPrefix d ell h D y a b ((2^ell)^d-remaining)).val
  high : ∀ i : Fin 80,70 ≤ i.val → i≠73 → i≠76 → i≠78 → s.reg (low d i)=origin.reg (low d i)
  payload : TapeStore.SamePayload s origin
  head : ∀ c : Fin 3,c≠2 → s.bufferHead c=origin.bufferHead c

theorem pointLoop_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d))
    (inp : Inputs) (s : TapeStore (80+6*d) 3) (hc : Core d ell h D M y s)
    (ha : Numbered d 0 (2^ell) a.val s) (hb : Numbered d 1 (2^ell) b.val s)
    (hz : Numbered d 2 (2^ell) 0 s) (hzi : s.reg (low d 73)=0)
    (hacc : s.reg (low d 69)=0) (hcount : s.reg (low d 76)=(2^ell)^d)
    (hdM : d*((2^ell)-1) ≤ M) (hhead : 1+(2^ell)^d*(2^ell) ≤ M) :
    ∃ t e,t ≤ (2^ell)^d*(pointTime d M+2)+1 ∧
      (TapeProgram.countedLoop (pointBody d) (low d 76)).Stops inp
        (s.toCfg (TapeProgram.countedLoop (pointBody d) (low d 76)).entry) t e ∧
      Core d ell h D M y e.store ∧
      e.reg (low d 69)=(EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1.val ∧
      Numbered d 0 (2^ell) a.val e.store ∧ Numbered d 1 (2^ell) b.val e.store ∧
      e.reg (low d 73)=(2^ell)^d ∧ e.reg (low d 76)=0 ∧
      (∀ i : Fin 80,70 ≤ i.val → i≠73 → i≠76 → i≠78 → e.reg (low d i)=s.reg (low d i)) ∧
      TapeStore.SamePayload e.store s ∧ (∀ c : Fin 3,c≠2 → e.bufferHead c=s.bufferHead c) := by
  let Inv := PointLoopInv d ell h D M y a b s
  have hbody (n : ℕ) (c : TapeStore (80+6*d) 3) (hcn : c.reg (low d 76)=n+1) (hi : Inv (n+1) c) :
      ∃ t e,t ≤ pointTime d M ∧ (pointBody d).Stops inp
        ((TapeProgram.decStore (low d 76) c).toCfg (pointBody d).entry) t e ∧ Inv n e.store ∧ e.reg (low d 76)=n := by
    let k := (2^ell)^d-(n+1)
    have hk : k<(2^ell)^d := by dsimp [k]; have := hi.le; omega
    have hkn : (2^ell)^d-n=k+1 := by dsimp [k]; have := hi.le; omega
    let c' := c.setReg (low d 76) n
    have hc' : TapeProgram.decStore (low d 76) c=c' := by
      simp only [TapeProgram.decStore,c',TapeStore.setReg,hcn,Nat.add_sub_cancel]
    have hbnd : n ≤ M := by have hh := hi.core.bounded (low d 76); rw [hcn] at hh; omega
    have hcore := hi.core.setReg 76 (by decide) (by decide) n hbnd
    have ha' := hi.aTuple.setReg 76 (by decide) n
    have hb' := hi.bTuple.setReg 76 (by decide) n
    have hz' := hi.zTuple.setReg 76 (by decide) n
    have hzi' : c'.reg (low d 73)=k := by simpa [c',TapeStore.setReg,k] using hi.index
    have hac' : c'.reg (low d 69)=(pointPrefix d ell h D y a b k).val := by
      simpa [c',TapeStore.setReg,k] using hi.accumulator
    obtain ⟨t,e,ht,he,hec,hev,hea,heb,hez,hei,hef,hep,heh⟩ :=
      pointBody_stops d ell h D M hM y a b ⟨k,hk⟩ (pointPrefix d ell h D y a b k) inp c'
        hcore ha' hb' hz' hzi' hac' hdM hhead
    refine ⟨t,e,ht,?_,?_,?_⟩
    · simpa only [hc'] using he
    · refine ⟨by have := hi.le; omega,hec,hea,heb,?_,?_,?_,?_,?_,?_⟩
      · simpa only [hkn] using hez
      · simpa only [hkn] using hei
      · change e.reg (low d 69)=_
        rw [hev,pointPrefix_step d ell h D y a b k hk,hkn]
      · intro i hi70 hi73 hi76 hi78
        change e.reg (low d i)=_
        rw [hef i hi70 hi73 hi78]
        change c'.reg (low d i)=_
        simp only [c',TapeStore.setReg,Function.update_of_ne ((low_eq_iff d _ _).not.mpr hi76)]
        exact hi.high i hi70 hi73 hi76 hi78
      · exact hep.trans ((TapeStore.setReg_payload c _ _).trans hi.payload)
      · intro b hb2
        change e.bufferHead b=_
        rw [heh b hb2]
        exact hi.head b hb2
    · rw [hef 76 (by decide) (by decide) (by decide)]
      simp [c',TapeStore.setReg]
  have hi : Inv ((2^ell)^d) s := by
    refine ⟨le_rfl,hc,ha,hb,?_,?_,?_,?_,TapeStore.SamePayload.refl _,?_⟩
    · simpa using hz
    · simpa using hzi
    · simpa [pointPrefix_zero,SamplerProgram.zeroIndex_value] using hacc
    · intro i hi hi73 hi76 hi78; rfl
    · intro c hc; rfl
  obtain ⟨t,e,ht,he,hie,hez⟩ := loop_stops (pointBody d) (low d 76) inp (pointTime d M) Inv hbody
    ((2^ell)^d) s hcount hi
  refine ⟨t,_,ht,he,hie.core,?_,hie.aTuple,hie.bTuple,?_,hez,hie.high,hie.payload,hie.head⟩
  · simpa only [Nat.sub_zero,pointPrefix_full] using hie.accumulator
  · simpa only [Nat.sub_zero] using hie.index

#print axioms pointLoop_stops

end ExpandingCodes.Computation.TesterGram
