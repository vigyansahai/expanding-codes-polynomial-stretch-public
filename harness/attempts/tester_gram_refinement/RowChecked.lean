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

theorem Core.frame {d ell : ℕ} {h : 0<ell} {D M : ℕ}
    {y : Fin ((2^ell)^d) → Bool} {s e : TapeStore (80+6*d) 3}
    (hc : Core d ell h D M y s) (hb : ∀ j,e.reg j ≤ M)
    (hf : ∀ i : Fin 80,i=3 ∨ i=19 ∨ i=23 ∨ i=24 ∨ i=65 ∨ i=70 → e.reg (low d i)=s.reg (low d i))
    (hp : TapeStore.SamePayload e s) (hh : e.bufferHead 2=s.bufferHead 2) : Core d ell h D M y e := by
  refine ⟨hb,?_,(hf 65 (by tauto)).trans hc.degree,(hf 70 (by tauto)).trans hc.size,
    hc.inputMarked.of_payload hp,fun z => (hc.inputTable z).of_payload hp,?_⟩
  · apply hc.environment.frame
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl <;> exact hf _ (by tauto)
  · rw [hh]
    exact hc.inputHead

theorem initialize_payload {R B : ℕ} (q tmp : Fin R) (ps : List (SamplerOdometer.Digit R))
    (s : TapeStore R B) :
    FieldConvolution.tapeData (SamplerOdometer.initializeStore q tmp ps s)=FieldConvolution.tapeData s := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    rw [SamplerOdometer.initializeStore,ih]
    rfl

theorem initialize_other (d : ℕ) (g h : Fin 3) (hgh : g≠h) (q k : ℕ)
    (s : TapeStore (80+6*d) 3) (hn : Numbered d g q k s) :
    Numbered d g q k (SamplerOdometer.initializeStore (low d 23) (low d 2) (tuple d h) s) := by
  apply hn.frame
  · exact SamplerOdometer.initializeStore_fresh _ _ _ _ _ (by simp) (low_not_tuple d h 23)
  · intro j hj
    apply SamplerOdometer.initializeStore_fresh
    · obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj
      all_goals exact digit_ne_low d _ i 2
    · exact tuple_other d g h hgh j hj

/-- The four actual entry-prefix fragments clear the sum and point index,
initialize the physical z tuple, and copy m to the point-loop countdown. -/
def pairPrepare (d : ℕ) := TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeMacros.clear (B := 3) (low d 69))
    (SamplerOdometer.initDigits (low d 23) (low d 2) (zDigits d)))
    (TapeMacros.clear (low d 73))) (TapeMacros.copy (low d 70) (low d 76) (low d 2))

theorem pairPrepare_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d))
    (inp : Inputs) (s : TapeStore (80+6*d) 3) (hc : Core d ell h D M y s)
    (ha : Numbered d 0 (2^ell) a.val s) (hb : Numbered d 1 (2^ell) b.val s) :
    ∃ t e,t ≤ d*(8*M+20)+9*M+12 ∧ (pairPrepare d).Stops inp (s.toCfg (pairPrepare d).entry) t e ∧
      Core d ell h D M y e.store ∧ Numbered d 0 (2^ell) a.val e.store ∧ Numbered d 1 (2^ell) b.val e.store ∧
      Numbered d 2 (2^ell) 0 e.store ∧ e.reg (low d 73)=0 ∧ e.reg (low d 69)=0 ∧
      e.reg (low d 76)=(2^ell)^d ∧
      (∀ i : Fin 80,70 ≤ i.val → i≠73 → i≠76 → e.reg (low d i)=s.reg (low d i)) ∧
      FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  let s₀ := s.setReg (low d 69) 0
  have h₀ := TapeMacros.clear_stops (B := 3) (low d 69) inp (s.reg (low d 69)) s rfl
  have hb₀ : ∀ j,s₀.reg j ≤ M := FieldPrograms.setReg_bound _ _ _ _ hc.bounded (by omega)
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := SamplerOdometer.initialize_stops (low d 23) (low d 2) (tuple d 2)
    (tuple_unique d 2) inp M s₀ hb₀
  have hf₁ (i : Fin 80) (hi : i≠2) : c₁.reg (low d i)=s₀.reg (low d i) := by
    change c₁.store.reg (low d i)=_
    rw [hs₁]
    exact SamplerOdometer.initializeStore_fresh _ _ _ _ _ ((low_eq_iff d _ _).not.mpr hi) (low_not_tuple d 2 i)
  have htape₁ : FieldConvolution.tapeData c₁.store=FieldConvolution.tapeData s := by
    rw [hs₁,initialize_payload]
    rfl
  have h₂ := TapeMacros.clear_stops (low d 73) inp (c₁.reg (low d 73)) c₁.store rfl
  let s₂ := c₁.store.setReg (low d 73) 0
  have hb₂ : ∀ j,s₂.reg j ≤ M := FieldPrograms.setReg_bound _ _ _ _ hb₁ (by omega)
  obtain ⟨t₃,e,ht₃,h₃,hs₃,hb₃⟩ := SamplerEvaluation.copy_stops_bound (low d 70) (low d 76) (low d 2)
    (by simp) (by simp) (by simp) inp M s₂ hb₂
  have h70 : s₂.reg (low d 70)=(2^ell)^d := by
    simp only [s₂,TapeStore.setReg,Function.update_of_ne (show low d 70≠low d 73 by simp)]
    rw [hf₁ 70 (by decide)]
    simpa [s₀,TapeStore.setReg] using hc.size
  have hreg (i : Fin 80) : e.reg (low d i)=
      if i=2 then 0 else if i=76 then (2^ell)^d else if i=73 then 0 else c₁.reg (low d i) := by
    change e.store.reg (low d i)=_
    rw [hs₃]
    simp only [h70,s₂,TapeStore.setReg]
    have h70' : c₁.reg (low d 70)=(2^ell)^d := by simpa [s₂,TapeStore.setReg] using h70
    simp [Function.update,low_eq_iff,h70']
  have hdig (g : Fin 6) (i : Fin d) : e.reg (digit d g i)=c₁.reg (digit d g i) := by
    change e.store.reg (digit d g i)=_
    rw [hs₃]
    simp [s₂,TapeStore.setReg,Function.update_of_ne (digit_ne_low d g i _)]
  have htape : FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
    rw [hs₃]
    simpa only [s₂,FieldConvolution.tapeData_setReg] using htape₁
  have hframe (i : Fin 80) (hi : i≠2 ∧ i≠69 ∧ i≠73 ∧ i≠76) : e.reg (low d i)=s.reg (low d i) := by
    rw [hreg]
    simp only [hi.1,hi.2.2.2,hi.2.2.1,if_false]
    rw [hf₁ i hi.1]
    simp [s₀,TapeStore.setReg,((low_eq_iff d _ _).not.mpr hi.2.1)]
  have hnum (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k c₁.store) : Numbered d g (2^ell) k e.store := by
    apply hn.frame (by simpa [hreg])
    intro j hj
    obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj <;> exact hdig _ i
  have hnum₀ (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k s) : Numbered d g (2^ell) k s₀ :=
    hn.setReg 69 (by decide) 0
  have hall := ((h₀.seq h₁).seq h₂).seq h₃
  refine ⟨_,_,?_,hall,?_,?_,?_,?_,?_,?_,?_,?_,htape⟩
  · have h69 := hc.bounded (low d 69)
    have h73 := hc.bounded (low d 73)
    have hf73 : c₁.reg (low d 73)=s.reg (low d 73) := by rw [hf₁ 73 (by decide)]; simp [s₀,TapeStore.setReg]
    simp only [tuple,List.length_ofFn] at ht₁
    rw [hf73]
    omega
  · apply hc.frame hb₃ _ (tapeData_payload htape) (congrFun (tapeData_head htape) 2)
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> exact hframe _ (by decide)
  · apply hnum
    rw [hs₁]
    exact initialize_other d 0 2 (by decide) _ _ s₀ (hnum₀ 0 _ ha)
  · apply hnum
    rw [hs₁]
    exact initialize_other d 1 2 (by decide) _ _ s₀ (hnum₀ 1 _ hb)
  · apply hnum
    rw [hs₁]
    apply numbered_initialize d 2 _ (Nat.one_lt_pow h.ne' (by decide))
    simpa [s₀,TapeStore.setReg,termWorkspace] using hc.environment.cardinal
  · simp [hreg]
  · rw [hreg]
    simpa [s₀,TapeStore.setReg] using hf₁ 69 (by decide)
  · simp [hreg]
  · intro i hi hi73 hi76
    apply hframe
    refine ⟨?_,?_,hi73,hi76⟩
    all_goals intro he; subst i; norm_num at hi

#print axioms pairPrepare_stops

theorem Core.frame_input {d ell : ℕ} {h : 0<ell} {D M : ℕ}
    {y : Fin ((2^ell)^d) → Bool} {s e : TapeStore (80+6*d) 3}
    (hc : Core d ell h D M y s) (hb : ∀ j,e.reg j ≤ M)
    (hf : ∀ i : Fin 80,i=3 ∨ i=19 ∨ i=23 ∨ i=24 ∨ i=65 ∨ i=70 → e.reg (low d i)=s.reg (low d i))
    (hs : ∀ k,(e.bufferTape 2).getD k .blank=(s.bufferTape 2).getD k .blank)
    (hh : e.bufferHead 2=s.bufferHead 2) : Core d ell h D M y e := by
  refine ⟨hb,?_,(hf 65 (by tauto)).trans hc.degree,(hf 70 (by tauto)).trans hc.size,?_,?_,?_⟩
  · apply hc.environment.frame
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl <;> exact hf _ (by tauto)
  · exact ⟨by rw [hs]; exact hc.inputMarked.1,fun k hk => by rw [hs]; exact hc.inputMarked.2 k hk⟩
  · intro z
    exact ⟨(hc.inputTable z).1,fun k hk => by rw [hs]; exact (hc.inputTable z).2 k hk⟩
  · rw [hh]
    exact hc.inputHead

/-- The physical q-cell entry write and actual b/flat-index advances. -/
def pairFinish (d : ℕ) := TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq
    (TapeMacros.copy (B := 3) (low d 23) (low d 79) (low d 2))
    (TapeArrays.writeBlock (low d 69) (low d 79) (0 : Fin 3)))
    (TapeMacros.increment (low d 77)))
    (SamplerOdometer.program (low d 23) (low d 2) (bDigits d)))
    (TapeMacros.increment (low d 72))

def pairFinishAfter {L : ℕ} (d : ℕ) (P : TapeProgram (80+6*d) 3 L) :=
  TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq (TapeProgram.seq P
    (TapeMacros.copy (low d 23) (low d 79) (low d 2)))
    (TapeArrays.writeBlock (low d 69) (low d 79) (0 : Fin 3)))
    (TapeMacros.increment (low d 77)))
    (SamplerOdometer.program (low d 23) (low d 2) (bDigits d)))
    (TapeMacros.increment (low d 72))

theorem pairFinishAfter_stops {L : ℕ} (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) (v : Fin (2^ell)) (flat : ℕ)
    (inp : Inputs) (s : TapeStore (80+6*d) 3) (hc : Core d ell h D M y s)
    (ha : Numbered d 0 (2^ell) a.val s) (hb : Numbered d 1 (2^ell) b.val s)
    (hv : s.reg (low d 69)=v.val) (hi : s.reg (low d 72)=b.val)
    (hf : s.reg (low d 77)=flat) (hflat : flat+1 ≤ M)
    (P : TapeProgram (80+6*d) 3 L) (origin : TapeStore (80+6*d) 3) (tP : ℕ)
    (hP : ∃ c,P.Stops inp (origin.toCfg P.entry) tP c ∧ c.store=s) :
    ∃ t e,t ≤ tP+d*(8*M+20)+10*M+17 ∧
      (pairFinishAfter d P).Stops inp (origin.toCfg (pairFinishAfter d P).entry) t e ∧
      Core d ell h D M y e.store ∧ Numbered d 0 (2^ell) a.val e.store ∧
      Numbered d 1 (2^ell) (b.val+1) e.store ∧ e.reg (low d 72)=b.val+1 ∧ e.reg (low d 77)=flat+1 ∧
      (∀ i : Fin 80,70 ≤ i.val → i≠72 → i≠77 → i≠79 → e.reg (low d i)=s.reg (low d i)) ∧
      TapeArrays.EntryWritten s e.store 0 (s.bufferHead 0) (2^ell) v.val := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := SamplerEvaluation.copy_stops_bound (low d 23) (low d 79) (low d 2)
    (by simp) (by simp) (by simp) inp M s hc.bounded
  have hq : s.reg (low d 23)=2^ell := hc.environment.cardinal
  have hv₁ : c₁.reg (low d 69)=v.val := by change c₁.store.reg _=_; rw [hs₁]; simpa [TapeStore.setReg] using hv
  have hw₁ : c₁.reg (low d 79)=2^ell := by change c₁.store.reg _=_; rw [hs₁]; simp [TapeStore.setReg,hq]
  obtain ⟨c₂,h₂,hs₂⟩ := TapeArrays.writeBlock_stops (low d 69) (low d 79) (by simp) 0 inp v.val (2^ell)
    c₁.store hv₁ hw₁ (Nat.le_of_lt v.isLt)
  have hreg₂ : c₂.reg=((c₁.store.setReg (low d 69) 0).setReg (low d 79) 0).reg := by
    change c₂.store.reg=_
    rw [hs₂,TapeArrays.writeBlockStore_reg]
  have hb₂ : ∀ j,c₂.reg j ≤ M := by
    rw [hreg₂]
    exact FieldPrograms.setReg_bound _ _ _ _ (FieldPrograms.setReg_bound _ _ _ _ hb₁ (by omega)) (by omega)
  have hf₂ (i : Fin 80) (hi : i≠2 ∧ i≠69 ∧ i≠79) : c₂.reg (low d i)=s.reg (low d i) := by
    rw [hreg₂]
    simp only [TapeStore.setReg,Function.update_of_ne ((low_eq_iff d _ _).not.mpr hi.2.2),
      Function.update_of_ne ((low_eq_iff d _ _).not.mpr hi.2.1)]
    change c₁.store.reg (low d i)=_
    rw [hs₁]
    simp [TapeStore.setReg,((low_eq_iff d _ _).not.mpr hi.1),((low_eq_iff d _ _).not.mpr hi.2.2)]
  have hd₂ (g : Fin 6) (i : Fin d) : c₂.reg (digit d g i)=s.reg (digit d g i) := by
    rw [hreg₂]
    simp only [TapeStore.setReg,Function.update_of_ne (digit_ne_low d g i _)]
    change c₁.store.reg (digit d g i)=_
    rw [hs₁]
    simp only [TapeStore.setReg,Function.update_of_ne (digit_ne_low d g i _)]
  have hn₂ (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k s) : Numbered d g (2^ell) k c₂.store := by
    apply hn.frame (hf₂ 23 (by decide))
    intro j hj
    obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj <;> exact hd₂ _ i
  have h₃ := TapeMacros.increment_stops (low d 77) inp c₂.store
  let s₃ := c₂.store.setReg (low d 77) (c₂.reg (low d 77)+1)
  have hf₂77 : c₂.reg (low d 77)=flat := (hf₂ 77 (by decide)).trans hf
  have hb₃ : ∀ j,s₃.reg j ≤ M := FieldPrograms.setReg_bound _ _ _ _ hb₂ (by rw [hf₂77]; exact hflat)
  have hn₃ : Numbered d 1 (2^ell) b.val s₃ := (hn₂ 1 _ hb).setReg 77 (by decide) _
  obtain ⟨t₄,c₄,ht₄,h₄,hs₄,hb₄⟩ := SamplerOdometer.program_stops_valid (low d 23) (low d 2) (tuple d 1)
    (tuple_unique d 1) inp M s₃ hb₃ hn₃.2.1
  have hf₄ (i : Fin 80) (hi : i≠2) : c₄.reg (low d i)=s₃.reg (low d i) := by
    change c₄.store.reg (low d i)=_
    rw [hs₄]
    exact SamplerOdometer.nextStore_fresh _ _ _ _ _ ((low_eq_iff d _ _).not.mpr hi) (low_not_tuple d 1 i)
  have hi₄ : c₄.reg (low d 72)=b.val := by rw [hf₄ 72 (by decide)]; simpa [s₃,TapeStore.setReg] using (hf₂ 72 (by decide)).trans hi
  have h₅ := TapeMacros.increment_stops (low d 72) inp c₄.store
  let e := (c₄.store.setReg (low d 72) (c₄.reg (low d 72)+1)).toCfg (1 : Fin 2)
  have hb₅ : ∀ j,e.reg j ≤ M := by
    apply FieldPrograms.setReg_bound _ _ _ _ hb₄
    rw [hi₄]
    have hm := hc.bounded (low d 70)
    rw [hc.size] at hm
    have hh := b.isLt
    omega
  have hreg (i : Fin 80) (hi : i≠2 ∧ i≠72 ∧ i≠77 ∧ i≠69 ∧ i≠79) : e.reg (low d i)=s.reg (low d i) := by
    change (c₄.store.setReg (low d 72) _).reg (low d i)=_
    simp only [TapeStore.setReg,Function.update_of_ne ((low_eq_iff d _ _).not.mpr hi.2.1)]
    rw [hf₄ i hi.1]
    simp only [s₃,TapeStore.setReg,Function.update_of_ne ((low_eq_iff d _ _).not.mpr hi.2.2.1)]
    exact hf₂ i ⟨hi.1,hi.2.2.2⟩
  have hpay₄ : FieldConvolution.tapeData c₄.store=FieldConvolution.tapeData c₂.store := by
    rw [hs₄]
    have hh := SamplerOdometer.nextStore_payload (low d 23) (low d 2) (tuple d 1) s₃
    exact congrArg (fun (x : (Fin 4 → ℕ) × List Bool × (Fin 3 → List Sym) × (Fin 3 → ℕ)) => x)
      (show FieldConvolution.tapeData (SamplerOdometer.nextStore (low d 23) (low d 2) (tuple d 1) s₃)=FieldConvolution.tapeData s₃ by
        simp only [FieldConvolution.tapeData,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2])
  have hpay : FieldConvolution.tapeData e.store=FieldConvolution.tapeData c₂.store := hpay₄
  have hw : TapeArrays.EntryWritten s e.store 0 (s.bufferHead 0) (2^ell) v.val := by
    have hp := tapeData_payload hpay
    have hh := tapeData_head hpay
    have hro : c₂.roHead=s.roHead := by change c₂.store.roHead=_; rw [hs₂,TapeArrays.writeBlockStore_roHead,hs₁]; rfl
    have hout : c₂.output=s.output := by change c₂.store.output=_; rw [hs₂,TapeArrays.writeBlockStore_output,hs₁]; rfl
    refine ⟨hp.roHead.trans hro,hp.output.trans hout,?_,?_⟩
    · rw [hh]
      change c₂.store.bufferHead=_
      rw [hs₂,TapeArrays.writeBlockStore_head _ _ _ _ _ _ (Nat.le_of_lt v.isLt),hs₁]
      rfl
    · intro c k
      rw [hp.symbol]
      change (c₂.store.bufferTape c).getD k .blank=_
      rw [hs₂,TapeArrays.writeBlockStore_symbol _ _ _ _ _ _ (Nat.le_of_lt v.isLt),hs₁]
      rfl
  have hn₅ (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k c₄.store) : Numbered d g (2^ell) k e.store :=
    hn.setReg 72 (by decide) _
  obtain ⟨cP,hP,hPs⟩ := hP
  rw [← hPs] at h₁
  have hall := ((((hP.seq h₁).seq h₂).seq h₃).seq h₄).seq h₅
  refine ⟨_,_,?_,hall,?_,?_,?_,?_,?_,?_,hw⟩
  · have hqM : 2^ell ≤ M := hq ▸ hc.bounded (low d 23)
    have hvM := v.isLt
    simp only [tuple,List.length_ofFn] at ht₄
    omega
  · apply hc.frame_input hb₅ _ _ _
    · intro i hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
      · exact hreg 3 (by decide)
      · exact hreg 19 (by decide)
      · exact hreg 23 (by decide)
      · exact hreg 24 (by decide)
      · exact hreg 65 (by decide)
      · exact hreg 70 (by decide)
    · intro k
      simpa using hw.symbol 2 k
    · rw [hw.head]
      rfl
  · apply hn₅
    rw [hs₄]
    exact numbered_next_other d 0 1 (by decide) _ _ s₃ ((hn₂ 0 _ ha).setReg 77 (by decide) _)
  · apply hn₅
    rw [hs₄]
    exact numbered_next d 1 _ _ (Nat.one_lt_pow h.ne' (by decide)) s₃ hn₃
  · simp [e,TapeStore.setReg,hi₄]
  · change (c₄.store.setReg (low d 72) (c₄.reg (low d 72)+1)).reg (low d 77)=_
    simp only [TapeStore.setReg,Function.update_of_ne (show low d 77≠low d 72 by simp)]
    rw [hf₄ 77 (by decide)]
    simp [s₃,TapeStore.setReg,hf₂77]
  · intro i hi hi72 hi77 hi79
    apply hreg
    refine ⟨?_,hi72,hi77,?_,hi79⟩
    all_goals intro he; subst i; norm_num at hi

#print axioms pairFinishAfter_stops

structure GramEffect (d : ℕ) (s e : TapeStore (80+6*d) 3) (q flat v : ℕ) : Prop where
  roHead : e.roHead=s.roHead
  output : e.output=s.output
  head : e.bufferHead 0=1+(flat+1)*q
  spareHead : e.bufferHead 1=s.bufferHead 1
  symbol : ∀ c k,(e.bufferTape c).getD k .blank=
    if c=0 ∧ 1+flat*q ≤ k ∧ k<1+(flat+1)*q then
      if k<1+flat*q+v then .one else .zero
    else (s.bufferTape c).getD k .blank

def pairTime (d M m : ℕ) := d*(8*M+20)+9*M+12+1+(m*(pointTime d M+2)+1)+d*(8*M+20)+10*M+17

theorem pairBody_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) (flat : ℕ)
    (inp : Inputs) (s : TapeStore (80+6*d) 3) (hc : Core d ell h D M y s)
    (ha : Numbered d 0 (2^ell) a.val s) (hb : Numbered d 1 (2^ell) b.val s)
    (hi : s.reg (low d 72)=b.val) (hf : s.reg (low d 77)=flat)
    (hh : s.bufferHead 0=1+flat*(2^ell)) (hflat : flat+1 ≤ M)
    (hdM : d*((2^ell)-1) ≤ M) (hhead : 1+(2^ell)^d*(2^ell) ≤ M) :
    ∃ t e,t ≤ pairTime d M ((2^ell)^d) ∧ (pairBody d).Stops inp (s.toCfg (pairBody d).entry) t e ∧
      Core d ell h D M y e.store ∧ Numbered d 0 (2^ell) a.val e.store ∧
      Numbered d 1 (2^ell) (b.val+1) e.store ∧ e.reg (low d 72)=b.val+1 ∧ e.reg (low d 77)=flat+1 ∧
      (∀ i : Fin 80,70 ≤ i.val → i≠72 → i≠73 → i≠76 → i≠77 → i≠78 → i≠79 →
        e.reg (low d i)=s.reg (low d i)) ∧
      GramEffect d s e.store (2^ell) flat (EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1.val := by
  obtain ⟨t₁,c₁,ht₁,h₁,hc₁,ha₁,hb₁,hz₁,hi₁,hv₁,hn₁,hf₁,hd₁⟩ := pairPrepare_stops d ell h D M y a b inp s hc ha hb
  obtain ⟨t₂,c₂,ht₂,h₂,hc₂,hv₂,ha₂,hb₂,hi₂,hn₂,hf₂,hp₂,hh₂⟩ := pointLoop_stops d ell h D M hM y a b inp c₁.store
    hc₁ ha₁ hb₁ hz₁ hi₁ hv₁ hn₁ hdM hhead
  have hpre := h₁.seq h₂
  have hreg (i : Fin 80) (hi : 70 ≤ i.val) (hi73 : i≠73) (hi76 : i≠76) (hi78 : i≠78) :
      c₂.reg (low d i)=s.reg (low d i) := (hf₂ i hi hi73 hi76 hi78).trans (hf₁ i hi hi73 hi76)
  have hpay : TapeStore.SamePayload c₂.store s := hp₂.trans (tapeData_payload hd₁)
  have hheads (c : Fin 3) (hc2 : c≠2) : c₂.bufferHead c=s.bufferHead c :=
    (hh₂ c hc2).trans (congrFun (tapeData_head hd₁) c)
  obtain ⟨t₃,e,ht₃,h₃,hce,hae,hbe,hie,hfe,hre,hwrite⟩ := pairFinishAfter_stops d ell h D M y a b
    (EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1 flat inp c₂.store hc₂ ha₂ hb₂ hv₂
    ((hreg 72 (by decide) (by decide) (by decide) (by decide)).trans hi)
    ((hreg 77 (by decide) (by decide) (by decide) (by decide)).trans hf) hflat
    (TapeProgram.seq (pairPrepare d) (TapeProgram.countedLoop (pointBody d) (low d 76))) s (t₁+1+t₂)
    ⟨_,hpre,rfl⟩
  refine ⟨t₃,_,?_,h₃,hce,hae,hbe,hie,hfe,?_,?_⟩
  · unfold pairTime
    omega
  · intro i hi hi72 hi73 hi76 hi77 hi78 hi79
    exact (hre i hi hi72 hi77 hi79).trans (hreg i hi hi73 hi76 hi78)
  · have hstart : c₂.store.bufferHead 0=1+flat*(2^ell) := (hheads 0 (by decide)).trans hh
    refine ⟨hwrite.roHead.trans hpay.roHead,hwrite.output.trans hpay.output,?_,?_,?_⟩
    · change e.store.bufferHead 0=_
      rw [hwrite.head]
      have hstart' : c₂.bufferHead 0=1+flat*(2^ell) := hstart
      simp only [Function.update_self,hstart',Nat.add_mul,Nat.one_mul,Nat.add_assoc]
    · change e.store.bufferHead 1=_
      rw [hwrite.head,Function.update_of_ne (by decide : (1:Fin 3)≠0)]
      exact hheads 1 (by decide)
    · intro c k
      rw [hwrite.symbol,hpay.symbol,hstart]
      simp only [Nat.add_mul,Nat.one_mul,Nat.add_assoc]

#print axioms pairBody_stops

def GramPrefix (d : ℕ) (q : ℕ) (value : ℕ → ℕ) (flat : ℕ) (s : TapeStore (80+6*d) 3) : Prop :=
  ∀ k,k<flat → TapeArrays.ThermometerAt s 0 (1+k*q) q (value k)

theorem GramEffect.prefix {d q flat v : ℕ} {s e : TapeStore (80+6*d) 3}
    (he : GramEffect d s e q flat v) (value : ℕ → ℕ) (hv : v=value flat) (hvq : v ≤ q)
    (hp : GramPrefix d q value flat s) : GramPrefix d q value (flat+1) e := by
  intro k hk
  by_cases heq : k=flat
  · subst k
    refine ⟨hv ▸ hvq,?_⟩
    intro j hj
    rw [he.symbol]
    have hright : 1+flat*q+j<1+(flat+1)*q := by rw [Nat.add_mul,Nat.one_mul]; omega
    have hleft : 1+flat*q ≤ 1+flat*q+j := by omega
    simp only [true_and,hleft,hright,and_self,if_true]
    rw [← hv]
    split_ifs <;> first | rfl | omega
  · have hkflat : k<flat := by omega
    refine ⟨(hp k hkflat).1,?_⟩
    intro j hj
    rw [he.symbol]
    have hmul := Nat.mul_le_mul_right q (show k+1 ≤ flat by omega)
    rw [Nat.add_mul,Nat.one_mul] at hmul
    have hnot : ¬ (1+flat*q ≤ 1+k*q+j) := by omega
    simp only [hnot,false_and,and_false,if_false]
    exact (hp k hkflat).2 j hj

theorem GramEffect.bottomMarked {d q flat v : ℕ} {s e : TapeStore (80+6*d) 3}
    (he : GramEffect d s e q flat v) (hm : TapeArrays.BottomMarked s 0) : TapeArrays.BottomMarked e 0 := by
  constructor
  · rw [he.symbol]
    have hh : ¬1+flat*q ≤ 0 := by omega
    simp only [hh,false_and,and_false,if_false]
    exact hm.1
  · intro k hk
    rw [he.symbol]
    split_ifs <;> first | decide | exact hm.2 k hk

def gramValue (d ell : ℕ) (h : 0<ell) (D : ℕ) (y : Fin ((2^ell)^d) → Bool) : ℕ → ℕ :=
  GaussianProgram.flatEntry (EncodedTester.table (BinaryField.indexOperations ell h) D y)

theorem gramValue_pair (d ell : ℕ) (h : 0<ell) (D : ℕ) (y : Fin ((2^ell)^d) → Bool)
    (a b : Fin ((2^ell)^d)) :
    gramValue d ell h D y (a.val*(2^ell)^d+b.val)=
      (EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1.val := by
  have hval : (finProdFinEquiv (a,b)).val=a.val*(2^ell)^d+b.val := by simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  have hk : a.val*(2^ell)^d+b.val<(2^ell)^d*(2^ell)^d := hval ▸ (finProdFinEquiv (a,b)).isLt
  have he : (⟨a.val*(2^ell)^d+b.val,hk⟩ : Fin ((2^ell)^d*(2^ell)^d))=finProdFinEquiv (a,b) := Fin.ext hval.symm
  simp [gramValue,GaussianProgram.flatEntry,dif_pos hk,he,EncodedTester.table,Gaussian.toMatrix,Gaussian.ofMatrix]

structure BuildState (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (origin : TapeStore (80+6*d) 3) (flat : ℕ)
    (s : TapeStore (80+6*d) 3) : Prop where
  core : Core d ell h D M y s
  index : s.reg (low d 77)=flat
  head : s.bufferHead 0=1+flat*(2^ell)
  entries : GramPrefix d (2^ell) (gramValue d ell h D y) flat s
  marked : TapeArrays.BottomMarked s 0
  spareMarked : TapeArrays.BottomMarked s 1
  spareHead : s.bufferHead 1=origin.bufferHead 1
  roHead : s.roHead=origin.roHead
  output : s.output=origin.output

theorem BuildState.frame {d ell : ℕ} {h : 0<ell} {D M flat : ℕ}
    {y : Fin ((2^ell)^d) → Bool} {origin s e : TapeStore (80+6*d) 3}
    (hs : BuildState d ell h D M y origin flat s) (hc : Core d ell h D M y e)
    (hi : e.reg (low d 77)=flat) (ht : FieldConvolution.tapeData e=FieldConvolution.tapeData s) :
    BuildState d ell h D M y origin flat e := by
  have hp := tapeData_payload ht
  have hh := tapeData_head ht
  refine ⟨hc,hi,(congrFun hh 0).trans hs.head,?_,hs.marked.of_payload hp,hs.spareMarked.of_payload hp,
    (congrFun hh 1).trans hs.spareHead,hp.roHead.trans hs.roHead,hp.output.trans hs.output⟩
  intro k hk
  exact (hs.entries k hk).of_payload hp

theorem BuildState.after_pair {d ell : ℕ} {h : 0<ell} {D M flat : ℕ}
    {y : Fin ((2^ell)^d) → Bool} {origin s e : TapeStore (80+6*d) 3}
    (hs : BuildState d ell h D M y origin flat s) (hc : Core d ell h D M y e)
    (hi : e.reg (low d 77)=flat+1) (a b : Fin ((2^ell)^d))
    (hflat : flat=a.val*(2^ell)^d+b.val)
    (he : GramEffect d s e (2^ell) flat (EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1.val) :
    BuildState d ell h D M y origin (flat+1) e := by
  refine ⟨hc,hi,he.head,?_,he.bottomMarked hs.marked,?_,he.spareHead.trans hs.spareHead,
    he.roHead.trans hs.roHead,he.output.trans hs.output⟩
  · apply he.prefix _ _ (Nat.le_of_lt (EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1.isLt) hs.entries
    rw [hflat,gramValue_pair]
  · constructor
    · rw [he.symbol]
      simpa using hs.spareMarked.1
    · intro k hk
      rw [he.symbol]
      simpa using hs.spareMarked.2 k hk

/-- The real per-row prefix initializes b, clears its scalar index and installs
m in the column-loop countdown; all tape data and the a tuple are preserved. -/
def rowPrepare (d : ℕ) := TapeProgram.seq (TapeProgram.seq
    (SamplerOdometer.initDigits (B := 3) (low d 23) (low d 2) (bDigits d))
    (TapeMacros.clear (low d 72))) (TapeMacros.copy (low d 70) (low d 75) (low d 2))

theorem rowPrepare_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a : Fin ((2^ell)^d))
    (inp : Inputs) (s : TapeStore (80+6*d) 3) (hc : Core d ell h D M y s)
    (ha : Numbered d 0 (2^ell) a.val s) :
    ∃ t e,t ≤ d*(8*M+20)+8*M+10 ∧ (rowPrepare d).Stops inp (s.toCfg (rowPrepare d).entry) t e ∧
      Core d ell h D M y e.store ∧ Numbered d 0 (2^ell) a.val e.store ∧ Numbered d 1 (2^ell) 0 e.store ∧
      e.reg (low d 72)=0 ∧ e.reg (low d 75)=(2^ell)^d ∧
      (∀ i : Fin 80,70 ≤ i.val → i≠72 → i≠75 → e.reg (low d i)=s.reg (low d i)) ∧
      FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := SamplerOdometer.initialize_stops (low d 23) (low d 2) (tuple d 1)
    (tuple_unique d 1) inp M s hc.bounded
  have hf₁ (i : Fin 80) (hi : i≠2) : c₁.reg (low d i)=s.reg (low d i) := by
    change c₁.store.reg (low d i)=_
    rw [hs₁]
    exact SamplerOdometer.initializeStore_fresh _ _ _ _ _ ((low_eq_iff d _ _).not.mpr hi) (low_not_tuple d 1 i)
  have htape₁ : FieldConvolution.tapeData c₁.store=FieldConvolution.tapeData s := by rw [hs₁,initialize_payload]
  have h₂ := TapeMacros.clear_stops (low d 72) inp (c₁.reg (low d 72)) c₁.store rfl
  let s₂ := c₁.store.setReg (low d 72) 0
  have hb₂ : ∀ j,s₂.reg j ≤ M := FieldPrograms.setReg_bound _ _ _ _ hb₁ (by omega)
  obtain ⟨t₃,e,ht₃,h₃,hs₃,hb₃⟩ := SamplerEvaluation.copy_stops_bound (low d 70) (low d 75) (low d 2)
    (by simp) (by simp) (by simp) inp M s₂ hb₂
  have h70 : c₁.reg (low d 70)=(2^ell)^d := (hf₁ 70 (by decide)).trans hc.size
  have hreg (i : Fin 80) : e.reg (low d i)=
      if i=2 then 0 else if i=75 then (2^ell)^d else if i=72 then 0 else c₁.reg (low d i) := by
    change e.store.reg (low d i)=_
    rw [hs₃]
    simp [s₂,TapeStore.setReg,Function.update,low_eq_iff,h70]
  have hdig (g : Fin 6) (i : Fin d) : e.reg (digit d g i)=c₁.reg (digit d g i) := by
    change e.store.reg (digit d g i)=_
    rw [hs₃]
    simp [s₂,TapeStore.setReg,Function.update_of_ne (digit_ne_low d g i _)]
  have htape : FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
    rw [hs₃]
    simpa only [s₂,FieldConvolution.tapeData_setReg] using htape₁
  have hframe (i : Fin 80) (hi : i≠2 ∧ i≠72 ∧ i≠75) : e.reg (low d i)=s.reg (low d i) := by
    rw [hreg]
    simp only [hi.1,hi.2.2,hi.2.1,if_false]
    exact hf₁ i hi.1
  have hnum (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k c₁.store) : Numbered d g (2^ell) k e.store := by
    apply hn.frame (by simpa [hreg])
    intro j hj
    obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj <;> exact hdig _ i
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_,_,?_,hall,?_,?_,?_,?_,?_,?_,htape⟩
  · have h72 := hc.bounded (low d 72)
    rw [hf₁ 72 (by decide)]
    simp only [tuple,List.length_ofFn] at ht₁
    omega
  · apply hc.frame hb₃ _ (tapeData_payload htape) (congrFun (tapeData_head htape) 2)
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> exact hframe _ (by decide)
  · apply hnum
    rw [hs₁]
    exact initialize_other d 0 1 (by decide) _ _ s ha
  · apply hnum
    rw [hs₁]
    exact numbered_initialize d 1 _ (Nat.one_lt_pow h.ne' (by decide)) s hc.environment.cardinal
  · simp [hreg]
  · simp [hreg]
  · intro i hi hi72 hi75
    apply hframe
    refine ⟨?_,hi72,hi75⟩
    intro he; subst i; norm_num at hi

#print axioms rowPrepare_stops

structure RowLoopInv (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (origin : TapeStore (80+6*d) 3)
    (a : Fin ((2^ell)^d)) (outer remaining : ℕ) (s : TapeStore (80+6*d) 3) : Prop where
  le : remaining ≤ (2^ell)^d
  build : BuildState d ell h D M y origin (a.val*(2^ell)^d+((2^ell)^d-remaining)) s
  aTuple : Numbered d 0 (2^ell) a.val s
  bTuple : Numbered d 1 (2^ell) ((2^ell)^d-remaining) s
  aIndex : s.reg (low d 71)=a.val
  bIndex : s.reg (low d 72)=(2^ell)^d-remaining
  outer : s.reg (low d 74)=outer

theorem rowLoop_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
    (y : Fin ((2^ell)^d) → Bool) (a : Fin ((2^ell)^d))
    (origin : TapeStore (80+6*d) 3) (inp : Inputs) (s : TapeStore (80+6*d) 3)
    (hc : BuildState d ell h D M y origin (a.val*(2^ell)^d) s)
    (ha : Numbered d 0 (2^ell) a.val s) (hb : Numbered d 1 (2^ell) 0 s)
    (hai : s.reg (low d 71)=a.val) (hbi : s.reg (low d 72)=0)
    (hn : s.reg (low d 75)=(2^ell)^d)
    (hdM : d*((2^ell)-1) ≤ M) (hhead : 1+(2^ell)^d*(2^ell) ≤ M)
    (hmatrix : (2^ell)^d*(2^ell)^d ≤ M) :
    ∃ t e,t ≤ (2^ell)^d*(pairTime d M ((2^ell)^d)+2)+1 ∧
      (TapeProgram.countedLoop (pairBody d) (low d 75)).Stops inp
        (s.toCfg (TapeProgram.countedLoop (pairBody d) (low d 75)).entry) t e ∧
      BuildState d ell h D M y origin ((a.val+1)*(2^ell)^d) e.store ∧
      Numbered d 0 (2^ell) a.val e.store ∧ e.reg (low d 71)=a.val ∧
      e.reg (low d 74)=s.reg (low d 74) ∧ e.reg (low d 75)=0 := by
  let Inv := RowLoopInv d ell h D M y origin a (s.reg (low d 74))
  have hbody (n : ℕ) (c : TapeStore (80+6*d) 3) (hcn : c.reg (low d 75)=n+1) (hi : Inv (n+1) c) :
      ∃ t e,t ≤ pairTime d M ((2^ell)^d) ∧ (pairBody d).Stops inp
        ((TapeProgram.decStore (low d 75) c).toCfg (pairBody d).entry) t e ∧ Inv n e.store ∧ e.reg (low d 75)=n := by
    let k := (2^ell)^d-(n+1)
    have hk : k<(2^ell)^d := by dsimp [k]; have := hi.le; omega
    have hkn : (2^ell)^d-n=k+1 := by dsimp [k]; have := hi.le; omega
    let c' := c.setReg (low d 75) n
    have hc' : TapeProgram.decStore (low d 75) c=c' := by simp [TapeProgram.decStore,c',TapeStore.setReg,hcn]
    have hbnd : n ≤ M := by have hh := hi.build.core.bounded (low d 75); rw [hcn] at hh; omega
    have hcore := hi.build.core.setReg 75 (by decide) (by decide) n hbnd
    have hbuild : BuildState d ell h D M y origin (a.val*(2^ell)^d+k) c' := by
      apply hi.build.frame hcore
      · simpa [c',TapeStore.setReg,k] using hi.build.index
      · rfl
    have hflat : a.val*(2^ell)^d+k+1 ≤ M := by
      have hh := (finProdFinEquiv (a,(⟨k,hk⟩ : Fin ((2^ell)^d)))).isLt
      have hnum : (finProdFinEquiv (a,(⟨k,hk⟩ : Fin ((2^ell)^d)))).val=a.val*(2^ell)^d+k := by simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
      rw [hnum] at hh
      omega
    obtain ⟨t,e,ht,he,hec,hea,heb,hei,hef,her,hew⟩ := pairBody_stops d ell h D M hM y a ⟨k,hk⟩ (a.val*(2^ell)^d+k) inp c'
      hcore (hi.aTuple.setReg 75 (by decide) n) (hi.bTuple.setReg 75 (by decide) n)
      (by simpa [c',TapeStore.setReg,k] using hi.bIndex) hbuild.index hbuild.head hflat hdM hhead
    refine ⟨t,e,ht,?_,?_,?_⟩
    · simpa only [hc'] using he
    · refine ⟨by have := hi.le; omega,?_,hea,?_,?_,?_,?_⟩
      · have hb' := hbuild.after_pair hec hef a ⟨k,hk⟩ rfl hew
        convert hb' using 1 <;> rw [hkn] <;> omega
      · simpa only [hkn] using heb
      · exact (her 71 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          (by simpa [c',TapeStore.setReg] using hi.aIndex)
      · simpa only [hkn] using hei
      · exact (her 74 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          (by simpa [c',TapeStore.setReg] using hi.outer)
    · rw [her 75 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp [c',TapeStore.setReg]
  have hi : Inv ((2^ell)^d) s := by
    refine ⟨le_rfl,?_,ha,?_,hai,?_,rfl⟩
    · simpa using hc
    · simpa using hb
    · simpa using hbi
  obtain ⟨t,e,ht,he,hie,hez⟩ := loop_stops (pairBody d) (low d 75) inp (pairTime d M ((2^ell)^d)) Inv hbody
    ((2^ell)^d) s hn hi
  refine ⟨t,_,ht,he,?_,hie.aTuple,hie.aIndex,hie.outer,hez⟩
  convert hie.build using 1
  simp only [Nat.sub_zero]
  ring

#print axioms rowLoop_stops

def rowFinishAfter {L : ℕ} (d : ℕ) (P : TapeProgram (80+6*d) 3 L) :=
  TapeProgram.seq (TapeProgram.seq P
    (SamplerOdometer.program (low d 23) (low d 2) (aDigits d))) (TapeMacros.increment (low d 71))

theorem rowFinishAfter_stops {L : ℕ} (d ell : ℕ) (h : 0<ell) (D M flat : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a : Fin ((2^ell)^d))
    (origin : TapeStore (80+6*d) 3) (inp : Inputs) (s : TapeStore (80+6*d) 3)
    (hs : BuildState d ell h D M y origin flat s) (ha : Numbered d 0 (2^ell) a.val s)
    (hi : s.reg (low d 71)=a.val)
    (P : TapeProgram (80+6*d) 3 L) (start : TapeStore (80+6*d) 3) (tP : ℕ)
    (hP : ∃ c,P.Stops inp (start.toCfg P.entry) tP c ∧ c.store=s) :
    ∃ t e,t ≤ tP+d*(8*M+20)+3 ∧ (rowFinishAfter d P).Stops inp (start.toCfg (rowFinishAfter d P).entry) t e ∧
      BuildState d ell h D M y origin flat e.store ∧ Numbered d 0 (2^ell) (a.val+1) e.store ∧
      e.reg (low d 71)=a.val+1 ∧ e.reg (low d 74)=s.reg (low d 74) := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := SamplerOdometer.program_stops_valid (low d 23) (low d 2) (tuple d 0)
    (tuple_unique d 0) inp M s hs.core.bounded ha.2.1
  have hf₁ (i : Fin 80) (hi : i≠2) : c₁.reg (low d i)=s.reg (low d i) := by
    change c₁.store.reg (low d i)=_
    rw [hs₁]
    exact SamplerOdometer.nextStore_fresh _ _ _ _ _ ((low_eq_iff d _ _).not.mpr hi) (low_not_tuple d 0 i)
  have hi₁ : c₁.reg (low d 71)=a.val := (hf₁ 71 (by decide)).trans hi
  have h₂ := TapeMacros.increment_stops (low d 71) inp c₁.store
  let e := (c₁.store.setReg (low d 71) (c₁.reg (low d 71)+1)).toCfg (1 : Fin 2)
  have hb₂ : ∀ j,e.reg j ≤ M := by
    apply FieldPrograms.setReg_bound _ _ _ _ hb₁
    rw [hi₁]
    have hm := hs.core.bounded (low d 70)
    rw [hs.core.size] at hm
    have hh := a.isLt
    omega
  have hframe (i : Fin 80) (hi : i≠2 ∧ i≠71) : e.reg (low d i)=s.reg (low d i) := by
    change (c₁.store.setReg (low d 71) (c₁.reg (low d 71)+1)).reg (low d i)=_
    simp only [TapeStore.setReg,Function.update_of_ne ((low_eq_iff d _ _).not.mpr hi.2)]
    exact hf₁ i hi.1
  have hdata : FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
    change FieldConvolution.tapeData c₁.store=_
    rw [hs₁]
    have hh := SamplerOdometer.nextStore_payload (low d 23) (low d 2) (tuple d 0) s
    simp only [FieldConvolution.tapeData,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2]
  have hcore : Core d ell h D M y e.store := by
    apply hs.core.frame hb₂ _ (tapeData_payload hdata) (congrFun (tapeData_head hdata) 2)
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hframe 3 (by decide)
    · exact hframe 19 (by decide)
    · exact hframe 23 (by decide)
    · exact hframe 24 (by decide)
    · exact hframe 65 (by decide)
    · exact hframe 70 (by decide)
  obtain ⟨cP,hP,hPs⟩ := hP
  rw [← hPs] at h₁
  have hall := (hP.seq h₁).seq h₂
  refine ⟨_,_,?_,hall,hs.frame hcore ((hframe 77 (by decide)).trans hs.index) hdata,?_,?_,hframe 74 (by decide)⟩
  · simp only [tuple,List.length_ofFn] at ht₁
    omega
  · have hh : Numbered d 0 (2^ell) (a.val+1) c₁.store := by
      rw [hs₁]
      exact numbered_next d 0 _ _ (Nat.one_lt_pow h.ne' (by decide)) s ha
    exact hh.setReg 71 (by decide) _
  · simp [e,TapeStore.setReg,hi₁]

def rowTime (d M m : ℕ) := d*(8*M+20)+8*M+10+1+(m*(pairTime d M m+2)+1)+d*(8*M+20)+3

theorem rowBody_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
    (y : Fin ((2^ell)^d) → Bool) (a : Fin ((2^ell)^d))
    (origin : TapeStore (80+6*d) 3) (inp : Inputs) (s : TapeStore (80+6*d) 3)
    (hs : BuildState d ell h D M y origin (a.val*(2^ell)^d) s)
    (ha : Numbered d 0 (2^ell) a.val s) (hi : s.reg (low d 71)=a.val)
    (hdM : d*((2^ell)-1) ≤ M) (hhead : 1+(2^ell)^d*(2^ell) ≤ M)
    (hmatrix : (2^ell)^d*(2^ell)^d ≤ M) :
    ∃ t e,t ≤ rowTime d M ((2^ell)^d) ∧ (rowBody d).Stops inp (s.toCfg (rowBody d).entry) t e ∧
      BuildState d ell h D M y origin ((a.val+1)*(2^ell)^d) e.store ∧
      Numbered d 0 (2^ell) (a.val+1) e.store ∧ e.reg (low d 71)=a.val+1 ∧ e.reg (low d 74)=s.reg (low d 74) := by
  obtain ⟨t₁,c₁,ht₁,h₁,hc₁,ha₁,hb₁,hi₁,hn₁,hf₁,hd₁⟩ := rowPrepare_stops d ell h D M y a inp s hs.core ha
  have hbuild₁ : BuildState d ell h D M y origin (a.val*(2^ell)^d) c₁.store :=
    hs.frame hc₁ ((hf₁ 77 (by decide) (by decide) (by decide)).trans hs.index) hd₁
  obtain ⟨t₂,c₂,ht₂,h₂,hb₂,ha₂,hi₂,hf₂,hn₂⟩ := rowLoop_stops d ell h D M hM y a origin inp c₁.store hbuild₁ ha₁ hb₁
    ((hf₁ 71 (by decide) (by decide) (by decide)).trans hi) hi₁ hn₁ hdM hhead hmatrix
  have hpre := h₁.seq h₂
  obtain ⟨t₃,e,ht₃,h₃,hbe,hae,hie,hfe⟩ := rowFinishAfter_stops d ell h D M ((a.val+1)*(2^ell)^d) y a origin inp c₂.store
    hb₂ ha₂ hi₂ (TapeProgram.seq (rowPrepare d) (TapeProgram.countedLoop (pairBody d) (low d 75))) s (t₁+1+t₂) ⟨_,hpre,rfl⟩
  refine ⟨t₃,_,?_,h₃,hbe,hae,hie,?_⟩
  · unfold rowTime
    omega
  · exact hfe.trans (hf₂.trans (hf₁ 74 (by decide) (by decide) (by decide)))

#print axioms rowBody_stops

end ExpandingCodes.Computation.TesterGram
