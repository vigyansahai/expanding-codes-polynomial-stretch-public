import ExpandingCodes.Computation.RandomBits
import ExpandingCodes.Computation.TapeArrays

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ExpandingCodes.Computation
open NKtLB
namespace RandomTables
variable {R B : ℕ}

/-- One more runtime register supplies the number of table entries. -/
structure Layout (R : ℕ) where
  random : RandomBits.Layout R
  count : Fin R
  fresh : ∀ j, random.reg j ≠ count

/-- One actual random index, an actual preserving copy of q, then a physical
q-cell thermometer write. All sizes remain data in unary registers. -/
def entry (l : RandomBits.Layout R) (b : Fin B) : TapeProgram R B 53 :=
  TapeProgram.seq (TapeProgram.seq (RandomBits.randomIndex l)
    (TapeMacros.copy l.q l.count l.scratch)) (TapeArrays.writeBlock l.acc l.count b)

def entryStore (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs)
    (d : TapeStore R B) : TapeStore R B :=
  let c := RandomBits.indexStore l inp d
  TapeArrays.writeBlockStore l.acc l.count b (c.reg l.acc) (d.reg l.q)
    ((c.setReg l.count (d.reg l.q)).setReg l.scratch 0)

def entryBound (q : ℕ) : ℕ := (q+1)*(7*q+30)+8*q+12

 theorem entry_stops (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs) (d : TapeStore R B)
    (hq : d.reg l.q = 2^(d.reg l.ell)) (he : d.reg l.ell ≤ d.reg l.q)
    (hc : d.reg l.count ≤ d.reg l.q) (hs : d.reg l.scratch ≤ d.reg l.q)
    (ha : d.reg l.acc ≤ d.reg l.q) (ht : d.reg l.tmp ≤ d.reg l.q) :
    ∃ t e, t ≤ entryBound (d.reg l.q) ∧
      (entry l b).Stops inp (d.toCfg (entry l b).entry) t e ∧
      e.store = entryStore l b inp d := by
  obtain ⟨t, c, hb, hr, hpost⟩ := RandomBits.randomIndex_polynomial l inp d hq he hc hs ha ht
  obtain ⟨e, hcopy, hcopypost⟩ := TapeMacros.copy_stops l.q l.count l.scratch
    (l.reg.injective.ne (by decide)) (l.reg.injective.ne (by decide))
    (l.reg.injective.ne (by decide)) inp c.store
  have hcr : c.store.reg l.count = 0 := by rw [hpost]; exact RandomBits.indexStore_count l inp d
  have hcs : c.store.reg l.scratch = 0 := by rw [hpost]; exact RandomBits.indexStore_scratch l inp d
  have hcq : c.store.reg l.q = d.reg l.q := by rw [hpost]; exact RandomBits.indexStore_q l inp d
  have hec : e.store.reg l.count = d.reg l.q := by
    rw [hcopypost, hcq]
    simp [TapeStore.setReg, RandomBits.Layout.count, RandomBits.Layout.scratch]
  have hea : e.store.reg l.acc = c.store.reg l.acc := by
    rw [hcopypost]
    simp [TapeStore.setReg, RandomBits.Layout.acc, RandomBits.Layout.count, RandomBits.Layout.scratch]
  have hv : c.store.reg l.acc ≤ d.reg l.q := by
    rw [hpost, hq]
    exact (RandomBits.indexStore_acc_lt l inp d).le
  have hw := TapeArrays.writeBlock_stops l.acc l.count (l.reg.injective.ne (by decide)) b inp
    (c.store.reg l.acc) (d.reg l.q) e.store hea hec hv
  obtain ⟨f, hf, hfs⟩ := hw
  have hall := (hr.seq hcopy).seq hf
  refine ⟨t+1+(c.store.reg l.count+c.store.reg l.scratch+5*c.store.reg l.q+7)+1+
    (2*d.reg l.q+c.store.reg l.acc+3), f.mapPC (TapeProgram.rightLabel 46), ?_, ?_, ?_⟩
  · simp only [entryBound]
    change c.reg l.count = 0 at hcr
    change c.reg l.scratch = 0 at hcs
    change c.reg l.q = d.reg l.q at hcq
    change c.reg l.acc ≤ d.reg l.q at hv
    rw [hcr, hcs, hcq]
    omega
  · exact hall
  · change f.store = _
    rw [hfs, hcopypost, hcq, hpost]
    rfl

/-- The source loop has 55 labels for every runtime table length and width. -/
def fill (l : Layout R) (b : Fin B) : TapeProgram R B 55 :=
  TapeProgram.countedLoop (entry l.random b) l.count

theorem entryStore_reg (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs)
    (d : TapeStore R B) (j : Fin R) :
    (entryStore l b inp d).reg j =
      if j = l.acc ∨ j = l.count ∨ j = l.tmp ∨ j = l.scratch then 0 else d.reg j := by
  rw [entryStore, TapeArrays.writeBlockStore_reg]
  by_cases ha : j = l.acc
  · subst j
    simp [TapeStore.setReg, RandomBits.Layout.acc, RandomBits.Layout.count, RandomBits.Layout.scratch]
  · by_cases hc : j = l.count
    · subst j
      simp [TapeStore.setReg]
    · by_cases ht : j = l.tmp
      · subst j
        simp [TapeStore.setReg, RandomBits.Layout.tmp, RandomBits.Layout.acc,
          RandomBits.Layout.count, RandomBits.Layout.scratch, RandomBits.indexStore_tmp]
      · by_cases hs : j = l.scratch
        · subst j
          simp [TapeStore.setReg, RandomBits.Layout.scratch, RandomBits.Layout.acc, RandomBits.Layout.count]
        · simp only [ha, hc, ht, hs, or_self, ite_false]
          simp only [TapeStore.setReg, Function.update_of_ne ha, Function.update_of_ne hc,
            Function.update_of_ne hs]
          rw [RandomBits.indexStore, RandomBits.bitsStore_reg_other l inp _ _ j ha hc ht hs]
          simp [RandomBits.prepareStore, TapeStore.setReg, ha, hc, ht, hs]

 theorem entryStore_roHead (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs)
    (d : TapeStore R B) :
    (entryStore l b inp d).roHead = Function.update d.roHead 3 (d.roHead 3+d.reg l.ell) := by
  rw [entryStore, TapeArrays.writeBlockStore_roHead]
  exact RandomBits.indexStore_roHead l inp d

 theorem entryStore_head (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs)
    (d : TapeStore R B) (hq : d.reg l.q = 2^(d.reg l.ell)) :
    (entryStore l b inp d).bufferHead = Function.update d.bufferHead b (d.bufferHead b+d.reg l.q) := by
  have hv : (RandomBits.indexStore l inp d).reg l.acc ≤ d.reg l.q := by
    rw [hq]
    exact (RandomBits.indexStore_acc_lt l inp d).le
  rw [entryStore, TapeArrays.writeBlockStore_head _ _ _ _ _ _ hv]
  exact congrArg (fun f => Function.update f b (f b+d.reg l.q))
    (RandomBits.indexStore_payload l inp d).2.2

 theorem entryStore_output (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs)
    (d : TapeStore R B) : (entryStore l b inp d).output = d.output := by
  rw [entryStore, TapeArrays.writeBlockStore_output]
  exact (RandomBits.indexStore_payload l inp d).1

 theorem entryStore_symbol (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs)
    (d : TapeStore R B) (hq : d.reg l.q = 2^(d.reg l.ell)) (c : Fin B) (k : ℕ) :
    ((entryStore l b inp d).bufferTape c).getD k .blank =
      if c = b ∧ d.bufferHead b ≤ k ∧ k < d.bufferHead b+d.reg l.q then
        if k < d.bufferHead b+RandomBits.value inp (d.reg l.ell) (d.roHead 3) 0 then .one else .zero
      else (d.bufferTape c).getD k .blank := by
  have hv : (RandomBits.indexStore l inp d).reg l.acc ≤ d.reg l.q := by
    rw [hq]
    exact (RandomBits.indexStore_acc_lt l inp d).le
  rw [entryStore, TapeArrays.writeBlockStore_symbol _ _ _ _ _ _ hv]
  simp only [TapeStore.setReg, RandomBits.indexStore_acc,
    (RandomBits.indexStore_payload l inp d).2.1, (RandomBits.indexStore_payload l inp d).2.2]

/-- The mutable sampler scratch is empty at table-entry boundaries. -/
def Clean (l : RandomBits.Layout R) (d : TapeStore R B) : Prop :=
  d.reg l.acc = 0 ∧ d.reg l.count = 0 ∧ d.reg l.tmp = 0 ∧ d.reg l.scratch = 0

 theorem entryStore_clean (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs)
    (d : TapeStore R B) : Clean l (entryStore l b inp d) := by
  simp [Clean, entryStore_reg]

/-- Explicit data semantics of the runtime-length physical table fill. -/
def fillStore (l : Layout R) (b : Fin B) (inp : Inputs) : ℕ → TapeStore R B → TapeStore R B
  | 0, d => d
  | n+1, d => fillStore l b inp n (entryStore l.random b inp (TapeProgram.decStore l.count d))

 theorem fill_stops (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hn : d.reg l.count = n) (hq : d.reg l.random.q = 2^(d.reg l.random.ell))
    (he : d.reg l.random.ell ≤ d.reg l.random.q) (hclean : Clean l.random d) :
    ∃ t, t ≤ n*(entryBound (d.reg l.random.q)+2)+1 ∧
      (fill l b).Stops inp (d.toCfg (TapeProgram.loopHeader 53)) t
        ((fillStore l b inp n d).toCfg (TapeProgram.loopExit 53)) := by
  induction n generalizing d with
  | zero => exact ⟨1, by omega, TapeProgram.loop_zero (entry l.random b) l.count inp d hn⟩
  | succ n ih =>
    let d₁ := TapeProgram.decStore l.count d
    let d₂ := entryStore l.random b inp d₁
    have hdr (j : Fin 6) : d₁.reg (l.random.reg j) = d.reg (l.random.reg j) := by
      simp [d₁, TapeProgram.decStore, l.fresh j]
    have hq₁ : d₁.reg l.random.q = 2^(d₁.reg l.random.ell) := by simpa only [hdr] using hq
    have he₁ : d₁.reg l.random.ell ≤ d₁.reg l.random.q := by simpa only [hdr] using he
    have hclean₁ : Clean l.random d₁ := by simpa only [Clean, hdr] using hclean
    obtain ⟨s, c, hs, hc, hcs⟩ := entry_stops l.random b inp d₁ hq₁ he₁
      (by rw [hclean₁.2.1]; omega) (by rw [hclean₁.2.2.2]; omega)
      (by rw [hclean₁.1]; omega) (by rw [hclean₁.2.2.1]; omega)
    have hr : d₂.reg l.count = n := by
      rw [entryStore_reg]
      simp [d₂, d₁, TapeProgram.decStore, hn, Ne.symm (l.fresh 2), Ne.symm (l.fresh 3),
        Ne.symm (l.fresh 4), Ne.symm (l.fresh 5)]
    have hq₂ : d₂.reg l.random.q = d.reg l.random.q := by
      rw [entryStore_reg]
      simp [RandomBits.Layout.q, RandomBits.Layout.acc, RandomBits.Layout.count,
        RandomBits.Layout.tmp, RandomBits.Layout.scratch, hdr]
    have he₂ : d₂.reg l.random.ell = d.reg l.random.ell := by
      rw [entryStore_reg]
      simp [RandomBits.Layout.ell, RandomBits.Layout.acc, RandomBits.Layout.count,
        RandomBits.Layout.tmp, RandomBits.Layout.scratch, hdr]
    obtain ⟨t, ht, hstop⟩ := ih d₂ hr (by rw [hq₂, he₂]; exact hq)
      (by rw [hq₂, he₂]; exact he) (entryStore_clean _ _ _ _)
    have hh := TapeProgram.loop_positive_header (entry l.random b) l.count inp d (by omega)
    have hb := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (entry l.random b) l.count)
    have hx := TapeProgram.loop_body_return (entry l.random b) l.count inp c hc.halted
    have hcx : c.store.toCfg (TapeProgram.loopHeader 53) = d₂.toCfg (TapeProgram.loopHeader 53) := by rw [hcs]
    rw [hcx] at hx
    refine ⟨1+s+1+t, ?_, ⟨?_, hstop.halted⟩⟩
    · rw [hq₂] at ht
      rw [hdr 1] at hs
      nlinarith [Nat.add_mul n 1 (entryBound (d.reg l.random.q)+2)]
    · exact ((hh.trans hb).trans hx).trans hstop.exec

theorem fillStore_reg_other (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ)
    (d : TapeStore R B) (j : Fin R) (ha : j ≠ l.random.acc) (hc : j ≠ l.random.count)
    (ht : j ≠ l.random.tmp) (hs : j ≠ l.random.scratch) (hk : j ≠ l.count) :
    (fillStore l b inp n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [fillStore, ih, entryStore_reg]
    simp [ha, hc, ht, hs, hk, TapeProgram.decStore]

theorem fillStore_count (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (fillStore l b inp n d).reg l.count = d.reg l.count-n := by
  induction n generalizing d with
  | zero => simp [fillStore]
  | succ n ih =>
    rw [fillStore, ih, entryStore_reg]
    simp [Ne.symm (l.fresh 2), Ne.symm (l.fresh 3), Ne.symm (l.fresh 4), Ne.symm (l.fresh 5),
      TapeProgram.decStore, Nat.sub_sub, Nat.add_comm]

 theorem fillStore_clean (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hc : Clean l.random d) : Clean l.random (fillStore l b inp n d) := by
  induction n generalizing d with
  | zero => exact hc
  | succ n ih => exact ih _ (entryStore_clean _ _ _ _)

 theorem fillStore_ell (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (fillStore l b inp n d).reg l.random.ell = d.reg l.random.ell := by
  apply fillStore_reg_other
  any_goals exact l.random.reg.injective.ne (by decide)
  exact l.fresh 0

 theorem fillStore_q (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (fillStore l b inp n d).reg l.random.q = d.reg l.random.q := by
  apply fillStore_reg_other
  any_goals exact l.random.reg.injective.ne (by decide)
  exact l.fresh 1

 theorem entryStore_ell (l : Layout R) (b : Fin B) (inp : Inputs) (d : TapeStore R B) :
    (entryStore l.random b inp (TapeProgram.decStore l.count d)).reg l.random.ell = d.reg l.random.ell := by
  rw [entryStore_reg]
  simp [RandomBits.Layout.ell, RandomBits.Layout.acc, RandomBits.Layout.count,
    RandomBits.Layout.tmp, RandomBits.Layout.scratch, TapeProgram.decStore, l.fresh 0]

 theorem entryStore_q (l : Layout R) (b : Fin B) (inp : Inputs) (d : TapeStore R B) :
    (entryStore l.random b inp (TapeProgram.decStore l.count d)).reg l.random.q = d.reg l.random.q := by
  rw [entryStore_reg]
  simp [RandomBits.Layout.q, RandomBits.Layout.acc, RandomBits.Layout.count,
    RandomBits.Layout.tmp, RandomBits.Layout.scratch, TapeProgram.decStore, l.fresh 1]

 theorem fillStore_roHead (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (fillStore l b inp n d).roHead =
      Function.update d.roHead 3 (d.roHead 3+n*d.reg l.random.ell) := by
  induction n generalizing d with
  | zero => simp [fillStore]
  | succ n ih =>
    rw [fillStore, ih, entryStore_ell, entryStore_roHead]
    simp only [TapeProgram.decStore, Function.update_of_ne (l.fresh 0),
      Function.update_self, Function.update_idem]
    congr 1
    ring

 theorem fillStore_head (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hq : d.reg l.random.q = 2^(d.reg l.random.ell)) :
    (fillStore l b inp n d).bufferHead =
      Function.update d.bufferHead b (d.bufferHead b+n*d.reg l.random.q) := by
  induction n generalizing d with
  | zero => simp [fillStore]
  | succ n ih =>
    have hq₁ : (TapeProgram.decStore l.count d).reg l.random.q =
        2^((TapeProgram.decStore l.count d).reg l.random.ell) := by
      simpa [TapeProgram.decStore, l.fresh 0, l.fresh 1] using hq
    have hq₂ : (entryStore l.random b inp (TapeProgram.decStore l.count d)).reg l.random.q =
        2^((entryStore l.random b inp (TapeProgram.decStore l.count d)).reg l.random.ell) := by
      rw [entryStore_q, entryStore_ell]
      exact hq
    rw [fillStore, ih _ hq₂, entryStore_q, entryStore_head _ _ _ _ hq₁]
    simp only [TapeProgram.decStore, Function.update_of_ne (l.fresh 1),
      Function.update_self, Function.update_idem]
    congr 1
    ring

 theorem fillStore_output (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (fillStore l b inp n d).output = d.output := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [fillStore, ih, entryStore_output]

/-- Every physical cell outside the filled interval is preserved. -/
 theorem fillStore_outside (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hq : d.reg l.random.q = 2^(d.reg l.random.ell)) (c : Fin B) (k : ℕ)
    (hout : c ≠ b ∨ k < d.bufferHead b ∨ d.bufferHead b+n*d.reg l.random.q ≤ k) :
    ((fillStore l b inp n d).bufferTape c).getD k .blank = (d.bufferTape c).getD k .blank := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    let e := entryStore l.random b inp (TapeProgram.decStore l.count d)
    have hq₁ : (TapeProgram.decStore l.count d).reg l.random.q =
        2^((TapeProgram.decStore l.count d).reg l.random.ell) := by
      simpa [TapeProgram.decStore, l.fresh 0, l.fresh 1] using hq
    have hq₂ : e.reg l.random.q = 2^(e.reg l.random.ell) := by
      rw [entryStore_q, entryStore_ell]
      exact hq
    have hh : e.bufferHead b = d.bufferHead b+d.reg l.random.q := by
      rw [entryStore_head _ _ _ _ hq₁]
      simp [TapeProgram.decStore, l.fresh 1]
    have hrq : e.reg l.random.q = d.reg l.random.q := entryStore_q l b inp d
    have heout : c ≠ b ∨ k < e.bufferHead b ∨ e.bufferHead b+n*e.reg l.random.q ≤ k := by
      rw [hh, hrq]
      rcases hout with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by nlinarith [Nat.add_mul n 1 (d.reg l.random.q)]))
    rw [fillStore, ih e hq₂ heout, entryStore_symbol _ _ _ _ hq₁]
    have hnot : ¬ (c = b ∧ d.bufferHead b ≤ k ∧ k < d.bufferHead b+d.reg l.random.q) := by
      rcases hout with h | h | h
      · tauto
      · omega
      · intro hc
        nlinarith [Nat.zero_le (n*d.reg l.random.q), Nat.add_mul n 1 (d.reg l.random.q)]
    simpa [TapeProgram.decStore, l.fresh 1, hnot]

/-- Each contiguous q-cell block stores exactly the index from its ell-bit
randomness block, including arbitrary starting heads and input suffixes. -/
 theorem fillStore_table (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hq : d.reg l.random.q = 2^(d.reg l.random.ell)) (i j : ℕ)
    (hi : i < n) (hj : j < d.reg l.random.q) :
    ((fillStore l b inp n d).bufferTape b).getD (d.bufferHead b+i*d.reg l.random.q+j) .blank =
      if j < RandomBits.value inp (d.reg l.random.ell) (d.roHead 3+i*d.reg l.random.ell) 0
      then .one else .zero := by
  induction n generalizing d i with
  | zero => omega
  | succ n ih =>
    let e := entryStore l.random b inp (TapeProgram.decStore l.count d)
    have hq₁ : (TapeProgram.decStore l.count d).reg l.random.q =
        2^((TapeProgram.decStore l.count d).reg l.random.ell) := by
      simpa [TapeProgram.decStore, l.fresh 0, l.fresh 1] using hq
    have hq₂ : e.reg l.random.q = 2^(e.reg l.random.ell) := by
      rw [entryStore_q, entryStore_ell]
      exact hq
    have hh : e.bufferHead b = d.bufferHead b+d.reg l.random.q := by
      rw [entryStore_head _ _ _ _ hq₁]
      simp [TapeProgram.decStore, l.fresh 1]
    have hro : e.roHead 3 = d.roHead 3+d.reg l.random.ell := by
      rw [entryStore_roHead]
      simp [TapeProgram.decStore, l.fresh 0]
    rw [fillStore]
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.add_zero]
      rw [fillStore_outside l b inp n e hq₂ b (d.bufferHead b+j)
        (Or.inr (Or.inl (by rw [hh]; omega)))]
      rw [entryStore_symbol _ _ _ _ hq₁]
      simp only [TapeProgram.decStore, Function.update_of_ne (l.fresh 1),
        Function.update_of_ne (l.fresh 0)]
      have h₁ : d.bufferHead b ≤ d.bufferHead b+j := by omega
      have h₂ : d.bufferHead b+j < d.bufferHead b+d.reg l.random.q := by omega
      have h₃ : d.bufferHead b+j < d.bufferHead b+RandomBits.value inp (d.reg l.random.ell) (d.roHead 3) 0 ↔
          j < RandomBits.value inp (d.reg l.random.ell) (d.roHead 3) 0 := by omega
      simp [h₁, h₂, h₃]
    | succ i =>
      have hi' : i < n := by omega
      have hj' : j < e.reg l.random.q := by rw [entryStore_q]; exact hj
      have ht := ih e hq₂ i hi' hj'
      rw [entryStore_q, entryStore_ell, hh, hro] at ht
      convert ht using 1 <;> congr 2 <;> ring

open ExpandingCodes.PolynomialStretch

/-- Canonical contiguous blocking of the K*ell fair coins. -/
def blocksEquiv (K ell : ℕ) : (Fin (K*ell) → Bool) ≃ (Fin K → Fin ell → Bool) where
  toFun x i j := x (finProdFinEquiv (i,j))
  invFun x z := x (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2
  left_inv x := by
    funext z
    change x (finProdFinEquiv (finProdFinEquiv.symm z)) = x z
    exact congrArg x (finProdFinEquiv.apply_symm_apply z)
  right_inv x := by
    funext i j
    change x (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 = x i j
    simp only [Equiv.symm_apply_apply]

/-- Each physical table entry is an independent exact binary index. -/
def tableIndexEquiv (K ell : ℕ) : (Fin (K*ell) → Bool) ≃ (Fin K → Fin (2^ell)) :=
  (blocksEquiv K ell).trans (Equiv.piCongrRight fun _ => RandomBits.bitsIndexEquiv ell)

 theorem uniform_tableIndex (K ell : ℕ) (E : (Fin K → Fin (2^ell)) → Prop) :
    uniformProb (fun x : Fin (K*ell) → Bool => E (tableIndexEquiv K ell x)) = uniformProb E :=
  uniformProb_equiv (tableIndexEquiv K ell) E

 theorem tableIndexEquiv_apply (K ell : ℕ) (x : Fin (K*ell) → Bool) (i : Fin K) :
    tableIndexEquiv K ell x i =
      RandomBits.bitsIndexEquiv ell (fun j => x ⟨i.val*ell+j.val, by nlinarith [i.isLt, j.isLt]⟩) := by
  change RandomBits.bitsIndexEquiv ell (fun j => x (finProdFinEquiv (i,j))) = _
  congr 1
  funext j
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv]
  ring

def sampledValues (inp : Inputs) (K ell h : ℕ) : Fin K → Fin (2^ell) :=
  fun i => ⟨RandomBits.value inp ell (h+i.val*ell) 0,
    by simpa using RandomBits.value_lt inp ell (h+i.val*ell) 0⟩

 theorem sampledValues_block (inp : Inputs) (pre suffix : List Bool) (K ell : ℕ)
    (x : Fin (K*ell) → Bool) :
    sampledValues {inp with rand := pre ++ (List.ofFn x ++ suffix)} K ell pre.length =
      tableIndexEquiv K ell x := by
  funext i
  apply Fin.ext
  rw [tableIndexEquiv_apply]
  change RandomBits.value {inp with rand := pre ++ (List.ofFn x ++ suffix)} ell
    (pre.length+i.val*ell) 0 = _
  rw [RandomBits.value_eq_bitsIndex]
  congr 2
  funext j
  have h := RandomBits.bitAt_block inp pre suffix x
    (⟨i.val*ell+j.val, by nlinarith [i.isLt, j.isLt]⟩ : Fin (K*ell))
  simpa [Nat.add_assoc] using h

/-- Exact joint law of all entries from exactly K*ell fair bits. The block
storage theorem connects these values to the actual source buffer cells. -/
 theorem uniform_sampledValues (inp : Inputs) (pre suffix : List Bool) (K ell : ℕ)
    (E : (Fin K → Fin (2^ell)) → Prop) :
    uniformProb (fun x : Fin (K*ell) → Bool =>
      E (sampledValues {inp with rand := pre ++ (List.ofFn x ++ suffix)} K ell pre.length)) =
      uniformProb E := by
  simp_rw [sampledValues_block]
  exact uniform_tableIndex K ell E

 theorem fillStore_sampledValues (l : Layout R) (b : Fin B) (inp : Inputs) (K : ℕ)
    (d : TapeStore R B) (hq : d.reg l.random.q = 2^(d.reg l.random.ell)) (i : Fin K) :
    TapeArrays.ThermometerAt (fillStore l b inp K d) b
      (d.bufferHead b+i.val*d.reg l.random.q) (d.reg l.random.q)
      (sampledValues inp K (d.reg l.random.ell) (d.roHead 3) i).val := by
  constructor
  · change RandomBits.value inp _ _ 0 ≤ d.reg l.random.q
    rw [hq]
    exact (by simpa using (RandomBits.value_lt inp (d.reg l.random.ell)
      (d.roHead 3+i.val*d.reg l.random.ell) 0).le)
  · intro j hj
    exact fillStore_table l b inp K d hq i.val j i.isLt hj

#print axioms entry_stops
#print axioms fill_stops
#print axioms fillStore_table
#print axioms uniform_tableIndex
#print axioms uniform_sampledValues
#print axioms fillStore_sampledValues

end RandomTables
end ExpandingCodes.Computation
