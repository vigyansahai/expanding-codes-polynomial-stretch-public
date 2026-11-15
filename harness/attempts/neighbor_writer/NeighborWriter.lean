import ExpandingCodes.Computation.TapeControl
import ExpandingCodes.Computation.ParameterPrograms

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ExpandingCodes.Computation
open NKtLB
namespace NeighborWriter
open TapeProgram ParameterPrograms
variable {R B : ℕ}

def reverse (r : Fin 6 → Fin R) : Fin 6 → Fin R := fun j => r (Equiv.swap 0 1 j)

theorem reverse_injective (r : Fin 6 → Fin R) (hr : Function.Injective r) :
    Function.Injective (reverse r) := hr.comp (Equiv.swap 0 1).injective

@[simp] theorem reverse_zero (r : Fin 6 → Fin R) : reverse r 0 = r 1 := by simp [reverse]
@[simp] theorem reverse_one (r : Fin 6 → Fin R) : reverse r 1 = r 0 := by simp [reverse]
@[simp] theorem reverse_two (r : Fin 6 → Fin R) : reverse r 2 = r 2 := by simp [reverse, Equiv.swap_apply_def]
@[simp] theorem reverse_three (r : Fin 6 → Fin R) : reverse r 3 = r 3 := by simp [reverse, Equiv.swap_apply_def]
@[simp] theorem reverse_four (r : Fin 6 → Fin R) : reverse r 4 = r 4 := by simp [reverse, Equiv.swap_apply_def]
@[simp] theorem reverse_five (r : Fin 6 → Fin R) : reverse r 5 = r 5 := by simp [reverse, Equiv.swap_apply_def]

theorem lessThanStore_other (r : Fin 6 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₂ : j ≠ r 2) (h₃ : j ≠ r 3) (h₄ : j ≠ r 4) (h₅ : j ≠ r 5) :
    (lessThanStore r d).reg j = d.reg j := by
  simp [lessThanStore, lessCore, lessPrepare, ltLoopStore, TapeStore.setReg, h₂,h₃,h₄,h₅]

/-- Mark the output counter as one if the two preserved inputs agree. A prior
one stays one. Every comparison is an actual unary source program. -/
def markEq (r : Fin 6 → Fin R) (out : Fin R) : TapeProgram R B 77 :=
  TapeProgram.seq (lessThan r)
    (branchZero (r 2)
      (TapeProgram.seq (lessThan (reverse r))
        (branchZero (r 2) (loadConstant out 1) skip)) skip)

def markStore (r : Fin 6 → Fin R) (out : Fin R) (d : TapeStore R B) : TapeStore R B :=
  let c := lessThanStore r d
  if c.reg (r 2) = 0 then
    let e := lessThanStore (reverse r) c
    if e.reg (r 2) = 0 then e.setReg out 1 else e
  else c

theorem markStore_other (r : Fin 6 → Fin R) (out : Fin R) (d : TapeStore R B) (j : Fin R)
    (ho : j ≠ out) (h₂ : j ≠ r 2) (h₃ : j ≠ r 3) (h₄ : j ≠ r 4) (h₅ : j ≠ r 5) :
    (markStore r out d).reg j = d.reg j := by
  have hrev := lessThanStore_other (reverse r) (lessThanStore r d) j
    (by simpa using h₂) (by simpa using h₃) (by simpa using h₄) (by simpa using h₅)
  have hdir := lessThanStore_other r d j h₂ h₃ h₄ h₅
  dsimp only [markStore]
  split_ifs <;> simp [TapeStore.setReg, ho, hrev, hdir]

theorem markStore_out (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (out : Fin R) (ho : ∀ j, out ≠ r j) (d : TapeStore R B) :
    (markStore r out d).reg out =
      if d.reg (r 0) = d.reg (r 1) then 1 else d.reg out := by
  have hdir := lessThanStore_other r d out (ho 2) (ho 3) (ho 4) (ho 5)
  have hrev := lessThanStore_other (reverse r) (lessThanStore r d) out
    (by simpa using ho 2) (by simpa using ho 3) (by simpa using ho 4) (by simpa using ho 5)
  have hzero := lessThanStore_preserves r hr d 0 (by simp)
  have hone := lessThanStore_preserves r hr d 1 (by simp)
  have hv₂ : (lessThanStore (reverse r) (lessThanStore r d)).reg (r 2) =
      if d.reg (r 1) < d.reg (r 0) then 1 else 0 := by
    simpa only [reverse_two, reverse_zero, reverse_one, hzero, hone] using
      lessThanStore_value (reverse r) (reverse_injective r hr) (lessThanStore r d)
  dsimp only [markStore]
  rw [lessThanStore_value r hr d]
  by_cases hxy : d.reg (r 0) < d.reg (r 1)
  · simp [hxy, Nat.ne_of_lt hxy, hdir]
  · simp only [hxy, if_false, ite_true, hv₂]
    by_cases hyx : d.reg (r 1) < d.reg (r 0)
    · simp [hyx, Ne.symm (Nat.ne_of_lt hyx), hrev, hdir]
    · have he : d.reg (r 0) = d.reg (r 1) := by omega
      simp [hyx, he, TapeStore.setReg]

theorem markStore_bound (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (out : Fin R) (d : TapeStore R B) (M : ℕ) (hM : 1 ≤ M)
    (hd : ∀ j, d.reg j ≤ M) : ∀ j, (markStore r out d).reg j ≤ M := by
  have h₁ := lessThanStore_bound r hr d M hM hd
  have h₂ := lessThanStore_bound (reverse r) (reverse_injective r hr)
    (lessThanStore r d) M hM h₁
  dsimp only [markStore]
  split_ifs
  · exact FieldPrograms.setReg_bound _ out 1 M h₂ hM
  · exact h₂
  · exact h₁

theorem markEq_stops (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (out : Fin R) (inp : Inputs) (d : TapeStore R B) (M : ℕ) (hM : 1 ≤ M)
    (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 160*(M+1) ∧
      (markEq r out).Stops inp (d.toCfg (markEq (B := B) r out).entry) t e ∧
      e.store = markStore r out d := by
  obtain ⟨t,c,ht,hc,hcs⟩ := lessThan_stops r hr inp M hM d hd
  have hb : ∀ j, c.store.reg j ≤ M := by
    rw [hcs]
    exact lessThanStore_bound r hr d M hM hd
  have hskip (s : TapeStore R B) :
      ∃ t e, t ≤ 0 ∧ (skip : TapeProgram R B 1).Stops inp
        (s.toCfg (skip : TapeProgram R B 1).entry) t e ∧ e.store = s :=
    ⟨0,s.toCfg 0,le_rfl,skip_stops inp s,rfl⟩
  have hsecond (s : TapeStore R B) (hs : ∀ j, s.reg j ≤ M) :
      ∃ t e, t ≤ 80*(M+1) ∧
        (TapeProgram.seq (lessThan (reverse r))
          (branchZero (r 2) (loadConstant out 1) skip)).Stops inp
            (s.toCfg (TapeProgram.seq (lessThan (reverse r))
              (branchZero (r 2) (loadConstant (B := B) out 1) skip)).entry) t e ∧
        e.store =
          if (lessThanStore (reverse r) s).reg (r 2) = 0 then
            (lessThanStore (reverse r) s).setReg out 1 else lessThanStore (reverse r) s := by
    obtain ⟨u,e,hu,he,hes⟩ := lessThan_stops (reverse r) (reverse_injective r hr) inp M hM s hs
    have heb : ∀ j, e.store.reg j ≤ M := by
      rw [hes]
      exact lessThanStore_bound (reverse r) (reverse_injective r hr) s M hM hs
    obtain ⟨f,hf,hfs⟩ := loadConstant_stops out 1 inp e.store
    have hload : ∃ t f, t ≤ M+4 ∧ (loadConstant out 1).Stops inp
        (e.store.toCfg (loadConstant (B := B) out 1).entry) t f ∧
          f.store = e.store.setReg out 1 := by
      exact ⟨_,f,by have := heb out; omega,hf,hfs⟩
    obtain ⟨v,f,hv,hf,hfs⟩ := branchZero_stops (r 2) (loadConstant out 1) skip inp
      e.store (e.store.setReg out 1) e.store (M+4) 0 hload (hskip e.store)
    refine ⟨u+1+v, f.mapPC (rightLabel 33), ?_, he.seq hf, ?_⟩
    · simp only [max_eq_left (by omega : 0 ≤ M+4)] at hv
      omega
    · change f.store = _
      have her : e.reg (r 2) = (lessThanStore (reverse r) s).reg (r 2) :=
        congrArg (fun s : TapeStore R B => s.reg (r 2)) hes
      simpa only [hes, her] using hfs
  obtain ⟨u,e,hu,he,hes⟩ := branchZero_stops (r 2)
    (TapeProgram.seq (lessThan (reverse r)) (branchZero (r 2) (loadConstant out 1) skip))
    skip inp c.store
    (if (lessThanStore (reverse r) c.store).reg (r 2) = 0 then
      (lessThanStore (reverse r) c.store).setReg out 1 else lessThanStore (reverse r) c.store)
    c.store (80*(M+1)) 0 (hsecond c.store hb) (hskip c.store)
  refine ⟨t+1+u,e.mapPC (rightLabel 33),?_,?_,?_⟩
  · simp only [max_eq_left (Nat.zero_le _)] at hu
    omega
  · convert hc.seq he using 1 <;> rfl
  · change e.store = _
    have hcr : c.reg (r 2) = (lessThanStore r d).reg (r 2) :=
      congrArg (fun s : TapeStore R B => s.reg (r 2)) hcs
    simpa only [hcs, hcr, markStore] using hes

/-- Emit and consume an already proved Boolean counter. Two charged source
instructions suffice; no arbitrary natural-to-Boolean operation is present. -/
def emitFlag (r : Fin R) : TapeProgram R B 4 where
  entry := 0
  code j := if j = 0 then .dec r 1 2 else if j = 1 then .emit false 3
    else if j = 2 then .emit true 3 else .halt

def emitStore (r : Fin R) (d : TapeStore R B) : TapeStore R B :=
  {d with reg := Function.update d.reg r 0, output := d.output ++ [decide (d.reg r = 1)]}

theorem emitFlag_stops (r : Fin R) (inp : Inputs) (d : TapeStore R B) (h : d.reg r ≤ 1) :
    (emitFlag r).Stops inp (d.toCfg 0) 2 ((emitStore r d).toCfg 3) := by
  by_cases hz : d.reg r = 0
  · have hf : emitStore r d = {d with output := d.output ++ [false]} := by
      simp [emitStore, hz, Function.update_eq_self]
    refine ⟨?_, by simp [TapeProgram.halted, emitFlag]⟩
    rw [hf]
    exact Exec.step (d := d.toCfg 1) (by simp [TapeProgram.halted, emitFlag])
      (by simp [TapeProgram.step, emitFlag, TapeStore.toCfg, hz])
      (Exec.one (by simp [TapeProgram.halted, emitFlag])
        (by simp [TapeProgram.step, emitFlag, TapeStore.toCfg]))
  · have ho : d.reg r = 1 := by omega
    let c := d.setReg r 0
    refine ⟨?_, by simp [TapeProgram.halted, emitFlag]⟩
    exact Exec.step (d := c.toCfg 2) (by simp [TapeProgram.halted, emitFlag])
      (by simp [TapeProgram.step, emitFlag, TapeStore.toCfg, c, TapeStore.setReg, ho])
      (Exec.one (by simp [TapeProgram.halted, emitFlag])
        (by simp [TapeProgram.step, emitFlag, TapeStore.toCfg, emitStore, c, TapeStore.setReg, ho]))

/-- Eight common registers and one statically allocated neighbor register per
layer. This allocation depends only on fixed k, never on runtime n. -/
structure Layout (R k : ℕ) where
  reg : Fin 8 ⊕ Fin k → Fin R
  injective : Function.Injective reg

namespace Layout
variable {k : ℕ}
abbrev n (l : Layout R k) := l.reg (.inl 0)
abbrev col (l : Layout R k) := l.reg (.inl 1)
abbrev out (l : Layout R k) := l.reg (.inl 2)
abbrev count (l : Layout R k) := l.reg (.inl 7)
abbrev neighbor (l : Layout R k) (i : Fin k) := l.reg (.inr i)

def comparisonIndex (i : Fin k) : Fin 6 → (Fin 8 ⊕ Fin k) :=
  ![.inl 1,.inr i,.inl 3,.inl 4,.inl 5,.inl 6]

def comparison (l : Layout R k) (i : Fin k) : Fin 6 → Fin R :=
  l.reg ∘ comparisonIndex i

theorem comparison_injective (l : Layout R k) (i : Fin k) :
    Function.Injective (l.comparison i) := by
  apply l.injective.comp
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [comparisonIndex]

theorem out_fresh (l : Layout R k) (i : Fin k) : ∀ j, l.out ≠ l.comparison i j := by
  intro j
  apply l.injective.ne
  fin_cases j <;> simp [comparison, comparisonIndex]

theorem mark_frame (l : Layout R k) (i : Fin k) (d : TapeStore R B)
    (a : Fin 8) (ha : a = 0 ∨ a = 1 ∨ a = 7) :
    (markStore (l.comparison i) l.out d).reg (l.reg (.inl a)) = d.reg (l.reg (.inl a)) := by
  apply markStore_other
  all_goals apply l.injective.ne
  all_goals rcases ha with rfl | rfl | rfl <;> simp [comparison, comparisonIndex]

theorem mark_neighbor (l : Layout R k) (i j : Fin k) (d : TapeStore R B) :
    (markStore (l.comparison i) l.out d).reg (l.neighbor j) = d.reg (l.neighbor j) := by
  apply markStore_other
  all_goals apply l.injective.ne
  all_goals simp [comparison, comparisonIndex]

theorem mark_out (l : Layout R k) (i : Fin k) (d : TapeStore R B) :
    (markStore (l.comparison i) l.out d).reg l.out =
      if d.reg l.col = d.reg (l.neighbor i) then 1 else d.reg l.out :=
  markStore_out (l.comparison i) (l.comparison_injective i) l.out (l.out_fresh i) d
end Layout

def marksLabels : ℕ → ℕ
  | 0 => 1
  | n+1 => 77+marksLabels n

def marks {k : ℕ} (l : Layout R k) : (is : List (Fin k)) → TapeProgram R B (marksLabels is.length)
  | [] => skip
  | i::is => TapeProgram.seq (markEq (l.comparison i) l.out) (marks l is)

def marksStore {k : ℕ} (l : Layout R k) : List (Fin k) → TapeStore R B → TapeStore R B
  | [],d => d
  | i::is,d => marksStore l is (markStore (l.comparison i) l.out d)

theorem marksStore_bound {k : ℕ} (l : Layout R k) (is : List (Fin k))
    (d : TapeStore R B) (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (marksStore l is d).reg j ≤ M := by
  induction is generalizing d with
  | nil => exact hd
  | cons i is ih =>
    exact ih _ (markStore_bound _ (l.comparison_injective i) _ d M hM hd)

theorem marksStore_frame {k : ℕ} (l : Layout R k) (is : List (Fin k))
    (d : TapeStore R B) (a : Fin 8) (ha : a = 0 ∨ a = 1 ∨ a = 7) :
    (marksStore l is d).reg (l.reg (.inl a)) = d.reg (l.reg (.inl a)) := by
  induction is generalizing d with
  | nil => rfl
  | cons i is ih =>
    rw [marksStore,ih]
    exact l.mark_frame i d a ha

theorem marksStore_neighbor {k : ℕ} (l : Layout R k) (is : List (Fin k))
    (d : TapeStore R B) (j : Fin k) :
    (marksStore l is d).reg (l.neighbor j) = d.reg (l.neighbor j) := by
  induction is generalizing d with
  | nil => rfl
  | cons i is ih =>
    rw [marksStore,ih]
    exact l.mark_neighbor i j d

theorem marksStore_out {k : ℕ} (l : Layout R k) (is : List (Fin k)) (d : TapeStore R B) :
    (marksStore l is d).reg l.out =
      if ∃ i ∈ is, d.reg l.col = d.reg (l.neighbor i) then 1 else d.reg l.out := by
  induction is generalizing d with
  | nil => simp [marksStore]
  | cons i is ih =>
    rw [marksStore,ih]
    simp only [Layout.col,l.mark_frame i d 1 (by simp),l.mark_neighbor,l.mark_out]
    by_cases hi : d.reg l.col = d.reg (l.neighbor i)
    · simp [hi]
    · simp [hi]

theorem marks_stops {k : ℕ} (l : Layout R k) (is : List (Fin k))
    (inp : Inputs) (d : TapeStore R B) (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ is.length*(160*(M+1)+1) ∧
      (marks l is).Stops inp (d.toCfg (marks (B := B) l is).entry) t e ∧
      e.store = marksStore l is d := by
  induction is generalizing d with
  | nil => exact ⟨0,d.toCfg (0 : Fin 1),by simp,skip_stops inp d,rfl⟩
  | cons i is ih =>
    obtain ⟨t,c,ht,hc,hcs⟩ := markEq_stops (l.comparison i) (l.comparison_injective i)
      l.out inp d M hM hd
    have hb : ∀ j, c.store.reg j ≤ M := by
      rw [hcs]
      exact markStore_bound _ (l.comparison_injective i) _ d M hM hd
    obtain ⟨s,e,hs,he,hes⟩ := ih c.store hb
    refine ⟨t+1+s,e.mapPC (rightLabel 77),?_,hc.seq he,?_⟩
    · simp only [List.length_cons]
      nlinarith
    · change e.store = _
      rw [hes,hcs]
      rfl

theorem markStore_payload (r : Fin 6 → Fin R) (out : Fin R) (d : TapeStore R B) :
    (markStore r out d).roHead = d.roHead ∧ (markStore r out d).output = d.output ∧
      (markStore r out d).bufferTape = d.bufferTape ∧
      (markStore r out d).bufferHead = d.bufferHead := by
  dsimp only [markStore]
  split_ifs <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem marksStore_payload {k : ℕ} (l : Layout R k) (is : List (Fin k)) (d : TapeStore R B) :
    (marksStore l is d).roHead = d.roHead ∧ (marksStore l is d).output = d.output ∧
      (marksStore l is d).bufferTape = d.bufferTape ∧
      (marksStore l is d).bufferHead = d.bufferHead := by
  induction is generalizing d with
  | nil => exact ⟨rfl,rfl,rfl,rfl⟩
  | cons i is ih =>
    obtain ⟨hr,ho,hb,hh⟩ := markStore_payload (l.comparison i) l.out d
    obtain ⟨ir,io,ib,ihd⟩ := ih (markStore (l.comparison i) l.out d)
    exact ⟨ir.trans hr,io.trans ho,ib.trans hb,ihd.trans hh⟩

def bodyLabels (k : ℕ) : ℕ := marksLabels (List.finRange k).length+4+2

/-- One actual column: scan the statically allocated neighbors, emit one bit,
consume its Boolean flag, then increment the preserved column counter. -/
def body {k : ℕ} (l : Layout R k) : TapeProgram R B (bodyLabels k) :=
  TapeProgram.seq (TapeProgram.seq (marks l (List.finRange k)) (emitFlag l.out))
    (TapeMacros.increment l.col)

def bodyStore {k : ℕ} (l : Layout R k) (d : TapeStore R B) : TapeStore R B :=
  let e := emitStore l.out (marksStore l (List.finRange k) d)
  e.setReg l.col (e.reg l.col+1)

theorem bodyStore_col {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (bodyStore l d).reg l.col = d.reg l.col+1 := by
  have hcol : l.col ≠ l.out := l.injective.ne (by simp)
  simp [bodyStore,emitStore,TapeStore.setReg,hcol,
    marksStore_frame l (List.finRange k) d 1 (by simp)]

theorem bodyStore_out {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (bodyStore l d).reg l.out = 0 := by
  have hcol : l.out ≠ l.col := l.injective.ne (by simp)
  simp [bodyStore,emitStore,TapeStore.setReg,hcol]

theorem bodyStore_frame {k : ℕ} (l : Layout R k) (d : TapeStore R B)
    (a : Fin 8) (ha : a = 0 ∨ a = 7) :
    (bodyStore l d).reg (l.reg (.inl a)) = d.reg (l.reg (.inl a)) := by
  have hc : l.reg (.inl a) ≠ l.col := by apply l.injective.ne; rcases ha with rfl | rfl <;> simp
  have ho : l.reg (.inl a) ≠ l.out := by apply l.injective.ne; rcases ha with rfl | rfl <;> simp
  simp only [bodyStore,TapeStore.setReg,Function.update_of_ne hc,emitStore,Function.update_of_ne ho]
  exact marksStore_frame l (List.finRange k) d a (by rcases ha with h | h <;> simp [h])

theorem bodyStore_neighbor {k : ℕ} (l : Layout R k) (d : TapeStore R B) (i : Fin k) :
    (bodyStore l d).reg (l.neighbor i) = d.reg (l.neighbor i) := by
  have hc : l.neighbor i ≠ l.col := l.injective.ne (by simp)
  have ho : l.neighbor i ≠ l.out := l.injective.ne (by simp)
  simp [bodyStore,TapeStore.setReg,emitStore,hc,ho,marksStore_neighbor]

theorem bodyStore_output {k : ℕ} (l : Layout R k) (d : TapeStore R B) (h : d.reg l.out = 0) :
    (bodyStore l d).output = d.output ++ [decide (∃ i, d.reg l.col = d.reg (l.neighbor i))] := by
  have hm := marksStore_out l (List.finRange k) d
  simp only [List.mem_finRange,true_and,h] at hm
  have hp := (marksStore_payload l (List.finRange k) d).2.1
  dsimp only [bodyStore,TapeStore.setReg,emitStore]
  rw [hm,hp]
  by_cases he : ∃ i, d.reg l.col = d.reg (l.neighbor i) <;> simp [he]

theorem bodyStore_bound {k : ℕ} (l : Layout R k) (d : TapeStore R B) (M : ℕ)
    (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) (hc : d.reg l.col < M) :
    ∀ j, (bodyStore l d).reg j ≤ M := by
  have hm := marksStore_bound l (List.finRange k) d M hM hd
  have hb : ∀ j, (emitStore l.out (marksStore l (List.finRange k) d)).reg j ≤ M :=
    FieldPrograms.setReg_bound _ l.out 0 M hm (by omega)
  intro j
  by_cases hj : j = l.col
  · subst j
    rw [bodyStore_col]
    omega
  · simpa only [bodyStore,TapeStore.setReg,Function.update_of_ne hj] using hb j

theorem body_stops {k : ℕ} (l : Layout R k) (inp : Inputs) (d : TapeStore R B)
    (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) (ho : d.reg l.out ≤ 1) :
    ∃ t e, t ≤ k*(160*(M+1)+1)+5 ∧
      (body l).Stops inp (d.toCfg (body (B := B) l).entry) t e ∧ e.store = bodyStore l d := by
  obtain ⟨t,c,ht,hc,hcs⟩ := marks_stops l (List.finRange k) inp d M hM hd
  have hb : c.reg l.out ≤ 1 := by
    change c.store.reg l.out ≤ 1
    rw [hcs,marksStore_out]
    split <;> omega
  have he := emitFlag_stops l.out inp c.store hb
  have hi := TapeMacros.increment_stops l.col inp (emitStore l.out c.store)
  have hall := (hc.seq he).seq hi
  let e := ((emitStore l.out c.store).setReg l.col ((emitStore l.out c.store).reg l.col+1)).toCfg (1 : Fin 2)
  refine ⟨t+5,e.mapPC (rightLabel (marksLabels (List.finRange k).length+4)),?_,?_,?_⟩
  · simpa only [List.length_finRange] using Nat.add_le_add_right ht 5
  · convert hall using 1 <;> rfl
  · change (emitStore l.out c.store).setReg l.col ((emitStore l.out c.store).reg l.col+1) = _
    rw [hcs]
    rfl

def loopStore {k : ℕ} (l : Layout R k) : ℕ → TapeStore R B → TapeStore R B
  | 0,d => d
  | n+1,d => loopStore l n (bodyStore l (decStore l.count d))

theorem dec_col {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (decStore l.count d).reg l.col = d.reg l.col := by
  simp [decStore,show l.col ≠ l.count from l.injective.ne (by simp)]

theorem dec_out {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (decStore l.count d).reg l.out = d.reg l.out := by
  simp [decStore,show l.out ≠ l.count from l.injective.ne (by simp)]

theorem dec_neighbor {k : ℕ} (l : Layout R k) (d : TapeStore R B) (i : Fin k) :
    (decStore l.count d).reg (l.neighbor i) = d.reg (l.neighbor i) := by
  simp [decStore,show l.neighbor i ≠ l.count from l.injective.ne (by simp)]

theorem dec_output {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (decStore l.count d).output = d.output := rfl

theorem loopStore_col {k : ℕ} (l : Layout R k) (n : ℕ) (d : TapeStore R B) :
    (loopStore l n d).reg l.col = d.reg l.col+n := by
  induction n generalizing d with
  | zero => simp [loopStore]
  | succ n ih =>
    rw [loopStore,ih,bodyStore_col,dec_col]
    omega

theorem loopStore_out {k : ℕ} (l : Layout R k) (n : ℕ) (d : TapeStore R B) (ho : d.reg l.out = 0) :
    (loopStore l n d).reg l.out = 0 := by
  induction n generalizing d with
  | zero => exact ho
  | succ n ih => exact ih _ (bodyStore_out l _)

theorem loopStore_neighbor {k : ℕ} (l : Layout R k) (n : ℕ) (d : TapeStore R B) (i : Fin k) :
    (loopStore l n d).reg (l.neighbor i) = d.reg (l.neighbor i) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [loopStore,ih,bodyStore_neighbor,dec_neighbor]

theorem loopStore_output {k : ℕ} (l : Layout R k) (n : ℕ) (d : TapeStore R B) (ho : d.reg l.out = 0) :
    (loopStore l n d).output = d.output ++
      List.ofFn (fun j : Fin n => decide (∃ i, d.reg l.col+j.val = d.reg (l.neighbor i))) := by
  induction n generalizing d with
  | zero => simp [loopStore]
  | succ n ih =>
    rw [loopStore,ih _ (bodyStore_out l _),bodyStore_output l _ (by rw [dec_out]; exact ho)]
    simp [bodyStore_col,bodyStore_neighbor,decStore,Layout.col,Layout.count,Layout.neighbor,
      l.injective.eq_iff,List.ofFn_succ,List.append_assoc,
      Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem loop_stops {k : ℕ} (l : Layout R k) (inp : Inputs) (n M : ℕ)
    (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hn : d.reg l.count = n) (hc : d.reg l.col+n ≤ M) (ho : d.reg l.out = 0) :
    ∃ t, t ≤ n*(k*(160*(M+1)+1)+7)+1 ∧
      (countedLoop (body l) l.count).Stops inp (d.toCfg (loopHeader (bodyLabels k))) t
        ((loopStore l n d).toCfg (loopExit (bodyLabels k))) := by
  induction n generalizing d with
  | zero => exact ⟨1,by omega,loop_zero (body l) l.count inp d hn⟩
  | succ n ih =>
    let d₁ := decStore l.count d
    have hb₁ : ∀ j, d₁.reg j ≤ M := by
      intro j
      by_cases hj : j = l.count
      · subst j
        simpa [d₁,decStore] using (Nat.sub_le (d.reg l.count) 1).trans (hd l.count)
      · simpa [d₁,decStore,hj] using hd j
    have hcol₁ : d₁.reg l.col = d.reg l.col := dec_col l d
    have hout₁ : d₁.reg l.out = 0 := (dec_out l d).trans ho
    obtain ⟨s,e,hs,he,hes⟩ := body_stops l inp d₁ M hM hb₁ (by omega)
    let d₂ := bodyStore l d₁
    have hb₂ : ∀ j, d₂.reg j ≤ M := bodyStore_bound l d₁ M hM hb₁ (by omega)
    have hn₂ : d₂.reg l.count = n := by
      rw [show d₂ = bodyStore l d₁ from rfl,bodyStore_frame l d₁ 7 (by simp)]
      simp [d₁,decStore,hn]
    have hcol₂ : d₂.reg l.col+n ≤ M := by
      change (bodyStore l d₁).reg l.col+n ≤ M
      rw [bodyStore_col,hcol₁]
      omega
    obtain ⟨t,ht,hstop⟩ := ih d₂ hb₂ hn₂ hcol₂ (bodyStore_out l d₁)
    have hh := loop_positive_header (body l) l.count inp d (by omega)
    have hb := he.exec.relabel (leftLabel 2) (loop_code_body_active (body l) l.count)
    have hx := loop_body_return (body l) l.count inp e he.halted
    have heq : e.store.toCfg (loopHeader (bodyLabels k)) = d₂.toCfg (loopHeader (bodyLabels k)) := by rw [hes]
    rw [heq] at hx
    refine ⟨1+s+1+t,?_,⟨?_,hstop.halted⟩⟩
    · rw [Nat.succ_mul]
      omega
    · exact ((hh.trans hb).trans hx).trans hstop.exec

def prepare {k : ℕ} (l : Layout R k) : TapeProgram R B 15 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.clear l.col) (TapeMacros.clear l.out))
    (TapeMacros.copy l.n l.count (l.reg (.inl 6)))

def prepareStore {k : ℕ} (l : Layout R k) (d : TapeStore R B) : TapeStore R B :=
  ((((d.setReg l.col 0).setReg l.out 0).setReg l.count (d.reg l.n)).setReg (l.reg (.inl 6)) 0)

theorem prepareStore_col {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (prepareStore l d).reg l.col = 0 := by
  simp [prepareStore,TapeStore.setReg,Layout.col,Layout.out,Layout.count,l.injective.eq_iff]

theorem prepareStore_out {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (prepareStore l d).reg l.out = 0 := by
  simp [prepareStore,TapeStore.setReg,Layout.col,Layout.out,Layout.count,l.injective.eq_iff]

theorem prepareStore_count {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (prepareStore l d).reg l.count = d.reg l.n := by
  simp [prepareStore,TapeStore.setReg,Layout.col,Layout.out,Layout.count,l.injective.eq_iff]

theorem prepareStore_n {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (prepareStore l d).reg l.n = d.reg l.n := by
  simp [prepareStore,TapeStore.setReg,Layout.n,Layout.col,Layout.out,Layout.count,l.injective.eq_iff]

theorem prepareStore_neighbor {k : ℕ} (l : Layout R k) (d : TapeStore R B) (i : Fin k) :
    (prepareStore l d).reg (l.neighbor i) = d.reg (l.neighbor i) := by
  simp [prepareStore,TapeStore.setReg,Layout.neighbor,Layout.col,Layout.out,Layout.count,l.injective.eq_iff]

theorem prepareStore_bound {k : ℕ} (l : Layout R k) (d : TapeStore R B) (M : ℕ)
    (hd : ∀ j, d.reg j ≤ M) : ∀ j, (prepareStore l d).reg j ≤ M := by
  exact FieldPrograms.setReg_bound _ _ 0 M
    (FieldPrograms.setReg_bound _ _ (d.reg l.n) M
      (FieldPrograms.setReg_bound _ _ 0 M
        (FieldPrograms.setReg_bound _ _ 0 M hd (Nat.zero_le _)) (Nat.zero_le _))
      (hd l.n)) (Nat.zero_le _)

theorem prepare_stops {k : ℕ} (l : Layout R k) (inp : Inputs) (d : TapeStore R B)
    (M : ℕ) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 16*(M+1) ∧
      (prepare l).Stops inp (d.toCfg (prepare (B := B) l).entry) t e ∧ e.store = prepareStore l d := by
  have h₁ := TapeMacros.clear_stops l.col inp (d.reg l.col) d rfl
  let d₁ := d.setReg l.col 0
  have h₂ := TapeMacros.clear_stops l.out inp (d₁.reg l.out) d₁ rfl
  let d₂ := d₁.setReg l.out 0
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops l.n l.count (l.reg (.inl 6))
    (l.injective.ne (by simp)) (l.injective.ne (by simp)) (l.injective.ne (by simp)) inp d₂
  have hn₂ : d₂.reg l.n = d.reg l.n := by
    simp [d₂,d₁,TapeStore.setReg,Layout.n,Layout.col,Layout.out,l.injective.eq_iff]
  have hc₂ : d₂.reg l.count = d.reg l.count := by
    simp [d₂,d₁,TapeStore.setReg,Layout.count,Layout.col,Layout.out,l.injective.eq_iff]
  have ht₂ : d₂.reg (l.reg (.inl 6)) = d.reg (l.reg (.inl 6)) := by
    simp [d₂,d₁,TapeStore.setReg,Layout.col,Layout.out,l.injective.eq_iff]
  have ho₁ : d₁.reg l.out = d.reg l.out := by
    simp [d₁,TapeStore.setReg,Layout.col,Layout.out,l.injective.eq_iff]
  have hall := (h₁.seq h₂).seq he
  refine ⟨d.reg l.col+1+1+(d₁.reg l.out+1)+1+
    (d₂.reg l.count+d₂.reg (l.reg (.inl 6))+5*d₂.reg l.n+7),
    e.mapPC (rightLabel 4),?_,?_,?_⟩
  · rw [hn₂,hc₂,ht₂,ho₁]
    have := hd l.col
    have := hd l.out
    have := hd l.count
    have := hd (l.reg (.inl 6))
    have := hd l.n
    omega
  · convert hall using 1 <;> rfl
  · change e.store = _
    rw [hes,hn₂]
    rfl

def writeRow {k : ℕ} (l : Layout R k) : TapeProgram R B (15+(bodyLabels k+2)) :=
  TapeProgram.seq (prepare l) (countedLoop (body l) l.count)

def writeRowStore {k : ℕ} (l : Layout R k) (d : TapeStore R B) : TapeStore R B :=
  loopStore l (d.reg l.n) (prepareStore l d)

def writeRowBound (k M : ℕ) : ℕ :=
  16*(M+1)+1+M*(k*(160*(M+1)+1)+7)+1

theorem writeRow_stops {k : ℕ} (l : Layout R k) (inp : Inputs) (d : TapeStore R B)
    (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ writeRowBound k M ∧
      (writeRow l).Stops inp (d.toCfg (writeRow (B := B) l).entry) t e ∧
      e.store = writeRowStore l d := by
  obtain ⟨s,c,hs,hc,hcs⟩ := prepare_stops l inp d M hd
  have hb : ∀ j, c.store.reg j ≤ M := by rw [hcs]; exact prepareStore_bound l d M hd
  have hn : c.store.reg l.count = d.reg l.n := by rw [hcs,prepareStore_count]
  have hcol : c.store.reg l.col+d.reg l.n ≤ M := by
    rw [hcs,prepareStore_col,zero_add]
    exact hd l.n
  have ho : c.store.reg l.out = 0 := by rw [hcs,prepareStore_out]
  obtain ⟨t,ht,hstop⟩ := loop_stops l inp (d.reg l.n) M hM c.store hb hn hcol ho
  refine ⟨s+1+t,_,?_,hc.seq hstop,?_⟩
  · have hh := Nat.mul_le_mul_right (k*(160*(M+1)+1)+7) (hd l.n)
    unfold writeRowBound
    omega
  · change loopStore l (d.reg l.n) c.store = _
    rw [hcs]
    rfl

theorem writeRow_output {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (writeRowStore l d).output = d.output ++
      List.ofFn (fun j : Fin (d.reg l.n) => decide (∃ i, j.val = d.reg (l.neighbor i))) := by
  unfold writeRowStore
  rw [loopStore_output l _ _ (prepareStore_out l d)]
  simp [prepareStore,TapeStore.setReg,Layout.col,Layout.out,Layout.count,Layout.neighbor,
    l.injective.eq_iff]

theorem bodyStore_payload {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (bodyStore l d).roHead = d.roHead ∧ (bodyStore l d).bufferTape = d.bufferTape ∧
      (bodyStore l d).bufferHead = d.bufferHead := by
  obtain ⟨hr,_,hb,hh⟩ := marksStore_payload l (List.finRange k) d
  exact ⟨hr,hb,hh⟩

theorem loopStore_payload {k : ℕ} (l : Layout R k) (n : ℕ) (d : TapeStore R B) :
    (loopStore l n d).roHead = d.roHead ∧ (loopStore l n d).bufferTape = d.bufferTape ∧
      (loopStore l n d).bufferHead = d.bufferHead := by
  induction n generalizing d with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨ir,ib,ihd⟩ := ih (bodyStore l (decStore l.count d))
    obtain ⟨hr,hb,hh⟩ := bodyStore_payload l (decStore l.count d)
    exact ⟨ir.trans hr,ib.trans hb,ihd.trans hh⟩

theorem writeRow_payload {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (writeRowStore l d).roHead = d.roHead ∧ (writeRowStore l d).bufferTape = d.bufferTape ∧
      (writeRowStore l d).bufferHead = d.bufferHead :=
  loopStore_payload l _ (prepareStore l d)

theorem marksStore_fresh {k : ℕ} (l : Layout R k) (is : List (Fin k))
    (d : TapeStore R B) (j : Fin R) (hj : ∀ i, j ≠ l.reg i) :
    (marksStore l is d).reg j = d.reg j := by
  induction is generalizing d with
  | nil => rfl
  | cons i is ih =>
    rw [marksStore,ih]
    exact markStore_other _ _ d j (hj (.inl 2)) (hj (.inl 3))
      (hj (.inl 4)) (hj (.inl 5)) (hj (.inl 6))

theorem bodyStore_fresh {k : ℕ} (l : Layout R k) (d : TapeStore R B)
    (j : Fin R) (hj : ∀ i, j ≠ l.reg i) : (bodyStore l d).reg j = d.reg j := by
  simp only [bodyStore,TapeStore.setReg,Function.update_of_ne (hj (.inl 1)),
    emitStore,Function.update_of_ne (hj (.inl 2))]
  exact marksStore_fresh l _ d j hj

theorem loopStore_fresh {k : ℕ} (l : Layout R k) (n : ℕ) (d : TapeStore R B)
    (j : Fin R) (hj : ∀ i, j ≠ l.reg i) : (loopStore l n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [loopStore,ih,bodyStore_fresh l _ j hj]
    simp [decStore,hj (.inl 7)]

theorem writeRow_fresh {k : ℕ} (l : Layout R k) (d : TapeStore R B)
    (j : Fin R) (hj : ∀ i, j ≠ l.reg i) : (writeRowStore l d).reg j = d.reg j := by
  rw [writeRowStore,loopStore_fresh l _ _ j hj]
  simp [prepareStore,TapeStore.setReg,hj (.inl 1),hj (.inl 2),hj (.inl 6),hj (.inl 7)]

theorem loopStore_n {k : ℕ} (l : Layout R k) (n : ℕ) (d : TapeStore R B) :
    (loopStore l n d).reg l.n = d.reg l.n := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [loopStore,ih,bodyStore_frame l _ 0 (by simp)]
    simp [decStore,Layout.n,Layout.count,l.injective.eq_iff]

theorem writeRow_n {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (writeRowStore l d).reg l.n = d.reg l.n := by
  rw [writeRowStore,loopStore_n,prepareStore_n]

theorem writeRow_neighbor {k : ℕ} (l : Layout R k) (d : TapeStore R B) (i : Fin k) :
    (writeRowStore l d).reg (l.neighbor i) = d.reg (l.neighbor i) := by
  rw [writeRowStore,loopStore_neighbor,prepareStore_neighbor]

theorem loopStore_bound {k : ℕ} (l : Layout R k) (n : ℕ) (d : TapeStore R B)
    (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) (hc : d.reg l.col+n ≤ M) :
    ∀ j, (loopStore l n d).reg j ≤ M := by
  induction n generalizing d with
  | zero => exact hd
  | succ n ih =>
    have hb : ∀ j, (decStore l.count d).reg j ≤ M := by
      intro j
      by_cases hj : j = l.count
      · subst j
        simpa [decStore] using (Nat.sub_le (d.reg l.count) 1).trans (hd l.count)
      · simpa [decStore,hj] using hd j
    have hcol : (decStore l.count d).reg l.col < M := by rw [dec_col]; omega
    have he := bodyStore_bound l (decStore l.count d) M hM hb hcol
    have hec : (bodyStore l (decStore l.count d)).reg l.col+n ≤ M := by
      rw [bodyStore_col,dec_col]
      omega
    exact ih _ he hec

theorem writeRowStore_bound {k : ℕ} (l : Layout R k) (d : TapeStore R B)
    (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (writeRowStore l d).reg j ≤ M := by
  apply loopStore_bound l _ _ M hM (prepareStore_bound l d M hd)
  rw [prepareStore_col,zero_add]
  exact hd l.n

theorem loopStore_count {k : ℕ} (l : Layout R k) (n : ℕ) (d : TapeStore R B) :
    (loopStore l n d).reg l.count = d.reg l.count-n := by
  induction n generalizing d with
  | zero => simp [loopStore]
  | succ n ih =>
    rw [loopStore,ih,bodyStore_frame l _ 7 (by simp)]
    simp [decStore,Nat.sub_sub,Nat.add_comm]

theorem writeRowStore_post {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (writeRowStore l d).reg l.col = d.reg l.n ∧
      (writeRowStore l d).reg l.out = 0 ∧ (writeRowStore l d).reg l.count = 0 := by
  exact ⟨by rw [writeRowStore,loopStore_col,prepareStore_col,zero_add],
    loopStore_out l _ _ (prepareStore_out l d),
    by rw [writeRowStore,loopStore_count,prepareStore_count,Nat.sub_self]⟩

theorem writeRowBound_polynomial (k M : ℕ) :
    writeRowBound k M ≤ (161*k+25)*(M+1)^2 := by
  have hb : k*(160*(M+1)+1)+7 ≤ (161*k+7)*(M+1) := by nlinarith
  have hl : M*(k*(160*(M+1)+1)+7) ≤ (161*k+7)*(M+1)^2 := by
    calc
      _ ≤ M*((161*k+7)*(M+1)) := Nat.mul_le_mul_left M hb
      _ ≤ (M+1)*((161*k+7)*(M+1)) := Nat.mul_le_mul_right _ (Nat.le_succ M)
      _ = _ := by ring
  have hx : M+1 ≤ (M+1)^2 := by nlinarith
  have hp : 1 ≤ (M+1)^2 := by omega
  unfold writeRowBound
  nlinarith

#print axioms markStore_out
#print axioms markEq_stops
#print axioms emitFlag_stops
#print axioms marksStore_out
#print axioms marks_stops
#print axioms body_stops
#print axioms loopStore_output
#print axioms loop_stops
#print axioms writeRow_stops
#print axioms writeRow_output
#print axioms writeRow_fresh
#print axioms writeRowBound_polynomial
#print axioms writeRowStore_bound
end NeighborWriter
end ExpandingCodes.Computation
