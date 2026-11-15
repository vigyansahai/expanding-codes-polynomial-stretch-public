import ExpandingCodes.Computation.CounterCompiler

set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

/-- Data carried between finite source-program fragments. -/
structure CounterStore (R : ℕ) where
  reg : Fin R → ℕ
  roHead : Fin 4 → ℕ
  output : List Bool

namespace CounterCfg
variable {R L K : ℕ}

abbrev store (c : CounterCfg R L) : CounterStore R := ⟨c.reg, c.roHead, c.output⟩

abbrev mapPC (f : Fin L → Fin K) (c : CounterCfg R L) : CounterCfg R K :=
  ⟨f c.pc, c.reg, c.roHead, c.output⟩
end CounterCfg

namespace CounterStore
variable {R L : ℕ}

abbrev toCfg (d : CounterStore R) (j : Fin L) : CounterCfg R L :=
  ⟨j, d.reg, d.roHead, d.output⟩

@[simp] theorem store_toCfg (d : CounterStore R) (j : Fin L) : (d.toCfg j).store = d := by
  cases d
  rfl
end CounterStore

namespace CounterInstr
variable {R L K : ℕ}

/-- Relabels finite jump destinations; it adds no machine operation. -/
def relabel (f : Fin L → Fin K) : CounterInstr R L → CounterInstr R K
  | .halt => .halt
  | .jump j => .jump (f j)
  | .inc r j => .inc r (f j)
  | .dec r z p => .dec r (f z) (f p)
  | .emit b j => .emit b (f j)
  | .read r next => .read r (f ∘ next)

 theorem relabel_eq_halt (f : Fin L → Fin K) (i : CounterInstr R L) :
    relabel f i = .halt ↔ i = .halt := by
  cases i <;> simp [relabel]
end CounterInstr

namespace CounterProgram
variable {R L K : ℕ}

/-- A finite active execution prefix. It records exactly the actual instructions
executed, excluding extra repetitions of the source's absorbing halt. -/
inductive Exec (P : CounterProgram R L) (inp : Inputs) :
    CounterCfg R L → ℕ → CounterCfg R L → Prop where
  | refl (c) : Exec P inp c 0 c
  | step {c d e t} (active : ¬ P.halted c) (next : P.step inp c = d)
      (tail : Exec P inp d t e) : Exec P inp c (t+1) e

/-- An active source execution ending at a halt instruction. -/
structure Stops (P : CounterProgram R L) (inp : Inputs)
    (c : CounterCfg R L) (t : ℕ) (d : CounterCfg R L) : Prop where
  exec : P.Exec inp c t d
  halted : P.halted d

 theorem Exec.iterate {P : CounterProgram R L} {inp : Inputs}
    {c d : CounterCfg R L} {t : ℕ} (h : P.Exec inp c t d) :
    (P.step inp)^[t] c = d := by
  induction h with
  | refl c => rfl
  | step active next tail ih =>
    rw [Function.iterate_succ_apply, next]
    exact ih

 theorem Exec.one {P : CounterProgram R L} {inp : Inputs} {c d : CounterCfg R L}
    (ha : ¬ P.halted c) (hs : P.step inp c = d) : P.Exec inp c 1 d :=
  Exec.step ha hs (Exec.refl d)

 theorem Exec.trans {P : CounterProgram R L} {inp : Inputs}
    {c d e : CounterCfg R L} {t s : ℕ}
    (h : P.Exec inp c t d) (k : P.Exec inp d s e) : P.Exec inp c (t+s) e := by
  induction h with
  | refl c => simpa using k
  | step active next tail ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Exec.step active next (ih k)

 theorem step_relabel (P : CounterProgram R L) (Q : CounterProgram R K)
    (f : Fin L → Fin K) (inp : Inputs) (c : CounterCfg R L)
    (hc : Q.code (f c.pc) = CounterInstr.relabel f (P.code c.pc)) :
    Q.step inp (c.mapPC f) = (P.step inp c).mapPC f := by
  simp only [step, CounterCfg.mapPC, hc]
  cases h : P.code c.pc <;> simp only [CounterInstr.relabel]
  all_goals try rfl
  split <;> simp_all

/-- Relabeling preserves active traces even when the embedding redirects halt
instructions. Only labels actually executed before halt are constrained. -/
 theorem Exec.relabel {P : CounterProgram R L} {Q : CounterProgram R K}
    {inp : Inputs} {c d : CounterCfg R L} {t : ℕ} (h : P.Exec inp c t d)
    (f : Fin L → Fin K)
    (hc : ∀ j, P.code j ≠ .halt → Q.code (f j) = CounterInstr.relabel f (P.code j)) :
    Q.Exec inp (c.mapPC f) t (d.mapPC f) := by
  induction h with
  | refl c => exact Exec.refl _
  | @step c d e t active next tail ih =>
    have hcode := hc c.pc active
    apply Exec.step (d := d.mapPC f)
    · change Q.code (f c.pc) ≠ .halt
      rw [hcode]
      intro h
      exact active ((CounterInstr.relabel_eq_halt f (P.code c.pc)).mp h)
    · rw [step_relabel P Q f inp c hcode, next]
    · exact ih

/-- A proved source routine immediately supplies a canonical machine bound. -/
 theorem Stops.compile {P : CounterProgram R L} {inp : Inputs} {t : ℕ}
    {d : CounterCfg R L} (h : P.Stops inp P.init t d) (O : Set (List Bool)) :
    (CounterCompiler.compile P).HaltsWith O inp (1+2*t) (bitsSym d.output) := by
  have hr : P.run inp t = d := h.exec.iterate
  simpa [hr] using CounterCompiler.compile_halts P O inp t (by simpa [hr] using h.halted)

/-- Constructive inclusions into the disjoint union of two finite code tables. -/
def leftLabel (K : ℕ) (j : Fin L) : Fin (L+K) := finSumFinEquiv (.inl j)
def rightLabel (L : ℕ) (j : Fin K) : Fin (L+K) := finSumFinEquiv (.inr j)

/-- Finite program sequencing. Each halt in the first fragment becomes one jump
into the second fragment; all other instructions are copied with relabeled targets. -/
def seq (P : CounterProgram R L) (Q : CounterProgram R K) : CounterProgram R (L+K) where
  entry := leftLabel K P.entry
  code := fun j => match finSumFinEquiv.symm j with
    | .inl i => match P.code i with
      | .halt => .jump (rightLabel L Q.entry)
      | a => a.relabel (leftLabel K)
    | .inr i => (Q.code i).relabel (rightLabel L)

 theorem seq_code_left_active (P : CounterProgram R L) (Q : CounterProgram R K)
    (j : Fin L) (hj : P.code j ≠ .halt) :
    (CounterProgram.seq P Q).code (leftLabel K j) = (P.code j).relabel (leftLabel K) := by
  simp only [seq, leftLabel, Equiv.symm_apply_apply]

 theorem seq_code_left_halt (P : CounterProgram R L) (Q : CounterProgram R K)
    (j : Fin L) (hj : P.code j = .halt) :
    (CounterProgram.seq P Q).code (leftLabel K j) = .jump (rightLabel L Q.entry) := by
  simp [seq, leftLabel, hj]

 theorem seq_code_right (P : CounterProgram R L) (Q : CounterProgram R K) (j : Fin K) :
    (CounterProgram.seq P Q).code (rightLabel L j) = (Q.code j).relabel (rightLabel L) := by
  simp [seq, rightLabel]

/-- Exact compositional source cost: first routine, one linking jump, second routine. -/
 theorem Stops.seq {P : CounterProgram R L} {Q : CounterProgram R K} {inp : Inputs}
    {c d : CounterCfg R L} {e : CounterCfg R K} {t s : ℕ}
    (hp : P.Stops inp c t d) (hq : Q.Stops inp (d.store.toCfg Q.entry) s e) :
    (CounterProgram.seq P Q).Stops inp (c.mapPC (leftLabel K)) (t+1+s) (e.mapPC (rightLabel L)) := by
  have hleft := hp.exec.relabel (leftLabel K) (seq_code_left_active P Q)
  have hright := hq.exec.relabel (rightLabel L) (fun j _ => seq_code_right P Q j)
  have hbridge : (CounterProgram.seq P Q).Exec inp (d.mapPC (leftLabel K)) 1
      ((d.store.toCfg Q.entry).mapPC (rightLabel L)) := by
    apply Exec.one
    · change (CounterProgram.seq P Q).code (leftLabel K d.pc) ≠ .halt
      rw [seq_code_left_halt P Q d.pc hp.halted]
      simp
    · simp only [step, CounterCfg.mapPC]
      rw [seq_code_left_halt P Q d.pc hp.halted]
  constructor
  · exact (hleft.trans hbridge).trans hright
  · change (CounterProgram.seq P Q).code (rightLabel L e.pc) = .halt
    rw [seq_code_right, hq.halted]
    rfl

/-- A syntactic sufficient condition for an instruction to preserve a register. -/
def preservesRegister (r : Fin R) : CounterInstr R L → Prop
  | .inc s _ => s ≠ r
  | .dec s _ _ => s ≠ r
  | _ => True

/-- A loop counter is fresh when the body never increments or decrements it. -/
def Fresh (P : CounterProgram R L) (r : Fin R) : Prop :=
  ∀ j, preservesRegister r (P.code j)

 theorem step_reg_of_fresh (P : CounterProgram R L) (r : Fin R) (hf : P.Fresh r)
    (inp : Inputs) (c : CounterCfg R L) : (P.step inp c).reg r = c.reg r := by
  have h := hf c.pc
  cases hc : P.code c.pc <;> simp only [hc, preservesRegister] at h
  all_goals simp only [step, hc]
  all_goals try rfl
  case inc s j => simp [Function.update_of_ne (Ne.symm h)]
  case dec s z p => split <;> simp [Function.update_of_ne (Ne.symm h)]

 theorem Exec.reg_of_fresh {P : CounterProgram R L} {r : Fin R}
    {inp : Inputs} {c d : CounterCfg R L} {t : ℕ} (h : P.Exec inp c t d) (hf : P.Fresh r) :
    d.reg r = c.reg r := by
  induction h with
  | refl c => rfl
  | step active next tail ih =>
    rw [ih, ← next]
    exact step_reg_of_fresh P r hf inp _

/-- The body occupies the first L labels, followed by a decrement/test header and halt exit. -/
def loopHeader (L : ℕ) : Fin (L+2) := rightLabel L (0 : Fin 2)
def loopExit (L : ℕ) : Fin (L+2) := rightLabel L (1 : Fin 2)

def countedLoop (P : CounterProgram R L) (r : Fin R) : CounterProgram R (L+2) where
  entry := loopHeader L
  code := fun j => match finSumFinEquiv.symm j with
    | .inl i => match P.code i with
      | .halt => .jump (loopHeader L)
      | a => a.relabel (leftLabel 2)
    | .inr i => if i = 0 then .dec r (loopExit L) (leftLabel 2 P.entry) else .halt

 theorem loop_code_body_active (P : CounterProgram R L) (r : Fin R)
    (j : Fin L) (hj : P.code j ≠ .halt) :
    (countedLoop P r).code (leftLabel 2 j) = (P.code j).relabel (leftLabel 2) := by
  simp only [countedLoop, leftLabel, Equiv.symm_apply_apply]

 theorem loop_code_body_halt (P : CounterProgram R L) (r : Fin R)
    (j : Fin L) (hj : P.code j = .halt) :
    (countedLoop P r).code (leftLabel 2 j) = .jump (loopHeader L) := by
  simp [countedLoop, leftLabel, hj]

 theorem loop_code_header (P : CounterProgram R L) (r : Fin R) :
    (countedLoop P r).code (loopHeader L) = .dec r (loopExit L) (leftLabel 2 P.entry) := by
  simp [countedLoop, loopHeader, rightLabel]

 theorem loop_code_exit (P : CounterProgram R L) (r : Fin R) :
    (countedLoop P r).code (loopExit L) = .halt := by
  simp [countedLoop, loopExit, rightLabel]

/-- Store after the loop's positive decrement instruction. -/
abbrev decStore (r : Fin R) (d : CounterStore R) : CounterStore R :=
  { d with reg := Function.update d.reg r (d.reg r - 1) }

 theorem loop_zero (P : CounterProgram R L) (r : Fin R) (inp : Inputs)
    (d : CounterStore R) (hd : d.reg r = 0) :
    (countedLoop P r).Stops inp (d.toCfg (loopHeader L)) 1 (d.toCfg (loopExit L)) := by
  constructor
  · apply Exec.one
    · change (countedLoop P r).code (loopHeader L) ≠ .halt
      rw [loop_code_header]
      simp
    · simp only [step, CounterStore.toCfg, loop_code_header, hd, ite_true]
  · exact loop_code_exit P r

 theorem loop_positive_header (P : CounterProgram R L) (r : Fin R) (inp : Inputs)
    (d : CounterStore R) (hd : d.reg r ≠ 0) :
    (countedLoop P r).Exec inp (d.toCfg (loopHeader L)) 1
      (((decStore r d).toCfg P.entry).mapPC (leftLabel 2)) := by
  apply Exec.one
  · change (countedLoop P r).code (loopHeader L) ≠ .halt
    rw [loop_code_header]
    simp
  · simp only [step, CounterStore.toCfg, loop_code_header, if_neg hd]

 theorem loop_body_return (P : CounterProgram R L) (r : Fin R) (inp : Inputs)
    (c : CounterCfg R L) (hc : P.halted c) :
    (countedLoop P r).Exec inp (c.mapPC (leftLabel 2)) 1 (c.store.toCfg (loopHeader L)) := by
  apply Exec.one
  · change (countedLoop P r).code (leftLabel 2 c.pc) ≠ .halt
    rw [loop_code_body_halt P r c.pc hc]
    simp
  · simp only [step, CounterCfg.mapPC]
    rw [loop_code_body_halt P r c.pc hc]

/-- A modular loop rule with an explicit source-step bound. The body is an actual
finite program, and `hbody` consists of checked finite executions of that program.
The indexed invariant describes the payload after each remaining iteration. -/
 theorem countedLoop_stops (P : CounterProgram R L) (r : Fin R) (hf : P.Fresh r)
    (inp : Inputs) (B : ℕ) (Inv : ℕ → CounterStore R → Prop)
    (hbody : ∀ n d, d.reg r = n+1 → Inv (n+1) d →
      ∃ t c, t ≤ B ∧ P.Stops inp ((decStore r d).toCfg P.entry) t c ∧ Inv n c.store)
    (n : ℕ) (d : CounterStore R) (hd : d.reg r = n) (hi : Inv n d) :
    ∃ t e, t ≤ n*(B+2)+1 ∧
      (countedLoop P r).Stops inp (d.toCfg (loopHeader L)) t (e.toCfg (loopExit L)) ∧
      Inv 0 e ∧ e.reg r = 0 := by
  induction n generalizing d with
  | zero =>
    exact ⟨1, d, by omega, loop_zero P r inp d hd, hi, hd⟩
  | succ n ih =>
    obtain ⟨s, c, hs, hstop, hInv⟩ := hbody n d hd hi
    have hc : c.reg r = n := by
      have hh := hstop.exec.reg_of_fresh hf
      simpa [CounterStore.toCfg, decStore, hd] using hh
    obtain ⟨t, e, ht, he, hIe, hzero⟩ := ih c.store hc hInv
    have hheader := loop_positive_header P r inp d (by omega)
    have hrun := hstop.exec.relabel (leftLabel 2) (loop_code_body_active P r)
    have hreturn := loop_body_return P r inp c hstop.halted
    refine ⟨1+s+1+t, e, ?_, ⟨?_, he.halted⟩, hIe, hzero⟩
    · simp only [Nat.succ_mul]
      omega
    · exact ((hheader.trans hrun).trans hreturn).trans he.exec

#print axioms countedLoop_stops

#print axioms Stops.seq
#print axioms Stops.compile
end CounterProgram
end ExpandingCodes.Computation
