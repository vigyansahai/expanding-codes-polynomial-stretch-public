import ExpandingCodes.Computation.TapeCompiler

set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

/-- Data carried between finite source-program fragments. -/
structure TapeStore (R B : ℕ) where
  reg : Fin R → ℕ
  roHead : Fin 4 → ℕ
  output : List Bool
  bufferTape : Fin B → List Sym
  bufferHead : Fin B → ℕ

namespace TapeCfg
variable {R B L K : ℕ}

abbrev store (c : TapeCfg R B L) : TapeStore R B := ⟨c.reg, c.roHead, c.output, c.bufferTape, c.bufferHead⟩

abbrev mapPC (f : Fin L → Fin K) (c : TapeCfg R B L) : TapeCfg R B K :=
  ⟨f c.pc, c.reg, c.roHead, c.output, c.bufferTape, c.bufferHead⟩
end TapeCfg

namespace TapeStore
variable {R B L : ℕ}

abbrev toCfg (d : TapeStore R B) (j : Fin L) : TapeCfg R B L :=
  ⟨j, d.reg, d.roHead, d.output, d.bufferTape, d.bufferHead⟩

@[simp] theorem store_toCfg (d : TapeStore R B) (j : Fin L) : (d.toCfg j).store = d := by
  cases d
  rfl
end TapeStore

namespace TapeInstr
variable {R B L K : ℕ}

/-- Relabels finite jump destinations; it adds no machine operation. -/
def relabel (f : Fin L → Fin K) : TapeInstr R B L → TapeInstr R B K
  | .halt => .halt
  | .jump j => .jump (f j)
  | .inc r j => .inc r (f j)
  | .dec r z p => .dec r (f z) (f p)
  | .emit b j => .emit b (f j)
  | .read r next => .read r (f ∘ next)
  | .buffer b action => .buffer b (fun x => let a := action x; (a.1, a.2.1, f a.2.2))

 theorem relabel_eq_halt (f : Fin L → Fin K) (i : TapeInstr R B L) :
    relabel f i = .halt ↔ i = .halt := by
  cases i <;> simp [relabel]
end TapeInstr

namespace TapeProgram
variable {R B L K : ℕ}

/-- A finite active execution prefix. It records exactly the actual instructions
executed, excluding extra repetitions of the source's absorbing halt. -/
inductive Exec (P : TapeProgram R B L) (inp : Inputs) :
    TapeCfg R B L → ℕ → TapeCfg R B L → Prop where
  | refl (c) : Exec P inp c 0 c
  | step {c d e t} (active : ¬ P.halted c) (next : P.step inp c = d)
      (tail : Exec P inp d t e) : Exec P inp c (t+1) e

/-- An active source execution ending at a halt instruction. -/
structure Stops (P : TapeProgram R B L) (inp : Inputs)
    (c : TapeCfg R B L) (t : ℕ) (d : TapeCfg R B L) : Prop where
  exec : P.Exec inp c t d
  halted : P.halted d

 theorem Exec.iterate {P : TapeProgram R B L} {inp : Inputs}
    {c d : TapeCfg R B L} {t : ℕ} (h : P.Exec inp c t d) :
    (P.step inp)^[t] c = d := by
  induction h with
  | refl c => rfl
  | step active next tail ih =>
    rw [Function.iterate_succ_apply, next]
    exact ih

 theorem Exec.one {P : TapeProgram R B L} {inp : Inputs} {c d : TapeCfg R B L}
    (ha : ¬ P.halted c) (hs : P.step inp c = d) : P.Exec inp c 1 d :=
  Exec.step ha hs (Exec.refl d)

 theorem Exec.trans {P : TapeProgram R B L} {inp : Inputs}
    {c d e : TapeCfg R B L} {t s : ℕ}
    (h : P.Exec inp c t d) (k : P.Exec inp d s e) : P.Exec inp c (t+s) e := by
  induction h with
  | refl c => simpa using k
  | step active next tail ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Exec.step active next (ih k)

 theorem step_relabel (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (f : Fin L → Fin K) (inp : Inputs) (c : TapeCfg R B L)
    (hc : Q.code (f c.pc) = TapeInstr.relabel f (P.code c.pc)) :
    Q.step inp (c.mapPC f) = (P.step inp c).mapPC f := by
  simp only [step, TapeCfg.mapPC, hc]
  cases h : P.code c.pc <;> simp only [TapeInstr.relabel]
  all_goals try rfl
  split <;> simp_all

/-- Relabeling preserves active traces even when the embedding redirects halt
instructions. Only labels actually executed before halt are constrained. -/
 theorem Exec.relabel {P : TapeProgram R B L} {Q : TapeProgram R B K}
    {inp : Inputs} {c d : TapeCfg R B L} {t : ℕ} (h : P.Exec inp c t d)
    (f : Fin L → Fin K)
    (hc : ∀ j, P.code j ≠ .halt → Q.code (f j) = TapeInstr.relabel f (P.code j)) :
    Q.Exec inp (c.mapPC f) t (d.mapPC f) := by
  induction h with
  | refl c => exact Exec.refl _
  | @step c d e t active next tail ih =>
    have hcode := hc c.pc active
    apply Exec.step (d := d.mapPC f)
    · change Q.code (f c.pc) ≠ .halt
      rw [hcode]
      intro h
      exact active ((TapeInstr.relabel_eq_halt f (P.code c.pc)).mp h)
    · rw [step_relabel P Q f inp c hcode, next]
    · exact ih

/-- A proved source routine immediately supplies a canonical machine bound. -/
 theorem Stops.compile {P : TapeProgram R B L} {inp : Inputs} {t : ℕ}
    {d : TapeCfg R B L} (h : P.Stops inp P.init t d) (O : Set (List Bool)) :
    (TapeCompiler.compile P).HaltsWith O inp (1+2*t) (bitsSym d.output) := by
  have hr : P.run inp t = d := h.exec.iterate
  simpa [hr] using TapeCompiler.compile_halts P O inp t (by simpa [hr] using h.halted)

/-- Constructive inclusions into the disjoint union of two finite code tables. -/
def leftLabel (K : ℕ) (j : Fin L) : Fin (L+K) := finSumFinEquiv (.inl j)
def rightLabel (L : ℕ) (j : Fin K) : Fin (L+K) := finSumFinEquiv (.inr j)

/-- Finite program sequencing. Each halt in the first fragment becomes one jump
into the second fragment; all other instructions are copied with relabeled targets. -/
def seq (P : TapeProgram R B L) (Q : TapeProgram R B K) : TapeProgram R B (L+K) where
  entry := leftLabel K P.entry
  code := fun j => match finSumFinEquiv.symm j with
    | .inl i => match P.code i with
      | .halt => .jump (rightLabel L Q.entry)
      | a => a.relabel (leftLabel K)
    | .inr i => (Q.code i).relabel (rightLabel L)

 theorem seq_code_left_active (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (j : Fin L) (hj : P.code j ≠ .halt) :
    (TapeProgram.seq P Q).code (leftLabel K j) = (P.code j).relabel (leftLabel K) := by
  simp only [seq, leftLabel, Equiv.symm_apply_apply]

 theorem seq_code_left_halt (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (j : Fin L) (hj : P.code j = .halt) :
    (TapeProgram.seq P Q).code (leftLabel K j) = .jump (rightLabel L Q.entry) := by
  simp [seq, leftLabel, hj]

 theorem seq_code_right (P : TapeProgram R B L) (Q : TapeProgram R B K) (j : Fin K) :
    (TapeProgram.seq P Q).code (rightLabel L j) = (Q.code j).relabel (rightLabel L) := by
  simp [seq, rightLabel]

/-- Exact compositional source cost: first routine, one linking jump, second routine. -/
 theorem Stops.seq {P : TapeProgram R B L} {Q : TapeProgram R B K} {inp : Inputs}
    {c d : TapeCfg R B L} {e : TapeCfg R B K} {t s : ℕ}
    (hp : P.Stops inp c t d) (hq : Q.Stops inp (d.store.toCfg Q.entry) s e) :
    (TapeProgram.seq P Q).Stops inp (c.mapPC (leftLabel K)) (t+1+s) (e.mapPC (rightLabel L)) := by
  have hleft := hp.exec.relabel (leftLabel K) (seq_code_left_active P Q)
  have hright := hq.exec.relabel (rightLabel L) (fun j _ => seq_code_right P Q j)
  have hbridge : (TapeProgram.seq P Q).Exec inp (d.mapPC (leftLabel K)) 1
      ((d.store.toCfg Q.entry).mapPC (rightLabel L)) := by
    apply Exec.one
    · change (TapeProgram.seq P Q).code (leftLabel K d.pc) ≠ .halt
      rw [seq_code_left_halt P Q d.pc hp.halted]
      simp
    · simp only [step, TapeCfg.mapPC]
      rw [seq_code_left_halt P Q d.pc hp.halted]
  constructor
  · exact (hleft.trans hbridge).trans hright
  · change (TapeProgram.seq P Q).code (rightLabel L e.pc) = .halt
    rw [seq_code_right, hq.halted]
    rfl

/-- A syntactic sufficient condition for an instruction to preserve a register. -/
def preservesRegister (r : Fin R) : TapeInstr R B L → Prop
  | .inc s _ => s ≠ r
  | .dec s _ _ => s ≠ r
  | _ => True

/-- A loop counter is fresh when the body never increments or decrements it. -/
def Fresh (P : TapeProgram R B L) (r : Fin R) : Prop :=
  ∀ j, preservesRegister r (P.code j)

 theorem step_reg_of_fresh (P : TapeProgram R B L) (r : Fin R) (hf : P.Fresh r)
    (inp : Inputs) (c : TapeCfg R B L) : (P.step inp c).reg r = c.reg r := by
  have h := hf c.pc
  cases hc : P.code c.pc <;> simp only [hc, preservesRegister] at h
  all_goals simp only [step, hc]
  all_goals try rfl
  case inc s j => simp [Function.update_of_ne (Ne.symm h)]
  case dec s z p => split <;> simp [Function.update_of_ne (Ne.symm h)]

 theorem Exec.reg_of_fresh {P : TapeProgram R B L} {r : Fin R}
    {inp : Inputs} {c d : TapeCfg R B L} {t : ℕ} (h : P.Exec inp c t d) (hf : P.Fresh r) :
    d.reg r = c.reg r := by
  induction h with
  | refl c => rfl
  | step active next tail ih =>
    rw [ih, ← next]
    exact step_reg_of_fresh P r hf inp _

/-- The body occupies the first L labels, followed by a decrement/test header and halt exit. -/
def loopHeader (L : ℕ) : Fin (L+2) := rightLabel L (0 : Fin 2)
def loopExit (L : ℕ) : Fin (L+2) := rightLabel L (1 : Fin 2)

def countedLoop (P : TapeProgram R B L) (r : Fin R) : TapeProgram R B (L+2) where
  entry := loopHeader L
  code := fun j => match finSumFinEquiv.symm j with
    | .inl i => match P.code i with
      | .halt => .jump (loopHeader L)
      | a => a.relabel (leftLabel 2)
    | .inr i => if i = 0 then .dec r (loopExit L) (leftLabel 2 P.entry) else .halt

 theorem loop_code_body_active (P : TapeProgram R B L) (r : Fin R)
    (j : Fin L) (hj : P.code j ≠ .halt) :
    (countedLoop P r).code (leftLabel 2 j) = (P.code j).relabel (leftLabel 2) := by
  simp only [countedLoop, leftLabel, Equiv.symm_apply_apply]

 theorem loop_code_body_halt (P : TapeProgram R B L) (r : Fin R)
    (j : Fin L) (hj : P.code j = .halt) :
    (countedLoop P r).code (leftLabel 2 j) = .jump (loopHeader L) := by
  simp [countedLoop, leftLabel, hj]

 theorem loop_code_header (P : TapeProgram R B L) (r : Fin R) :
    (countedLoop P r).code (loopHeader L) = .dec r (loopExit L) (leftLabel 2 P.entry) := by
  simp [countedLoop, loopHeader, rightLabel]

 theorem loop_code_exit (P : TapeProgram R B L) (r : Fin R) :
    (countedLoop P r).code (loopExit L) = .halt := by
  simp [countedLoop, loopExit, rightLabel]

/-- Store after the loop's positive decrement instruction. -/
abbrev decStore (r : Fin R) (d : TapeStore R B) : TapeStore R B :=
  { d with reg := Function.update d.reg r (d.reg r - 1) }

 theorem loop_zero (P : TapeProgram R B L) (r : Fin R) (inp : Inputs)
    (d : TapeStore R B) (hd : d.reg r = 0) :
    (countedLoop P r).Stops inp (d.toCfg (loopHeader L)) 1 (d.toCfg (loopExit L)) := by
  constructor
  · apply Exec.one
    · change (countedLoop P r).code (loopHeader L) ≠ .halt
      rw [loop_code_header]
      simp
    · simp only [step, TapeStore.toCfg, loop_code_header, hd, ite_true]
  · exact loop_code_exit P r

 theorem loop_positive_header (P : TapeProgram R B L) (r : Fin R) (inp : Inputs)
    (d : TapeStore R B) (hd : d.reg r ≠ 0) :
    (countedLoop P r).Exec inp (d.toCfg (loopHeader L)) 1
      (((decStore r d).toCfg P.entry).mapPC (leftLabel 2)) := by
  apply Exec.one
  · change (countedLoop P r).code (loopHeader L) ≠ .halt
    rw [loop_code_header]
    simp
  · simp only [step, TapeStore.toCfg, loop_code_header, if_neg hd]

 theorem loop_body_return (P : TapeProgram R B L) (r : Fin R) (inp : Inputs)
    (c : TapeCfg R B L) (hc : P.halted c) :
    (countedLoop P r).Exec inp (c.mapPC (leftLabel 2)) 1 (c.store.toCfg (loopHeader L)) := by
  apply Exec.one
  · change (countedLoop P r).code (leftLabel 2 c.pc) ≠ .halt
    rw [loop_code_body_halt P r c.pc hc]
    simp
  · simp only [step, TapeCfg.mapPC]
    rw [loop_code_body_halt P r c.pc hc]

/-- A modular loop rule with an explicit source-step bound. The body is an actual
finite program, and `hbody` consists of checked finite executions of that program.
The indexed invariant describes the payload after each remaining iteration. -/
 theorem countedLoop_stops (P : TapeProgram R B L) (r : Fin R) (hf : P.Fresh r)
    (inp : Inputs) (C : ℕ) (Inv : ℕ → TapeStore R B → Prop)
    (hbody : ∀ n d, d.reg r = n+1 → Inv (n+1) d →
      ∃ t c, t ≤ C ∧ P.Stops inp ((decStore r d).toCfg P.entry) t c ∧ Inv n c.store)
    (n : ℕ) (d : TapeStore R B) (hd : d.reg r = n) (hi : Inv n d) :
    ∃ t e, t ≤ n*(C+2)+1 ∧
      (countedLoop P r).Stops inp (d.toCfg (loopHeader L)) t (e.toCfg (loopExit L)) ∧
      Inv 0 e ∧ e.reg r = 0 := by
  induction n generalizing d with
  | zero =>
    exact ⟨1, d, by omega, loop_zero P r inp d hd, hi, hd⟩
  | succ n ih =>
    obtain ⟨s, c, hs, hstop, hInv⟩ := hbody n d hd hi
    have hc : c.reg r = n := by
      have hh := hstop.exec.reg_of_fresh hf
      simpa [TapeStore.toCfg, decStore, hd] using hh
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
end TapeProgram
end ExpandingCodes.Computation
