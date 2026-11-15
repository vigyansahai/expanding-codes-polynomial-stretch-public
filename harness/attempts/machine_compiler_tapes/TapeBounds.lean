import ExpandingCodes.Computation.TapeProgram

set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

/-- Canonical finite-list tape storage grows only as far as the written cell. -/
 theorem tape_write_length (l : List Sym) (h : ℕ) (a : Sym) :
    (Machine.writeAt l h a).length = max l.length (h+1) := by
  simp only [Machine.writeAt, List.length_set, List.length_append, List.length_replicate]
  omega

 theorem tape_move_le (move : Move) (h : ℕ) : Machine.moveHead move h ≤ h+1 := by
  cases move <;> simp [Machine.moveHead] <;> omega

namespace TapeProgram
variable {R B L : ℕ}

/-- A physical buffer bound, counting cells rather than a numerical encoding of
an entire array. Each buffer head and its stored list length are bounded by n. -/
def BufferBounded (c : TapeCfg R B L) (n : ℕ) : Prop :=
  ∀ b, c.bufferHead b ≤ n ∧ (c.bufferTape b).length ≤ n

 theorem bufferBounded_mono {c : TapeCfg R B L} {n m : ℕ}
    (h : BufferBounded c n) (hnm : n ≤ m) : BufferBounded c m :=
  fun b => ⟨(h b).1.trans hnm, (h b).2.trans hnm⟩

 theorem bufferBounded_step (P : TapeProgram R B L) (inp : Inputs)
    (c : TapeCfg R B L) (n : ℕ) (h : BufferBounded c n) :
    BufferBounded (P.step inp c) (n+1) := by
  have hw : BufferBounded c (n+1) := bufferBounded_mono h (Nat.le_succ n)
  cases hc : P.code c.pc with
  | halt => simpa only [step, hc] using hw
  | jump j => simpa only [step, hc, BufferBounded] using hw
  | inc r j => simpa only [step, hc, BufferBounded] using hw
  | dec r z p =>
    simp only [step, hc]
    split <;> exact hw
  | emit bit j => simpa only [step, hc, BufferBounded] using hw
  | read r next => simpa only [step, hc, BufferBounded] using hw
  | buffer b action =>
    intro i
    simp only [step, hc]
    by_cases hi : i = b
    · subst i
      simp only [Function.update_self]
      constructor
      · exact (tape_move_le _ _).trans (Nat.succ_le_succ (h b).1)
      · rw [tape_write_length]
        exact max_le ((h b).2.trans (Nat.le_succ n)) (Nat.succ_le_succ (h b).1)
    · simpa only [Function.update_of_ne hi] using hw i

/-- After t source cell operations, every explicit buffer occupies at most t
stored cells and its head is at position at most t. -/
 theorem bufferBounded_run (P : TapeProgram R B L) (inp : Inputs) (t : ℕ) :
    BufferBounded (P.run inp t) t := by
  induction t with
  | zero => intro b; simp [run, init]
  | succ t ih =>
    rw [run_succ]
    exact bufferBounded_step P inp _ t ih

#print axioms bufferBounded_run
end TapeProgram
end ExpandingCodes.Computation
