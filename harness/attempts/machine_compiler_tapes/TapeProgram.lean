import Definitions.Def_NKtLB_Machine

set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

/-- Finite unary-counter programs with explicit symbol work buffers. Each buffer
operation inspects only the cell under its head; there are no whole-array or arithmetic oracles. -/
inductive TapeInstr (registers buffers labels : ℕ) where
  | halt
  | jump (next : Fin labels)
  | inc (reg : Fin registers) (next : Fin labels)
  | dec (reg : Fin registers) (zero positive : Fin labels)
  | emit (bit : Bool) (next : Fin labels)
  | read (tape : Fin 4) (next : Sym → Fin labels)
  /-- A four-entry table. One scanned cell determines one written symbol, one
  unit head movement, and one finite next label; the rest of the tape is inaccessible. -/
  | buffer (tape : Fin buffers) (action : Sym → Sym × Move × Fin labels)

structure TapeProgram (registers buffers labels : ℕ) where
  entry : Fin labels
  code : Fin labels → TapeInstr registers buffers labels

structure TapeCfg (registers buffers labels : ℕ) where
  pc : Fin labels
  reg : Fin registers → ℕ
  roHead : Fin 4 → ℕ
  output : List Bool
  bufferTape : Fin buffers → List Sym
  bufferHead : Fin buffers → ℕ

namespace TapeProgram
variable {R B L : ℕ}

def init (P : TapeProgram R B L) : TapeCfg R B L :=
  ⟨P.entry, fun _ => 0, fun _ => 0, [], fun _ => [], fun _ => 0⟩

def halted (P : TapeProgram R B L) (c : TapeCfg R B L) : Prop :=
  P.code c.pc = .halt

instance (P : TapeProgram R B L) (c : TapeCfg R B L) : Decidable (P.halted c) := by
  unfold halted
  cases P.code c.pc
  · exact isTrue rfl
  all_goals exact isFalse (by intro h; cases h)

/-- Exact source semantics. Buffer contents are explicit finite symbol lists,
not arrays packed into a unary natural register. -/
def step (P : TapeProgram R B L) (inp : Inputs) (c : TapeCfg R B L) : TapeCfg R B L :=
  match P.code c.pc with
  | .halt => c
  | .jump j => { c with pc := j }
  | .inc r j => { c with pc := j, reg := Function.update c.reg r (c.reg r + 1) }
  | .dec r z p =>
    if c.reg r = 0 then { c with pc := z }
    else { c with pc := p, reg := Function.update c.reg r (c.reg r - 1) }
  | .emit b j => { c with pc := j, output := (c.output ++ [b]) }
  | .read r next =>
    { c with
      pc := next (Machine.readRO (inp.get r) (c.roHead r))
      roHead := Function.update c.roHead r (c.roHead r + 1) }
  | .buffer b action =>
    let a := action ((c.bufferTape b).getD (c.bufferHead b) .blank)
    { c with
      pc := a.2.2
      bufferTape := Function.update c.bufferTape b
        (Machine.writeAt (c.bufferTape b) (c.bufferHead b) a.1)
      bufferHead := Function.update c.bufferHead b (Machine.moveHead a.2.1 (c.bufferHead b)) }

/-- Number of target transitions used by the compiler for a single instruction.
Halting configurations are already represented by the target's halting state. -/
def cost (P : TapeProgram R B L) (c : TapeCfg R B L) : ℕ :=
  match P.code c.pc with
  | .halt => 0
  | .inc _ _ => 2
  | _ => 1

def run (P : TapeProgram R B L) (inp : Inputs) (t : ℕ) : TapeCfg R B L :=
  (P.step inp)^[t] P.init

def time (P : TapeProgram R B L) (inp : Inputs) : ℕ → ℕ
  | 0 => 0
  | t+1 => P.time inp t + P.cost (P.run inp t)

 theorem cost_le_two (P : TapeProgram R B L) (c : TapeCfg R B L) : P.cost c ≤ 2 := by
  unfold cost
  cases P.code c.pc <;> simp

 theorem time_le (P : TapeProgram R B L) (inp : Inputs) (t : ℕ) :
    P.time inp t ≤ 2*t := by
  induction t with
  | zero => simp [time]
  | succ t ih =>
    have hc := P.cost_le_two (P.run inp t)
    simp only [time]
    omega

 theorem run_succ (P : TapeProgram R B L) (inp : Inputs) (t : ℕ) :
    P.run inp (t+1) = P.step inp (P.run inp t) :=
  Function.iterate_succ_apply' _ _ _

 theorem step_halted (P : TapeProgram R B L) (inp : Inputs) (c : TapeCfg R B L)
    (h : P.halted c) : P.step inp c = c := by
  change P.code c.pc = .halt at h
  simp [step, h]

#print axioms time_le
end TapeProgram
end ExpandingCodes.Computation
