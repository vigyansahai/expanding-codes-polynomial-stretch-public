import Definitions.Def_NKtLB_Machine

set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

/-- A deliberately small instruction language. Every branch has a finite target;
there is no instruction for evaluating an arbitrary function of register values. -/
inductive CounterInstr (registers labels : ℕ) where
  | halt
  | jump (next : Fin labels)
  | inc (reg : Fin registers) (next : Fin labels)
  | dec (reg : Fin registers) (zero positive : Fin labels)
  | emit (bit : Bool) (next : Fin labels)
  | read (tape : Fin 4) (next : Sym → Fin labels)

structure CounterProgram (registers labels : ℕ) where
  entry : Fin labels
  code : Fin labels → CounterInstr registers labels

structure CounterCfg (registers labels : ℕ) where
  pc : Fin labels
  reg : Fin registers → ℕ
  roHead : Fin 4 → ℕ
  output : List Bool

namespace CounterProgram
variable {R L : ℕ}

def init (P : CounterProgram R L) : CounterCfg R L :=
  ⟨P.entry, fun _ => 0, fun _ => 0, []⟩

def halted (P : CounterProgram R L) (c : CounterCfg R L) : Prop :=
  P.code c.pc = .halt

instance (P : CounterProgram R L) (c : CounterCfg R L) : Decidable (P.halted c) := by
  unfold halted
  cases P.code c.pc
  · exact isTrue rfl
  all_goals exact isFalse (by intro h; cases h)

/-- Exact register semantics, including the canonical read-only tape convention. -/
def step (P : CounterProgram R L) (inp : Inputs) (c : CounterCfg R L) : CounterCfg R L :=
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

/-- Number of target transitions used by the compiler for a single instruction.
Halting configurations are already represented by the target's halting state. -/
def cost (P : CounterProgram R L) (c : CounterCfg R L) : ℕ :=
  match P.code c.pc with
  | .halt => 0
  | .inc _ _ => 2
  | _ => 1

def run (P : CounterProgram R L) (inp : Inputs) (t : ℕ) : CounterCfg R L :=
  (P.step inp)^[t] P.init

def time (P : CounterProgram R L) (inp : Inputs) : ℕ → ℕ
  | 0 => 0
  | t+1 => P.time inp t + P.cost (P.run inp t)

 theorem cost_le_two (P : CounterProgram R L) (c : CounterCfg R L) : P.cost c ≤ 2 := by
  unfold cost
  cases P.code c.pc <;> simp

 theorem time_le (P : CounterProgram R L) (inp : Inputs) (t : ℕ) :
    P.time inp t ≤ 2*t := by
  induction t with
  | zero => simp [time]
  | succ t ih =>
    have hc := P.cost_le_two (P.run inp t)
    simp only [time]
    omega

 theorem run_succ (P : CounterProgram R L) (inp : Inputs) (t : ℕ) :
    P.run inp (t+1) = P.step inp (P.run inp t) :=
  Function.iterate_succ_apply' _ _ _

 theorem step_halted (P : CounterProgram R L) (inp : Inputs) (c : CounterCfg R L)
    (h : P.halted c) : P.step inp c = c := by
  change P.code c.pc = .halt at h
  simp [step, h]

#print axioms time_le
end CounterProgram
end ExpandingCodes.Computation
