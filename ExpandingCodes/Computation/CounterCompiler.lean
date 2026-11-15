import ExpandingCodes.Computation.CounterMachine
import ExpandingCodes.Computation.CounterTape
import ExpandingCodes.Computation.Basic

set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

/-- Two banks of instruction labels (ordinary and increment completion), plus
start, halt, and an unreachable oracle-query state. -/
abbrev CounterControl (L : ℕ) := (Fin L ⊕ Fin L) ⊕ Fin 3

namespace CounterCompiler
variable {R L : ℕ}

def controlEquiv (L : ℕ) : CounterControl L ≃ Fin (L+L+3) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 3))).trans finSumFinEquiv

def startControl : CounterControl L := .inr 0
def haltControl : CounterControl L := .inr 1
def queryControl : CounterControl L := .inr 2
def normal (j : Fin L) : CounterControl L := .inl (.inl j)
def finish (j : Fin L) : CounterControl L := .inl (.inr j)

def workIdx (r : Fin R) : Fin (R+2) := ⟨r.val, by omega⟩
def outIdx (R : ℕ) : Fin (R+2) := ⟨R, by omega⟩

def target (P : CounterProgram R L) (j : Fin L) : CounterControl L :=
  match P.code j with
  | .halt => haltControl
  | _ => normal j

def idle (rw : Fin (R+2) → Sym) : Fin (R+2) → Sym × Move :=
  fun k => (rw k, .stay)

def roIdle : Fin 4 → Move := fun _ => .stay

/-- A literal finite transition table over the four scanned symbols. The
`next : Sym → Fin L` field of a read instruction is just a four-entry branch table. -/
def transition (P : CounterProgram R L) (q : CounterControl L)
    (ro : Fin 4 → Sym) (rw : Fin (R+2) → Sym) :
    CounterControl L × (Fin 4 → Move) × (Fin (R+2) → Sym × Move) :=
  match q with
  | .inr s =>
    if s = 0 then
      (target P P.entry, roIdle, fun k =>
        if k.val < R then (.bot, .stay) else (rw k, .stay))
    else (haltControl, roIdle, idle rw)
  | .inl (.inr j) =>
    match P.code j with
    | .inc r next => (target P next, roIdle,
        Function.update (idle rw) (workIdx r) (.one, .stay))
    | _ => (haltControl, roIdle, idle rw)
  | .inl (.inl j) =>
    match P.code j with
    | .halt => (haltControl, roIdle, idle rw)
    | .jump next => (target P next, roIdle, idle rw)
    | .inc r _ => (finish j, roIdle,
        Function.update (idle rw) (workIdx r) (rw (workIdx r), .right))
    | .dec r zero positive =>
      if rw (workIdx r) = .bot then (target P zero, roIdle, idle rw)
      else (target P positive, roIdle,
        Function.update (idle rw) (workIdx r) (.blank, .left))
    | .emit b next => (target P next, roIdle,
        Function.update (idle rw) (outIdx R) (Sym.ofBool b, .right))
    | .read r next =>
      (target P (next (ro r)), Function.update roIdle r .right, idle rw)

/-- Compiles every finite counter program to the exact canonical NKtLB machine.
No oracle, arithmetic, or unbounded memory action occurs in its transition table. -/
abbrev compile (P : CounterProgram R L) : Machine where
  nStates := L+L+3
  start := controlEquiv L startControl
  halt := controlEquiv L haltControl
  query := controlEquiv L queryControl
  qyes := controlEquiv L haltControl
  qno := controlEquiv L haltControl
  works := R
  δ := fun q ro rw =>
    let a := transition P ((controlEquiv L).symm q) ro rw
    (controlEquiv L a.1, a.2)

 theorem target_ne_query (P : CounterProgram R L) (j : Fin L) :
    target P j ≠ queryControl := by
  unfold target
  cases P.code j <;> simp [haltControl, queryControl, normal]

 theorem transition_ne_query (P : CounterProgram R L) (q : CounterControl L)
    (ro : Fin 4 → Sym) (rw : Fin (R+2) → Sym) :
    (transition P q ro rw).1 ≠ queryControl := by
  rcases q with (j | j) | s
  · cases h : P.code j <;> simp only [transition, h] <;> try split_ifs
    all_goals first | exact target_ne_query P _ | simp [finish, haltControl, queryControl]
  · cases h : P.code j <;> simp only [transition, h]
    all_goals first | exact target_ne_query P _ | simp [haltControl, queryControl]
  · simp only [transition]
    split <;> first | exact target_ne_query P _ | simp [haltControl, queryControl]

 theorem compile_start_ne_query (P : CounterProgram R L) :
    (compile P).start ≠ (compile P).query := by
  simp [compile, startControl, queryControl]

 theorem compile_delta_ne_query (P : CounterProgram R L)
    (q : Fin (compile P).nStates) (ro : Fin 4 → Sym)
    (rw : Fin ((compile P).works+2) → Sym) :
    ((compile P).δ q ro rw).1 ≠ (compile P).query := by
  change controlEquiv L _ ≠ controlEquiv L queryControl
  exact (controlEquiv L).injective.ne (transition_ne_query P _ ro rw)

/-- The compiled machine never reaches the query state, for any oracle and inputs. -/
 theorem compile_run_ne_query (P : CounterProgram R L) (O : Set (List Bool))
    (inp : Inputs) (t : ℕ) :
    ((compile P).run O inp t).state ≠ (compile P).query := by
  induction t with
  | zero => exact compile_start_ne_query P
  | succ t ih =>
    rw [Machine.run_succ]
    unfold Machine.step
    split
    · exact ih
    · simp only [if_neg ih]
      exact compile_delta_ne_query P _ _ _

/-- The exact relation required at instruction boundaries. Work tapes use the
proved unary invariant; the output is represented extensionally by its finite bit word. -/
structure Represents (P : CounterProgram R L) (c : CounterCfg R L)
    (m : Machine.Cfg (compile P)) : Prop where
  state : m.state = controlEquiv L (target P c.pc)
  roHead : m.roHead = c.roHead
  workHead : ∀ r, m.rwHead (workIdx r) = c.reg r
  workTape : ∀ r, TapeRep (m.rwTape (workIdx r)) (unary (c.reg r))
  outHead : m.rwHead (outIdx R) = c.output.length
  outTape : TapeRep (m.rwTape (outIdx R)) (fun k => (bitsSym c.output).getD k .blank)

 theorem target_eq_halt (P : CounterProgram R L) (j : Fin L) :
    target P j = haltControl ↔ P.code j = .halt := by
  unfold target
  cases P.code j <;> simp [haltControl, normal]

 theorem Represents.halt {P : CounterProgram R L} {c : CounterCfg R L}
    {m : Machine.Cfg (compile P)} (h : Represents P c m) (hc : P.halted c) :
    m.state = (compile P).halt := by
  rw [h.state, (target_eq_halt P c.pc).mpr hc]

/-- A finite local proof obligation: simulate each of the six instruction forms,
with the two-action increment distinguished from the one-action instructions. -/
def LocalSimulation (P : CounterProgram R L) : Prop :=
  ∀ (O : Set (List Bool)) (inp : Inputs) (c : CounterCfg R L)
    (m : Machine.Cfg (compile P)),
    Represents P c m →
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m)

 theorem initial_represents (P : CounterProgram R L) (O : Set (List Bool)) (inp : Inputs) :
    Represents P P.init ((compile P).run O inp 1) := by
  have hs : (compile P).start ≠ (compile P).halt := by
    simp [compile, startControl, haltControl]
  have hq := compile_start_ne_query P
  have he : ((compile P).run O inp 1) =
      { state := controlEquiv L (target P P.entry)
        roHead := fun _ => 0
        rwTape := fun k => if k.val < R then [.bot] else [.blank]
        rwHead := fun _ => 0 } := by
    simp [Machine.run, Machine.init, Machine.step, hs, hq, compile, transition,
      startControl, haltControl, queryControl, roIdle, Machine.moveHead, Machine.writeAt]
    constructor <;> funext k <;> split_ifs <;> rfl
  rw [he]
  constructor
  · rfl
  · rfl
  · intro r; rfl
  · intro r k
    have hlt : r.val < R := r.isLt
    simp [workIdx, CounterProgram.init, unary, hlt]
    by_cases hk : k = 0 <;> simp [hk]
  · rfl
  · intro k
    simp [outIdx, CounterProgram.init, bitsSym, List.getD_eq_getElem?_getD]

/-- Ordinary target transitions expose only canonical head moves and `writeAt`. -/
 theorem step_normal (P : CounterProgram R L) (O : Set (List Bool)) (inp : Inputs)
    (j : Fin L) (m : Machine.Cfg (compile P))
    (hm : m.state = controlEquiv L (normal j)) :
    (compile P).step O inp m =
      let a := transition P (normal j)
        (fun i => Machine.readRO (inp.get i) (m.roHead i))
        (fun k => (m.rwTape k).getD (m.rwHead k) .blank)
      { state := controlEquiv L a.1
        roHead := fun i => Machine.moveHead (a.2.1 i) (m.roHead i)
        rwTape := fun k => Machine.writeAt (m.rwTape k) (m.rwHead k) (a.2.2 k).1
        rwHead := fun k => Machine.moveHead (a.2.2 k).2 (m.rwHead k) } := by
  have hh : m.state ≠ (compile P).halt := by
    rw [hm]; simp [compile, normal, haltControl]
  have hq : m.state ≠ (compile P).query := by
    rw [hm]; simp [compile, normal, queryControl]
  simp only [Machine.step, if_neg hh, if_neg hq]
  simp only [compile, hm, Equiv.symm_apply_apply]

 theorem local_halt (P : CounterProgram R L) (O : Set (List Bool)) (inp : Inputs)
    (c : CounterCfg R L) (m : Machine.Cfg (compile P))
    (hc : P.halted c) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  rw [P.step_halted inp c hc]
  change P.code c.pc = .halt at hc
  simpa [CounterProgram.cost, hc] using hr

 theorem local_jump (P : CounterProgram R L) (O : Set (List Bool)) (inp : Inputs)
    (c : CounterCfg R L) (m : Machine.Cfg (compile P)) (j : Fin L)
    (hc : P.code c.pc = .jump j) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  simp only [CounterProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, CounterProgram.step]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro r
    simpa [idle, Machine.moveHead] using hr.workHead r
  · intro r k
    simp only [idle, getD_writeAt]
    rw [hr.workTape r k, hr.workTape r (m.rwHead (workIdx r))]
    split_ifs with hk
    · exact congrArg (unary (c.reg r)) hk.symm
    · rfl
  · simpa [idle, Machine.moveHead] using hr.outHead
  · intro k
    simp only [idle, getD_writeAt]
    rw [hr.outTape k, hr.outTape (m.rwHead (outIdx R))]
    split_ifs with hk
    · exact congrArg (fun z => (bitsSym c.output).getD z .blank) hk.symm
    · rfl

 theorem local_read (P : CounterProgram R L) (O : Set (List Bool)) (inp : Inputs)
    (c : CounterCfg R L) (m : Machine.Cfg (compile P)) (r : Fin 4)
    (next : Sym → Fin L) (hc : P.code c.pc = .read r next) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  simp only [CounterProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, CounterProgram.step]
  constructor
  · simp [hr.roHead]
  · funext i
    by_cases hi : i = r <;> simp [hi, roIdle, Machine.moveHead, hr.roHead]
  · intro i
    simpa [idle, Machine.moveHead] using hr.workHead i
  · intro i k
    simp only [idle, getD_writeAt]
    rw [hr.workTape i k, hr.workTape i (m.rwHead (workIdx i))]
    split_ifs with hk
    · exact congrArg (unary (c.reg i)) hk.symm
    · rfl
  · simpa [idle, Machine.moveHead] using hr.outHead
  · intro k
    simp only [idle, getD_writeAt]
    rw [hr.outTape k, hr.outTape (m.rwHead (outIdx R))]
    split_ifs with hk
    · exact congrArg (fun z => (bitsSym c.output).getD z .blank) hk.symm
    · rfl

 theorem workIdx_ne_outIdx (r : Fin R) : workIdx r ≠ outIdx R := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [workIdx, outIdx] at hv
  omega

 theorem outIdx_ne_workIdx (r : Fin R) : outIdx R ≠ workIdx r :=
  Ne.symm (workIdx_ne_outIdx r)

 theorem getD_append_singleton (l : List Sym) (a : Sym) (k : ℕ) :
    (l ++ [a]).getD k .blank = if k = l.length then a else l.getD k .blank := by
  by_cases hk : k < l.length
  · rw [List.getD_append _ _ _ _ hk, if_neg (by omega)]
  · by_cases he : k = l.length
    · subst k
      rw [List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    · rw [List.getD_eq_default (l ++ [a]) .blank (by simp; omega), if_neg he,
        List.getD_eq_default l .blank (by omega)]

 theorem local_emit (P : CounterProgram R L) (O : Set (List Bool)) (inp : Inputs)
    (c : CounterCfg R L) (m : Machine.Cfg (compile P)) (b : Bool) (j : Fin L)
    (hc : P.code c.pc = .emit b j) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  simp only [CounterProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, CounterProgram.step]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro r
    simpa [Function.update_of_ne (workIdx_ne_outIdx r), idle, Machine.moveHead]
      using hr.workHead r
  · intro r k
    simp only [Function.update_of_ne (workIdx_ne_outIdx r), idle, getD_writeAt]
    rw [hr.workTape r k, hr.workTape r (m.rwHead (workIdx r))]
    split_ifs with hk
    · exact congrArg (unary (c.reg r)) hk.symm
    · rfl
  · simp [Function.update_self, Machine.moveHead, hr.outHead]
  · intro k
    simp only [Function.update_self, getD_writeAt, hr.outHead]
    rw [hr.outTape k]
    simp only [bitsSym, List.map_append, List.map_cons, List.map_nil]
    rw [getD_append_singleton]
    simp [List.length_map]

@[simp] theorem workIdx_eq_iff (r s : Fin R) : workIdx r = workIdx s ↔ r = s := by
  simp [workIdx, Fin.ext_iff]

 theorem local_dec_zero (P : CounterProgram R L) (O : Set (List Bool)) (inp : Inputs)
    (c : CounterCfg R L) (m : Machine.Cfg (compile P)) (r : Fin R) (z p : Fin L)
    (hc : P.code c.pc = .dec r z p) (hr : Represents P c m) (hz : c.reg r = 0) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  have hscan : (m.rwTape (workIdx r)).getD (m.rwHead (workIdx r)) .blank = .bot := by
    rw [hr.workHead r, hr.workTape r, hz]
    rfl
  simp only [CounterProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, CounterProgram.step, hscan, hz, ite_true, eq_self_iff_true]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro i
    simpa [idle, Machine.moveHead] using hr.workHead i
  · intro i k
    simp only [idle, getD_writeAt]
    rw [hr.workTape i k, hr.workTape i (m.rwHead (workIdx i))]
    split_ifs with hk
    · exact congrArg (unary (c.reg i)) hk.symm
    · rfl
  · simpa [idle, Machine.moveHead] using hr.outHead
  · intro k
    simp only [idle, getD_writeAt]
    rw [hr.outTape k, hr.outTape (m.rwHead (outIdx R))]
    split_ifs with hk
    · exact congrArg (fun z => (bitsSym c.output).getD z .blank) hk.symm
    · rfl

 theorem local_dec_positive (P : CounterProgram R L) (O : Set (List Bool)) (inp : Inputs)
    (c : CounterCfg R L) (m : Machine.Cfg (compile P)) (r : Fin R) (z p : Fin L) (n : ℕ)
    (hc : P.code c.pc = .dec r z p) (hr : Represents P c m) (hn : c.reg r = n+1) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  have hscan : (m.rwTape (workIdx r)).getD (m.rwHead (workIdx r)) .blank = .one := by
    rw [hr.workHead r, hr.workTape r, hn]
    simp
  simp only [CounterProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, CounterProgram.step, hscan, hn,
    reduceCtorEq, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro i
    by_cases hi : i = r
    · subst i
      simp [Function.update_self, Machine.moveHead, hr.workHead, hn]
    · have hi' : workIdx i ≠ workIdx r := by simpa using hi
      simpa [Function.update_of_ne hi', Function.update_of_ne hi, idle, Machine.moveHead]
        using hr.workHead i
  · intro i
    by_cases hi : i = r
    · subst i
      have ht : TapeRep (m.rwTape (workIdx r)) (unary (n+1)) := by
        simpa [hn] using hr.workTape r
      simpa [Function.update_self, hr.workHead, hn] using (unary_dec_one_step ht).1
    · have hi' : workIdx i ≠ workIdx r := by simpa using hi
      intro k
      simp only [Function.update_of_ne hi', Function.update_of_ne hi, idle, getD_writeAt]
      rw [hr.workTape i k, hr.workTape i (m.rwHead (workIdx i))]
      split_ifs with hk
      · exact congrArg (unary (c.reg i)) hk.symm
      · rfl
  · simpa [Function.update_of_ne (outIdx_ne_workIdx r), idle, Machine.moveHead] using hr.outHead
  · intro k
    simp only [Function.update_of_ne (outIdx_ne_workIdx r), idle, getD_writeAt]
    rw [hr.outTape k, hr.outTape (m.rwHead (outIdx R))]
    split_ifs with hk
    · exact congrArg (fun z => (bitsSym c.output).getD z .blank) hk.symm
    · rfl

 theorem step_finish (P : CounterProgram R L) (O : Set (List Bool)) (inp : Inputs)
    (j : Fin L) (m : Machine.Cfg (compile P))
    (hm : m.state = controlEquiv L (finish j)) :
    (compile P).step O inp m =
      let a := transition P (finish j)
        (fun i => Machine.readRO (inp.get i) (m.roHead i))
        (fun k => (m.rwTape k).getD (m.rwHead k) .blank)
      { state := controlEquiv L a.1
        roHead := fun i => Machine.moveHead (a.2.1 i) (m.roHead i)
        rwTape := fun k => Machine.writeAt (m.rwTape k) (m.rwHead k) (a.2.2 k).1
        rwHead := fun k => Machine.moveHead (a.2.2 k).2 (m.rwHead k) } := by
  have hh : m.state ≠ (compile P).halt := by
    rw [hm]; simp [compile, finish, haltControl]
  have hq : m.state ≠ (compile P).query := by
    rw [hm]; simp [compile, finish, queryControl]
  simp only [Machine.step, if_neg hh, if_neg hq]
  simp only [compile, hm, Equiv.symm_apply_apply]

 theorem tape_write_scanned {l : List Sym} {f : ℕ → Sym}
    (hr : TapeRep l f) (h : ℕ) : TapeRep (Machine.writeAt l h (l.getD h .blank)) f := by
  rw [hr h]
  exact hr.write_same h

 theorem local_inc (P : CounterProgram R L) (O : Set (List Bool)) (inp : Inputs)
    (c : CounterCfg R L) (m : Machine.Cfg (compile P)) (r : Fin R) (j : Fin L)
    (hc : P.code c.pc = .inc r j) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  have hfinish : ((compile P).step O inp m).state = controlEquiv L (finish c.pc) := by
    rw [step_normal P O inp c.pc m hm]
    simp only [normal, transition, hc]
  simp only [CounterProgram.cost, hc]
  change Represents P (P.step inp c) ((compile P).step O inp ((compile P).step O inp m))
  rw [step_finish P O inp c.pc _ hfinish, step_normal P O inp c.pc m hm]
  simp only [normal, finish, transition, hc, CounterProgram.step]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro i
    by_cases hi : i = r
    · subst i
      simp [Function.update_self, Machine.moveHead, hr.workHead]
    · have hi' : workIdx i ≠ workIdx r := by simpa using hi
      simpa [Function.update_of_ne hi', Function.update_of_ne hi, idle, Machine.moveHead]
        using hr.workHead i
  · intro i
    by_cases hi : i = r
    · subst i
      simpa [Function.update_self, idle, Machine.moveHead, hr.workHead]
        using (unary_inc_two_steps (hr.workTape r)).1
    · have hi' : workIdx i ≠ workIdx r := by simpa using hi
      simpa [Function.update_of_ne hi', Function.update_of_ne hi, idle, Machine.moveHead]
        using tape_write_scanned (tape_write_scanned (hr.workTape i) (m.rwHead (workIdx i)))
          (m.rwHead (workIdx i))
  · simpa [Function.update_of_ne (outIdx_ne_workIdx r), idle, Machine.moveHead] using hr.outHead
  · simpa [Function.update_of_ne (outIdx_ne_workIdx r), idle, Machine.moveHead]
      using tape_write_scanned (tape_write_scanned hr.outTape (m.rwHead (outIdx R)))
        (m.rwHead (outIdx R))

 theorem localSimulation (P : CounterProgram R L) : LocalSimulation P := by
  intro O inp c m hr
  cases hc : P.code c.pc with
  | halt => exact local_halt P O inp c m hc hr
  | jump j => exact local_jump P O inp c m j hc hr
  | inc r j => exact local_inc P O inp c m r j hc hr
  | dec r z p =>
    cases hn : c.reg r with
    | zero => exact local_dec_zero P O inp c m r z p hc hr hn
    | succ n => exact local_dec_positive P O inp c m r z p n hc hr hn
  | emit b j => exact local_emit P O inp c m b j hc hr
  | read r next => exact local_read P O inp c m r next hc hr

/-- Once the finite local instruction obligations are supplied, every source
execution is simulated at its exact accumulated microstep time. -/
 theorem run_represents (P : CounterProgram R L) (hs : LocalSimulation P)
    (O : Set (List Bool)) (inp : Inputs) (t : ℕ) :
    Represents P (P.run inp t) ((compile P).run O inp (1 + P.time inp t)) := by
  induction t with
  | zero => simpa [CounterProgram.run, CounterProgram.time] using initial_represents P O inp
  | succ t ih =>
    have h := hs O inp (P.run inp t) _ ih
    rw [CounterProgram.run_succ]
    simpa only [CounterProgram.time, ← Nat.add_assoc, Machine.run_add] using h

/-- Halting/output correctness and the actual target time bound follow from the
finite local simulation obligation, rather than from a polynomial-time oracle. -/
 theorem haltsWith_of_localSimulation (P : CounterProgram R L) (hs : LocalSimulation P)
    (O : Set (List Bool)) (inp : Inputs) (t : ℕ) (hh : P.halted (P.run inp t)) :
    (compile P).HaltsWith O inp (1+2*t) (bitsSym (P.run inp t).output) := by
  have hr := run_represents P hs O inp t
  apply Machine.HaltsWith.mono (t := 1 + P.time inp t) ?_ (by
    have := P.time_le inp t
    omega)
  constructor
  · exact hr.halt hh
  · exact hr.outTape.output

/-- Every finite counter program is implemented with constant overhead by a
fixed, explicitly constructed canonical NKtLB machine. -/
 theorem compile_halts (P : CounterProgram R L) (O : Set (List Bool)) (inp : Inputs)
    (t : ℕ) (hh : P.halted (P.run inp t)) :
    (compile P).HaltsWith O inp (1+2*t) (bitsSym (P.run inp t).output) :=
  haltsWith_of_localSimulation P (localSimulation P) O inp t hh

 theorem compile_computes (P : CounterProgram R L) (u : List Bool) (t : ℕ)
    (hh : P.halted (P.run ⟨u, [], [], []⟩ t)) :
    (compile P).Computes (1+2*t) u (P.run ⟨u, [], [], []⟩ t).output :=
  compile_halts P ∅ ⟨u, [], [], []⟩ t hh

#print axioms localSimulation
#print axioms compile_halts
#print axioms compile_computes
#print axioms compile_run_ne_query
end CounterCompiler
end ExpandingCodes.Computation
