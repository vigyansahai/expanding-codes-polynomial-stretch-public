import ExpandingCodes.Computation.TapeProgram
import ExpandingCodes.Computation.CounterCompiler

set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace TapeCompiler
open CounterCompiler (controlEquiv startControl haltControl queryControl normal finish
  getD_append_singleton tape_write_scanned)
variable {R B L : ℕ}

def workIdx (B : ℕ) (r : Fin R) : Fin (R+B+2) := ⟨r.val, by omega⟩
def outIdx (R B : ℕ) : Fin (R+B+2) := ⟨R+B, by omega⟩

/-- Buffer cells have distinct physical tapes after the unary counter tapes. -/
def bufferIdx (R : ℕ) (b : Fin B) : Fin (R+B+2) := ⟨R+b.val, by omega⟩

 theorem workIdx_ne_bufferIdx (r : Fin R) (b : Fin B) : workIdx B r ≠ bufferIdx R b := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [workIdx, bufferIdx] at hv
  omega

 theorem bufferIdx_ne_workIdx (b : Fin B) (r : Fin R) : bufferIdx R b ≠ workIdx B r :=
  Ne.symm (workIdx_ne_bufferIdx r b)

 theorem bufferIdx_ne_outIdx (b : Fin B) : bufferIdx R b ≠ outIdx R B := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [bufferIdx, outIdx] at hv
  omega

 theorem outIdx_ne_bufferIdx (b : Fin B) : outIdx R B ≠ bufferIdx R b :=
  Ne.symm (bufferIdx_ne_outIdx (R := R) b)

@[simp] theorem bufferIdx_eq_iff (b c : Fin B) : bufferIdx R b = bufferIdx R c ↔ b = c := by
  simp [bufferIdx, Fin.ext_iff]

def target (P : TapeProgram R B L) (j : Fin L) : CounterControl L :=
  match P.code j with
  | .halt => haltControl
  | _ => normal j

def idle (rw : Fin (R+B+2) → Sym) : Fin (R+B+2) → Sym × Move :=
  fun k => (rw k, .stay)

def roIdle : Fin 4 → Move := fun _ => .stay

/-- A literal finite transition table over the four scanned symbols. The
`next : Sym → Fin L` field of a read instruction is just a four-entry branch table. -/
def transition (P : TapeProgram R B L) (q : CounterControl L)
    (ro : Fin 4 → Sym) (rw : Fin (R+B+2) → Sym) :
    CounterControl L × (Fin 4 → Move) × (Fin (R+B+2) → Sym × Move) :=
  match q with
  | .inr s =>
    if s = 0 then
      (target P P.entry, roIdle, fun k =>
        if k.val < R then (.bot, .stay) else (rw k, .stay))
    else (haltControl, roIdle, idle rw)
  | .inl (.inr j) =>
    match P.code j with
    | .inc r next => (target P next, roIdle,
        Function.update (idle rw) (workIdx B r) (.one, .stay))
    | _ => (haltControl, roIdle, idle rw)
  | .inl (.inl j) =>
    match P.code j with
    | .halt => (haltControl, roIdle, idle rw)
    | .jump next => (target P next, roIdle, idle rw)
    | .inc r _ => (finish j, roIdle,
        Function.update (idle rw) (workIdx B r) (rw (workIdx B r), .right))
    | .dec r zero positive =>
      if rw (workIdx B r) = .bot then (target P zero, roIdle, idle rw)
      else (target P positive, roIdle,
        Function.update (idle rw) (workIdx B r) (.blank, .left))
    | .emit b next => (target P next, roIdle,
        Function.update (idle rw) (outIdx R B) (Sym.ofBool b, .right))
    | .read r next =>
      (target P (next (ro r)), Function.update roIdle r .right, idle rw)
    | .buffer b action =>
      let a := action (rw (bufferIdx R b))
      (target P a.2.2, roIdle,
        Function.update (idle rw) (bufferIdx R b) (a.1, a.2.1))

/-- Compiles every finite tape program to the exact canonical NKtLB machine.
No oracle, arithmetic, or unbounded memory action occurs in its transition table. -/
abbrev compile (P : TapeProgram R B L) : Machine where
  nStates := L+L+3
  start := controlEquiv L startControl
  halt := controlEquiv L haltControl
  query := controlEquiv L queryControl
  qyes := controlEquiv L haltControl
  qno := controlEquiv L haltControl
  works := R+B
  δ := fun q ro rw =>
    let a := transition P ((controlEquiv L).symm q) ro rw
    (controlEquiv L a.1, a.2)

 theorem target_ne_query (P : TapeProgram R B L) (j : Fin L) :
    target P j ≠ queryControl := by
  unfold target
  cases P.code j <;> simp [haltControl, queryControl, normal]

 theorem transition_ne_query (P : TapeProgram R B L) (q : CounterControl L)
    (ro : Fin 4 → Sym) (rw : Fin (R+B+2) → Sym) :
    (transition P q ro rw).1 ≠ queryControl := by
  rcases q with (j | j) | s
  · cases h : P.code j <;> simp only [transition, h] <;> try split_ifs
    all_goals first | exact target_ne_query P _ | simp [finish, haltControl, queryControl]
  · cases h : P.code j <;> simp only [transition, h]
    all_goals first | exact target_ne_query P _ | simp [haltControl, queryControl]
  · simp only [transition]
    split <;> first | exact target_ne_query P _ | simp [haltControl, queryControl]

 theorem compile_start_ne_query (P : TapeProgram R B L) :
    (compile P).start ≠ (compile P).query := by
  simp [compile, startControl, queryControl]

 theorem compile_delta_ne_query (P : TapeProgram R B L)
    (q : Fin (compile P).nStates) (ro : Fin 4 → Sym)
    (rw : Fin ((compile P).works+2) → Sym) :
    ((compile P).δ q ro rw).1 ≠ (compile P).query := by
  change controlEquiv L _ ≠ controlEquiv L queryControl
  exact (controlEquiv L).injective.ne (transition_ne_query P _ ro rw)

/-- The compiled machine never reaches the query state, for any oracle and inputs. -/
 theorem compile_run_ne_query (P : TapeProgram R B L) (O : Set (List Bool))
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
proved unary invariant; buffers and output are represented extensionally, so
trailing-blank storage never changes the represented data. -/
structure Represents (P : TapeProgram R B L) (c : TapeCfg R B L)
    (m : Machine.Cfg (compile P)) : Prop where
  state : m.state = controlEquiv L (target P c.pc)
  roHead : m.roHead = c.roHead
  workHead : ∀ r, m.rwHead (workIdx B r) = c.reg r
  workTape : ∀ r, TapeRep (m.rwTape (workIdx B r)) (unary (c.reg r))
  outHead : m.rwHead (outIdx R B) = c.output.length
  outTape : TapeRep (m.rwTape (outIdx R B)) (fun k => (bitsSym c.output).getD k .blank)
  bufferHead : ∀ b, m.rwHead (bufferIdx R b) = c.bufferHead b
  bufferTape : ∀ b, TapeRep (m.rwTape (bufferIdx R b)) (fun k => (c.bufferTape b).getD k .blank)

 theorem target_eq_halt (P : TapeProgram R B L) (j : Fin L) :
    target P j = haltControl ↔ P.code j = .halt := by
  unfold target
  cases P.code j <;> simp [haltControl, normal]

 theorem Represents.halt {P : TapeProgram R B L} {c : TapeCfg R B L}
    {m : Machine.Cfg (compile P)} (h : Represents P c m) (hc : P.halted c) :
    m.state = (compile P).halt := by
  rw [h.state, (target_eq_halt P c.pc).mpr hc]

/-- A finite local proof obligation: simulate each of the seven instruction forms,
with the two-action increment distinguished from the one-action instructions. -/
def LocalSimulation (P : TapeProgram R B L) : Prop :=
  ∀ (O : Set (List Bool)) (inp : Inputs) (c : TapeCfg R B L)
    (m : Machine.Cfg (compile P)),
    Represents P c m →
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m)

 theorem initial_represents (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs) :
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
    simp [workIdx, TapeProgram.init, unary, hlt]
    by_cases hk : k = 0 <;> simp [hk]
  · rfl
  · intro k
    simp [outIdx, TapeProgram.init, bitsSym, List.getD_eq_getElem?_getD]

  · intro b; rfl
  · intro b k
    have hnot : ¬ R + b.val < R := by omega
    simp [bufferIdx, TapeProgram.init, hnot, List.getD_eq_getElem?_getD]

/-- Ordinary target transitions expose only canonical head moves and `writeAt`. -/
 theorem step_normal (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
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

 theorem local_halt (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P))
    (hc : P.halted c) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  rw [P.step_halted inp c hc]
  change P.code c.pc = .halt at hc
  simpa [TapeProgram.cost, hc] using hr

 theorem local_jump (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P)) (j : Fin L)
    (hc : P.code c.pc = .jump j) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  simp only [TapeProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, TapeProgram.step]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro r
    simpa [idle, Machine.moveHead] using hr.workHead r
  · intro r k
    simp only [idle, getD_writeAt]
    rw [hr.workTape r k, hr.workTape r (m.rwHead (workIdx B r))]
    split_ifs with hk
    · exact congrArg (unary (c.reg r)) hk.symm
    · rfl
  · simpa [idle, Machine.moveHead] using hr.outHead
  · intro k
    simp only [idle, getD_writeAt]
    rw [hr.outTape k, hr.outTape (m.rwHead (outIdx R B))]
    split_ifs with hk
    · exact congrArg (fun z => (bitsSym c.output).getD z .blank) hk.symm
    · rfl
  · intro b
    simpa [idle, Machine.moveHead] using hr.bufferHead b
  · intro b
    simpa [idle, Machine.moveHead] using tape_write_scanned (hr.bufferTape b) (m.rwHead (bufferIdx R b))


 theorem local_read (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P)) (r : Fin 4)
    (next : Sym → Fin L) (hc : P.code c.pc = .read r next) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  simp only [TapeProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, TapeProgram.step]
  constructor
  · simp [hr.roHead]
  · funext i
    by_cases hi : i = r <;> simp [hi, roIdle, Machine.moveHead, hr.roHead]
  · intro i
    simpa [idle, Machine.moveHead] using hr.workHead i
  · intro i k
    simp only [idle, getD_writeAt]
    rw [hr.workTape i k, hr.workTape i (m.rwHead (workIdx B i))]
    split_ifs with hk
    · exact congrArg (unary (c.reg i)) hk.symm
    · rfl
  · simpa [idle, Machine.moveHead] using hr.outHead
  · intro k
    simp only [idle, getD_writeAt]
    rw [hr.outTape k, hr.outTape (m.rwHead (outIdx R B))]
    split_ifs with hk
    · exact congrArg (fun z => (bitsSym c.output).getD z .blank) hk.symm
    · rfl
  · intro b
    simpa [idle, Machine.moveHead] using hr.bufferHead b
  · intro b
    simpa [idle, Machine.moveHead] using tape_write_scanned (hr.bufferTape b) (m.rwHead (bufferIdx R b))


 theorem workIdx_ne_outIdx (r : Fin R) : workIdx B r ≠ outIdx R B := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [workIdx, outIdx] at hv
  omega

 theorem outIdx_ne_workIdx (r : Fin R) : outIdx R B ≠ workIdx B r :=
  Ne.symm (workIdx_ne_outIdx (B := B) r)

 theorem local_emit (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P)) (b : Bool) (j : Fin L)
    (hc : P.code c.pc = .emit b j) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  simp only [TapeProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, TapeProgram.step]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro r
    simpa [Function.update_of_ne (workIdx_ne_outIdx (B := B) r), idle, Machine.moveHead]
      using hr.workHead r
  · intro r k
    simp only [Function.update_of_ne (workIdx_ne_outIdx (B := B) r), idle, getD_writeAt]
    rw [hr.workTape r k, hr.workTape r (m.rwHead (workIdx B r))]
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
  · intro b
    simpa [Function.update_of_ne (bufferIdx_ne_outIdx (R := R) b), idle, Machine.moveHead] using hr.bufferHead b
  · intro b
    simpa [Function.update_of_ne (bufferIdx_ne_outIdx (R := R) b), idle, Machine.moveHead] using tape_write_scanned (hr.bufferTape b) (m.rwHead (bufferIdx R b))


@[simp] theorem workIdx_eq_iff (r s : Fin R) : workIdx B r = workIdx B s ↔ r = s := by
  simp [workIdx, Fin.ext_iff]

 theorem local_dec_zero (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P)) (r : Fin R) (z p : Fin L)
    (hc : P.code c.pc = .dec r z p) (hr : Represents P c m) (hz : c.reg r = 0) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  have hscan : (m.rwTape (workIdx B r)).getD (m.rwHead (workIdx B r)) .blank = .bot := by
    rw [hr.workHead r, hr.workTape r, hz]
    rfl
  simp only [TapeProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, TapeProgram.step, hscan, hz, ite_true, eq_self_iff_true]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro i
    simpa [idle, Machine.moveHead] using hr.workHead i
  · intro i k
    simp only [idle, getD_writeAt]
    rw [hr.workTape i k, hr.workTape i (m.rwHead (workIdx B i))]
    split_ifs with hk
    · exact congrArg (unary (c.reg i)) hk.symm
    · rfl
  · simpa [idle, Machine.moveHead] using hr.outHead
  · intro k
    simp only [idle, getD_writeAt]
    rw [hr.outTape k, hr.outTape (m.rwHead (outIdx R B))]
    split_ifs with hk
    · exact congrArg (fun z => (bitsSym c.output).getD z .blank) hk.symm
    · rfl
  · intro b
    simpa [idle, Machine.moveHead] using hr.bufferHead b
  · intro b
    simpa [idle, Machine.moveHead] using tape_write_scanned (hr.bufferTape b) (m.rwHead (bufferIdx R b))


 theorem local_dec_positive (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P)) (r : Fin R) (z p : Fin L) (n : ℕ)
    (hc : P.code c.pc = .dec r z p) (hr : Represents P c m) (hn : c.reg r = n+1) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  have hscan : (m.rwTape (workIdx B r)).getD (m.rwHead (workIdx B r)) .blank = .one := by
    rw [hr.workHead r, hr.workTape r, hn]
    simp
  simp only [TapeProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, TapeProgram.step, hscan, hn,
    reduceCtorEq, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro i
    by_cases hi : i = r
    · subst i
      simp [Function.update_self, Machine.moveHead, hr.workHead, hn]
    · have hi' : workIdx B i ≠ workIdx B r := by simpa using hi
      simpa [Function.update_of_ne hi', Function.update_of_ne hi, idle, Machine.moveHead]
        using hr.workHead i
  · intro i
    by_cases hi : i = r
    · subst i
      have ht : TapeRep (m.rwTape (workIdx B r)) (unary (n+1)) := by
        simpa [hn] using hr.workTape r
      simpa [Function.update_self, hr.workHead, hn] using (unary_dec_one_step ht).1
    · have hi' : workIdx B i ≠ workIdx B r := by simpa using hi
      intro k
      simp only [Function.update_of_ne hi', Function.update_of_ne hi, idle, getD_writeAt]
      rw [hr.workTape i k, hr.workTape i (m.rwHead (workIdx B i))]
      split_ifs with hk
      · exact congrArg (unary (c.reg i)) hk.symm
      · rfl
  · simpa [Function.update_of_ne (outIdx_ne_workIdx (B := B) r), idle, Machine.moveHead] using hr.outHead
  · intro k
    simp only [Function.update_of_ne (outIdx_ne_workIdx (B := B) r), idle, getD_writeAt]
    rw [hr.outTape k, hr.outTape (m.rwHead (outIdx R B))]
    split_ifs with hk
    · exact congrArg (fun z => (bitsSym c.output).getD z .blank) hk.symm
    · rfl
  · intro b
    simpa [Function.update_of_ne (bufferIdx_ne_workIdx b r), idle, Machine.moveHead] using hr.bufferHead b
  · intro b
    simpa [Function.update_of_ne (bufferIdx_ne_workIdx b r), idle, Machine.moveHead] using tape_write_scanned (hr.bufferTape b) (m.rwHead (bufferIdx R b))


 theorem step_finish (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
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

 theorem local_inc (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P)) (r : Fin R) (j : Fin L)
    (hc : P.code c.pc = .inc r j) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  have hfinish : ((compile P).step O inp m).state = controlEquiv L (finish c.pc) := by
    rw [step_normal P O inp c.pc m hm]
    simp only [normal, transition, hc]
  simp only [TapeProgram.cost, hc]
  change Represents P (P.step inp c) ((compile P).step O inp ((compile P).step O inp m))
  rw [step_finish P O inp c.pc _ hfinish, step_normal P O inp c.pc m hm]
  simp only [normal, finish, transition, hc, TapeProgram.step]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro i
    by_cases hi : i = r
    · subst i
      simp [Function.update_self, Machine.moveHead, hr.workHead]
    · have hi' : workIdx B i ≠ workIdx B r := by simpa using hi
      simpa [Function.update_of_ne hi', Function.update_of_ne hi, idle, Machine.moveHead]
        using hr.workHead i
  · intro i
    by_cases hi : i = r
    · subst i
      simpa [Function.update_self, idle, Machine.moveHead, hr.workHead]
        using (unary_inc_two_steps (hr.workTape r)).1
    · have hi' : workIdx B i ≠ workIdx B r := by simpa using hi
      simpa [Function.update_of_ne hi', Function.update_of_ne hi, idle, Machine.moveHead]
        using tape_write_scanned (tape_write_scanned (hr.workTape i) (m.rwHead (workIdx B i)))
          (m.rwHead (workIdx B i))
  · simpa [Function.update_of_ne (outIdx_ne_workIdx (B := B) r), idle, Machine.moveHead] using hr.outHead
  · simpa [Function.update_of_ne (outIdx_ne_workIdx (B := B) r), idle, Machine.moveHead]
      using tape_write_scanned (tape_write_scanned hr.outTape (m.rwHead (outIdx R B)))
        (m.rwHead (outIdx R B))
  · intro b
    simpa [Function.update_of_ne (bufferIdx_ne_workIdx b r), idle, Machine.moveHead] using hr.bufferHead b
  · intro b
    simpa [Function.update_of_ne (bufferIdx_ne_workIdx b r), idle, Machine.moveHead] using tape_write_scanned (tape_write_scanned (hr.bufferTape b) (m.rwHead (bufferIdx R b))) (m.rwHead (bufferIdx R b))


/-- One buffer instruction is exactly one legal cell operation, even when the
source and target use different trailing-blank storage for that buffer. -/
 theorem local_buffer (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P)) (b : Fin B)
    (action : Sym → Sym × Move × Fin L)
    (hc : P.code c.pc = .buffer b action) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  have hscan : (m.rwTape (bufferIdx R b)).getD (m.rwHead (bufferIdx R b)) .blank =
      (c.bufferTape b).getD (c.bufferHead b) .blank := by
    rw [hr.bufferHead b, hr.bufferTape b]
  simp only [TapeProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, TapeProgram.step]
  rw [hscan]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro r
    simpa [Function.update_of_ne (workIdx_ne_bufferIdx r b), idle, Machine.moveHead]
      using hr.workHead r
  · intro r
    simpa [Function.update_of_ne (workIdx_ne_bufferIdx r b), idle]
      using tape_write_scanned (hr.workTape r) (m.rwHead (workIdx B r))
  · simpa [Function.update_of_ne (outIdx_ne_bufferIdx (R := R) b), idle, Machine.moveHead]
      using hr.outHead
  · simpa [Function.update_of_ne (outIdx_ne_bufferIdx (R := R) b), idle]
      using tape_write_scanned hr.outTape (m.rwHead (outIdx R B))
  · intro i
    by_cases hi : i = b
    · subst i
      simp only [Function.update_self]
      rw [hr.bufferHead b]
    · have hi' : bufferIdx R i ≠ bufferIdx R b := by simpa using hi
      simpa [Function.update_of_ne hi', Function.update_of_ne hi, idle, Machine.moveHead]
        using hr.bufferHead i
  · intro i
    by_cases hi : i = b
    · subst i
      intro k
      simp only [Function.update_self, getD_writeAt]
      rw [hr.bufferHead b, hr.bufferTape b k]
    · have hi' : bufferIdx R i ≠ bufferIdx R b := by simpa using hi
      simpa [Function.update_of_ne hi', Function.update_of_ne hi, idle]
        using tape_write_scanned (hr.bufferTape i) (m.rwHead (bufferIdx R i))

 theorem localSimulation (P : TapeProgram R B L) : LocalSimulation P := by
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
  | buffer b action => exact local_buffer P O inp c m b action hc hr

/-- Once the finite local instruction obligations are supplied, every source
execution is simulated at its exact accumulated microstep time. -/
 theorem run_represents (P : TapeProgram R B L) (hs : LocalSimulation P)
    (O : Set (List Bool)) (inp : Inputs) (t : ℕ) :
    Represents P (P.run inp t) ((compile P).run O inp (1 + P.time inp t)) := by
  induction t with
  | zero => simpa [TapeProgram.run, TapeProgram.time] using initial_represents P O inp
  | succ t ih =>
    have h := hs O inp (P.run inp t) _ ih
    rw [TapeProgram.run_succ]
    simpa only [TapeProgram.time, ← Nat.add_assoc, Machine.run_add] using h

/-- Halting/output correctness and the actual target time bound follow from the
finite local simulation obligation, rather than from a polynomial-time oracle. -/
 theorem haltsWith_of_localSimulation (P : TapeProgram R B L) (hs : LocalSimulation P)
    (O : Set (List Bool)) (inp : Inputs) (t : ℕ) (hh : P.halted (P.run inp t)) :
    (compile P).HaltsWith O inp (1+2*t) (bitsSym (P.run inp t).output) := by
  have hr := run_represents P hs O inp t
  apply Machine.HaltsWith.mono (t := 1 + P.time inp t) ?_ (by
    have := P.time_le inp t
    omega)
  constructor
  · exact hr.halt hh
  · exact hr.outTape.output

/-- Every finite tape program is implemented with constant overhead by a
fixed, explicitly constructed canonical NKtLB machine. -/
 theorem compile_halts (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (t : ℕ) (hh : P.halted (P.run inp t)) :
    (compile P).HaltsWith O inp (1+2*t) (bitsSym (P.run inp t).output) :=
  haltsWith_of_localSimulation P (localSimulation P) O inp t hh

 theorem compile_computes (P : TapeProgram R B L) (u : List Bool) (t : ℕ)
    (hh : P.halted (P.run ⟨u, [], [], []⟩ t)) :
    (compile P).Computes (1+2*t) u (P.run ⟨u, [], [], []⟩ t).output :=
  compile_halts P ∅ ⟨u, [], [], []⟩ t hh

#print axioms localSimulation
#print axioms compile_halts
#print axioms compile_computes
#print axioms compile_run_ne_query
end TapeCompiler
end ExpandingCodes.Computation
