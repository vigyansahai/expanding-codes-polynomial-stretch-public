import ExpandingCodes.Computation.TapeControl
import ExpandingCodes.Computation.FieldPrograms

set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
open scoped BigOperators
namespace SamplerOdometer
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

/-- One physical decrement/test. Both outcomes halt after one transition. -/
def decrement (r : Fin R) : TapeProgram R B 2 where
  entry := 0
  code j := if j=0 then .dec r 1 1 else .halt

theorem decrement_stops (r : Fin R) (inp : Inputs) (d : TapeStore R B) :
    (decrement r).Stops inp (d.toCfg 0) 1 ((d.setReg r (d.reg r-1)).toCfg 1) := by
  constructor
  · apply TapeProgram.Exec.one
    · simp [TapeProgram.halted,decrement]
    · simp only [TapeProgram.step,decrement,TapeStore.toCfg,ite_true]
      split
      · rename_i hz
        simp [hz,TapeStore.setReg]
      · rfl
  · simp [TapeProgram.halted,decrement]

/-- A digit is stored together with its countdown q-1-digit. All digits have
separate unary counters; no tuple is packed into a unary number. -/
abbrev Digit (R : ℕ) := Fin R × Fin R

def used : List (Digit R) → List (Fin R)
  | [] => []
  | p::ps => p.1::p.2::used ps

def reset (q tmp : Fin R) (p : Digit R) : TapeProgram R B 15 :=
  TapeProgram.seq (TapeProgram.seq (TapeMacros.clear p.1)
    (TapeMacros.copy q p.2 tmp)) (decrement p.2)

def resetStore (q tmp : Fin R) (p : Digit R) (s : TapeStore R B) : TapeStore R B :=
  ((s.setReg p.1 0).setReg p.2 (s.reg q-1)).setReg tmp 0

def advance (p : Digit R) : TapeProgram R B 4 :=
  TapeProgram.seq (decrement p.2) (TapeMacros.increment p.1)

def advanceStore (p : Digit R) (s : TapeStore R B) : TapeStore R B :=
  (s.setReg p.2 (s.reg p.2-1)).setReg p.1 (s.reg p.1+1)

def labels : List (Digit R) → ℕ
  | [] => 1
  | _::ps => (15+labels ps)+4+2

/-- Fixed-dimensional little-endian odometer. Each stage performs a physical
countdown test, an increment, or a physical reset followed by carry. The finite
code table depends only on the list of digit registers, never runtime q. -/
def program (q tmp : Fin R) : (ps : List (Digit R)) → TapeProgram R B (labels ps)
  | [] => TapeProgram.skip
  | p::ps => TapeProgram.branchZero p.2
      (TapeProgram.seq (reset q tmp p) (program q tmp ps)) (advance p)

def nextStore (q tmp : Fin R) : List (Digit R) → TapeStore R B → TapeStore R B
  | [],s => s
  | p::ps,s => if s.reg p.2=0 then nextStore q tmp ps (resetStore q tmp p s)
      else advanceStore p s

theorem advance_stops (p : Digit R) (hp : p.1≠p.2)
    (inp : Inputs) (s : TapeStore R B) :
    (advance p).Stops inp (s.toCfg (advance (B := B) p).entry) 3
      ((advanceStore p s).toCfg (TapeProgram.rightLabel 2 (1 : Fin 2))) := by
  have h₁ := decrement_stops p.2 inp s
  have h₂ := TapeMacros.increment_stops p.1 inp (s.setReg p.2 (s.reg p.2-1))
  have hall := h₁.seq h₂
  simpa [advance,advanceStore,TapeStore.setReg,hp,TapeCfg.mapPC,TapeStore.toCfg,TapeProgram.seq,decrement] using hall

theorem reset_stops (q tmp : Fin R) (p : Digit R)
    (hqp : q≠p.1) (hqc : q≠p.2) (hqt : q≠tmp)
    (hpc : p.1≠p.2) (hpt : p.1≠tmp) (hct : p.2≠tmp)
    (inp : Inputs) (s : TapeStore R B) :
    ∃ t e, t  ≤  s.reg p.1+s.reg p.2+s.reg tmp+5*s.reg q+11 ∧
      (reset q tmp p).Stops inp (s.toCfg (reset (B := B) q tmp p).entry) t e ∧
      e.store=resetStore q tmp p s := by
  have h₁ := TapeMacros.clear_stops p.1 inp (s.reg p.1) s rfl
  obtain ⟨c,h₂,hcs⟩ := TapeMacros.copy_stops q p.2 tmp hqc hqt hct inp (s.setReg p.1 0)
  have h₃ := decrement_stops p.2 inp c.store
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_,_,?_,hall,?_⟩
  · simp only [TapeStore.setReg,Function.update_of_ne (Ne.symm hpc),Function.update_of_ne (Ne.symm hpt),Function.update_of_ne hqp]
    omega
  · change c.store.setReg p.2 (c.reg p.2-1)=_
    rw [show c.reg p.2=(s.reg q) by
      change c.store.reg p.2=_; rw [hcs]; simp [TapeStore.setReg,hct,hqp]]
    rw [hcs]
    simp only [resetStore]
    rw [show (s.setReg p.1 0).reg q=s.reg q by simp [TapeStore.setReg,hqp]]
    rw [setReg_comm _ tmp p.2 _ _ (Ne.symm hct),TapeStore.setReg_same]

theorem resetStore_bound (q tmp : Fin R) (p : Digit R) (s : TapeStore R B)
    (M : ℕ) (hs : ∀ j,s.reg j ≤ M) : ∀ j,(resetStore q tmp p s).reg j ≤ M := by
  unfold resetStore
  apply setReg_bound
  · apply setReg_bound
    · exact setReg_bound s _ 0 M hs (by omega)
    · exact (Nat.sub_le _ _).trans (hs q)
  · omega

theorem advanceStore_bound (p : Digit R) (s : TapeStore R B)
    (M : ℕ) (hs : ∀ j,s.reg j ≤ M) : ∀ j,(advanceStore p s).reg j ≤ M+1 := by
  unfold advanceStore
  apply setReg_bound
  · apply setReg_bound
    · exact fun j => (hs j).trans (by omega)
    · exact (Nat.sub_le _ _).trans ((hs p.2).trans (by omega))
  · have := hs p.1; omega

/-- Uniform source bound for the actual finite odometer. It is valid even for
arbitrary scratch contents; canonical digit invariants are proved separately. -/
theorem program_stops (q tmp : Fin R) (ps : List (Digit R))
    (huniq : (q::tmp::used ps).Nodup) (inp : Inputs)
    (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M) :
    ∃ t e, t  ≤  ps.length*(8*M+20) ∧
      (program q tmp ps).Stops inp (s.toCfg (program (B := B) q tmp ps).entry) t e ∧
      e.store=nextStore q tmp ps s ∧ ∀ j,e.reg j ≤ M+1 := by
  induction ps generalizing s with
  | nil =>
    refine ⟨0,s.toCfg ⟨0,by simp [labels]⟩,by simp, TapeProgram.skip_stops inp s,rfl,?_⟩
    exact fun j => (hs j).trans (by omega)
  | cons p ps ih =>
    have hu : q≠tmp ∧ q≠p.1 ∧ q≠p.2 ∧ q∉used ps ∧
        tmp≠p.1 ∧ tmp≠p.2 ∧ tmp∉used ps ∧
        p.1≠p.2 ∧ p.1∉used ps ∧ p.2∉used ps ∧ (used ps).Nodup := by
      simp only [used,List.nodup_cons,List.mem_cons,not_or] at huniq
      tauto
    rcases hu with ⟨hqt,hqp,hqc,hqps,htp,htc,htps,hpc,hpps,hcps,hps⟩
    have hut : (q::tmp::used ps).Nodup := by
      simp only [List.nodup_cons,List.mem_cons,not_or]
      exact ⟨⟨hqt,hqps⟩,htps,hps⟩
    have hpt : p.1≠tmp := Ne.symm htp
    have hct : p.2≠tmp := Ne.symm htc
    by_cases hz : s.reg p.2=0
    · obtain ⟨a,c,ha,hc,hcs⟩ := reset_stops q tmp p hqp hqc hqt hpc hpt hct inp s
      obtain ⟨b,e,hb,he,hes,heb⟩ := ih hut (resetStore q tmp p s)
        (resetStore_bound q tmp p s M hs)
      rw [← hcs] at he
      have hcarry := hc.seq he
      have hall := TapeProgram.branchZero_stops_zero p.2
        (TapeProgram.seq (reset q tmp p) (program q tmp ps)) (advance p) inp s hz hcarry
      refine ⟨1+(a+1+b),_,?_,hall,?_,heb⟩
      · have h₁ := hs p.1; have h₂ := hs p.2; have h₃ := hs tmp; have h₄ := hs q
        change 1+(a+1+b)  ≤  (ps.length+1)*(8*M+20)
        rw [Nat.add_mul,Nat.one_mul]
        omega
      · simpa only [nextStore,if_pos hz] using hes
    · have hc := advance_stops p hpc inp s
      have hall := TapeProgram.branchZero_stops_positive p.2
        (TapeProgram.seq (reset q tmp p) (program q tmp ps)) (advance p) inp s hz hc
      refine ⟨5,_,?_,hall,?_,?_⟩
      · change 5  ≤  (ps.length+1)*(8*M+20)
        rw [Nat.add_mul,Nat.one_mul]
        omega
      · simp [nextStore,hz]
      · exact advanceStore_bound p s M hs

theorem nextStore_fresh (q tmp : Fin R) (ps : List (Digit R))
    (s : TapeStore R B) (j : Fin R) (hjt : j≠tmp) (hj : j∉used ps) :
    (nextStore q tmp ps s).reg j=s.reg j := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [used,List.mem_cons,not_or] at hj
    simp only [nextStore]
    split
    · rw [ih _ hj.2.2]
      simp [resetStore,TapeStore.setReg,hjt,hj.1,hj.2.1]
    · simp [advanceStore,TapeStore.setReg,hj.1,hj.2.1]

theorem nextStore_payload (q tmp : Fin R) (ps : List (Digit R)) (s : TapeStore R B) :
    (nextStore q tmp ps s).roHead=s.roHead ∧
      (nextStore q tmp ps s).output=s.output ∧
      (nextStore q tmp ps s).bufferTape=s.bufferTape ∧
      (nextStore q tmp ps s).bufferHead=s.bufferHead := by
  induction ps generalizing s with
  | nil => exact ⟨rfl,rfl,rfl,rfl⟩
  | cons p ps ih =>
    simp only [nextStore]
    split
    · simpa only [resetStore,TapeStore.setReg] using ih (resetStore q tmp p s)
    · exact ⟨rfl,rfl,rfl,rfl⟩

/-- The ordinary little-endian digit list represented by the separate counters. -/
def readings (ps : List (Digit R)) (s : TapeStore R B) : List ℕ := ps.map (fun p => s.reg p.1)

def successor (q : ℕ) : List ℕ → List ℕ
  | [] => []
  | x::xs => if x+1=q then 0::successor q xs else (x+1)::xs

/-- Runtime invariant linking a digit with its unary countdown. -/
def Valid (q : Fin R) (ps : List (Digit R)) (s : TapeStore R B) : Prop :=
  ∀ p∈ps,s.reg p.1+s.reg p.2+1=s.reg q

theorem readings_congr (ps : List (Digit R)) (s e : TapeStore R B)
    (h : ∀ p∈ps,s.reg p.1=e.reg p.1) : readings ps s=readings ps e := by
  exact List.map_congr_left h

theorem used_mem_left (ps : List (Digit R)) (p : Digit R) (hp : p∈ps) : p.1∈used ps := by
  induction ps with
  | nil => simp at hp
  | cons z ps ih =>
    simp only [List.mem_cons] at hp
    rcases hp with rfl|hp
    · simp [used]
    · simp [used,ih hp]

theorem used_mem_right (ps : List (Digit R)) (p : Digit R) (hp : p∈ps) : p.2∈used ps := by
  induction ps with
  | nil => simp at hp
  | cons z ps ih =>
    simp only [List.mem_cons] at hp
    rcases hp with rfl|hp
    · simp [used]
    · simp [used,ih hp]

theorem program_readings (q tmp : Fin R) (ps : List (Digit R))
    (huniq : (q::tmp::used ps).Nodup) (s : TapeStore R B) (hv : Valid q ps s) :
    readings ps (nextStore q tmp ps s)=successor (s.reg q) (readings ps s) := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    have hu : q≠tmp ∧ q≠p.1 ∧ q≠p.2 ∧ q∉used ps ∧
        tmp≠p.1 ∧ tmp≠p.2 ∧ tmp∉used ps ∧
        p.1≠p.2 ∧ p.1∉used ps ∧ p.2∉used ps ∧ (used ps).Nodup := by
      simp only [used,List.nodup_cons,List.mem_cons,not_or] at huniq
      tauto
    rcases hu with ⟨hqt,hqp,hqc,hqps,htp,htc,htps,hpc,hpps,hcps,hps⟩
    have hut : (q::tmp::used ps).Nodup := by
      simp only [List.nodup_cons,List.mem_cons,not_or]
      exact ⟨⟨hqt,hqps⟩,htps,hps⟩
    have hpv := hv p (by simp)
    have htail : Valid q ps s := fun a ha => hv a (by simp [ha])
    have hneq (a : Digit R) (ha : a∈ps) :
        a.1≠p.1 ∧ a.1≠p.2 ∧ a.1≠tmp ∧ a.2≠p.1 ∧ a.2≠p.2 ∧ a.2≠tmp := by
      have hl := used_mem_left ps a ha
      have hr := used_mem_right ps a ha
      constructor
      · exact fun he => hpps (he ▸ hl)
      constructor
      · exact fun he => hcps (he ▸ hl)
      constructor
      · exact fun he => htps (he ▸ hl)
      constructor
      · exact fun he => hpps (he ▸ hr)
      constructor
      · exact fun he => hcps (he ▸ hr)
      · exact fun he => htps (he ▸ hr)
    by_cases hz : s.reg p.2=0
    · have heq : s.reg p.1+1=s.reg q := by omega
      let e := resetStore q tmp p s
      have heqQ : e.reg q=s.reg q := by simp [e,resetStore,TapeStore.setReg,hqt,hqp,hqc]
      have hev : Valid q ps e := by
        intro a ha
        rcases hneq a ha with ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
        simpa [e,resetStore,TapeStore.setReg,h₁,h₂,h₃,h₄,h₅,h₆,hqt,hqp,hqc] using htail a ha
      have hre : readings ps e=readings ps s := by
        apply readings_congr
        intro a ha
        rcases hneq a ha with ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
        simp [e,resetStore,TapeStore.setReg,h₁,h₂,h₃]
      have hf := nextStore_fresh q tmp ps e p.1 (Ne.symm htp) hpps
      have hp0 : (nextStore q tmp ps e).reg p.1=0 := by
        rw [hf]
        simp [e,resetStore,TapeStore.setReg,Ne.symm htp,hpc]
      have hh := ih hut e hev
      rw [heqQ,hre] at hh
      rw [nextStore,if_pos hz]
      change (nextStore q tmp ps e).reg p.1 :: readings ps (nextStore q tmp ps e)=_
      rw [hp0,hh]
      simp only [readings,List.map_cons,successor,if_pos heq]
    · have heq : s.reg p.1+1≠s.reg q := by omega
      have hre : readings ps (advanceStore p s)=readings ps s := by
        apply readings_congr
        intro a ha
        rcases hneq a ha with ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
        simp [advanceStore,TapeStore.setReg,h₁,h₂]
      simp only [nextStore,if_neg hz,readings,List.map_cons,successor,if_neg heq]
      change (advanceStore p s).reg p.1 :: readings ps (advanceStore p s)=_
      rw [hre]
      simp [advanceStore,TapeStore.setReg,readings]

def initializeLabels : List (Digit R) → ℕ
  | [] => 1
  | _::ps => 15+initializeLabels ps

/-- Initialize every separate digit to zero and every countdown to runtime q-1
using copies of the runtime radix. This is finite code for any fixed dimension. -/
def initDigits (q tmp : Fin R) : (ps : List (Digit R)) → TapeProgram R B (initializeLabels ps)
  | [] => TapeProgram.skip
  | p::ps => TapeProgram.seq (reset q tmp p) (initDigits q tmp ps)

def initializeStore (q tmp : Fin R) : List (Digit R) → TapeStore R B → TapeStore R B
  | [],s => s
  | p::ps,s => initializeStore q tmp ps (resetStore q tmp p s)

theorem initializeStore_fresh (q tmp : Fin R) (ps : List (Digit R))
    (s : TapeStore R B) (j : Fin R) (hjt : j≠tmp) (hj : j∉used ps) :
    (initializeStore q tmp ps s).reg j=s.reg j := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [used,List.mem_cons,not_or] at hj
    rw [initializeStore,ih _ hj.2.2]
    simp [resetStore,TapeStore.setReg,hjt,hj.1,hj.2.1]

theorem initialize_stops (q tmp : Fin R) (ps : List (Digit R))
    (huniq : (q::tmp::used ps).Nodup) (inp : Inputs)
    (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M) :
    ∃ t e, t  ≤  ps.length*(8*M+20) ∧
      (initDigits q tmp ps).Stops inp (s.toCfg (initDigits (B := B) q tmp ps).entry) t e ∧
      e.store=initializeStore q tmp ps s ∧ ∀ j,e.reg j ≤ M := by
  induction ps generalizing s with
  | nil =>
    exact ⟨0,s.toCfg ⟨0,by simp [initializeLabels]⟩,by simp,
      TapeProgram.skip_stops inp s,rfl,hs⟩
  | cons p ps ih =>
    have hu : q≠tmp ∧ q≠p.1 ∧ q≠p.2 ∧ q∉used ps ∧
        tmp≠p.1 ∧ tmp≠p.2 ∧ tmp∉used ps ∧
        p.1≠p.2 ∧ p.1∉used ps ∧ p.2∉used ps ∧ (used ps).Nodup := by
      simp only [used,List.nodup_cons,List.mem_cons,not_or] at huniq
      tauto
    rcases hu with ⟨hqt,hqp,hqc,hqps,htp,htc,htps,hpc,hpps,hcps,hps⟩
    have hut : (q::tmp::used ps).Nodup := by
      simp only [List.nodup_cons,List.mem_cons,not_or]
      exact ⟨⟨hqt,hqps⟩,htps,hps⟩
    obtain ⟨a,c,ha,hc,hcs⟩ := reset_stops q tmp p hqp hqc hqt hpc (Ne.symm htp) (Ne.symm htc) inp s
    obtain ⟨b,e,hb,he,hes,heb⟩ := ih hut (resetStore q tmp p s)
      (resetStore_bound q tmp p s M hs)
    rw [← hcs] at he
    have hall := hc.seq he
    refine ⟨a+1+b,_,?_,hall,hes,heb⟩
    change a+1+b  ≤  (ps.length+1)*(8*M+20)
    rw [Nat.add_mul,Nat.one_mul]
    have h₁ := hs p.1; have h₂ := hs p.2; have h₃ := hs tmp; have h₄ := hs q
    omega

theorem initializeStore_values (q tmp : Fin R) (ps : List (Digit R))
    (huniq : (q::tmp::used ps).Nodup) (s : TapeStore R B) :
    ∀ p∈ps,(initializeStore q tmp ps s).reg p.1=0 ∧
      (initializeStore q tmp ps s).reg p.2=s.reg q-1 := by
  induction ps generalizing s with
  | nil => simp
  | cons p ps ih =>
    have hu : q≠tmp ∧ q≠p.1 ∧ q≠p.2 ∧ q∉used ps ∧
        tmp≠p.1 ∧ tmp≠p.2 ∧ tmp∉used ps ∧
        p.1≠p.2 ∧ p.1∉used ps ∧ p.2∉used ps ∧ (used ps).Nodup := by
      simp only [used,List.nodup_cons,List.mem_cons,not_or] at huniq
      tauto
    rcases hu with ⟨hqt,hqp,hqc,hqps,htp,htc,htps,hpc,hpps,hcps,hps⟩
    have hut : (q::tmp::used ps).Nodup := by
      simp only [List.nodup_cons,List.mem_cons,not_or]
      exact ⟨⟨hqt,hqps⟩,htps,hps⟩
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl|ha
    · rw [initializeStore,initializeStore_fresh q tmp ps _ a.1 (Ne.symm htp) hpps,
        initializeStore_fresh q tmp ps _ a.2 (Ne.symm htc) hcps]
      simp [resetStore,TapeStore.setReg,Ne.symm htp,Ne.symm htc,hpc]
    · have hh := ih hut (resetStore q tmp p s) a ha
      simpa [initializeStore,resetStore,TapeStore.setReg,hqt,hqp,hqc] using hh

theorem initializeStore_valid (q tmp : Fin R) (ps : List (Digit R))
    (huniq : (q::tmp::used ps).Nodup) (s : TapeStore R B) (hq : 0<s.reg q) :
    Valid q ps (initializeStore q tmp ps s) := by
  intro p hp
  have hv := initializeStore_values q tmp ps huniq s p hp
  have hfresh : (initializeStore q tmp ps s).reg q=s.reg q := by
    apply initializeStore_fresh
    · exact fun he => (List.nodup_cons.mp huniq).1 (by simp [he])
    · exact fun he => (List.nodup_cons.mp huniq).1 (by simp [he])
  rw [hv.1,hv.2,hfresh]
  omega

theorem program_valid (q tmp : Fin R) (ps : List (Digit R))
    (huniq : (q::tmp::used ps).Nodup) (s : TapeStore R B) (hv : Valid q ps s) :
    Valid q ps (nextStore q tmp ps s) := by
  induction ps generalizing s with
  | nil => simp [Valid]
  | cons p ps ih =>
    have hu : q≠tmp ∧ q≠p.1 ∧ q≠p.2 ∧ q∉used ps ∧
        tmp≠p.1 ∧ tmp≠p.2 ∧ tmp∉used ps ∧
        p.1≠p.2 ∧ p.1∉used ps ∧ p.2∉used ps ∧ (used ps).Nodup := by
      simp only [used,List.nodup_cons,List.mem_cons,not_or] at huniq
      tauto
    rcases hu with ⟨hqt,hqp,hqc,hqps,htp,htc,htps,hpc,hpps,hcps,hps⟩
    have hut : (q::tmp::used ps).Nodup := by
      simp only [List.nodup_cons,List.mem_cons,not_or]
      exact ⟨⟨hqt,hqps⟩,htps,hps⟩
    have hpv := hv p (by simp)
    have htail : Valid q ps s := fun a ha => hv a (by simp [ha])
    have hneq (a : Digit R) (ha : a∈ps) :
        a.1≠p.1 ∧ a.1≠p.2 ∧ a.1≠tmp ∧ a.2≠p.1 ∧ a.2≠p.2 ∧ a.2≠tmp := by
      have hl := used_mem_left ps a ha
      have hr := used_mem_right ps a ha
      exact ⟨fun he => hpps (he ▸ hl),fun he => hcps (he ▸ hl),fun he => htps (he ▸ hl),
        fun he => hpps (he ▸ hr),fun he => hcps (he ▸ hr),fun he => htps (he ▸ hr)⟩
    by_cases hz : s.reg p.2=0
    · let e := resetStore q tmp p s
      have heqQ : e.reg q=s.reg q := by simp [e,resetStore,TapeStore.setReg,hqt,hqp,hqc]
      have hev : Valid q ps e := by
        intro a ha
        rcases hneq a ha with ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
        simpa [e,resetStore,TapeStore.setReg,h₁,h₂,h₃,h₄,h₅,h₆,hqt,hqp,hqc] using htail a ha
      have hvnext := ih hut e hev
      rw [nextStore,if_pos hz]
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl|ha
      · rw [nextStore_fresh q tmp ps _ a.1 (Ne.symm htp) hpps,
          nextStore_fresh q tmp ps _ a.2 (Ne.symm htc) hcps,
          nextStore_fresh q tmp ps _ q hqt hqps]
        simp [resetStore,TapeStore.setReg,hqt,hqp,hqc,Ne.symm htp,Ne.symm htc,hpc]
        omega
      · exact hvnext a ha
    · rw [nextStore,if_neg hz]
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl|ha
      · simp [advanceStore,TapeStore.setReg,hpc,Ne.symm hpc,hqp,hqc]
        omega
      · rcases hneq a ha with ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
        simpa [advanceStore,TapeStore.setReg,h₁,h₂,h₄,h₅,hqp,hqc] using htail a ha

/-- Finite counter iterates preserve the canonical complement invariant. -/
theorem iterate_valid (q tmp : Fin R) (ps : List (Digit R))
    (huniq : (q::tmp::used ps).Nodup) (s : TapeStore R B) (hv : Valid q ps s) (n : ℕ) :
    Valid q ps ((nextStore q tmp ps)^[n] s) := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact program_valid q tmp ps huniq _ ih

theorem successor_length (q : ℕ) (xs : List ℕ) : (successor q xs).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [successor]; split <;> simp [ih]

/-- The finite carry routine enumerates integers modulo q^d in the same
least-significant-coordinate-first order as finFunctionFinEquiv. -/
theorem successor_number (q : ℕ) (hq : 1<q) (xs : List ℕ)
    (hx : ∀ x∈xs,x<q) :
    Nat.ofDigits q (successor q xs)=(Nat.ofDigits q xs+1)%q^xs.length := by
  induction xs with
  | nil => simp [successor]
  | cons x xs ih =>
    have h₀ : x<q := hx x (by simp)
    have ht : ∀ z∈xs,z<q := fun z hz => hx z (by simp [hz])
    have hb := Nat.ofDigits_lt_base_pow_length hq ht
    simp only [successor,List.length_cons]
    by_cases heq : x+1=q
    · rw [if_pos heq,Nat.ofDigits_cons,ih ht,Nat.ofDigits_cons]
      have hnum : x+q*Nat.ofDigits q xs+1=q*(Nat.ofDigits q xs+1) := by
        rw [Nat.mul_add,Nat.mul_one]
        omega
      rw [hnum,pow_succ',Nat.mul_mod_mul_left]
      simp
    · rw [if_neg heq,Nat.ofDigits_cons,Nat.ofDigits_cons]
      have hb' : x+q*Nat.ofDigits q xs+1<q^(xs.length+1) := by
        rw [pow_succ']
        have hx' : x+1<q := by omega
        have hm : q*(Nat.ofDigits q xs+1) ≤ q*q^xs.length := Nat.mul_le_mul_left q (by omega)
        rw [Nat.mul_add,Nat.mul_one] at hm
        omega
      rw [Nat.mod_eq_of_lt hb']
      omega

theorem readings_bounded (q : Fin R) (ps : List (Digit R))
    (s : TapeStore R B) (hv : Valid q ps s) : ∀ x∈readings ps s,x<s.reg q := by
  intro x hx
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
  have := hv p hp
  omega

theorem program_number (q tmp : Fin R) (ps : List (Digit R))
    (huniq : (q::tmp::used ps).Nodup) (s : TapeStore R B) (hv : Valid q ps s)
    (hq : 1<s.reg q) :
    Nat.ofDigits (s.reg q) (readings ps (nextStore q tmp ps s))=
      (Nat.ofDigits (s.reg q) (readings ps s)+1)%(s.reg q)^ps.length := by
  rw [program_readings q tmp ps huniq s hv,successor_number _ hq _ (readings_bounded q ps s hv)]
  simp [readings]

theorem number_ofFn (q d : ℕ) (f : Fin d → ℕ) :
    Nat.ofDigits q (List.ofFn f)=∑ i : Fin d,f i*q^i.val := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [List.ofFn_succ,Nat.ofDigits_cons,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ']
    ring

theorem number_eq_finFunctionFinEquiv (q d : ℕ) (f : Fin d → Fin q) :
    Nat.ofDigits q (List.ofFn (fun i => (f i).val))=(finFunctionFinEquiv f).val := by
  rw [number_ofFn,finFunctionFinEquiv_apply]

theorem canonical_digits (q d : ℕ) (f : Fin d → Fin q) (z : Fin (q^d))
    (hz : Nat.ofDigits q (List.ofFn (fun i => (f i).val))=z.val) :
    f=finFunctionFinEquiv.symm z := by
  apply finFunctionFinEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rw [← number_eq_finFunctionFinEquiv]
  exact hz

theorem iterate_radix (q tmp : Fin R) (ps : List (Digit R))
    (huniq : (q::tmp::used ps).Nodup) (s : TapeStore R B) (n : ℕ) :
    ((nextStore q tmp ps)^[n] s).reg q=s.reg q := by
  have hqt : q≠tmp := by
    intro he; exact (List.nodup_cons.mp huniq).1 (by simp [he])
  have hqps : q∉used ps := by
    intro he; exact (List.nodup_cons.mp huniq).1 (by simp [he])
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',nextStore_fresh q tmp ps _ q hqt hqps,ih]

/-- Exact numerical row invariant for an arbitrary number of physical carries. -/
theorem iterate_number (q tmp : Fin R) (ps : List (Digit R))
    (huniq : (q::tmp::used ps).Nodup) (s : TapeStore R B) (hv : Valid q ps s)
    (hq : 1<s.reg q) (n : ℕ) :
    Nat.ofDigits (s.reg q) (readings ps ((nextStore q tmp ps)^[n] s))=
      (Nat.ofDigits (s.reg q) (readings ps s)+n)%(s.reg q)^ps.length := by
  induction n with
  | zero =>
    have hb := Nat.ofDigits_lt_base_pow_length hq (readings_bounded q ps s hv)
    simpa [readings] using (Nat.mod_eq_of_lt hb).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hn := iterate_radix q tmp ps huniq s n
    have hi := program_number q tmp ps huniq _ (iterate_valid q tmp ps huniq s hv n) (by omega)
    rw [hn] at hi
    rw [hi,ih]
    simp only [Nat.mod_add_mod,Nat.add_assoc]

theorem labels_eq (ps : List (Digit R)) : labels ps=21*ps.length+1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [labels,List.length_cons,ih]; omega

theorem initializeLabels_eq (ps : List (Digit R)) : initializeLabels ps=15*ps.length+1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [initializeLabels,List.length_cons,ih]; omega

theorem used_mem_iff (ps : List (Digit R)) (j : Fin R) :
    j∈used ps ↔ ∃ p∈ps,j=p.1 ∨ j=p.2 := by
  induction ps with
  | nil => simp [used]
  | cons p ps ih => simp [used,ih,or_assoc]

theorem nextStore_tmp_le (q tmp : Fin R) (ps : List (Digit R))
    (s : TapeStore R B) (ht : tmp∉used ps) :
    (nextStore q tmp ps s).reg tmp ≤ s.reg tmp := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [used,List.mem_cons,not_or] at ht
    rw [nextStore]
    split
    · have hh := ih (resetStore q tmp p s) ht.2.2
      have hh' : (nextStore q tmp ps (resetStore q tmp p s)).reg tmp ≤ 0 := by
        simpa [resetStore,TapeStore.setReg] using hh
      exact hh'.trans (Nat.zero_le _)
    · simp [advanceStore,TapeStore.setReg,ht.1,ht.2.1]

/-- Canonical digits never require a growing caller counter envelope. -/
theorem nextStore_bound (q tmp : Fin R) (ps : List (Digit R))
    (huniq : (q::tmp::used ps).Nodup) (s : TapeStore R B) (hv : Valid q ps s)
    (M : ℕ) (hs : ∀ j,s.reg j ≤ M) : ∀ j,(nextStore q tmp ps s).reg j ≤ M := by
  have hqt : q≠tmp := by
    intro he; exact (List.nodup_cons.mp huniq).1 (by simp [he])
  have hqps : q∉used ps := by
    intro he; exact (List.nodup_cons.mp huniq).1 (by simp [he])
  have htps : tmp∉used ps := (List.nodup_cons.mp (List.nodup_cons.mp huniq).2).1
  have hvnext := program_valid q tmp ps huniq s hv
  have hqnext := nextStore_fresh q tmp ps s q hqt hqps
  intro j
  by_cases ht : j=tmp
  · subst j
    exact (nextStore_tmp_le q tmp ps s htps).trans (hs tmp)
  by_cases hj : j∈used ps
  · obtain ⟨p,hp,hj⟩ := (used_mem_iff ps j).mp hj
    have hpair := hvnext p hp
    rw [hqnext] at hpair
    have hbound := hs q
    rcases hj with rfl|rfl <;> omega
  · rw [nextStore_fresh q tmp ps s j ht hj]
    exact hs j

theorem program_stops_valid (q tmp : Fin R) (ps : List (Digit R))
    (huniq : (q::tmp::used ps).Nodup) (inp : Inputs)
    (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M) (hv : Valid q ps s) :
    ∃ t e, t  ≤  ps.length*(8*M+20) ∧
      (program q tmp ps).Stops inp (s.toCfg (program (B := B) q tmp ps).entry) t e ∧
      e.store=nextStore q tmp ps s ∧ ∀ j,e.reg j ≤ M := by
  obtain ⟨t,e,ht,he,hes,heb⟩ := program_stops q tmp ps huniq inp M s hs
  refine ⟨t,e,ht,he,hes,?_⟩
  change ∀ j,e.store.reg j ≤ M
  rw [hes]
  exact nextStore_bound q tmp ps huniq s hv M hs

#print axioms program_stops_valid

#print axioms canonical_digits
#print axioms iterate_number

#print axioms successor_number
#print axioms program_number

#print axioms program_valid
#print axioms iterate_valid

#print axioms initialize_stops
#print axioms initializeStore_valid

#print axioms program_stops
#print axioms program_readings
end SamplerOdometer
end ExpandingCodes.Computation
