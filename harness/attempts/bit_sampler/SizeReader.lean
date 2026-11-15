import ExpandingCodes.Computation.TapeMacros

set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB
namespace SizeReader
variable {R B : ℕ}

/-- A three-label source scanner counts consecutive input ones and consumes
one delimiter. Every iteration inspects only the current RO0 symbol. -/
def scan (r : Fin R) : TapeProgram R B 3 where
  entry := 0
  code j := if j = 0 then .read 0 (fun s => if s = .one then 1 else 2)
    else if j = 1 then .inc r 0 else .halt

def scanStore (r : Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B :=
  { d.setReg r (d.reg r+n) with
    roHead := Function.update d.roHead 0 (d.roHead 0+n+1) }

 theorem scan_stops (r : Fin R) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hones : ∀ j, j < n → Machine.readRO inp.input (d.roHead 0+j) = .one)
    (hend : Machine.readRO inp.input (d.roHead 0+n) ≠ .one) :
    (scan r).Stops inp (d.toCfg 0) (2*n+1) ((scanStore r n d).toCfg 2) := by
  induction n generalizing d with
  | zero =>
    have hz : Machine.readRO inp.input (d.roHead 0) ≠ .one := by simpa using hend
    constructor
    · apply TapeProgram.Exec.one
      · simp [TapeProgram.halted, scan]
      · simp [TapeProgram.step, scan, scanStore, TapeStore.toCfg, TapeStore.setReg, Inputs.get, hz]
    · simp [TapeProgram.halted, scan]
  | succ n ih =>
    let d₁ : TapeStore R B := { d with roHead := Function.update d.roHead 0 (d.roHead 0+1) }
    let d₂ := d₁.setReg r (d.reg r+1)
    have hfirst : Machine.readRO inp.input (d.roHead 0) = .one := by simpa using hones 0 (by omega)
    have hones₂ : ∀ j, j < n → Machine.readRO inp.input (d₂.roHead 0+j) = .one := by
      intro j hj
      have h := hones (j+1) (by omega)
      simpa [d₂, d₁, TapeStore.setReg, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have hend₂ : Machine.readRO inp.input (d₂.roHead 0+n) ≠ .one := by
      simpa [d₂, d₁, TapeStore.setReg, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend
    have ht := ih d₂ hones₂ hend₂
    have hs₁ : (scan r).step inp (d.toCfg 0) = d₁.toCfg 1 := by
      simp [TapeProgram.step, scan, TapeStore.toCfg, d₁, Inputs.get, hfirst]
    have hs₂ : (scan r).step inp (d₁.toCfg 1) = d₂.toCfg 0 := by
      simp [TapeProgram.step, scan, TapeStore.toCfg, TapeStore.setReg, d₁, d₂]
    have hpost : scanStore r n d₂ = scanStore r (n+1) d := by
      simp [scanStore, d₂, d₁, TapeStore.setReg, Function.update_idem,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    constructor
    · have h := TapeProgram.Exec.step (by simp [TapeProgram.halted, scan]) hs₁
        (TapeProgram.Exec.step (by simp [TapeProgram.halted, scan]) hs₂ ht.exec)
      simpa [hpost, Nat.mul_succ, Nat.add_assoc] using h
    · simp [TapeProgram.halted, scan]

/-- Clear one runtime unary size register and then scan the input prefix. -/
def sizeInput (r : Fin R) : TapeProgram R B 5 :=
  TapeProgram.seq (TapeMacros.clear r) (scan r)

def sizeStore (r : Fin R) (n : ℕ) (d : TapeStore R B) : TapeStore R B :=
  { d.setReg r n with roHead := Function.update d.roHead 0 (d.roHead 0+n+1) }

 theorem sizeInput_stops (r : Fin R) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hones : ∀ j, j < n → Machine.readRO inp.input (d.roHead 0+j) = .one)
    (hend : Machine.readRO inp.input (d.roHead 0+n) ≠ .one) :
    (sizeInput r).Stops inp (d.toCfg (sizeInput (B := B) r).entry) (d.reg r+2*n+3)
      ((sizeStore r n d).toCfg (2 : Fin 3) |>.mapPC (TapeProgram.rightLabel 2)) := by
  have hc := TapeMacros.clear_stops r inp (d.reg r) d rfl
  have hs := scan_stops r inp n (d.setReg r 0) hones hend
  have hall := hc.seq hs
  convert hall using 1 <;> first | rfl | simp [scanStore, sizeStore, TapeStore.setReg, Function.update_idem] | omega

theorem sizeInput_unary (r : Fin R) (inp : Inputs) (n : ℕ) (tail : List Bool)
    (d : TapeStore R B) (hh : d.roHead 0 = 0)
    (hi : inp.input = List.replicate n true ++ false :: tail) :
    (sizeInput r).Stops inp (d.toCfg (sizeInput (B := B) r).entry) (d.reg r+2*n+3)
      ((sizeStore r n d).toCfg (2 : Fin 3) |>.mapPC (TapeProgram.rightLabel 2)) := by
  apply sizeInput_stops
  · intro j hj
    simp only [hi, hh, Nat.zero_add, Machine.readRO]
    rw [List.getElem?_append_left (by simpa using hj), List.getElem?_replicate]
    simp [hj, Sym.ofBool]
  · simp only [hi, hh, Nat.zero_add, Machine.readRO]
    rw [List.getElem?_append_right (by simp : (List.replicate n true).length ≤ n)]
    simp [Sym.ofBool]

#print axioms sizeInput_unary
#print axioms scan_stops
#print axioms sizeInput_stops

end SizeReader
end ExpandingCodes.Computation
