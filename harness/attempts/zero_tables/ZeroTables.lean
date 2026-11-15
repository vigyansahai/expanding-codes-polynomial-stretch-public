import ExpandingCodes.Computation.TapeArrays

set_option autoImplicit false

namespace ExpandingCodes.Computation.ZeroTables
open NKtLB TapeArrays
variable {R B K : ℕ}

/-- The existing three-label physical zero writer consumes a runtime cell
count. Neither table length nor field width occurs in the code parameters. -/
def program (r : Fin R) (b : Fin B) : TapeProgram R B 3 := writeRun r b .zero

def result (r : Fin R) (b : Fin B) (N : ℕ) (d : TapeStore R B) : TapeStore R B :=
  fillStore b .zero N (d.setReg r 0)

theorem result_reg (r : Fin R) (b : Fin B) (N : ℕ) (d : TapeStore R B) :
    (result r b N d).reg = Function.update d.reg r 0 := by
  rw [result,fillStore_reg]
  rfl

theorem result_head (r : Fin R) (b : Fin B) (N : ℕ) (d : TapeStore R B)
    (hh : d.bufferHead b = 1) :
    (result r b N d).bufferHead = Function.update d.bufferHead b (1+N) := by
  rw [result,fillStore_head]
  simpa only [TapeStore.setReg,hh]

theorem result_symbol (r : Fin R) (b : Fin B) (N : ℕ) (d : TapeStore R B)
    (hh : d.bufferHead b = 1) (c : Fin B) (j : ℕ) :
    ((result r b N d).bufferTape c).getD j .blank =
      if c = b ∧ 1 ≤ j ∧ j < 1+N then .zero else (d.bufferTape c).getD j .blank := by
  rw [result,fillStore_symbol]
  simp only [TapeStore.setReg,hh]

theorem result_table (r : Fin R) (b : Fin B) (width : ℕ) (d : TapeStore R B)
    (hh : d.bufferHead b = 1) :
    ThermometerTable (result r b (K*width) d) b width (fun _ : Fin K => 0) := by
  intro i
  refine ⟨Nat.zero_le _,?_⟩
  intro j hj
  have hlow : 1 ≤ entryOffset i.val width+j := by unfold entryOffset; omega
  have hrow : (i.val+1)*width ≤ K*width := Nat.mul_le_mul_right width i.isLt
  have hhigh : entryOffset i.val width+j < 1+K*width := by
    unfold entryOffset
    rw [Nat.add_mul,Nat.one_mul] at hrow
    omega
  rw [result_symbol r b (K*width) d hh]
  simp [hlow,hhigh]

theorem result_bottomMarked (r : Fin R) (b : Fin B) (N : ℕ) (d : TapeStore R B)
    (hh : d.bufferHead b = 1) (hm : BottomMarked d b) : BottomMarked (result r b N d) b := by
  constructor
  · rw [result_symbol r b N d hh]
    simpa using hm.1
  · intro j hj
    rw [result_symbol r b N d hh]
    split_ifs
    · decide
    · exact hm.2 j hj

theorem result_other_symbol (r : Fin R) (b : Fin B) (N : ℕ) (d : TapeStore R B)
    (c : Fin B) (hc : c ≠ b) (j : ℕ) :
    ((result r b N d).bufferTape c).getD j .blank = (d.bufferTape c).getD j .blank := by
  rw [result,fillStore_symbol]
  simp [hc,TapeStore.setReg]

theorem result_other_table {L : ℕ} (r : Fin R) (b : Fin B) (N : ℕ) (d : TapeStore R B)
    (c : Fin B) (hc : c ≠ b) (width : ℕ) (values : Fin L → ℕ)
    (h : ThermometerTable d c width values) :
    ThermometerTable (result r b N d) c width values := by
  intro i
  refine ⟨(h i).1,?_⟩
  intro j hj
  rw [result_other_symbol r b N d c hc]
  exact (h i).2 j hj

theorem program_stops (r : Fin R) (b : Fin B) (N : ℕ) (inp : Inputs) (d : TapeStore R B)
    (hn : d.reg r = N) :
    (program r b).Stops inp (d.toCfg 0) (2*N+1) ((result r b N d).toCfg 2) :=
  writeRun_stops r b .zero inp N d hn

theorem result_bound (r : Fin R) (b : Fin B) (N : ℕ) (d : TapeStore R B) (M : ℕ)
    (hd : ∀ j, d.reg j ≤ M) : ∀ j, (result r b N d).reg j ≤ M := by
  intro j
  rw [result_reg]
  by_cases hj : j = r
  · subst j
    simp
  · simpa [Function.update_of_ne hj] using hd j

theorem result_payload (r : Fin R) (b : Fin B) (N : ℕ) (d : TapeStore R B) :
    (result r b N d).roHead = d.roHead ∧ (result r b N d).output = d.output := by
  exact ⟨fillStore_roHead b .zero N (d.setReg r 0),fillStore_output b .zero N (d.setReg r 0)⟩

#print axioms result_table
#print axioms program_stops
#print axioms result_other_table
end ExpandingCodes.Computation.ZeroTables
