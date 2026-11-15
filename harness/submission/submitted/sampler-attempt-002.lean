import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime
import Mathlib
import Theorems.Thm_ExpandingCodes_Computation_SamplerAssembly_prelude_stops
import Theorems.Thm_ExpandingCodes_Computation_SamplerProgram_layer_stops
import Theorems.Thm_ExpandingCodes_Computation_TapeCompiler_compile_halts

set_option autoImplicit false
open scoped Classical BigOperators


section FlattenModule0


set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch























end ExpandingCodes.PolynomialStretch

end FlattenModule0

/-! Inlined whole module: ExpandingCodes.Computation.BinaryPolynomial -/
section FlattenModule1





set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch.BinaryPolynomial

open Polynomial





























theorem indexEquiv_inverse_value (ell : ℕ) (c : Coefficients ell) :
    ((indexEquiv ell).symm c).val = ∑ j : Fin ell, (c j).val * 2 ^ j.val := rfl
































































































































































































end ExpandingCodes.PolynomialStretch.BinaryPolynomial

end FlattenModule1

/-! Inlined whole module: ExpandingCodes.Computation.BinaryField -/
section FlattenModule2


set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch.BinaryField

open Polynomial BinaryPolynomial

































































theorem polynomial_add {ell : ℕ} (a b : Coefficients ell) :
    polynomial (add a b) = polynomial a + polynomial b := by
  simp only [polynomial, add, map_add, Finset.sum_add_distrib]

theorem decode_add (ell : ℕ) (h : 0 < ell) (a b : Coefficients ell) :
    decode ell h (add a b) = decode ell h a + decode ell h b := by
  simp only [decode, polynomial_add, map_add]







































































































































































































theorem multiply_inverse (ell : ℕ) (h : 0 < ell) (x : Coefficients ell)
    (hx : x ≠ zero ell) :
    multiply ell h (selectedIndex ell h) x (inverse ell h x) = one ell := by
  unfold inverse
  rw [dif_neg hx]
  have hmem := Finset.min'_mem
    (Finset.univ.filter (fun i : Fin (2 ^ ell) =>
      multiply ell h (selectedIndex ell h) x (indexEquiv ell i) = one ell))
    (by
      obtain ⟨i, hi⟩ := exists_inverseIndex ell h x hx
      exact ⟨i, by simpa using hi⟩)
  exact (Finset.mem_filter.mp hmem).2

theorem decode_inverse (ell : ℕ) (h : 0 < ell) (x : Coefficients ell) :
    decode ell h (inverse ell h x) = (decode ell h x)⁻¹ := by
  by_cases hx : x = zero ell
  · subst x
    simp [inverse, decode_zero]
  · have hm := congrArg (decode ell h) (multiply_inverse ell h x hx)
    rw [decode_multiply, decode_one] at hm
    exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hm)







theorem elements_addIndex (ell : ℕ) (h : 0 < ell) (i j : Fin (2 ^ ell)) :
    elements ell h (addIndex ell i j) = elements ell h i + elements ell h j := by
  change decode ell h (indexEquiv ell ((indexEquiv ell).symm
    (add (indexEquiv ell i) (indexEquiv ell j)))) = _
  rw [Equiv.apply_symm_apply, decode_add]
  rfl

theorem elements_multiplyIndex (ell : ℕ) (h : 0 < ell) (i j : Fin (2 ^ ell)) :
    elements ell h (multiplyIndex ell h (selectedIndex ell h) (indexEquiv ell i)
      (indexEquiv ell j)) = elements ell h i * elements ell h j := by
  exact decode_multiply ell h (indexEquiv ell i) (indexEquiv ell j)

theorem elements_inverseIndex (ell : ℕ) (h : 0 < ell) (i : Fin (2 ^ ell)) :
    elements ell h (inverseIndex ell h i) = (elements ell h i)⁻¹ := by
  change decode ell h (indexEquiv ell ((indexEquiv ell).symm
    (inverse ell h (indexEquiv ell i)))) = _
  rw [Equiv.apply_symm_apply]
  exact decode_inverse ell h (indexEquiv ell i)

























































end ExpandingCodes.PolynomialStretch.BinaryField

end FlattenModule2

/-! Inlined whole module: ExpandingCodes.Construction.Geometry -/
section FlattenModule3



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch





theorem fieldSize_pos (d n : ℕ) : 0 < fieldSize d n := by
  exact pow_pos (by decide) _

theorem fieldSize_ge_two (d n : ℕ) : 2 ≤ fieldSize d n := by
  unfold fieldSize
  have h := fieldExponent_pos d n
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ fieldExponent d n := Nat.pow_le_pow_right (by decide) h



























end ExpandingCodes.PolynomialStretch

end FlattenModule3

/-! Inlined whole module: ExpandingCodes.Construction.BinaryGeometry -/
section FlattenModule4



set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch

















theorem binaryGeometry_rowOrder (d n : ℕ) (i : Fin (rowCount d n)) (j : Fin d) :
    (binaryGeometry d n).rowOrder i j = BinaryField.elements (fieldExponent d n)
      (fieldExponent_pos d n) (finFunctionFinEquiv.symm i j) := rfl

end ExpandingCodes.PolynomialStretch

end FlattenModule4


section FlattenModule5


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB


























namespace TapeProgram
variable {R B L : ℕ}



















































 



 








 



 





end TapeProgram
end ExpandingCodes.Computation

end FlattenModule5


section FlattenModule6


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB





















namespace CounterProgram
variable {R L : ℕ}











































 



 








 



 





end CounterProgram
end ExpandingCodes.Computation

end FlattenModule6

/-! Inlined whole module: ExpandingCodes.Computation.CounterTape -/
section FlattenModule7


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB





 



















 





 







@[simp] theorem unary_zero (n : ℕ) : unary n 0 = .bot := by simp [unary]
@[simp] theorem unary_self_succ (n : ℕ) : unary (n+1) (n+1) = .one := by simp [unary]
@[simp] theorem unary_after (n : ℕ) : unary n (n+1) = .blank := by simp [unary]

 







 







 


























































 





 












end ExpandingCodes.Computation

end FlattenModule7

/-! Inlined whole module: ExpandingCodes.Computation.Basic -/
section FlattenModule8


set_option autoImplicit false
open scoped Classical

namespace NKtLB.Machine

theorem step_of_halt (M : NKtLB.Machine) (O : Set (List Bool)) (inp : Inputs)
    (c : Cfg M) (hc : c.state = M.halt) : M.step O inp c = c := by
  simp [step, hc]

theorem run_succ (M : NKtLB.Machine) (O : Set (List Bool)) (inp : Inputs) (t : ℕ) :
    M.run O inp (t + 1) = M.step O inp (M.run O inp t) := by
  exact Function.iterate_succ_apply' _ _ _

theorem run_add (M : NKtLB.Machine) (O : Set (List Bool)) (inp : Inputs) (t s : ℕ) :
    M.run O inp (t + s) = (M.step O inp)^[s] (M.run O inp t) := by
  simpa only [run, Nat.add_comm t s] using Function.iterate_add_apply (M.step O inp) s t M.init

theorem run_stable_of_halt (M : NKtLB.Machine) (O : Set (List Bool)) (inp : Inputs)
    (t : ℕ) (ht : (M.run O inp t).state = M.halt) (s : ℕ) :
    M.run O inp (t + s) = M.run O inp t := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.add_succ, run_succ, ih, step_of_halt M O inp _ ht]

theorem HaltsWith.mono {M : NKtLB.Machine} {O : Set (List Bool)} {inp : Inputs}
    {t T : ℕ} {z : List Sym} (h : M.HaltsWith O inp t z) (ht : t ≤ T) :
    M.HaltsWith O inp T z := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
  simpa only [HaltsWith, run_stable_of_halt M O inp t h.1 s] using h

theorem HaltsWith.output_unique {M : NKtLB.Machine} {O : Set (List Bool)} {inp : Inputs}
    {t T : ℕ} {z z' : List Sym} (h : M.HaltsWith O inp t z)
    (h' : M.HaltsWith O inp T z') : z = z' := by
  rcases le_total t T with hle | hle
  · exact (h.mono hle).2.symm.trans h'.2
  · exact h.2.symm.trans (h'.mono hle).2

theorem Computes.mono {M : NKtLB.Machine} {t T : ℕ} {u v : List Bool}
    (h : M.Computes t u v) (ht : t ≤ T) : M.Computes T u v :=
  HaltsWith.mono h ht

theorem bitsSym_injective : Function.Injective bitsSym := by
  apply List.map_injective_iff.mpr
  intro a b h
  cases a <;> cases b <;> simp_all [Sym.ofBool]

theorem Computes.output_unique {M : NKtLB.Machine} {t T : ℕ} {u v v' : List Bool}
    (h : M.Computes t u v) (h' : M.Computes T u v') : v = v' :=
  bitsSym_injective (HaltsWith.output_unique h h')

end NKtLB.Machine

end FlattenModule8

/-! Inlined whole module: ExpandingCodes.Computation.CounterCompiler -/
section FlattenModule9




set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB





namespace CounterCompiler
variable {R L : ℕ}










def workIdx (r : Fin R) : Fin (R+2) := ⟨r.val, by omega⟩

























































 




 










 



 































 




 












 












































 







 



























 




























 





 


 










 




























@[simp] theorem workIdx_eq_iff (r s : Fin R) : workIdx r = workIdx s ↔ r = s := by
  simp [workIdx, Fin.ext_iff]

 






























 











































 

















 




 




































 












































 








end CounterCompiler
end ExpandingCodes.Computation

end FlattenModule9

/-! Inlined whole module: ExpandingCodes.Computation.TapeCompiler -/
section FlattenModule10



set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace TapeCompiler
open CounterCompiler (controlEquiv startControl haltControl queryControl normal finish
  getD_append_singleton )
variable {R B L : ℕ}







 





 


 





 


@[simp] theorem bufferIdx_eq_iff (b c : Fin B) : bufferIdx R b = bufferIdx R c ↔ b = c := by
  simp [bufferIdx, Fin.ext_iff]




























































 




 










 



 


































 




 












 

















































 







 
































 

































 





 


 

































@[simp] theorem workIdx_eq_iff (r s : Fin R) : workIdx B r = workIdx B s ↔ r = s := by
  simp [workIdx, Fin.ext_iff]

 



































 
















































 

















 
























































































 













































 








end TapeCompiler
end ExpandingCodes.Computation

end FlattenModule10

/-! Inlined whole module: ExpandingCodes.Computation.TapeLoops -/
section FlattenModule11


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB









namespace TapeCfg
variable {R B L K : ℕ}





end TapeCfg

namespace TapeStore
variable {R B L : ℕ}




@[simp] theorem store_toCfg (d : TapeStore R B) (j : Fin L) : (d.toCfg j).store = d := by
  cases d
  rfl
end TapeStore

namespace TapeInstr
variable {R B L K : ℕ}











 theorem relabel_eq_halt (f : Fin L → Fin K) (i : TapeInstr R B L) :
    relabel f i = .halt ↔ i = .halt := by
  cases i <;> simp [relabel]
end TapeInstr

namespace TapeProgram
variable {R B L K : ℕ}















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

































end TapeProgram
end ExpandingCodes.Computation

end FlattenModule11

/-! Inlined whole module: ExpandingCodes.Computation.TapeMacros -/
section FlattenModule12


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace TapeStore
variable {R B : ℕ}





@[simp] theorem setReg_same (d : TapeStore R B) (r : Fin R) (m n : ℕ) :
    (d.setReg r m).setReg r n = d.setReg r n := by
  simp [setReg, Function.update_idem]

end TapeStore

namespace TapeMacros
variable {R B : ℕ}






 theorem increment_stops (r : Fin R) (inp : Inputs) (d : TapeStore R B) :
    (increment r).Stops inp (d.toCfg 0) 1 ((d.setReg r (d.reg r + 1)).toCfg 1) := by
  constructor
  · apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, increment, TapeStore.toCfg]
    · simp [TapeProgram.step, increment, TapeStore.toCfg, TapeStore.setReg]
  · simp [TapeProgram.halted, increment, TapeStore.toCfg]






 theorem clear_stops (r : Fin R) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hd : d.reg r = n) :
    (clear r).Stops inp (d.toCfg 0) (n+1) ((d.setReg r 0).toCfg 1) := by
  induction n generalizing d with
  | zero =>
    constructor
    · apply TapeProgram.Exec.one
      · simp [TapeProgram.halted, clear, TapeStore.toCfg]
      · have he : d.setReg r 0 = d := by
          simp [TapeStore.setReg, ← hd]
        simp [TapeProgram.step, clear, TapeStore.toCfg, hd, he]
    · simp [TapeProgram.halted, clear, TapeStore.toCfg]
  | succ n ih =>
    let e := d.setReg r n
    have he : e.reg r = n := by simp [e, TapeStore.setReg]
    have hstop := ih e he
    have hs : (clear r).step inp (d.toCfg 0) = e.toCfg 0 := by
      simp [TapeProgram.step, clear, TapeStore.toCfg, TapeStore.setReg, e, hd]
    constructor
    · simpa [e] using TapeProgram.Exec.step
        (by simp [TapeProgram.halted, clear, TapeStore.toCfg]) hs hstop.exec
    · simp [TapeProgram.halted, clear, TapeStore.toCfg]











 theorem transferStore_step (d : TapeStore R B) (src dst : Fin R) (hne : src ≠ dst)
    (n : ℕ) (hd : d.reg src = n+1) :
    transferStore ((d.setReg src n).setReg dst (d.reg dst+1)) src dst =
      transferStore d src dst := by
  simp only [transferStore, TapeStore.setReg]
  congr 1
  funext j
  by_cases hj : j = dst
  · subst j
    simp [Function.update, hne, Ne.symm hne, hd]
    omega
  · simp only [Function.update_of_ne hj]
    by_cases hs : j = src
    · subst j
      simp [Function.update_of_ne hne]
    · simp [Function.update_of_ne hs, Function.update_of_ne hj]

 theorem transfer_stops (src dst : Fin R) (hne : src ≠ dst) (inp : Inputs)
    (n : ℕ) (d : TapeStore R B) (hd : d.reg src = n) :
    (transfer src dst).Stops inp (d.toCfg 0) (2*n+1) ((transferStore d src dst).toCfg 2) := by
  induction n generalizing d with
  | zero =>
    have he : transferStore d src dst = d := by
      have hc : d.setReg src 0 = d := by simp [TapeStore.setReg, ← hd]
      unfold transferStore
      rw [hc]
      simp [hd, TapeStore.setReg]
    constructor
    · apply TapeProgram.Exec.one
      · simp [TapeProgram.halted, transfer, TapeStore.toCfg]
      · simp [TapeProgram.step, transfer, TapeStore.toCfg, hd, he]
    · simp [TapeProgram.halted, transfer, TapeStore.toCfg]
  | succ n ih =>
    let d₁ := d.setReg src n
    let e := d₁.setReg dst (d.reg dst+1)
    have he : e.reg src = n := by simp [e, d₁, TapeStore.setReg, hne]
    have htail := ih e he
    have hs₁ : (transfer src dst).step inp (d.toCfg 0) = d₁.toCfg 1 := by
      simp [TapeProgram.step, transfer, TapeStore.toCfg, TapeStore.setReg, d₁, hd]
    have hs₂ : (transfer src dst).step inp (d₁.toCfg 1) = e.toCfg 0 := by
      simp [TapeProgram.step, transfer, TapeStore.toCfg, TapeStore.setReg, e, d₁,
        Function.update_of_ne (Ne.symm hne)]
    have hpost : transferStore e src dst = transferStore d src dst :=
      transferStore_step d src dst hne n hd
    constructor
    · have h := TapeProgram.Exec.step
        (by simp [TapeProgram.halted, transfer, TapeStore.toCfg]) hs₁
        (TapeProgram.Exec.step (by simp [TapeProgram.halted, transfer, TapeStore.toCfg]) hs₂ htail.exec)
      simpa [hpost, Nat.mul_succ, Nat.add_assoc] using h
    · simp [TapeProgram.halted, transfer, TapeStore.toCfg]










 theorem distributeStore_step (d : TapeStore R B) (src dst tmp : Fin R)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (n : ℕ) (hd : d.reg src = n+1) :
    distributeStore (((d.setReg src n).setReg dst (d.reg dst+1)).setReg tmp (d.reg tmp+1)) src dst tmp =
      distributeStore d src dst tmp := by
  simp only [distributeStore, TapeStore.setReg]
  congr 1
  funext j
  by_cases ht : j = tmp
  · subst j
    simp [Function.update, hsd, hst, hdt, Ne.symm hsd, Ne.symm hst, Ne.symm hdt, hd]
    omega
  · simp only [Function.update_of_ne ht]
    by_cases hd' : j = dst
    · subst j
      simp [Function.update, hsd, hst, hdt, Ne.symm hsd, Ne.symm hst, Ne.symm hdt, hd]
      omega
    · simp only [Function.update_of_ne hd']
      by_cases hs : j = src
      · subst j
        simp [Function.update, hsd, hst, hdt]
      · simp [Function.update, hs, hd', ht]

 theorem distribute_stops (src dst tmp : Fin R)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp) (inp : Inputs)
    (n : ℕ) (d : TapeStore R B) (hd : d.reg src = n) :
    (distribute src dst tmp).Stops inp (d.toCfg 0) (3*n+1)
      ((distributeStore d src dst tmp).toCfg 3) := by
  induction n generalizing d with
  | zero =>
    have he : distributeStore d src dst tmp = d := by
      have hc : d.setReg src 0 = d := by simp [TapeStore.setReg, ← hd]
      unfold distributeStore
      rw [hc]
      simp [hd, TapeStore.setReg]
    constructor
    · apply TapeProgram.Exec.one
      · simp [TapeProgram.halted, distribute]
      · simp [TapeProgram.step, distribute, TapeStore.toCfg, hd, he]
    · simp [TapeProgram.halted, distribute]
  | succ n ih =>
    let d₁ := d.setReg src n
    let d₂ := d₁.setReg dst (d.reg dst+1)
    let e := d₂.setReg tmp (d.reg tmp+1)
    have he : e.reg src = n := by simp [e, d₂, d₁, TapeStore.setReg, hsd, hst]
    have htail := ih e he
    have hs₁ : (distribute src dst tmp).step inp (d.toCfg 0) = d₁.toCfg 1 := by
      simp [TapeProgram.step, distribute, TapeStore.toCfg, TapeStore.setReg, d₁, hd]
    have hs₂ : (distribute src dst tmp).step inp (d₁.toCfg 1) = d₂.toCfg 2 := by
      simp [TapeProgram.step, distribute, TapeStore.toCfg, TapeStore.setReg, d₂, d₁,
        Function.update_of_ne (Ne.symm hsd)]
    have hs₃ : (distribute src dst tmp).step inp (d₂.toCfg 2) = e.toCfg 0 := by
      simp [TapeProgram.step, distribute, TapeStore.toCfg, TapeStore.setReg, e, d₂, d₁,
        Function.update_of_ne (Ne.symm hst), Function.update_of_ne (Ne.symm hdt)]
    have hpost : distributeStore e src dst tmp = distributeStore d src dst tmp :=
      distributeStore_step d src dst tmp hsd hst hdt n hd
    constructor
    · have h := TapeProgram.Exec.step (by simp [TapeProgram.halted, distribute]) hs₁
        (TapeProgram.Exec.step (by simp [TapeProgram.halted, distribute]) hs₂
          (TapeProgram.Exec.step (by simp [TapeProgram.halted, distribute]) hs₃ htail.exec))
      simpa [hpost, Nat.mul_succ, Nat.add_assoc] using h
    · simp [TapeProgram.halted, distribute]







 theorem copy_post (d : TapeStore R B) (src dst tmp : Fin R)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp) :
    transferStore (distributeStore ((d.setReg dst 0).setReg tmp 0) src dst tmp) tmp src =
      (d.setReg dst (d.reg src)).setReg tmp 0 := by
  simp only [transferStore, distributeStore, TapeStore.setReg]
  congr 1
  funext j
  by_cases hs : j = src
  · subst j
    simp [Function.update, hsd, hst, hdt, Ne.symm hsd, Ne.symm hst, Ne.symm hdt]
  · by_cases ht : j = tmp
    · subst j
      simp [Function.update, hsd, hst, hdt, Ne.symm hsd, Ne.symm hst, Ne.symm hdt]
    · by_cases hd : j = dst
      · subst j
        simp [Function.update, hsd, hst, hdt, Ne.symm hsd, Ne.symm hst, Ne.symm hdt]
      · simp [Function.update, hs, ht, hd]

 theorem copy_stops (src dst tmp : Fin R)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (copy src dst tmp).Stops inp (d.toCfg (copy (B := B) src dst tmp).entry)
      (d.reg dst + d.reg tmp + 5*d.reg src + 7) e ∧
      e.store = (d.setReg dst (d.reg src)).setReg tmp 0 := by
  let d₁ := d.setReg dst 0
  let d₂ := d₁.setReg tmp 0
  let d₃ := distributeStore d₂ src dst tmp
  have h₁ := clear_stops dst inp (d.reg dst) d rfl
  have h₂ := clear_stops tmp inp (d.reg tmp) d₁ (by simp [d₁, TapeStore.setReg, Ne.symm hdt])
  have h₃ := distribute_stops src dst tmp hsd hst hdt inp (d.reg src) d₂
    (by simp [d₂, d₁, TapeStore.setReg, hsd, hst])
  have hreg : d₃.reg tmp = d.reg src := by
    simp [d₃, d₂, d₁, distributeStore, TapeStore.setReg, hsd, hst, hdt]
  have h₄ := transfer_stops tmp src (Ne.symm hst) inp (d.reg src) d₃ hreg
  have h₁₂ := h₁.seq h₂
  have h₁₂₃ := h₁₂.seq h₃
  have hall := h₁₂₃.seq h₄
  refine ⟨((transferStore d₃ tmp src).toCfg (2 : Fin 3)).mapPC (TapeProgram.rightLabel 8), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change transferStore d₃ tmp src = _
    exact copy_post d src dst tmp hsd hst hdt





 

















 































 





















end TapeMacros
end ExpandingCodes.Computation

end FlattenModule12

/-! Inlined whole module: ExpandingCodes.Computation.UnaryArithmetic -/
section FlattenModule13


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace UnaryArithmetic
variable {R B : ℕ}

@[simp] theorem setReg_self (d : TapeStore R B) (r : Fin R) :
    d.setReg r (d.reg r) = d := by simp [TapeStore.setReg]

@[simp] theorem reg_set_same (d : TapeStore R B) (r : Fin R) (n : ℕ) :
    (d.setReg r n).reg r = n := by simp [TapeStore.setReg]




theorem setReg_comm (d : TapeStore R B) (r s : Fin R) (m n : ℕ) (h : r ≠ s) :
    (d.setReg r m).setReg s n = (d.setReg s n).setReg r m := by
  simp only [TapeStore.setReg]
  congr 1
  exact Function.update_comm h m n d.reg









































































































































































































































































end UnaryArithmetic
end ExpandingCodes.Computation

end FlattenModule13

/-! Inlined whole module: ExpandingCodes.Computation.TapeArrays -/
section FlattenModule14



set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace TapeStore
variable {R B : ℕ}








 


 



 

end TapeStore

namespace TapeArrays
variable {R B : ℕ}
open TapeMacros






 












@[simp] theorem moved_reg (d : TapeStore R B) (b : Fin B) (m : Move) :
    (moved d b m).reg = d.reg := rfl

@[simp] theorem moved_head (d : TapeStore R B) (b : Fin B) (m : Move) :
    (moved d b m).bufferHead = Function.update d.bufferHead b (Machine.moveHead m (d.bufferHead b)) := rfl








 















































 





























































 





























 






















 








 









 










 



















































 





 





 





 







 


































 



































 




























































 



















 




 






 



 



 













 










































 








 





 









 































 































































 
























 














 




































































 































 














 





























































 

























































 


 








 















 


















































end TapeArrays
end ExpandingCodes.Computation





















end FlattenModule14

/-! Inlined whole module: ExpandingCodes.Computation.TapeControl -/
section FlattenModule15


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB
namespace TapeProgram
variable {R B L K : ℕ}



















theorem branchZero_left (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (i : Fin L) : (branchZero r P Q).code (branchLeft K i) =
      (P.code i).relabel (branchLeft K) := by
  simp [branchZero, branchLeft, leftLabel]

theorem branchZero_right (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (i : Fin K) : (branchZero r P Q).code (branchRight L i) =
      (Q.code i).relabel (branchRight L) := by
  simp [branchZero, branchRight, leftLabel, rightLabel]

theorem branchZero_test (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K) :
    (branchZero r P Q).code (branchTest L K) =
      .dec r (branchLeft K P.entry) (branchRestore L K) := by
  simp [branchZero, branchTest, rightLabel]

theorem branchZero_restore (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K) :
    (branchZero r P Q).code (branchRestore L K) = .inc r (branchRight L Q.entry) := by
  simp [branchZero, branchRestore, rightLabel]

theorem branchZero_stops_zero (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (inp : Inputs) (d : TapeStore R B) (hr : d.reg r = 0)
    {t : ℕ} {e : TapeCfg R B L} (hp : P.Stops inp (d.toCfg P.entry) t e) :
    (branchZero r P Q).Stops inp (d.toCfg (branchTest L K)) (1+t)
      (e.mapPC (branchLeft K)) := by
  have ht : (branchZero r P Q).Exec inp (d.toCfg (branchTest L K)) 1
      ((d.toCfg P.entry).mapPC (branchLeft K)) := by
    apply Exec.one
    · rw [halted, branchZero_test]
      simp
    · simp [step, branchZero_test, TapeStore.toCfg, TapeCfg.mapPC, hr]
  refine ⟨ht.trans (hp.exec.relabel (branchLeft K) (fun i _ => branchZero_left r P Q i)), ?_⟩
  change (branchZero r P Q).code (branchLeft K e.pc) = .halt
  rw [branchZero_left, hp.halted]
  rfl

theorem branchZero_stops_positive (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (inp : Inputs) (d : TapeStore R B) (hr : d.reg r ≠ 0)
    {t : ℕ} {e : TapeCfg R B K} (hq : Q.Stops inp (d.toCfg Q.entry) t e) :
    (branchZero r P Q).Stops inp (d.toCfg (branchTest L K)) (2+t)
      (e.mapPC (branchRight L)) := by
  let c := decStore r d
  have hs₁ : (branchZero r P Q).step inp (d.toCfg (branchTest L K)) =
      c.toCfg (branchRestore L K) := by
    simp [step, branchZero_test, TapeStore.toCfg, c, decStore, hr]
  have hs₂ : (branchZero r P Q).step inp (c.toCfg (branchRestore L K)) =
      (d.toCfg Q.entry).mapPC (branchRight L) := by
    have hr₁ : d.reg r-1+1 = d.reg r := Nat.sub_add_cancel (Nat.pos_of_ne_zero hr)
    simp [step, branchZero_restore, TapeStore.toCfg, TapeCfg.mapPC, c, decStore,
      Function.update_idem, hr₁, Function.update_eq_self]
  have ht : (branchZero r P Q).Exec inp (d.toCfg (branchTest L K)) 2
      ((d.toCfg Q.entry).mapPC (branchRight L)) := by
    exact Exec.step (by rw [halted, branchZero_test]; simp) hs₁
      (Exec.one (by rw [halted, branchZero_restore]; simp) hs₂)
  refine ⟨ht.trans (hq.exec.relabel (branchRight L) (fun i _ => branchZero_right r P Q i)), ?_⟩
  change (branchZero r P Q).code (branchRight L e.pc) = .halt
  rw [branchZero_right, hq.halted]
  rfl

/-- A compositional bounded contract for the real branch transition table. -/
theorem branchZero_stops (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (inp : Inputs) (d f g : TapeStore R B) (A C : ℕ)
    (hp : ∃ t e, t ≤ A ∧ P.Stops inp (d.toCfg P.entry) t e ∧ e.store = f)
    (hq : ∃ t e, t ≤ C ∧ Q.Stops inp (d.toCfg Q.entry) t e ∧ e.store = g) :
    ∃ t e, t ≤ max A C + 2 ∧
      (branchZero r P Q).Stops inp (d.toCfg (branchZero r P Q).entry) t e ∧
      e.store = if d.reg r = 0 then f else g := by
  by_cases hr : d.reg r = 0
  · obtain ⟨t,e,ht,he,hes⟩ := hp
    refine ⟨1+t,e.mapPC (branchLeft K), ?_, branchZero_stops_zero r P Q inp d hr he, ?_⟩
    · have := le_max_left A C
      omega
    · simpa [hr] using hes
  · obtain ⟨t,e,ht,he,hes⟩ := hq
    refine ⟨2+t,e.mapPC (branchRight L), ?_, branchZero_stops_positive r P Q inp d hr he, ?_⟩
    · have := le_max_right A C
      omega
    · simpa [hr] using hes





theorem skip_stops (inp : Inputs) (d : TapeStore R B) :
    skip.Stops inp (d.toCfg (0 : Fin 1)) 0 (d.toCfg 0) :=
  ⟨Exec.refl _, rfl⟩




end TapeProgram
end ExpandingCodes.Computation

end FlattenModule15

/-! Inlined whole module: ExpandingCodes.Computation.FieldPrograms -/
section FlattenModule16


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace FieldPrograms
open UnaryArithmetic
variable {R B : ℕ}








































































































































































theorem setReg_bound (d : TapeStore R B) (r : Fin R) (n M : ℕ)
    (hd : ∀ j, d.reg j ≤ M) (hn : n ≤ M) : ∀ j, (d.setReg r n).reg j ≤ M := by
  intro j
  by_cases h : j = r
  · subst j; simpa using hn
  · simpa [TapeStore.setReg, h] using hd j



























































































































































end FieldPrograms
end ExpandingCodes.Computation

end FlattenModule16

/-! Inlined whole module: ExpandingCodes.Computation.ParameterPrograms -/
section FlattenModule17


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}











theorem raise_stops (r : Fin R) (c : ℕ) (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (raise r c).Stops inp (d.toCfg (raise (B := B) r c).entry) (2*c) e ∧
      e.store = d.setReg r (d.reg r+c) := by
  induction c generalizing d with
  | zero =>
    refine ⟨d.toCfg ⟨0, by simp [raiseLabels]⟩, ?_, ?_⟩
    · exact ⟨TapeProgram.Exec.refl _, rfl⟩
    · simp
  | succ c ih =>
    have h₁ := TapeMacros.increment_stops r inp d
    obtain ⟨e, he, hes⟩ := ih (d.setReg r (d.reg r+1))
    have hall := h₁.seq he
    refine ⟨e.mapPC (TapeProgram.rightLabel 2), ?_, ?_⟩
    · convert hall using 1 <;> first | rfl | omega
    · change e.store = _
      rw [hes]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]





theorem loadConstant_stops (r : Fin R) (c : ℕ) (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (loadConstant r c).Stops inp
      (d.toCfg (loadConstant (B := B) r c).entry) (d.reg r+2*c+2) e ∧
      e.store = d.setReg r c := by
  have hc := TapeMacros.clear_stops r inp (d.reg r) d rfl
  obtain ⟨e, he, hes⟩ := raise_stops r c inp (d.setReg r 0)
  have hall := hc.seq he
  refine ⟨e.mapPC (TapeProgram.rightLabel 2), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change e.store = _
    simpa using hes












theorem ltLoopStore_step (a b dst : Fin R)
    (hab : a ≠ b) (had : a ≠ dst) (hbd : b ≠ dst) (m n : ℕ) (d : TapeStore R B) :
    ltLoopStore a b dst m n ((d.setReg b n).setReg a m) =
      ltLoopStore a b dst (m+1) (n+1) d := by
  simp only [ltLoopStore, TapeStore.setReg]
  congr 1
  funext j
  by_cases hd : j = dst
  · subst j
    simp [Function.update, Ne.symm had, Ne.symm hbd]
  · by_cases hb : j = b
    · subst j; simp [Function.update, hbd]
    · by_cases ha : j = a
      · subst j; simp [Function.update, hab, had]
      · simp [Function.update, hd, hb, ha]

theorem ltLoop_stops (a b dst : Fin R)
    (hab : a ≠ b) (had : a ≠ dst) (hbd : b ≠ dst)
    (inp : Inputs) (m n : ℕ) (d : TapeStore R B)
    (ha : d.reg a = m) (hb : d.reg b = n) :
    (ltLoop a b dst).Stops inp (d.toCfg 0)
      (2*min m n+1+2*(if m<n then 1 else 0))
      ((ltLoopStore a b dst m n d).toCfg 4) := by
  induction m generalizing n d with
  | zero =>
    cases n with
    | zero =>
      have he : ltLoopStore a b dst 0 0 d = d := by
        have hsa : d.setReg a 0 = d := by simp [TapeStore.setReg, ← ha]
        have hsb : d.setReg b 0 = d := by simp [TapeStore.setReg, ← hb]
        simp [ltLoopStore, hsa, hsb]
      constructor
      · apply TapeProgram.Exec.one
        · simp [TapeProgram.halted, ltLoop]
        · simp [TapeProgram.step, ltLoop, TapeStore.toCfg, hb, he]
      · simp [TapeProgram.halted, ltLoop]
    | succ n =>
      let d₁ := d.setReg b n
      let e := d₁.setReg dst (d.reg dst+1)
      have h₁ : (ltLoop a b dst).step inp (d.toCfg 0) = d₁.toCfg 1 := by
        simp [TapeProgram.step, ltLoop, TapeStore.toCfg, d₁, TapeStore.setReg, hb]
      have h₂ : (ltLoop a b dst).step inp (d₁.toCfg 1) = d₁.toCfg 3 := by
        simp [TapeProgram.step, ltLoop, TapeStore.toCfg, d₁, TapeStore.setReg, hab, ha]
      have h₃ : (ltLoop a b dst).step inp (d₁.toCfg 3) = e.toCfg 4 := by
        simp [TapeProgram.step, ltLoop, TapeStore.toCfg, d₁, e, TapeStore.setReg, Ne.symm hbd]
      have he : ltLoopStore a b dst 0 (n+1) d = e := by
        have hs : d.setReg a 0 = d := by simp [TapeStore.setReg, ← ha]
        simp [ltLoopStore, e, d₁, hs]
      constructor
      · have ht := TapeProgram.Exec.step (by simp [TapeProgram.halted, ltLoop]) h₁
          (TapeProgram.Exec.step (by simp [TapeProgram.halted, ltLoop]) h₂
            (TapeProgram.Exec.one (by simp [TapeProgram.halted, ltLoop]) h₃))
        simpa [he] using ht
      · simp [TapeProgram.halted, ltLoop]
  | succ m ih =>
    cases n with
    | zero =>
      have he : ltLoopStore a b dst (m+1) 0 d = d := by
        have hsa : d.setReg a (m+1) = d := by simp [TapeStore.setReg, ← ha]
        have hsb : d.setReg b 0 = d := by simp [TapeStore.setReg, ← hb]
        simp [ltLoopStore, hsa, hsb]
      constructor
      · apply TapeProgram.Exec.one
        · simp [TapeProgram.halted, ltLoop]
        · simp [TapeProgram.step, ltLoop, TapeStore.toCfg, hb, he]
      · simp [TapeProgram.halted, ltLoop]
    | succ n =>
      let d₁ := d.setReg b n
      let d₂ := d₁.setReg a m
      have h₁ : (ltLoop a b dst).step inp (d.toCfg 0) = d₁.toCfg 1 := by
        simp [TapeProgram.step, ltLoop, TapeStore.toCfg, d₁, TapeStore.setReg, hb]
      have h₂ : (ltLoop a b dst).step inp (d₁.toCfg 1) = d₂.toCfg 0 := by
        simp [TapeProgram.step, ltLoop, TapeStore.toCfg, d₁, d₂, TapeStore.setReg, hab, ha]
      have htail := ih n d₂ (by simp [d₂, TapeStore.setReg])
        (by simp [d₂, d₁, TapeStore.setReg, Ne.symm hab])
      have hpost : ltLoopStore a b dst m n d₂ = ltLoopStore a b dst (m+1) (n+1) d :=
        ltLoopStore_step a b dst hab had hbd m n d
      constructor
      · have hall := TapeProgram.Exec.step (by simp [TapeProgram.halted, ltLoop]) h₁
          (TapeProgram.Exec.step (by simp [TapeProgram.halted, ltLoop]) h₂ htail.exec)
        rw [hpost] at hall
        convert hall using 1 <;> first | rfl | simp; omega
      · simp [TapeProgram.halted, ltLoop]











theorem reg_layout {N : ℕ} (r : Fin N → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i j : Fin N) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j; simp
  · simp [TapeStore.setReg, h, show r j ≠ r i from fun he => h (hr he)]













theorem lessThanStore_value (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) :
    (lessThanStore r d).reg (r 2) = if d.reg (r 0)<d.reg (r 1) then 1 else 0 := by
  simp [lessThanStore, lessCore, lessPrepare, ltLoopStore, reg_layout r hr]

theorem lessThanStore_preserves (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (j : Fin 6) (hj : j = 0 ∨ j = 1) :
    (lessThanStore r d).reg (r j) = d.reg (r j) := by
  rcases hj with rfl | rfl
  all_goals simp [lessThanStore, lessCore, lessPrepare, ltLoopStore, reg_layout r hr]

theorem lessThanStore_scratch (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (j : Fin 6) (hj : j = 3 ∨ j = 4 ∨ j = 5) :
    (lessThanStore r d).reg (r j) = 0 := by
  rcases hj with rfl | rfl | rfl
  all_goals simp [lessThanStore, lessCore, lessPrepare, ltLoopStore, reg_layout r hr]

theorem lessThanStore_bound (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (lessThanStore r d).reg j ≤ M := by
  intro j
  by_cases h₂ : j = r 2
  · subst j
    rw [lessThanStore_value r hr]
    split <;> omega
  · by_cases h₃ : j = r 3
    · subst j; rw [lessThanStore_scratch r hr d 3 (by simp)]; omega
    · by_cases h₄ : j = r 4
      · subst j; rw [lessThanStore_scratch r hr d 4 (by simp)]; omega
      · by_cases h₅ : j = r 5
        · subst j; rw [lessThanStore_scratch r hr d 5 (by simp)]; omega
        · simpa [lessThanStore, lessCore, lessPrepare, ltLoopStore, TapeStore.setReg,
            h₂, h₃, h₄, h₅] using hd j

theorem lessThan_stops (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 64*(M+1) ∧
      (lessThan r).Stops inp (d.toCfg (lessThan (B := B) r).entry) t e ∧
      e.store = lessThanStore r d := by
  obtain ⟨c₁, h₁, hcs₁⟩ := TapeMacros.copy_stops (r 0) (r 3) (r 5)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d
  have hb₁ : ∀ j, c₁.reg j ≤ M := by
    change ∀ j, c₁.store.reg j ≤ M
    rw [hcs₁]
    exact setReg_bound _ _ 0 M (setReg_bound d _ _ M hd (hd (r 0))) (by omega)
  obtain ⟨c₂, h₂, hcs₂⟩ := TapeMacros.copy_stops (r 1) (r 4) (r 5)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₁.store
  have hb₂ : ∀ j, c₂.reg j ≤ M := by
    change ∀ j, c₂.store.reg j ≤ M
    rw [hcs₂]
    exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hb₁ (hb₁ (r 1))) (by omega)
  have h₃ := TapeMacros.clear_stops (r 2) inp (c₂.reg (r 2)) c₂.store rfl
  have hprep : c₂.store.setReg (r 2) 0 = lessPrepare r d := by
    rw [hcs₂, hcs₁]
    rfl
  have h₄ := ltLoop_stops (r 3) (r 4) (r 2)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp
    (d.reg (r 0)) (d.reg (r 1)) (lessPrepare r d)
    (by simp [lessPrepare, reg_layout r hr]) (by simp [lessPrepare, reg_layout r hr])
  rw [← hprep] at h₄
  have hpostprep : ltLoopStore (r 3) (r 4) (r 2) (d.reg (r 0)) (d.reg (r 1))
      (c₂.store.setReg (r 2) 0) = lessCore r d := by rw [hprep]; rfl
  rw [hpostprep] at h₄
  have h₅ := TapeMacros.clear_stops (r 3) inp ((lessCore r d).reg (r 3)) (lessCore r d) rfl
  have h₆ := TapeMacros.clear_stops (r 4) inp
    (((lessCore r d).setReg (r 3) 0).reg (r 4)) ((lessCore r d).setReg (r 3) 0) rfl
  have hall := ((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆
  refine ⟨_, _, ?_, hall, rfl⟩
  have ht₁ : d.reg (r 3)+d.reg (r 5)+5*d.reg (r 0)+7 ≤ 7*M+7 := by
    have := hd (r 3); have := hd (r 5); have := hd (r 0); omega
  have ht₂ : c₁.reg (r 4)+c₁.reg (r 5)+5*c₁.reg (r 1)+7 ≤ 7*M+7 := by
    have := hb₁ (r 4); have := hb₁ (r 5); have := hb₁ (r 1); omega
  have ht₄ : 2*min (d.reg (r 0)) (d.reg (r 1))+1+
      2*(if d.reg (r 0)<d.reg (r 1) then 1 else 0) ≤ 2*M+3 := by
    have hm := (Nat.min_le_left (d.reg (r 0)) (d.reg (r 1))).trans (hd (r 0))
    split <;> omega
  have ht₅ : (lessCore r d).reg (r 3) ≤ M := by
    simp [lessCore, ltLoopStore, reg_layout r hr]
    have := hd (r 0); omega
  have ht₆ : ((lessCore r d).setReg (r 3) 0).reg (r 4) ≤ M := by
    simp [lessCore, ltLoopStore, reg_layout r hr]
    have := hd (r 1); omega
  have ht₃ := hb₂ (r 2)
  simp only [TapeCfg.store]
  omega




end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule17

/-! Inlined whole module: ExpandingCodes.Construction.ParameterBounds -/
section FlattenModule18


set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

private theorem parameter_inv_ge_one (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    1 ≤ ε⁻¹ :=
  (one_le_inv₀ hε.1).2 (by linarith [hε.2])

theorem dimension_ge_four (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    4 ≤ dimension ε := by
  have hi := parameter_inv_ge_one ε hε
  have hs : (1 : ℝ) ≤ ε⁻¹ ^ 2 := by nlinarith
  have hc : (2 : ℝ) ≤ (⌈512 * ε⁻¹ ^ 2⌉₊ : ℝ) :=
    (by nlinarith : (2 : ℝ) ≤ 512 * ε⁻¹ ^ 2).trans (Nat.le_ceil _)
  have hc' : 2 ≤ ⌈512 * ε⁻¹ ^ 2⌉₊ := by exact_mod_cast hc
  unfold dimension
  omega


















































end ExpandingCodes.PolynomialStretch

end FlattenModule18

/-! Inlined whole module: ExpandingCodes.Construction.Growth -/
section FlattenModule19



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

theorem fieldSize_lower (d n : ℕ) : n ^ (2 * d) ≤ fieldSize d n := by
  apply (Nat.le_pow_clog (by decide : 1 < 2) _).trans
  exact Nat.pow_le_pow_right (by decide) (le_max_right 1 _)

theorem fieldSize_upper (d n : ℕ) (hd : 0 < d) (hn : 2 ≤ n) :
    fieldSize d n < 2 * n ^ (2 * d) := by
  have hx : 1 < n ^ (2 * d) := one_lt_pow₀ (by omega) (by omega)
  have hc : 1 ≤ Nat.clog 2 (n ^ (2 * d)) := Nat.clog_pos (by decide) hx
  have hs : (Nat.clog 2 (n ^ (2 * d))).pred + 1 = Nat.clog 2 (n ^ (2 * d)) := by
    simpa only [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hc
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hx
  unfold fieldSize fieldExponent
  rw [max_eq_right hc, ← hs, pow_succ]
  nlinarith










theorem arity_exceeds_row_exponent (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    2 * dimension ε ^ 2 + 1 ≤ arity ε := by
  have hi : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε.1).2 (by linarith [hε.2])
  have hs : (1 : ℝ) ≤ ε⁻¹ ^ 2 := by nlinarith
  have hd := dimension_ge_four ε hε
  have hd' : (4 : ℝ) ≤ dimension ε := by exact_mod_cast hd
  have hc : 4 * (dimension ε : ℝ) ^ 2 * ε⁻¹ ^ 2 ≤ (arity ε : ℝ) := Nat.le_ceil _
  have hp := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 4 * (dimension ε : ℝ) ^ 2 by positivity)
  have hfinal : (2 : ℝ) * (dimension ε : ℝ) ^ 2 + 1 ≤ arity ε := by nlinarith
  exact_mod_cast hfinal


























end ExpandingCodes.PolynomialStretch

end FlattenModule19

/-! Inlined whole module: ExpandingCodes.Probability.FiniteUniform -/
section FlattenModule20


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

theorem uniformProb_eq_card_filter {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) :
    uniformProb E = ((Finset.univ.filter E).card : ℝ) / Fintype.card Ω := by
  classical
  simp [uniformProb, eventProb, ← Finset.sum_filter, div_eq_mul_inv]

theorem uniformProb_eq_card_subtype {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) :
    uniformProb E = (Fintype.card {ω // E ω} : ℝ) / Fintype.card Ω := by
  classical
  rw [uniformProb_eq_card_filter]
  simp only [Fintype.card_subtype]

theorem uniformProb_equiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [Nonempty Ω] [Nonempty Ξ] (e : Ω ≃ Ξ) (E : Ξ → Prop) :
    uniformProb (fun ω => E (e ω)) = uniformProb E := by
  classical
  rw [uniformProb_eq_card_subtype, uniformProb_eq_card_subtype]
  have ec : {ω // E (e ω)} ≃ {ξ // E ξ} :=
    { toFun := fun ω => ⟨e ω.val, ω.property⟩
      invFun := fun ξ => ⟨e.symm ξ.val, by simpa using ξ.property⟩
      left_inv := fun ω => by ext; simp
      right_inv := fun ξ => by ext; simp }
  rw [Fintype.card_congr ec, Fintype.card_congr e]

theorem uniformProb_congr {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {E D : Ω → Prop} (h : ∀ ω, E ω ↔ D ω) : uniformProb E = uniformProb D := by
  congr 1
  funext ω
  exact propext (h ω)






































































end ExpandingCodes.PolynomialStretch

end FlattenModule20

/-! Inlined whole module: ExpandingCodes.Computation.RandomBits -/
section FlattenModule21




set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ExpandingCodes.Computation
open NKtLB

namespace RandomBits
variable {R B : ℕ}












@[simp] theorem Layout.reg_eq (l : Layout R) (i j : Fin 6) :
    l.reg i = l.reg j ↔ i = j := l.reg.injective.eq_iff



















 




























 




















 

























 

















 

























 



















 







 































 








 
















 









 







 








 








 







































 

































 





























 




 




 




 





 





 




 




 




 



















open scoped BigOperators
open ExpandingCodes.PolynomialStretch













 theorem bitsIndexEquiv_val (ell : ℕ) (x : Fin ell → Bool) :
    (bitsIndexEquiv ell x).val = ∑ j : Fin ell, bitNat (x j) * 2^(ell-1-j.val) := by
  rw [bitsIndexEquiv, Equiv.trans_apply, Equiv.trans_apply,
    BinaryPolynomial.indexEquiv_inverse_value]
  change (∑ j : Fin ell, (BinaryPolynomial.bitEquiv (x j.rev)).val * 2^j.val) = _
  have hb (b : Bool) : (BinaryPolynomial.bitEquiv b).val = bitNat b := by cases b <;> rfl
  simp_rw [hb]
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin ell))]
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  simp only [Fin.val_rev]
  omega

 theorem value_eq_sum (inp : Inputs) (n h a : ℕ) :
    value inp n h a = 2^n*a +
      ∑ j : Fin n, bitNat (bitAt inp (h+j.val)) * 2^(n-1-j.val) := by
  induction n generalizing h a with
  | zero => simp [value]
  | succ n ih =>
    rw [value, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero, Nat.add_sub_cancel,
      Nat.sub_zero]
    have ht : (∑ j : Fin n, bitNat (bitAt inp (h+1+j.val)) * 2^(n-1-j.val)) =
        ∑ j : Fin n, bitNat (bitAt inp (h+(j.val+1))) * 2^(n-(j.val+1)) := by
      apply Finset.sum_congr rfl
      intro j _
      have hj : n-1-j.val = n-(j.val+1) := by omega
      rw [hj]
      congr 3 <;> omega
    rw [ht, pow_succ]
    ring

/-- The exact value computed at any random-head offset is the finite bit
bijection; this also fixes the endianness relative to `indexEquiv`. -/
 theorem value_eq_bitsIndex (inp : Inputs) (ell h : ℕ) :
    value inp ell h 0 =
      (bitsIndexEquiv ell (fun j => bitAt inp (h+j.val))).val := by
  rw [value_eq_sum, bitsIndexEquiv_val]
  simp

 












 













theorem bitAt_block (inp : Inputs) (pre suffix : List Bool) {ell : ℕ}
    (x : Fin ell → Bool) (j : Fin ell) :
    bitAt {inp with rand := pre ++ (List.ofFn x ++ suffix)} (pre.length+j.val) = x j := by
  unfold bitAt Machine.readRO
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simpa using j.isLt), List.getElem?_ofFn]
  simp only [j.isLt, dite_true]
  cases hx : x j <;> rfl













 

































end RandomBits
end ExpandingCodes.Computation

end FlattenModule21

/-! Inlined whole module: ExpandingCodes.Computation.RandomTables -/
section FlattenModule22



set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ExpandingCodes.Computation
open NKtLB
namespace RandomTables
variable {R B : ℕ}





















 




































































 





 









 




 
















 








 































































 





 





 





 





 





 











 



















 




















































































open ExpandingCodes.PolynomialStretch



















 



 theorem tableIndexEquiv_apply (K ell : ℕ) (x : Fin (K*ell) → Bool) (i : Fin K) :
    tableIndexEquiv K ell x i =
      RandomBits.bitsIndexEquiv ell (fun j => x ⟨i.val*ell+j.val, by nlinarith [i.isLt, j.isLt]⟩) := by
  change RandomBits.bitsIndexEquiv ell (fun j => x (finProdFinEquiv (i,j))) = _
  congr 1
  funext j
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv]
  ring





 theorem sampledValues_block (inp : Inputs) (pre suffix : List Bool) (K ell : ℕ)
    (x : Fin (K*ell) → Bool) :
    sampledValues {inp with rand := pre ++ (List.ofFn x ++ suffix)} K ell pre.length =
      tableIndexEquiv K ell x := by
  funext i
  apply Fin.ext
  rw [tableIndexEquiv_apply]
  change RandomBits.value {inp with rand := pre ++ (List.ofFn x ++ suffix)} ell
    (pre.length+i.val*ell) 0 = _
  rw [RandomBits.value_eq_bitsIndex]
  congr 2
  funext j
  have h := RandomBits.bitAt_block inp pre suffix x
    (⟨i.val*ell+j.val, by nlinarith [i.isLt, j.isLt]⟩ : Fin (K*ell))
  simpa [Nat.add_assoc] using h











 



















end RandomTables
end ExpandingCodes.Computation

end FlattenModule22


section FlattenModule23



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch




























end ExpandingCodes.PolynomialStretch

end FlattenModule23


section FlattenModule24


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch




























































end ExpandingCodes.PolynomialStretch

end FlattenModule24


section FlattenModule25


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch





































































































































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule25


section FlattenModule26



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch































































































end ExpandingCodes.PolynomialStretch

end FlattenModule26


section FlattenModule27


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch



























end ExpandingCodes.PolynomialStretch

end FlattenModule27


section FlattenModule28





set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch



































































































































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule28


section FlattenModule29





set_option autoImplicit false

open scoped BigOperators Topology Pointwise
open Set Filter MeasureTheory

namespace ExpandingCodes.PolynomialStretch



























































































































end ExpandingCodes.PolynomialStretch

end FlattenModule29


section FlattenModule30


set_option autoImplicit false

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace ExpandingCodes.PolynomialStretch
























































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule30


section FlattenModule31



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

universe u







































































































end ExpandingCodes.PolynomialStretch

end FlattenModule31


section FlattenModule32




set_option autoImplicit false

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace ExpandingCodes.PolynomialStretch







































































end ExpandingCodes.PolynomialStretch

end FlattenModule32


section FlattenModule33



set_option autoImplicit false
open Filter Topology

namespace ExpandingCodes.PolynomialStretch


























































































end ExpandingCodes.PolynomialStretch

end FlattenModule33


section FlattenModule34



set_option autoImplicit false
open scoped Classical
open Filter Topology

namespace ExpandingCodes.PolynomialStretch





























end ExpandingCodes.PolynomialStretch

end FlattenModule34


section FlattenModule35


set_option autoImplicit false
set_option maxRecDepth 2048
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

























































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule35


section FlattenModule36


set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch













































































end ExpandingCodes.PolynomialStretch

end FlattenModule36


section FlattenModule37



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch



































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule37


section FlattenModule38



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch


























































end ExpandingCodes.PolynomialStretch

end FlattenModule38

/-! Inlined whole module: ExpandingCodes.Construction.HashParameters -/
section FlattenModule39



set_option autoImplicit false
open Filter Topology

namespace ExpandingCodes.PolynomialStretch








































theorem hash_arity_pos (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) : 0 < arity ε := by
  have := arity_exceeds_row_exponent ε hε
  omega




































































































end ExpandingCodes.PolynomialStretch

end FlattenModule39


section FlattenModule40





set_option autoImplicit false
set_option maxRecDepth 2048
open scoped Classical BigOperators
open Filter Topology

namespace ExpandingCodes.PolynomialStretch


























































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule40


section FlattenModule41




set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
















































end ExpandingCodes.PolynomialStretch

end FlattenModule41


section FlattenModule42



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch





























































end ExpandingCodes.PolynomialStretch

end FlattenModule42

/-! Inlined whole module: ExpandingCodes.Probability.BoundedDifferences -/
section FlattenModule43



/-!
# Sharp finite bounded differences on the uniform Boolean cube

The probability in the final theorem is the mission's canonical `uniformProb`.
`uniformMean` and `HasUnitBoundedDifferences` are local helper interfaces. The
proof uses exact finite sums, splits coordinates by `Fin.consEquiv`, and proves
the centered MGF bound by induction. The two-point estimate is Mathlib's
`Real.cosh_le_exp_half_sq`; finite exponential Markov and optimization give the
sharp exponent `-2 * t^2 / m`. No measure-theoretic martingale is required.
-/

set_option autoImplicit false
open scoped BigOperators Classical

namespace ExpandingCodes.PolynomialStretch





section Mean
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

@[simp] theorem uniformMean_const (c : ℝ) : uniformMean (fun _ : Ω => c) = c := by
  simp [uniformMean, Fintype.card_ne_zero]




























/-- Bridge to the mission's canonical finite uniform probability. -/
theorem uniformProb_eq_uniformMean (E : Ω → Prop) :
    uniformProb E = uniformMean (fun x => if E x then 1 else 0) := by
  classical
  unfold uniformProb eventProb uniformMean
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

end Mean







































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule43

/-! Inlined whole module: ExpandingCodes.Probability.GridBand -/
section FlattenModule44



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

theorem uniformProb_prod (α β : Type*) [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (E : α × β → Prop) :
    uniformProb E = uniformMean (fun b => uniformProb (fun a => E (a, b))) := by
  classical
  simp_rw [uniformProb_eq_uniformMean]
  unfold uniformMean
  simp only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_div]
  ring






















































end ExpandingCodes.PolynomialStretch

end FlattenModule44

/-! Inlined whole module: ExpandingCodes.Construction.ExpansionTransfer -/
section FlattenModule45




set_option autoImplicit false
open scoped Classical BigOperators Topology
open Filter

namespace ExpandingCodes.PolynomialStretch

theorem eventProb_map {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (P : PMF Ω) (f : Ω → Ξ) (E : Ξ → Prop) :
    eventProb (P.map f) E = eventProb P (fun x => E (f x)) := by
  classical
  have hm (y : Ξ) : ((P.map f) y).toReal =
      ∑ x, if y = f x then (P x).toReal else 0 := by
    rw [PMF.map_apply, tsum_fintype]
    rw [ENNReal.toReal_sum (fun x _ => by
      split_ifs
      · exact P.apply_ne_top x
      · simp)]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  unfold eventProb
  simp_rw [hm]
  have hi (y : Ξ) : (if E y then ∑ x, if y = f x then (P x).toReal else 0 else 0) =
      ∑ x, if y = f x then (if E (f x) then (P x).toReal else 0) else 0 := by
    by_cases hy : E y
    · rw [if_pos hy]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hxy : y = f x
      · subst y
        simp [hy]
      · simp [hxy]
    · rw [if_neg hy]
      symm
      apply Finset.sum_eq_zero
      intro x _
      by_cases hxy : y = f x
      · subst y
        simp [hy]
      · simp [hxy]
  simp_rw [hi]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp


































































end ExpandingCodes.PolynomialStretch

end FlattenModule45

/-! Inlined whole module: ExpandingCodes.Computation.SamplerTables -/
section FlattenModule46



set_option autoImplicit false
set_option linter.style.haveILetI false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch
namespace SamplerTables













































theorem formsEquiv_apply {d n : ℕ} (g : Geometry d n) (k : ℕ)
    (t : Fin (formEntries d n k) → Fin (fieldSize d n))
    (r : Fin 2) (i : Fin k) (a : g.F) (j : Fin d) :
    formsEquiv g k t r i a j =
      g.elements (t (flatFour 2 k (fieldSize d n) d (((r,i),g.elements.symm a),j))) := rfl














theorem hashesEquiv_apply {d n : ℕ} (g : Geometry d n) (k b : ℕ)
    (t : Fin (hashEntries d n k) → Fin b) (i : Fin k) (a u v : g.F) :
    hashesEquiv g k b t i (a,u,v) =
      t (flatFour k (fieldSize d n) (fieldSize d n) (fieldSize d n)
        (((i,g.elements.symm a),g.elements.symm u),g.elements.symm v)) := rfl






theorem splitBits_list (a b : ℕ) (ω : Fin (a+b) → Bool) :
    List.ofFn ω = List.ofFn (splitBits a b ω).1 ++ List.ofFn (splitBits a b ω).2 := by
  change List.ofFn ω =
    List.ofFn (fun i : Fin a => ω (Fin.castLE (Nat.le_add_right a b) i)) ++
      List.ofFn (fun i : Fin b => ω (Fin.natAdd a i))
  exact List.ofFn_add























theorem uniform_decodeCoins {d n : ℕ} (g : Geometry d n) (k beta extra : ℕ)
    (E : (Forms g.F d k × Hashes g.F k (2^beta)) → Prop) :
    uniformProb (fun ω => E (decodeCoins g k beta extra ω)) = uniformProb E := by
  letI : Nonempty (Fin (2^beta)) := ⟨⟨0, pow_pos (by omega) beta⟩⟩
  rw [show (fun ω => E (decodeCoins g k beta extra ω)) =
    (fun ω => (fun p => E p.1) (coinsEquiv g k beta extra ω)) from rfl]
  rw [uniformProb_equiv (coinsEquiv g k beta extra) (fun p => E p.1), uniformProb_prod]
  exact uniformMean_const (Ω := Fin extra → Bool) (uniformProb E)

/-- The abstract bijection decodes exactly the values read by the physical
table-fill programs, first all form entries, then all hash entries. -/
theorem decodeCoins_physical {d n : ℕ} (g : Geometry d n) (k beta extra : ℕ)
    (inp : NKtLB.Inputs) (ω : Fin (entropy d n k beta+extra) → Bool) :
    decodeCoins g k beta extra ω =
      (formsEquiv g k (Computation.RandomTables.sampledValues
        {inp with rand := List.ofFn ω} (formEntries d n k) (fieldExponent d n) 0),
       hashesEquiv g k (2^beta) (Computation.RandomTables.sampledValues
        {inp with rand := List.ofFn ω} (hashEntries d n k) beta
          (formEntries d n k * fieldExponent d n))) := by
  let A := formEntries d n k * fieldExponent d n
  let H := hashEntries d n k * beta
  let main := (splitBits (A+H) extra ω).1
  let xf := (splitBits A H main).1
  let xh := (splitBits A H main).2
  let tail := (splitBits (A+H) extra ω).2
  have hlist : List.ofFn ω = List.ofFn xf ++ (List.ofFn xh ++ List.ofFn tail) := by
    exact (splitBits_list (A+H) extra ω).trans
      ((congrArg (fun l => l ++ List.ofFn tail) (splitBits_list A H main)).trans
        (List.append_assoc _ _ _))
  have hF := Computation.RandomTables.sampledValues_block inp []
    (List.ofFn xh ++ List.ofFn tail) (formEntries d n k) (fieldExponent d n) xf
  have hH := Computation.RandomTables.sampledValues_block inp (List.ofFn xf)
    (List.ofFn tail) (hashEntries d n k) beta xh
  simp only [List.nil_append, List.length_nil] at hF
  simp only [List.length_ofFn] at hH
  change
    (formsEquiv g k (Computation.RandomTables.tableIndexEquiv _ _ xf),
     hashesEquiv g k (2^beta) (Computation.RandomTables.tableIndexEquiv _ _ xh)) = _
  rw [hlist, hF, hH]







/-- Exact canonical sampling law, allowing any number of unused final coins. -/
theorem generator_law (θ : ℝ) (n extra : ℕ) (g : Geometry (dimension θ) n)
    (G : Generator (rowCount (dimension θ) n) n) :
    uniformProb (fun ω => generator g (arity θ) (Nat.log 2 (n/arity θ)) extra ω = G) =
      (sampleLaw θ n g G).toReal := by
  rw [show (fun ω => generator g (arity θ) (Nat.log 2 (n/arity θ)) extra ω = G) =
    (fun ω => (fun p => combined g p.1 p.2 = G)
      (decodeCoins g (arity θ) (Nat.log 2 (n/arity θ)) extra ω)) from rfl]
  rw [uniform_decodeCoins g (arity θ) (Nat.log 2 (n/arity θ)) extra
    (fun p => combined g p.1 p.2 = G)]
  have he : eventProb (sampleLaw θ n g) (fun H => H = G) = (sampleLaw θ n g G).toReal := by
    classical
    unfold eventProb
    rw [Finset.sum_eq_single G]
    · simp
    · intro H _ hH
      simp [hH]
    · simp
  rw [← he]
  unfold sampleLaw
  rw [eventProb_map]
  rfl







theorem padEquiv_list (E T : ℕ) (h : E ≤ T) (ω : Fin T → Bool) :
    List.ofFn (padEquiv E T h ω) = List.ofFn ω := by
  have hh := List.ofFn_congr (Nat.add_sub_of_le h) (padEquiv E T h ω)
  have hf : (fun i : Fin T => padEquiv E T h ω (Fin.cast (Nat.add_sub_of_le h).symm i)) = ω := by
    funext i
    apply congrArg ω
    apply Fin.ext
    rfl
  exact hh.trans (congrArg List.ofFn hf)








theorem fromTape_law (θ : ℝ) (n T : ℕ) (g : Geometry (dimension θ) n)
    (h : entropy (dimension θ) n (arity θ) (Nat.log 2 (n/arity θ)) ≤ T)
    (G : Generator (rowCount (dimension θ) n) n) :
    uniformProb (fun ω => fromTape θ n T g h ω = G) = (sampleLaw θ n g G).toReal := by
  change uniformProb (fun ω => (fun x => generator g (arity θ)
    (Nat.log 2 (n/arity θ)) (T-entropy (dimension θ) n (arity θ)
      (Nat.log 2 (n/arity θ))) x = G) (padEquiv _ T h ω)) = _
  rw [uniformProb_equiv (padEquiv _ T h) (fun x => generator g (arity θ)
    (Nat.log 2 (n/arity θ)) (T-entropy (dimension θ) n (arity θ)
      (Nat.log 2 (n/arity θ))) x = G)]
  exact generator_law θ n _ g G









end SamplerTables
end ExpandingCodes.PolynomialStretch

end FlattenModule46

/-! Inlined whole module: ExpandingCodes.Computation.PolynomialBounds -/
section FlattenModule47



set_option autoImplicit false

namespace ExpandingCodes.Computation







namespace PolynomialBound
variable {f g : ℕ → ℕ}

theorem const (c : ℕ) : PolynomialBound (fun _ => c) :=
  ⟨c,0,by intro n _; simp⟩

theorem identity : PolynomialBound (fun n => n) :=
  ⟨1,1,by intro n _; simp⟩

theorem of_le (hf : PolynomialBound f) (h : ∀ n ≥ 2, g n ≤ f n) : PolynomialBound g := by
  obtain ⟨C,a,hf⟩ := hf
  exact ⟨C,a,fun n hn => (h n hn).trans (hf n hn)⟩

theorem add (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun n => f n+g n) := by
  obtain ⟨C,a,hf⟩ := hf
  obtain ⟨D,b,hg⟩ := hg
  refine ⟨C+D,max a b,?_⟩
  intro n hn
  have hp : 1 ≤ n+1 := by omega
  have ha := (hf n hn).trans
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_right hp (le_max_left a b)))
  have hb := (hg n hn).trans
    (Nat.mul_le_mul_left D (Nat.pow_le_pow_right hp (le_max_right a b)))
  calc
    f n+g n ≤ C*(n+1)^max a b+D*(n+1)^max a b := Nat.add_le_add ha hb
    _ = _ := by ring

theorem mul (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun n => f n*g n) := by
  obtain ⟨C,a,hf⟩ := hf
  obtain ⟨D,b,hg⟩ := hg
  refine ⟨C*D,a+b,?_⟩
  intro n hn
  simpa [pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    Nat.mul_le_mul (hf n hn) (hg n hn)

theorem pow (hf : PolynomialBound f) (r : ℕ) : PolynomialBound (fun n => (f n)^r) := by
  obtain ⟨C,a,hf⟩ := hf
  refine ⟨C^r,a*r,?_⟩
  intro n hn
  simpa [mul_pow, pow_mul] using Nat.pow_le_pow_left (hf n hn) r





theorem natLog (base : ℕ) (hf : PolynomialBound f) :
    PolynomialBound (fun n => Nat.log base (f n)) :=
  hf.of_le (fun n _ => Nat.log_le_self base (f n))

theorem div (hf : PolynomialBound f) (k : ℕ) : PolynomialBound (fun n => f n/k) :=
  hf.of_le (fun n _ => Nat.div_le_self (f n) k)

end PolynomialBound
end ExpandingCodes.Computation

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation

theorem fieldSize_polynomial (d : ℕ) (hd : 0 < d) :
    PolynomialBound (fieldSize d) := by
  refine ⟨2,2*d,?_⟩
  intro n hn
  exact (fieldSize_upper d n hd hn).le.trans
    (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.le_succ n) _))

theorem fieldExponent_polynomial (d : ℕ) (hd : 0 < d) :
    PolynomialBound (fieldExponent d) := by
  apply (fieldSize_polynomial d hd).of_le
  intro n _
  exact (Nat.lt_two_pow_self : fieldExponent d n < 2 ^ fieldExponent d n).le

theorem rowCount_polynomial (d : ℕ) (hd : 0 < d) :
    PolynomialBound (rowCount d) := (fieldSize_polynomial d hd).pow d

theorem samplerEntropy_polynomial (d k : ℕ) (hd : 0 < d) :
    PolynomialBound (fun n => SamplerTables.entropy d n k (Nat.log 2 (n/k))) := by
  have hq := fieldSize_polynomial d hd
  have he := fieldExponent_polynomial d hd
  have hbeta := (PolynomialBound.identity.div k).natLog 2
  exact (((((PolynomialBound.const 2).mul (PolynomialBound.const k)).mul hq).mul
    (PolynomialBound.const d)).mul he).add
    (((((PolynomialBound.const k).mul hq).mul hq).mul hq).mul hbeta)

/-- A single polynomial can cover both the actual proved time bound and the
required entropy. Raising its coefficient to 2*C+1 leaves compiler overhead. -/
theorem common_polynomial_envelope {f g : ℕ → ℕ}
    (hf : PolynomialBound f) (hg : PolynomialBound g) :
    ∃ C a : ℕ, ∀ n ≥ 2, f n ≤ C*(n+1)^a ∧ g n ≤ (2*C+1)*(n+1)^a := by
  obtain ⟨C,a,h⟩ := hf.add hg
  refine ⟨C,a,?_⟩
  intro n hn
  have hh := h n hn
  constructor
  · exact (Nat.le_add_right (f n) (g n)).trans hh
  · exact ((Nat.le_add_left (g n) (f n)).trans hh).trans
      (Nat.mul_le_mul_right _ (by omega))



end ExpandingCodes.PolynomialStretch

end FlattenModule47


section FlattenModule48



set_option autoImplicit false

namespace ExpandingCodes.Computation.FieldPrograms
open NKtLB
open ExpandingCodes.PolynomialStretch.BinaryPolynomial

































































end ExpandingCodes.Computation.FieldPrograms

end FlattenModule48

/-! Inlined whole module: ExpandingCodes.Computation.FieldConvolution -/
section FlattenModule49



set_option autoImplicit false

namespace ExpandingCodes.Computation.FieldConvolution
open NKtLB FieldPrograms
open ExpandingCodes.PolynomialStretch
open BinaryPolynomial
variable {R B : ℕ}










































































































































































































































































































































































































































































































































@[simp] theorem tapeData_setReg (d : TapeStore R B) (i : Fin R) (n : ℕ) :
    tapeData (d.setReg i n) = tapeData d := rfl









































































































































end ExpandingCodes.Computation.FieldConvolution

end FlattenModule49


section FlattenModule50


set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.FieldCertificates
open NKtLB FieldPrograms FieldConvolution
open ExpandingCodes.PolynomialStretch
open BinaryPolynomial
variable {R B : ℕ}
































































































































































































































































































































































































































































































































































































































































































































































































































































































































end ExpandingCodes.Computation.FieldCertificates

end FlattenModule50


section FlattenModule51


set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.SourceFieldArithmetic
open NKtLB FieldPrograms FieldConvolution FieldCertificates
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B L : ℕ}










































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end ExpandingCodes.Computation.SourceFieldArithmetic

end FlattenModule51

/-! Inlined whole module: ExpandingCodes.Computation.SamplerEvaluation -/
section FlattenModule52







set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace SamplerEvaluation
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

theorem reg_layout {L : ℕ} (r : Fin L → Fin R) (hr : Function.Injective r)
    (s : TapeStore R B) (i j : Fin L) (v : ℕ) :
    (s.setReg (r i) v).reg (r j)=if j=i then v else s.reg (r j) := by
  simp [TapeStore.setReg,Function.update,hr.eq_iff]

/-- A physical copy with its caller-counter bound. This does not touch any
buffer, head, output, or register outside destination/scratch. -/
theorem copy_stops_bound (src dst tmp : Fin R)
    (hsd : src≠dst) (hst : src≠tmp) (hdt : dst≠tmp)
    (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j       ≤       M) :
    ∃ t e, t       ≤       7*M+7 ∧
      (TapeMacros.copy src dst tmp).Stops inp
        (s.toCfg (TapeMacros.copy (B := B) src dst tmp).entry) t e ∧
      e.store=(s.setReg dst (s.reg src)).setReg tmp 0 ∧ ∀ j,e.reg j       ≤       M := by
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops src dst tmp hsd hst hdt inp s
  refine ⟨_,e,?_,he,hes,?_⟩
  · have h₁ := hs src; have h₂ := hs dst; have h₃ := hs tmp; omega
  · change ∀ j,e.store.reg j       ≤       M
    rw [hes]
    exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hs (hs src)) (by omega)





































































































































































































































































































































































































































































































































































































































































































theorem hashEnvelope_polynomial (i t : ℕ) : PolynomialBound (fun M => hashEnvelope i M t) := by
  induction t with
  | zero =>
    simpa only [hashEnvelope] using (PolynomialBound.identity.add (PolynomialBound.const i)).add (PolynomialBound.const 1)
  | succ t ih =>
    simpa only [hashEnvelope] using (ih.add (PolynomialBound.const 1)).pow 2

theorem hashIndexTimeBound_polynomial (i : ℕ) : PolynomialBound (hashIndexTimeBound i) := by
  exact (((((PolynomialBound.identity.add (PolynomialBound.const (2*i))).add (PolynomialBound.const 5)).add
    ((PolynomialBound.const 32).mul (hashEnvelope_polynomial i 1))).add
      ((PolynomialBound.const 32).mul (hashEnvelope_polynomial i 2))).add
        ((PolynomialBound.const 32).mul (hashEnvelope_polynomial i 3)))
























































































































































































































































theorem hashedColumnTimeBound_polynomial (i : ℕ) : PolynomialBound (hashedColumnTimeBound i) := by
  exact ((((hashIndexTimeBound_polynomial i).add
    ((PolynomialBound.const 64).mul ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 2))).add
      ((PolynomialBound.const 7).mul PolynomialBound.identity)).add (PolynomialBound.const 10)).add
        ((PolynomialBound.const i).mul ((PolynomialBound.const 5).mul PolynomialBound.identity |>.add (PolynomialBound.const 6)))






















end SamplerEvaluation
end ExpandingCodes.Computation

end FlattenModule52

/-! Inlined whole module: ExpandingCodes.Computation.SamplerOdometer -/
section FlattenModule53



set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
open scoped BigOperators
namespace SamplerOdometer
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}






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

















end SamplerOdometer
end ExpandingCodes.Computation

end FlattenModule53

/-! Inlined whole module: ExpandingCodes.Computation.GaussianElimination -/
section FlattenModule54





set_option autoImplicit false

namespace ExpandingCodes.Computation.Gaussian

variable {F : Type*} [Field F] [DecidableEq F]










omit [Field F] [DecidableEq F] in
@[simp] theorem toMatrix_ofMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    toMatrix (ofMatrix A) = A := by
  ext i j
  simp [toMatrix, ofMatrix]





@[simp] theorem length_cells (m n : ℕ) : (cells m n).length = m*n := by
  simp [cells, List.length_flatMap, List.length_finRange]

@[simp] theorem mem_cells {m n : ℕ} (p : Fin m × Fin n) : p ∈ cells m n := by
  simp [cells]
























































































def Work.total (w : Work) : ℕ :=
  w.comparisons+w.inverses+w.arithmetic+w.reads+w.writes+w.enumerated






@[simp] theorem Work.total_add (a b : Work) :
    (a.add b).total = a.total + b.total := by
  simp [Work.total, Work.add]; omega











































































end ExpandingCodes.Computation.Gaussian

end FlattenModule54

/-! Inlined whole module: ExpandingCodes.Computation.GaussianCorrectness -/
section FlattenModule55







set_option autoImplicit false

namespace ExpandingCodes.Computation.Gaussian

open Matrix Module LinearMap
open scoped Matrix

variable {F : Type*} [Field F]































































@[simp] theorem pivotEquiv_inl {m : ℕ} (p : Fin (m+1)) (u : PUnit.{1}) :
    pivotEquiv p (Sum.inl u) = p := by
  simp [pivotEquiv]

@[simp] theorem pivotEquiv_inr {m : ℕ} (p : Fin (m+1)) (i : Fin m) :
    pivotEquiv p (Sum.inr i) = p.succAbove i := by
  simp [pivotEquiv]




































































end ExpandingCodes.Computation.Gaussian

end FlattenModule55

/-! Inlined whole module: ExpandingCodes.Computation.EncodedGaussian -/
section FlattenModule56




set_option autoImplicit false

namespace ExpandingCodes.Computation.EncodedGaussian

open Gaussian
























@[simp] theorem toMatrix_mapTable {α β : Type*} (f : α → β) {m n : ℕ}
    (A : Table α m n) (i : Fin m) (j : Fin n) :
    toMatrix (mapTable f A) i j = f (toMatrix A i j) := by
  simp [mapTable, toMatrix, ofMatrix]

variable {α : Type*} [DecidableEq α]






























variable {F : Type*} [Field F] [DecidableEq F]
variable {O : Operations α} {decode : α → F}





















































end ExpandingCodes.Computation.EncodedGaussian

namespace ExpandingCodes.PolynomialStretch.BinaryField

open Computation.EncodedGaussian BinaryPolynomial













theorem elements_zeroIndex (ell : ℕ) (h : 0 < ell) :
    elements ell h (zeroIndex ell) = 0 := by
  change decode ell h (indexEquiv ell ((indexEquiv ell).symm (zero ell))) = 0
  rw [Equiv.apply_symm_apply, decode_zero]

theorem elements_oneIndex (ell : ℕ) (h : 0 < ell) :
    elements ell h (oneIndex ell) = 1 := by
  change decode ell h (indexEquiv ell ((indexEquiv ell).symm (one ell))) = 1
  rw [Equiv.apply_symm_apply, decode_one]

theorem indexOperations_interpretation (ell : ℕ) (h : 0 < ell) :
    Interpretation (indexOperations ell h) (elements ell h) where
  injective := (elements ell h).injective
  zero := elements_zeroIndex ell h
  one := elements_oneIndex ell h
  add := elements_addIndex ell h
  sub := by
    intro a b
    change elements ell h (addIndex ell a b) = _
    rw [elements_addIndex, CharTwo.sub_eq_add]
  mul := elements_multiplyIndex ell h
  inv := elements_inverseIndex ell h





end ExpandingCodes.PolynomialStretch.BinaryField

end FlattenModule56

/-! Inlined whole module: ExpandingCodes.Algebra.FullEvaluation -/
section FlattenModule57



set_option autoImplicit false

open scoped BigOperators

namespace ExpandingCodes.PolynomialStretch









@[simp] theorem fullEvaluationMatrix_good {d n : ℕ} (g : Geometry d n)
    (a : Monomials g.F d (auxiliaryDegree (Fintype.card g.F) d))
    (z : Fin (rowCount d n)) :
    fullEvaluationMatrix g a.1 z = evaluationMatrix g a z := by
  simp [fullEvaluationMatrix, evaluationMatrix, monomialEval, a.2]

































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule57

/-! Inlined whole module: ExpandingCodes.Computation.EncodedTester -/
section FlattenModule58




set_option autoImplicit false

open scoped BigOperators

namespace ExpandingCodes.Computation.EncodedTester

open EncodedGaussian Gaussian

variable {α : Type*}














@[simp] theorem power_cost (O : Operations α) (x : α) (k : ℕ) :
    (power O x k).2 = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [power, ih]





















variable {F : Type*} [Field F] {O : Operations α} {decode : α → F}

theorem power_decode (h : Interpretation O decode) (x : α) (k : ℕ) :
    decode (power O x k).1 = (decode x)^k := by
  induction k with
  | zero => simpa [power] using h.one
  | succ k ih => simp [power, h.mul, ih, pow_succ]







theorem sum_decode (h : Interpretation O decode) (xs : List (α × ℕ)) :
    decode (sum O xs).1 = (xs.map (fun x => decode x.1)).sum := by
  induction xs with
  | nil => exact h.zero
  | cons a as ih => simp [sum, h.add, ih]



































































































end ExpandingCodes.Computation.EncodedTester

namespace ExpandingCodes.PolynomialStretch

open Computation EncodedGaussian EncodedTester








@[simp] theorem encodedExponentOrder_val {d n : ℕ} (g : Geometry d n)
    (a : Fin (rowCount d n)) (i : Fin d) :
    (encodedExponentOrder g a i).val = (digits (fieldSize d n) d a i).val := rfl








































































































end ExpandingCodes.PolynomialStretch

end FlattenModule58

/-! Inlined whole module: ExpandingCodes.Computation.EncodedSampler -/
section FlattenModule59




set_option autoImplicit false
open scoped BigOperators

namespace ExpandingCodes.Computation.EncodedSampler

open EncodedGaussian EncodedTester
open ExpandingCodes.PolynomialStretch

variable {q d k b : ℕ}


























































variable {F : Type*} [Field F] {O : Operations (Fin q)} {decode : Fin q → F}

theorem fixed_decode (h : Interpretation O decode) (a : Fin q) (z : Fin d → Fin q) :
    decode (fixed O a z).1 = ∑ j, (decode a)^j.val * decode (z j) := by
  unfold fixed
  rw [sum_decode h]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, h.mul, power_decode h]

theorem linear_decode (h : Interpretation O decode) (s z : Fin d → Fin q) :
    decode (linear O s z).1 = ∑ j, decode (s j) * decode (z j) := by
  unfold linear
  rw [sum_decode h]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, h.mul]

end ExpandingCodes.Computation.EncodedSampler

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation EncodedGaussian EncodedTester

theorem encodedSampler_address {d n k : ℕ} (g : Geometry d n)
    (O : Operations (Fin (fieldSize d n))) (hO : Interpretation O g.elements)
    (s : Fin (SamplerTables.formEntries d n k) → Fin (fieldSize d n))
    (hk : k ≤ fieldSize d n) (i : Fin k) (z : Fin d → Fin (fieldSize d n)) :
    let a := (EncodedSampler.address O s i z).1
    (g.elements a.1,g.elements a.2.1,g.elements a.2.2) =
      address g (SamplerTables.formsEquiv g k s) i (fun j => g.elements (z j)) := by
  have hi : i.val < fieldSize d n := lt_of_lt_of_le i.isLt hk
  have hf : g.elements.symm (∑ j, g.elements ⟨i.val,hi⟩ ^ j.val * g.elements (z j)) =
      (EncodedSampler.fixed O ⟨i.val,hi⟩ z).1 := by
    rw [← EncodedSampler.fixed_decode hO, Equiv.symm_apply_apply]
  dsimp only [EncodedSampler.address, address]
  rw [dif_pos hi]
  simp only [EncodedSampler.fixed_decode hO, EncodedSampler.linear_decode hO,
    SamplerTables.formsEquiv_apply, fixedForm, linearForm,
    alpha, dif_pos hi]
  rw [hf]

theorem encodedSampler_matrix {d n k b : ℕ} (g : Geometry d n)
    (O : Operations (Fin (fieldSize d n))) (hO : Interpretation O g.elements)
    (s : Fin (SamplerTables.formEntries d n k) → Fin (fieldSize d n))
    (h : Fin (SamplerTables.hashEntries d n k) → Fin b)
    (hk : k ≤ fieldSize d n)
    (hz : ∀ z j, g.rowOrder z j = g.elements (digits (fieldSize d n) d z j)) :
    EncodedSampler.matrix n O s h =
      combined g (SamplerTables.formsEquiv g k s) (SamplerTables.hashesEquiv g k b h) := by
  classical
  funext z j
  unfold EncodedSampler.matrix combined
  congr 1
  apply propext
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨i,EncodedSampler.neighbor O s h i (digits (fieldSize d n) d z), hi, ?_⟩
    rw [show g.rowOrder z = (fun l => g.elements (digits (fieldSize d n) d z l)) by funext l; exact hz z l,
      ← encodedSampler_address g O hO s hk i]
    simp [EncodedSampler.neighbor, SamplerTables.hashesEquiv_apply]
  · rintro ⟨i,u,hi,hu⟩
    refine ⟨i, ?_⟩
    rw [show g.rowOrder z = (fun l => g.elements (digits (fieldSize d n) d z l)) by funext l; exact hz z l,
      ← encodedSampler_address g O hO s hk i] at hu
    have hn : EncodedSampler.neighbor O s h i (digits (fieldSize d n) d z) = u := by
      simpa [EncodedSampler.neighbor, SamplerTables.hashesEquiv_apply] using hu
    rw [hn]
    exact hi

theorem binary_encodedSampler_matrix (d n k b : ℕ)
    (s : Fin (SamplerTables.formEntries d n k) → Fin (fieldSize d n))
    (h : Fin (SamplerTables.hashEntries d n k) → Fin b) (hk : k ≤ fieldSize d n) :
    EncodedSampler.matrix n
      (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n)) s h =
      combined (binaryGeometry d n) (SamplerTables.formsEquiv (binaryGeometry d n) k s)
        (SamplerTables.hashesEquiv (binaryGeometry d n) k b h) := by
  exact encodedSampler_matrix (binaryGeometry d n) _
    (BinaryField.indexOperations_interpretation _ _) s h hk (binaryGeometry_rowOrder d n)











theorem binarySamplerFromInput_eq (d n k beta extra : ℕ) (inp : NKtLB.Inputs)
    (ω : Fin (SamplerTables.entropy d n k beta+extra) → Bool) (hk : k ≤ fieldSize d n) :
    binarySamplerFromInput d n k beta {inp with rand := List.ofFn ω} =
      SamplerTables.generator (binaryGeometry d n) k beta extra ω := by
  unfold binarySamplerFromInput
  erw [binary_encodedSampler_matrix d n k (2^beta) _ _ hk]
  unfold SamplerTables.generator
  rw [SamplerTables.decodeCoins_physical (binaryGeometry d n) k beta extra inp ω]

theorem binarySamplerFromInput_law (θ : ℝ) (n T : ℕ)
    (hk : arity θ ≤ fieldSize (dimension θ) n)
    (hT : SamplerTables.entropy (dimension θ) n (arity θ) (Nat.log 2 (n/arity θ)) ≤ T)
    (G : Generator (rowCount (dimension θ) n) n) :
    uniformProb (fun ω : Fin T → Bool => binarySamplerFromInput (dimension θ) n (arity θ)
      (Nat.log 2 (n/arity θ)) ⟨sizeInput n, [], [], List.ofFn ω⟩ = G) =
      (sampleLaw θ n (binaryGeometry (dimension θ) n) G).toReal := by
  have hf (ω : Fin T → Bool) : binarySamplerFromInput (dimension θ) n (arity θ)
      (Nat.log 2 (n/arity θ)) ⟨sizeInput n, [], [], List.ofFn ω⟩ =
      SamplerTables.fromTape θ n T (binaryGeometry (dimension θ) n) hT ω := by
    unfold SamplerTables.fromTape
    rw [← binarySamplerFromInput_eq (dimension θ) n (arity θ) (Nat.log 2 (n/arity θ)) _
      (⟨sizeInput n, [], [], List.ofFn ω⟩ : NKtLB.Inputs) _ hk,
      SamplerTables.padEquiv_list]
  calc
    _ = uniformProb (fun ω => SamplerTables.fromTape θ n T
        (binaryGeometry (dimension θ) n) hT ω = G) :=
      uniformProb_congr (fun ω => by rw [hf ω])
    _ = _ := SamplerTables.fromTape_law θ n T (binaryGeometry (dimension θ) n) hT G



end ExpandingCodes.PolynomialStretch

end FlattenModule59


section FlattenModule60



set_option autoImplicit false

namespace ExpandingCodes.Computation.SamplerLayerBounds
open ExpandingCodes.PolynomialStretch
variable {q d k b : ℕ}

























































end ExpandingCodes.Computation.SamplerLayerBounds

end FlattenModule60

/-! Inlined whole module: ExpandingCodes.Computation.SamplerProgram -/
section FlattenModule61






set_option autoImplicit false
namespace ExpandingCodes.Computation.SamplerProgram
open NKtLB SamplerEvaluation
open ExpandingCodes.PolynomialStretch BinaryPolynomial
open FieldPrograms UnaryArithmetic
variable {R B : ℕ}
















theorem Environment.frame {r : Fin 31 → Fin R} {ell : ℕ} {m : Fin (2^ell)}
    {s e : TapeStore R B} (h : Environment r ell m s)
    (hf : ∀ i : Fin 31,i=3 ∨ i=19 ∨ i=23 ∨ i=24 → e.reg (r i)=s.reg (r i)) :
    Environment r ell m e := by
  constructor
  · rw [hf 3 (by decide)]; exact h.modulus
  · rw [hf 19 (by decide)]; exact h.length
  · rw [hf 23 (by decide)]; exact h.cardinal
  · rw [hf 24 (by decide)]; exact h.square



























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































namespace Storage






































@[simp] theorem point_val (d k : ℕ) (j : Fin d) : (point d k j).val=80+j.val := rfl
@[simp] theorem countdown_val (d k : ℕ) (j : Fin d) : (countdown d k j).val=80+d+j.val := rfl
@[simp] theorem coefficient_val (d k : ℕ) (j : Fin d) : (coefficient d k j).val=80+2*d+j.val := rfl

end Storage

namespace Storage






















end Storage


























theorem powerCoefficientTimeBound_polynomial (d : ℕ) : PolynomialBound (powerCoefficientTimeBound d) := by
  exact (PolynomialBound.const (d+2)).mul
    ((PolynomialBound.const 13440).mul ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 6))

theorem fixedTimeBound_polynomial (d : ℕ) : PolynomialBound (fixedTimeBound d) := by
  exact (((PolynomialBound.const d).mul ((powerCoefficientTimeBound_polynomial d).add (PolynomialBound.const 1))).add
    (PolynomialBound.const 1)).add
      ((PolynomialBound.const (d+1)).mul ((PolynomialBound.const 13320).mul
        ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 6)))

theorem vectorTimeBound_polynomial (c d : ℕ) : PolynomialBound (vectorTimeBound c d) := by
  exact (PolynomialBound.const (112+6*c+6*d*(c+1)+2*d)).mul
    ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 2)

theorem randomLinearTimeBound_polynomial (c d : ℕ) : PolynomialBound (randomLinearTimeBound c d) := by
  exact (((PolynomialBound.const d).mul ((vectorTimeBound_polynomial c d).add (PolynomialBound.const 1))).add
    (PolynomialBound.const 1)).add
      ((PolynomialBound.const (d+1)).mul ((PolynomialBound.const 13320).mul
        ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 6)))

theorem layerTimeBound_polynomial (d k : ℕ) (i : Fin k) : PolynomialBound (layerTimeBound d k i) := by
  exact ((((((fixedTimeBound_polynomial d).add (randomLinearTimeBound_polynomial i.val d)).add
    (randomLinearTimeBound_polynomial (i.val+k) d)).add (hashedColumnTimeBound_polynomial i.val)).add
      ((PolynomialBound.const 22).mul PolynomialBound.identity)).add (PolynomialBound.const (2*i.val))).add
        (PolynomialBound.const 30)




theorem layerTimeBound_le_uniform (d k M : ℕ) (i : Fin k) :
    layerTimeBound d k i M    ≤    layerTimeUniform d k M := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (layerTimeBound d k j M)) (Finset.mem_univ i)

theorem layerTimeUniform_polynomial (d k : ℕ) : PolynomialBound (layerTimeUniform d k) := by
  classical
  have hs : ∀ s : Finset (Fin k),PolynomialBound (fun M => s.sum (fun i => layerTimeBound d k i M)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using PolynomialBound.const 0
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using (layerTimeBound_polynomial d k i).add ih
  exact hs Finset.univ

namespace Storage

theorem point_injective (d k : ℕ) : Function.Injective (point d k) := by
  intro i j hij; apply Fin.ext
  have hh := congrArg Fin.val hij
  simp only [point_val] at hh
  omega













































































































































































end Storage




namespace Storage

theorem countdown_injective (d k : ℕ) : Function.Injective (countdown d k) := by
  intro i j hij; apply Fin.ext
  have hh := congrArg Fin.val hij
  simp only [countdown_val] at hh
  omega

theorem point_ne_countdown (d k : ℕ) (j a : Fin d) : point d k j≠countdown d k a := by
  intro hij
  have hh := congrArg Fin.val hij
  simp only [point_val,countdown_val] at hh
  have := j.isLt
  omega

theorem used_map_pairs (d k : ℕ) (js : List (Fin d)) :
    SamplerOdometer.used (js.map (fun j => (point d k j,countdown d k j)))=
      js.flatMap (fun j => [point d k j,countdown d k j]) := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [SamplerOdometer.used,ih]

@[simp] theorem pointPairs_length (d k : ℕ) : (pointPairs d k).length=d := by simp [pointPairs]







theorem used_pointPairs_nodup (d k : ℕ) : (SamplerOdometer.used (pointPairs d k)).Nodup := by
  rw [pointPairs,used_map_pairs]
  apply List.nodup_flatMap.mpr
  constructor
  · intro j hj
    simp [point_ne_countdown d k j j]
  · apply (List.nodup_finRange d).imp
    intro a b hab
    apply List.disjoint_left.mpr
    intro x hx hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx hy
    rcases hx with rfl|rfl
    · rcases hy with hp|hc
      · exact hab (point_injective d k hp)
      · exact point_ne_countdown d k a b hc
    · rcases hy with hp|hc
      · exact point_ne_countdown d k b a hp.symm
      · exact hab (countdown_injective d k hc)

theorem used_pointPairs_high (d k : ℕ) :
    ∀ x∈SamplerOdometer.used (pointPairs d k),80   ≤   x.val := by
  rw [pointPairs,used_map_pairs]
  intro x hx
  obtain ⟨j,hj,hx⟩ := List.mem_flatMap.mp hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl <;> simp only [point_val,countdown_val] <;> omega

theorem pointPairs_nodup (d k : ℕ) :
    (low d k 35::low d k 61::SamplerOdometer.used (pointPairs d k)).Nodup := by
  simp only [List.nodup_cons,List.mem_cons,not_or]
  refine ⟨⟨(low_injective d k).ne (by decide),?_⟩,?_,used_pointPairs_nodup d k⟩
  · intro hx
    have hh := used_pointPairs_high d k _ hx
    simp [low] at hh
  · intro hx
    have hh := used_pointPairs_high d k _ hx
    simp [low] at hh
end Storage

























































































































































































































































































































































































































































































































































































end ExpandingCodes.Computation.SamplerProgram

end FlattenModule61


section FlattenModule62


set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterPowers
open NKtLB SamplerEvaluation SamplerProgram
open ExpandingCodes.PolynomialStretch BinaryPolynomial
open FieldPrograms UnaryArithmetic
variable {R B : ℕ}



































































































































































































































































































end ExpandingCodes.Computation.TesterPowers

end FlattenModule62


section FlattenModule63



set_option autoImplicit false
open scoped BigOperators
namespace ExpandingCodes.Computation.TesterEvaluation
open NKtLB SamplerEvaluation SamplerProgram TesterPowers
open FieldPrograms UnaryArithmetic
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B : ℕ}




































































































































































































































































































































































































































































end ExpandingCodes.Computation.TesterEvaluation

end FlattenModule63


section FlattenModule64



set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterInput
open NKtLB SamplerEvaluation
open FieldPrograms UnaryArithmetic
variable {R B : ℕ}






















































































































































































































































































































end ExpandingCodes.Computation.TesterInput

end FlattenModule64


section FlattenModule65


set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}





























































































































































































































































end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule65


section FlattenModule66


set_option autoImplicit false
namespace ExpandingCodes.Computation
namespace SizeParameters





































































































end SizeParameters
end ExpandingCodes.Computation

end FlattenModule66


section FlattenModule67



set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}




















































































































































































































































































































































































































end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule67


section FlattenModule68


set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}











































































































































end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule68


section FlattenModule69


set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}




























































































































end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule69


section FlattenModule70





set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}




































































































































end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule70

/-! Inlined whole module: ExpandingCodes.Computation.ParameterPolynomial -/
section FlattenModule71


set_option autoImplicit false
namespace ExpandingCodes.Computation
namespace ParameterPrograms





namespace PolynomialMajorant

theorem const (C : ℕ) : PolynomialMajorant (fun _ => C) := ⟨C,0,by simp⟩
theorem id : PolynomialMajorant (fun n => n) := ⟨1,1,by intro n; simp⟩






theorem add {f g : ℕ → ℕ} (hf : PolynomialMajorant f) (hg : PolynomialMajorant g) :
    PolynomialMajorant (fun n => f n+g n) := by
  obtain ⟨C,a,hf⟩ := hf
  obtain ⟨D,b,hg⟩ := hg
  refine ⟨C+D,a+b,?_⟩
  intro n
  have hpa : (n+1)^a≤(n+1)^(a+b) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpb : (n+1)^b≤(n+1)^(a+b) := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    f n+g n≤C*(n+1)^a+D*(n+1)^b := Nat.add_le_add (hf n) (hg n)
    _≤C*(n+1)^(a+b)+D*(n+1)^(a+b) :=
      Nat.add_le_add (Nat.mul_le_mul_left C hpa) (Nat.mul_le_mul_left D hpb)
    _=(C+D)*(n+1)^(a+b) := by ring

theorem mul {f g : ℕ → ℕ} (hf : PolynomialMajorant f) (hg : PolynomialMajorant g) :
    PolynomialMajorant (fun n => f n*g n) := by
  obtain ⟨C,a,hf⟩ := hf
  obtain ⟨D,b,hg⟩ := hg
  refine ⟨C*D,a+b,?_⟩
  intro n
  calc
    f n*g n≤(C*(n+1)^a)*(D*(n+1)^b) := Nat.mul_le_mul (hf n) (hg n)
    _=(C*D)*(n+1)^(a+b) := by rw [pow_add]; ring

theorem pow {f : ℕ → ℕ} (hf : PolynomialMajorant f) (e : ℕ) :
    PolynomialMajorant (fun n => (f n)^e) := by
  obtain ⟨C,a,hf⟩ := hf
  refine ⟨C^e,a*e,?_⟩
  intro n
  calc
    (f n)^e≤(C*(n+1)^a)^e := Nat.pow_le_pow_left (hf n) e
    _=C^e*(n+1)^(a*e) := by rw [mul_pow,pow_mul]

theorem comp {f g : ℕ → ℕ} (hf : PolynomialMajorant f) (hg : PolynomialMajorant g) :
    PolynomialMajorant (fun n => f (g n)) := by
  obtain ⟨C,a,hf⟩ := hf
  obtain ⟨D,b,hg⟩ := (hg.add (const 1)).pow a
  refine ⟨C*D,b,?_⟩
  intro n
  calc
    f (g n)≤C*(g n+1)^a := hf _
    _≤C*(D*(n+1)^b) := Nat.mul_le_mul_left C (hg n)
    _=(C*D)*(n+1)^b := by ring

end PolynomialMajorant









theorem powerCounterBound_polynomial (e : ℕ) : PolynomialMajorant (powerCounterBound e) :=
  ⟨e+1,e+1,fun _ => Nat.le_refl _⟩
theorem powerTimeBound_polynomial (e : ℕ) : PolynomialMajorant (powerTimeBound e) :=
  ⟨512*(e+1)^3,2*(e+1),fun _ => Nat.le_refl _⟩
theorem ceilingCounterBound_polynomial : PolynomialMajorant ceilingCounterBound :=
  ⟨2,1,by intro n; simp [ceilingCounterBound]; omega⟩
theorem ceilingTimeBound_polynomial : PolynomialMajorant ceilingTimeBound :=
  ⟨512,2,fun _ => Nat.le_refl _⟩
theorem divisionTimeBound_polynomial : PolynomialMajorant divisionTimeBound :=
  ⟨16,1,by intro n; simp [divisionTimeBound]⟩
theorem floorCounterBound_polynomial : PolynomialMajorant floorCounterBound :=
  ⟨4,1,by intro n; simp [floorCounterBound]; omega⟩
theorem floorTimeBound_polynomial : PolynomialMajorant floorTimeBound :=
  ⟨4096,2,fun _ => Nat.le_refl _⟩










theorem setup_bounds_polynomial (d : ℕ) :
    PolynomialMajorant (setupTimeBound d) ∧ PolynomialMajorant (setupCounterBound d) := by
  have h₁ := powerCounterBound_polynomial (2*d)
  have h₂ := ceilingCounterBound_polynomial.comp h₁
  have h₃ := (powerCounterBound_polynomial d).comp h₂
  constructor
  · exact ((((((((powerTimeBound_polynomial (2*d)).add (PolynomialMajorant.const 1)).add
      (ceilingTimeBound_polynomial.comp h₁)).add (PolynomialMajorant.const 1)).add
      ((powerTimeBound_polynomial d).comp h₂)).add (PolynomialMajorant.const 1)).add
      (divisionTimeBound_polynomial.comp h₃)).add (PolynomialMajorant.const 1)).add
      (floorTimeBound_polynomial.comp h₃)
  · exact floorCounterBound_polynomial.comp h₃


end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule71


section FlattenModule72


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB
namespace SizeReader
variable {R B : ℕ}












 










































 



























end SizeReader
end ExpandingCodes.Computation

end FlattenModule72


section FlattenModule73




set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}























































































































































































































































































end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule73


section FlattenModule74


set_option autoImplicit false
open scoped BigOperators

namespace ExpandingCodes.Computation.RawIrreducibility
open Polynomial
open ExpandingCodes.PolynomialStretch BinaryPolynomial BinaryField
open FieldConvolution FieldCertificates FieldPrograms













































































































































end ExpandingCodes.Computation.RawIrreducibility

end FlattenModule74


section FlattenModule75



set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.SourceModulus
open NKtLB FieldPrograms FieldConvolution FieldCertificates SourceFieldArithmetic
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B : ℕ}














































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end ExpandingCodes.Computation.SourceModulus

end FlattenModule75


section FlattenModule76


set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.SourceFieldSetup
open NKtLB FieldPrograms FieldConvolution SourceFieldArithmetic
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B : ℕ}



























































































































































































































end ExpandingCodes.Computation.SourceFieldSetup

end FlattenModule76

/-! Inlined whole module: ExpandingCodes.Computation.TesterGram -/
section FlattenModule77






set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterGram
open NKtLB























































































































@[simp] theorem low_eq_iff (d : ℕ) (i j : Fin 80) : low d i=low d j ↔ i=j := by
  constructor
  · intro hij
    exact Fin.ext (congrArg (Fin.val : Registers d → ℕ) hij)
  · exact congrArg (low d)



























































































































































































































end ExpandingCodes.Computation.TesterGram

end FlattenModule77


section FlattenModule78


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace TapeInstr
variable {R B S C L : ℕ}















end TapeInstr

namespace TapeCfg
variable {R B S C L : ℕ}



end TapeCfg

namespace TapeStore
variable {R B S C L : ℕ}







end TapeStore

namespace TapeProgram
variable {R B S C L : ℕ}


















































































































end TapeProgram
end ExpandingCodes.Computation

end FlattenModule78

/-! Inlined whole module: ExpandingCodes.Computation.GaussianProgram -/
section FlattenModule79




set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianProgram

open NKtLB TapeArrays







































































































section SearchLoop

variable {R B L : ℕ}
































@[simp] theorem searchLoop_tail (P : TapeProgram R B L) (remaining value index found : Fin R)
    (k : Fin 6) :
    (searchLoop P remaining value index found).code (searchLabel L k) =
      if k = 0 then .dec remaining (searchLabel L 5) (TapeProgram.leftLabel 6 P.entry)
      else if k = 1 then .dec value (searchLabel L 2) (searchLabel L 3)
      else if k = 2 then .inc index (searchLabel L 0)
      else if k = 3 then .inc value (searchLabel L 4)
      else if k = 4 then .inc found (searchLabel L 5) else .halt := by
  simp [searchLoop, searchLabel, TapeProgram.rightLabel]
























































































end SearchLoop






































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































@[simp] theorem paddedSchur_apply {α : Type*} (O : EncodedGaussian.Operations α) {m n : ℕ}
    (A : Gaussian.Table α m n) (p : Fin m × Fin n) (i : Fin m) (j : Fin n) :
    Gaussian.toMatrix (paddedSchur O A p) i j = O.sub (Gaussian.toMatrix A i j)
      (O.mul (O.mul (Gaussian.toMatrix A i p.2) (O.inv (Gaussian.toMatrix A p.1 p.2)))
        (Gaussian.toMatrix A p.1 j)) := by
  simp [paddedSchur, Gaussian.toMatrix, Gaussian.ofMatrix]
















































end ExpandingCodes.Computation.GaussianProgram

end FlattenModule79

/-! Inlined whole module: ExpandingCodes.Computation.TesterGramCorrectness -/
section FlattenModule80




set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterGram
open NKtLB
open ExpandingCodes.PolynomialStretch




@[simp] theorem tuple_zero (d : ℕ) : tuple d 0=aDigits d := rfl
@[simp] theorem tuple_one (d : ℕ) : tuple d 1=bDigits d := rfl
@[simp] theorem tuple_two (d : ℕ) : tuple d 2=zDigits d := rfl


























































































































































































































































































































































































@[simp] theorem pointPrefix_zero (d ell : ℕ) (h : 0<ell) (D : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) :
    pointPrefix d ell h D y a b 0=BinaryField.zeroIndex ell := rfl


















@[simp] theorem pointPrefix_full (d ell : ℕ) (h : 0<ell) (D : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) :
    pointPrefix d ell h D y a b ((2^ell)^d)=
      (EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1 := by
  unfold pointPrefix EncodedTester.entry
  rw [List.take_of_length_le (by simp)]





















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end ExpandingCodes.Computation.TesterGram

end FlattenModule80

/-! Inlined whole module: ExpandingCodes.Computation.RuntimeBounds -/
section FlattenModule81



set_option autoImplicit false

namespace ExpandingCodes.Computation

theorem ParameterPrograms.PolynomialMajorant.toPolynomialBound {f : ℕ → ℕ}
    (hf : ParameterPrograms.PolynomialMajorant f) : PolynomialBound f := by
  obtain ⟨C,a,hf⟩ := hf
  exact ⟨C,a,fun n _ => hf n⟩

/-- Finitely many excluded sizes only affect the numerical coefficient.
This arithmetic conversion asserts no source execution by itself. -/
theorem PolynomialBound.toMajorant {f : ℕ → ℕ} (hf : PolynomialBound f) :
    ParameterPrograms.PolynomialMajorant f := by
  obtain ⟨C,a,hf⟩ := hf
  let D := C+f 0+f 1
  refine ⟨D,a,?_⟩
  intro n
  by_cases hn : 2 ≤ n
  · exact (hf n hn).trans (Nat.mul_le_mul_right _ (by dsimp [D]; omega))
  · have hcases : n = 0 ∨ n = 1 := by omega
    have hp : 1 ≤ (n+1)^a := one_le_pow₀ (by omega)
    have hD : D ≤ D*(n+1)^a := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left D hp
    apply le_trans (b := D) ?_ hD
    rcases hcases with rfl | rfl <;> dsimp [D] <;> omega

theorem PolynomialBound.comp {f g : ℕ → ℕ} (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun n => f (g n)) :=
  (hf.toMajorant.comp hg.toMajorant).toPolynomialBound

end ExpandingCodes.Computation

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation
















end ExpandingCodes.PolynomialStretch

end FlattenModule81


section FlattenModule82


set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation

































































end ExpandingCodes.PolynomialStretch

end FlattenModule82


section FlattenModule83



set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterPrefix
open NKtLB TesterGram FieldPrograms
open ExpandingCodes.PolynomialStretch




































































































































































































































































end ExpandingCodes.Computation.TesterPrefix

end FlattenModule83


section FlattenModule84


set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterFrontend
open NKtLB TesterGram TesterPrefix
open ExpandingCodes.PolynomialStretch



























































































































end ExpandingCodes.Computation.TesterFrontend

end FlattenModule84

/-! Inlined whole module: ExpandingCodes.Computation.GaussianGrid -/
section FlattenModule85


set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianGrid

open NKtLB GaussianProgram



























































































@[simp] theorem addressStore_D (d : Store) : (addressStore d).reg 9 = d.reg 41+d.reg 42 := by
  simp [addressStore,sumPost,TapeStore.setReg]
@[simp] theorem addressStore_C (d : Store) : (addressStore d).reg 10 = d.reg 41+d.reg 43 := by
  simp [addressStore,sumPost,TapeStore.setReg]
@[simp] theorem addressStore_B (d : Store) : (addressStore d).reg 11 = d.reg 44+d.reg 42 := by
  simp [addressStore,sumPost,TapeStore.setReg]
@[simp] theorem addressStore_target (d : Store) : (addressStore d).reg 12 = d.reg 45 := by
  simp [addressStore,sumPost,TapeStore.setReg]
































































































































































































































































































































































































































































































































































































































































































































































































end ExpandingCodes.Computation.GaussianGrid

end FlattenModule85


section FlattenModule86



set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianPivot
open NKtLB GaussianProgram
open ExpandingCodes.PolynomialStretch
























































































































































































































































































































































end ExpandingCodes.Computation.GaussianPivot

end FlattenModule86

/-! Inlined whole module: ExpandingCodes.Computation.PaddedGaussian -/
section FlattenModule87



set_option autoImplicit false

namespace ExpandingCodes.Computation.PaddedGaussian
open GaussianProgram EncodedGaussian
open ExpandingCodes.PolynomialStretch

variable {q m n : ℕ}






























































































@[simp] theorem step_done (O : Operations (Fin q)) (s : State q m n) (hd : s.done = true) :
    step O s = s := by simp [step,hd]












variable {F : Type*} [Field F] [DecidableEq F]
variable {O : Operations (Fin q)} {decode : Fin q → F}










































































end ExpandingCodes.Computation.PaddedGaussian

end FlattenModule87

/-! Inlined whole module: ExpandingCodes.Computation.GaussianDriver -/
section FlattenModule88




set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianDriver

open NKtLB GaussianProgram GaussianGrid

section Branch
variable {R B L K : ℕ}



















@[simp] theorem branchZero_code_zero (P : TapeProgram R B L) (Q : TapeProgram R B K) (r : Fin R) (j : Fin L) :
    (branchZero P Q r).code (zeroLabel K j) = (P.code j).relabel (zeroLabel K) := by
  simp [branchZero,zeroLabel,TapeProgram.leftLabel]

@[simp] theorem branchZero_code_positive (P : TapeProgram R B L) (Q : TapeProgram R B K) (r : Fin R) (j : Fin K) :
    (branchZero P Q r).code (positiveLabel L j) = (Q.code j).relabel (positiveLabel L) := by
  simp [branchZero,positiveLabel,TapeProgram.leftLabel,TapeProgram.rightLabel]

@[simp] theorem branchZero_code_header (P : TapeProgram R B L) (Q : TapeProgram R B K) (r : Fin R) (j : Fin 2) :
    (branchZero P Q r).code (branchLabel L K j) =
      if j = 0 then .dec r (zeroLabel K P.entry) (branchLabel L K 1)
      else .inc r (positiveLabel L Q.entry) := by
  simp [branchZero,branchLabel,TapeProgram.rightLabel]







































end Branch
















@[simp] theorem inputBuffer_not (b : Bool) : inputBuffer (!b) = outputBuffer b := by cases b <;> rfl
@[simp] theorem outputBuffer_not (b : Bool) : outputBuffer (!b) = inputBuffer b := by cases b <;> rfl









































































































































































































































































































































































































































































































































































end ExpandingCodes.Computation.GaussianDriver

end FlattenModule88


section FlattenModule89


set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianDriver
open NKtLB GaussianProgram GaussianGrid EncodedGaussian
open ExpandingCodes.PolynomialStretch






















































































































end ExpandingCodes.Computation.GaussianDriver

end FlattenModule89


section FlattenModule90



set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterProgram

open NKtLB

variable {R B : ℕ}




















































































































































































































end ExpandingCodes.Computation.TesterProgram

end FlattenModule90


section FlattenModule91





set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterSuffix
open NKtLB ParameterPrograms
variable {R B : ℕ}






























































































end ExpandingCodes.Computation.TesterSuffix

end FlattenModule91


section FlattenModule92




set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterBackend
open NKtLB GaussianProgram
open ExpandingCodes.PolynomialStretch












































end ExpandingCodes.Computation.TesterBackend

end FlattenModule92


section FlattenModule93


set_option autoImplicit false

namespace ExpandingCodes.Computation.ZeroTables
open NKtLB TapeArrays
variable {R B K : ℕ}

























































































end ExpandingCodes.Computation.ZeroTables

end FlattenModule93


section FlattenModule94





set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterBackendPrep
open NKtLB UnaryArithmetic FieldPrograms TapeArrays GaussianProgram
open ExpandingCodes.PolynomialStretch





































































































































end ExpandingCodes.Computation.TesterBackendPrep

end FlattenModule94


section FlattenModule95


set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterBackendComplete
open NKtLB GaussianProgram TapeArrays
open ExpandingCodes.PolynomialStretch
open TesterBackendPrep











































































































































end ExpandingCodes.Computation.TesterBackendComplete

end FlattenModule95


section FlattenModule96



set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterAssembly
open NKtLB GaussianProgram TapeArrays
open ExpandingCodes.PolynomialStretch




















































end ExpandingCodes.Computation.TesterAssembly

end FlattenModule96

/-! Inlined whole module: ExpandingCodes.Computation.SourceBridge -/
section FlattenModule97





set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

theorem wordBits_injective {m : ℕ} : Function.Injective (wordBits (m := m)) := by
  intro v w h
  have hh := List.ofFn_injective h
  funext i
  have hi := congrFun hh i
  have hcases (a : Bit) : a = 0 ∨ a = 1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hcases (v i) with hv | hv <;> rcases hcases (w i) with hw | hw <;> simp_all

theorem matrixBits_injective {m n : ℕ} :
    Function.Injective (matrixBits (m := m) (n := n)) := by
  induction m with
  | zero =>
    intro G H h
    funext i
    exact Fin.elim0 i
  | succ m ih =>
    intro G H h
    have hs : wordBits (G 0) ++ matrixBits (fun i => G i.succ) =
        wordBits (H 0) ++ matrixBits (fun i => H i.succ) := by
      simpa only [matrixBits, wordBits, List.ofFn_succ, List.flatten_cons] using h
    obtain ⟨hzero, htail⟩ := List.append_inj hs (by simp [wordBits])
    have hz := wordBits_injective hzero
    have ht := ih htail
    funext i
    exact Fin.cases hz (fun j => congrFun ht j) i

open ExpandingCodes.Computation





















/-- The sampler compiler bridge separates source execution from the independently
provable finite uniform law of its mathematical output function. -/
theorem samplerImplementation_of_tape {R B L : ℕ}
    (θ : ℚ) (g : ∀ n, Geometry (dimension (θ : ℝ)) n)
    (P : TapeProgram R B L) (C a N : ℕ) (hN : 2 ≤ N)
    (f : ∀ n, (Fin ((2*C+1) * (n+1)^a) → Bool) →
      Generator (rowCount (dimension (θ : ℝ)) n) n)
    (h : ∀ n ≥ N, ∀ ω : Fin ((2*C+1) * (n+1)^a) → Bool,
      ∃ t ≤ C * (n+1)^a,
        P.halted (P.run ⟨sizeInput n, [], [], List.ofFn ω⟩ t) ∧
          (P.run ⟨sizeInput n, [], [], List.ofFn ω⟩ t).output = matrixBits (f n ω))
    (hlaw : ∀ n ≥ N, ∀ G : Generator (rowCount (dimension (θ : ℝ)) n) n,
      uniformProb (fun ω : Fin ((2*C+1) * (n+1)^a) → Bool => f n ω = G) =
        (sampleLaw (θ : ℝ) n (g n) G).toReal) : SamplerImplementation θ g := by
  let M := TapeCompiler.compile P
  have hr (n : ℕ) (hn : N ≤ n) (ω : Fin ((2*C+1) * (n+1)^a) → Bool) :
      sampledRun M n ((2*C+1) * (n+1)^a) ((2*C+1) * (n+1)^a) ω
        (matrixBits (f n ω)) := by
    obtain ⟨t, ht, hh, hout⟩ := h n hn ω
    have hp : 1 ≤ (n+1)^a := one_le_pow₀ (by omega)
    have htime : 1+2*t ≤ (2*C+1) * (n+1)^a := by nlinarith
    have hm := (TapeCompiler.compile_halts P ∅ ⟨sizeInput n, [], [], List.ofFn ω⟩ t hh).mono htime
    simpa only [sampledRun, M, hout] using hm
  refine ⟨M, 2*C+1, a, N, by omega, hN, ?_⟩
  intro n hn
  refine ⟨fun ω => ⟨f n ω, hr n hn ω⟩, ?_⟩
  intro G
  rw [← hlaw n hn G]
  apply uniformProb_congr
  intro ω
  constructor
  · intro hrun
    have hb := NKtLB.Machine.HaltsWith.output_unique hrun (hr n hn ω)
    exact (matrixBits_injective (NKtLB.Machine.bitsSym_injective hb)).symm
  · intro heq
    rw [← heq]
    exact hr n hn ω

end ExpandingCodes.PolynomialStretch

end FlattenModule97


section FlattenModule98




set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation






















end ExpandingCodes.PolynomialStretch

end FlattenModule98


section FlattenModule99





set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterImplementation
open NKtLB TesterGram
open ExpandingCodes.PolynomialStretch



































































end ExpandingCodes.Computation.TesterImplementation

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation
















end ExpandingCodes.PolynomialStretch

end FlattenModule99

/-! Inlined whole module: ExpandingCodes.Computation.NeighborWriter -/
section FlattenModule100



set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ExpandingCodes.Computation
open NKtLB
namespace NeighborWriter
open TapeProgram ParameterPrograms
variable {R B : ℕ}



theorem reverse_injective (r : Fin 6 → Fin R) (hr : Function.Injective r) :
    Function.Injective (reverse r) := hr.comp (Equiv.swap 0 1).injective

@[simp] theorem reverse_zero (r : Fin 6 → Fin R) : reverse r 0 = r 1 := by simp [reverse]
@[simp] theorem reverse_one (r : Fin 6 → Fin R) : reverse r 1 = r 0 := by simp [reverse]
@[simp] theorem reverse_two (r : Fin 6 → Fin R) : reverse r 2 = r 2 := by simp [reverse, Equiv.swap_apply_def]
@[simp] theorem reverse_three (r : Fin 6 → Fin R) : reverse r 3 = r 3 := by simp [reverse, Equiv.swap_apply_def]
@[simp] theorem reverse_four (r : Fin 6 → Fin R) : reverse r 4 = r 4 := by simp [reverse, Equiv.swap_apply_def]
@[simp] theorem reverse_five (r : Fin 6 → Fin R) : reverse r 5 = r 5 := by simp [reverse, Equiv.swap_apply_def]

theorem lessThanStore_other (r : Fin 6 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₂ : j ≠ r 2) (h₃ : j ≠ r 3) (h₄ : j ≠ r 4) (h₅ : j ≠ r 5) :
    (lessThanStore r d).reg j = d.reg j := by
  simp [lessThanStore, lessCore, lessPrepare, ltLoopStore, TapeStore.setReg, h₂,h₃,h₄,h₅]
















theorem markStore_other (r : Fin 6 → Fin R) (out : Fin R) (d : TapeStore R B) (j : Fin R)
    (ho : j ≠ out) (h₂ : j ≠ r 2) (h₃ : j ≠ r 3) (h₄ : j ≠ r 4) (h₅ : j ≠ r 5) :
    (markStore r out d).reg j = d.reg j := by
  have hrev := lessThanStore_other (reverse r) (lessThanStore r d) j
    (by simpa using h₂) (by simpa using h₃) (by simpa using h₄) (by simpa using h₅)
  have hdir := lessThanStore_other r d j h₂ h₃ h₄ h₅
  dsimp only [markStore]
  split_ifs <;> simp [TapeStore.setReg, ho, hrev, hdir]

theorem markStore_out (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (out : Fin R) (ho : ∀ j, out ≠ r j) (d : TapeStore R B) :
    (markStore r out d).reg out =
      if d.reg (r 0) = d.reg (r 1) then 1 else d.reg out := by
  have hdir := lessThanStore_other r d out (ho 2) (ho 3) (ho 4) (ho 5)
  have hrev := lessThanStore_other (reverse r) (lessThanStore r d) out
    (by simpa using ho 2) (by simpa using ho 3) (by simpa using ho 4) (by simpa using ho 5)
  have hzero := lessThanStore_preserves r hr d 0 (by simp)
  have hone := lessThanStore_preserves r hr d 1 (by simp)
  have hv₂ : (lessThanStore (reverse r) (lessThanStore r d)).reg (r 2) =
      if d.reg (r 1) < d.reg (r 0) then 1 else 0 := by
    simpa only [reverse_two, reverse_zero, reverse_one, hzero, hone] using
      lessThanStore_value (reverse r) (reverse_injective r hr) (lessThanStore r d)
  dsimp only [markStore]
  rw [lessThanStore_value r hr d]
  by_cases hxy : d.reg (r 0) < d.reg (r 1)
  · simp [hxy, Nat.ne_of_lt hxy, hdir]
  · simp only [hxy, if_false, ite_true, hv₂]
    by_cases hyx : d.reg (r 1) < d.reg (r 0)
    · simp [hyx, Ne.symm (Nat.ne_of_lt hyx), hrev, hdir]
    · have he : d.reg (r 0) = d.reg (r 1) := by omega
      simp [hyx, he, TapeStore.setReg]

theorem markStore_bound (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (out : Fin R) (d : TapeStore R B) (M : ℕ) (hM : 1 ≤ M)
    (hd : ∀ j, d.reg j ≤ M) : ∀ j, (markStore r out d).reg j ≤ M := by
  have h₁ := lessThanStore_bound r hr d M hM hd
  have h₂ := lessThanStore_bound (reverse r) (reverse_injective r hr)
    (lessThanStore r d) M hM h₁
  dsimp only [markStore]
  split_ifs
  · exact FieldPrograms.setReg_bound _ out 1 M h₂ hM
  · exact h₂
  · exact h₁

theorem markEq_stops (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (out : Fin R) (inp : Inputs) (d : TapeStore R B) (M : ℕ) (hM : 1 ≤ M)
    (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 160*(M+1) ∧
      (markEq r out).Stops inp (d.toCfg (markEq (B := B) r out).entry) t e ∧
      e.store = markStore r out d := by
  obtain ⟨t,c,ht,hc,hcs⟩ := lessThan_stops r hr inp M hM d hd
  have hb : ∀ j, c.store.reg j ≤ M := by
    rw [hcs]
    exact lessThanStore_bound r hr d M hM hd
  have hskip (s : TapeStore R B) :
      ∃ t e, t ≤ 0 ∧ (skip : TapeProgram R B 1).Stops inp
        (s.toCfg (skip : TapeProgram R B 1).entry) t e ∧ e.store = s :=
    ⟨0,s.toCfg 0,le_rfl,skip_stops inp s,rfl⟩
  have hsecond (s : TapeStore R B) (hs : ∀ j, s.reg j ≤ M) :
      ∃ t e, t ≤ 80*(M+1) ∧
        (TapeProgram.seq (lessThan (reverse r))
          (branchZero (r 2) (loadConstant out 1) skip)).Stops inp
            (s.toCfg (TapeProgram.seq (lessThan (reverse r))
              (branchZero (r 2) (loadConstant (B := B) out 1) skip)).entry) t e ∧
        e.store =
          if (lessThanStore (reverse r) s).reg (r 2) = 0 then
            (lessThanStore (reverse r) s).setReg out 1 else lessThanStore (reverse r) s := by
    obtain ⟨u,e,hu,he,hes⟩ := lessThan_stops (reverse r) (reverse_injective r hr) inp M hM s hs
    have heb : ∀ j, e.store.reg j ≤ M := by
      rw [hes]
      exact lessThanStore_bound (reverse r) (reverse_injective r hr) s M hM hs
    obtain ⟨f,hf,hfs⟩ := loadConstant_stops out 1 inp e.store
    have hload : ∃ t f, t ≤ M+4 ∧ (loadConstant out 1).Stops inp
        (e.store.toCfg (loadConstant (B := B) out 1).entry) t f ∧
          f.store = e.store.setReg out 1 := by
      exact ⟨_,f,by have := heb out; omega,hf,hfs⟩
    obtain ⟨v,f,hv,hf,hfs⟩ := branchZero_stops (r 2) (loadConstant out 1) skip inp
      e.store (e.store.setReg out 1) e.store (M+4) 0 hload (hskip e.store)
    refine ⟨u+1+v, f.mapPC (rightLabel 33), ?_, he.seq hf, ?_⟩
    · simp only [max_eq_left (by omega : 0 ≤ M+4)] at hv
      omega
    · change f.store = _
      have her : e.reg (r 2) = (lessThanStore (reverse r) s).reg (r 2) :=
        congrArg (fun s : TapeStore R B => s.reg (r 2)) hes
      simpa only [hes, her] using hfs
  obtain ⟨u,e,hu,he,hes⟩ := branchZero_stops (r 2)
    (TapeProgram.seq (lessThan (reverse r)) (branchZero (r 2) (loadConstant out 1) skip))
    skip inp c.store
    (if (lessThanStore (reverse r) c.store).reg (r 2) = 0 then
      (lessThanStore (reverse r) c.store).setReg out 1 else lessThanStore (reverse r) c.store)
    c.store (80*(M+1)) 0 (hsecond c.store hb) (hskip c.store)
  refine ⟨t+1+u,e.mapPC (rightLabel 33),?_,?_,?_⟩
  · simp only [max_eq_left (Nat.zero_le _)] at hu
    omega
  · convert hc.seq he using 1 <;> rfl
  · change e.store = _
    have hcr : c.reg (r 2) = (lessThanStore r d).reg (r 2) :=
      congrArg (fun s : TapeStore R B => s.reg (r 2)) hcs
    simpa only [hcs, hcr, markStore] using hes











theorem emitFlag_stops (r : Fin R) (inp : Inputs) (d : TapeStore R B) (h : d.reg r ≤ 1) :
    (emitFlag r).Stops inp (d.toCfg 0) 2 ((emitStore r d).toCfg 3) := by
  by_cases hz : d.reg r = 0
  · have hf : emitStore r d = {d with output := d.output ++ [false]} := by
      simp [emitStore, hz, Function.update_eq_self]
    refine ⟨?_, by simp [TapeProgram.halted, emitFlag]⟩
    rw [hf]
    exact Exec.step (d := d.toCfg 1) (by simp [TapeProgram.halted, emitFlag])
      (by simp [TapeProgram.step, emitFlag, TapeStore.toCfg, hz])
      (Exec.one (by simp [TapeProgram.halted, emitFlag])
        (by simp [TapeProgram.step, emitFlag, TapeStore.toCfg]))
  · have ho : d.reg r = 1 := by omega
    let c := d.setReg r 0
    refine ⟨?_, by simp [TapeProgram.halted, emitFlag]⟩
    exact Exec.step (d := c.toCfg 2) (by simp [TapeProgram.halted, emitFlag])
      (by simp [TapeProgram.step, emitFlag, TapeStore.toCfg, c, TapeStore.setReg, ho])
      (Exec.one (by simp [TapeProgram.halted, emitFlag])
        (by simp [TapeProgram.step, emitFlag, TapeStore.toCfg, emitStore, c, TapeStore.setReg, ho]))







namespace Layout
variable {k : ℕ}












theorem comparison_injective (l : Layout R k) (i : Fin k) :
    Function.Injective (l.comparison i) := by
  apply l.injective.comp
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [comparisonIndex]

theorem out_fresh (l : Layout R k) (i : Fin k) : ∀ j, l.out ≠ l.comparison i j := by
  intro j
  apply l.injective.ne
  fin_cases j <;> simp [comparison, comparisonIndex]

theorem mark_frame (l : Layout R k) (i : Fin k) (d : TapeStore R B)
    (a : Fin 8) (ha : a = 0 ∨ a = 1 ∨ a = 7) :
    (markStore (l.comparison i) l.out d).reg (l.reg (.inl a)) = d.reg (l.reg (.inl a)) := by
  apply markStore_other
  all_goals apply l.injective.ne
  all_goals rcases ha with rfl | rfl | rfl <;> simp [comparison, comparisonIndex]

theorem mark_neighbor (l : Layout R k) (i j : Fin k) (d : TapeStore R B) :
    (markStore (l.comparison i) l.out d).reg (l.neighbor j) = d.reg (l.neighbor j) := by
  apply markStore_other
  all_goals apply l.injective.ne
  all_goals simp [comparison, comparisonIndex]

theorem mark_out (l : Layout R k) (i : Fin k) (d : TapeStore R B) :
    (markStore (l.comparison i) l.out d).reg l.out =
      if d.reg l.col = d.reg (l.neighbor i) then 1 else d.reg l.out :=
  markStore_out (l.comparison i) (l.comparison_injective i) l.out (l.out_fresh i) d
end Layout













theorem marksStore_bound {k : ℕ} (l : Layout R k) (is : List (Fin k))
    (d : TapeStore R B) (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (marksStore l is d).reg j ≤ M := by
  induction is generalizing d with
  | nil => exact hd
  | cons i is ih =>
    exact ih _ (markStore_bound _ (l.comparison_injective i) _ d M hM hd)

theorem marksStore_frame {k : ℕ} (l : Layout R k) (is : List (Fin k))
    (d : TapeStore R B) (a : Fin 8) (ha : a = 0 ∨ a = 1 ∨ a = 7) :
    (marksStore l is d).reg (l.reg (.inl a)) = d.reg (l.reg (.inl a)) := by
  induction is generalizing d with
  | nil => rfl
  | cons i is ih =>
    rw [marksStore,ih]
    exact l.mark_frame i d a ha

theorem marksStore_neighbor {k : ℕ} (l : Layout R k) (is : List (Fin k))
    (d : TapeStore R B) (j : Fin k) :
    (marksStore l is d).reg (l.neighbor j) = d.reg (l.neighbor j) := by
  induction is generalizing d with
  | nil => rfl
  | cons i is ih =>
    rw [marksStore,ih]
    exact l.mark_neighbor i j d

theorem marksStore_out {k : ℕ} (l : Layout R k) (is : List (Fin k)) (d : TapeStore R B) :
    (marksStore l is d).reg l.out =
      if ∃ i ∈ is, d.reg l.col = d.reg (l.neighbor i) then 1 else d.reg l.out := by
  induction is generalizing d with
  | nil => simp [marksStore]
  | cons i is ih =>
    rw [marksStore,ih]
    simp only [Layout.col,l.mark_frame i d 1 (by simp),l.mark_neighbor,l.mark_out]
    by_cases hi : d.reg l.col = d.reg (l.neighbor i)
    · simp [hi]
    · simp [hi]

theorem marks_stops {k : ℕ} (l : Layout R k) (is : List (Fin k))
    (inp : Inputs) (d : TapeStore R B) (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ is.length*(160*(M+1)+1) ∧
      (marks l is).Stops inp (d.toCfg (marks (B := B) l is).entry) t e ∧
      e.store = marksStore l is d := by
  induction is generalizing d with
  | nil => exact ⟨0,d.toCfg (0 : Fin 1),by simp,skip_stops inp d,rfl⟩
  | cons i is ih =>
    obtain ⟨t,c,ht,hc,hcs⟩ := markEq_stops (l.comparison i) (l.comparison_injective i)
      l.out inp d M hM hd
    have hb : ∀ j, c.store.reg j ≤ M := by
      rw [hcs]
      exact markStore_bound _ (l.comparison_injective i) _ d M hM hd
    obtain ⟨s,e,hs,he,hes⟩ := ih c.store hb
    refine ⟨t+1+s,e.mapPC (rightLabel 77),?_,hc.seq he,?_⟩
    · simp only [List.length_cons]
      nlinarith
    · change e.store = _
      rw [hes,hcs]
      rfl

theorem markStore_payload (r : Fin 6 → Fin R) (out : Fin R) (d : TapeStore R B) :
    (markStore r out d).roHead = d.roHead ∧ (markStore r out d).output = d.output ∧
      (markStore r out d).bufferTape = d.bufferTape ∧
      (markStore r out d).bufferHead = d.bufferHead := by
  dsimp only [markStore]
  split_ifs <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem marksStore_payload {k : ℕ} (l : Layout R k) (is : List (Fin k)) (d : TapeStore R B) :
    (marksStore l is d).roHead = d.roHead ∧ (marksStore l is d).output = d.output ∧
      (marksStore l is d).bufferTape = d.bufferTape ∧
      (marksStore l is d).bufferHead = d.bufferHead := by
  induction is generalizing d with
  | nil => exact ⟨rfl,rfl,rfl,rfl⟩
  | cons i is ih =>
    obtain ⟨hr,ho,hb,hh⟩ := markStore_payload (l.comparison i) l.out d
    obtain ⟨ir,io,ib,ihd⟩ := ih (markStore (l.comparison i) l.out d)
    exact ⟨ir.trans hr,io.trans ho,ib.trans hb,ihd.trans hh⟩













theorem bodyStore_col {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (bodyStore l d).reg l.col = d.reg l.col+1 := by
  have hcol : l.col ≠ l.out := l.injective.ne (by simp)
  simp [bodyStore,emitStore,TapeStore.setReg,hcol,
    marksStore_frame l (List.finRange k) d 1 (by simp)]

theorem bodyStore_out {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (bodyStore l d).reg l.out = 0 := by
  have hcol : l.out ≠ l.col := l.injective.ne (by simp)
  simp [bodyStore,emitStore,TapeStore.setReg,hcol]

theorem bodyStore_frame {k : ℕ} (l : Layout R k) (d : TapeStore R B)
    (a : Fin 8) (ha : a = 0 ∨ a = 7) :
    (bodyStore l d).reg (l.reg (.inl a)) = d.reg (l.reg (.inl a)) := by
  have hc : l.reg (.inl a) ≠ l.col := by apply l.injective.ne; rcases ha with rfl | rfl <;> simp
  have ho : l.reg (.inl a) ≠ l.out := by apply l.injective.ne; rcases ha with rfl | rfl <;> simp
  simp only [bodyStore,TapeStore.setReg,Function.update_of_ne hc,emitStore,Function.update_of_ne ho]
  exact marksStore_frame l (List.finRange k) d a (by rcases ha with h | h <;> simp [h])

theorem bodyStore_neighbor {k : ℕ} (l : Layout R k) (d : TapeStore R B) (i : Fin k) :
    (bodyStore l d).reg (l.neighbor i) = d.reg (l.neighbor i) := by
  have hc : l.neighbor i ≠ l.col := l.injective.ne (by simp)
  have ho : l.neighbor i ≠ l.out := l.injective.ne (by simp)
  simp [bodyStore,TapeStore.setReg,emitStore,hc,ho,marksStore_neighbor]

theorem bodyStore_output {k : ℕ} (l : Layout R k) (d : TapeStore R B) (h : d.reg l.out = 0) :
    (bodyStore l d).output = d.output ++ [decide (∃ i, d.reg l.col = d.reg (l.neighbor i))] := by
  have hm := marksStore_out l (List.finRange k) d
  simp only [List.mem_finRange,true_and,h] at hm
  have hp := (marksStore_payload l (List.finRange k) d).2.1
  dsimp only [bodyStore,TapeStore.setReg,emitStore]
  rw [hm,hp]
  by_cases he : ∃ i, d.reg l.col = d.reg (l.neighbor i) <;> simp [he]

theorem bodyStore_bound {k : ℕ} (l : Layout R k) (d : TapeStore R B) (M : ℕ)
    (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) (hc : d.reg l.col < M) :
    ∀ j, (bodyStore l d).reg j ≤ M := by
  have hm := marksStore_bound l (List.finRange k) d M hM hd
  have hb : ∀ j, (emitStore l.out (marksStore l (List.finRange k) d)).reg j ≤ M :=
    FieldPrograms.setReg_bound _ l.out 0 M hm (by omega)
  intro j
  by_cases hj : j = l.col
  · subst j
    rw [bodyStore_col]
    omega
  · simpa only [bodyStore,TapeStore.setReg,Function.update_of_ne hj] using hb j

theorem body_stops {k : ℕ} (l : Layout R k) (inp : Inputs) (d : TapeStore R B)
    (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) (ho : d.reg l.out ≤ 1) :
    ∃ t e, t ≤ k*(160*(M+1)+1)+5 ∧
      (body l).Stops inp (d.toCfg (body (B := B) l).entry) t e ∧ e.store = bodyStore l d := by
  obtain ⟨t,c,ht,hc,hcs⟩ := marks_stops l (List.finRange k) inp d M hM hd
  have hb : c.reg l.out ≤ 1 := by
    change c.store.reg l.out ≤ 1
    rw [hcs,marksStore_out]
    split <;> omega
  have he := emitFlag_stops l.out inp c.store hb
  have hi := TapeMacros.increment_stops l.col inp (emitStore l.out c.store)
  have hall := (hc.seq he).seq hi
  let e := ((emitStore l.out c.store).setReg l.col ((emitStore l.out c.store).reg l.col+1)).toCfg (1 : Fin 2)
  refine ⟨t+5,e.mapPC (rightLabel (marksLabels (List.finRange k).length+4)),?_,?_,?_⟩
  · simpa only [List.length_finRange] using Nat.add_le_add_right ht 5
  · convert hall using 1 <;> rfl
  · change (emitStore l.out c.store).setReg l.col ((emitStore l.out c.store).reg l.col+1) = _
    rw [hcs]
    rfl





theorem dec_col {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (decStore l.count d).reg l.col = d.reg l.col := by
  simp [decStore,show l.col ≠ l.count from l.injective.ne (by simp)]

theorem dec_out {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (decStore l.count d).reg l.out = d.reg l.out := by
  simp [decStore,show l.out ≠ l.count from l.injective.ne (by simp)]




























theorem loopStore_output {k : ℕ} (l : Layout R k) (n : ℕ) (d : TapeStore R B) (ho : d.reg l.out = 0) :
    (loopStore l n d).output = d.output ++
      List.ofFn (fun j : Fin n => decide (∃ i, d.reg l.col+j.val = d.reg (l.neighbor i))) := by
  induction n generalizing d with
  | zero => simp [loopStore]
  | succ n ih =>
    rw [loopStore,ih _ (bodyStore_out l _),bodyStore_output l _ (by rw [dec_out]; exact ho)]
    simp [bodyStore_col,bodyStore_neighbor,decStore,Layout.col,Layout.count,Layout.neighbor,
      l.injective.eq_iff,List.ofFn_succ,List.append_assoc,
      Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem loop_stops {k : ℕ} (l : Layout R k) (inp : Inputs) (n M : ℕ)
    (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hn : d.reg l.count = n) (hc : d.reg l.col+n ≤ M) (ho : d.reg l.out = 0) :
    ∃ t, t ≤ n*(k*(160*(M+1)+1)+7)+1 ∧
      (countedLoop (body l) l.count).Stops inp (d.toCfg (loopHeader (bodyLabels k))) t
        ((loopStore l n d).toCfg (loopExit (bodyLabels k))) := by
  induction n generalizing d with
  | zero => exact ⟨1,by omega,loop_zero (body l) l.count inp d hn⟩
  | succ n ih =>
    let d₁ := decStore l.count d
    have hb₁ : ∀ j, d₁.reg j ≤ M := by
      intro j
      by_cases hj : j = l.count
      · subst j
        simpa [d₁,decStore] using (Nat.sub_le (d.reg l.count) 1).trans (hd l.count)
      · simpa [d₁,decStore,hj] using hd j
    have hcol₁ : d₁.reg l.col = d.reg l.col := dec_col l d
    have hout₁ : d₁.reg l.out = 0 := (dec_out l d).trans ho
    obtain ⟨s,e,hs,he,hes⟩ := body_stops l inp d₁ M hM hb₁ (by omega)
    let d₂ := bodyStore l d₁
    have hb₂ : ∀ j, d₂.reg j ≤ M := bodyStore_bound l d₁ M hM hb₁ (by omega)
    have hn₂ : d₂.reg l.count = n := by
      rw [show d₂ = bodyStore l d₁ from rfl,bodyStore_frame l d₁ 7 (by simp)]
      simp [d₁,decStore,hn]
    have hcol₂ : d₂.reg l.col+n ≤ M := by
      change (bodyStore l d₁).reg l.col+n ≤ M
      rw [bodyStore_col,hcol₁]
      omega
    obtain ⟨t,ht,hstop⟩ := ih d₂ hb₂ hn₂ hcol₂ (bodyStore_out l d₁)
    have hh := loop_positive_header (body l) l.count inp d (by omega)
    have hb := he.exec.relabel (leftLabel 2) (loop_code_body_active (body l) l.count)
    have hx := loop_body_return (body l) l.count inp e he.halted
    have heq : e.store.toCfg (loopHeader (bodyLabels k)) = d₂.toCfg (loopHeader (bodyLabels k)) := by rw [hes]
    rw [heq] at hx
    refine ⟨1+s+1+t,?_,⟨?_,hstop.halted⟩⟩
    · rw [Nat.succ_mul]
      omega
    · exact ((hh.trans hb).trans hx).trans hstop.exec








theorem prepareStore_col {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (prepareStore l d).reg l.col = 0 := by
  simp [prepareStore,TapeStore.setReg,Layout.col,Layout.out,Layout.count,l.injective.eq_iff]

theorem prepareStore_out {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (prepareStore l d).reg l.out = 0 := by
  simp [prepareStore,TapeStore.setReg,Layout.col,Layout.out,Layout.count,l.injective.eq_iff]

theorem prepareStore_count {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (prepareStore l d).reg l.count = d.reg l.n := by
  simp [prepareStore,TapeStore.setReg,Layout.col,Layout.out,Layout.count,l.injective.eq_iff]

theorem prepareStore_n {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (prepareStore l d).reg l.n = d.reg l.n := by
  simp [prepareStore,TapeStore.setReg,Layout.n,Layout.col,Layout.out,Layout.count,l.injective.eq_iff]





theorem prepareStore_bound {k : ℕ} (l : Layout R k) (d : TapeStore R B) (M : ℕ)
    (hd : ∀ j, d.reg j ≤ M) : ∀ j, (prepareStore l d).reg j ≤ M := by
  exact FieldPrograms.setReg_bound _ _ 0 M
    (FieldPrograms.setReg_bound _ _ (d.reg l.n) M
      (FieldPrograms.setReg_bound _ _ 0 M
        (FieldPrograms.setReg_bound _ _ 0 M hd (Nat.zero_le _)) (Nat.zero_le _))
      (hd l.n)) (Nat.zero_le _)

theorem prepare_stops {k : ℕ} (l : Layout R k) (inp : Inputs) (d : TapeStore R B)
    (M : ℕ) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 16*(M+1) ∧
      (prepare l).Stops inp (d.toCfg (prepare (B := B) l).entry) t e ∧ e.store = prepareStore l d := by
  have h₁ := TapeMacros.clear_stops l.col inp (d.reg l.col) d rfl
  let d₁ := d.setReg l.col 0
  have h₂ := TapeMacros.clear_stops l.out inp (d₁.reg l.out) d₁ rfl
  let d₂ := d₁.setReg l.out 0
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops l.n l.count (l.reg (.inl 6))
    (l.injective.ne (by simp)) (l.injective.ne (by simp)) (l.injective.ne (by simp)) inp d₂
  have hn₂ : d₂.reg l.n = d.reg l.n := by
    simp [d₂,d₁,TapeStore.setReg,Layout.n,Layout.col,Layout.out,l.injective.eq_iff]
  have hc₂ : d₂.reg l.count = d.reg l.count := by
    simp [d₂,d₁,TapeStore.setReg,Layout.count,Layout.col,Layout.out,l.injective.eq_iff]
  have ht₂ : d₂.reg (l.reg (.inl 6)) = d.reg (l.reg (.inl 6)) := by
    simp [d₂,d₁,TapeStore.setReg,Layout.col,Layout.out,l.injective.eq_iff]
  have ho₁ : d₁.reg l.out = d.reg l.out := by
    simp [d₁,TapeStore.setReg,Layout.col,Layout.out,l.injective.eq_iff]
  have hall := (h₁.seq h₂).seq he
  refine ⟨d.reg l.col+1+1+(d₁.reg l.out+1)+1+
    (d₂.reg l.count+d₂.reg (l.reg (.inl 6))+5*d₂.reg l.n+7),
    e.mapPC (rightLabel 4),?_,?_,?_⟩
  · rw [hn₂,hc₂,ht₂,ho₁]
    have := hd l.col
    have := hd l.out
    have := hd l.count
    have := hd (l.reg (.inl 6))
    have := hd l.n
    omega
  · convert hall using 1 <;> rfl
  · change e.store = _
    rw [hes,hn₂]
    rfl










theorem writeRow_stops {k : ℕ} (l : Layout R k) (inp : Inputs) (d : TapeStore R B)
    (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ writeRowBound k M ∧
      (writeRow l).Stops inp (d.toCfg (writeRow (B := B) l).entry) t e ∧
      e.store = writeRowStore l d := by
  obtain ⟨s,c,hs,hc,hcs⟩ := prepare_stops l inp d M hd
  have hb : ∀ j, c.store.reg j ≤ M := by rw [hcs]; exact prepareStore_bound l d M hd
  have hn : c.store.reg l.count = d.reg l.n := by rw [hcs,prepareStore_count]
  have hcol : c.store.reg l.col+d.reg l.n ≤ M := by
    rw [hcs,prepareStore_col,zero_add]
    exact hd l.n
  have ho : c.store.reg l.out = 0 := by rw [hcs,prepareStore_out]
  obtain ⟨t,ht,hstop⟩ := loop_stops l inp (d.reg l.n) M hM c.store hb hn hcol ho
  refine ⟨s+1+t,_,?_,hc.seq hstop,?_⟩
  · have hh := Nat.mul_le_mul_right (k*(160*(M+1)+1)+7) (hd l.n)
    unfold writeRowBound
    omega
  · change loopStore l (d.reg l.n) c.store = _
    rw [hcs]
    rfl

theorem writeRow_output {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (writeRowStore l d).output = d.output ++
      List.ofFn (fun j : Fin (d.reg l.n) => decide (∃ i, j.val = d.reg (l.neighbor i))) := by
  unfold writeRowStore
  rw [loopStore_output l _ _ (prepareStore_out l d)]
  simp [prepareStore,TapeStore.setReg,Layout.col,Layout.out,Layout.count,Layout.neighbor,
    l.injective.eq_iff]

theorem bodyStore_payload {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (bodyStore l d).roHead = d.roHead ∧ (bodyStore l d).bufferTape = d.bufferTape ∧
      (bodyStore l d).bufferHead = d.bufferHead := by
  obtain ⟨hr,_,hb,hh⟩ := marksStore_payload l (List.finRange k) d
  exact ⟨hr,hb,hh⟩

theorem loopStore_payload {k : ℕ} (l : Layout R k) (n : ℕ) (d : TapeStore R B) :
    (loopStore l n d).roHead = d.roHead ∧ (loopStore l n d).bufferTape = d.bufferTape ∧
      (loopStore l n d).bufferHead = d.bufferHead := by
  induction n generalizing d with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨ir,ib,ihd⟩ := ih (bodyStore l (decStore l.count d))
    obtain ⟨hr,hb,hh⟩ := bodyStore_payload l (decStore l.count d)
    exact ⟨ir.trans hr,ib.trans hb,ihd.trans hh⟩

theorem writeRow_payload {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (writeRowStore l d).roHead = d.roHead ∧ (writeRowStore l d).bufferTape = d.bufferTape ∧
      (writeRowStore l d).bufferHead = d.bufferHead :=
  loopStore_payload l _ (prepareStore l d)

theorem marksStore_fresh {k : ℕ} (l : Layout R k) (is : List (Fin k))
    (d : TapeStore R B) (j : Fin R) (hj : ∀ i, j ≠ l.reg i) :
    (marksStore l is d).reg j = d.reg j := by
  induction is generalizing d with
  | nil => rfl
  | cons i is ih =>
    rw [marksStore,ih]
    exact markStore_other _ _ d j (hj (.inl 2)) (hj (.inl 3))
      (hj (.inl 4)) (hj (.inl 5)) (hj (.inl 6))

theorem bodyStore_fresh {k : ℕ} (l : Layout R k) (d : TapeStore R B)
    (j : Fin R) (hj : ∀ i, j ≠ l.reg i) : (bodyStore l d).reg j = d.reg j := by
  simp only [bodyStore,TapeStore.setReg,Function.update_of_ne (hj (.inl 1)),
    emitStore,Function.update_of_ne (hj (.inl 2))]
  exact marksStore_fresh l _ d j hj

theorem loopStore_fresh {k : ℕ} (l : Layout R k) (n : ℕ) (d : TapeStore R B)
    (j : Fin R) (hj : ∀ i, j ≠ l.reg i) : (loopStore l n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [loopStore,ih,bodyStore_fresh l _ j hj]
    simp [decStore,hj (.inl 7)]

theorem writeRow_fresh {k : ℕ} (l : Layout R k) (d : TapeStore R B)
    (j : Fin R) (hj : ∀ i, j ≠ l.reg i) : (writeRowStore l d).reg j = d.reg j := by
  rw [writeRowStore,loopStore_fresh l _ _ j hj]
  simp [prepareStore,TapeStore.setReg,hj (.inl 1),hj (.inl 2),hj (.inl 6),hj (.inl 7)]

theorem loopStore_n {k : ℕ} (l : Layout R k) (n : ℕ) (d : TapeStore R B) :
    (loopStore l n d).reg l.n = d.reg l.n := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [loopStore,ih,bodyStore_frame l _ 0 (by simp)]
    simp [decStore,Layout.n,Layout.count,l.injective.eq_iff]

theorem writeRow_n {k : ℕ} (l : Layout R k) (d : TapeStore R B) :
    (writeRowStore l d).reg l.n = d.reg l.n := by
  rw [writeRowStore,loopStore_n,prepareStore_n]





theorem loopStore_bound {k : ℕ} (l : Layout R k) (n : ℕ) (d : TapeStore R B)
    (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) (hc : d.reg l.col+n ≤ M) :
    ∀ j, (loopStore l n d).reg j ≤ M := by
  induction n generalizing d with
  | zero => exact hd
  | succ n ih =>
    have hb : ∀ j, (decStore l.count d).reg j ≤ M := by
      intro j
      by_cases hj : j = l.count
      · subst j
        simpa [decStore] using (Nat.sub_le (d.reg l.count) 1).trans (hd l.count)
      · simpa [decStore,hj] using hd j
    have hcol : (decStore l.count d).reg l.col < M := by rw [dec_col]; omega
    have he := bodyStore_bound l (decStore l.count d) M hM hb hcol
    have hec : (bodyStore l (decStore l.count d)).reg l.col+n ≤ M := by
      rw [bodyStore_col,dec_col]
      omega
    exact ih _ he hec

theorem writeRowStore_bound {k : ℕ} (l : Layout R k) (d : TapeStore R B)
    (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (writeRowStore l d).reg j ≤ M := by
  apply loopStore_bound l _ _ M hM (prepareStore_bound l d M hd)
  rw [prepareStore_col,zero_add]
  exact hd l.n
















theorem writeRowBound_polynomial (k M : ℕ) :
    writeRowBound k M ≤ (161*k+25)*(M+1)^2 := by
  have hb : k*(160*(M+1)+1)+7 ≤ (161*k+7)*(M+1) := by nlinarith
  have hl : M*(k*(160*(M+1)+1)+7) ≤ (161*k+7)*(M+1)^2 := by
    calc
      _ ≤ M*((161*k+7)*(M+1)) := Nat.mul_le_mul_left M hb
      _ ≤ (M+1)*((161*k+7)*(M+1)) := Nat.mul_le_mul_right _ (Nat.le_succ M)
      _ = _ := by ring
  have hx : M+1 ≤ (M+1)^2 := by nlinarith
  have hp : 1 ≤ (M+1)^2 := by omega
  unfold writeRowBound
  nlinarith














end NeighborWriter
end ExpandingCodes.Computation

end FlattenModule100

/-! Inlined whole module: ExpandingCodes.Computation.SamplerEnvelope -/
section FlattenModule101


set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation



theorem samplerBucketCount_le (k n : ℕ) : samplerBucketCount k n ≤ n+1 := by
  by_cases hz : n/k = 0
  · simp [samplerBucketCount,hz]
  · exact ((Nat.pow_log_le_self 2 hz).trans (Nat.div_le_self n k)).trans (Nat.le_succ n)

theorem samplerBucketCount_polynomial (k : ℕ) : PolynomialBound (samplerBucketCount k) :=
  (PolynomialBound.identity.add (PolynomialBound.const 1)).of_le (fun n _ => samplerBucketCount_le k n)


























theorem samplerEnvelope_covers (d k n : ℕ) : SamplerEnvelopeCovers d k n (samplerEnvelope d k n) := by
  constructor <;> unfold samplerEnvelope <;> omega

theorem samplerEnvelope_polynomial (d k : ℕ) (hd : 0 < d) : PolynomialBound (samplerEnvelope d k) := by
  have hq := fieldSize_polynomial d hd
  have he := fieldExponent_polynomial d hd
  have hm := rowCount_polynomial d hd
  have hb := samplerBucketCount_polynomial k
  have hsetup := ((ParameterPrograms.setup_bounds_polynomial d).2.comp
    (ParameterPrograms.PolynomialMajorant.id.add (ParameterPrograms.PolynomialMajorant.const 1))).toPolynomialBound
  have hforms := (((((PolynomialBound.const 2).mul (PolynomialBound.const k)).mul hq).mul
    (PolynomialBound.const d)).mul hq).add (PolynomialBound.const 1)
  have hhashes := (((PolynomialBound.const k).mul (hq.pow 3)).mul hb).add (PolynomialBound.const 1)
  exact ((((((((((((PolynomialBound.const 2).add hsetup).add
    (PolynomialBound.const (2*k*d+d+k+1))).add (hq.pow 2)).add
      (((PolynomialBound.const 3).mul he).add (PolynomialBound.const 1))).add
        ((PolynomialBound.const 2).mul hq)).add hforms).add hhashes).add hm).add
          PolynomialBound.identity).add (hm.mul PolynomialBound.identity)).add
            ((PolynomialBound.const k).mul hb)).add (samplerEntropy_polynomial d k hd)



end ExpandingCodes.PolynomialStretch

end FlattenModule101

/-! Inlined whole module: ExpandingCodes.Computation.SamplerRows -/
section FlattenModule102



set_option autoImplicit false

namespace ExpandingCodes.Computation.SamplerRows
open ExpandingCodes.PolynomialStretch EncodedTester

variable {q d k b n : ℕ}












theorem matrixBits_eq (O : EncodedGaussian.Operations (Fin q))
    (s : Fin (2*k*q*d) → Fin q) (h : Fin (k*q*q*q) → Fin b) :
    matrixBits (EncodedSampler.matrix n O s h) =
      (List.ofFn (row (n := n) O s h)).flatten := by
  classical
  unfold matrixBits row EncodedSampler.matrix
  congr 1
  apply congrArg List.ofFn
  funext z
  apply congrArg List.ofFn
  funext j
  split_ifs <;> simp_all

@[simp] theorem prefix_zero (O : EncodedGaussian.Operations (Fin q))
    (s : Fin (2*k*q*d) → Fin q) (h : Fin (k*q*q*q) → Fin b)
    (hr : 0 ≤ q^d) : rowsBefore (n := n) O s h 0 hr = [] := by
  simp [rowsBefore]

theorem prefix_succ (O : EncodedGaussian.Operations (Fin q))
    (s : Fin (2*k*q*d) → Fin q) (h : Fin (k*q*q*q) → Fin b)
    (r : ℕ) (hr : r+1 ≤ q^d) :
    rowsBefore (n := n) O s h (r+1) hr =
      rowsBefore (n := n) O s h r (by omega) ++ row (n := n) O s h ⟨r,by omega⟩ := by
  unfold rowsBefore
  rw [List.ofFn_succ']
  simp only [List.concat_eq_append,List.flatten_append,List.flatten_singleton]
  rfl

theorem prefix_full (O : EncodedGaussian.Operations (Fin q))
    (s : Fin (2*k*q*d) → Fin q) (h : Fin (k*q*q*q) → Fin b) :
    rowsBefore (n := n) O s h (q^d) le_rfl = matrixBits (EncodedSampler.matrix n O s h) := by
  rw [matrixBits_eq]
  rfl

/-- A canonical enumeration index determines every physical point digit. The
premise is the odometer's actual little-endian reading list, so callers only
need their concrete layout's one reading identity. -/
theorem readings_eq_digits {R B : ℕ} (qreg : Fin R)
    (ps : List (SamplerOdometer.Digit R)) (s : TapeStore R B)
    (hv : SamplerOdometer.Valid qreg ps s) (hq : s.reg qreg = q)
    (rs : Fin d → Fin R)
    (hread : SamplerOdometer.readings ps s = List.ofFn (fun j => s.reg (rs j)))
    (r : ℕ) (hr : r < q^d)
    (hnum : Nat.ofDigits q (SamplerOdometer.readings ps s) = r) :
    ∀ j, s.reg (rs j) = (digits q d ⟨r,hr⟩ j).val := by
  have hlt (j : Fin d) : s.reg (rs j) < q := by
    have hj : s.reg (rs j) ∈ SamplerOdometer.readings ps s := by
      rw [hread]
      exact List.mem_ofFn.mpr ⟨j,rfl⟩
    simpa only [hq] using SamplerOdometer.readings_bounded qreg ps s hv _ hj
  let f : Fin d → Fin q := fun j => ⟨s.reg (rs j),hlt j⟩
  have he := SamplerOdometer.canonical_digits q d f ⟨r,hr⟩ (by
    change Nat.ofDigits q (List.ofFn (fun j => s.reg (rs j))) = r
    rw [← hread]
    exact hnum)
  intro j
  exact congrArg (fun g : Fin d → Fin q => (g j).val) he


end ExpandingCodes.Computation.SamplerRows

end FlattenModule102

/-! Inlined whole module: ExpandingCodes.Computation.SamplerAssembly -/
section FlattenModule103










set_option autoImplicit false
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false
namespace ExpandingCodes.Computation.SamplerAssembly
open NKtLB UnaryArithmetic FieldPrograms ParameterPrograms SamplerEvaluation
open ExpandingCodes.PolynomialStretch
variable {R B : ℕ}









































































































































































































































































































































































































































































































































































































































































































































































































































/-- This loop rule uses the proved physical post-counter frame of its body.
It does not assume a runtime evaluator or a unit-cost body transition. -/
theorem countedLoop_stops_frame {L : ℕ} (P : TapeProgram R B L) (r : Fin R)
    (inp : Inputs) (C : ℕ) (Inv : ℕ → TapeStore R B → Prop)
    (hbody : ∀ n s,s.reg r=n+1 → Inv (n+1) s →
      ∃ t c,t ≤ C ∧ P.Stops inp ((TapeProgram.decStore r s).toCfg P.entry) t c ∧
        Inv n c.store ∧ c.reg r=n)
    (n : ℕ) (s : TapeStore R B) (hn : s.reg r=n) (hi : Inv n s) :
    ∃ t e,t ≤ n*(C+2)+1 ∧
      (TapeProgram.countedLoop P r).Stops inp (s.toCfg (TapeProgram.loopHeader L)) t
        (e.toCfg (TapeProgram.loopExit L)) ∧ Inv 0 e ∧ e.reg r=0 := by
  induction n generalizing s with
  | zero => exact ⟨1,s,by omega,TapeProgram.loop_zero P r inp s hn,hi,hn⟩
  | succ n ih =>
    obtain ⟨t,c,ht,hc,hIc,hcr⟩ := hbody n s hn hi
    obtain ⟨u,e,hu,he,hIe,her⟩ := ih c.store hcr hIc
    have hheader := TapeProgram.loop_positive_header P r inp s (by omega)
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2) (TapeProgram.loop_code_body_active P r)
    have hreturn := TapeProgram.loop_body_return P r inp c hc.halted
    refine ⟨1+t+1+u,e,?_,⟨((hheader.trans hrun).trans hreturn).trans he.exec,he.halted⟩,hIe,her⟩
    simp only [Nat.succ_mul]
    omega


















theorem Sizes.frame {r : Fin 80 → Fin R} {d n k : ℕ} {s e : TapeStore R B}
    (h : Sizes r d n k s) (hf : ∀ j : Fin 80,32 ≤ j.val → j.val<40 → e.reg (r j)=s.reg (r j)) :
    Sizes r d n k e := by
  rcases h with ⟨a,b,c,d,e,f,g,h⟩
  constructor
  all_goals first | rw [hf _ (by decide) (by decide)];assumption

 






































theorem sizeStageTime_polynomial (d : ℕ) : PolynomialBound (sizeStageTime d) := by
  have hp : ParameterPrograms.PolynomialMajorant (fun n => 2*n+4+setupTimeBound d (n+1)) :=
    (((ParameterPrograms.PolynomialMajorant.const 2).mul ParameterPrograms.PolynomialMajorant.id).add
      (ParameterPrograms.PolynomialMajorant.const 4)).add
      ((setup_bounds_polynomial d).1.comp
        (ParameterPrograms.PolynomialMajorant.id.add (ParameterPrograms.PolynomialMajorant.const 1)))
  exact hp.toPolynomialBound


































































































































theorem TablesReady.frame {d n k M : ℕ} {inp : Inputs} {s e : TapeStore R 2}
    (h : TablesReady d n k inp M s)
    (hsym : ∀ b j,(e.bufferTape b).getD j .blank=(s.bufferTape b).getD j .blank)
    (hh : ∀ b,e.bufferHead b ≤ M) : TablesReady d n k inp M e := by
  constructor
  · intro i
    exact ⟨(h.forms i).1,fun j hj => by rw [hsym];exact (h.forms i).2 j hj⟩
  · intro i
    exact ⟨(h.hashes i).1,fun j hj => by rw [hsym];exact (h.hashes i).2 j hj⟩
  · intro b
    exact ⟨by rw [hsym];exact (h.marked b).1,fun j hj => by rw [hsym];exact (h.marked b).2 j hj⟩
  · exact hh














































































open ExpandingCodes.PolynomialStretch
























































































































theorem preludeTime_polynomial (d k : ℕ) (hd : 0<d) :
    PolynomialBound (fun n => preludeTime d n (samplerEnvelope d k n)) := by
  have hM := (samplerEnvelope_polynomial d k hd).add (PolynomialBound.const 1)
  exact (((sizeStageTime_polynomial d).add ((PolynomialBound.const 391).mul (hM.pow 3))).add
    ((PolynomialBound.const 40020).mul (hM.pow 7))).add (PolynomialBound.const 2)





theorem RuntimeReady.frame {r : Fin 80 → Fin R} {d n k M : ℕ} {inp : Inputs}
    {s e : TapeStore R 2} (h : RuntimeReady r d n k inp M s)
    (hr : ∀ j,Protected j → e.reg (r j)=s.reg (r j))
    (ht : ∀ b j,(e.bufferTape b).getD j .blank=(s.bufferTape b).getD j .blank)
    (hh : ∀ b,e.bufferHead b ≤ M) (hb : ∀ j,e.reg j ≤ M) : RuntimeReady r d n k inp M e := by
  constructor
  · apply h.sizes.frame
    intro j hj hj'
    exact hr j (Or.inr (Or.inr (Or.inr (Or.inr ⟨hj,hj'⟩))))
  · apply h.environment.frame
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact hr 3 (Or.inl rfl)
    · exact hr 19 (Or.inr (Or.inl rfl))
    · exact hr 23 (Or.inr (Or.inr (Or.inl rfl)))
    · exact hr 24 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact h.tables.frame ht hh
  · exact hb

theorem RuntimeReady.setReg {r : Fin 80 → Fin R} {d n k M : ℕ} {inp : Inputs}
    {s : TapeStore R 2} (h : RuntimeReady r d n k inp M s) (j : Fin R) (a : ℕ)
    (ha : a ≤ M) (hj : ∀ i,Protected i → r i≠j) : RuntimeReady r d n k inp M (s.setReg j a) := by
  apply h.frame
  · intro i hi;simp [TapeStore.setReg,hj i hi]
  · intro b n;rfl
  · exact h.tables.heads
  · exact setReg_bound s j a M h.counters ha

namespace Concrete
open SamplerProgram






































































/-- A finite sequential composition rule for the actual layer code. The
single-layer premise is strictly smaller than the k-layer program; the result
tracks all produced neighbor counters and the untouched remaining counters. -/
theorem layers_stops_of (d k : ℕ) (inp : Inputs) (C : ℕ)
    (Good : TapeStore (Storage.registers d k) 2 → Prop) (value : Fin k → ℕ)
    (hstep : ∀ i s,Good s → ∃ t e,t ≤ C ∧
      (layer d k i).Stops inp (s.toCfg (layer d k i).entry) t e ∧ Good e.store ∧
      e.reg (Storage.neighbor d k i)=value i ∧
      (∀ j,j≠i → e.reg (Storage.neighbor d k j)=s.reg (Storage.neighbor d k j)))
    (is : List (Fin k)) (s : TapeStore (Storage.registers d k) 2) (hs : Good s) :
    ∃ t e,t ≤ is.length*(C+1) ∧
      (layers d k is).Stops inp (s.toCfg (layers d k is).entry) t e ∧ Good e.store ∧
      (∀ i,i∈is → e.reg (Storage.neighbor d k i)=value i) ∧
      (∀ i,i∉is → e.reg (Storage.neighbor d k i)=s.reg (Storage.neighbor d k i)) := by
  induction is generalizing s with
  | nil =>
    exact ⟨0,s.toCfg ⟨0,by simp [layersLabels]⟩,by simp,TapeProgram.skip_stops inp s,hs,by simp,by simp⟩
  | cons i is ih =>
    obtain ⟨t,c,ht,hc,hGc,hnew,hframe⟩ := hstep i s hs
    obtain ⟨u,e,hu,he,hGe,hvalues,htail⟩ := ih c.store hGc
    refine ⟨_,_,?_,hc.seq he,hGe,?_,?_⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · intro j hj
      rcases List.mem_cons.mp hj with hji|hj
      · subst j
        by_cases hi : i∈is
        · exact hvalues i hi
        · rw [htail i hi]
          exact hnew
      · exact hvalues j hj
    · intro j hj
      have hji : j≠i := by intro heq;subst j;exact hj (by simp)
      have hjtail : j∉is := by intro hin;exact hj (by simp [hin])
      rw [htail j hjtail]
      exact hframe j hji

theorem writeRow_matches {d k n q b : ℕ}
    (O : EncodedGaussian.Operations (Fin q)) (forms : Fin (2*k*q*d) → Fin q)
    (hashes : Fin (k*q*q*q) → Fin b) (z : Fin (q^d))
    (s : TapeStore (Storage.registers d k) 2) (hn : s.reg (Storage.low d k 32)=n)
    (hv : ∀ i,s.reg (Storage.neighbor d k i)=i.val*b+
      (EncodedSampler.neighbor O forms hashes i (EncodedTester.digits q d z)).val) :
    (NeighborWriter.writeRowStore (writerLayout d k) s).output=
      s.output++SamplerRows.row (n:=n) O forms hashes z := by
  have h := NeighborWriter.writeRow_output (writerLayout d k) s
  change (NeighborWriter.writeRowStore (writerLayout d k) s).output=s.output++
    List.ofFn (fun j : Fin (s.reg (Storage.low d k 32)) =>
      decide (∃ i,j.val=s.reg (Storage.neighbor d k i))) at h
  rw [hn] at h
  simpa only [hv,SamplerRows.row] using h

theorem low_not_used (d k : ℕ) (j : Fin 80) :
    Storage.low d k j∉SamplerOdometer.used (Storage.pointPairs d k) := by
  intro hj
  obtain ⟨p,hp,hj⟩ := (SamplerOdometer.used_mem_iff _ _).mp hj
  obtain ⟨i,hi,hpi⟩ := List.mem_map.mp hp
  subst p
  rcases hj with hj|hj
  · have h := congrArg Fin.val hj
    have := j.isLt
    simp only [Storage.low_val,Storage.point_val] at h
    omega
  · have h := congrArg Fin.val hj
    have := j.isLt
    simp only [Storage.low_val,Storage.countdown_val] at h
    omega

theorem initializeStore_payload (q tmp : Fin R) (ps : List (SamplerOdometer.Digit R))
    (s : TapeStore R B) : FieldConvolution.tapeData (SamplerOdometer.initializeStore q tmp ps s)=
      FieldConvolution.tapeData s := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    rw [SamplerOdometer.initializeStore,ih]
    rfl

theorem nextStore_tapeData (q tmp : Fin R) (ps : List (SamplerOdometer.Digit R))
    (s : TapeStore R B) : FieldConvolution.tapeData (SamplerOdometer.nextStore q tmp ps s)=
      FieldConvolution.tapeData s := by
  have h := SamplerOdometer.nextStore_payload q tmp ps s
  exact congrArg₂ Prod.mk h.1 (congrArg₂ Prod.mk h.2.1 (congrArg₂ Prod.mk h.2.2.1 h.2.2.2))

theorem odometer_frame (d n k M : ℕ) (inp : Inputs)
    (s e : TapeStore (Storage.registers d k) 2)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s)
    (hf : ∀ j : Fin 80,j≠61 → e.reg (Storage.low d k j)=s.reg (Storage.low d k j))
    (ht : FieldConvolution.tapeData e=FieldConvolution.tapeData s) (hb : ∀ j,e.reg j ≤ M) :
    RuntimeReady (Storage.low d k) d n k inp M e := by
  apply hs.frame
  · intro j hj
    apply hf
    rcases hj with rfl|rfl|rfl|rfl|hj <;> omega
  · intro b j;exact congrArg (fun z => (z.2.2.1 b).getD j .blank) ht
  · intro b
    exact (congrArg (fun z => z.2.2.2 b) ht).le.trans (hs.tables.heads b)
  · exact hb

theorem initializeStore_ready (d n k M : ℕ) (inp : Inputs)
    (s : TapeStore (Storage.registers d k) 2)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s)
    (hb : ∀ j,(SamplerOdometer.initializeStore (Storage.low d k 35) (Storage.low d k 61)
      (Storage.pointPairs d k) s).reg j ≤ M) :
    RuntimeReady (Storage.low d k) d n k inp M
      (SamplerOdometer.initializeStore (Storage.low d k 35) (Storage.low d k 61) (Storage.pointPairs d k) s) := by
  apply odometer_frame d n k M inp s _ hs
  · intro j hj
    exact SamplerOdometer.initializeStore_fresh _ _ _ s _
      ((Storage.low_injective d k).ne hj) (low_not_used d k j)
  · exact initializeStore_payload _ _ _ s
  · exact hb

theorem nextStore_ready (d n k M : ℕ) (inp : Inputs)
    (s : TapeStore (Storage.registers d k) 2)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s)
    (hb : ∀ j,(SamplerOdometer.nextStore (Storage.low d k 35) (Storage.low d k 61)
      (Storage.pointPairs d k) s).reg j ≤ M) :
    RuntimeReady (Storage.low d k) d n k inp M
      (SamplerOdometer.nextStore (Storage.low d k 35) (Storage.low d k 61) (Storage.pointPairs d k) s) := by
  apply odometer_frame d n k M inp s _ hs
  · intro j hj
    exact SamplerOdometer.nextStore_fresh _ _ _ s _
      ((Storage.low_injective d k).ne hj) (low_not_used d k j)
  · exact nextStore_tapeData _ _ _ s
  · exact hb

theorem writeRow_low (d k : ℕ) (s : TapeStore (Storage.registers d k) 2)
    (j : Fin 80) (hj : j.val<40) :
    (NeighborWriter.writeRowStore (writerLayout d k) s).reg (Storage.low d k j)=s.reg (Storage.low d k j) := by
  by_cases h32 : j=32
  · subst j;exact NeighborWriter.writeRow_n _ s
  apply NeighborWriter.writeRow_fresh
  intro i
  cases i with
  | inl a =>
    intro heq
    have h := congrArg Fin.val heq
    change j.val=(writerIndex a).val at h
    fin_cases a <;> simp [writerIndex] at h <;> first | exact h32 (Fin.ext h) | omega
  | inr a =>
    intro heq
    have h := congrArg Fin.val heq
    change j.val=80+4*d+a.val at h
    omega

theorem writeRow_point (d k : ℕ) (s : TapeStore (Storage.registers d k) 2) (j : Fin d) :
    (NeighborWriter.writeRowStore (writerLayout d k) s).reg (Storage.point d k j)=s.reg (Storage.point d k j) := by
  apply NeighborWriter.writeRow_fresh
  intro i
  cases i with
  | inl a =>
    intro heq
    have h := congrArg Fin.val heq
    change 80+j.val=(writerIndex a).val at h
    fin_cases a <;> simp [writerIndex] at h <;> omega
  | inr a =>
    intro heq
    have h := congrArg Fin.val heq
    change 80+j.val=80+4*d+a.val at h
    have := j.isLt
    omega

theorem writeRow_countdown (d k : ℕ) (s : TapeStore (Storage.registers d k) 2) (j : Fin d) :
    (NeighborWriter.writeRowStore (writerLayout d k) s).reg (Storage.countdown d k j)=s.reg (Storage.countdown d k j) := by
  apply NeighborWriter.writeRow_fresh
  intro i
  cases i with
  | inl a =>
    intro heq
    have h := congrArg Fin.val heq
    change 80+d+j.val=(writerIndex a).val at h
    fin_cases a <;> simp [writerIndex] at h <;> omega
  | inr a =>
    intro heq
    have h := congrArg Fin.val heq
    change 80+d+j.val=80+4*d+a.val at h
    have := j.isLt
    omega

theorem writeRow_remaining (d k : ℕ) (s : TapeStore (Storage.registers d k) 2) :
    (NeighborWriter.writeRowStore (writerLayout d k) s).reg (Storage.low d k 60)=s.reg (Storage.low d k 60) := by
  apply NeighborWriter.writeRow_fresh
  intro i
  cases i with
  | inl a =>
    intro heq
    have h := congrArg Fin.val heq
    change 60=(writerIndex a).val at h
    fin_cases a <;> simp [writerIndex] at h
  | inr a =>
    intro heq
    have h := congrArg Fin.val heq
    change 60=80+4*d+a.val at h
    omega

theorem writeRow_ready (d n k M : ℕ) (inp : Inputs)
    (s : TapeStore (Storage.registers d k) 2) (hM : 1 ≤ M)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s) :
    RuntimeReady (Storage.low d k) d n k inp M (NeighborWriter.writeRowStore (writerLayout d k) s) := by
  have ht := NeighborWriter.writeRow_payload (writerLayout d k) s
  apply hs.frame
  · intro j hj
    apply writeRow_low
    rcases hj with rfl|rfl|rfl|rfl|hj <;> omega
  · intro b j;rw [ht.2.1]
  · intro b;rw [ht.2.2];exact hs.tables.heads b
  · exact NeighborWriter.writeRowStore_bound (writerLayout d k) s M hM hs.counters

theorem writeRow_valid (d k : ℕ) (s : TapeStore (Storage.registers d k) 2)
    (hv : SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) s) :
    SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k)
      (NeighborWriter.writeRowStore (writerLayout d k) s) := by
  intro p hp
  obtain ⟨i,hi,hpi⟩ := List.mem_map.mp hp
  subst p
  change _+_+1=_
  rw [writeRow_point,writeRow_countdown,writeRow_low d k s 35 (by decide)]
  exact hv _ (List.mem_map.mpr ⟨i,hi,rfl⟩)

theorem writeRow_readings (d k : ℕ) (s : TapeStore (Storage.registers d k) 2) :
    SamplerOdometer.readings (Storage.pointPairs d k) (NeighborWriter.writeRowStore (writerLayout d k) s)=
      SamplerOdometer.readings (Storage.pointPairs d k) s := by
  apply SamplerOdometer.readings_congr
  intro p hp
  obtain ⟨i,hi,hpi⟩ := List.mem_map.mp hp
  subst p
  exact writeRow_point d k s i

















theorem pointPairs_readings (d k : ℕ) (s : TapeStore (Storage.registers d k) 2) :
    SamplerOdometer.readings (Storage.pointPairs d k) s=List.ofFn (fun j => s.reg (Storage.point d k j)) := by
  simp [SamplerOdometer.readings,Storage.pointPairs,List.map_map,List.ofFn_eq_map]

theorem RowState.point (d n k M : ℕ) (inp : Inputs) (r : ℕ) (hr : r<rowCount d n)
    (s : TapeStore (Storage.registers d k) 2) (hs : RowState d n k M inp r (Nat.le_of_lt hr) s) :
    ∀ j,s.reg (Storage.point d k j)=(EncodedTester.digits (fieldSize d n) d ⟨r,hr⟩ j).val := by
  exact SamplerRows.readings_eq_digits (Storage.low d k 35) (Storage.pointPairs d k) s hs.valid
    hs.ready.sizes.field (Storage.point d k) (pointPairs_readings d k s) r hr
    (by rw [hs.number,Nat.mod_eq_of_lt hr])

















theorem rowBody_stops_of_layers (d n k M : ℕ) (inp : Inputs) (hM : 1 ≤ M)
    (huniq : (Storage.low d k 35::Storage.low d k 61::SamplerOdometer.used (Storage.pointPairs d k)).Nodup)
    (C : ℕ)
    (hLayers : ∀ (s : TapeStore (Storage.registers d k) 2) (z : Fin ((fieldSize d n)^d)),
      RuntimeReady (Storage.low d k) d n k inp M s →
      SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) s →
      (∀ j,s.reg (Storage.point d k j)=(EncodedTester.digits (fieldSize d n) d z j).val) →
      ∃ t e,t ≤ C ∧ (layers d k (List.finRange k)).Stops inp
        (s.toCfg (layers d k (List.finRange k)).entry) t e ∧ LayerBlockPost d n k M inp s z e.store)
    (r : ℕ) (hr : r<rowCount d n) (s : TapeStore (Storage.registers d k) 2)
    (hs : RowState d n k M inp r (Nat.le_of_lt hr) s) :
    ∃ t e,t ≤ rowBodyTime d k C M ∧
      (rowBody d k).Stops inp (s.toCfg (rowBody d k).entry) t e ∧
      RowState d n k M inp (r+1) (by omega) e.store ∧
      e.reg (Storage.low d k 60)=s.reg (Storage.low d k 60) := by
  let z : Fin ((fieldSize d n)^d) := ⟨r,hr⟩
  obtain ⟨t₁,a,ht₁,ha,hap⟩ := hLayers s z hs.ready hs.valid (RowState.point d n k M inp r hr s hs)
  obtain ⟨t₂,b,ht₂,hb,hbs⟩ := NeighborWriter.writeRow_stops (writerLayout d k) inp a.store M hM hap.ready.counters
  have hbReady : RuntimeReady (Storage.low d k) d n k inp M b.store := by
    rw [hbs];exact writeRow_ready d n k M inp a.store hM hap.ready
  have hbValid : SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) b.store := by
    rw [hbs];exact writeRow_valid d k a.store hap.valid
  obtain ⟨t₃,e,ht₃,he,hes,heb⟩ := SamplerOdometer.program_stops_valid (Storage.low d k 35)
    (Storage.low d k 61) (Storage.pointPairs d k) huniq inp M b.store hbReady.counters hbValid
  have heReady : RuntimeReady (Storage.low d k) d n k inp M e.store := by
    rw [hes]
    apply nextStore_ready d n k M inp b.store hbReady
    simpa only [← hes] using heb
  have heValid : SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) e.store := by
    rw [hes];exact SamplerOdometer.program_valid _ _ _ huniq b.store hbValid
  have hbn : Nat.ofDigits (fieldSize d n) (SamplerOdometer.readings (Storage.pointPairs d k) b.store)=r := by
    rw [hbs,writeRow_readings,hap.readings,hs.number,Nat.mod_eq_of_lt hr]
  have hen := SamplerOdometer.program_number (Storage.low d k 35) (Storage.low d k 61)
    (Storage.pointPairs d k) huniq b.store hbValid
    (by rw [hbReady.sizes.field];have := fieldSize_ge_two d n;omega)
  have hnum : Nat.ofDigits (fieldSize d n) (SamplerOdometer.readings (Storage.pointPairs d k) e.store)=
      (r+1)%rowCount d n := by
    rw [hes]
    rw [hbReady.sizes.field] at hen
    rw [hbn] at hen
    simpa only [rowCount,Storage.pointPairs,List.length_map,List.length_finRange] using hen
  have hrnext : r+1 ≤ (fieldSize d n)^d := by change r+1 ≤ rowCount d n;omega
  have heo := (SamplerOdometer.nextStore_payload (Storage.low d k 35) (Storage.low d k 61)
    (Storage.pointPairs d k) b.store).2.1
  have hout : e.output=SamplerRows.rowsBefore (n:=n) (operations d n) (formValues d n k inp)
      (hashValues d n k inp) (r+1) hrnext := by
    change e.store.output=_
    rw [hes,heo,hbs,writeRow_matches (operations d n) (formValues d n k inp) (hashValues d n k inp)
      z a.store hap.ready.sizes.input hap.neighbors,hap.output,hs.output]
    exact (SamplerRows.prefix_succ (operations d n) (formValues d n k inp) (hashValues d n k inp) r hrnext).symm
  have hremaining : e.reg (Storage.low d k 60)=s.reg (Storage.low d k 60) := by
    change e.store.reg _=_
    rw [hes,SamplerOdometer.nextStore_fresh _ _ _ _ _
      ((Storage.low_injective d k).ne (by decide)) (low_not_used d k 60),hbs,writeRow_remaining,hap.remaining]
  refine ⟨_,_,?_,(ha.seq hb).seq he,⟨heReady,heValid,hnum,hout⟩,hremaining⟩
  unfold rowBodyTime
  simp only [Storage.pointPairs,List.length_map,List.length_finRange] at ht₃
  omega

theorem point_ne_low (d k : ℕ) (i : Fin d) (j : Fin 80) : Storage.point d k i≠Storage.low d k j := by
  intro heq
  have h := congrArg Fin.val heq
  have := j.isLt
  simp only [Storage.point_val,Storage.low_val] at h
  omega

theorem countdown_ne_low (d k : ℕ) (i : Fin d) (j : Fin 80) : Storage.countdown d k i≠Storage.low d k j := by
  intro heq
  have h := congrArg Fin.val heq
  have := j.isLt
  simp only [Storage.countdown_val,Storage.low_val] at h
  omega

theorem RowState.setLow (d n k M : ℕ) (inp : Inputs) (r : ℕ) (hr : r ≤ rowCount d n)
    (s : TapeStore (Storage.registers d k) 2) (hs : RowState d n k M inp r hr s)
    (j : Fin 80) (hj : ¬Protected j) (a : ℕ) (ha : a ≤ M) :
    RowState d n k M inp r hr (s.setReg (Storage.low d k j) a) := by
  have hf : ∀ i,Protected i → Storage.low d k i≠Storage.low d k j := by
    intro i hi heq
    have h := Storage.low_injective d k heq
    subst i
    exact hj hi
  have hq := hf 35 (by right;right;right;right;decide)
  have hread : SamplerOdometer.readings (Storage.pointPairs d k) (s.setReg (Storage.low d k j) a)=
      SamplerOdometer.readings (Storage.pointPairs d k) s := by
    rw [pointPairs_readings,pointPairs_readings]
    congr 1
    funext i
    simp [TapeStore.setReg,point_ne_low d k i j]
  constructor
  · exact hs.ready.setReg _ _ ha hf
  · intro p hp
    obtain ⟨i,hi,hpi⟩ := List.mem_map.mp hp
    subst p
    simpa [TapeStore.setReg,point_ne_low d k i j,countdown_ne_low d k i j,hq] using hs.valid _
      (List.mem_map.mpr ⟨i,hi,rfl⟩)
  · rw [hread];exact hs.number
  · exact hs.output












/-- Full actual runtime row loop, reduced only to the strictly smaller actual
layer block. The invariant accounts for every written row and physical carry. -/
theorem finish_stops_of_layers (d n k M : ℕ) (inp : Inputs) (hM : 1 ≤ M)
    (huniq : (Storage.low d k 35::Storage.low d k 61::SamplerOdometer.used (Storage.pointPairs d k)).Nodup)
    (C : ℕ) (hLayers : LayerBlockContract d n k M inp C)
    (s : TapeStore (Storage.registers d k) 2)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s) (hout : s.output=[]) :
    ∃ t e,t ≤ finishTime d n k C M ∧
      (finish d k).Stops inp (s.toCfg (finish d k).entry) t e ∧
      e.output=matrixBits (binarySamplerFromInput d n k (Nat.log 2 (n/k)) inp) := by
  let q := Storage.low d k 35
  let tmp := Storage.low d k 61
  let ps := Storage.pointPairs d k
  obtain ⟨t₁,a,ht₁,ha,has,hab⟩ := SamplerOdometer.initialize_stops q tmp ps huniq inp M s hs.counters
  have haReady : RuntimeReady (Storage.low d k) d n k inp M a.store := by
    rw [has]
    apply initializeStore_ready d n k M inp s hs
    intro j
    have h : a.store.reg j ≤ M := hab j
    rw [has] at h
    exact h
  have haValid : SamplerOdometer.Valid q ps a.store := by
    rw [has]
    apply SamplerOdometer.initializeStore_valid q tmp ps huniq s
    rw [hs.sizes.field]
    exact fieldSize_pos d n
  have haNumber : Nat.ofDigits (fieldSize d n) (SamplerOdometer.readings ps a.store)=0 := by
    rw [has]
    change Nat.ofDigits (fieldSize d n) (SamplerOdometer.readings (Storage.pointPairs d k) _)=0
    rw [pointPairs_readings,SamplerOdometer.number_ofFn]
    apply Finset.sum_eq_zero
    intro i hi
    have hv := SamplerOdometer.initializeStore_values q tmp ps huniq s
      (Storage.point d k i,Storage.countdown d k i)
      (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
    simp only [hv.1,zero_mul]
  have haOut : a.output=[] := by
    have ht := initializeStore_payload q tmp ps s
    change a.store.output=[]
    rw [has]
    exact (congrArg (fun z => z.2.1) ht).trans hout
  have haState : RowState d n k M inp 0 (Nat.zero_le _) a.store := by
    exact ⟨haReady,haValid,by simpa using haNumber,by simpa [SamplerRows.rowsBefore] using haOut⟩
  obtain ⟨t₂,b,ht₂,hb,hbs,hbb⟩ := copy_stops_bound (Storage.low d k 36) (Storage.low d k 60)
    (Storage.low d k 61) ((Storage.low_injective d k).ne (by decide))
    ((Storage.low_injective d k).ne (by decide)) ((Storage.low_injective d k).ne (by decide)) inp M a.store hab
  have hmM : rowCount d n ≤ M := by rw [← haReady.sizes.rows];exact hab _
  have hbState : RowState d n k M inp 0 (Nat.zero_le _) b.store := by
    rw [hbs,haReady.sizes.rows]
    exact (haState.setLow d n k M inp 0 (Nat.zero_le _) a.store 60 (by simp [Protected]) _ hmM).setLow
      d n k M inp 0 (Nat.zero_le _) _ 61 (by simp [Protected]) 0 (Nat.zero_le _)
  have hbCount : b.reg (Storage.low d k 60)=rowCount d n := by
    change b.store.reg _=_
    rw [hbs]
    simpa [SamplerEvaluation.reg_layout (Storage.low d k) (Storage.low_injective d k)] using haReady.sizes.rows
  let m := rowCount d n
  let Inv : ℕ → TapeStore (Storage.registers d k) 2 → Prop := fun rem c =>
    rem ≤ m ∧ RowState d n k M inp (m-rem) (Nat.sub_le m rem) c
  have hbody : ∀ rem c,c.reg (Storage.low d k 60)=rem+1 → Inv (rem+1) c →
      ∃ t e,t ≤ rowBodyTime d k C M ∧
        (rowBody d k).Stops inp ((TapeProgram.decStore (Storage.low d k 60) c).toCfg (rowBody d k).entry) t e ∧
        Inv rem e.store ∧ e.reg (Storage.low d k 60)=rem := by
    intro rem c hcr hI
    rcases hI with ⟨hrem,hstate⟩
    have hdec : RowState d n k M inp (m-(rem+1)) (Nat.sub_le m (rem+1))
        (TapeProgram.decStore (Storage.low d k 60) c) :=
      hstate.setLow d n k M inp _ _ c 60 (by simp [Protected]) _
        ((Nat.sub_le _ _).trans (hstate.ready.counters _))
    have hr : m-(rem+1)<rowCount d n := by change m-(rem+1) < m;omega
    obtain ⟨t,e,ht,he,hpost,her⟩ := rowBody_stops_of_layers d n k M inp hM huniq C hLayers
      (m-(rem+1)) hr (TapeProgram.decStore (Storage.low d k 60) c) hdec
    refine ⟨t,e,ht,he,⟨by omega,?_⟩,?_⟩
    · have heq : m-(rem+1)+1=m-rem := by omega
      simpa only [heq] using hpost
    · rw [her]
      simp [TapeProgram.decStore,hcr]
  have hbI : Inv m b.store := by
    constructor
    · rfl
    · simpa [Inv] using hbState
  obtain ⟨t₃,e,ht₃,he,hIe,her⟩ := countedLoop_stops_frame (rowBody d k) (Storage.low d k 60) inp
    (rowBodyTime d k C M) Inv hbody m b.store hbCount hbI
  have heOut : e.output=matrixBits (binarySamplerFromInput d n k (Nat.log 2 (n/k)) inp) := by
    have ho := hIe.2.output
    change e.output=SamplerRows.rowsBefore (n:=n) (operations d n) (formValues d n k inp)
      (hashValues d n k inp) ((fieldSize d n)^d) le_rfl at ho
    exact ho.trans (SamplerRows.prefix_full (q:=fieldSize d n) (d:=d) (k:=k) (b:=2^Nat.log 2 (n/k))
      (n:=n) (operations d n) (formValues d n k inp) (hashValues d n k inp))
  refine ⟨_,_,?_,(ha.seq hb).seq he,heOut⟩
  unfold finishTime
  simp only [ps,Storage.pointPairs,List.length_map,List.length_finRange] at ht₁
  change t₃ ≤ rowCount d n*(rowBodyTime d k C M+2)+1 at ht₃
  omega

theorem layerInvariant_of_ready (d n k M : ℕ) (inp : Inputs)
    (s : TapeStore (Storage.registers d k) 2)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s) (z : Fin ((fieldSize d n)^d))
    (hz : ∀ j,s.reg (Storage.point d k j)=(EncodedTester.digits (fieldSize d n) d z j).val) :
    LayerInvariant d k (fieldExponent d n) (2^Nat.log 2 (n/k)) (fieldExponent_pos d n)
      (formValues d n k inp) (hashValues d n k inp) (EncodedTester.digits (fieldSize d n) d z) M s := by
  refine ⟨hs.environment,hs.sizes.buckets,hz,hs.counters,hs.tables.heads,?_⟩
  exact ⟨hs.tables.marked 0,hs.tables.marked 1,hs.tables.forms,hs.tables.hashes⟩

theorem layerCaps_of_envelope (d n k M : ℕ) (hd : 1 ≤ d) (hM : SamplerEnvelopeCovers d k n M) :
    LayerCaps d k (fieldExponent d n) (2^Nat.log 2 (n/k)) M := by
  constructor
  · simpa [fieldSize,Nat.add_comm] using hM.forms
  · simpa [fieldSize,samplerBucketCount,pow_succ,pow_two,Nat.mul_assoc,Nat.add_comm] using hM.hashes
  · have hq1 : 1 ≤ fieldSize d n := Nat.one_le_pow _ _ (by decide)
    have hd' := Nat.mul_le_mul_left (2*k*fieldSize d n) hd
    have hq' := Nat.mul_le_mul_left (2*k*fieldSize d n*d) hq1
    change 2*k*fieldSize d n ≤ M
    have hf := hM.forms
    nlinarith
  · exact hM.neighbors

theorem ready_of_layerInvariant (d n k M : ℕ) (inp : Inputs)
    (s e : TapeStore (Storage.registers d k) 2)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s) (z : Fin ((fieldSize d n)^d))
    (he : LayerInvariant d k (fieldExponent d n) (2^Nat.log 2 (n/k)) (fieldExponent_pos d n)
      (formValues d n k inp) (hashValues d n k inp) (EncodedTester.digits (fieldSize d n) d z) M e)
    (hf : ∀ j : Fin 80,32 ≤ j.val → j.val<40 → e.reg (Storage.low d k j)=s.reg (Storage.low d k j)) :
    RuntimeReady (Storage.low d k) d n k inp M e := by
  refine ⟨hs.sizes.frame hf,he.field,?_,he.counters⟩
  refine ⟨he.tables.formTable,he.tables.hashTable,?_,he.heads⟩
  intro b
  fin_cases b
  · exact he.tables.formMarked
  · exact he.tables.hashMarked









theorem StablePost.refl (d n k M : ℕ) (inp : Inputs) (s : TapeStore (Storage.registers d k) 2)
    (hs : RuntimeReady (Storage.low d k) d n k inp M s) : StablePost d n k M inp s s :=
  ⟨hs,fun _ => rfl,fun _ => rfl,rfl,rfl⟩

theorem StablePost.trans {d n k M : ℕ} {inp : Inputs}
    {s e f : TapeStore (Storage.registers d k) 2}
    (h : StablePost d n k M inp s e) (g : StablePost d n k M inp e f) : StablePost d n k M inp s f :=
  ⟨g.ready,fun j => (g.points j).trans (h.points j),fun j => (g.countdowns j).trans (h.countdowns j),
    g.remaining.trans h.remaining,g.output.trans h.output⟩

















theorem block_contract_of_step (d n k M : ℕ) (inp : Inputs) (C : ℕ)
    (hStep : StepContract d n k M inp C) : LayerBlockContract d n k M inp (k*(C+1)) := by
  intro s z hs hv hz
  let Good : TapeStore (Storage.registers d k) 2 → Prop := StablePost d n k M inp s
  let value : Fin k → ℕ := fun i => i.val*(2^Nat.log 2 (n/k))+
    (EncodedSampler.neighbor (operations d n) (formValues d n k inp) (hashValues d n k inp) i
      (EncodedTester.digits (fieldSize d n) d z)).val
  have hstep : ∀ i c,Good c → ∃ t e,t ≤ C ∧
      (layer d k i).Stops inp (c.toCfg (layer d k i).entry) t e ∧ Good e.store ∧
      e.reg (Storage.neighbor d k i)=value i ∧
      (∀ j,j≠i → e.reg (Storage.neighbor d k j)=c.reg (Storage.neighbor d k j)) := by
    intro i c hc
    obtain ⟨t,e,ht,he,hpost⟩ := hStep i c z hc.ready (fun j => (hc.points j).trans (hz j))
    exact ⟨t,e,ht,he,hc.trans hpost.stable,hpost.neighbor,hpost.other⟩
  obtain ⟨t,e,ht,he,hstable,hvalues,hframe⟩ := layers_stops_of d k inp C Good value hstep
    (List.finRange k) s (StablePost.refl d n k M inp s hs)
  have heValid : SamplerOdometer.Valid (Storage.low d k 35) (Storage.pointPairs d k) e.store := by
    intro p hp
    obtain ⟨i,hi,hpi⟩ := List.mem_map.mp hp
    subst p
    rw [hstable.points,hstable.countdowns,hstable.ready.sizes.field,← hs.sizes.field]
    exact hv _ (List.mem_map.mpr ⟨i,hi,rfl⟩)
  have heRead : SamplerOdometer.readings (Storage.pointPairs d k) e.store=
      SamplerOdometer.readings (Storage.pointPairs d k) s := by
    apply SamplerOdometer.readings_congr
    intro p hp
    obtain ⟨i,hi,hpi⟩ := List.mem_map.mp hp
    subst p
    exact hstable.points i
  refine ⟨t,e,by simpa using ht,he,⟨hstable.ready,heValid,heRead,hstable.remaining,hstable.output,?_⟩⟩
  intro i
  exact hvalues i (List.mem_finRange i)






theorem sourceTime_polynomial (d k : ℕ) (hd : 0<d) : PolynomialBound (fun n => sourceTime d n k) := by
  have hM := samplerEnvelope_polynomial d k hd
  have hC : PolynomialBound (fun n => blockTime d k (samplerEnvelope d k n)) :=
    (PolynomialBound.const k).mul (((layerTimeUniform_polynomial d k).comp hM).add (PolynomialBound.const 1))
  have hW0 : PolynomialBound (fun M => NeighborWriter.writeRowBound k M) :=
    ((PolynomialBound.const (161*k+25)).mul
      ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 2)).of_le
      (fun M _ => NeighborWriter.writeRowBound_polynomial k M)
  have hW := hW0.comp hM
  have hO : PolynomialBound (fun n => d*(8*samplerEnvelope d k n+20)) :=
    (PolynomialBound.const d).mul (((PolynomialBound.const 8).mul hM).add (PolynomialBound.const 20))
  have hRow : PolynomialBound (fun n => rowBodyTime d k (blockTime d k (samplerEnvelope d k n))
      (samplerEnvelope d k n)) :=
    ((hC.add hW).add hO).add (PolynomialBound.const 2)
  have hF : PolynomialBound (fun n => finishTime d n k (blockTime d k (samplerEnvelope d k n))
      (samplerEnvelope d k n)) :=
    (((hO.add (((PolynomialBound.const 7).mul hM).add (PolynomialBound.const 7))).add
      (PolynomialBound.const 2)).add
      ((rowCount_polynomial d hd).mul (hRow.add (PolynomialBound.const 2)))).add (PolynomialBound.const 1)
  exact ((preludeTime_polynomial d k hd).add (PolynomialBound.const 1)).add hF

theorem sampler_stops_of_step (d n k : ℕ) (hd : 1 ≤ d) (hk : 0<k) (hn : 2 ≤ n) (hnk : k ≤ n)
    (inp : Inputs) (hi : inp.input=sizeInput n)
    (hStep : StepContract d n k (samplerEnvelope d k n) inp
      (layerTimeUniform d k (samplerEnvelope d k n))) :
    ∃ t e,t ≤ sourceTime d n k ∧
      (sampler d k).Stops inp ((initialStore (Storage.registers d k) 2).toCfg (sampler d k).entry) t e ∧
      e.output=matrixBits (binarySamplerFromInput d n k (Nat.log 2 (n/k)) inp) := by
  have hM := samplerEnvelope_covers d k n
  obtain ⟨t₁,a,ht₁,ha,has,haReady,haOut⟩ := prelude_stops (Storage.low d k)
    (Storage.low_injective d k) d n k hd hk hn hnk inp hi (samplerEnvelope d k n) hM
  obtain ⟨t₂,e,ht₂,he,heo⟩ := finish_stops_of_layers d n k (samplerEnvelope d k n) inp
    (by have := hM.two;omega) (Storage.pointPairs_nodup d k) (blockTime d k (samplerEnvelope d k n))
    (block_contract_of_step d n k _ inp _ hStep) a.store haReady haOut
  refine ⟨_,_,?_,ha.seq he,heo⟩
  unfold sourceTime
  omega

theorem sampler_source_of_step (d n k : ℕ) (hd : 1 ≤ d) (hk : 0<k) (hn : 2 ≤ n) (hnk : k ≤ n)
    (ω : List Bool)
    (hStep : StepContract d n k (samplerEnvelope d k n) ⟨sizeInput n,[],[],ω⟩
      (layerTimeUniform d k (samplerEnvelope d k n))) :
    ∃ t ≤ sourceTime d n k,
      (sampler d k).halted ((sampler d k).run ⟨sizeInput n,[],[],ω⟩ t) ∧
      ((sampler d k).run ⟨sizeInput n,[],[],ω⟩ t).output=
        matrixBits (binarySamplerFromInput d n k (Nat.log 2 (n/k)) ⟨sizeInput n,[],[],ω⟩) := by
  obtain ⟨t,e,ht,he,heo⟩ := sampler_stops_of_step d n k hd hk hn hnk ⟨sizeInput n,[],[],ω⟩ rfl hStep
  have hr := he.exec.iterate
  change (sampler d k).run ⟨sizeInput n,[],[],ω⟩ t=e at hr
  exact ⟨t,ht,by rw [hr];exact he.halted,by rw [hr];exact heo⟩

theorem fieldSize_covers_arity (d n k : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) (hkn : k ≤ n) :
    k ≤ fieldSize d n := by
  calc
    k ≤ n := hkn
    _ = n^1 := by simp
    _ ≤ n^(2*d) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ fieldSize d n := fieldSize_lower d n


theorem step_contract (d n k M : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) (hkn : k ≤ n)
    (hM : SamplerEnvelopeCovers d k n M) (inp : NKtLB.Inputs) :
    StepContract d n k M inp (SamplerProgram.layerTimeUniform d k M) := by
  intro i s z hs hz
  have hkq := fieldSize_covers_arity d n k hd hn hkn
  have hI := layerInvariant_of_ready d n k M inp s hs z hz
  obtain ⟨t,e,ht,he,hIe,hpay,hvalue,hpoints,hcounts,hprotected,hout,hother,hframe⟩ :=
    SamplerProgram.layer_stops i hkq (show 0<2^Nat.log 2 (n/k) from pow_pos (by decide) _)
      (show 1 ≤ M from by have := hM.two;omega) (layerCaps_of_envelope d n k M hd hM) inp s hI
  have heReady : RuntimeReady (SamplerProgram.Storage.low d k) d n k inp M e.store := by
    apply ready_of_layerInvariant d n k M inp s e.store hs z hIe
    intro j hj hj'
    exact hprotected j (Or.inl ⟨hj,by omega⟩)
  have hstable : StablePost d n k M inp s e.store :=
    ⟨heReady,hpoints,hcounts,hprotected 60 (Or.inr (by decide)),hout⟩
  refine ⟨t,e,ht.trans (SamplerProgram.layerTimeBound_le_uniform d k M i),he,⟨hstable,?_,hother⟩⟩
  exact hvalue

/-- The complete concrete sampler really halts and emits the frozen indexed
matrix on every finite random tape, with a polynomial source-step bound. -/
theorem sampler_source (d n k : ℕ) (hd : 1 ≤ d) (hk : 0<k) (hn : 2 ≤ n) (hnk : k ≤ n)
    (ω : List Bool) :
    ∃ t ≤ sourceTime d n k,
      (sampler d k).halted ((sampler d k).run ⟨sizeInput n,[],[],ω⟩ t) ∧
      ((sampler d k).run ⟨sizeInput n,[],[],ω⟩ t).output=
        matrixBits (binarySamplerFromInput d n k (Nat.log 2 (n/k)) ⟨sizeInput n,[],[],ω⟩) := by
  exact sampler_source_of_step d n k hd hk hn hnk ω
    (step_contract d n k (samplerEnvelope d k n) hd hn hnk (samplerEnvelope_covers d k n) _)




end Concrete
end ExpandingCodes.Computation.SamplerAssembly

end FlattenModule103

/-! Inlined whole module: ExpandingCodes.Computation.SamplerSource -/
section FlattenModule104




set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation

/-- A concrete finite source program implementing the explicit indexed sampler
gives the entire canonical sampler clause. Its actual execution and numerical
step bound are hypotheses; random-tape length, exact law, compiler overhead,
and the sufficiently-large-size threshold are proved here. -/
theorem binary_sampler_of_source {R B L : ℕ} (θ : ℚ)
    (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2)
    (P : TapeProgram R B L) (time : ℕ → ℕ) (N : ℕ)
    (htime : PolynomialBound time)
    (hsource : ∀ n ≥ N, ∀ ω : List Bool,
      ∃ t ≤ time n,
        P.halted (P.run ⟨sizeInput n, [], [], ω⟩ t) ∧
          (P.run ⟨sizeInput n, [], [], ω⟩ t).output =
            matrixBits (binarySamplerFromInput (dimension (θ : ℝ)) n (arity (θ : ℝ))
              (Nat.log 2 (n/arity (θ : ℝ))) ⟨sizeInput n, [], [], ω⟩)) :
    SamplerImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) := by
  let d := dimension (θ : ℝ)
  let k := arity (θ : ℝ)
  have hd : 0 < d := (by decide : 0 < 4).trans_le (dimension_ge_four (θ : ℝ) hθ)
  obtain ⟨C,a,hbound⟩ := common_polynomial_envelope htime (samplerEntropy_polynomial d k hd)
  let N' := max N (max 2 k)
  have hN' : 2 ≤ N' := (le_max_left 2 k).trans (le_max_right N (max 2 k))
  apply samplerImplementation_of_tape θ (fun n => binaryGeometry d n) P C a N' hN'
    (fun n ω => binarySamplerFromInput d n k (Nat.log 2 (n/k))
      ⟨sizeInput n, [], [], List.ofFn ω⟩)
  · intro n hn ω
    have hnN : N ≤ n := (le_max_left N (max 2 k)).trans hn
    have hn2 : 2 ≤ n := hN'.trans hn
    obtain ⟨t,ht,hh,hout⟩ := hsource n hnN (List.ofFn ω)
    exact ⟨t,ht.trans (hbound n hn2).1,hh,hout⟩
  · intro n hn G
    have hn2 : 2 ≤ n := hN'.trans hn
    have hkn : k ≤ n := (le_max_right 2 k).trans ((le_max_right N (max 2 k)).trans hn)
    have hkq : k ≤ fieldSize d n := hkn.trans ((show n ≤ n^(2*d) from by
      calc n = n^1 := by simp
           _ ≤ n^(2*d) := Nat.pow_le_pow_right (by omega) (by omega)).trans
        (fieldSize_lower d n))
    exact binarySamplerFromInput_law (θ : ℝ) n _ hkq (hbound n hn2).2 G


end ExpandingCodes.PolynomialStretch

end FlattenModule104

/-! Inlined whole module: ExpandingCodes.Computation.SamplerImplementation -/
section FlattenModule105




set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation
open SamplerAssembly.Concrete























/-- The frozen sampler implementation, witnessed by the fully concrete finite
source program and its proved exact output, random law, and polynomial clock. -/
theorem binary_sampler_implementation_source (θ : ℚ)
    (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2) :
    SamplerImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) := by
  let d := dimension (θ : ℝ)
  let k := arity (θ : ℝ)
  have hd4 : 4 ≤ d := dimension_ge_four (θ : ℝ) hθ
  have hk : 0 < k := hash_arity_pos (θ : ℝ) hθ
  apply binary_sampler_of_source θ hθ (sampler d k) (fun n => sourceTime d n k) (max 2 k)
    (sourceTime_polynomial d k (by omega))
  intro n hn ω
  exact sampler_source d n k (by omega) hk ((le_max_left 2 k).trans hn) ((le_max_right 2 k).trans hn) ω



end ExpandingCodes.PolynomialStretch

end FlattenModule105


section FlattenModule106





set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch















end ExpandingCodes.PolynomialStretch

end FlattenModule106


section FlattenModule107


set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch







end ExpandingCodes.PolynomialStretch

end FlattenModule107


section FlattenModule108


set_option autoImplicit false
open scoped Classical BigOperators Topology
open Filter

namespace ExpandingCodes.PolynomialStretch
























































end ExpandingCodes.PolynomialStretch

end FlattenModule108


section FlattenModule109










set_option autoImplicit false

namespace ExpandingCodes

open scoped BigOperators

variable {K σ : Type*} [Field K] [Fintype K] [Fintype σ] [DecidableEq σ]

































































end ExpandingCodes

end FlattenModule109


section FlattenModule110









set_option autoImplicit false

namespace ExpandingCodes

open scoped BigOperators

variable {K σ ι : Type*} [Field K]






















variable [Fintype K]










































































end ExpandingCodes

end FlattenModule110


section FlattenModule111








set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch























































































end ExpandingCodes.PolynomialStretch

end FlattenModule111


section FlattenModule112


set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch























end ExpandingCodes.PolynomialStretch

end FlattenModule112


section FlattenModule113



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch








































































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule113


section FlattenModule114















set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

open Module




























































































































































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule114


section FlattenModule115



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

open Module











































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule115


section FlattenModule116



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch





























































































































end ExpandingCodes.PolynomialStretch

end FlattenModule116


section FlattenModule117



set_option autoImplicit false
open scoped Classical BigOperators Topology
open Filter

namespace ExpandingCodes.PolynomialStretch





















































end ExpandingCodes.PolynomialStretch

end FlattenModule117


section FlattenModule118


set_option autoImplicit false
open scoped Classical BigOperators Topology
open Set MeasureTheory

namespace ExpandingCodes.PolynomialStretch
















































































































end ExpandingCodes.PolynomialStretch

end FlattenModule118


section FlattenModule119


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

































































































end ExpandingCodes.PolynomialStretch

end FlattenModule119


section FlattenModule120




set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch




















































































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule120


section FlattenModule121



















set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.Erasure

open Module Filter Finset

variable {K I : Type*} [Field K]































































































































variable [Fintype I]





























































































































































































































































































































































































































































































































end ExpandingCodes.Erasure

end FlattenModule121


section FlattenModule122

















set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]












































































































































































































end ExpandingCodes.SharpThreshold

end FlattenModule122


section FlattenModule123









set_option autoImplicit false
namespace ExpandingCodes.SharpThreshold

















































































































































































end ExpandingCodes.SharpThreshold

end FlattenModule123


section FlattenModule124



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.SharpThreshold
open Finset
open ExpandingCodes.Erasure
variable {I : Type*} [Fintype I]






































































































































































































































































































































end ExpandingCodes.SharpThreshold

end FlattenModule124


section FlattenModule125


set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]










end ExpandingCodes.SharpThreshold

end FlattenModule125


section FlattenModule126






set_option autoImplicit false
open scoped Classical
namespace ExpandingCodes.SharpThreshold
open Finset
open ExpandingCodes.Erasure
variable {I : Type*} [Fintype I]
































































































































end ExpandingCodes.SharpThreshold

end FlattenModule126


section FlattenModule127


set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]

























end ExpandingCodes.SharpThreshold

end FlattenModule127


section FlattenModule128




set_option autoImplicit false
open scoped Classical
namespace ExpandingCodes.SharpThreshold
open Finset
open ExpandingCodes.Erasure
variable {I : Type*} [Fintype I]































































































































































































end ExpandingCodes.SharpThreshold

end FlattenModule128


section FlattenModule129


set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]













end ExpandingCodes.SharpThreshold

end FlattenModule129


section FlattenModule130


set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]


















end ExpandingCodes.SharpThreshold

end FlattenModule130


section FlattenModule131


set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure
open scoped Classical

variable {I : Type*} [Fintype I]







































































end ExpandingCodes.SharpThreshold

end FlattenModule131


section FlattenModule132
















set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]





















































































































































































































end ExpandingCodes.SharpThreshold

end FlattenModule132


section FlattenModule133













set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open Filter


























































































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule133


section FlattenModule134





set_option autoImplicit false
open scoped Classical Topology
open Filter

namespace ExpandingCodes.PolynomialStretch































end ExpandingCodes.PolynomialStretch

end FlattenModule134


section FlattenModule135




set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch



















end ExpandingCodes.PolynomialStretch

end FlattenModule135


section FlattenModule136


end FlattenModule136


section FlattenModule137

















set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

open Filter Module



















































































































open MeasureTheory
























































































































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule137


section FlattenModule138


set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch


















end ExpandingCodes.PolynomialStretch

end FlattenModule138


section FlattenModule139





end FlattenModule139


section FlattenModule140



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open Filter

















end ExpandingCodes.PolynomialStretch

end FlattenModule140


section FlattenModule141



set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch




















end ExpandingCodes.PolynomialStretch

end FlattenModule141


section FlattenModule142


set_option autoImplicit false
open Filter Topology

namespace ExpandingCodes.PolynomialStretch




































end ExpandingCodes.PolynomialStretch

end FlattenModule142


section FlattenModule143




set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch


























































end ExpandingCodes.PolynomialStretch

end FlattenModule143


section FlattenModule144


end FlattenModule144


section FlattenModule145



set_option autoImplicit false
open scoped Classical
open ExpandingCodes.PolynomialStretch



















end FlattenModule145

open ExpandingCodes.PolynomialStretch in
theorem solution (θ : ℚ)
    (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2) :
    SamplerImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) := by
  exact ExpandingCodes.PolynomialStretch.binary_sampler_implementation_source θ hθ
