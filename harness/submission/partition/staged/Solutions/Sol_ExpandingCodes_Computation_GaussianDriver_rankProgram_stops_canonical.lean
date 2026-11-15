import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime
import Mathlib
import Theorems.Thm_ExpandingCodes_Computation_SourceFieldArithmetic_addition_stops
import Theorems.Thm_ExpandingCodes_Computation_SourceFieldArithmetic_inverse_stops
import Theorems.Thm_ExpandingCodes_Computation_SourceFieldArithmetic_multiply_stops

set_option autoImplicit false
open scoped BigOperators


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


section FlattenModule3



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch









































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





 theorem getD_writeAt (l : List Sym) (h k : ℕ) (a : Sym) :
    (Machine.writeAt l h a).getD k Sym.blank =
      if k = h then a else l.getD k Sym.blank := by
  have hlen : h < (l ++ List.replicate (h + 1 - l.length) Sym.blank).length := by
    simp only [List.length_append, List.length_replicate]
    omega
  unfold Machine.writeAt
  by_cases hk : k = h
  · subst k
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hlen]
    simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hk)]
    simp only [if_neg hk]
    by_cases kl : k < l.length
    · rw [← List.getD_eq_getElem?_getD, List.getD_append _ _ _ _ kl]
    · rw [← List.getD_eq_getElem?_getD,
        List.getD_append_right _ _ _ _ (by omega),
        List.getD_eq_default l Sym.blank (by omega)]
      simp [List.getD_eq_getElem?_getD]

 





 







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





 theorem addPreserving_post (d : TapeStore R B) (src dst tmp : Fin R)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp) :
    transferStore (distributeStore (d.setReg tmp 0) src dst tmp) tmp src =
      (d.setReg dst (d.reg dst+d.reg src)).setReg tmp 0 := by
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

 theorem addPreserving_stops (src dst tmp : Fin R)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (addPreserving src dst tmp).Stops inp (d.toCfg (addPreserving (B := B) src dst tmp).entry)
      (d.reg tmp + 5*d.reg src + 5) e ∧
      e.store = (d.setReg dst (d.reg dst+d.reg src)).setReg tmp 0 := by
  let d₁ := d.setReg tmp 0
  let d₂ := distributeStore d₁ src dst tmp
  have h₁ := clear_stops tmp inp (d.reg tmp) d rfl
  have h₂ := distribute_stops src dst tmp hsd hst hdt inp (d.reg src) d₁
    (by simp [d₁, TapeStore.setReg, hst])
  have hreg : d₂.reg tmp = d.reg src := by
    simp [d₂, d₁, distributeStore, TapeStore.setReg, hsd, hst, hdt]
  have h₃ := transfer_stops tmp src (Ne.symm hst) inp (d.reg src) d₂ hreg
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨((transferStore d₂ tmp src).toCfg (2 : Fin 3)).mapPC (TapeProgram.rightLabel 6), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change transferStore d₂ tmp src = _
    exact addPreserving_post d src dst tmp hsd hst hdt













 





















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








theorem mulLoopStore_step (d : TapeStore R B) (a dst tmp count : Fin R)
    (had : a ≠ dst) (hat : a ≠ tmp) (hac : a ≠ count)
    (hdt : dst ≠ tmp) (hdc : dst ≠ count) (htc : tmp ≠ count)
    (n : ℕ) :
    mulLoopStore
      (((d.setReg count n).setReg dst (d.reg dst+d.reg a)).setReg tmp 0)
      a dst tmp count n = mulLoopStore d a dst tmp count (n+1) := by
  simp only [mulLoopStore, TapeStore.setReg]
  congr 1
  funext j
  by_cases ht : j = tmp
  · subst j; simp [Function.update]
  · simp only [Function.update_of_ne ht]
    by_cases hd : j = dst
    · subst j
      simp [Function.update, had, hat, hac, hdt, hdc, htc,
        Ne.symm hdt, Ne.symm hdc, Nat.succ_mul]
      omega
    · simp only [Function.update_of_ne hd]
      by_cases hc : j = count
      · subst j; simp [Function.update]
      · simp [Function.update, hc, hd, ht]

/-- A checked repeated-addition execution. Neither operand size nor the runtime
loop count occurs in the finite program's type or code table. -/
theorem mulLoop_stops (a dst tmp count : Fin R)
    (had : a ≠ dst) (hat : a ≠ tmp) (hac : a ≠ count)
    (hdt : dst ≠ tmp) (hdc : dst ≠ count) (htc : tmp ≠ count)
    (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hn : d.reg count = n) (ht : d.reg tmp = 0) :
    (mulLoop a dst tmp count).Stops inp
      (d.toCfg (TapeProgram.loopHeader 9)) (n*(5*d.reg a+7)+1)
      ((mulLoopStore d a dst tmp count n).toCfg (TapeProgram.loopExit 9)) := by
  induction n generalizing d with
  | zero =>
    have he : mulLoopStore d a dst tmp count 0 = d := by
      have hc : d.setReg count 0 = d := by simp [TapeStore.setReg, ← hn]
      have htt : d.setReg tmp 0 = d := by simp [TapeStore.setReg, ← ht]
      simp only [mulLoopStore, zero_mul, Nat.add_zero, hc]
      simpa [TapeStore.setReg] using htt
    simpa [mulLoop, he] using
      TapeProgram.loop_zero (TapeMacros.addPreserving a dst tmp) count inp d hn
  | succ n ih =>
    let d₁ := d.setReg count n
    obtain ⟨c, hc, hstore⟩ := TapeMacros.addPreserving_stops a dst tmp had hat hdt inp d₁
    have hca : c.reg a = d.reg a := by
      change c.store.reg a = _
      rw [hstore]
      simp [d₁, TapeStore.setReg, had, hat, hac]
    have hcn : c.reg count = n := by
      change c.store.reg count = _
      rw [hstore]
      simp [d₁, TapeStore.setReg, Ne.symm hdc, Ne.symm htc]
    have hct : c.reg tmp = 0 := by
      change c.store.reg tmp = _
      rw [hstore]
      simp
    have htail := ih c.store hcn hct
    have hs : d₁.reg tmp + 5*d₁.reg a + 5 = 5*d.reg a+5 := by
      simp [d₁, TapeStore.setReg, hat, hac, htc, ht]
    rw [hs] at hc
    have hhead := TapeProgram.loop_positive_header
      (TapeMacros.addPreserving a dst tmp) count inp d (by omega)
    have hdec : TapeProgram.decStore count d = d₁ := by
      simp [TapeProgram.decStore, d₁, TapeStore.setReg, hn]
    rw [hdec] at hhead
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (TapeMacros.addPreserving a dst tmp) count)
    have hreturn := TapeProgram.loop_body_return
      (TapeMacros.addPreserving a dst tmp) count inp c hc.halted
    have hpost : mulLoopStore c.store a dst tmp count n =
        mulLoopStore d a dst tmp count (n+1) := by
      rw [hstore]
      have hda : d₁.reg a = d.reg a := by simp [d₁, TapeStore.setReg, hac]
      have hdd : d₁.reg dst = d.reg dst := by simp [d₁, TapeStore.setReg, hdc]
      rw [hda, hdd]
      exact mulLoopStore_step d a dst tmp count had hat hac hdt hdc htc n
    constructor
    · have hall := ((hhead.trans hrun).trans hreturn).trans htail.exec
      rw [hpost] at hall
      change (mulLoop a dst tmp count).Exec inp _ _ _ at hall
      convert hall using 1
      simp only [TapeCfg.store, hca]
      ring
    · exact TapeProgram.loop_code_exit (TapeMacros.addPreserving a dst tmp) count










theorem multiply_stops (a b dst tmp count : Fin R)
    (had : a ≠ dst) (hat : a ≠ tmp) (hac : a ≠ count)
    (hbd : b ≠ dst) (hbt : b ≠ tmp) (hbc : b ≠ count)
    (hdt : dst ≠ tmp) (hdc : dst ≠ count) (htc : tmp ≠ count)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ t e, t ≤ d.reg dst+d.reg count+d.reg tmp+5*d.reg b+
        d.reg b*(5*d.reg a+7)+11 ∧
      (multiply a b dst tmp count).Stops inp
        (d.toCfg (multiply (B := B) a b dst tmp count).entry) t e ∧
      e.store = multiplyStore d a b dst tmp count := by
  let d₁ := d.setReg dst 0
  have h₁ := TapeMacros.clear_stops dst inp (d.reg dst) d rfl
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops b count tmp hbc hbt (Ne.symm htc) inp d₁
  have hca : c.reg a = d.reg a := by
    change c.store.reg a = _
    rw [hcs]
    simp [d₁, TapeStore.setReg, had, hat, hac]
  have hcn : c.reg count = d.reg b := by
    change c.store.reg count = _
    rw [hcs]
    simp [d₁, TapeStore.setReg, hbd, Ne.symm htc]
  have hct : c.reg tmp = 0 := by
    change c.store.reg tmp = _
    rw [hcs]
    simp
  have hloop := mulLoop_stops a dst tmp count had hat hac hdt hdc htc
    inp (d.reg b) c.store hcn hct
  have hall := (h₁.seq hc).seq hloop
  have hpost : mulLoopStore c.store a dst tmp count (d.reg b) =
      multiplyStore d a b dst tmp count := by
    rw [hcs]
    simp only [mulLoopStore, multiplyStore, d₁, TapeStore.setReg]
    congr 1
    funext j
    by_cases ht : j = tmp
    · subst j
      simp [Function.update, htc, Ne.symm htc]
    · by_cases hc' : j = count
      · subst j
        simp [Function.update, had, hat, hac, hbd, hdt, hdc, htc, Ne.symm htc, Ne.symm hdc]
      · by_cases hd : j = dst
        · subst j
          simp [Function.update, had, hat, hac, hbd, hbt, hbc, hdt, hdc, htc,
            Ne.symm hdt, Ne.symm hdc, Nat.mul_comm]
        · simp [Function.update, ht, hc', hd]
  refine ⟨_, _, ?_, hall, ?_⟩
  · simp [d₁, TapeStore.setReg, Ne.symm hdc, Ne.symm hdt, hbd, TapeCfg.store, hca]
    omega
  · change mulLoopStore c.store a dst tmp count (d.reg b) = _
    exact hpost

theorem multiply_stops_polynomial (a b dst tmp count : Fin R)
    (had : a ≠ dst) (hat : a ≠ tmp) (hac : a ≠ count)
    (hbd : b ≠ dst) (hbt : b ≠ tmp) (hbc : b ≠ count)
    (hdt : dst ≠ tmp) (hdc : dst ≠ count) (htc : tmp ≠ count)
    (inp : Inputs) (d : TapeStore R B) (M : ℕ)
    (ha : d.reg a ≤ M) (hb : d.reg b ≤ M) (hd : d.reg dst ≤ M)
    (ht : d.reg tmp ≤ M) (hc : d.reg count ≤ M) :
    ∃ t e, t ≤ 32*(M+1)^2 ∧
      (multiply a b dst tmp count).Stops inp
        (d.toCfg (multiply (B := B) a b dst tmp count).entry) t e ∧
      e.store = multiplyStore d a b dst tmp count := by
  obtain ⟨t, e, htime, hstop, hstore⟩ :=
    multiply_stops a b dst tmp count had hat hac hbd hbt hbc hdt hdc htc inp d
  refine ⟨t, e, htime.trans ?_, hstop, hstore⟩
  have hp := Nat.mul_le_mul hb (show 5*d.reg a+7 ≤ 7*(M+1) by omega)
  nlinarith































































































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








 theorem SamePayload.refl (d : TapeStore R B) : SamePayload d d :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

 theorem SamePayload.trans {d e f : TapeStore R B}
    (h : SamePayload d e) (k : SamePayload e f) : SamePayload d f :=
  ⟨h.roHead.trans k.roHead, h.output.trans k.output, fun b n => (h.symbol b n).trans (k.symbol b n)⟩

 theorem setReg_payload (d : TapeStore R B) (r : Fin R) (n : ℕ) :
    SamePayload (d.setReg r n) d := ⟨rfl, rfl, fun _ _ => rfl⟩
end TapeStore

namespace TapeArrays
variable {R B : ℕ}
open TapeMacros






 theorem moved_payload (d : TapeStore R B) (b : Fin B) (m : Move) :
    TapeStore.SamePayload (moved d b m) d := by
  constructor
  · rfl
  · rfl
  · intro c k
    by_cases h : c = b
    · subst c
      simp only [moved, cellStore, Function.update_self]
      rw [getD_writeAt]
      split <;> simp_all
    · simp [moved, cellStore, Function.update_of_ne h]

@[simp] theorem moved_reg (d : TapeStore R B) (b : Fin B) (m : Move) :
    (moved d b m).reg = d.reg := rfl

@[simp] theorem moved_head (d : TapeStore R B) (b : Fin B) (m : Move) :
    (moved d b m).bufferHead = Function.update d.bufferHead b (Machine.moveHead m (d.bufferHead b)) := rfl








 theorem seekRight_stops (r : Fin R) (b : Fin B) (inp : Inputs)
    (n : ℕ) (d : TapeStore R B) (hd : d.reg r = n) :
    ∃ e, (seekRight r b).Stops inp (d.toCfg 0) (2*n+1) (e.toCfg 2) ∧
      e.reg = Function.update d.reg r 0 ∧
      e.bufferHead = Function.update d.bufferHead b (d.bufferHead b+n) ∧
      TapeStore.SamePayload e d := by
  induction n generalizing d with
  | zero =>
    refine ⟨d, ?_, ?_, ?_, TapeStore.SamePayload.refl d⟩
    · constructor
      · apply TapeProgram.Exec.one
        · simp [TapeProgram.halted, seekRight]
        · simp [TapeProgram.step, seekRight, TapeStore.toCfg, hd]
      · simp [TapeProgram.halted, seekRight]
    · simp [← hd]
    · simp
  | succ n ih =>
    let d₁ := d.setReg r n
    let d₂ := moved d₁ b .right
    have hd₂ : d₂.reg r = n := by simp [d₂, d₁, TapeStore.setReg]
    obtain ⟨e, he, her, heh, hep⟩ := ih d₂ hd₂
    refine ⟨e, ?_, ?_, ?_, ?_⟩
    · have hs₁ : (seekRight r b).step inp (d.toCfg 0) = d₁.toCfg 1 := by
        simp [TapeProgram.step, seekRight, TapeStore.toCfg, TapeStore.setReg, d₁, hd]
      have hs₂ : (seekRight r b).step inp (d₁.toCfg 1) = d₂.toCfg 0 := by
        simp [TapeProgram.step, seekRight, TapeStore.toCfg, d₂, moved, cellStore]
      constructor
      · have h := TapeProgram.Exec.step (by simp [TapeProgram.halted, seekRight]) hs₁
          (TapeProgram.Exec.step (by simp [TapeProgram.halted, seekRight]) hs₂ he.exec)
        simpa [Nat.mul_succ, Nat.add_assoc] using h
      · exact he.halted
    · simpa [d₂, d₁, TapeStore.setReg, Function.update_idem] using her
    · rw [heh]
      simp [d₂, d₁, moved, cellStore, TapeStore.setReg, Machine.moveHead, Function.update_idem, Nat.add_assoc, Nat.add_comm]
    · exact hep.trans ((moved_payload d₁ b .right).trans (TapeStore.setReg_payload d r n))













 theorem reset_stops (b : Fin B) (inp : Inputs) (h : ℕ) (d : TapeStore R B)
    (hd : d.bufferHead b = h) (hm : Marked d b) :
    ∃ e, (reset b).Stops inp (d.toCfg 0) (h+1) (e.toCfg 1) ∧
      e.reg = d.reg ∧ e.bufferHead = Function.update d.bufferHead b 0 ∧
      TapeStore.SamePayload e d := by
  induction h generalizing d with
  | zero =>
    let e := moved d b .stay
    have hm0 := hm.1
    change ((d.bufferTape b)[0]?).getD .blank = .bot at hm0
    refine ⟨e, ?_, rfl, ?_, moved_payload d b .stay⟩
    · constructor
      · apply TapeProgram.Exec.one
        · simp [TapeProgram.halted, reset]
        · simp [TapeProgram.step, reset, TapeStore.toCfg, hd, hm0, e, moved, cellStore]
      · simp [TapeProgram.halted, reset]
    · simp [e, moved, cellStore, hd, Machine.moveHead]
  | succ h ih =>
    let d₁ := moved d b .left
    have hs : (d.bufferTape b).getD (d.bufferHead b) .blank ≠ .bot :=
      hm.2 _ (by omega) (by omega)
    have hd₁ : d₁.bufferHead b = h := by simp [d₁, moved, cellStore, hd, Machine.moveHead]
    have hp := moved_payload d b .left
    have hm₁ : Marked d₁ b := by
      constructor
      · rw [hp.symbol]
        exact hm.1
      · intro k hk hkh
        rw [hp.symbol]
        exact hm.2 k hk (by rw [hd₁] at hkh; omega)
    obtain ⟨e, he, her, heh, hep⟩ := ih d₁ hd₁ hm₁
    refine ⟨e, ?_, her, ?_, hep.trans hp⟩
    · constructor
      · have hs₁ : (reset b).step inp (d.toCfg 0) = d₁.toCfg 0 := by
          change ((d.bufferTape b)[d.bufferHead b]?).getD .blank ≠ .bot at hs
          simp [TapeProgram.step, reset, TapeStore.toCfg, hs, d₁, moved, cellStore]
        exact TapeProgram.Exec.step (by simp [TapeProgram.halted, reset]) hs₁ he.exec
      · exact he.halted
    · rw [heh]
      simp [d₁, moved, cellStore, Function.update_idem]






















 





























 






















 








 









 










 



















































 theorem fillStore_reg (b : Fin B) (s : Sym) (n : ℕ) (d : TapeStore R B) :
    (fillStore b s n d).reg = d.reg := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => exact ih _

 theorem fillStore_roHead (b : Fin B) (s : Sym) (n : ℕ) (d : TapeStore R B) :
    (fillStore b s n d).roHead = d.roHead := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => exact ih _

 theorem fillStore_output (b : Fin B) (s : Sym) (n : ℕ) (d : TapeStore R B) :
    (fillStore b s n d).output = d.output := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => exact ih _

 theorem fillStore_head (b : Fin B) (s : Sym) (n : ℕ) (d : TapeStore R B) :
    (fillStore b s n d).bufferHead = Function.update d.bufferHead b (d.bufferHead b+n) := by
  induction n generalizing d with
  | zero => simp [fillStore]
  | succ n ih =>
    rw [fillStore, ih]
    simp [painted, cellStore, Machine.moveHead, Function.update_idem, Nat.add_assoc, Nat.add_comm]

 theorem fillStore_symbol (b : Fin B) (s : Sym) (n : ℕ) (d : TapeStore R B)
    (c : Fin B) (k : ℕ) :
    ((fillStore b s n d).bufferTape c).getD k .blank =
      if c = b ∧ d.bufferHead b ≤ k ∧ k < d.bufferHead b+n then s
      else (d.bufferTape c).getD k .blank := by
  induction n generalizing d with
  | zero =>
    simp only [fillStore, Nat.add_zero]
    split_ifs with hc
    · omega
    · rfl
  | succ n ih =>
    rw [fillStore, ih]
    simp only [painted, cellStore, Machine.moveHead, Function.update_self]
    by_cases hc : c = b
    · subst c
      simp only [Function.update_self, true_and, getD_writeAt]
      by_cases hk : k = d.bufferHead b
      · subst k
        simp
      · by_cases hl : d.bufferHead b < k
        · have h₂ : (d.bufferHead b+1 ≤ k ∧ k < d.bufferHead b+1+n) ↔
              (d.bufferHead b ≤ k ∧ k < d.bufferHead b+(n+1)) := by omega
          simp only [h₂, if_neg hk]
        · have h₁ : ¬ d.bufferHead b+1 ≤ k := by omega
          have h₂ : ¬ d.bufferHead b ≤ k := by omega
          simp [h₁, h₂, hk]
    · simp [hc, Function.update_of_ne hc]







 theorem writeRun_stops (r : Fin R) (b : Fin B) (s : Sym) (inp : Inputs)
    (n : ℕ) (d : TapeStore R B) (hd : d.reg r = n) :
    (writeRun r b s).Stops inp (d.toCfg 0) (2*n+1)
      ((fillStore b s n (d.setReg r 0)).toCfg 2) := by
  induction n generalizing d with
  | zero =>
    have hc : d.setReg r 0 = d := by simp [TapeStore.setReg, ← hd]
    constructor
    · apply TapeProgram.Exec.one
      · simp [TapeProgram.halted, writeRun]
      · simp [TapeProgram.step, writeRun, TapeStore.toCfg, hd, fillStore, hc]
    · simp [TapeProgram.halted, writeRun]
  | succ n ih =>
    let d₁ := d.setReg r n
    let e := painted d₁ b s
    have he : e.reg r = n := by simp [e, d₁, painted, cellStore, TapeStore.setReg]
    have ht := ih e he
    have hs₁ : (writeRun r b s).step inp (d.toCfg 0) = d₁.toCfg 1 := by
      simp [TapeProgram.step, writeRun, TapeStore.toCfg, d₁, TapeStore.setReg, hd]
    have hs₂ : (writeRun r b s).step inp (d₁.toCfg 1) = e.toCfg 0 := by
      simp [TapeProgram.step, writeRun, TapeStore.toCfg, e, painted, cellStore]
    have hpost : e.setReg r 0 = painted (d.setReg r 0) b s := by
      simp [e, d₁, painted, cellStore, TapeStore.setReg, Function.update_idem]
    constructor
    · have h := TapeProgram.Exec.step (by simp [TapeProgram.halted, writeRun]) hs₁
        (TapeProgram.Exec.step (by simp [TapeProgram.halted, writeRun]) hs₂ ht.exec)
      simpa [hpost, fillStore, Nat.mul_succ, Nat.add_assoc] using h
    · exact ht.halted








 theorem writeDebit_stops (value width : Fin R) (hne : value ≠ width) (b : Fin B)
    (s : Sym) (inp : Inputs) (n : ℕ) (d : TapeStore R B) (hd : d.reg value = n) :
    (writeDebit value width b s).Stops inp (d.toCfg 0) (3*n+1)
      ((fillStore b s n ((d.setReg value 0).setReg width (d.reg width-n))).toCfg 3) := by
  induction n generalizing d with
  | zero =>
    have hc : (d.setReg value 0).setReg width (d.reg width-0) = d := by
      have hv : d.setReg value 0 = d := by simp [TapeStore.setReg, ← hd]
      rw [hv]
      simp [TapeStore.setReg]
    constructor
    · apply TapeProgram.Exec.one
      · simp [TapeProgram.halted, writeDebit]
      · change (writeDebit value width b s).step inp (d.toCfg 0) =
          (((d.setReg value 0).setReg width (d.reg width-0)).toCfg 3)
        rw [hc]
        simp [TapeProgram.step, writeDebit, TapeStore.toCfg, hd]
    · simp [TapeProgram.halted, writeDebit]
  | succ n ih =>
    let d₁ := d.setReg value n
    let d₂ := d₁.setReg width (d.reg width-1)
    let e := painted d₂ b s
    have he : e.reg value = n := by simp [e, d₂, d₁, painted, cellStore, TapeStore.setReg, hne]
    have ht := ih e he
    have hs₁ : (writeDebit value width b s).step inp (d.toCfg 0) = d₁.toCfg 1 := by
      simp [TapeProgram.step, writeDebit, TapeStore.toCfg, d₁, TapeStore.setReg, hd]
    have hs₂ : (writeDebit value width b s).step inp (d₁.toCfg 1) = d₂.toCfg 2 := by
      simp only [TapeProgram.step, writeDebit, TapeStore.toCfg, show (1 : Fin 4) ≠ 0 by decide,
        if_false, if_true]
      split <;> simp_all [d₂, d₁, TapeStore.setReg, Function.update_of_ne (Ne.symm hne)]
    have hs₃ : (writeDebit value width b s).step inp (d₂.toCfg 2) = e.toCfg 0 := by
      simp [TapeProgram.step, writeDebit, TapeStore.toCfg, e, painted, cellStore]
    have hpost : (e.setReg value 0).setReg width (e.reg width-n) =
        painted ((d.setReg value 0).setReg width (d.reg width-(n+1))) b s := by
      simp only [e, d₂, d₁, painted, cellStore, TapeStore.setReg]
      congr 1
      funext j
      by_cases hw : j = width
      · subst j
        simp [Function.update, hne, Ne.symm hne, Nat.sub_sub, Nat.add_comm]
      · by_cases hv : j = value
        · subst j
          simp [Function.update, hne, Ne.symm hne]
        · simp [Function.update, hw, hv]
    constructor
    · have h := TapeProgram.Exec.step (by simp [TapeProgram.halted, writeDebit]) hs₁
        (TapeProgram.Exec.step (by simp [TapeProgram.halted, writeDebit]) hs₂
          (TapeProgram.Exec.step (by simp [TapeProgram.halted, writeDebit]) hs₃ ht.exec))
      rw [hpost] at h
      convert h using 1 <;> first | rfl | omega
    · exact ht.halted










 theorem writeBlock_stops (value width : Fin R) (hne : value ≠ width) (b : Fin B)
    (inp : Inputs) (v w : ℕ) (d : TapeStore R B) (hv : d.reg value = v)
    (hw : d.reg width = w) (hvw : v ≤ w) :
    ∃ e, (writeBlock value width b).Stops inp (d.toCfg (writeBlock (B := B) value width b).entry)
      (2*w+v+3) e ∧ e.store = writeBlockStore value width b v w d := by
  let d₁ := fillStore b .one v ((d.setReg value 0).setReg width (w-v))
  have h₁ := writeDebit_stops value width hne b .one inp v d hv
  have h₁' : (writeDebit value width b .one).Stops inp (d.toCfg 0) (3*v+1) (d₁.toCfg 3) := by
    simpa [d₁, hw] using h₁
  have hr : d₁.reg width = w-v := by simp [d₁, fillStore_reg, TapeStore.setReg]
  have h₂ := writeRun_stops width b .zero inp (w-v) d₁ hr
  have hall := h₁'.seq h₂
  refine ⟨((writeBlockStore value width b v w d).toCfg (2 : Fin 3)).mapPC (TapeProgram.rightLabel 4), ?_, rfl⟩
  · convert hall using 1 <;> first | rfl | omega






 theorem writeBlockStore_reg (value width : Fin R) (b : Fin B) (v w : ℕ) (d : TapeStore R B) :
    (writeBlockStore value width b v w d).reg =
      ((d.setReg value 0).setReg width 0).reg := by
  simp [writeBlockStore, fillStore_reg, TapeStore.setReg, Function.update_idem]

 theorem writeBlockStore_head (value width : Fin R) (b : Fin B) (v w : ℕ)
    (d : TapeStore R B) (hv : v ≤ w) :
    (writeBlockStore value width b v w d).bufferHead =
      Function.update d.bufferHead b (d.bufferHead b+w) := by
  have h : v+(w-v) = w := by omega
  simp [writeBlockStore, fillStore_head, TapeStore.setReg, Function.update_idem, Nat.add_assoc, h]

 theorem writeBlockStore_roHead (value width : Fin R) (b : Fin B) (v w : ℕ) (d : TapeStore R B) :
    (writeBlockStore value width b v w d).roHead = d.roHead := by
  simp [writeBlockStore, fillStore_roHead, TapeStore.setReg]

 theorem writeBlockStore_output (value width : Fin R) (b : Fin B) (v w : ℕ) (d : TapeStore R B) :
    (writeBlockStore value width b v w d).output = d.output := by
  simp [writeBlockStore, fillStore_output, TapeStore.setReg]

 theorem writeBlockStore_symbol (value width : Fin R) (b : Fin B) (v w : ℕ)
    (d : TapeStore R B) (hv : v ≤ w) (c : Fin B) (k : ℕ) :
    ((writeBlockStore value width b v w d).bufferTape c).getD k .blank =
      if c = b ∧ d.bufferHead b ≤ k ∧ k < d.bufferHead b+w then
        if k < d.bufferHead b+v then .one else .zero
      else (d.bufferTape c).getD k .blank := by
  simp only [writeBlockStore, fillStore_symbol, fillStore_head, TapeStore.setReg,
    Function.update_self]
  by_cases hc : c = b
  · subst c
    simp only [true_and]
    split_ifs <;> first | rfl | omega
  · simp [hc]

 










/-- Moving a preserving scanner one cell shifts a thermometer window and
removes one possible leading one. -/
 theorem ThermometerAt.tail {d e : TapeStore R B} {b : Fin B} {w v : ℕ}
    (h : ThermometerAt d b (d.bufferHead b) (w+1) v)
    (hp : TapeStore.SamePayload e d) (hh : e.bufferHead b = d.bufferHead b+1) :
    ThermometerAt e b (e.bufferHead b) w (v-1) := by
  refine ⟨by have := h.1; omega, ?_⟩
  intro j hj
  rw [hp.symbol, hh]
  have hk := h.2 (j+1) (by omega)
  have he : d.bufferHead b+1+j = d.bufferHead b+(j+1) := by omega
  rw [he, hk]
  have hi : j+1 < v ↔ j < v-1 := by omega
  simp only [hi]


















 theorem readTick_payload (width value : Fin R) (b : Fin B) (d : TapeStore R B) :
    TapeStore.SamePayload (readTickStore width value b d) d := by
  have hp := (moved_payload (TapeProgram.decStore width d) b .right).trans
    (TapeStore.setReg_payload d width (d.reg width-1))
  unfold readTickStore
  split
  · exact (TapeStore.setReg_payload _ value (d.reg value+1)).trans hp
  · exact hp

 theorem readTick_head (width value : Fin R) (b : Fin B) (d : TapeStore R B) :
    (readTickStore width value b d).bufferHead =
      Function.update d.bufferHead b (d.bufferHead b+1) := by
  unfold readTickStore
  split <;> rfl

 theorem readTick_reg (width value : Fin R) (hne : width ≠ value) (b : Fin B) (d : TapeStore R B) :
    (readTickStore width value b d).reg =
      Function.update (Function.update d.reg width (d.reg width-1)) value
        (d.reg value + readDelta d b) := by
  unfold readTickStore readDelta
  split
  · rfl
  · simp [TapeStore.setReg, moved, cellStore, TapeProgram.decStore,
      Function.update_of_ne (Ne.symm hne)]

 theorem readTick_exec (width value : Fin R) (hne : width ≠ value) (b : Fin B)
    (inp : Inputs) (d : TapeStore R B) (hd : d.reg width ≠ 0) :
    (readBlock width value b).Exec inp (d.toCfg 0) (2+readDelta d b)
      ((readTickStore width value b d).toCfg 0) := by
  let d₁ := TapeProgram.decStore width d
  let d₂ := moved d₁ b .right
  have hs₁ : (readBlock width value b).step inp (d.toCfg 0) = d₁.toCfg 1 := by
    simp [TapeProgram.step, readBlock, TapeStore.toCfg, hd, d₁, TapeProgram.decStore]
  by_cases hs : (d.bufferTape b).getD (d.bufferHead b) .blank = .one
  · have hs' := hs
    change ((d.bufferTape b)[d.bufferHead b]?).getD .blank = .one at hs'
    have hs₂ : (readBlock width value b).step inp (d₁.toCfg 1) = d₂.toCfg 2 := by
      simp [TapeProgram.step, readBlock, TapeStore.toCfg, d₂, d₁, TapeProgram.decStore,
        moved, cellStore, hs']
    have hs₃ : (readBlock width value b).step inp (d₂.toCfg 2) =
        (readTickStore width value b d).toCfg 0 := by
      simp [TapeProgram.step, readBlock, TapeStore.toCfg, readTickStore, hs', d₂, d₁,
        moved, cellStore, TapeStore.setReg, TapeProgram.decStore, Function.update_of_ne (Ne.symm hne)]
    have h := TapeProgram.Exec.step (by simp [TapeProgram.halted, readBlock]) hs₁
      (TapeProgram.Exec.step (by simp [TapeProgram.halted, readBlock]) hs₂
        (TapeProgram.Exec.one (by simp [TapeProgram.halted, readBlock]) hs₃))
    simpa only [readDelta, if_pos hs] using h
  · have hs' := hs
    change ((d.bufferTape b)[d.bufferHead b]?).getD .blank ≠ .one at hs'
    have hs₂ : (readBlock width value b).step inp (d₁.toCfg 1) =
        (readTickStore width value b d).toCfg 0 := by
      simp [TapeProgram.step, readBlock, TapeStore.toCfg, readTickStore, hs, d₁,
        TapeProgram.decStore, moved, cellStore, hs']
    have h := TapeProgram.Exec.step (by simp [TapeProgram.halted, readBlock]) hs₁
      (TapeProgram.Exec.one (by simp [TapeProgram.halted, readBlock]) hs₂)
    simpa only [readDelta, if_neg hs] using h

 theorem readBlock_stops (width value : Fin R) (hne : width ≠ value) (b : Fin B)
    (inp : Inputs) (w v : ℕ) (d : TapeStore R B) (hw : d.reg width = w)
    (ht : ThermometerAt d b (d.bufferHead b) w v) :
    ∃ e, (readBlock width value b).Stops inp (d.toCfg 0) (2*w+v+1) (e.toCfg 3) ∧
      e.reg = Function.update (Function.update d.reg width 0) value (d.reg value+v) ∧
      e.bufferHead = Function.update d.bufferHead b (d.bufferHead b+w) ∧
      TapeStore.SamePayload e d := by
  induction w generalizing d v with
  | zero =>
    have hv : v = 0 := by have := ht.1; omega
    refine ⟨d, ?_, ?_, ?_, TapeStore.SamePayload.refl d⟩
    · constructor
      · simpa [hv] using TapeProgram.Exec.one
          (by simp [TapeProgram.halted, readBlock])
          (show (readBlock width value b).step inp (d.toCfg 0) = d.toCfg 3 by
            simp [TapeProgram.step, readBlock, TapeStore.toCfg, hw])
      · simp [TapeProgram.halted, readBlock]
    · rw [show Function.update d.reg width 0 = d.reg by simp [← hw]]
      simp [hv]
    · simp
  | succ w ih =>
    let d₁ := readTickStore width value b d
    have hd₁ : d₁.reg width = w := by
      rw [readTick_reg width value hne]
      simp [Function.update_of_ne hne, hw]
    have hh : d₁.bufferHead b = d.bufferHead b+1 := by
      rw [readTick_head]
      simp
    have hp := readTick_payload width value b d
    have ht₁ := ht.tail hp hh
    obtain ⟨e, he, her, heh, hep⟩ := ih (v-1) d₁ hd₁ ht₁
    have hδ : readDelta d b+(v-1) = v := by
      have hfirst := ht.2 0 (by omega)
      simp only [Nat.add_zero] at hfirst
      cases v with
      | zero => simp only [readDelta, hfirst, Nat.lt_irrefl, if_false, Nat.zero_sub, Nat.add_zero]; decide
      | succ v => simp only [readDelta, hfirst, Nat.zero_lt_succ, if_true, Nat.add_sub_cancel]; omega
    refine ⟨e, ?_, ?_, ?_, hep.trans hp⟩
    · constructor
      · have hprefix := readTick_exec width value hne b inp d (by omega)
        have h := hprefix.trans he.exec
        convert h using 1 <;> first | rfl | omega
      · exact he.halted
    · rw [her, readTick_reg width value hne]
      funext j
      by_cases hv : j = value
      · subst j
        simp only [Function.update_self]
        omega
      · by_cases hw' : j = width
        · subst j
          simp [Function.update, hne, Ne.symm hne]
        · simp [Function.update, hv, hw']
    · rw [heh, readTick_head]
      simp [Function.update_idem, Nat.add_assoc, Nat.add_comm]









 theorem seekEntry_stops (offset : Fin R) (b : Fin B) (inp : Inputs)
    (i w : ℕ) (d : TapeStore R B) (ho : d.reg offset = entryOffset i w)
    (hm : Marked d b) :
    ∃ e, (seekEntry offset b).Stops inp (d.toCfg (seekEntry (R := R) offset b).entry)
      (d.bufferHead b+2*entryOffset i w+3) e ∧
      e.reg = Function.update d.reg offset 0 ∧
      e.bufferHead = Function.update d.bufferHead b (entryOffset i w) ∧
      TapeStore.SamePayload e.store d := by
  obtain ⟨d₁, h₁, hr₁, hh₁, hp₁⟩ := reset_stops b inp (d.bufferHead b) d rfl hm
  have ho₁ : d₁.reg offset = entryOffset i w := by rw [hr₁]; exact ho
  obtain ⟨e, h₂, hr₂, hh₂, hp₂⟩ := seekRight_stops offset b inp (entryOffset i w) d₁ ho₁
  have hall := h₁.seq h₂
  refine ⟨(e.toCfg (2 : Fin 3)).mapPC (TapeProgram.rightLabel 2), ?_, ?_, ?_, hp₂.trans hp₁⟩
  · convert hall using 1 <;> first | rfl | omega
  · simpa [hr₁] using hr₂
  · change e.bufferHead = _
    rw [hh₂, hh₁]
    simp [Function.update_idem]







 theorem ThermometerAt.of_payload {d e : TapeStore R B} {b : Fin B} {start w v : ℕ}
    (h : ThermometerAt d b start w v) (hp : TapeStore.SamePayload e d) :
    ThermometerAt e b start w v := by
  refine ⟨h.1, ?_⟩
  intro j hj
  rw [hp.symbol]
  exact h.2 j hj








 theorem positionEntry_stops (index width offset tmp count : Fin R)
    (hio : index ≠ offset) (hit : index ≠ tmp) (hic : index ≠ count)
    (hwo : width ≠ offset) (hwt : width ≠ tmp) (hwc : width ≠ count)
    (hot : offset ≠ tmp) (hoc : offset ≠ count) (htc : tmp ≠ count)
    (b : Fin B) (inp : Inputs) (d : TapeStore R B) (hm : Marked d b) :
    ∃ t e, t ≤ d.reg offset+d.reg count+d.reg tmp+5*d.reg width+
        d.reg width*(5*d.reg index+7)+11 + d.bufferHead b+
        2*entryOffset (d.reg index) (d.reg width)+6 ∧
      (positionEntry index width offset tmp count b).Stops inp
        (d.toCfg (positionEntry index width offset tmp count b).entry) t e ∧
      e.reg = (((d.setReg offset 0).setReg tmp 0).setReg count 0).reg ∧
      e.bufferHead = Function.update d.bufferHead b (entryOffset (d.reg index) (d.reg width)) ∧
      TapeStore.SamePayload e.store d := by
  obtain ⟨t, c, ht, hc, hcs⟩ := UnaryArithmetic.multiply_stops index width offset tmp count
    hio hit hic hwo hwt hwc hot hoc htc inp d
  have ho : c.reg offset = d.reg index*d.reg width := by
    change c.store.reg offset = _
    rw [hcs]
    simp [UnaryArithmetic.multiplyStore, TapeStore.setReg, hot, hoc]
  let d₂ := c.store.setReg offset (c.reg offset+1)
  have hinc := TapeMacros.increment_stops offset inp c.store
  have ho₂ : d₂.reg offset = entryOffset (d.reg index) (d.reg width) := by
    simp [d₂, TapeStore.setReg, ho, entryOffset, Nat.add_comm]
  have hheads : d₂.bufferHead = d.bufferHead := by
    change c.store.bufferHead = d.bufferHead
    rw [hcs]
    rfl
  have hpMul : TapeStore.SamePayload c.store d := by
    rw [hcs]
    exact (TapeStore.setReg_payload _ count 0).trans
      ((TapeStore.setReg_payload _ tmp 0).trans
        (TapeStore.setReg_payload d offset (d.reg index*d.reg width)))
  have hp₂ : TapeStore.SamePayload d₂ d :=
    (TapeStore.setReg_payload c.store offset (c.reg offset+1)).trans hpMul
  have hm₂ : Marked d₂ b := by
    constructor
    · rw [hp₂.symbol]
      exact hm.1
    · intro k hk hkh
      rw [hp₂.symbol]
      exact hm.2 k hk (by simpa [hheads] using hkh)
  obtain ⟨e, hseek, her, heh, hep⟩ := seekEntry_stops offset b inp
    (d.reg index) (d.reg width) d₂ ho₂ hm₂
  have hall := (hc.seq hinc).seq hseek
  refine ⟨(t+1+1)+1+(d₂.bufferHead b+2*entryOffset (d.reg index) (d.reg width)+3),
    e.mapPC (TapeProgram.rightLabel 26), ?_, ?_, ?_, ?_, hep.trans hp₂⟩
  · rw [hheads]
    omega
  · convert hall using 1 <;> rfl
  · change e.reg = _
    rw [her]
    change Function.update d₂.reg offset 0 = _
    simp only [d₂, TapeStore.setReg, Function.update_idem]
    change Function.update c.store.reg offset 0 = _
    rw [hcs]
    simp only [UnaryArithmetic.multiplyStore, TapeStore.setReg]
    funext j
    by_cases ho' : j = offset
    · subst j
      simp [Function.update, hot, hoc, htc]
    · by_cases ht' : j = tmp
      · subst j
        simp [Function.update, hot, hoc, htc, Ne.symm hot, Ne.symm hoc, Ne.symm htc]
      · by_cases hc' : j = count
        · subst j
          simp [Function.update, hot, hoc, htc, Ne.symm hot, Ne.symm hoc, Ne.symm htc]
        · simp [Function.update, ho', ht', hc']
  · simpa [hheads] using heh

 































 theorem entryAccessBound_le (d : TapeStore R B) (index width offset tmp count : Fin R)
    (b : Fin B) (M : ℕ) (hi : d.reg index ≤ M) (hw : d.reg width ≤ M)
    (ho : d.reg offset ≤ M) (ht : d.reg tmp ≤ M) (hc : d.reg count ≤ M)
    (hh : d.bufferHead b ≤ M) : entryAccessBound d index width offset tmp count b ≤ 50*(M+1)^2 := by
  have hp : d.reg index*d.reg width ≤ M*M := Nat.mul_le_mul hi hw
  have hq : d.reg width*(5*d.reg index+7) ≤ M*(5*M+7) :=
    Nat.mul_le_mul hw (by omega)
  unfold entryAccessBound positionBound entryOffset
  nlinarith






 theorem readEntry_stops (index width offset tmp count value : Fin R)
    (hio : index ≠ offset) (hit : index ≠ tmp) (hic : index ≠ count)
    (hwo : width ≠ offset) (hwt : width ≠ tmp) (hwc : width ≠ count)
    (hot : offset ≠ tmp) (hoc : offset ≠ count) (htc : tmp ≠ count)
    (hwv : width ≠ value) (hvo : value ≠ offset) (hvt : value ≠ tmp) (hvc : value ≠ count)
    (b : Fin B) (inp : Inputs) (d : TapeStore R B) (hm : Marked d b)
    (hv : d.reg value = 0) (v : ℕ)
    (hblock : ThermometerAt d b (entryOffset (d.reg index) (d.reg width)) (d.reg width) v) :
    ∃ t e, t ≤ entryAccessBound d index width offset tmp count b ∧
      (readEntry index width offset tmp count value b).Stops inp
        (d.toCfg (readEntry index width offset tmp count value b).entry) t e ∧
      e.reg = Function.update (Function.update
        (((d.setReg offset 0).setReg tmp 0).setReg count 0).reg width 0) value v ∧
      e.bufferHead = Function.update d.bufferHead b
        (entryOffset (d.reg index) (d.reg width)+d.reg width) ∧
      TapeStore.SamePayload e.store d := by
  obtain ⟨t, c, ht, hc, hcr, hch, hcp⟩ := positionEntry_stops index width offset tmp count
    hio hit hic hwo hwt hwc hot hoc htc b inp d hm
  have hcwidth : c.reg width = d.reg width := by
    rw [hcr]
    simp [TapeStore.setReg, hwo, hwt, hwc]
  have hcvalue : c.reg value = 0 := by
    rw [hcr]
    simp [TapeStore.setReg, hvo, hvt, hvc, hv]
  have hchead : c.bufferHead b = entryOffset (d.reg index) (d.reg width) := by
    rw [hch]
    simp
  have hct : ThermometerAt c.store b (c.bufferHead b) (d.reg width) v := by
    rw [hchead]
    exact hblock.of_payload hcp
  obtain ⟨e, he, her, heh, hep⟩ := readBlock_stops width value hwv b inp
    (d.reg width) v c.store hcwidth hct
  have hall := hc.seq he
  refine ⟨t+1+(2*d.reg width+v+1), (e.toCfg (3 : Fin 4)).mapPC (TapeProgram.rightLabel 31),
    ?_, ?_, ?_, ?_, hep.trans hcp⟩
  · have := hblock.1
    change t ≤ positionBound d index width offset tmp count b at ht
    unfold entryAccessBound
    omega
  · convert hall using 1 <;> rfl
  · change e.reg = _
    simpa [hcr, hcvalue] using her
  · change e.bufferHead = _
    rw [heh]
    change Function.update c.bufferHead b (c.bufferHead b+d.reg width) = _
    rw [hch]
    simp [Function.update_idem]















 theorem writeEntry_stops (index width offset tmp count value : Fin R)
    (hio : index ≠ offset) (hit : index ≠ tmp) (hic : index ≠ count)
    (hwo : width ≠ offset) (hwt : width ≠ tmp) (hwc : width ≠ count)
    (hot : offset ≠ tmp) (hoc : offset ≠ count) (htc : tmp ≠ count)
    (hvw : value ≠ width) (hvo : value ≠ offset) (hvt : value ≠ tmp) (hvc : value ≠ count)
    (b : Fin B) (inp : Inputs) (d : TapeStore R B) (hm : Marked d b)
    (hv : d.reg value ≤ d.reg width) :
    ∃ t e, t ≤ entryAccessBound d index width offset tmp count b ∧
      (writeEntry index width offset tmp count value b).Stops inp
        (d.toCfg (writeEntry index width offset tmp count value b).entry) t e ∧
      e.reg = (((((d.setReg offset 0).setReg tmp 0).setReg count 0).setReg value 0).setReg width 0).reg ∧
      EntryWritten d e.store b (entryOffset (d.reg index) (d.reg width)) (d.reg width) (d.reg value) := by
  obtain ⟨t, c, ht, hc, hcr, hch, hcp⟩ := positionEntry_stops index width offset tmp count
    hio hit hic hwo hwt hwc hot hoc htc b inp d hm
  have hcwidth : c.reg width = d.reg width := by
    rw [hcr]
    simp [TapeStore.setReg, hwo, hwt, hwc]
  have hcvalue : c.reg value = d.reg value := by
    rw [hcr]
    simp [TapeStore.setReg, hvo, hvt, hvc]
  have hchead : c.bufferHead b = entryOffset (d.reg index) (d.reg width) := by
    rw [hch]
    simp
  obtain ⟨e, he, hes⟩ := writeBlock_stops value width hvw b inp
    (d.reg value) (d.reg width) c.store hcvalue hcwidth hv
  have hall := hc.seq he
  refine ⟨t+1+(2*d.reg width+d.reg value+3), e.mapPC (TapeProgram.rightLabel 31), ?_, ?_, ?_, ?_⟩
  · change t ≤ positionBound d index width offset tmp count b at ht
    unfold entryAccessBound
    omega
  · convert hall using 1 <;> rfl
  · change e.store.reg = _
    rw [hes, writeBlockStore_reg]
    change Function.update (Function.update c.reg value 0) width 0 = _
    rw [hcr]
    rfl
  · change EntryWritten d e.store b _ _ _
    rw [hes]
    constructor
    · rw [writeBlockStore_roHead]
      exact hcp.roHead
    · rw [writeBlockStore_output]
      exact hcp.output
    · rw [writeBlockStore_head value width b (d.reg value) (d.reg width) c.store hv]
      change Function.update c.bufferHead b (c.bufferHead b+d.reg width) = _
      rw [hch]
      simp [Function.update_idem]
    · intro f k
      rw [writeBlockStore_symbol value width b (d.reg value) (d.reg width) c.store hv]
      have hcsh : c.store.bufferHead b = entryOffset (d.reg index) (d.reg width) := hchead
      rw [hcsh, hcp.symbol]







 theorem BottomMarked.marked {d : TapeStore R B} {b : Fin B} (h : BottomMarked d b) :
    Marked d b := ⟨h.1, fun k hk _ => h.2 k hk⟩

 theorem BottomMarked.of_payload {d e : TapeStore R B} {b : Fin B}
    (h : BottomMarked d b) (hp : TapeStore.SamePayload e d) : BottomMarked e b := by
  constructor
  · rw [hp.symbol]
    exact h.1
  · intro k hk
    rw [hp.symbol]
    exact h.2 k hk

 theorem EntryWritten.bottomMarked {d e : TapeStore R B} {b : Fin B} {start w v : ℕ}
    (h : EntryWritten d e b start w v) (hs : 0 < start) (hm : BottomMarked d b) :
    BottomMarked e b := by
  constructor
  · rw [h.symbol]
    have hn : ¬ start ≤ 0 := by omega
    have hout : ¬(b = b ∧ start ≤ 0 ∧ 0 < start+w) := by omega
    rw [if_neg hout]
    exact hm.1
  · intro k hk
    rw [h.symbol]
    split_ifs <;> first | decide | exact hm.2 k hk




 














/-- A checked physical overwrite updates exactly one logical table entry. -/
 theorem EntryWritten.table {N : ℕ} {d e : TapeStore R B} {b : Fin B} {w v : ℕ}
    {a : Fin N → ℕ} {i : Fin N}
    (h : EntryWritten d e b (entryOffset i.val w) w v) (hv : v ≤ w)
    (ht : ThermometerTable d b w a) :
    ThermometerTable e b w (Function.update a i v) := by
  intro j
  by_cases hji : j = i
  · subst j
    refine ⟨by simpa using hv, ?_⟩
    intro k hk
    rw [h.symbol]
    have h₁ : entryOffset i.val w ≤ entryOffset i.val w+k := by omega
    have h₂ : entryOffset i.val w+k < entryOffset i.val w+w := by omega
    have h₃ : entryOffset i.val w+k < entryOffset i.val w+v ↔ k < v := by omega
    simp [h₁, h₂, h₃]
  · refine ⟨?_, ?_⟩
    · simpa [Function.update_of_ne hji] using (ht j).1
    · intro k hk
      rw [h.symbol]
      have hne : j.val ≠ i.val := by intro he; exact hji (Fin.ext he)
      have hn : ¬(entryOffset i.val w ≤ entryOffset j.val w+k ∧
          entryOffset j.val w+k < entryOffset i.val w+w) := by
        intro hoverlap
        unfold entryOffset at hoverlap
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hle : (j.val+1)*w ≤ i.val*w := Nat.mul_le_mul_right w (by omega)
          nlinarith
        · have hle : (i.val+1)*w ≤ j.val*w := Nat.mul_le_mul_right w (by omega)
          nlinarith
      simp only [true_and, if_neg hn, Function.update_of_ne hji]
      exact (ht j).2 k hk




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


section FlattenModule17


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}



































































































































































































































































end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule17


section FlattenModule18


set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch
































































end ExpandingCodes.PolynomialStretch

end FlattenModule18


section FlattenModule19



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch






























































end ExpandingCodes.PolynomialStretch

end FlattenModule19


section FlattenModule20


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch





































































































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













 














 


























 












 


































 

































end RandomBits
end ExpandingCodes.Computation

end FlattenModule21


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


section FlattenModule39



set_option autoImplicit false
open Filter Topology

namespace ExpandingCodes.PolynomialStretch















































































































































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







































end Mean







































































































































end ExpandingCodes.PolynomialStretch

end FlattenModule43


section FlattenModule44



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

































































end ExpandingCodes.PolynomialStretch

end FlattenModule44


section FlattenModule45




set_option autoImplicit false
open scoped Classical BigOperators Topology
open Filter

namespace ExpandingCodes.PolynomialStretch










































































































end ExpandingCodes.PolynomialStretch

end FlattenModule45


section FlattenModule46



set_option autoImplicit false
set_option linter.style.haveILetI false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch
namespace SamplerTables
























































































































































































































end SamplerTables
end ExpandingCodes.PolynomialStretch

end FlattenModule46


section FlattenModule47



set_option autoImplicit false

namespace ExpandingCodes.Computation







namespace PolynomialBound
variable {f g : ℕ → ℕ}




















































end PolynomialBound
end ExpandingCodes.Computation

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation










































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


section FlattenModule52







set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace SamplerEvaluation
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}

























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































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





theorem pivot_some {m n : ℕ} {A : Table F m n} {p : Fin m × Fin n}
    (h : pivot A = some p) : toMatrix A p.1 p.2 ≠ 0 := by
  have := List.find?_some h
  simpa using this

theorem pivot_none {m n : ℕ} {A : Table F m n}
    (h : pivot A = none) : toMatrix A = 0 := by
  ext i j
  have hh := List.find?_eq_none.mp h (i,j) (mem_cells (i,j))
  simpa using hh












































theorem scan_result {m n : ℕ} (A : Table F m n) (ps : List (Fin m × Fin n)) :
    (scan A ps).1 = ps.find? (fun p => toMatrix A p.1 p.2 != 0) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      cases hb : (toMatrix A p.1 p.2 != 0) <;> simp [scan, List.find?, hb, ih]























def Work.total (w : Work) : ℕ :=
  w.comparisons+w.inverses+w.arithmetic+w.reads+w.writes+w.enumerated






@[simp] theorem Work.total_add (a b : Work) :
    (a.add b).total = a.total + b.total := by
  simp [Work.total, Work.add]; omega



















theorem run_rank {m n : ℕ} (A : Table F m n) : (run A).1 = rank A := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [run, rank]
      have hs : (scan A (cells (m+1) (n+1))).1 = pivot A := scan_result _ _
      rw [hs]
      split
      · rfl
      · simp only [ih]











































end ExpandingCodes.Computation.Gaussian

end FlattenModule54

/-! Inlined whole module: ExpandingCodes.Computation.GaussianCorrectness -/
section FlattenModule55







set_option autoImplicit false

namespace ExpandingCodes.Computation.Gaussian

open Matrix Module LinearMap
open scoped Matrix

variable {F : Type*} [Field F]











/-- Direct-sum rank identity used to discharge exactly one Gaussian pivot. -/
theorem rank_fromBlocks_zero {m n o p : Type*}
    [Fintype m] [Fintype n] [Fintype o] [Fintype p]
    (A : Matrix m n F) (D : Matrix o p F) :
    (Matrix.fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  let e := LinearEquiv.sumArrowLequivProdArrow m o F F
  let f := LinearEquiv.sumArrowLequivProdArrow n p F F
  have hcomp : e.toLinearMap.comp (Matrix.fromBlocks A 0 0 D).mulVecLin =
      (A.mulVecLin.prodMap D.mulVecLin).comp f.toLinearMap := by
    ext v i <;> simp [e, f, Matrix.fromBlocks_mulVec] <;> rfl
  have hr : ((Matrix.fromBlocks A 0 0 D).mulVecLin.range).map e.toLinearMap =
      A.mulVecLin.range.prod D.mulVecLin.range := by
    rw [← LinearMap.range_comp, hcomp, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, LinearMap.range_prodMap]
  calc
    (Matrix.fromBlocks A 0 0 D).rank =
        finrank F (((Matrix.fromBlocks A 0 0 D).mulVecLin.range).map e.toLinearMap) :=
      (e.finrank_map_eq _).symm
    _ = finrank F (A.mulVecLin.range.prod D.mulVecLin.range) := by rw [hr]
    _ = finrank F (A.mulVecLin.range × D.mulVecLin.range) :=
      (prodSubmoduleEquiv _ _).finrank_eq
    _ = A.rank + D.rank := Module.finrank_prod

/-- Invertible block factors implement Gaussian elimination without changing
rank. This is a proof identity, not an algorithm choosing certificates. -/
theorem rank_fromBlocks_schur {m n o : Type*}
    [Fintype m] [Fintype n] [Fintype o]
    [DecidableEq m] [DecidableEq n] [DecidableEq o]
    (A : Matrix m m F) (B : Matrix m n F) (C : Matrix o m F)
    (D : Matrix o n F) [Invertible A] :
    (Matrix.fromBlocks A B C D).rank = A.rank + (D - C * ⅟A * B).rank := by
  let L := Matrix.fromBlocks (1 : Matrix m m F) 0 (C * ⅟A) (1 : Matrix o o F)
  let U := Matrix.fromBlocks (1 : Matrix m m F) (⅟A * B) 0 (1 : Matrix n n F)
  have hL : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det L).mp (by
    dsimp [L]
    rw [Matrix.isUnit_fromBlocks_zero₁₂]
    exact ⟨isUnit_one, isUnit_one⟩)
  have hU : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp (by
    dsimp [U]
    rw [Matrix.isUnit_fromBlocks_zero₂₁]
    exact ⟨isUnit_one, isUnit_one⟩)
  rw [Matrix.fromBlocks_eq_of_invertible₁₁ A B C D]
  change ((L * Matrix.fromBlocks A 0 0 (D - C * ⅟A * B)) * U).rank = _
  rw [Matrix.rank_mul_eq_left_of_isUnit_det U _ hU,
    Matrix.rank_mul_eq_right_of_isUnit_det L _ hL, rank_fromBlocks_zero]







@[simp] theorem pivotEquiv_inl {m : ℕ} (p : Fin (m+1)) (u : PUnit.{1}) :
    pivotEquiv p (Sum.inl u) = p := by
  simp [pivotEquiv]

@[simp] theorem pivotEquiv_inr {m : ℕ} (p : Fin (m+1)) (i : Fin m) :
    pivotEquiv p (Sum.inr i) = p.succAbove i := by
  simp [pivotEquiv]

/-- A nonzero scalar pivot contributes exactly one to rank; the remaining
rank is the rank of the concretely computed Schur complement. -/
theorem rank_eq_schur_add_one [DecidableEq F] {m n : ℕ}
    (T : Table F (m+1) (n+1)) (p : Fin (m+1) × Fin (n+1))
    (hp : toMatrix T p.1 p.2 ≠ 0) :
    (toMatrix T).rank = (toMatrix (schur T p)).rank + 1 := by
  let M := toMatrix T
  let A : Matrix PUnit.{1} PUnit.{1} F := fun _ _ => M p.1 p.2
  let B : Matrix PUnit.{1} (Fin n) F := fun _ j => M p.1 (p.2.succAbove j)
  let C : Matrix (Fin m) PUnit.{1} F := fun i _ => M (p.1.succAbove i) p.2
  let D : Matrix (Fin m) (Fin n) F :=
    fun i j => M (p.1.succAbove i) (p.2.succAbove j)
  let : Invertible A := {
    invOf := fun _ _ => (M p.1 p.2)⁻¹
    invOf_mul_self := by
      ext i j
      change (∑ _ : PUnit.{1}, (M p.1 p.2)⁻¹ * M p.1 p.2) = _
      simp [M, hp]
    mul_invOf_self := by
      ext i j
      change (∑ _ : PUnit.{1}, M p.1 p.2 * (M p.1 p.2)⁻¹) = _
      simp [M, hp] }
  have hA : A.rank = 1 := by
    simpa using Matrix.rank_of_isUnit A (isUnit_of_invertible A)
  have hM : M.submatrix (pivotEquiv p.1) (pivotEquiv p.2) =
      Matrix.fromBlocks A B C D := by
    ext (i | i) (j | j) <;> simp [Matrix.submatrix_apply, Matrix.fromBlocks, A, B, C, D]
  have hS : D - C * ⅟A * B = toMatrix (schur T p) := by
    have hi : ⅟A = (fun _ _ => (M p.1 p.2)⁻¹ : Matrix PUnit.{1} PUnit.{1} F) := rfl
    rw [hi]
    ext i j
    change D i j - ∑ k : PUnit.{1}, (∑ l : PUnit.{1}, C i l * (M p.1 p.2)⁻¹) * B k j = _
    simp [schur, B, C, D, M, toMatrix, ofMatrix]
  calc
    (toMatrix T).rank = (M.submatrix (pivotEquiv p.1) (pivotEquiv p.2)).rank :=
      (Matrix.rank_submatrix M _ _).symm
    _ = (Matrix.fromBlocks A B C D).rank := by rw [hM]
    _ = A.rank + (D - C * ⅟A * B).rank := rank_fromBlocks_schur A B C D
    _ = (toMatrix (schur T p)).rank + 1 := by rw [hA, hS, Nat.add_comm]

/-- Exact correctness of the deterministic pivot-count algorithm. -/
theorem rank_correct [DecidableEq F] {m n : ℕ} (T : Table F m n) :
    rank T = (toMatrix T).rank := by
  induction m generalizing n with
  | zero =>
    have hz : toMatrix T = 0 := by ext i; exact Fin.elim0 i
    simp [rank, hz]
  | succ m ih =>
    cases n with
    | zero =>
      have hz : toMatrix T = 0 := by ext i j; exact Fin.elim0 j
      simp [rank, hz]
    | succ n =>
      simp only [rank]
      split
      next h => simp [pivot_none h]
      next p h =>
        rw [ih, rank_eq_schur_add_one T p (pivot_some h)]



theorem run_correct [DecidableEq F] {m n : ℕ} (T : Table F m n) :
    (run T).1 = (toMatrix T).rank :=
  (run_rank T).trans (rank_correct T)



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

theorem nonzero_decode (h : Interpretation O decode) (a : α) :
    (a != O.zero) = (decode a != 0) := by
  by_cases ha : a = O.zero
  · simp [ha, h.zero]
  · have hd : decode a ≠ 0 := by
      intro he
      exact ha (h.injective (he.trans h.zero.symm))
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne]
    exact ⟨fun _ => hd, fun _ => ha⟩

theorem scan_decode (h : Interpretation O decode) {m n : ℕ}
    (A : Table α m n) (ps : List (Fin m × Fin n)) :
    scan O A ps = Gaussian.scan (mapTable decode A) ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [scan, Gaussian.scan, toMatrix_mapTable, nonzero_decode h, ih]

theorem schur_decode (h : Interpretation O decode) {m n : ℕ}
    (A : Table α (m+1) (n+1)) (p : Fin (m+1) × Fin (n+1)) :
    mapTable decode (schur O A p) = Gaussian.schur (mapTable decode A) p := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [mapTable, schur, Gaussian.schur, toMatrix, ofMatrix, h.sub, h.mul, h.inv]

/-- An operation-preserving map commutes with every search, pivot, arithmetic
entry and resource counter. The algebraic rank proof is reused unchanged. -/
theorem run_decode (h : Interpretation O decode) {m n : ℕ} (A : Table α m n) :
    run O A = Gaussian.run (mapTable decode A) := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [run, Gaussian.run, scan_decode h]
      cases hs : (Gaussian.scan (mapTable decode A) (cells (m+1) (n+1))).1 with
      | none => rfl
      | some p => simp only [ih, schur_decode h]

theorem run_correct (h : Interpretation O decode) {m n : ℕ} (A : Table α m n) :
    (run O A).1 = (toMatrix (mapTable decode A)).rank := by
  rw [run_decode h, Gaussian.run_correct]






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

theorem fullEvaluationMatrix_bad {d n : ℕ} (g : Geometry d n)
    (a : Fin d → Fin (Fintype.card g.F))
    (ha : ¬ (∑ i, (a i).val) ≤ auxiliaryDegree (Fintype.card g.F) d)
    (z : Fin (rowCount d n)) : fullEvaluationMatrix g a z = 0 := by
  simp [fullEvaluationMatrix, ha]






/-- Restricting a matrix to its possibly nonzero rows and columns preserves
rank, with the omitted rows and columns explicitly required to be zero. -/
theorem rank_eq_subtype_restriction {F I : Type*} [Field F] [Fintype I]
    (p : I → Prop) [DecidablePred p] (M : Matrix I I F)
    (hrow : ∀ i, ¬p i → ∀ j, M i j = 0)
    (hcol : ∀ j, ¬p j → ∀ i, M i j = 0) :
    M.rank = (M.submatrix (Subtype.val : {i // p i} → I)
      (Subtype.val : {i // p i} → I)).rank := by
  classical
  let e := Equiv.sumCompl p
  have h : M.submatrix e e = Matrix.fromBlocks
      (M.submatrix (Subtype.val : {i // p i} → I)
        (Subtype.val : {i // p i} → I)) 0 0 0 := by
    ext (i | i) (j | j)
    · rfl
    · exact hcol j.1 j.2 i.1
    · exact hrow i.1 i.2 j.1
    · exact hrow i.1 i.2 j.1
  rw [← Matrix.rank_submatrix M e e, h,
    Computation.Gaussian.rank_fromBlocks_zero, Matrix.rank_zero, Nat.add_zero]

theorem fullTestMatrix_restriction {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) :
    (fullTestMatrix g y).submatrix
      (Subtype.val : Monomials g.F d (auxiliaryDegree (Fintype.card g.F) d) → _)
      Subtype.val = testMatrix g y := by
  classical
  ext a b
  simp only [fullTestMatrix, testMatrix, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.diagonal_apply]
  simp only [fullEvaluationMatrix_good]

/-- Exact bridge from the finite rectangular enumeration used by the algorithm
to the mission's immutable canonical test matrix. -/
theorem fullTestMatrix_rank {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) :
    (fullTestMatrix g y).rank = (testMatrix g y).rank := by
  classical
  rw [← fullTestMatrix_restriction g y]
  apply rank_eq_subtype_restriction
    (fun a : Fin d → Fin (Fintype.card g.F) =>
      (∑ i, (a i).val) ≤ auxiliaryDegree (Fintype.card g.F) d)
    (fullTestMatrix g y)
  · intro a ha b
    simp [fullTestMatrix, Matrix.mul_apply, fullEvaluationMatrix_bad g a ha]
  · intro b hb a
    simp [fullTestMatrix, Matrix.mul_apply, Matrix.transpose_apply,
      fullEvaluationMatrix_bad g b hb]





































































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

theorem product_decode (h : Interpretation O decode) (xs : List (α × ℕ)) :
    decode (product O xs).1 = (xs.map (fun x => decode x.1)).prod := by
  induction xs with
  | nil => exact h.one
  | cons a as ih => simp [product, h.mul, ih]

theorem sum_decode (h : Interpretation O decode) (xs : List (α × ℕ)) :
    decode (sum O xs).1 = (xs.map (fun x => decode x.1)).sum := by
  induction xs with
  | nil => exact h.zero
  | cons a as ih => simp [sum, h.add, ih]
























theorem evaluation_decode {q d : ℕ} {O : Operations (Fin q)} {f : Fin q → F}
    (h : Interpretation O f) (R : ℕ) (a z : Fin (q^d)) :
    f (evaluation O R a z).1 =
      if (∑ i, (digits q d a i).val) ≤ R then
        ∏ i, (f (digits q d z i)) ^ (digits q d a i).val else 0 := by
  unfold evaluation
  split
  · simp [product_decode h, List.map_ofFn, power_decode h, List.prod_ofFn]
  · exact h.zero






















































theorem entry_decode {q d : ℕ} {O : Operations (Fin q)} {f : Fin q → F}
    (h : Interpretation O f) (R : ℕ) (y : Fin (q^d) → Bool) (a b : Fin (q^d)) :
    f (entry O R y a b).1 = ∑ z,
      if y z then f (evaluation O R a z).1 * f (evaluation O R b z).1 else 0 := by
  unfold entry
  rw [sum_decode h]
  simp only [List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro z _
  unfold term
  split <;> simp_all [h.mul, h.zero]

end ExpandingCodes.Computation.EncodedTester

namespace ExpandingCodes.PolynomialStretch

open Computation EncodedGaussian EncodedTester








@[simp] theorem encodedExponentOrder_val {d n : ℕ} (g : Geometry d n)
    (a : Fin (rowCount d n)) (i : Fin d) :
    (encodedExponentOrder g a i).val = (digits (fieldSize d n) d a i).val := rfl






theorem fullTestMatrix_apply {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) (a b : Fin d → Fin (Fintype.card g.F)) :
    fullTestMatrix g y a b = ∑ z,
      if y z = 0 then 0 else fullEvaluationMatrix g a z * fullEvaluationMatrix g b z := by
  classical
  simp [fullTestMatrix, Matrix.mul_apply, Matrix.diagonal_apply]

theorem binary_evaluation_decode (d n : ℕ) (a z : Fin (rowCount d n)) :
    BinaryField.elements (fieldExponent d n) (fieldExponent_pos d n)
      (evaluation (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n))
        (auxiliaryDegree (fieldSize d n) d) a z).1 =
    fullEvaluationMatrix (binaryGeometry d n) (encodedExponentOrder (binaryGeometry d n) a) z := by
  calc
    _ = if (∑ i, (digits (fieldSize d n) d a i).val) ≤ auxiliaryDegree (fieldSize d n) d
        then ∏ i, (BinaryField.elements (fieldExponent d n) (fieldExponent_pos d n)
          (digits (fieldSize d n) d z i)) ^ (digits (fieldSize d n) d a i).val else 0 :=
      evaluation_decode (BinaryField.indexOperations_interpretation _ _) _ _ _
    _ = _ := by
      simp only [fullEvaluationMatrix, geometry_card, encodedExponentOrder_val,
        binaryGeometry_rowOrder]
      rfl

theorem binaryTestTable_decode (d n : ℕ) (y : Word (rowCount d n)) :
    Gaussian.toMatrix (mapTable
      (BinaryField.elements (fieldExponent d n) (fieldExponent_pos d n))
      (binaryTestTable d n y)) =
    (fullTestMatrix (binaryGeometry d n) y).submatrix
      (encodedExponentOrder (binaryGeometry d n)) (encodedExponentOrder (binaryGeometry d n)) := by
  ext a b
  simp only [rowCount, fieldSize, mapTable, binaryTestTable, table, Gaussian.toMatrix, Gaussian.ofMatrix,
    Vector.getElem_ofFn]
  calc
    _ = ∑ z : Fin (rowCount d n), if decide (y z ≠ 0) then
        BinaryField.elements (fieldExponent d n) (fieldExponent_pos d n)
          (evaluation (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n))
            (auxiliaryDegree (fieldSize d n) d) a z).1 *
        BinaryField.elements (fieldExponent d n) (fieldExponent_pos d n)
          (evaluation (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n))
            (auxiliaryDegree (fieldSize d n) d) b z).1 else 0 :=
      entry_decode (BinaryField.indexOperations_interpretation _ _) _ _ _ _
    _ = _ := by
      simp only [binary_evaluation_decode]
      change _ = fullTestMatrix (binaryGeometry d n) y
        (encodedExponentOrder (binaryGeometry d n) a) (encodedExponentOrder (binaryGeometry d n) b)
      rw [fullTestMatrix_apply]
      simp
      rfl

theorem binaryTestTable_rank (d n : ℕ) (y : Word (rowCount d n)) :
    (EncodedGaussian.run
      (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n))
      (binaryTestTable d n y)).1 = (testMatrix (binaryGeometry d n) y).rank := by
  classical
  calc
    _ = (Gaussian.toMatrix (mapTable
        (BinaryField.elements (fieldExponent d n) (fieldExponent_pos d n))
        (binaryTestTable d n y))).rank :=
      EncodedGaussian.run_correct (BinaryField.indexOperations_interpretation _ _) _
    _ = _ := by
      rw [binaryTestTable_decode]
      exact (Matrix.rank_submatrix _ (encodedExponentOrder (binaryGeometry d n))
        (encodedExponentOrder (binaryGeometry d n))).trans
          (fullTestMatrix_rank (binaryGeometry d n) y)



































end ExpandingCodes.PolynomialStretch

end FlattenModule58


section FlattenModule59




set_option autoImplicit false
open scoped BigOperators

namespace ExpandingCodes.Computation.EncodedSampler

open EncodedGaussian EncodedTester
open ExpandingCodes.PolynomialStretch

variable {q d k b : ℕ}


























































variable {F : Type*} [Field F] {O : Operations (Fin q)} {decode : Fin q → F}













end ExpandingCodes.Computation.EncodedSampler

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation EncodedGaussian EncodedTester


































































































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




















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































namespace Storage






































@[simp] theorem point_val (d k : ℕ) (j : Fin d) : (point d k j).val=80+j.val := rfl
@[simp] theorem countdown_val (d k : ℕ) (j : Fin d) : (countdown d k j).val=80+d+j.val := rfl
@[simp] theorem coefficient_val (d k : ℕ) (j : Fin d) : (coefficient d k j).val=80+2*d+j.val := rfl

end Storage

namespace Storage






















end Storage





































































namespace Storage



















































































































































































end Storage




namespace Storage





















@[simp] theorem pointPairs_length (d k : ℕ) : (pointPairs d k).length=d := by simp [pointPairs]












































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


section FlattenModule71


set_option autoImplicit false
namespace ExpandingCodes.Computation
namespace ParameterPrograms





namespace PolynomialMajorant





















































end PolynomialMajorant















































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














theorem readPost_outside (d : Store) (v : ℕ) (r : Fin 64) (hr : 9 ≤ r.val) :
    (readPost d v).reg r = d.reg r := by
  have h1 : r ≠ 1 := by intro h; subst r; norm_num at hr
  have h3 : r ≠ 3 := by intro h; subst r; norm_num at hr
  have h4 : r ≠ 4 := by intro h; subst r; norm_num at hr
  have h5 : r ≠ 5 := by intro h; subst r; norm_num at hr
  have h6 : r ≠ 6 := by intro h; subst r; norm_num at hr
  simp [readPost, TapeStore.setReg, h1, h3, h4, h5, h6]

theorem readPost_scratch_zero (d : Store) (v : ℕ) (r : Fin 64)
    (hr : r = 1 ∨ r = 3 ∨ r = 4 ∨ r = 5) : (readPost d v).reg r = 0 := by
  rcases hr with rfl | rfl | rfl | rfl <;> simp [readPost,TapeStore.setReg]





/-- Complete physical read with a persistent q register. Copying q and clearing
the accumulator are actual finite source routines, included in the bound. -/
theorem readCurrent_stops (b : Fin 2) (inp : Inputs) (d : Store) (M v : ℕ)
    (hm : BottomMarked d b) (hM : AccessBounded d M) (hh : d.bufferHead b ≤ M)
    (hv : ThermometerAt d b (entryOffset (d.reg 2) (d.reg 0)) (d.reg 0) v) :
    ∃ t e, t ≤ 100*(M+1)^2 ∧
      (readCurrent b).Stops inp (d.toCfg (readCurrent b).entry) t e ∧
      e.reg = (readPost d v).reg ∧
      e.bufferHead = Function.update d.bufferHead b
        (entryOffset (d.reg 2) (d.reg 0)+d.reg 0) ∧
      TapeStore.SamePayload e.store d := by
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops
    (B := 2) (0 : Fin 64) 1 4 (by decide) (by decide) (by decide) inp d
  have hcr : c.reg = ((d.setReg 1 (d.reg 0)).setReg 4 0).reg :=
    congrArg TapeStore.reg hcs
  let d₁ := c.store.setReg 6 0
  have hclear := TapeMacros.clear_stops (6 : Fin 64) inp (c.reg 6) c.store rfl
  have hcp : TapeStore.SamePayload c.store d := by
    rw [hcs]
    exact (TapeStore.setReg_payload _ 4 0).trans
      (TapeStore.setReg_payload d 1 (d.reg 0))
  have hdp : TapeStore.SamePayload d₁ d :=
    (TapeStore.setReg_payload c.store 6 0).trans hcp
  have hdh : d₁.bufferHead = d.bufferHead := by
    change c.store.bufferHead = d.bufferHead
    rw [hcs]
    rfl
  have hd1 : d₁.reg 1 = d.reg 0 := by simp [d₁, hcr, TapeStore.setReg]
  have hd2 : d₁.reg 2 = d.reg 2 := by simp [d₁, hcr, TapeStore.setReg]
  have hdt : ThermometerAt d₁ b (entryOffset (d₁.reg 2) (d₁.reg 1)) (d₁.reg 1) v := by
    rw [hd1, hd2]
    exact hv.of_payload hdp
  obtain ⟨s, e, hs, he, her, heh, hep⟩ := readEntry_stops
    (2 : Fin 64) 1 3 4 5 6 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) b inp d₁
      (hm.of_payload hdp).marked (by simp [d₁, TapeStore.setReg]) v hdt
  have hbound : entryAccessBound d₁ 2 1 3 4 5 b ≤ 50*(M+1)^2 := by
    rcases hM with ⟨h0,h1,h2,h3,h4,h5,h6⟩
    apply entryAccessBound_le d₁ 2 1 3 4 5 b M
    · simpa [d₁, hcr, TapeStore.setReg] using h2
    · simpa [d₁, hcr, TapeStore.setReg] using h0
    · simpa [d₁, hcr, TapeStore.setReg] using h3
    · simp [d₁, hcr, TapeStore.setReg]
    · simpa [d₁, hcr, TapeStore.setReg] using h5
    · simpa [hdh] using hh
  have hall := hc.seq (hclear.seq he)
  refine ⟨_, _, ?_, hall, ?_, ?_, hep.trans hdp⟩
  · have hc6 : c.reg 6 = d.reg 6 := by change c.store.reg 6 = _; rw [hcs]; simp [TapeStore.setReg]
    rw [hc6]
    rcases hM with ⟨h0,h1,h2,h3,h4,h5,h6⟩
    nlinarith
  · change e.reg = _
    rw [her]
    simp only [d₁, hcr, readPost, TapeStore.setReg]
    funext r
    by_cases h6 : r = 6
    · subst r; simp
    · by_cases h5 : r = 5
      · subst r; simp
      · by_cases h4 : r = 4
        · subst r; simp
        · by_cases h3 : r = 3
          · subst r; simp
          · by_cases h1 : r = 1
            · subst r; simp
            · simp [Function.update, h1, h3, h4, h5, h6]
  · change e.bufferHead = _
    rw [heh, hd1, hd2, hdh]



section SearchLoop

variable {R B L : ℕ}




















theorem searchLoop_body_active (P : TapeProgram R B L) (remaining value index found : Fin R)
    (j : Fin L) (hj : P.code j ≠ .halt) :
    (searchLoop P remaining value index found).code (TapeProgram.leftLabel 6 j) =
      (P.code j).relabel (TapeProgram.leftLabel 6) := by
  simp only [searchLoop, TapeProgram.leftLabel, Equiv.symm_apply_apply]

theorem searchLoop_body_halt (P : TapeProgram R B L) (remaining value index found : Fin R)
    (j : Fin L) (hj : P.code j = .halt) :
    (searchLoop P remaining value index found).code (TapeProgram.leftLabel 6 j) =
      .jump (searchLabel L 1) := by
  simp [searchLoop, TapeProgram.leftLabel, hj]

@[simp] theorem searchLoop_tail (P : TapeProgram R B L) (remaining value index found : Fin R)
    (k : Fin 6) :
    (searchLoop P remaining value index found).code (searchLabel L k) =
      if k = 0 then .dec remaining (searchLabel L 5) (TapeProgram.leftLabel 6 P.entry)
      else if k = 1 then .dec value (searchLabel L 2) (searchLabel L 3)
      else if k = 2 then .inc index (searchLabel L 0)
      else if k = 3 then .inc value (searchLabel L 4)
      else if k = 4 then .inc found (searchLabel L 5) else .halt := by
  simp [searchLoop, searchLabel, TapeProgram.rightLabel]

theorem searchLoop_zero (P : TapeProgram R B L) (remaining value index found : Fin R)
    (inp : Inputs) (d : TapeStore R B) (hr : d.reg remaining = 0) :
    (searchLoop P remaining value index found).Stops inp (d.toCfg (searchLabel L 0)) 1
      (d.toCfg (searchLabel L 5)) := by
  constructor
  · apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, searchLoop_tail]
    · simp [TapeProgram.step, searchLoop_tail, TapeStore.toCfg, hr]
  · simp [TapeProgram.halted, searchLoop_tail]

theorem searchLoop_header (P : TapeProgram R B L) (remaining value index found : Fin R)
    (inp : Inputs) (d : TapeStore R B) (hr : 0 < d.reg remaining) :
    (searchLoop P remaining value index found).Exec inp (d.toCfg (searchLabel L 0)) 1
      ((TapeProgram.decStore remaining d).toCfg (TapeProgram.leftLabel 6 P.entry)) := by
  apply TapeProgram.Exec.one
  · simp [TapeProgram.halted, searchLoop_tail]
  · simp [TapeProgram.step, searchLoop_tail, TapeStore.toCfg, TapeProgram.decStore, Nat.ne_of_gt hr]

theorem searchLoop_return (P : TapeProgram R B L) (remaining value index found : Fin R)
    (inp : Inputs) (c : TapeCfg R B L) (hc : P.halted c) :
    (searchLoop P remaining value index found).Exec inp (c.mapPC (TapeProgram.leftLabel 6)) 1
      (c.store.toCfg (searchLabel L 1)) := by
  apply TapeProgram.Exec.one
  · change (searchLoop P remaining value index found).code (TapeProgram.leftLabel 6 c.pc) ≠ .halt
    rw [searchLoop_body_halt _ _ _ _ _ _ hc]
    simp
  · simp only [TapeProgram.step, TapeCfg.mapPC]
    rw [searchLoop_body_halt _ _ _ _ _ _ hc]

theorem searchLoop_continue (P : TapeProgram R B L) (remaining value index found : Fin R)
    (inp : Inputs) (d : TapeStore R B) (hr : 0 < d.reg remaining)
    (t : ℕ) (c : TapeCfg R B L)
    (hc : P.Stops inp ((TapeProgram.decStore remaining d).toCfg P.entry) t c)
    (hv : c.reg value = 0) :
    (searchLoop P remaining value index found).Exec inp (d.toCfg (searchLabel L 0)) (t+4)
      ((c.store.setReg index (c.reg index+1)).toCfg (searchLabel L 0)) := by
  have hh := searchLoop_header P remaining value index found inp d hr
  have hb := hc.exec.relabel (TapeProgram.leftLabel 6)
    (searchLoop_body_active P remaining value index found)
  have hreturn := searchLoop_return P remaining value index found inp c hc.halted
  have htest : (searchLoop P remaining value index found).Exec inp
      (c.store.toCfg (searchLabel L 1)) 1 (c.store.toCfg (searchLabel L 2)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, searchLoop_tail]
    · simp [TapeProgram.step, searchLoop_tail, TapeStore.toCfg, hv]
  have hinc : (searchLoop P remaining value index found).Exec inp
      (c.store.toCfg (searchLabel L 2)) 1
      ((c.store.setReg index (c.reg index+1)).toCfg (searchLabel L 0)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, searchLoop_tail]
    · simp [TapeProgram.step, searchLoop_tail, TapeStore.toCfg, TapeStore.setReg]
  convert (((hh.trans hb).trans hreturn).trans htest).trans hinc using 1 <;> first | rfl | omega

theorem searchLoop_found (P : TapeProgram R B L) (remaining value index found : Fin R)
    (inp : Inputs) (d : TapeStore R B) (hr : 0 < d.reg remaining)
    (t : ℕ) (c : TapeCfg R B L)
    (hc : P.Stops inp ((TapeProgram.decStore remaining d).toCfg P.entry) t c)
    (hv : 0 < c.reg value) :
    (searchLoop P remaining value index found).Stops inp (d.toCfg (searchLabel L 0)) (t+5)
      ((c.store.setReg found (c.reg found+1)).toCfg (searchLabel L 5)) := by
  have hh := searchLoop_header P remaining value index found inp d hr
  have hb := hc.exec.relabel (TapeProgram.leftLabel 6)
    (searchLoop_body_active P remaining value index found)
  have hreturn := searchLoop_return P remaining value index found inp c hc.halted
  let d₁ := c.store.setReg value (c.reg value-1)
  have htest : (searchLoop P remaining value index found).Exec inp
      (c.store.toCfg (searchLabel L 1)) 1 (d₁.toCfg (searchLabel L 3)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, searchLoop_tail]
    · simp [TapeProgram.step, searchLoop_tail, TapeStore.toCfg, d₁, TapeStore.setReg, Nat.ne_of_gt hv]
  have hrestore : (searchLoop P remaining value index found).Exec inp
      (d₁.toCfg (searchLabel L 3)) 1 (c.store.toCfg (searchLabel L 4)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, searchLoop_tail]
    · simp [TapeProgram.step, searchLoop_tail, TapeStore.toCfg, d₁, TapeStore.setReg,
        Function.update_idem, Nat.sub_add_cancel hv]
  have hmark : (searchLoop P remaining value index found).Exec inp
      (c.store.toCfg (searchLabel L 4)) 1
      ((c.store.setReg found (c.reg found+1)).toCfg (searchLabel L 5)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, searchLoop_tail]
    · simp [TapeProgram.step, searchLoop_tail, TapeStore.toCfg, TapeStore.setReg]
  constructor
  · convert ((((hh.trans hb).trans hreturn).trans htest).trans hrestore).trans hmark using 1
      <;> first | rfl | omega
  · simp [TapeProgram.halted, searchLoop_tail]

end SearchLoop




























































/-- Uniform physical pivot search. The invariant preserves the whole encoded
matrix while advancing the runtime flat index past exactly the zero entries.
Both code size and register count are independent of q and the cell count. -/
theorem pivotScan_stops (b : Fin 2) (inp : Inputs) (a : ℕ → ℕ)
    (q i n K : ℕ) (d : Store) (hq : q ≤ K) (hi : i+n ≤ K)
    (hr0 : d.reg 0 = q) (hr2 : d.reg 2 = i) (hr6 : d.reg 6 = 0)
    (hr7 : d.reg 7 = n) (hr8 : d.reg 8 = 0)
    (hm : BottomMarked d b) (hb : AccessBounded d ((K+1)^2))
    (hh : d.bufferHead b ≤ (K+1)^2)
    (hblocks : ∀ j, j < n → ThermometerAt d b (entryOffset (i+j) q) q (a (i+j))) :
    ∃ (t : ℕ) (e : Store), t ≤ n*(100*((K+1)^2+1)^2+5)+1 ∧
      (pivotScan b).Stops inp (d.toCfg (searchLabel 48 0)) t (e.toCfg (searchLabel 48 5)) ∧
      ScanOutcome a q i n K b d e := by
  induction n generalizing i d with
  | zero =>
    refine ⟨1, d, by simp, searchLoop_zero (readCurrent b) 7 6 2 8 inp d hr7, ?_⟩
    exact ⟨hr0, hr2, hr6, by simpa [scanResult] using hr8, hb, hh,
      TapeStore.SamePayload.refl d, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => le_rfl, le_rfl⟩
  | succ n ih =>
    let d₀ := TapeProgram.decStore (7 : Fin 64) d
    have hd₀p : TapeStore.SamePayload d₀ d := TapeStore.setReg_payload d 7 (d.reg 7-1)
    have hd₀0 : d₀.reg 0 = q := by simp [d₀, TapeProgram.decStore, hr0]
    have hd₀2 : d₀.reg 2 = i := by simp [d₀, TapeProgram.decStore, hr2]
    have hd₀b : AccessBounded d₀ ((K+1)^2) := by
      simpa [AccessBounded, d₀, TapeProgram.decStore] using hb
    have hblock : ThermometerAt d₀ b (entryOffset (d₀.reg 2) (d₀.reg 0)) (d₀.reg 0) (a i) := by
      rw [hd₀0, hd₀2]
      simpa using (hblocks 0 (by omega)).of_payload hd₀p
    obtain ⟨s, c, hs, hc, hcr, hch, hcp⟩ := readCurrent_stops b inp d₀ ((K+1)^2) (a i)
      (hm.of_payload hd₀p) hd₀b hh hblock
    have hc0 : c.reg 0 = q := by rw [hcr]; simp [readPost, TapeStore.setReg, hd₀0]
    have hc2 : c.reg 2 = i := by rw [hcr]; simp [readPost, TapeStore.setReg, hd₀2]
    have hc6 : c.reg 6 = a i := by rw [hcr]; simp [readPost, TapeStore.setReg]
    have hc7 : c.reg 7 = n := by
      rw [hcr]
      simp [readPost, TapeStore.setReg, d₀, TapeProgram.decStore, hr7]
    have hc8 : c.reg 8 = 0 := by
      rw [hcr]
      simp [readPost, TapeStore.setReg, d₀, TapeProgram.decStore, hr8]
    have hcpd : TapeStore.SamePayload c.store d := hcp.trans hd₀p
    have hK : K ≤ (K+1)^2 := by nlinarith
    have hqK : q ≤ (K+1)^2 := hq.trans hK
    have hiK : i ≤ (K+1)^2 := (by omega : i ≤ K).trans hK
    have haK : a i ≤ (K+1)^2 := hblock.1.trans (by rw [hd₀0]; exact hqK)
    have hcb : AccessBounded c.store ((K+1)^2) := by
      simp [AccessBounded, hcr, readPost, TapeStore.setReg, hd₀0, hd₀2, hqK, hiK, haK]
    have hchead : c.bufferHead b ≤ (K+1)^2 := by
      rw [hch]
      simp only [Function.update_self, hd₀0, hd₀2]
      have hmul : (i+1)*q ≤ K*K := Nat.mul_le_mul (by omega) hq
      unfold entryOffset
      nlinarith
    have hcframe (r : Fin 64) (hr : 9 ≤ r.val) : c.reg r = d.reg r := by
      rw [hcr]
      rw [readPost_outside d₀ (a i) r hr]
      have h7 : r ≠ 7 := by intro h; subst r; norm_num at hr
      simp [d₀, TapeProgram.decStore, h7]
    have hcheadframe (c' : Fin 2) (hne : c' ≠ b) : c.bufferHead c' = d.bufferHead c' := by
      rw [hch]
      simp [Function.update_of_ne hne, d₀, TapeProgram.decStore]
    by_cases hai : a i = 0
    · let d₁ := c.store.setReg 2 (c.reg 2+1)
      have hd₁p : TapeStore.SamePayload d₁ d :=
        (TapeStore.setReg_payload c.store 2 (c.reg 2+1)).trans hcpd
      have hd₁0 : d₁.reg 0 = q := by simp [d₁, TapeStore.setReg, hc0]
      have hd₁2 : d₁.reg 2 = i+1 := by simp [d₁, TapeStore.setReg, hc2]
      have hd₁6 : d₁.reg 6 = 0 := by simp [d₁, TapeStore.setReg, hc6, hai]
      have hd₁7 : d₁.reg 7 = n := by simp [d₁, TapeStore.setReg, hc7]
      have hd₁8 : d₁.reg 8 = 0 := by simp [d₁, TapeStore.setReg, hc8]
      have hd₁b : AccessBounded d₁ ((K+1)^2) := by
        have hi1 : i+1 ≤ (K+1)^2 := (by omega : i+1 ≤ K).trans hK
        simpa [AccessBounded, d₁, TapeStore.setReg, hc2, hiK, hi1] using hcb
      have htail : ∀ j, j < n → ThermometerAt d₁ b
          (entryOffset (i+1+j) q) q (a (i+1+j)) := by
        intro j hj
        have h := (hblocks (j+1) (by omega)).of_payload hd₁p
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      obtain ⟨t, e, ht, he, ho⟩ := ih (i+1) d₁ (by omega) hd₁0 hd₁2 hd₁6 hd₁7 hd₁8
        (hm.of_payload hd₁p) hd₁b hchead htail
      have hcont := searchLoop_continue (readCurrent b) 7 6 2 8 inp d
        (by omega) s c hc (by rw [hc6]; exact hai)
      refine ⟨s+4+t, e, ?_, ⟨hcont.trans he.exec, he.halted⟩, ?_⟩
      · rw [show (n+1)*(100*((K+1)^2+1)^2+5) =
          n*(100*((K+1)^2+1)^2+5)+(100*((K+1)^2+1)^2+5) by ring]
        omega
      · refine ⟨ho.width, ?_, ?_, ?_, ho.bounded, ho.head, ho.payload.trans hd₁p, ?_, ?_, ?_, ?_⟩
        · simpa [scanResult, hai] using ho.index
        · simpa [scanResult, hai] using ho.value
        · simpa [scanResult, hai] using ho.found
        · intro r hr
          rw [ho.outside r hr]
          have hne : r ≠ 2 := by intro h; subst r; norm_num at hr
          simpa [d₁, TapeStore.setReg, hne] using hcframe r hr
        · intro c' hne
          rw [ho.otherHead c' hne]
          exact hcheadframe c' hne
        · intro r hr
          have hr2 : r ≠ 2 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
          have hz : d₁.reg r = 0 := by
            simp only [d₁,TapeStore.setReg,Function.update_of_ne hr2]
            rw [hcr]
            exact readPost_scratch_zero d₀ (a i) r hr
          have hh := ho.scratch r hr
          rw [hz] at hh
          exact hh.trans (Nat.zero_le _)
        · have hh := ho.remaining
          rw [hd₁7] at hh
          rw [hr7]
          omega
    · have hfound := searchLoop_found (readCurrent b) 7 6 2 8 inp d
        (by omega) s c hc (by rw [hc6]; omega)
      let e := c.store.setReg 8 (c.reg 8+1)
      refine ⟨s+5, e, ?_, hfound, ?_⟩
      · rw [show (n+1)*(100*((K+1)^2+1)^2+5) =
          n*(100*((K+1)^2+1)^2+5)+(100*((K+1)^2+1)^2+5) by ring]
        nlinarith
      · refine ⟨?_, ?_, ?_, ?_, ?_, hchead, ?_, ?_, ?_, ?_, ?_⟩
        · simp [e, TapeStore.setReg, hc0]
        · simp [e, TapeStore.setReg, hc2, scanResult, hai]
        · simp [e, TapeStore.setReg, hc6, scanResult, hai]
        · simp [e, TapeStore.setReg, hc8, scanResult, hai]
        · simpa [AccessBounded, e, TapeStore.setReg] using hcb
        · exact (TapeStore.setReg_payload c.store 8 (c.reg 8+1)).trans hcpd
        · intro r hr
          have hne : r ≠ 8 := by intro h; subst r; norm_num at hr
          simpa [e, TapeStore.setReg, hne] using hcframe r hr
        · exact hcheadframe
        · intro r hr
          have hr8 : r ≠ 8 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
          change Function.update c.reg 8 (c.reg 8+1) r ≤ _
          rw [Function.update_of_ne hr8,hcr,readPost_scratch_zero d₀ (a i) r hr]
          exact Nat.zero_le _
        · simp [e,TapeStore.setReg,hc7,hr7]



theorem ScanOutcome.all_bounded {a : ℕ → ℕ} {q i n K M : ℕ} {b : Fin 2} {d e : Store}
    (h : ScanOutcome a q i n K b d e) (hM : 1 ≤ M) (hd : ∀ r,d.reg r ≤ M)
    (hq : q ≤ M) (hi : i+n ≤ M) (hv : ∀ j,j < n → a (i+j) ≤ M) : ∀ r,e.reg r ≤ M := by
  have h0 : e.reg 0 ≤ M := h.width.le.trans hq
  have h2 : e.reg 2 ≤ M := by
    rw [h.index]
    rcases scanResult_spec a i n with hs | hs
    · rw [hs.2.1];exact hi
    · have := hs.2.1;omega
  have h6 : e.reg 6 ≤ M := by
    rw [h.value]
    rcases scanResult_spec a i n with hs | hs
    · rw [hs.1];exact Nat.zero_le M
    · have hj : (scanResult a i n).1-i < n := by have := hs.1;have := hs.2.1;omega
      have hh := hv ((scanResult a i n).1-i) hj
      rw [Nat.add_sub_of_le hs.1] at hh
      exact hs.2.2.1.le.trans hh
  have h7 : e.reg 7 ≤ M := h.remaining.trans (hd 7)
  have h8 : e.reg 8 ≤ M := by
    rw [h.found]
    split <;> omega
  intro r
  fin_cases r <;> first
    | exact h0
    | exact h2
    | exact h6
    | exact h7
    | exact h8
    | exact (h.scratch _ (by decide)).trans (hd _)
    | exact (h.outside _ (by decide)).le.trans (hd _)

theorem pivotScan_table_stops {q m n : ℕ} (b : Fin 2) (inp : Inputs)
    (A : Gaussian.Table (Fin q) m n) (d : Store) (M : ℕ) (hM : 1 ≤ M)
    (hd : ∀ r,d.reg r ≤ M) (hsize : m*n ≤ M)
    (hr0 : d.reg 0 = q) (hr2 : d.reg 2 = 0) (hr6 : d.reg 6 = 0)
    (hr7 : d.reg 7 = m*n) (hr8 : d.reg 8 = 0)
    (hm : BottomMarked d b) (hh : d.bufferHead b ≤ (M+1)^2) (ht : MatrixStored d b A) :
    ∃ (t : ℕ) (e : Store),t ≤ m*n*(100*((M+1)^2+1)^2+5)+1 ∧
      (pivotScan b).Stops inp (d.toCfg (searchLabel 48 0)) t (e.toCfg (searchLabel 48 5)) ∧
      ScanOutcome (flatEntry A) q 0 (m*n) M b d e ∧ (∀ r,e.reg r ≤ M) := by
  have hq : q ≤ M := by rw [← hr0];exact hd 0
  have hb : AccessBounded d ((M+1)^2) := by
    have hMS : M ≤ (M+1)^2 := by nlinarith
    exact ⟨(hd 0).trans hMS,(hd 1).trans hMS,(hd 2).trans hMS,(hd 3).trans hMS,
      (hd 4).trans hMS,(hd 5).trans hMS,(hd 6).trans hMS⟩
  obtain ⟨t,e,htime,hstop,ho⟩ := pivotScan_stops b inp (flatEntry A) q 0 (m*n) M d hq
    (by simpa using hsize) hr0 hr2 hr6 hr7 hr8 hm hb hh (by
      intro j hj
      simpa using ht ⟨j,hj⟩)
  refine ⟨t,e,htime,hstop,ho,ho.all_bounded hM hd hq (by simpa using hsize) ?_⟩
  intro j hj
  rw [Nat.zero_add,flatEntry,dif_pos hj]
  exact (Nat.le_of_lt (Fin.isLt _)).trans hq



















































theorem binary_zeroIndex_val (ell : ℕ) : (PolynomialStretch.BinaryField.zeroIndex ell).val = 0 := by
  rw [PolynomialStretch.BinaryField.zeroIndex, PolynomialStretch.BinaryPolynomial.indexEquiv_inverse_value]
  simp [PolynomialStretch.BinaryField.zero]

/-- Nonzero pivots returned by the physical scan discharge the exact encoded
Schur rank reduction; no pivot certificate is chosen noncomputably. -/
theorem encoded_schur_rank_step {q m n : ℕ} {F : Type*} [Field F] [DecidableEq F]
    {O : EncodedGaussian.Operations (Fin q)} {decode : Fin q → F}
    (h : EncodedGaussian.Interpretation O decode)
    (A : Gaussian.Table (Fin q) (m+1) (n+1)) (p : Fin (m+1) × Fin (n+1))
    (hp : Gaussian.toMatrix A p.1 p.2 ≠ O.zero) :
    (Gaussian.toMatrix (EncodedGaussian.mapTable decode A)).rank =
      (Gaussian.toMatrix (EncodedGaussian.mapTable decode (EncodedGaussian.schur O A p))).rank+1 := by
  rw [EncodedGaussian.schur_decode h]
  apply Gaussian.rank_eq_schur_add_one
  rw [EncodedGaussian.toMatrix_mapTable]
  intro he
  exact hp (h.injective (he.trans h.zero.symm))

theorem high_ne_low (r : Fin 64) (hr : 9 ≤ r.val) (k : Fin 64) (hk : k.val < 9) :
    r ≠ k := by intro h; subst r; omega








theorem fetchPost_bounded (d : Store) (address dest : Fin 64) (v M : ℕ)
    (hM : ∀ r, d.reg r ≤ M) (hv : v ≤ M) :
    ∀ r, (fetchPost d address dest v).reg r ≤ M := by
  intro r
  simp only [fetchPost, readPost, TapeStore.setReg, Function.update_apply]
  split_ifs <;> first | exact hv | exact Nat.zero_le M | exact hM address | exact hM r

/-- Three real finite routines fetch one addressed matrix cell into a scalar
register. Every multiplication, reset and physical traversal is charged. -/
theorem fetch_stops (b : Fin 2) (address dest : Fin 64)
    (ha : 9 ≤ address.val) (hd : 9 ≤ dest.val) (inp : Inputs) (d : Store) (M v : ℕ)
    (hm : BottomMarked d b) (hM : ∀ r, d.reg r ≤ M) (hh : d.bufferHead b ≤ M)
    (hv : ThermometerAt d b (entryOffset (d.reg address) (d.reg 0)) (d.reg 0) v) :
    ∃ t e, t ≤ 120*(M+1)^2 ∧
      (fetch b address dest).Stops inp (d.toCfg (fetch b address dest).entry) t e ∧
      e.reg = (fetchPost d address dest v).reg ∧
      e.bufferHead = Function.update d.bufferHead b
        (entryOffset (d.reg address) (d.reg 0)+d.reg 0) ∧
      TapeStore.SamePayload e.store d := by
  have ha2 : address ≠ 2 := high_ne_low address ha 2 (by decide)
  have ha4 : address ≠ 4 := high_ne_low address ha 4 (by decide)
  have hd1 : dest ≠ 1 := high_ne_low dest hd 1 (by decide)
  have hd2 : dest ≠ 2 := high_ne_low dest hd 2 (by decide)
  have hd3 : dest ≠ 3 := high_ne_low dest hd 3 (by decide)
  have hd4 : dest ≠ 4 := high_ne_low dest hd 4 (by decide)
  have hd5 : dest ≠ 5 := high_ne_low dest hd 5 (by decide)
  have hd6 : dest ≠ 6 := high_ne_low dest hd 6 (by decide)
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops address (2 : Fin 64) 4
    ha2 ha4 (by decide) inp d
  have hcr : c.reg = ((d.setReg 2 (d.reg address)).setReg 4 0).reg := congrArg TapeStore.reg hcs
  have hcp : TapeStore.SamePayload c.store d := by
    rw [hcs]
    exact (TapeStore.setReg_payload _ 4 0).trans (TapeStore.setReg_payload d 2 (d.reg address))
  have hcBound : AccessBounded c.store M := by
    simp [AccessBounded, hcr, TapeStore.setReg, hM]
  have hct : ThermometerAt c.store b (entryOffset (c.reg 2) (c.reg 0)) (c.reg 0) v := by
    have hc2 : c.reg 2 = d.reg address := by rw [hcr]; simp [TapeStore.setReg]
    have hc0 : c.reg 0 = d.reg 0 := by rw [hcr]; simp [TapeStore.setReg]
    rw [hc2, hc0]
    exact hv.of_payload hcp
  obtain ⟨s, f, hs, hf, hfr, hfh, hfp⟩ := readCurrent_stops b inp c.store M v
    (hm.of_payload hcp) hcBound (by rw [hcs]; exact hh) hct
  obtain ⟨e, he, hes⟩ := TapeMacros.copy_stops (6 : Fin 64) dest 4
    (Ne.symm hd6) (by decide) hd4 inp f.store
  have her : e.reg = ((f.store.setReg dest (f.reg 6)).setReg 4 0).reg := congrArg TapeStore.reg hes
  have hfpd : TapeStore.SamePayload f.store d := hfp.trans hcp
  have hep : TapeStore.SamePayload e.store f.store := by
    rw [hes]
    exact (TapeStore.setReg_payload _ 4 0).trans (TapeStore.setReg_payload f.store dest (f.reg 6))
  have hf6 : f.reg 6 = v := by rw [hfr]; simp [readPost, TapeStore.setReg]
  have hf4 : f.reg 4 = 0 := by rw [hfr]; simp [readPost, TapeStore.setReg]
  have hfd : f.reg dest = d.reg dest := by
    rw [hfr]
    simp [readPost, TapeStore.setReg, hcr, hd1, hd2, hd3, hd4, hd5, hd6]
  have hall := hc.seq (hf.seq he)
  refine ⟨_, _, ?_, hall, ?_, ?_, hep.trans hfpd⟩
  · dsimp only [TapeCfg.store]
    rw [hf6, hf4, hfd]
    have hvM := hv.1.trans (hM 0)
    have h2 := hM 2
    have h4 := hM 4
    have haM := hM address
    have hdM := hM dest
    nlinarith
  · change e.reg = _
    rw [her]
    simp only [hfr, hcr, fetchPost, readPost, TapeStore.setReg]
    funext r
    by_cases hdest : r = dest
    · subst r
      simp [hd1, hd2, hd3, hd4, hd5, hd6]
    · by_cases h6 : r = 6
      · subst r; simp [Ne.symm hd6]
      · by_cases h5 : r = 5
        · subst r; simp [Ne.symm hd5]
        · by_cases h4 : r = 4
          · subst r; simp [Ne.symm hd4]
          · by_cases h3 : r = 3
            · subst r; simp [Ne.symm hd3]
            · by_cases h2 : r = 2
              · subst r; simp [Ne.symm hd2]
              · by_cases h1 : r = 1
                · subst r; simp [Ne.symm hd1]
                · simp [Function.update, hdest, h1, h2, h3, h4, h5, h6]
  · change e.bufferHead = _
    rw [show e.bufferHead = f.bufferHead from congrArg TapeStore.bufferHead hes, hfh]
    simp only [hcr, TapeStore.setReg]
    rw [show c.bufferHead = d.bufferHead from congrArg TapeStore.bufferHead hcs]
    simp







/-- Physical addressed write of the computed Schur entry. The finite code
reconstructs the width and computes every offset before moving the buffer head. -/
theorem writeCurrent_stops (b : Fin 2) (address : Fin 64) (ha : 9 ≤ address.val)
    (inp : Inputs) (d : Store) (M : ℕ) (hm : BottomMarked d b)
    (hM : ∀ r, d.reg r ≤ M) (hh : d.bufferHead b ≤ M) (hv : d.reg 6 ≤ d.reg 0) :
    ∃ t e, t ≤ 100*(M+1)^2 ∧
      (writeCurrent b address).Stops inp (d.toCfg (writeCurrent b address).entry) t e ∧
      e.reg = (readPost (d.setReg 2 (d.reg address)) 0).reg ∧
      EntryWritten d e.store b (entryOffset (d.reg address) (d.reg 0)) (d.reg 0) (d.reg 6) := by
  have ha2 : address ≠ 2 := high_ne_low address ha 2 (by decide)
  have ha4 : address ≠ 4 := high_ne_low address ha 4 (by decide)
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops address (2 : Fin 64) 4
    ha2 ha4 (by decide) inp d
  have hcr : c.reg = ((d.setReg 2 (d.reg address)).setReg 4 0).reg := congrArg TapeStore.reg hcs
  obtain ⟨f, hf, hfs⟩ := TapeMacros.copy_stops (0 : Fin 64) 1 4
    (by decide) (by decide) (by decide) inp c.store
  have hfr : f.reg = ((c.store.setReg 1 (c.reg 0)).setReg 4 0).reg := congrArg TapeStore.reg hfs
  have hcp : TapeStore.SamePayload c.store d := by
    rw [hcs]
    exact (TapeStore.setReg_payload _ 4 0).trans (TapeStore.setReg_payload d 2 (d.reg address))
  have hfp : TapeStore.SamePayload f.store d := by
    rw [hfs]
    exact ((TapeStore.setReg_payload _ 4 0).trans (TapeStore.setReg_payload c.store 1 (c.reg 0))).trans hcp
  have hfh : f.bufferHead = d.bufferHead := by
    change f.store.bufferHead = d.bufferHead
    rw [hfs, hcs]
    rfl
  have hf2 : f.reg 2 = d.reg address := by rw [hfr]; simp [TapeStore.setReg, hcr]
  have hf1 : f.reg 1 = d.reg 0 := by rw [hfr]; simp [TapeStore.setReg, hcr]
  have hf6 : f.reg 6 = d.reg 6 := by rw [hfr]; simp [TapeStore.setReg, hcr]
  have hfv : f.reg 6 ≤ f.reg 1 := by simpa only [hf1, hf6] using hv
  obtain ⟨s, e, hs, he, her, hew⟩ := writeEntry_stops
    (2 : Fin 64) 1 3 4 5 6 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) b inp f.store
      (hm.of_payload hfp).marked hfv
  have hbound : entryAccessBound f.store 2 1 3 4 5 b ≤ 50*(M+1)^2 := by
    apply entryAccessBound_le f.store 2 1 3 4 5 b M
    · simpa only [hf2] using hM address
    · simpa only [hf1] using hM 0
    · simpa [hfr, hcr, TapeStore.setReg] using hM 3
    · simp [hfr, TapeStore.setReg]
    · simpa [hfr, hcr, TapeStore.setReg] using hM 5
    · simpa only [hfh] using hh
  have hall := hc.seq (hf.seq he)
  refine ⟨_, _, ?_, hall, ?_, ?_⟩
  · dsimp only [TapeCfg.store]
    have hc1 : c.reg 1 = d.reg 1 := by rw [hcr]; simp [TapeStore.setReg]
    have hc4 : c.reg 4 = 0 := by rw [hcr]; simp [TapeStore.setReg]
    have hc0 : c.reg 0 = d.reg 0 := by rw [hcr]; simp [TapeStore.setReg]
    rw [hc1, hc4, hc0]
    have h0 := hM 0
    have h1 := hM 1
    have h2 := hM 2
    have h4 := hM 4
    have haM := hM address
    nlinarith
  · change e.reg = _
    rw [her]
    simp only [hfr, hcr, readPost, TapeStore.setReg]
    funext r
    by_cases h6 : r = 6
    · subst r; simp
    · by_cases h5 : r = 5
      · subst r; simp
      · by_cases h4 : r = 4
        · subst r; simp
        · by_cases h3 : r = 3
          · subst r; simp
          · by_cases h1 : r = 1
            · subst r; simp
            · simp [Function.update, h1, h3, h4, h5, h6]
  · change EntryWritten d e.store b _ _ _
    change EntryWritten f.store e.store b (entryOffset (f.reg 2) (f.reg 1)) (f.reg 1) (f.reg 6) at hew
    rw [hf1, hf2, hf6] at hew
    constructor
    · exact hew.roHead.trans hfp.roHead
    · exact hew.output.trans hfp.output
    · simpa [hfh] using hew.head
    · intro c' k
      rw [hew.symbol, hfp.symbol]




















theorem ScalarOutcome.setup {ell : ℕ} {h : 0 < ell} {d e : Store} {out : Fin 64} {v M : ℕ}
    (hs : ScalarOutcome d e out v M) (hd : FieldSetup ell h d) : FieldSetup ell h e := by
  rcases hd with ⟨h0,h36,h37,h38⟩
  refine ⟨(hs.frame 0 (by simp [Protected])).trans h0,
    (hs.frame 36 (by simp [Protected])).trans h36,
    (hs.frame 37 (by simp [Protected])).trans h37,
    (hs.frame 38 (by simp [Protected])).trans h38⟩

























/-- Composition of three actual finite field programs computes precisely one
Schur expression, retaining the pivot inverse and Gaussian loop state. -/
theorem schurArithmetic_stops {L₁ L₂ L₃ : ℕ}
    (mul₁ : TapeProgram 64 2 L₁) (mul₂ : TapeProgram 64 2 L₂) (sub : TapeProgram 64 2 L₃)
    (C₁ k₁ C₂ k₂ C₃ k₃ : ℕ)
    (hm₁ : ScalarContract mul₁ multiplyFunction 15 13 17 C₁ k₁)
    (hm₂ : ScalarContract mul₂ multiplyFunction 17 16 18 C₂ k₂)
    (hs : ScalarContract sub subtractFunction 14 18 6 C₃ k₃)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (d : Store) (M : ℕ)
    (hsetup : FieldSetup ell h d) (hM : ∀ r, d.reg r ≤ M)
    (x y z aInv : Fin (2^ell))
    (hx : d.reg 14 = x.val) (hy : d.reg 15 = y.val)
    (hz : d.reg 16 = z.val) (ha : d.reg 13 = aInv.val) :
    ∃ t e, t ≤ C₁*(M+1)^k₁+C₂*(M+1)^k₂+C₃*(M+1)^k₃+2 ∧
      (schurArithmetic mul₁ mul₂ sub).Stops inp
        (d.toCfg (schurArithmetic mul₁ mul₂ sub).entry) t e ∧
      ScalarOutcome d e.store 6
        ((PolynomialStretch.BinaryField.indexOperations ell h).sub x
          ((PolynomialStretch.BinaryField.indexOperations ell h).mul
            ((PolynomialStretch.BinaryField.indexOperations ell h).mul y aInv) z)).val M := by
  obtain ⟨t₁,c,ht₁,hc,hco⟩ := hm₁.stops ell h inp d M hsetup hM y aInv hy ha
  have hc16 : c.store.reg 16 = z.val :=
    (hco.frame 16 (by simp [Protected])).trans hz
  obtain ⟨t₂,f,ht₂,hf,hfo⟩ := hm₂.stops ell h inp c.store M (hco.setup hsetup) hco.bounded
    (multiplyFunction ell h y aInv) z hco.value hc16
  have hf14 : f.store.reg 14 = x.val :=
    (hfo.frame 14 (by simp [Protected])).trans
      ((hco.frame 14 (by simp [Protected])).trans hx)
  obtain ⟨t₃,e,ht₃,he,heo⟩ := hs.stops ell h inp f.store M (hfo.setup (hco.setup hsetup))
    hfo.bounded x (multiplyFunction ell h (multiplyFunction ell h y aInv) z) hf14 hfo.value
  have hall := hc.seq (hf.seq he)
  refine ⟨_, _, by omega, hall, ?_⟩
  refine ⟨heo.value, ?_, heo.bounded, heo.payload.trans (hfo.payload.trans hco.payload), ?_⟩
  · intro r hr
    exact (heo.frame r hr).trans ((hfo.frame r hr).trans (hco.frame r hr))
  · exact heo.heads.trans (hfo.heads.trans hco.heads)



theorem multiply_source_contract (r : Fin 27 → Fin 64) (hr : Function.Injective r)
    (left right out : Fin 64) (h0 : r 0 = left) (h1 : r 1 = right) (h20 : r 20 = out)
    (h3 : r 3 = 38) (h19 : r 19 = 37) (h23 : r 23 = 0) (h24 : r 24 = 36)
    (hframe : ∀ p, Protected p →
      (∃ i : Fin 27, (i < 2 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24) ∧ r i = p) ∨
      (∀ i, p ≠ r i)) :
    ScalarContract (SourceFieldArithmetic.multiply r) multiplyFunction left right out 10000 6 := by
  constructor
  intro ell h inp d M hs hd a b ha hb
  rcases hs with ⟨hq,hQ,hN,hm⟩
  have hM : 1 ≤ M := by
    have hp : 0 < 2^ell := pow_pos (by decide) ell
    have hbnd := hd 0
    omega
  obtain ⟨t,e,ht,he,_,hans,hin,hout,hbound,htape⟩ := SourceFieldArithmetic.multiply_stops
    r hr inp ell h (PolynomialStretch.BinaryPolynomial.selectedIndex ell h) a b M hM d hd
      (by simpa only [h0] using ha) (by simpa only [h1] using hb)
      (by simpa only [h3] using hm) (by simpa only [h19] using hN)
      (by simpa only [h23] using hq) (by simpa only [h24] using hQ)
  refine ⟨t,e,ht,he,?_⟩
  have hro : e.store.roHead = d.roHead := congrArg Prod.fst htape
  have houtput : e.store.output = d.output := congrArg (fun x => x.2.1) htape
  have hbuffer : e.store.bufferTape = d.bufferTape := congrArg (fun x => x.2.2.1) htape
  have hheads : e.store.bufferHead = d.bufferHead := congrArg (fun x => x.2.2.2) htape
  refine ⟨?_,?_,hbound,⟨hro,houtput,?_⟩,hheads⟩
  · simpa only [h20, multiplyFunction, PolynomialStretch.BinaryField.indexOperations] using hans
  · intro p hp
    rcases hframe p hp with ⟨i,hi,heq⟩ | hf
    · simpa only [heq] using hin i hi
    · exact hout p hf
  · intro b k
    rw [hbuffer]






set_option maxRecDepth 10000 in
theorem mulLayout₁_injective : Function.Injective (mulLayout 15 13 17) := by decide

set_option maxRecDepth 10000 in
theorem mulLayout₂_injective : Function.Injective (mulLayout 17 16 18) := by decide

set_option maxRecDepth 10000 in
theorem mulLayout₁_frame : ∀ p, Protected p →
    (∃ i : Fin 27, (i < 2 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24) ∧ mulLayout 15 13 17 i = p) ∨
    (∀ i, p ≠ mulLayout 15 13 17 i) := by unfold Protected; decide

set_option maxRecDepth 10000 in
theorem mulLayout₂_frame : ∀ p, Protected p →
    (∃ i : Fin 27, (i < 2 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24) ∧ mulLayout 17 16 18 i = p) ∨
    (∀ i, p ≠ mulLayout 17 16 18 i) := by unfold Protected; decide




theorem schurMultiply₁_contract : ScalarContract schurMultiply₁ multiplyFunction 15 13 17 10000 6 :=
  multiply_source_contract (mulLayout 15 13 17) mulLayout₁_injective 15 13 17
    rfl rfl rfl rfl rfl rfl rfl mulLayout₁_frame

theorem schurMultiply₂_contract : ScalarContract schurMultiply₂ multiplyFunction 17 16 18 10000 6 :=
  multiply_source_contract (mulLayout 17 16 18) mulLayout₂_injective 17 16 18
    rfl rfl rfl rfl rfl rfl rfl mulLayout₂_frame




theorem fetchPost_frame (d : Store) (address dest : Fin 64) (v : ℕ) (r : Fin 64)
    (hr : r = 0 ∨ 9 ≤ r.val) (hne : r ≠ dest) :
    (fetchPost d address dest v).reg r = d.reg r := by
  simp only [fetchPost, TapeStore.setReg, Function.update_of_ne hne]
  rcases hr with rfl | hr
  · simp [readPost, TapeStore.setReg]
  · rw [readPost_outside _ _ r hr]
    simp [TapeStore.setReg, high_ne_low r hr 2 (by decide)]

theorem fetchPost_setup (ell : ℕ) (h : 0 < ell) (d : Store) (address dest : Fin 64) (v : ℕ)
    (hs : FieldSetup ell h d) (hd0 : dest ≠ 0) (hd36 : dest ≠ 36)
    (hd37 : dest ≠ 37) (hd38 : dest ≠ 38) : FieldSetup ell h (fetchPost d address dest v) := by
  rcases hs with ⟨h0,h36,h37,h38⟩
  exact ⟨(fetchPost_frame d address dest v 0 (Or.inl rfl) (Ne.symm hd0)).trans h0,
    (fetchPost_frame d address dest v 36 (Or.inr (by decide)) (Ne.symm hd36)).trans h36,
    (fetchPost_frame d address dest v 37 (Or.inr (by decide)) (Ne.symm hd37)).trans h37,
    (fetchPost_frame d address dest v 38 (Or.inr (by decide)) (Ne.symm hd38)).trans h38⟩

theorem entryEnd_le (index q M : ℕ) (hi : index ≤ M) (hq : q ≤ M) :
    entryOffset index q+q ≤ (M+1)^2 := by
  have hp := Nat.mul_le_mul hi hq
  unfold entryOffset
  nlinarith


















theorem fetchSchur_stops (b : Fin 2) (ell : ℕ) (h : 0 < ell) (inp : Inputs)
    (d : Store) (M : ℕ) (hs : FieldSetup ell h d) (hM : ∀ r, d.reg r ≤ M)
    (hh : d.bufferHead b ≤ (M+1)^2) (hm : BottomMarked d b)
    (x y z : Fin (2^ell))
    (hx : ThermometerAt d b (entryOffset (d.reg 9) (d.reg 0)) (d.reg 0) x.val)
    (hy : ThermometerAt d b (entryOffset (d.reg 10) (d.reg 0)) (d.reg 0) y.val)
    (hz : ThermometerAt d b (entryOffset (d.reg 11) (d.reg 0)) (d.reg 0) z.val) :
    ∃ t e, t ≤ 360*((M+1)^2+1)^2+2 ∧
      (fetchSchur b).Stops inp (d.toCfg (fetchSchur b).entry) t e ∧
      FetchSchurOutcome ell h b d e.store x y z M := by
  have hMS : M ≤ (M+1)^2 := by nlinarith
  have hxM : x.val ≤ M := hx.1.trans (hM 0)
  have hyM : y.val ≤ M := hy.1.trans (hM 0)
  have hzM : z.val ≤ M := hz.1.trans (hM 0)
  obtain ⟨t₁,c,ht₁,hc,hcr,hch,hcp⟩ := fetch_stops b 9 14 (by decide) (by decide) inp d
    ((M+1)^2) x.val hm (fun r => (hM r).trans hMS) hh hx
  have hcb : ∀ r, c.reg r ≤ M := by
    rw [hcr]
    exact fetchPost_bounded d 9 14 x.val M hM hxM
  have hcf (r : Fin 64) (hr : r = 0 ∨ 9 ≤ r.val) (hne : r ≠ 14) : c.reg r = d.reg r :=
    (congrFun hcr r).trans (fetchPost_frame d 9 14 x.val r hr hne)
  have hcs : FieldSetup ell h c.store := by
    change FieldSetup ell h { c.store with reg := c.reg }
    rw [hcr]
    exact fetchPost_setup ell h d 9 14 x.val hs (by decide) (by decide) (by decide) (by decide)
  have hcHead : c.bufferHead b ≤ (M+1)^2 := by
    rw [hch]
    simp only [Function.update_self]
    exact entryEnd_le _ _ M (hM 9) (hM 0)
  have hcy : ThermometerAt c.store b (entryOffset (c.reg 10) (c.reg 0)) (c.reg 0) y.val := by
    rw [hcf 10 (Or.inr (by decide)) (by decide), hcf 0 (Or.inl rfl) (by decide)]
    exact hy.of_payload hcp
  obtain ⟨t₂,f,ht₂,hf,hfr,hfh,hfp⟩ := fetch_stops b 10 15 (by decide) (by decide) inp c.store
    ((M+1)^2) y.val (hm.of_payload hcp) (fun r => (hcb r).trans hMS) hcHead hcy
  have hfb : ∀ r, f.reg r ≤ M := by
    rw [hfr]
    exact fetchPost_bounded c.store 10 15 y.val M hcb hyM
  have hff (r : Fin 64) (hr : r = 0 ∨ 9 ≤ r.val) (hne : r ≠ 15) : f.reg r = c.reg r :=
    (congrFun hfr r).trans (fetchPost_frame c.store 10 15 y.val r hr hne)
  have hfs : FieldSetup ell h f.store := by
    change FieldSetup ell h { f.store with reg := f.reg }
    rw [hfr]
    exact fetchPost_setup ell h c.store 10 15 y.val hcs (by decide) (by decide) (by decide) (by decide)
  have hfHead : f.bufferHead b ≤ (M+1)^2 := by
    rw [hfh]
    simp only [Function.update_self]
    exact entryEnd_le _ _ M (hcb 10) (hcb 0)
  have hfpd := hfp.trans hcp
  have hfz : ThermometerAt f.store b (entryOffset (f.reg 11) (f.reg 0)) (f.reg 0) z.val := by
    rw [hff 11 (Or.inr (by decide)) (by decide), hff 0 (Or.inl rfl) (by decide),
      hcf 11 (Or.inr (by decide)) (by decide), hcf 0 (Or.inl rfl) (by decide)]
    exact hz.of_payload hfpd
  obtain ⟨t₃,e,ht₃,he,her,heh,hep⟩ := fetch_stops b 11 16 (by decide) (by decide) inp f.store
    ((M+1)^2) z.val (hm.of_payload hfpd) (fun r => (hfb r).trans hMS) hfHead hfz
  have hef (r : Fin 64) (hr : r = 0 ∨ 9 ≤ r.val) (hne : r ≠ 16) : e.reg r = f.reg r :=
    (congrFun her r).trans (fetchPost_frame f.store 11 16 z.val r hr hne)
  have hall := hc.seq (hf.seq he)
  refine ⟨_,_,by omega,hall,?_⟩
  change FetchSchurOutcome ell h b d e.store x y z M
  constructor
  · change FieldSetup ell h { e.store with reg := e.reg }
    rw [her]
    exact fetchPost_setup ell h f.store 11 16 z.val hfs (by decide) (by decide) (by decide) (by decide)
  · change e.reg 14 = x.val
    rw [hef 14 (Or.inr (by decide)) (by decide), hff 14 (Or.inr (by decide)) (by decide), hcr]
    simp [fetchPost, TapeStore.setReg]
  · change e.reg 15 = y.val
    rw [hef 15 (Or.inr (by decide)) (by decide), hfr]
    simp [fetchPost, TapeStore.setReg]
  · change e.reg 16 = z.val
    rw [her]
    simp [fetchPost, TapeStore.setReg]
  · exact (hef 13 (Or.inr (by decide)) (by decide)).trans
      ((hff 13 (Or.inr (by decide)) (by decide)).trans (hcf 13 (Or.inr (by decide)) (by decide)))
  · exact (hef 12 (Or.inr (by decide)) (by decide)).trans
      ((hff 12 (Or.inr (by decide)) (by decide)).trans (hcf 12 (Or.inr (by decide)) (by decide)))
  · change ∀ r, e.reg r ≤ M
    rw [her]
    exact fetchPost_bounded f.store 11 16 z.val M hfb hzM
  · change e.bufferHead b ≤ (M+1)^2
    rw [heh]
    simp only [Function.update_self]
    exact entryEnd_le _ _ M (hfb 11) (hfb 0)
  · intro c' hne
    change e.bufferHead c' = d.bufferHead c'
    rw [heh, Function.update_of_ne hne]
    change f.bufferHead c' = d.bufferHead c'
    rw [hfh, Function.update_of_ne hne]
    change c.bufferHead c' = d.bufferHead c'
    rw [hch, Function.update_of_ne hne]
  · exact hep.trans hfpd
  · intro r hr
    have hr9 : r = 0 ∨ 9 ≤ r.val := Or.inr (by omega)
    have h14 : r ≠ 14 := by intro he; subst r; norm_num at hr
    have h15 : r ≠ 15 := by intro he; subst r; norm_num at hr
    have h16 : r ≠ 16 := by intro he; subst r; norm_num at hr
    exact (hef r hr9 h16).trans ((hff r hr9 h15).trans (hcf r hr9 h14))








theorem accessPost_bounded (d : Store) (address : Fin 64) (v M : ℕ)
    (hM : ∀ r, d.reg r ≤ M) (hv : v ≤ M) :
    ∀ r, (readPost (d.setReg 2 (d.reg address)) v).reg r ≤ M := by
  intro r
  simp only [readPost, TapeStore.setReg, Function.update_apply]
  split_ifs <;> first | exact hv | exact Nat.zero_le M | exact hM address | exact hM r









/-- Complete physical Schur-cell update. All three input cells are actually
read, both multiplications are the concrete checked 374-label source program,
and the result is actually written into the second thermometer buffer. Only
the subtraction source routine is still a contracted finite-program parameter. -/
theorem schurEntry_stops {L : ℕ} (sub : TapeProgram 64 2 L) (C k : ℕ)
    (hsub : ScalarContract sub subtractFunction 14 18 6 C k)
    (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (d : Store) (M : ℕ)
    (hs : FieldSetup ell h d) (hM : ∀ r, d.reg r ≤ M)
    (hhI : d.bufferHead input ≤ (M+1)^2) (hhO : d.bufferHead output ≤ (M+1)^2)
    (hmI : BottomMarked d input) (hmO : BottomMarked d output)
    (x y z aInv : Fin (2^ell)) (hInv : d.reg 13 = aInv.val)
    (hx : ThermometerAt d input (entryOffset (d.reg 9) (d.reg 0)) (d.reg 0) x.val)
    (hy : ThermometerAt d input (entryOffset (d.reg 10) (d.reg 0)) (d.reg 0) y.val)
    (hz : ThermometerAt d input (entryOffset (d.reg 11) (d.reg 0)) (d.reg 0) z.val) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 (210+((374+(374+L))+60))) (beforeWrite : Store),
      t ≤ 460*((M+1)^2+1)^2+20000*(M+1)^6+C*(M+1)^k+6 ∧
      (schurEntry sub input output).Stops inp (d.toCfg (schurEntry sub input output).entry) t e ∧
      TapeStore.SamePayload beforeWrite d ∧
      EntryWritten beforeWrite e.store output (entryOffset (d.reg 12) (2^ell)) (2^ell)
        ((PolynomialStretch.BinaryField.indexOperations ell h).sub x
          ((PolynomialStretch.BinaryField.indexOperations ell h).mul
            ((PolynomialStretch.BinaryField.indexOperations ell h).mul y aInv) z)).val ∧
      (∀ r, 40 ≤ r.val → e.reg r = d.reg r) ∧ SchurCellState ell h input output e.store M := by
  obtain ⟨t₁,c,ht₁,hc,hco⟩ := fetchSchur_stops input ell h inp d M hs hM hhI hmI x y z hx hy hz
  obtain ⟨t₂,f,ht₂,hf,hfo⟩ := schurArithmetic_stops schurMultiply₁ schurMultiply₂ sub
    10000 6 10000 6 C k schurMultiply₁_contract schurMultiply₂_contract hsub
    ell h inp c.store M hco.setup hco.bounded x y z aInv hco.x hco.y hco.z
      (hco.inverse.trans hInv)
  have hfp : TapeStore.SamePayload f.store d := hfo.payload.trans hco.payload
  have hfh : f.store.bufferHead output = d.bufferHead output := by
    rw [hfo.heads]
    exact hco.otherHead output hio
  have hsetup : FieldSetup ell h f.store := hfo.setup hco.setup
  have h0 : f.store.reg 0 = 2^ell := hsetup.1
  have h12 : f.store.reg 12 = d.reg 12 :=
    (hfo.frame 12 (by simp [Protected])).trans hco.target
  have hv : f.store.reg 6 ≤ f.store.reg 0 := by
    rw [hfo.value, h0]
    exact Nat.le_of_lt (Fin.isLt _)
  have hMS : M ≤ (M+1)^2 := by nlinarith
  obtain ⟨t₃,e,ht₃,he,her,hew⟩ := writeCurrent_stops output 12 (by decide) inp f.store ((M+1)^2)
    (hmO.of_payload hfp) (fun r => (hfo.bounded r).trans hMS) (hfh.le.trans hhO) hv
  have heh : e.bufferHead = Function.update f.store.bufferHead output
      (entryOffset (f.store.reg 12) (f.store.reg 0)+f.store.reg 0) := hew.head
  have hall := hc.seq (hf.seq he)
  refine ⟨_,_,f.store,?_,hall,hfp,?_,?_,?_⟩
  · nlinarith
  · change EntryWritten f.store e.store output (entryOffset (d.reg 12) (2^ell)) (2^ell) _
    rw [h12, h0, hfo.value] at hew
    exact hew
  · intro r hr
    change e.reg r = _
    rw [her]
    rw [readPost_outside _ 0 r (by omega)]
    have hr2 : r ≠ 2 := by intro he; subst r; norm_num at hr
    simp only [TapeStore.setReg, Function.update_of_ne hr2]
    exact (hfo.frame r (by simp [Protected, hr])).trans (hco.caller r hr)
  · change SchurCellState ell h input output e.store M
    constructor
    · rcases hsetup with ⟨h0',h36,h37,h38⟩
      unfold FieldSetup
      change e.reg 0 = _ ∧ e.reg 36 = _ ∧ e.reg 37 = _ ∧ e.reg 38 = _
      rw [her]
      simpa [readPost, TapeStore.setReg] using And.intro h0' (And.intro h36 (And.intro h37 h38))
    · change ∀ r, e.reg r ≤ M
      rw [her]
      exact accessPost_bounded f.store 12 0 M hfo.bounded (Nat.zero_le M)
    · change e.bufferHead input ≤ (M+1)^2
      rw [heh, Function.update_of_ne (Ne.symm hio), hfo.heads]
      exact hco.head
    · change e.bufferHead output ≤ (M+1)^2
      rw [heh]
      simp only [Function.update_self]
      exact entryEnd_le _ _ M (hfo.bounded 12) (hfo.bounded 0)
    · have hpre := hmI.of_payload hfp
      constructor
      · rw [hew.symbol]
        simpa [Ne.symm hio] using hpre.1
      · intro j hj
        rw [hew.symbol]
        simpa [Ne.symm hio] using hpre.2 j hj
    · exact hew.bottomMarked (by simp [entryOffset]) (hmO.of_payload hfp)



theorem addition_source_contract (r : Fin 27 → Fin 64) (hr : Function.Injective r)
    (left right out : Fin 64) (h0 : r 0 = left) (h3 : r 3 = right) (h20 : r 20 = out)
    (h19 : r 19 = 37) (h23 : r 23 = 0)
    (hframe : ∀ p, Protected p →
      (∃ i : Fin 27, (i = 0 ∨ i = 3 ∨ i = 19 ∨ 23 ≤ i) ∧ i ≠ 25 ∧ r i = p) ∨
      (∀ i, p ≠ r i)) :
    ScalarContract (SourceFieldArithmetic.addition r) subtractFunction left right out 3000 5 := by
  constructor
  intro ell h inp d M hs hd a b ha hb
  rcases hs with ⟨hq,_,hN,_⟩
  have hM : 1 ≤ M := by
    have hp : 0 < 2^ell := pow_pos (by decide) ell
    have hbnd := hd 0
    omega
  obtain ⟨t,e,ht,he,_,hans,hin,hout,hbound,htape⟩ := SourceFieldArithmetic.addition_stops
    r hr inp ell a b M hM d hd (by simpa only [h0] using ha) (by simpa only [h3] using hb)
      (by simpa only [h19] using hN) (by simpa only [h23] using hq)
  refine ⟨t,e,ht,he,?_⟩
  have hro : e.store.roHead = d.roHead := congrArg Prod.fst htape
  have houtput : e.store.output = d.output := congrArg (fun x => x.2.1) htape
  have hbuffer : e.store.bufferTape = d.bufferTape := congrArg (fun x => x.2.2.1) htape
  have hheads : e.store.bufferHead = d.bufferHead := congrArg (fun x => x.2.2.2) htape
  refine ⟨?_,?_,hbound,⟨hro,houtput,?_⟩,hheads⟩
  · simpa only [h20, subtractFunction, PolynomialStretch.BinaryField.indexOperations] using hans
  · intro p hp
    rcases hframe p hp with ⟨i,hi,h25,heq⟩ | hf
    · simpa only [heq] using hin i hi h25
    · exact hout p hf
  · intro b k
    rw [hbuffer]




set_option maxRecDepth 10000 in
theorem subLayout_injective : Function.Injective subLayout := by decide

set_option maxRecDepth 10000 in
theorem subLayout_frame : ∀ p, Protected p →
    (∃ i : Fin 27, (i = 0 ∨ i = 3 ∨ i = 19 ∨ 23 ≤ i) ∧ i ≠ 25 ∧ subLayout i = p) ∨
    (∀ i, p ≠ subLayout i) := by unfold Protected; decide



theorem schurSubtract_contract : ScalarContract schurSubtract subtractFunction 14 18 6 3000 5 :=
  addition_source_contract subLayout subLayout_injective 14 18 6
    rfl rfl rfl rfl rfl subLayout_frame






theorem concreteSchurEntry_stops (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (d : Store) (M : ℕ)
    (hs : FieldSetup ell h d) (hM : ∀ r, d.reg r ≤ M)
    (hhI : d.bufferHead input ≤ (M+1)^2) (hhO : d.bufferHead output ≤ (M+1)^2)
    (hmI : BottomMarked d input) (hmO : BottomMarked d output)
    (x y z aInv : Fin (2^ell)) (hInv : d.reg 13 = aInv.val)
    (hx : ThermometerAt d input (entryOffset (d.reg 9) (d.reg 0)) (d.reg 0) x.val)
    (hy : ThermometerAt d input (entryOffset (d.reg 10) (d.reg 0)) (d.reg 0) y.val)
    (hz : ThermometerAt d input (entryOffset (d.reg 11) (d.reg 0)) (d.reg 0) z.val) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 1383) (beforeWrite : Store),
      t ≤ 460*((M+1)^2+1)^2+20000*(M+1)^6+3000*(M+1)^5+6 ∧
      (concreteSchurEntry input output).Stops inp (d.toCfg (concreteSchurEntry input output).entry) t e ∧
      TapeStore.SamePayload beforeWrite d ∧
      EntryWritten beforeWrite e.store output (entryOffset (d.reg 12) (2^ell)) (2^ell)
        ((PolynomialStretch.BinaryField.indexOperations ell h).sub x
          ((PolynomialStretch.BinaryField.indexOperations ell h).mul
            ((PolynomialStretch.BinaryField.indexOperations ell h).mul y aInv) z)).val ∧
      (∀ r, 40 ≤ r.val → e.reg r = d.reg r) ∧ SchurCellState ell h input output e.store M :=
  schurEntry_stops schurSubtract 3000 5 schurSubtract_contract input output hio
    ell h inp d M hs hM hhI hhO hmI hmO x y z aInv hInv hx hy hz













@[simp] theorem paddedSchur_apply {α : Type*} (O : EncodedGaussian.Operations α) {m n : ℕ}
    (A : Gaussian.Table α m n) (p : Fin m × Fin n) (i : Fin m) (j : Fin n) :
    Gaussian.toMatrix (paddedSchur O A p) i j = O.sub (Gaussian.toMatrix A i j)
      (O.mul (O.mul (Gaussian.toMatrix A i p.2) (O.inv (Gaussian.toMatrix A p.1 p.2)))
        (Gaussian.toMatrix A p.1 j)) := by
  simp [paddedSchur, Gaussian.toMatrix, Gaussian.ofMatrix]

theorem paddedSchur_rank {q m n : ℕ} {F : Type*} [Field F] [DecidableEq F]
    {O : EncodedGaussian.Operations (Fin q)} {decode : Fin q → F}
    (h : EncodedGaussian.Interpretation O decode)
    (A : Gaussian.Table (Fin q) (m+1) (n+1)) (p : Fin (m+1) × Fin (n+1))
    (hp : Gaussian.toMatrix A p.1 p.2 ≠ O.zero) :
    (Gaussian.toMatrix (EncodedGaussian.mapTable decode (paddedSchur O A p))).rank =
      (Gaussian.toMatrix (EncodedGaussian.mapTable decode (EncodedGaussian.schur O A p))).rank := by
  have hd : decode (Gaussian.toMatrix A p.1 p.2) ≠ 0 := by
    intro he
    exact hp (h.injective (he.trans h.zero.symm))
  have hpad (i : Fin (m+1)) (j : Fin (n+1)) :
      Gaussian.toMatrix (EncodedGaussian.mapTable decode (paddedSchur O A p)) i j =
        decode (Gaussian.toMatrix A i j) - decode (Gaussian.toMatrix A i p.2) *
          (decode (Gaussian.toMatrix A p.1 p.2))⁻¹ * decode (Gaussian.toMatrix A p.1 j) := by
    rw [EncodedGaussian.toMatrix_mapTable, paddedSchur_apply, h.sub, h.mul, h.mul, h.inv]
  have hsmall (i : Fin m) (j : Fin n) :
      Gaussian.toMatrix (EncodedGaussian.mapTable decode (EncodedGaussian.schur O A p)) i j =
        decode (Gaussian.toMatrix A (p.1.succAbove i) (p.2.succAbove j)) -
          decode (Gaussian.toMatrix A (p.1.succAbove i) p.2) *
          (decode (Gaussian.toMatrix A p.1 p.2))⁻¹ * decode (Gaussian.toMatrix A p.1 (p.2.succAbove j)) := by
    rw [EncodedGaussian.toMatrix_mapTable]
    simp [EncodedGaussian.schur, Gaussian.toMatrix, Gaussian.ofMatrix, h.sub, h.mul, h.inv]
  have he : (Gaussian.toMatrix (EncodedGaussian.mapTable decode (paddedSchur O A p))).submatrix
      (Gaussian.pivotEquiv p.1) (Gaussian.pivotEquiv p.2) =
      Matrix.fromBlocks (0 : Matrix PUnit.{1} PUnit.{1} F) 0 0
        (Gaussian.toMatrix (EncodedGaussian.mapTable decode (EncodedGaussian.schur O A p))) := by
    ext (i | i) (j | j) <;>
      simp [Matrix.submatrix_apply, Matrix.fromBlocks, Gaussian.pivotEquiv_inl,
        Gaussian.pivotEquiv_inr, hpad, hsmall, mul_assoc, hd]
  calc
    _ = ((Gaussian.toMatrix (EncodedGaussian.mapTable decode (paddedSchur O A p))).submatrix
        (Gaussian.pivotEquiv p.1) (Gaussian.pivotEquiv p.2)).rank :=
      (Matrix.rank_submatrix _ _ _).symm
    _ = _ := by rw [he, Gaussian.rank_fromBlocks_zero, Matrix.rank_zero, Nat.zero_add]

theorem paddedSchur_rank_step {q m n : ℕ} {F : Type*} [Field F] [DecidableEq F]
    {O : EncodedGaussian.Operations (Fin q)} {decode : Fin q → F}
    (h : EncodedGaussian.Interpretation O decode)
    (A : Gaussian.Table (Fin q) (m+1) (n+1)) (p : Fin (m+1) × Fin (n+1))
    (hp : Gaussian.toMatrix A p.1 p.2 ≠ O.zero) :
    (Gaussian.toMatrix (EncodedGaussian.mapTable decode A)).rank =
      (Gaussian.toMatrix (EncodedGaussian.mapTable decode (paddedSchur O A p))).rank+1 := by
  rw [paddedSchur_rank h A p hp]
  exact encoded_schur_rank_step h A p hp



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


section FlattenModule81



set_option autoImplicit false

namespace ExpandingCodes.Computation


























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







theorem sumInto_stops (left right dest : Fin 64)
    (hld : left ≠ dest) (hl4 : left ≠ 4) (hrd : right ≠ dest) (hr4 : right ≠ 4) (hd4 : dest ≠ 4)
    (inp : Inputs) (d : Store) :
    ∃ e, (sumInto left right dest).Stops inp (d.toCfg (sumInto left right dest).entry)
      (d.reg dest+d.reg 4+5*d.reg left+5*d.reg right+13) e ∧
      e.store = sumPost d left right dest := by
  obtain ⟨c,hc,hcs⟩ := TapeMacros.copy_stops left dest 4 hld hl4 hd4 inp d
  obtain ⟨e,he,hes⟩ := TapeMacros.addPreserving_stops right dest 4 hrd hr4 hd4 inp c.store
  have hcr : c.reg = ((d.setReg dest (d.reg left)).setReg 4 0).reg := congrArg TapeStore.reg hcs
  have hc4 : c.reg 4 = 0 := by rw [hcr]; simp [TapeStore.setReg]
  have hcright : c.reg right = d.reg right := by rw [hcr]; simp [TapeStore.setReg, hr4, hrd]
  have hall := hc.seq he
  refine ⟨e.mapPC (TapeProgram.rightLabel 11),?_,?_⟩
  · convert hall using 1 <;> first | rfl | (dsimp only [TapeCfg.store]; rw [hc4,hcright]; omega)
  · change e.store = _
    rw [hes,hcs]
    simp only [sumPost,TapeStore.setReg]
    congr 1
    funext r
    by_cases h4 : r = 4
    · subst r; simp
    · by_cases hd : r = dest
      · subst r; simp [hrd,hr4,hd4]
      · simp [Function.update,h4,hd]

theorem sumPost_bounded (d : Store) (left right dest : Fin 64) (M : ℕ)
    (hM : ∀ r, d.reg r ≤ M) (hsum : d.reg left+d.reg right ≤ M) :
    ∀ r, (sumPost d left right dest).reg r ≤ M := by
  intro r
  simp only [sumPost,TapeStore.setReg,Function.update_apply]
  split_ifs <;> first | exact Nat.zero_le M | exact hsum | exact hM r












/-- Runtime address arithmetic uses actual preserving unary additions. The
same 71-label code handles every matrix dimension and pivot position. -/
theorem prepareAddresses_stops (inp : Inputs) (d : Store) (M : ℕ)
    (hM : ∀ r,d.reg r ≤ M) (hD : d.reg 41+d.reg 42 ≤ M)
    (hC : d.reg 41+d.reg 43 ≤ M) (hB : d.reg 44+d.reg 42 ≤ M) :
    ∃ t e, t ≤ 100*(M+1) ∧ prepareAddresses.Stops inp (d.toCfg prepareAddresses.entry) t e ∧
      e.store = addressStore d ∧ (∀ r,e.reg r ≤ M) := by
  obtain ⟨c₁,h₁,hs₁⟩ := sumInto_stops 41 42 9
    (by decide) (by decide) (by decide) (by decide) (by decide) inp d
  have hb₁ : ∀ r,c₁.store.reg r ≤ M := by rw [hs₁]; exact sumPost_bounded d 41 42 9 M hM hD
  have hC₁ : c₁.store.reg 41+c₁.store.reg 43 ≤ M := by
    rw [hs₁]; simpa [sumPost,TapeStore.setReg] using hC
  obtain ⟨c₂,h₂,hs₂⟩ := sumInto_stops 41 43 10
    (by decide) (by decide) (by decide) (by decide) (by decide) inp c₁.store
  have hb₂ : ∀ r,c₂.store.reg r ≤ M := by rw [hs₂]; exact sumPost_bounded _ 41 43 10 M hb₁ hC₁
  have hB₂ : c₂.store.reg 44+c₂.store.reg 42 ≤ M := by
    rw [hs₂,hs₁]; simpa [sumPost,TapeStore.setReg] using hB
  obtain ⟨c₃,h₃,hs₃⟩ := sumInto_stops 44 42 11
    (by decide) (by decide) (by decide) (by decide) (by decide) inp c₂.store
  have hb₃ : ∀ r,c₃.store.reg r ≤ M := by rw [hs₃]; exact sumPost_bounded _ 44 42 11 M hb₂ hB₂
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops (45 : Fin 64) 12 4
    (by decide) (by decide) (by decide) inp c₃.store
  have hall := h₁.seq (h₂.seq (h₃.seq he))
  refine ⟨_,_,?_,hall,?_,?_⟩
  · have ht₁ : d.reg 9+d.reg 4+5*d.reg 41+5*d.reg 42+13 ≤ 12*M+13 := by
      have := hM 9; have := hM 4; have := hM 41; have := hM 42; omega
    have ht₂ : c₁.store.reg 10+c₁.store.reg 4+5*c₁.store.reg 41+5*c₁.store.reg 43+13 ≤ 12*M+13 := by
      have := hb₁ 10; have := hb₁ 4; have := hb₁ 41; have := hb₁ 43; omega
    have ht₃ : c₂.store.reg 11+c₂.store.reg 4+5*c₂.store.reg 44+5*c₂.store.reg 42+13 ≤ 12*M+13 := by
      have := hb₂ 11; have := hb₂ 4; have := hb₂ 44; have := hb₂ 42; omega
    have ht₄ : c₃.store.reg 12+c₃.store.reg 4+5*c₃.store.reg 45+7 ≤ 7*M+7 := by
      have := hb₃ 12; have := hb₃ 4; have := hb₃ 45; omega
    omega
  · change e.store = _
    rw [hes,hs₃,hs₂,hs₁]
    rfl
  · change ∀ r,e.store.reg r ≤ M
    rw [hes]
    exact FieldPrograms.setReg_bound _ 4 0 M
      (FieldPrograms.setReg_bound c₃.store 12 (c₃.store.reg 45) M hb₃ (hb₃ 45)) (Nat.zero_le M)

@[simp] theorem addressStore_D (d : Store) : (addressStore d).reg 9 = d.reg 41+d.reg 42 := by
  simp [addressStore,sumPost,TapeStore.setReg]
@[simp] theorem addressStore_C (d : Store) : (addressStore d).reg 10 = d.reg 41+d.reg 43 := by
  simp [addressStore,sumPost,TapeStore.setReg]
@[simp] theorem addressStore_B (d : Store) : (addressStore d).reg 11 = d.reg 44+d.reg 42 := by
  simp [addressStore,sumPost,TapeStore.setReg]
@[simp] theorem addressStore_target (d : Store) : (addressStore d).reg 12 = d.reg 45 := by
  simp [addressStore,sumPost,TapeStore.setReg]

theorem addressStore_frame (d : Store) (r : Fin 64) (hr : 40 ≤ r.val) :
    (addressStore d).reg r = d.reg r := by
  have h4 : r ≠ 4 := by intro he;subst r;norm_num at hr
  have h9 : r ≠ 9 := by intro he;subst r;norm_num at hr
  have h10 : r ≠ 10 := by intro he;subst r;norm_num at hr
  have h11 : r ≠ 11 := by intro he;subst r;norm_num at hr
  have h12 : r ≠ 12 := by intro he;subst r;norm_num at hr
  simp [addressStore,sumPost,TapeStore.setReg,h4,h9,h10,h11,h12]



theorem addressStore_payload (d : Store) : TapeStore.SamePayload (addressStore d) d :=
  ⟨rfl,rfl,fun _ _ => rfl⟩

theorem addressStore_setup (ell : ℕ) (h : 0 < ell) (d : Store) (hs : FieldSetup ell h d) :
    FieldSetup ell h (addressStore d) := by
  simpa [FieldSetup,addressStore,sumPost,TapeStore.setReg] using hs

theorem flatEntry_pair {q m n : ℕ} (A : Gaussian.Table (Fin q) m n) (i : Fin m) (j : Fin n) :
    flatEntry A (finProdFinEquiv (i,j)).val = (Gaussian.toMatrix A i j).val := by
  let k : Fin (m*n) := finProdFinEquiv (i,j)
  change flatEntry A k.val = _
  rw [flatEntry,dif_pos k.isLt]
  change (Gaussian.toMatrix A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).val = _
  rw [show finProdFinEquiv.symm k = (i,j) from finProdFinEquiv.symm_apply_apply (i,j)]

theorem storedEntry {q m n : ℕ} {d : Store} {b : Fin 2}
    {A : Gaussian.Table (Fin q) m n} (ht : MatrixStored d b A) (i : Fin m) (j : Fin n) :
    TapeArrays.ThermometerAt d b (TapeArrays.entryOffset (finProdFinEquiv (i,j)).val q) q
      (Gaussian.toMatrix A i j).val := by
  have h := ht (finProdFinEquiv (i,j))
  dsimp only at h
  rw [flatEntry_pair] at h
  exact h











/-- A source-level matrix-entry refinement: runtime counters compute the
three physical addresses, actual finite field code computes the expression,
and exactly the corresponding padded-Schur cell is physically overwritten. -/
theorem materializeCell_stops {m n : ℕ} (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (A : Gaussian.Table (Fin (2^ell)) m n)
    (p : Fin m × Fin n) (i : Fin m) (j : Fin n) (d : Store) (M : ℕ)
    (hs : FieldSetup ell h d) (hM : ∀ r,d.reg r ≤ M) (hsize : m*n ≤ M)
    (hhI : d.bufferHead input ≤ (M+1)^2) (hhO : d.bufferHead output ≤ (M+1)^2)
    (hmI : TapeArrays.BottomMarked d input) (hmO : TapeArrays.BottomMarked d output)
    (hstored : MatrixStored d input A) (hcoord : Coordinates p i j d)
    (hInv : d.reg 13 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
      (Gaussian.toMatrix A p.1 p.2)).val) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 1454) (beforeWrite : Store),
      t ≤ 100*(M+1)+460*((M+1)^2+1)^2+20000*(M+1)^6+3000*(M+1)^5+7 ∧
      (materializeCell input output).Stops inp (d.toCfg (materializeCell input output).entry) t e ∧
      TapeStore.SamePayload beforeWrite d ∧
      TapeArrays.EntryWritten beforeWrite e.store output
        (TapeArrays.entryOffset (finProdFinEquiv (i,j)).val (2^ell)) (2^ell)
        (Gaussian.toMatrix (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p) i j).val ∧
      (∀ r,40 ≤ r.val → e.reg r = d.reg r) ∧ SchurCellState ell h input output e.store M := by
  have hcell (i' : Fin m) (j' : Fin n) : i'.val*n+j'.val ≤ M := by
    have hidx := (finProdFinEquiv (i',j')).isLt
    change j'.val+n*i'.val < m*n at hidx
    nlinarith
  have hD : d.reg 41+d.reg 42 ≤ M := by rw [hcoord.rowBase,hcoord.column]; exact hcell i j
  have hC : d.reg 41+d.reg 43 ≤ M := by rw [hcoord.rowBase,hcoord.pivotColumn]; exact hcell i p.2
  have hB : d.reg 44+d.reg 42 ≤ M := by rw [hcoord.pivotBase,hcoord.column]; exact hcell p.1 j
  obtain ⟨t₁,c,ht₁,hc,hcs,hcb⟩ := prepareAddresses_stops inp d M hM hD hC hB
  have hcp : TapeStore.SamePayload c.store d := by rw [hcs]; exact addressStore_payload d
  have hch : c.store.bufferHead = d.bufferHead := by rw [hcs]; rfl
  have hc0 : c.store.reg 0 = 2^ell := by rw [hcs]; exact (addressStore_setup ell h d hs).1
  have hc9 : c.store.reg 9 = (finProdFinEquiv (i,j)).val := by
    rw [hcs,addressStore_D,hcoord.rowBase,hcoord.column]
    change i.val*n+j.val = j.val+n*i.val
    ring
  have hc10 : c.store.reg 10 = (finProdFinEquiv (i,p.2)).val := by
    rw [hcs,addressStore_C,hcoord.rowBase,hcoord.pivotColumn]
    change i.val*n+p.2.val = p.2.val+n*i.val
    ring
  have hc11 : c.store.reg 11 = (finProdFinEquiv (p.1,j)).val := by
    rw [hcs,addressStore_B,hcoord.pivotBase,hcoord.column]
    change p.1.val*n+j.val = j.val+n*p.1.val
    ring
  have hc12 : c.store.reg 12 = (finProdFinEquiv (i,j)).val := by
    rw [hcs,addressStore_target,hcoord.target]
    change i.val*n+j.val = j.val+n*i.val
    ring
  have hcInv : c.store.reg 13 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
      (Gaussian.toMatrix A p.1 p.2)).val := by
    rw [hcs]
    simpa [addressStore,sumPost,TapeStore.setReg] using hInv
  have hx : TapeArrays.ThermometerAt c.store input
      (TapeArrays.entryOffset (c.store.reg 9) (c.store.reg 0)) (c.store.reg 0)
      (Gaussian.toMatrix A i j).val := by
    rw [hc9,hc0]
    exact (storedEntry hstored i j).of_payload hcp
  have hy : TapeArrays.ThermometerAt c.store input
      (TapeArrays.entryOffset (c.store.reg 10) (c.store.reg 0)) (c.store.reg 0)
      (Gaussian.toMatrix A i p.2).val := by
    rw [hc10,hc0]
    exact (storedEntry hstored i p.2).of_payload hcp
  have hz : TapeArrays.ThermometerAt c.store input
      (TapeArrays.entryOffset (c.store.reg 11) (c.store.reg 0)) (c.store.reg 0)
      (Gaussian.toMatrix A p.1 j).val := by
    rw [hc11,hc0]
    exact (storedEntry hstored p.1 j).of_payload hcp
  obtain ⟨t₂,e,before,ht₂,he,hbefore,hew,hcaller,hstate⟩ := concreteSchurEntry_stops input output hio
    ell h inp c.store M (by rw [hcs]; exact addressStore_setup ell h d hs) hcb
    ((congrFun hch input).le.trans hhI) ((congrFun hch output).le.trans hhO)
    (hmI.of_payload hcp) (hmO.of_payload hcp)
    (Gaussian.toMatrix A i j) (Gaussian.toMatrix A i p.2) (Gaussian.toMatrix A p.1 j)
    ((PolynomialStretch.BinaryField.indexOperations ell h).inv (Gaussian.toMatrix A p.1 p.2)) hcInv hx hy hz
  have hall := hc.seq he
  refine ⟨_,_,before,by omega,hall,hbefore.trans hcp,?_,?_,hstate⟩
  · change TapeArrays.EntryWritten before e.store output _ _ _
    rw [hc12] at hew
    simpa only [paddedSchur_apply] using hew
  · intro r hr
    exact (hcaller r hr).trans (by rw [hcs]; exact addressStore_frame d r hr)



/-- The existing finite counted-loop code also supports semantic freshness:
actual body traces can certify the loop counter directly. This lets mapped
field subroutines restore protected counters internally without requiring a
syntactic no-touch condition. -/
theorem countedLoop_stops_of_body {R B L : ℕ} (P : TapeProgram R B L) (r : Fin R)
    (inp : Inputs) (C : ℕ) (Inv : ℕ → TapeStore R B → Prop)
    (hbody : ∀ n d, d.reg r = n+1 → Inv (n+1) d →
      ∃ t c, t ≤ C ∧ P.Stops inp ((TapeProgram.decStore r d).toCfg P.entry) t c ∧
        c.reg r = n ∧ Inv n c.store)
    (n : ℕ) (d : TapeStore R B) (hd : d.reg r = n) (hi : Inv n d) :
    ∃ t e, t ≤ n*(C+2)+1 ∧
      (TapeProgram.countedLoop P r).Stops inp (d.toCfg (TapeProgram.loopHeader L)) t
        (e.toCfg (TapeProgram.loopExit L)) ∧ Inv 0 e ∧ e.reg r = 0 := by
  induction n generalizing d with
  | zero => exact ⟨1,d,by omega,TapeProgram.loop_zero P r inp d hd,hi,hd⟩
  | succ n ih =>
    obtain ⟨s,c,hs,hstop,hc,hInv⟩ := hbody n d hd hi
    obtain ⟨t,e,ht,he,hIe,hzero⟩ := ih c.store hc hInv
    have hheader := TapeProgram.loop_positive_header P r inp d (by omega)
    have hrun := hstop.exec.relabel (TapeProgram.leftLabel 2) (TapeProgram.loop_code_body_active P r)
    have hreturn := TapeProgram.loop_body_return P r inp c hstop.halted
    refine ⟨1+s+1+t,e,?_,⟨((hheader.trans hrun).trans hreturn).trans he.exec,he.halted⟩,hIe,hzero⟩
    rw [show (n+1)*(C+2) = n*(C+2)+(C+2) by ring]
    omega



theorem matrixStored_of_payload {q m n : ℕ} {d e : Store} {b : Fin 2}
    {A : Gaussian.Table (Fin q) m n} (ht : MatrixStored d b A) (hp : TapeStore.SamePayload e d) :
    MatrixStored e b A := fun i => (ht i).of_payload hp














theorem cellTick_stops {m n : ℕ} (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (A : Gaussian.Table (Fin (2^ell)) m n)
    (p : Fin m × Fin n) (i : Fin m) (j : Fin n) (d : Store) (M : ℕ)
    (hs : FieldSetup ell h d) (hM : ∀ r,d.reg r ≤ M) (hsize : m*n ≤ M)
    (hhI : d.bufferHead input ≤ (M+1)^2) (hhO : d.bufferHead output ≤ (M+1)^2)
    (hmI : TapeArrays.BottomMarked d input) (hmO : TapeArrays.BottomMarked d output)
    (hstored : MatrixStored d input A) (hcoord : Coordinates p i j d)
    (hInv : d.reg 50 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
      (Gaussian.toMatrix A p.1 p.2)).val)
    (hcol : d.reg 42+1 ≤ M) (hcut : d.reg 45+1 ≤ M) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 1469) (beforeWrite : Store), t ≤ tickBudget M ∧
      (cellTick input output).Stops inp (d.toCfg (cellTick input output).entry) t e ∧
      TapeStore.SamePayload beforeWrite d ∧
      TapeArrays.EntryWritten beforeWrite e.store output
        (TapeArrays.entryOffset (finProdFinEquiv (i,j)).val (2^ell)) (2^ell)
        (Gaussian.toMatrix (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p) i j).val ∧
      e.reg 42 = d.reg 42+1 ∧ e.reg 45 = d.reg 45+1 ∧
      (∀ r,40 ≤ r.val → r ≠ 42 → r ≠ 45 → e.reg r = d.reg r) ∧
      SchurCellState ell h input output e.store M := by
  obtain ⟨c,hc,hcs⟩ := TapeMacros.copy_stops (50 : Fin 64) 13 4 (by decide) (by decide) (by decide) inp d
  have hcp : TapeStore.SamePayload c.store d := by
    rw [hcs]
    exact (TapeStore.setReg_payload _ 4 0).trans (TapeStore.setReg_payload d 13 (d.reg 50))
  have hcb : ∀ r,c.reg r ≤ M := by
    change ∀ r,c.store.reg r ≤ M
    rw [hcs]
    exact FieldPrograms.setReg_bound _ 4 0 M
      (FieldPrograms.setReg_bound d 13 (d.reg 50) M hM (hM 50)) (Nat.zero_le M)
  have hcf (r : Fin 64) (hr : 40 ≤ r.val) : c.store.reg r = d.reg r := by
    rw [hcs]
    have h13 : r ≠ 13 := by intro he;subst r;norm_num at hr
    have h4 : r ≠ 4 := by intro he;subst r;norm_num at hr
    simp [TapeStore.setReg,h13,h4]
  have hch : c.store.bufferHead = d.bufferHead := by rw [hcs];rfl
  have hcoordC : Coordinates p i j c.store :=
    ⟨(hcf 41 (by decide)).trans hcoord.rowBase,(hcf 42 (by decide)).trans hcoord.column,
      (hcf 43 (by decide)).trans hcoord.pivotColumn,(hcf 44 (by decide)).trans hcoord.pivotBase,
      (hcf 45 (by decide)).trans hcoord.target⟩
  have hInvC : c.store.reg 13 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
      (Gaussian.toMatrix A p.1 p.2)).val := by rw [hcs];simp [TapeStore.setReg,hInv]
  have hsC : FieldSetup ell h c.store := by rw [hcs];simpa [FieldSetup,TapeStore.setReg] using hs
  obtain ⟨s,f,before,hst,hf,hbefore,hew,hcaller,hstate⟩ := materializeCell_stops input output hio ell h inp A p i j
    c.store M hsC hcb hsize ((congrFun hch input).le.trans hhI) ((congrFun hch output).le.trans hhO)
    (hmI.of_payload hcp) (hmO.of_payload hcp) (matrixStored_of_payload hstored hcp) hcoordC hInvC
  have hff (r : Fin 64) (hr : 40 ≤ r.val) : f.store.reg r = d.reg r := (hcaller r hr).trans (hcf r hr)
  have hinc₁ := TapeMacros.increment_stops (42 : Fin 64) inp f.store
  let d₁ := f.store.setReg 42 (f.reg 42+1)
  have hinc₂ := TapeMacros.increment_stops (45 : Fin 64) inp d₁
  have hall := hc.seq (hf.seq (hinc₁.seq hinc₂))
  have hd₁45 : d₁.reg 45 = f.reg 45 := by simp [d₁,TapeStore.setReg]
  let e := d₁.setReg 45 (d₁.reg 45+1)
  have heStore : e = tickStore f.store := by simp [e,d₁,tickStore,TapeStore.setReg]
  refine ⟨_,_,before,?_,hall,hbefore.trans hcp,?_,?_,?_,?_,?_⟩
  · have h13 := hM 13
    have h4 := hM 4
    have h50 := hM 50
    change s ≤ cellBudget M at hst
    unfold tickBudget
    omega
  · change TapeArrays.EntryWritten before e output _ _ _
    rw [heStore]
    exact ⟨hew.roHead,hew.output,hew.head,hew.symbol⟩
  · change e.reg 42 = _
    rw [heStore]
    simpa [tickStore,TapeStore.setReg] using congrArg (fun v : ℕ => v+1) (hff 42 (by decide))
  · change e.reg 45 = _
    rw [heStore]
    simpa [tickStore,TapeStore.setReg] using congrArg (fun v : ℕ => v+1) (hff 45 (by decide))
  · intro r hr hr42 hr45
    change e.reg r = _
    rw [heStore]
    simpa [tickStore,TapeStore.setReg,hr42,hr45] using hff r hr
  · change SchurCellState ell h input output e M
    rw [heStore]
    constructor
    · simpa [FieldSetup,tickStore,TapeStore.setReg] using hstate.setup
    · exact FieldPrograms.setReg_bound _ 45 (f.store.reg 45+1) M
        (FieldPrograms.setReg_bound f.store 42 (f.store.reg 42+1) M hstate.bounded
          ((congrArg (fun v : ℕ => v+1) (hff 42 (by decide))).le.trans hcol))
        ((congrArg (fun v : ℕ => v+1) (hff 45 (by decide))).le.trans hcut)
    · exact hstate.inputHead
    · exact hstate.outputHead
    · exact hstate.inputMarked
    · exact hstate.outputMarked











theorem prefixValues_update {q m n : ℕ} (A : Gaussian.Table (Fin q) m n)
    (old : Fin (m*n) → ℕ) (cut : Fin (m*n)) :
    Function.update (prefixValues A old cut.val) cut (flatEntry A cut.val) =
      prefixValues A old (cut.val+1) := by
  funext j
  by_cases hj : j = cut
  · subst j;simp [prefixValues]
  · have hne : j.val ≠ cut.val := by intro he;exact hj (Fin.ext he)
    simp only [Function.update_of_ne hj,prefixValues]
    split_ifs <;> first | rfl | omega

theorem prefixStored_of_payload {q m n : ℕ} {A : Gaussian.Table (Fin q) m n}
    {old : Fin (m*n) → ℕ} {cut : ℕ} {d e : Store} {b : Fin 2}
    (ht : PrefixStored A old cut d b) (hp : TapeStore.SamePayload e d) : PrefixStored A old cut e b :=
  fun i => (ht i).of_payload hp

theorem prefixStored_written {q m n : ℕ} (A : Gaussian.Table (Fin q) m n)
    (old : Fin (m*n) → ℕ) (cut : Fin (m*n)) (d e : Store) (b : Fin 2)
    (ht : PrefixStored A old cut.val d b)
    (hw : TapeArrays.EntryWritten d e b (TapeArrays.entryOffset cut.val q) q (flatEntry A cut.val)) :
    PrefixStored A old (cut.val+1) e b := by
  have hv : flatEntry A cut.val ≤ q := by
    rw [flatEntry,dif_pos cut.isLt]
    exact Nat.le_of_lt (Fin.isLt _)
  have h := hw.table hv ht
  rw [prefixValues_update] at h
  exact h

theorem matrixStored_other_written {q m n : ℕ} {A : Gaussian.Table (Fin q) m n}
    {d e : Store} {input output : Fin 2} {start width value : ℕ}
    (ht : MatrixStored d input A) (hio : input ≠ output)
    (hw : TapeArrays.EntryWritten d e output start width value) : MatrixStored e input A := by
  intro i
  refine ⟨(ht i).1,?_⟩
  intro j hj
  rw [hw.symbol]
  simpa [hio] using (ht i).2 j hj

theorem prefixStored_complete {q m n : ℕ} {A : Gaussian.Table (Fin q) m n}
    {old : Fin (m*n) → ℕ} {d : Store} {b : Fin 2}
    (ht : PrefixStored A old (m*n) d b) : MatrixStored d b A := by
  intro i
  have h := ht i
  simpa [prefixValues,i.isLt] using h

























theorem columnLoop_stops {m n : ℕ} (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (A : Gaussian.Table (Fin (2^ell)) m n)
    (p : Fin m × Fin n) (i : Fin m) (old : Fin (m*n) → ℕ) (M : ℕ) (hsize : m*n ≤ M)
    (base : Store) (remaining : ℕ) (d : Store) (hd : d.reg 47 = remaining)
    (hi : ColumnInv ell h input output A p i old M base remaining d) :
    ∃ t e,t ≤ remaining*(tickBudget M+2)+1 ∧
      (columnLoop input output).Stops inp (d.toCfg (TapeProgram.loopHeader 1469)) t
        (e.toCfg (TapeProgram.loopExit 1469)) ∧
      ColumnInv ell h input output A p i old M base 0 e ∧ e.reg 47 = 0 := by
  apply countedLoop_stops_of_body (cellTick input output) 47 inp (tickBudget M)
    (ColumnInv ell h input output A p i old M base) _ remaining d hd hi
  intro r s hs47 hs
  let s₀ := TapeProgram.decStore (47 : Fin 64) s
  have hp : TapeStore.SamePayload s₀ s := TapeStore.setReg_payload s 47 (s.reg 47-1)
  have hsf (k : Fin 64) (hk : k ≠ 47) : s₀.reg k = s.reg k := by
    simp [s₀,TapeProgram.decStore,hk]
  have hs0b : ∀ k,s₀.reg k ≤ M :=
    FieldPrograms.setReg_bound s 47 (s.reg 47-1) M hs.state.bounded
      ((Nat.sub_le _ _).trans (hs.state.bounded 47))
  have hs0s : FieldSetup ell h s₀ := by
    simpa [FieldSetup,s₀,TapeProgram.decStore] using hs.state.setup
  have hj : s.reg 42 < n := by have := hs.columnCount;omega
  let j : Fin n := ⟨s.reg 42,hj⟩
  have hc : Coordinates p i j s₀ :=
    ⟨(hsf 41 (by decide)).trans hs.rowBase,hsf 42 (by decide),
      (hsf 43 (by decide)).trans hs.pivotColumn,(hsf 44 (by decide)).trans hs.pivotBase,
      by rw [hsf 45 (by decide),hs.cut]⟩
  have hnm : n ≤ M := by
    have hm : 1 ≤ m := by have := i.isLt;omega
    exact (calc n = 1*n := by omega
                _ ≤ m*n := Nat.mul_le_mul_right n hm).trans hsize
  have hcol : s₀.reg 42+1 ≤ M := by rw [hsf 42 (by decide)];omega
  have hidx : s.reg 45 < m*n := by
    rw [hs.cut]
    have hh := (finProdFinEquiv (i,j)).isLt
    change j.val+n*i.val < m*n at hh
    change s.reg 42+n*i.val < m*n at hh
    nlinarith
  have hcut : s₀.reg 45+1 ≤ M := by rw [hsf 45 (by decide)];omega
  obtain ⟨t,e,before,ht,he,hbefore,hew,he42,he45,heframe,hestate⟩ := cellTick_stops input output hio
    ell h inp A p i j s₀ M hs0s hs0b hsize hs.state.inputHead hs.state.outputHead
    (hs.state.inputMarked.of_payload hp) (hs.state.outputMarked.of_payload hp)
    (matrixStored_of_payload hs.inputStored hp) hc
    ((hsf 50 (by decide)).trans hs.inverse) hcol hcut
  have he47 : e.reg 47 = r := by
    rw [heframe 47 (by decide) (by decide) (by decide)]
    simp [s₀,TapeProgram.decStore,hs47]
  have he42' : e.reg 42 = s.reg 42+1 := he42.trans (congrArg (fun v : ℕ => v+1) (hsf 42 (by decide)))
  have he45' : e.reg 45 = s.reg 45+1 := he45.trans (congrArg (fun v : ℕ => v+1) (hsf 45 (by decide)))
  have hef (k : Fin 64) (hk : 40 ≤ k.val) (hk42 : k ≠ 42) (hk45 : k ≠ 45) (hk47 : k ≠ 47) :
      e.reg k = s.reg k := (heframe k hk hk42 hk45).trans (hsf k hk47)
  have hbp : TapeStore.SamePayload before s := hbefore.trans hp
  refine ⟨t,e,ht,he,he47,?_⟩
  refine {
    state:=hestate,
    columns:=(hef 40 (by decide) (by decide) (by decide) (by decide)).trans hs.columns,
    rows:=(hef 49 (by decide) (by decide) (by decide) (by decide)).trans hs.rows,
    rowBase:=(hef 41 (by decide) (by decide) (by decide) (by decide)).trans hs.rowBase,
    columnCount:=?_,
    pivotColumn:=(hef 43 (by decide) (by decide) (by decide) (by decide)).trans hs.pivotColumn,
    pivotBase:=(hef 44 (by decide) (by decide) (by decide) (by decide)).trans hs.pivotBase,
    cut:=?_,
    inverse:=(hef 50 (by decide) (by decide) (by decide) (by decide)).trans hs.inverse,
    inputStored:=matrixStored_other_written (matrixStored_of_payload hs.inputStored hbp) (Ne.symm hio) hew,
    written:=?_,frame:=?_,io:=?_}
  · change e.reg 42+r = n
    rw [he42']
    have := hs.columnCount
    omega
  · change e.reg 45 = i.val*n+e.reg 42
    rw [he45',he42',hs.cut]
    omega
  · let cut : Fin (m*n) := finProdFinEquiv (i,j)
    have hcutidx : cut.val = s.reg 45 := by
      change s.reg 42+n*i.val = s.reg 45
      rw [hs.cut]
      ring
    have hpref : PrefixStored (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
        old cut.val before output := by
      rw [hcutidx]
      exact prefixStored_of_payload hs.written hbp
    have hw : TapeArrays.EntryWritten before e.store output (TapeArrays.entryOffset cut.val (2^ell))
        (2^ell) (flatEntry (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p) cut.val) := by
      simpa only [cut,flatEntry_pair] using hew
    have hnew := prefixStored_written (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
      old cut before e.store output hpref hw
    rw [hcutidx] at hnew
    change PrefixStored (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
      old (e.reg 45) e.store output
    rw [he45']
    exact hnew
  · intro k hk hk42 hk45 hk47
    exact (hef k hk hk42 hk45 hk47).trans (hs.frame k hk hk42 hk45 hk47)
  · exact ⟨hew.roHead.trans (hbp.roHead.trans hs.io.1),hew.output.trans (hbp.output.trans hs.io.2)⟩



theorem state_setReg {ell : ℕ} {h : 0 < ell} {input output : Fin 2} {d : Store} {M : ℕ}
    (hs : SchurCellState ell h input output d M) (r : Fin 64) (v : ℕ)
    (h0 : r ≠ 0) (h36 : r ≠ 36) (h37 : r ≠ 37) (h38 : r ≠ 38) (hv : v ≤ M) :
    SchurCellState ell h input output (d.setReg r v) M := by
  constructor
  · simpa [FieldSetup,TapeStore.setReg,Ne.symm h0,Ne.symm h36,Ne.symm h37,Ne.symm h38] using hs.setup
  · exact FieldPrograms.setReg_bound d r v M hs.bounded hv
  · exact hs.inputHead
  · exact hs.outputHead
  · exact hs.inputMarked.of_payload (TapeStore.setReg_payload d r v)
  · exact hs.outputMarked.of_payload (TapeStore.setReg_payload d r v)







theorem rowPrepare_stops (inp : Inputs) (d : Store) :
    ∃ e,rowPrepare.Stops inp (d.toCfg rowPrepare.entry)
      (d.reg 42+d.reg 47+d.reg 4+5*d.reg 40+9) e ∧ e.store = rowPrepareStore d := by
  have hclear := TapeMacros.clear_stops (42 : Fin 64) inp (d.reg 42) d rfl
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops (40 : Fin 64) 47 4
    (by decide) (by decide) (by decide) inp (d.setReg 42 0)
  have hall := hclear.seq he
  refine ⟨e.mapPC (TapeProgram.rightLabel 2),?_,?_⟩
  · convert hall using 1 <;> first | rfl | (simp [TapeStore.setReg];omega)
  · change e.store = _
    simpa [rowPrepareStore,TapeStore.setReg] using hes

theorem rowPrepare_frame (d : Store) (r : Fin 64) (hr : 40 ≤ r.val) (hr42 : r ≠ 42) (hr47 : r ≠ 47) :
    (rowPrepareStore d).reg r = d.reg r := by
  have h4 : r ≠ 4 := by intro he;subst r;norm_num at hr
  simp [rowPrepareStore,TapeStore.setReg,hr42,hr47,h4]











































theorem rowBody_stops {m n : ℕ} (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (A : Gaussian.Table (Fin (2^ell)) m n)
    (p : Fin m × Fin n) (i : Fin m) (old : Fin (m*n) → ℕ) (M : ℕ) (hsize : m*n ≤ M)
    (d : Store) (hi : RowStart ell h input output A p i old M d) :
    ∃ t e,t ≤ rowBudget n M ∧
      (rowBody input output).Stops inp (d.toCfg (rowBody input output).entry) t e ∧
      RowOutcome ell h input output A p i old M d e.store := by
  obtain ⟨c,hc,hcs⟩ := rowPrepare_stops inp d
  have hcp : TapeStore.SamePayload c.store d := by
    rw [hcs]
    exact (TapeStore.setReg_payload _ 4 0).trans
      ((TapeStore.setReg_payload _ 47 (d.reg 40)).trans (TapeStore.setReg_payload d 42 0))
  have hcf (r : Fin 64) (hr : 40 ≤ r.val) (hr42 : r ≠ 42) (hr47 : r ≠ 47) : c.reg r = d.reg r := by
    change c.store.reg r = _
    rw [hcs]
    exact rowPrepare_frame d r hr hr42 hr47
  have hcstate : SchurCellState ell h input output c.store M := by
    rw [hcs]
    exact state_setReg (state_setReg (state_setReg hi.state 42 0 (by decide) (by decide) (by decide) (by decide)
      (Nat.zero_le M)) 47 (d.reg 40) (by decide) (by decide) (by decide) (by decide) (hi.state.bounded 40))
      4 0 (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)
  have hc42 : c.reg 42 = 0 := by change c.store.reg 42 = _;rw [hcs];simp [rowPrepareStore,TapeStore.setReg]
  have hc47 : c.reg 47 = n := by change c.store.reg 47 = _;rw [hcs];simp [rowPrepareStore,TapeStore.setReg,hi.columns]
  have hInit : ColumnInv ell h input output A p i old M d n c.store := by
    refine {
      state:=hcstate,
      columns:=(hcf 40 (by decide) (by decide) (by decide)).trans hi.columns,
      rows:=(hcf 49 (by decide) (by decide) (by decide)).trans hi.rows,
      rowBase:=(hcf 41 (by decide) (by decide) (by decide)).trans hi.rowBase,
      columnCount:=by simpa only [hc42,Nat.zero_add],
      pivotColumn:=(hcf 43 (by decide) (by decide) (by decide)).trans hi.pivotColumn,
      pivotBase:=(hcf 44 (by decide) (by decide) (by decide)).trans hi.pivotBase,
      cut:=?_,inverse:=(hcf 50 (by decide) (by decide) (by decide)).trans hi.inverse,
      inputStored:=matrixStored_of_payload hi.inputStored hcp,written:=?_,frame:=?_,io:=⟨hcp.roHead,hcp.output⟩}
    · change c.reg 45 = i.val*n+c.reg 42
      rw [hcf 45 (by decide) (by decide) (by decide),hi.cut,hc42]
      omega
    · change PrefixStored (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p)
        old (c.reg 45) c.store output
      rw [hcf 45 (by decide) (by decide) (by decide),hi.cut]
      exact prefixStored_of_payload hi.written hcp
    · intro r hr hr42 hr45 hr47
      exact hcf r hr hr42 hr47
  obtain ⟨s,f,hs,hf,hfo,hf47⟩ := columnLoop_stops input output hio ell h inp A p i old M hsize d n c.store hc47 hInit
  have hf42 : f.reg 42 = n := by have := hfo.columnCount;omega
  have hf41 : f.reg 41 = i.val*n := hfo.rowBase
  have hf40 : f.reg 40 = n := hfo.columns
  have hf45 : f.reg 45 = (i.val+1)*n := by rw [hfo.cut,hf42];ring
  have hsum : f.reg 41+f.reg 40 ≤ M := by
    rw [hf41,hf40]
    have hp := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
    nlinarith
  obtain ⟨e,he,hes⟩ := TapeMacros.addPreserving_stops (40 : Fin 64) 41 4
    (by decide) (by decide) (by decide) inp f
  have her : e.reg = ((f.setReg 41 (f.reg 41+f.reg 40)).setReg 4 0).reg := congrArg TapeStore.reg hes
  have hep : TapeStore.SamePayload e.store f := by
    rw [hes]
    exact (TapeStore.setReg_payload _ 4 0).trans (TapeStore.setReg_payload f 41 (f.reg 41+f.reg 40))
  have hef (r : Fin 64) (hr : 40 ≤ r.val) (hr41 : r ≠ 41) : e.reg r = f.reg r := by
    rw [her]
    have h4 : r ≠ 4 := by intro he;subst r;norm_num at hr
    simp [TapeStore.setReg,hr41,h4]
  have hall := hc.seq (hf.seq he)
  refine ⟨_,_,?_,hall,?_⟩
  · have ht₁ : d.reg 42+d.reg 47+d.reg 4+5*d.reg 40+9 ≤ 8*M+9 := by
      have := hi.state.bounded 42;have := hi.state.bounded 47;have := hi.state.bounded 4;have := hi.state.bounded 40;omega
    have ht₂ : f.reg 4+5*f.reg 40+5 ≤ 6*M+5 := by
      have := hfo.state.bounded 4;have := hfo.state.bounded 40;omega
    unfold rowBudget
    omega
  · change RowOutcome ell h input output A p i old M d e.store
    refine {
      state:=?_,columns:=(hef 40 (by decide) (by decide)).trans hfo.columns,
      rows:=(hef 49 (by decide) (by decide)).trans hfo.rows,nextBase:=?_,nextCut:=?_,
      pivotColumn:=(hef 43 (by decide) (by decide)).trans hfo.pivotColumn,
      pivotBase:=(hef 44 (by decide) (by decide)).trans hfo.pivotBase,
      inverse:=(hef 50 (by decide) (by decide)).trans hfo.inverse,
      inputStored:=matrixStored_of_payload hfo.inputStored hep,written:=?_,
      columnDone:=(hef 42 (by decide) (by decide)).trans hf42,
      countDone:=(hef 47 (by decide) (by decide)).trans hf47,frame:=?_,
      io:=⟨hep.roHead.trans hfo.io.1,hep.output.trans hfo.io.2⟩}
    · rw [hes]
      exact state_setReg (state_setReg hfo.state 41 (f.reg 41+f.reg 40)
        (by decide) (by decide) (by decide) (by decide) hsum)
        4 0 (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)
    · change e.reg 41 = _
      rw [her]
      simp [TapeStore.setReg,hf41,hf40,Nat.add_mul]
    · exact (hef 45 (by decide) (by decide)).trans hf45
    · have hh := prefixStored_of_payload hfo.written hep
      rw [hf45] at hh
      exact hh
    · intro r hr hr41 hr42 hr45 hr47
      exact (hef r hr hr41).trans (hfo.frame r hr hr42 hr45 hr47)
























theorem rowLoop_stops {m n : ℕ} (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (A : Gaussian.Table (Fin (2^ell)) m n)
    (p : Fin m × Fin n) (old : Fin (m*n) → ℕ) (M : ℕ) (hsize : m*n ≤ M)
    (base : Store) (remaining : ℕ) (d : Store) (hd : d.reg 46 = remaining)
    (hi : RowsInv ell h input output A p old M base remaining d) :
    ∃ t e,t ≤ remaining*(rowBudget n M+2)+1 ∧
      (rowLoop input output).Stops inp (d.toCfg (TapeProgram.loopHeader 1493)) t
        (e.toCfg (TapeProgram.loopExit 1493)) ∧
      RowsInv ell h input output A p old M base 0 e ∧ e.reg 46 = 0 := by
  apply countedLoop_stops_of_body (rowBody input output) 46 inp (rowBudget n M)
    (RowsInv ell h input output A p old M base) _ remaining d hd hi
  intro r s hs46 hs
  let s₀ := TapeProgram.decStore (46 : Fin 64) s
  have hp : TapeStore.SamePayload s₀ s := TapeStore.setReg_payload s 46 (s.reg 46-1)
  have hsf (k : Fin 64) (hk : k ≠ 46) : s₀.reg k = s.reg k := by simp [s₀,TapeProgram.decStore,hk]
  have hj : m-(r+1) < m := by have := hs.atMost;omega
  let i : Fin m := ⟨m-(r+1),hj⟩
  have hstart : RowStart ell h input output A p i old M s₀ := by
    refine {
      state:=state_setReg hs.state 46 (s.reg 46-1) (by decide) (by decide) (by decide) (by decide)
        ((Nat.sub_le _ _).trans (hs.state.bounded 46)),
      columns:=(hsf 40 (by decide)).trans hs.columns,
      rows:=(hsf 49 (by decide)).trans hs.rows,
      rowBase:=(hsf 41 (by decide)).trans hs.rowBase,
      cut:=(hsf 45 (by decide)).trans hs.cut,
      pivotColumn:=(hsf 43 (by decide)).trans hs.pivotColumn,
      pivotBase:=(hsf 44 (by decide)).trans hs.pivotBase,
      inverse:=(hsf 50 (by decide)).trans hs.inverse,
      inputStored:=matrixStored_of_payload hs.inputStored hp,
      written:=prefixStored_of_payload hs.written hp}
  obtain ⟨t,e,ht,he,ho⟩ := rowBody_stops input output hio ell h inp A p i old M hsize s₀ hstart
  have he46 : e.reg 46 = r := by
    change e.store.reg 46 = r
    rw [ho.frame 46 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s₀,TapeProgram.decStore,hs46]
  have hnext : (i.val+1)*n = (m-r)*n := by
    have heq : i.val+1 = m-r := by change m-(r+1)+1 = m-r;have := hs.atMost;omega
    rw [heq]
  refine ⟨t,e,ht,he,he46,?_⟩
  refine {
    atMost:=by have := hs.atMost;omega,
    state:=ho.state,columns:=ho.columns,rows:=ho.rows,
    rowBase:=ho.nextBase.trans hnext,cut:=ho.nextCut.trans hnext,
    pivotColumn:=ho.pivotColumn,pivotBase:=ho.pivotBase,inverse:=ho.inverse,
    inputStored:=ho.inputStored,written:=?_,frame:=?_,
    io:=⟨ho.io.1.trans (hp.roHead.trans hs.io.1),ho.io.2.trans (hp.output.trans hs.io.2)⟩}
  · simpa only [hnext] using ho.written
  · intro k hk hk41 hk42 hk45 hk46 hk47
    exact ((ho.frame k hk hk41 hk42 hk45 hk47).trans (hsf k hk46)).trans
      (hs.frame k hk hk41 hk42 hk45 hk46 hk47)







theorem gridPrepare_stops (inp : Inputs) (d : Store) :
    ∃ e,gridPrepare.Stops inp (d.toCfg gridPrepare.entry)
      (d.reg 41+d.reg 45+d.reg 46+d.reg 4+5*d.reg 49+11) e ∧ e.store = gridPrepareStore d := by
  have h₁ := TapeMacros.clear_stops (41 : Fin 64) inp (d.reg 41) d rfl
  have h₂ := TapeMacros.clear_stops (45 : Fin 64) inp (d.reg 45) (d.setReg 41 0) (by simp [TapeStore.setReg])
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops (49 : Fin 64) 46 4 (by decide) (by decide) (by decide)
    inp ((d.setReg 41 0).setReg 45 0)
  have hall := h₁.seq (h₂.seq he)
  refine ⟨(e.mapPC (TapeProgram.rightLabel 2)).mapPC (TapeProgram.rightLabel 2),?_,?_⟩
  · convert hall using 1 <;> first | rfl | (simp [TapeStore.setReg];omega)
  · change e.store = _
    simpa [gridPrepareStore,TapeStore.setReg] using hes

theorem gridPrepare_frame (d : Store) (r : Fin 64) (hr : 40 ≤ r.val)
    (hr41 : r ≠ 41) (hr45 : r ≠ 45) (hr46 : r ≠ 46) : (gridPrepareStore d).reg r = d.reg r := by
  have h4 : r ≠ 4 := by intro he;subst r;norm_num at hr
  simp [gridPrepareStore,TapeStore.setReg,h4,hr41,hr45,hr46]




theorem materializeGrid_stops {m n : ℕ} (input output : Fin 2) (hio : output ≠ input)
    (ell : ℕ) (h : 0 < ell) (inp : Inputs) (A : Gaussian.Table (Fin (2^ell)) m n)
    (p : Fin m × Fin n) (old : Fin (m*n) → ℕ) (M : ℕ) (hsize : m*n ≤ M) (d : Store)
    (hstate : SchurCellState ell h input output d M)
    (hcols : d.reg 40 = n) (hrows : d.reg 49 = m)
    (hpc : d.reg 43 = p.2.val) (hpr : d.reg 44 = p.1.val*n)
    (hInv : d.reg 50 = ((PolynomialStretch.BinaryField.indexOperations ell h).inv
      (Gaussian.toMatrix A p.1 p.2)).val)
    (hinput : MatrixStored d input A) (houtput : TapeArrays.ThermometerTable d output (2^ell) old) :
    ∃ t e,t ≤ 20*(M+1)+m*(rowBudget n M+2)+2 ∧
      (materializeGrid input output).Stops inp (d.toCfg (materializeGrid input output).entry) t e ∧
      SchurCellState ell h input output e.store M ∧ MatrixStored e.store input A ∧
      MatrixStored e.store output (paddedSchur (PolynomialStretch.BinaryField.indexOperations ell h) A p) ∧
      e.reg 41 = m*n ∧ e.reg 45 = m*n ∧ e.reg 46 = 0 ∧
      (∀ r,40 ≤ r.val → r ≠ 41 → r ≠ 42 → r ≠ 45 → r ≠ 46 → r ≠ 47 → e.reg r = d.reg r) ∧
      e.roHead = d.roHead ∧ e.output = d.output := by
  obtain ⟨c,hc,hcs⟩ := gridPrepare_stops inp d
  have hcp : TapeStore.SamePayload c.store d := by
    rw [hcs]
    exact (TapeStore.setReg_payload _ 4 0).trans ((TapeStore.setReg_payload _ 46 (d.reg 49)).trans
      ((TapeStore.setReg_payload _ 45 0).trans (TapeStore.setReg_payload d 41 0)))
  have hcf (r : Fin 64) (hr : 40 ≤ r.val) (hr41 : r ≠ 41) (hr45 : r ≠ 45) (hr46 : r ≠ 46) :
      c.reg r = d.reg r := by change c.store.reg r = _;rw [hcs];exact gridPrepare_frame d r hr hr41 hr45 hr46
  have hc41 : c.reg 41 = 0 := by change c.store.reg 41 = _;rw [hcs];simp [gridPrepareStore,TapeStore.setReg]
  have hc45 : c.reg 45 = 0 := by change c.store.reg 45 = _;rw [hcs];simp [gridPrepareStore,TapeStore.setReg]
  have hc46 : c.reg 46 = m := by change c.store.reg 46 = _;rw [hcs];simp [gridPrepareStore,TapeStore.setReg,hrows]
  have hcstate : SchurCellState ell h input output c.store M := by
    rw [hcs]
    exact state_setReg (state_setReg (state_setReg (state_setReg hstate 41 0 (by decide) (by decide) (by decide) (by decide)
      (Nat.zero_le M)) 45 0 (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M))
      46 (d.reg 49) (by decide) (by decide) (by decide) (by decide) (hstate.bounded 49))
      4 0 (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)
  have hInit : RowsInv ell h input output A p old M d m c.store := by
    refine {
      atMost:=le_rfl,state:=hcstate,
      columns:=(hcf 40 (by decide) (by decide) (by decide) (by decide)).trans hcols,
      rows:=(hcf 49 (by decide) (by decide) (by decide) (by decide)).trans hrows,
      rowBase:=by simpa only [Nat.sub_self,Nat.zero_mul] using hc41,
      cut:=by simpa only [Nat.sub_self,Nat.zero_mul] using hc45,
      pivotColumn:=(hcf 43 (by decide) (by decide) (by decide) (by decide)).trans hpc,
      pivotBase:=(hcf 44 (by decide) (by decide) (by decide) (by decide)).trans hpr,
      inverse:=(hcf 50 (by decide) (by decide) (by decide) (by decide)).trans hInv,
      inputStored:=matrixStored_of_payload hinput hcp,written:=?_,frame:=?_,io:=⟨hcp.roHead,hcp.output⟩}
    · have hout : TapeArrays.ThermometerTable c.store output (2^ell) old := fun j => (houtput j).of_payload hcp
      intro k
      simpa [prefixValues] using hout k
    · intro r hr hr41 hr42 hr45 hr46 hr47
      exact hcf r hr hr41 hr45 hr46
  obtain ⟨s,e,hs,he,ho,he46⟩ := rowLoop_stops input output hio ell h inp A p old M hsize d m c.store hc46 hInit
  have hall := hc.seq he
  refine ⟨_,_,?_,hall,ho.state,ho.inputStored,?_,?_,?_,he46,ho.frame,ho.io.1,ho.io.2⟩
  · have ht : d.reg 41+d.reg 45+d.reg 46+d.reg 4+5*d.reg 49+11 ≤ 20*(M+1) := by
      have := hstate.bounded 41;have := hstate.bounded 45;have := hstate.bounded 46
      have := hstate.bounded 4;have := hstate.bounded 49;omega
    omega
  · apply prefixStored_complete
    simpa only [Nat.sub_zero] using ho.written
  · simpa only [Nat.sub_zero] using ho.rowBase
  · simpa only [Nat.sub_zero] using ho.cut



end ExpandingCodes.Computation.GaussianGrid

end FlattenModule85

/-! Inlined whole module: ExpandingCodes.Computation.GaussianPivot -/
section FlattenModule86



set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianPivot
open NKtLB GaussianProgram
open ExpandingCodes.PolynomialStretch






set_option maxRecDepth 10000 in
theorem inverseLayout_injective : Function.Injective inverseLayout := by decide

set_option maxRecDepth 10000 in
theorem inverseLayout_frame : ∀ r : Fin 64, 40 ≤ r.val → r ≠ 50 →
    ∀ i : Fin 31, r ≠ inverseLayout i := by decide













/-- The actual 418-label exhaustive finite-field inverse routine, physically
mapped into the Gaussian driver's fixed register frame. -/
theorem invertPivot_stops (ell : ℕ) (h : 0 < ell) (inp : Inputs)
    (d : Store) (M : ℕ) (hs : FieldSetup ell h d) (hd : ∀ r, d.reg r ≤ M)
    (a : Fin (2^ell)) (ha : d.reg 6 = a.val) :
    ∃ t e, t ≤ 20000*(M+1)^7 ∧
      invertPivot.Stops inp (d.toCfg invertPivot.entry) t e ∧
      InverseOutcome ell h a d e.store M := by
  rcases hs with ⟨hq,hQ,hN,hm⟩
  have hM : 1 ≤ M := by
    have hp : 0 < 2^ell := pow_pos (by decide) ell
    have hb := hd 0
    omega
  have hi : SourceFieldArithmetic.InverseSetup inverseLayout ell h a d :=
    ⟨ha,hm,hN,hq,hQ⟩
  obtain ⟨t,e,ht,he,_,hv,hinput,houtside,hbound,htape⟩ := SourceFieldArithmetic.inverse_stops
    inverseLayout inverseLayout_injective inp ell h a M hM d hd hi
  refine ⟨t,e,ht,he,?_⟩
  have hro : e.store.roHead = d.roHead := congrArg Prod.fst htape
  have houtput : e.store.output = d.output := congrArg (fun x => x.2.1) htape
  have hbuffer : e.store.bufferTape = d.bufferTape := congrArg (fun x => x.2.2.1) htape
  have hheads : e.store.bufferHead = d.bufferHead := congrArg (fun x => x.2.2.2) htape
  refine ⟨hv,hinput 0 (by simp),?_,?_,hbound,⟨hro,houtput,?_⟩,hheads⟩
  · refine ⟨?_,?_,?_,?_⟩
    · exact (hinput 23 (by simp)).trans hq
    · exact (hinput 24 (by simp)).trans hQ
    · exact (hinput 19 (by simp)).trans hN
    · exact (hinput 3 (by simp)).trans hm
  · intro r hr hr₅₀
    exact houtside r (inverseLayout_frame r hr hr₅₀)
  · intro b k
    rw [hbuffer]



theorem coordinateDigits_nodup :
    ((40 : Fin 64)::59::SamplerOdometer.used coordinateDigits).Nodup := by decide







set_option maxRecDepth 10000 in
theorem coordinateStep_fresh : coordinateStep.Fresh 55 := by
  unfold TapeProgram.Fresh
  letI (j : Fin 43) : Decidable (TapeProgram.preservesRegister 55 (coordinateStep.code j)) :=
    decidablePreserves 55 (coordinateStep.code j)
  decide








theorem coordinateOutside (r : Fin 64) (hr : OutsideCoordinates r) :
    r ≠ 59 ∧ r ∉ SamplerOdometer.used coordinateDigits ∧ r ≠ 55 ∧ r ≠ 58 := by
  simp only [OutsideCoordinates,coordinateDigits,SamplerOdometer.used,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at hr ⊢
  tauto











theorem coordinateInvariant_dec (base : Store) (M remaining : ℕ) (s : Store)
    (hi : CoordinateInvariant base M remaining s) :
    CoordinateInvariant base M remaining (TapeProgram.decStore 55 s) := by
  refine ⟨hi.remaining_le,?_,?_,?_,?_,?_,hi.payload⟩
  · intro r
    by_cases hr : r = 55
    · subst r
      simpa [TapeProgram.decStore] using (Nat.sub_le (s.reg 55) 1).trans (hi.bounded 55)
    · simpa [TapeProgram.decStore,hr] using hi.bounded r
  · simpa [SamplerOdometer.Valid,coordinateDigits,TapeProgram.decStore] using hi.valid
  · simpa [TapeProgram.decStore] using hi.radix
  · simpa [SamplerOdometer.readings,coordinateDigits,TapeProgram.decStore] using hi.number
  · intro r hr
    simpa [TapeProgram.decStore,(coordinateOutside r hr).2.2.1] using hi.frame r hr

theorem coordinateInvariant_next (base : Store) (M n : ℕ) (s : Store)
    (hq : 1 < base.reg 40) (hflat : base.reg 2 < (base.reg 40)^2)
    (hi : CoordinateInvariant base M (n+1) s) :
    CoordinateInvariant base M n (SamplerOdometer.nextStore 40 59 coordinateDigits s) := by
  have hq' : 1 < s.reg 40 := by rw [hi.radix]; exact hq
  have hnumber := SamplerOdometer.program_number 40 59 coordinateDigits coordinateDigits_nodup s hi.valid hq'
  have hnew : base.reg 2-(n+1)+1 = base.reg 2-n := by have := hi.remaining_le; omega
  have hnewlt : base.reg 2-(n+1)+1 < (base.reg 40)^2 := by have := hi.remaining_le; omega
  have hfinallt : base.reg 2-n < (base.reg 40)^2 := (Nat.sub_le _ _).trans_lt hflat
  have hvalue : Nat.ofDigits (base.reg 40)
      (SamplerOdometer.readings coordinateDigits (SamplerOdometer.nextStore 40 59 coordinateDigits s)) =
        base.reg 2-n := by
    rw [hi.radix,hi.number] at hnumber
    simpa only [coordinateDigits,List.length_cons,List.length_nil,Nat.zero_add,
      Nat.reduceAdd,Nat.mod_eq_of_lt hnewlt,hnew,Nat.mod_eq_of_lt hfinallt] using hnumber
  have hdata : FieldConvolution.tapeData (SamplerOdometer.nextStore 40 59 coordinateDigits s) =
      FieldConvolution.tapeData s := by
    obtain ⟨hr,ho,hb,hh⟩ := SamplerOdometer.nextStore_payload 40 59 coordinateDigits s
    exact Prod.ext hr (Prod.ext ho (Prod.ext hb hh))
  refine ⟨by have := hi.remaining_le; omega,
    SamplerOdometer.nextStore_bound 40 59 coordinateDigits coordinateDigits_nodup s hi.valid M hi.bounded,
    SamplerOdometer.program_valid 40 59 coordinateDigits coordinateDigits_nodup s hi.valid,
    ?_,hvalue,?_,hdata.trans hi.payload⟩
  · exact (SamplerOdometer.nextStore_fresh 40 59 coordinateDigits s 40 (by decide) (by decide)).trans hi.radix
  · intro r hr
    rw [SamplerOdometer.nextStore_fresh 40 59 coordinateDigits s r
      (coordinateOutside r hr).1 (coordinateOutside r hr).2.1]
    exact hi.frame r hr

theorem coordinateLoop_stops (base : Store) (M n : ℕ) (s : Store) (inp : Inputs)
    (hq : 1 < base.reg 40) (hflat : base.reg 2 < (base.reg 40)^2)
    (hi : CoordinateInvariant base M n s) (hn : s.reg 55 = n) :
    ∃ t e, t ≤ n*(2*(8*M+20)+2)+1 ∧
      (TapeProgram.countedLoop coordinateStep 55).Stops inp
        (s.toCfg (TapeProgram.loopHeader 43)) t (e.toCfg (TapeProgram.loopExit 43)) ∧
      CoordinateInvariant base M 0 e ∧ e.reg 55 = 0 := by
  apply TapeProgram.countedLoop_stops coordinateStep 55 coordinateStep_fresh inp
    (2*(8*M+20)) (CoordinateInvariant base M)
  · intro m d _ hd
    have hd₁ := coordinateInvariant_dec base M (m+1) d hd
    obtain ⟨t,c,ht,hc,hcs,hb⟩ := SamplerOdometer.program_stops_valid
      40 59 coordinateDigits coordinateDigits_nodup inp M (TapeProgram.decStore 55 d) hd₁.bounded hd₁.valid
    refine ⟨t,c,?_,hc,?_⟩
    · simpa [coordinateDigits] using ht
    · rw [hcs]
      exact coordinateInvariant_next base M m _ hq hflat hd₁
  · exact hn
  · exact hi







private theorem initialize_bound {R B : ℕ} (q tmp : Fin R)
    (ps : List (SamplerOdometer.Digit R)) (d : TapeStore R B) (M : ℕ)
    (hd : ∀ r, d.reg r ≤ M) :
    ∀ r, (SamplerOdometer.initializeStore q tmp ps d).reg r ≤ M := by
  induction ps generalizing d with
  | nil => exact hd
  | cons p ps ih => exact ih _ (SamplerOdometer.resetStore_bound q tmp p d M hd)

theorem coordinateInit_frame (d : Store) (r : Fin 64) (hr : OutsideCoordinates r) :
    (coordinateInitStore d).reg r = d.reg r := by
  have h := coordinateOutside r hr
  simp only [coordinateInitStore,TapeStore.setReg,Function.update_of_ne h.2.2.2,
    Function.update_of_ne h.2.2.1]
  exact SamplerOdometer.initializeStore_fresh 40 59 coordinateDigits d r h.1 h.2.1

theorem coordinateInit_invariant (d : Store) (M : ℕ) (hd : ∀ r, d.reg r ≤ M)
    (hq : 1 < d.reg 40) : CoordinateInvariant d M (d.reg 2) (coordinateInitStore d) := by
  refine ⟨le_rfl,?_,?_,coordinateInit_frame d 40 (by decide),?_,coordinateInit_frame d,rfl⟩
  · exact FieldPrograms.setReg_bound _ 58 0 M
      (FieldPrograms.setReg_bound _ 55 (d.reg 2) M
        (initialize_bound 40 59 coordinateDigits d M hd) (hd 2)) (Nat.zero_le _)
  · simp [SamplerOdometer.Valid,coordinateInitStore,coordinateDigits,
      SamplerOdometer.initializeStore,SamplerOdometer.resetStore,TapeStore.setReg]
    omega
  · simp [coordinateInitStore,coordinateDigits,SamplerOdometer.readings,
      SamplerOdometer.initializeStore,SamplerOdometer.resetStore,TapeStore.setReg,Nat.ofDigits_cons]

theorem coordinateInit_count (d : Store) : (coordinateInitStore d).reg 55 = d.reg 2 := by
  simp [coordinateInitStore,TapeStore.setReg]

theorem coordinateInit_stops (d : Store) (inp : Inputs) (M : ℕ) (hd : ∀ r, d.reg r ≤ M) :
    ∃ t e, t ≤ 64*(M+1) ∧ coordinateInit.Stops inp (d.toCfg coordinateInit.entry) t e ∧
      e.store = coordinateInitStore d := by
  obtain ⟨s,c,hs,hc,hcs,hb⟩ := SamplerOdometer.initialize_stops
    40 59 coordinateDigits coordinateDigits_nodup inp M d hd
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops (B := 2) (2 : Fin 64) 55 58
    (by decide) (by decide) (by decide) inp c.store
  have hindex : c.store.reg 2 = d.reg 2 := by
    rw [hcs]
    exact SamplerOdometer.initializeStore_fresh 40 59 coordinateDigits d 2 (by decide) (by decide)
  refine ⟨s+1+(c.reg 55+c.reg 58+5*c.reg 2+7),e.mapPC (TapeProgram.rightLabel 31),?_,?_,?_⟩
  · have h55 := hb 55
    have h58 := hb 58
    have h2 := hb 2
    simp only [coordinateDigits,List.length_cons,List.length_nil,Nat.reduceAdd] at hs
    omega
  · convert hc.seq he using 1 <;> rfl
  · change e.store = _
    rw [hes,hindex,hcs]
    rfl



















theorem coordinates_stops (d : Store) (inp : Inputs) (M : ℕ)
    (hd : ∀ r, d.reg r ≤ M) (hq : 1 < d.reg 40) (hflat : d.reg 2 < (d.reg 40)^2) :
    ∃ t e, t ≤ 256*(M+1)^2 ∧ coordinates.Stops inp (d.toCfg coordinates.entry) t e ∧
      CoordinateOutcome d e.store M := by
  obtain ⟨s,c,hs,hc,hcs⟩ := coordinateInit_stops d inp M hd
  have hInv : CoordinateInvariant d M (d.reg 2) c.store := by
    rw [hcs]
    exact coordinateInit_invariant d M hd hq
  have hcount : c.store.reg 55 = d.reg 2 := by rw [hcs,coordinateInit_count]
  obtain ⟨t,f,ht,hf,hfi,hfz⟩ := coordinateLoop_stops d M (d.reg 2) c.store inp hq hflat hInv hcount
  have hlow : f.reg 43 < d.reg 40 := by
    have hh := hfi.valid (43,52) (by simp [coordinateDigits])
    rw [hfi.radix] at hh
    change f.reg 43+f.reg 52+1 = d.reg 40 at hh
    omega
  have hnumber : f.reg 43+d.reg 40*f.reg 53 = d.reg 2 := by
    simpa [SamplerOdometer.readings,coordinateDigits,Nat.ofDigits_cons] using hfi.number
  have hcol : f.reg 43 = d.reg 2 % d.reg 40 := by
    rw [← hnumber]
    simp [Nat.add_mod,Nat.mod_eq_of_lt hlow]
  have hrow : f.reg 53 = d.reg 2 / d.reg 40 := by
    rw [← hnumber,Nat.add_mul_div_left _ _ (by omega : 0 < d.reg 40),Nat.div_eq_of_lt hlow,zero_add]
  obtain ⟨u,e,hu,he,hes⟩ := UnaryArithmetic.multiply_stops_polynomial
    (B := 2) (53 : Fin 64) 40 44 56 57 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) inp f M
    (hfi.bounded 53) (hfi.bounded 40) (hfi.bounded 44) (hfi.bounded 56) (hfi.bounded 57)
  have hall := (hc.seq hf).seq he
  refine ⟨s+1+t+1+u,e.mapPC (TapeProgram.rightLabel 87),?_,?_,?_⟩
  · have ht' := ht.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_right (2*(8*M+20)+2) (hd 2)) 1)
    nlinarith
  · convert hall using 1 <;> rfl
  · have hprod : f.reg 53*f.reg 40 ≤ M := by
      rw [hfi.radix]
      have hh := hd 2
      nlinarith
    refine ⟨?_,?_,?_,?_,?_⟩
    · change e.store.reg 43 = _
      rw [hes]
      simpa [UnaryArithmetic.multiplyStore,TapeStore.setReg] using hcol
    · change e.store.reg 44 = _
      rw [hes]
      simp [UnaryArithmetic.multiplyStore,TapeStore.setReg,hrow,hfi.radix]
    · intro r hr
      change e.store.reg r = _
      rw [hes]
      simpa [UnaryArithmetic.multiplyStore,TapeStore.setReg,hr.2.1,hr.2.2.1,hr.2.2.2] using hfi.frame r hr.1
    · change ∀ r, e.store.reg r ≤ M
      rw [hes]
      exact FieldPrograms.setReg_bound _ _ 0 M
        (FieldPrograms.setReg_bound _ _ 0 M
          (FieldPrograms.setReg_bound _ _ (f.reg 53*f.reg 40) M hfi.bounded hprod) (Nat.zero_le _)) (Nat.zero_le _)
    · change FieldConvolution.tapeData e.store = _
      rw [hes]
      exact hfi.payload

















theorem preparePivot_stops (ell : ℕ) (h : 0 < ell) (d : Store) (inp : Inputs) (M : ℕ)
    (hs : FieldSetup ell h d) (hd : ∀ r, d.reg r ≤ M)
    (hq : 1 < d.reg 40) (hflat : d.reg 2 < (d.reg 40)^2)
    (a : Fin (2^ell)) (ha : d.reg 6 = a.val) :
    ∃ t e, t ≤ 21000*(M+1)^7 ∧ preparePivot.Stops inp (d.toCfg preparePivot.entry) t e ∧
      PivotOutcome ell h a d e.store M := by
  obtain ⟨t,c,ht,hc,hco⟩ := coordinates_stops d inp M hd hq hflat
  have hsetup : FieldSetup ell h c.store := by
    rcases hs with ⟨h0,h36,h37,h38⟩
    exact ⟨(hco.frame 0 (by decide)).trans h0,(hco.frame 36 (by decide)).trans h36,
      (hco.frame 37 (by decide)).trans h37,(hco.frame 38 (by decide)).trans h38⟩
  have hvalue : c.store.reg 6 = a.val := (hco.frame 6 (by decide)).trans ha
  obtain ⟨s,e,hs,he,heo⟩ := invertPivot_stops ell h inp c.store M hsetup hco.bounded a hvalue
  refine ⟨t+1+s,e.mapPC (TapeProgram.rightLabel 111),?_,?_,?_⟩
  · have hp : (M+1)^2 ≤ (M+1)^7 := Nat.pow_le_pow_right (by omega) (by decide)
    have hpos : 1 ≤ (M+1)^7 := one_le_pow₀ (by omega)
    nlinarith
  · convert hc.seq he using 1 <;> rfl
  · have hro : c.store.roHead = d.roHead := congrArg Prod.fst hco.payload
    have houtput : c.store.output = d.output := congrArg (fun x => x.2.1) hco.payload
    have hbuffer : c.store.bufferTape = d.bufferTape := congrArg (fun x => x.2.2.1) hco.payload
    have hheads : c.store.bufferHead = d.bufferHead := congrArg (fun x => x.2.2.2) hco.payload
    have hcp : TapeStore.SamePayload c.store d := ⟨hro,houtput,fun b k => by rw [hbuffer]⟩
    refine ⟨(heo.frame 43 (by decide) (by decide)).trans hco.col,
      (heo.frame 44 (by decide) (by decide)).trans hco.rowBase,heo.value,heo.setup,
      ?_,heo.bounded,heo.payload.trans hcp,heo.heads.trans hheads,
      heo.pivot.trans (hco.frame 6 (by decide))⟩
    intro r hr hrC hr50
    exact (heo.frame r hr hr50).trans (hco.frame r hrC)





end ExpandingCodes.Computation.GaussianPivot

end FlattenModule86

/-! Inlined whole module: ExpandingCodes.Computation.PaddedGaussian -/
section FlattenModule87



set_option autoImplicit false

namespace ExpandingCodes.Computation.PaddedGaussian
open GaussianProgram EncodedGaussian
open ExpandingCodes.PolynomialStretch

variable {q m n : ℕ}















theorem pivot_none_iff (A : Gaussian.Table (Fin q) m n) :
    pivot A = none ↔ (scanResult (flatEntry A) 0 (m*n)).2 = 0 := by
  by_cases hz : (scanResult (flatEntry A) 0 (m*n)).2 = 0 <;> simp [pivot,hz]

theorem pivot_some_iff (A : Gaussian.Table (Fin q) m n) (p : Fin m × Fin n) :
    pivot A = some p ↔ (scanResult (flatEntry A) 0 (m*n)).2 ≠ 0 ∧
      (scanResult (flatEntry A) 0 (m*n)).1 = (finProdFinEquiv p).val := by
  by_cases hz : (scanResult (flatEntry A) 0 (m*n)).2 = 0
  · simp [pivot,hz]
  · constructor
    · intro hp
      have he : finProdFinEquiv.symm
          (⟨(scanResult (flatEntry A) 0 (m*n)).1,scan_nonzero_lt A hz⟩ : Fin (m*n)) = p := by
        exact Option.some.inj (by simpa only [pivot,dif_neg hz] using hp)
      refine ⟨hz,?_⟩
      have hv := congrArg (fun p : Fin m × Fin n => (finProdFinEquiv p).val) he
      simpa only [Equiv.apply_symm_apply] using hv
    · rintro ⟨_,hi⟩
      simp only [pivot,dif_neg hz]
      apply congrArg some
      apply finProdFinEquiv.injective
      apply Fin.ext
      simpa only [Equiv.apply_symm_apply] using hi

theorem pivot_value {A : Gaussian.Table (Fin q) m n} {p : Fin m × Fin n}
    (hp : pivot A = some p) :
    (scanResult (flatEntry A) 0 (m*n)).2 = (Gaussian.toMatrix A p.1 p.2).val := by
  obtain ⟨hnz,hi⟩ := (pivot_some_iff A p).mp hp
  rcases scanResult_spec (flatEntry A) 0 (m*n) with hs | hs
  · exact (hnz hs.1).elim
  · rw [hs.2.2.1,hi,flatEntry,dif_pos (finProdFinEquiv p).isLt,
      Equiv.symm_apply_apply]

theorem pivot_nonzero (O : Operations (Fin q)) (hz : O.zero.val = 0)
    {A : Gaussian.Table (Fin q) m n} {p : Fin m × Fin n} (hp : pivot A = some p) :
    Gaussian.toMatrix A p.1 p.2 ≠ O.zero := by
  intro he
  have hv := pivot_value hp
  rw [he,hz] at hv
  exact ((pivot_some_iff A p).mp hp).1 hv

theorem pivot_none_matrix (O : Operations (Fin q)) (hz : O.zero.val = 0)
    {A : Gaussian.Table (Fin q) m n} (hp : pivot A = none) :
    Gaussian.toMatrix A = fun _ _ => O.zero := by
  have hn := (pivot_none_iff A).mp hp
  rcases scanResult_spec (flatEntry A) 0 (m*n) with hs | hs
  · funext i j
    apply Fin.ext
    let k : Fin (m*n) := finProdFinEquiv (i,j)
    have hh := hs.2.2 k.val (by omega) (by simpa using k.isLt)
    have he : flatEntry A k.val = (Gaussian.toMatrix A i j).val := by
      rw [flatEntry,dif_pos k.isLt]
      change (Gaussian.toMatrix A (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
        (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2).val = _
      rw [Equiv.symm_apply_apply]
    rw [he] at hh
    exact hh.trans hz.symm
  · exact (hs.2.2.2.1 hn).elim





















@[simp] theorem step_done (O : Operations (Fin q)) (s : State q m n) (hd : s.done = true) :
    step O s = s := by simp [step,hd]

theorem iterate_rank (O : Operations (Fin q)) (fuel : ℕ) (s : State q m n) :
    ((step O)^[fuel] s).rank = s.rank + if s.done then 0 else run O fuel s.table := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    rw [Function.iterate_succ_apply,ih]
    cases hd : s.done
    · cases hp : pivot s.table <;>
        simp [step,hd,hp,run,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
    · simp [step,hd]

variable {F : Type*} [Field F] [DecidableEq F]
variable {O : Operations (Fin q)} {decode : Fin q → F}

theorem padded_rank_step (h : Interpretation O decode)
    (A : Gaussian.Table (Fin q) m n) (p : Fin m × Fin n)
    (hp : Gaussian.toMatrix A p.1 p.2 ≠ O.zero) :
    (Gaussian.toMatrix (mapTable decode A)).rank =
      (Gaussian.toMatrix (mapTable decode (paddedSchur O A p))).rank+1 := by
  cases m with
  | zero => exact Fin.elim0 p.1
  | succ m =>
    cases n with
    | zero => exact Fin.elim0 p.2
    | succ n => exact paddedSchur_rank_step h A p hp

theorem pivot_none_rank (h : Interpretation O decode) (hz : O.zero.val = 0)
    {A : Gaussian.Table (Fin q) m n} (hp : pivot A = none) :
    (Gaussian.toMatrix (mapTable decode A)).rank = 0 := by
  have he := pivot_none_matrix O hz hp
  have hm : Gaussian.toMatrix (mapTable decode A) = 0 := by
    ext i j
    rw [toMatrix_mapTable,show Gaussian.toMatrix A i j = O.zero from congrFun (congrFun he i) j,h.zero]
    rfl
  rw [hm,Matrix.rank_zero]

theorem run_correct (h : Interpretation O decode) (hz : O.zero.val = 0)
    (fuel : ℕ) (A : Gaussian.Table (Fin q) m n)
    (hf : (Gaussian.toMatrix (mapTable decode A)).rank ≤ fuel) :
    run O fuel A = (Gaussian.toMatrix (mapTable decode A)).rank := by
  induction fuel generalizing A with
  | zero => simp only [run]; omega
  | succ fuel ih =>
    cases hp : pivot A with
    | none =>
      simp only [run,hp]
      exact (pivot_none_rank h hz hp).symm
    | some p =>
      have hr := padded_rank_step h A p (pivot_nonzero O hz hp)
      have hB : (Gaussian.toMatrix (mapTable decode (paddedSchur O A p))).rank ≤ fuel := by omega
      simp only [run,hp,ih _ hB]
      omega

theorem run_rows_correct (h : Interpretation O decode) (hz : O.zero.val = 0)
    (A : Gaussian.Table (Fin q) m n) :
    run O m A = (Gaussian.toMatrix (mapTable decode A)).rank := by
  apply run_correct h hz
  simpa only [Fintype.card_fin] using Matrix.rank_le_card_height (Gaussian.toMatrix (mapTable decode A))

theorem run_eq_encodedRun (h : Interpretation O decode) (hz : O.zero.val = 0)
    (A : Gaussian.Table (Fin q) m n) : run O m A = (EncodedGaussian.run O A).1 := by
  rw [run_rows_correct h hz,EncodedGaussian.run_correct h]

theorem binaryTest_rank (d n : ℕ) (y : Word (rowCount d n)) :
    run (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n)) (rowCount d n)
      (binaryTestTable d n y) = (testMatrix (binaryGeometry d n) y).rank := by
  erw [run_eq_encodedRun (BinaryField.indexOperations_interpretation _ _) (binary_zeroIndex_val _),
    binaryTestTable_rank]








theorem binary_iterate_rank (d n : ℕ) (y : Word (rowCount d n)) :
    ((step (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n)))^[rowCount d n]
      (⟨binaryTestTable d n y,0,false⟩ : State (fieldSize d n) (rowCount d n) (rowCount d n))).rank =
        (testMatrix (binaryGeometry d n) y).rank := by
  erw [iterate_rank]
  simpa using binaryTest_rank d n y





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

theorem branchZero_stops_zero (P : TapeProgram R B L) (Q : TapeProgram R B K) (r : Fin R)
    (inp : Inputs) (d : TapeStore R B) (hr : d.reg r = 0) (t : ℕ) (e : TapeCfg R B L)
    (he : P.Stops inp (d.toCfg P.entry) t e) :
    (branchZero P Q r).Stops inp (d.toCfg (branchZero P Q r).entry) (t+1) (e.mapPC (zeroLabel K)) := by
  have hh : (branchZero P Q r).Exec inp (d.toCfg (branchLabel L K 0)) 1
      (d.toCfg (zeroLabel K P.entry)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted]
    · simp [TapeProgram.step,TapeStore.toCfg,hr]
  have hb := he.exec.relabel (zeroLabel K) (fun j _ => branchZero_code_zero P Q r j)
  constructor
  · convert hh.trans hb using 1 <;> first | rfl | omega
  · change (branchZero P Q r).code (zeroLabel K e.pc) = .halt
    rw [branchZero_code_zero,he.halted]
    rfl

theorem branchZero_stops_positive (P : TapeProgram R B L) (Q : TapeProgram R B K) (r : Fin R)
    (inp : Inputs) (d : TapeStore R B) (hr : 0 < d.reg r) (t : ℕ) (e : TapeCfg R B K)
    (he : Q.Stops inp (d.toCfg Q.entry) t e) :
    (branchZero P Q r).Stops inp (d.toCfg (branchZero P Q r).entry) (t+2) (e.mapPC (positiveLabel L)) := by
  let d₁ := d.setReg r (d.reg r-1)
  have hh : (branchZero P Q r).Exec inp (d.toCfg (branchLabel L K 0)) 1
      (d₁.toCfg (branchLabel L K 1)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted]
    · simp [TapeProgram.step,TapeStore.toCfg,d₁,TapeStore.setReg,Nat.ne_of_gt hr]
  have hrestore : (branchZero P Q r).Exec inp (d₁.toCfg (branchLabel L K 1)) 1
      (d.toCfg (positiveLabel L Q.entry)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted]
    · simp [TapeProgram.step,TapeStore.toCfg,d₁,TapeStore.setReg,Function.update_idem,Nat.sub_add_cancel hr]
  have hb := he.exec.relabel (positiveLabel L) (fun j _ => branchZero_code_positive P Q r j)
  constructor
  · convert (hh.trans hrestore).trans hb using 1 <;> first | rfl | omega
  · change (branchZero P Q r).code (positiveLabel L e.pc) = .halt
    rw [branchZero_code_positive,he.halted]
    rfl

end Branch





theorem skip_stops (inp : Inputs) (d : Store) : skip.Stops inp (d.toCfg 0) 0 (d.toCfg 0) :=
  ⟨TapeProgram.Exec.refl _,rfl⟩









@[simp] theorem inputBuffer_not (b : Bool) : inputBuffer (!b) = outputBuffer b := by cases b <;> rfl
@[simp] theorem outputBuffer_not (b : Bool) : outputBuffer (!b) = inputBuffer b := by cases b <;> rfl
theorem buffers_ne (b : Bool) : outputBuffer b ≠ inputBuffer b := by cases b <;> decide










































theorem clear3Copy_stops (r : Fin 6 → Fin 64) (hr : Function.Injective r) (inp : Inputs) (d : Store) :
    ∃ e,(clear3Copy r).Stops inp (d.toCfg (clear3Copy r).entry)
      (d.reg (r 0)+d.reg (r 1)+d.reg (r 2)+d.reg (r 4)+d.reg (r 5)+5*d.reg (r 3)+13) e ∧
      e.store = clear3CopyStore r d := by
  let d₁ := d.setReg (r 0) 0
  let d₂ := d₁.setReg (r 1) 0
  let d₃ := d₂.setReg (r 2) 0
  have h₁ := TapeMacros.clear_stops (r 0) inp (d.reg (r 0)) d rfl
  have h₂ := TapeMacros.clear_stops (r 1) inp (d.reg (r 1)) d₁ (by simp [d₁,TapeStore.setReg,hr.eq_iff])
  have h₃ := TapeMacros.clear_stops (r 2) inp (d.reg (r 2)) d₂ (by simp [d₂,d₁,TapeStore.setReg,hr.eq_iff])
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops (r 3) (r 4) (r 5)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d₃
  have hall := h₁.seq (h₂.seq (h₃.seq he))
  refine ⟨((e.mapPC (TapeProgram.rightLabel 2)).mapPC (TapeProgram.rightLabel 2)).mapPC (TapeProgram.rightLabel 2),?_,?_⟩
  · convert hall using 1 <;> first | rfl | (simp [d₃,d₂,d₁,TapeStore.setReg,hr.eq_iff];omega)
  · change e.store = _
    simpa [clear3CopyStore,d₃,d₂,d₁,TapeStore.setReg,hr.eq_iff] using hes

theorem clear3CopyStore_bounded (r : Fin 6 → Fin 64) (d : Store) (M : ℕ) (hd : ∀ j,d.reg j ≤ M) :
    ∀ j,(clear3CopyStore r d).reg j ≤ M :=
  FieldPrograms.setReg_bound _ (r 5) 0 M
    (FieldPrograms.setReg_bound _ (r 4) (d.reg (r 3)) M
      (FieldPrograms.setReg_bound _ (r 2) 0 M
        (FieldPrograms.setReg_bound _ (r 1) 0 M
          (FieldPrograms.setReg_bound d (r 0) 0 M hd (Nat.zero_le M)) (Nat.zero_le M))
        (Nat.zero_le M)) (hd (r 3))) (Nat.zero_le M)




theorem scanLayout_injective : Function.Injective scanLayout := by decide
theorem initialLayout_injective : Function.Injective initialLayout := by decide




theorem scanSetup_stops (inp : Inputs) (d : Store) (M : ℕ) (hd : ∀ r,d.reg r ≤ M) :
    ∃ t e,t ≤ 10*M+13 ∧ scanSetup.Stops inp (d.toCfg scanSetup.entry) t e ∧
      e.store = scanSetupStore d ∧ (∀ r,e.reg r ≤ M) := by
  obtain ⟨e,he,hes⟩ := clear3Copy_stops scanLayout scanLayout_injective inp d
  refine ⟨_,e,?_,he,hes,?_⟩
  · change d.reg 2+d.reg 6+d.reg 8+d.reg 7+d.reg 63+5*d.reg 51+13 ≤ _
    have := hd 2;have := hd 6;have := hd 8;have := hd 7;have := hd 63;have := hd 51;omega
  · change ∀ r,e.store.reg r ≤ M
    rw [hes]
    exact clear3CopyStore_bounded scanLayout d M hd

theorem initialize_stops (inp : Inputs) (d : Store) (M : ℕ) (hd : ∀ r,d.reg r ≤ M) :
    ∃ t e,t ≤ 10*M+13 ∧ initializeProgram.Stops inp (d.toCfg initializeProgram.entry) t e ∧
      e.store = initializeStore d ∧ (∀ r,e.reg r ≤ M) := by
  obtain ⟨e,he,hes⟩ := clear3Copy_stops initialLayout initialLayout_injective inp d
  refine ⟨_,e,?_,he,hes,?_⟩
  · change d.reg 48+d.reg 60+d.reg 61+d.reg 62+d.reg 63+5*d.reg 49+13 ≤ _
    have := hd 48;have := hd 60;have := hd 61;have := hd 62;have := hd 63;have := hd 49;omega
  · change ∀ r,e.store.reg r ≤ M
    rw [hes]
    exact clear3CopyStore_bounded initialLayout d M hd




theorem scanSetupStore_payload (d : Store) : TapeStore.SamePayload (scanSetupStore d) d :=
  ⟨rfl,rfl,fun _ _ => rfl⟩

theorem initializeStore_payload (d : Store) : TapeStore.SamePayload (initializeStore d) d :=
  ⟨rfl,rfl,fun _ _ => rfl⟩

theorem scanSetupStore_frame (d : Store) (r : Fin 64)
    (h2 : r ≠ 2) (h6 : r ≠ 6) (h8 : r ≠ 8) (h7 : r ≠ 7) (h63 : r ≠ 63) :
    (scanSetupStore d).reg r = d.reg r := by
  simp [scanSetupStore,clear3CopyStore,scanLayout,TapeStore.setReg,h2,h6,h8,h7,h63]








theorem Common.selected {ell : ℕ} {h : 0 < ell} {m M : ℕ} {d : Store}
    (hc : Common ell h m M d) (b : Bool) : SchurCellState ell h (inputBuffer b) (outputBuffer b) d M := by
  cases b with
  | false => exact hc.state
  | true => exact ⟨hc.state.setup,hc.state.bounded,hc.state.outputHead,hc.state.inputHead,
      hc.state.outputMarked,hc.state.inputMarked⟩

theorem common_of_selected {ell : ℕ} {h : 0 < ell} {m M : ℕ} {d : Store} (b : Bool)
    (hs : SchurCellState ell h (inputBuffer b) (outputBuffer b) d M)
    (h40 : d.reg 40 = m) (h49 : d.reg 49 = m) (h51 : d.reg 51 = m*m) (hm : 1 < m) : Common ell h m M d := by
  cases b with
  | false => exact ⟨hs,h40,h49,h51,hm⟩
  | true => exact ⟨⟨hs.setup,hs.bounded,hs.outputHead,hs.inputHead,hs.outputMarked,hs.inputMarked⟩,h40,h49,h51,hm⟩

theorem Common.scanSetupStore {ell : ℕ} {h : 0 < ell} {m M : ℕ} {d : Store}
    (hc : Common ell h m M d) : Common ell h m M (scanSetupStore d) := by
  refine ⟨?_,?_,?_,?_,hc.large⟩
  · exact state_setReg (state_setReg (state_setReg (state_setReg (state_setReg hc.state 2 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)) 6 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)) 8 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)) 7 (d.reg 51)
      (by decide) (by decide) (by decide) (by decide) (hc.state.bounded 51)) 63 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)
  · exact (scanSetupStore_frame d 40 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.columns
  · exact (scanSetupStore_frame d 49 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.rows
  · exact (scanSetupStore_frame d 51 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.cells










theorem Represents.of_payload {ell m : ℕ} {b : Bool} {s : Model ell m} {d e : Store}
    (hr : Represents ell m b s d) (hp : TapeStore.SamePayload e d)
    (h60 : e.reg 60 = d.reg 60) (h61 : e.reg 61 = d.reg 61) (h48 : e.reg 48 = d.reg 48) :
    Represents ell m b s e := by
  rcases hr.spare with ⟨A,ha⟩
  exact ⟨h60.trans hr.buffer,h61.trans hr.done,h48.trans hr.rank,
    matrixStored_of_payload hr.current hp,⟨A,matrixStored_of_payload ha hp⟩⟩

theorem Represents.scanSetupStore {ell m : ℕ} {b : Bool} {s : Model ell m} {d : Store}
    (hr : Represents ell m b s d) : Represents ell m b s (scanSetupStore d) :=
  hr.of_payload (scanSetupStore_payload d)
    (scanSetupStore_frame d 60 (by decide) (by decide) (by decide) (by decide) (by decide))
    (scanSetupStore_frame d 61 (by decide) (by decide) (by decide) (by decide) (by decide))
    (scanSetupStore_frame d 48 (by decide) (by decide) (by decide) (by decide) (by decide))

theorem common_after_scan {ell : ℕ} {h : 0 < ell} {m M : ℕ} {d e : Store} {b : Fin 2}
    {A : Gaussian.Table (Fin (2^ell)) m m} (hc : Common ell h m M d)
    (ho : ScanOutcome (flatEntry A) (2^ell) 0 (m*m) M b d e) (hb : ∀ r,e.reg r ≤ M) :
    Common ell h m M e := by
  have hhead (c : Fin 2) : e.bufferHead c ≤ (M+1)^2 := by
    by_cases heq : c = b
    · subst c;exact ho.head
    · rw [ho.otherHead c heq]
      fin_cases c
      · exact hc.state.inputHead
      · exact hc.state.outputHead
  have hs : FieldSetup ell h e := by
    rcases hc.state.setup with ⟨h0,h36,h37,h38⟩
    exact ⟨ho.width,(ho.outside 36 (by decide)).trans h36,(ho.outside 37 (by decide)).trans h37,
      (ho.outside 38 (by decide)).trans h38⟩
  exact ⟨⟨hs,hb,hhead 0,hhead 1,hc.state.inputMarked.of_payload ho.payload,
    hc.state.outputMarked.of_payload ho.payload⟩,(ho.outside 40 (by decide)).trans hc.columns,
    (ho.outside 49 (by decide)).trans hc.rows,(ho.outside 51 (by decide)).trans hc.cells,hc.large⟩

theorem model_rank_step_le (ell : ℕ) (h : 0 < ell) (m : ℕ) (s : Model ell m) :
    (PaddedGaussian.step (PolynomialStretch.BinaryField.indexOperations ell h) s).rank ≤ s.rank+1 := by
  unfold PaddedGaussian.step
  split
  · omega
  · split <;> simp



theorem bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> decide

theorem Common.one_le {ell : ℕ} {h : 0 < ell} {m M : ℕ} {d : Store}
    (hc : Common ell h m M d) : 1 ≤ M := by
  have hq := hc.state.bounded 0
  rw [hc.state.setup.1] at hq
  have hp : 0 < 2^ell := pow_pos (by decide) ell
  omega

theorem Common.setReg {ell : ℕ} {h : 0 < ell} {m M : ℕ} {d : Store}
    (hc : Common ell h m M d) (r : Fin 64) (v : ℕ)
    (h0 : r ≠ 0) (h36 : r ≠ 36) (h37 : r ≠ 37) (h38 : r ≠ 38)
    (h40 : r ≠ 40) (h49 : r ≠ 49) (h51 : r ≠ 51) (hv : v ≤ M) :
    Common ell h m M (d.setReg r v) := by
  refine ⟨state_setReg hc.state r v h0 h36 h37 h38 hv,?_,?_,?_,hc.large⟩
  · simpa [TapeStore.setReg,Ne.symm h40] using hc.columns
  · simpa [TapeStore.setReg,Ne.symm h49] using hc.rows
  · simpa [TapeStore.setReg,Ne.symm h51] using hc.cells

theorem flip_stops (b : Bool) (inp : Inputs) (d : Store) (hd : d.reg 60 = bit b) :
    ∃ t e,t ≤ 2 ∧ (flip b).Stops inp (d.toCfg (flip b).entry) t e ∧
      e.store = d.setReg 60 (bit (!b)) := by
  cases b with
  | false =>
    have hs := TapeMacros.increment_stops (60 : Fin 64) inp d
    refine ⟨1,(d.setReg 60 1).toCfg 1,by decide,?_,rfl⟩
    simpa [flip,bit,hd,TapeMacros.increment] using hs
  | true =>
    have hs := TapeMacros.clear_stops (60 : Fin 64) inp 1 d hd
    exact ⟨2,(d.setReg 60 0).toCfg 1,by decide,hs,rfl⟩

theorem flat_coordinates {m : ℕ} (p : Fin m × Fin m) :
    (finProdFinEquiv p).val % m = p.2.val ∧
      (finProdFinEquiv p).val / m * m = p.1.val*m := by
  have he := finProdFinEquiv.symm_apply_apply p
  have hc := congrArg (fun x : Fin m × Fin m => x.2.val) he
  have hr := congrArg (fun x : Fin m × Fin m => x.1.val) he
  change (finProdFinEquiv p).val % m = p.2.val at hc
  change (finProdFinEquiv p).val / m = p.1.val at hr
  exact ⟨hc,congrArg (fun v : ℕ => v*m) hr⟩






theorem afterPivot_stops (b : Bool) (ell : ℕ) (h : 0 < ell) (m : ℕ) (s : Model ell m)
    (p : Fin m × Fin m) (inp : Inputs) (d : Store) (M : ℕ)
    (hc : Common ell h m M d) (hr : Represents ell m b s d) (hdone : s.done = false)
    (hflat : d.reg 2 = (finProdFinEquiv p).val)
    (hvalue : d.reg 6 = (Gaussian.toMatrix s.table p.1 p.2).val) (hnext : s.rank+1 ≤ M) :
    ∃ t e,t ≤ successBudget m M ∧ (afterPivot b).Stops inp (d.toCfg (afterPivot b).entry) t e ∧
      Common ell h m M e.store ∧
      Represents ell m (!b) (⟨paddedSchur (ops ell h) s.table p,s.rank+1,false⟩ : Model ell m) e.store ∧
      e.reg 62 = d.reg 62 ∧ e.roHead = d.roHead ∧ e.output = d.output := by
  have hflatB : d.reg 2 < (d.reg 40)^2 := by
    rw [hflat,hc.columns,pow_two]
    exact (finProdFinEquiv p).isLt
  obtain ⟨t₁,c,ht₁,hcs,hco⟩ := GaussianPivot.preparePivot_stops ell h d inp M hc.state.setup hc.state.bounded
    (by rw [hc.columns];exact hc.large) hflatB (Gaussian.toMatrix s.table p.1 p.2) hvalue
  have hcf (r : Fin 64) (hr40 : 40 ≤ r.val) (hC : GaussianPivot.OutsidePivotCoordinates r) (h50 : r ≠ 50) :
      c.store.reg r = d.reg r := hco.frame r hr40 hC h50
  have hseed : SchurCellState ell h (inputBuffer b) (outputBuffer b) c.store M :=
    ⟨hco.setup,hco.bounded,(congrFun hco.heads (inputBuffer b)).le.trans (hc.selected b).inputHead,
      (congrFun hco.heads (outputBuffer b)).le.trans (hc.selected b).outputHead,
      (hc.selected b).inputMarked.of_payload hco.payload,(hc.selected b).outputMarked.of_payload hco.payload⟩
  have hcol : c.store.reg 43 = p.2.val := by
    rw [hco.col,hflat,hc.columns]
    exact (flat_coordinates p).1
  have hrow : c.store.reg 44 = p.1.val*m := by
    rw [hco.rowBase,hflat,hc.columns]
    exact (flat_coordinates p).2
  rcases hr.spare with ⟨Aold,hOld⟩
  have hsize : m*m ≤ M := by rw [← hc.cells];exact hc.state.bounded 51
  obtain ⟨t₂,f,ht₂,hfs,hfo,hInput,hOutput,h41,h45,h46,hff,hro,hout⟩ := materializeGrid_stops
    (inputBuffer b) (outputBuffer b) (buffers_ne b) ell h inp s.table p
      (fun k : Fin (m*m) => flatEntry Aold k.val) M hsize c.store hseed
      ((hcf 40 (by decide) (by decide) (by decide)).trans hc.columns)
      ((hcf 49 (by decide) (by decide) (by decide)).trans hc.rows) hcol hrow hco.inverse
      (matrixStored_of_payload hr.current hco.payload) (matrixStored_of_payload hOld hco.payload)
  have hfc (r : Fin 64) (hr40 : 40 ≤ r.val) (h41 : r ≠ 41) (h42 : r ≠ 42)
      (h45 : r ≠ 45) (h46 : r ≠ 46) (h47 : r ≠ 47) : f.store.reg r = c.store.reg r :=
    hff r hr40 h41 h42 h45 h46 h47
  have hfCommon : Common ell h m M f.store := common_of_selected b hfo
    ((hfc 40 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hcf 40 (by decide) (by decide) (by decide)).trans hc.columns))
    ((hfc 49 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hcf 49 (by decide) (by decide) (by decide)).trans hc.rows))
    ((hfc 51 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hcf 51 (by decide) (by decide) (by decide)).trans hc.cells)) hc.large
  have hfRank : f.store.reg 48 = s.rank :=
    (hfc 48 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hcf 48 (by decide) (by decide) (by decide)).trans hr.rank)
  have hfFlag : f.store.reg 60 = bit b :=
    (hfc 60 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hcf 60 (by decide) (by decide) (by decide)).trans hr.buffer)
  have hfDone : f.store.reg 61 = 0 := by
    have hh := (hfc 61 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hcf 61 (by decide) (by decide) (by decide)).trans hr.done)
    simpa [hdone,bit] using hh
  have hf62 : f.store.reg 62 = d.reg 62 :=
    (hfc 62 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (hcf 62 (by decide) (by decide) (by decide))
  let dRank := f.store.setReg 48 (f.reg 48+1)
  have hRank := TapeMacros.increment_stops (48 : Fin 64) inp f.store
  have hRankCommon : Common ell h m M dRank := hfCommon.setReg 48 (f.reg 48+1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      ((congrArg (fun v : ℕ => v+1) hfRank).le.trans hnext)
  have hRankFlag : dRank.reg 60 = bit b :=
    (show dRank.reg 60 = f.store.reg 60 by simp [dRank,TapeStore.setReg]).trans hfFlag
  obtain ⟨t₃,e,ht₃,he,hes⟩ := flip_stops b inp dRank hRankFlag
  have heCommon : Common ell h m M e.store := by
    rw [hes]
    exact hRankCommon.setReg 60 (bit (!b)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) ((bit_le_one (!b)).trans hc.one_le)
  have hep : TapeStore.SamePayload e.store f.store := by
    rw [hes]
    exact (TapeStore.setReg_payload dRank 60 (bit (!b))).trans
      (TapeStore.setReg_payload f.store 48 (f.reg 48+1))
  have heRank : e.store.reg 48 = f.store.reg 48+1 := by rw [hes];simp [dRank,TapeStore.setReg]
  have heDone : e.store.reg 61 = 0 :=
    (show e.store.reg 61 = f.store.reg 61 by rw [hes];simp [dRank,TapeStore.setReg]).trans hfDone
  have he62 : e.store.reg 62 = d.reg 62 :=
    (show e.store.reg 62 = f.store.reg 62 by rw [hes];simp [dRank,TapeStore.setReg]).trans hf62
  have hall := hcs.seq (hfs.seq (hRank.seq he))
  refine ⟨_,_,?_,hall,heCommon,?_,he62,hep.roHead.trans (hro.trans hco.payload.roHead),
    hep.output.trans (hout.trans hco.payload.output)⟩
  · change t₂ ≤ gridBudget m M at ht₂
    unfold successBudget
    omega
  · refine ⟨?_,heDone,heRank.trans (congrArg (fun v : ℕ => v+1) hfRank),?_,?_⟩
    · change e.store.reg 60 = bit (!b)
      rw [hes]
      simp [TapeStore.setReg]
    · rw [inputBuffer_not]
      exact matrixStored_of_payload hOutput hep
    · refine ⟨s.table,?_⟩
      rw [outputBuffer_not]
      exact matrixStored_of_payload hInput hep



theorem Represents.setDone {ell m : ℕ} {b : Bool} {s : Model ell m} {d : Store}
    (hr : Represents ell m b s d) : Represents ell m b {s with done:=true} (d.setReg 61 1) := by
  rcases hr.spare with ⟨A,ha⟩
  exact ⟨by simpa [TapeStore.setReg] using hr.buffer,by simp [TapeStore.setReg,bit],
    by simpa [TapeStore.setReg] using hr.rank,
    matrixStored_of_payload hr.current (TapeStore.setReg_payload d 61 1),
    ⟨A,matrixStored_of_payload ha (TapeStore.setReg_payload d 61 1)⟩⟩



theorem scanRound_stops (b : Bool) (ell : ℕ) (h : 0 < ell) (m : ℕ) (s : Model ell m)
    (inp : Inputs) (d : Store) (M : ℕ) (hc : Common ell h m M d) (hr : Represents ell m b s d)
    (hdone : s.done = false) (hnext : s.rank+1 ≤ M) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 2118) (b' : Bool),t ≤ scanRoundBudget m M ∧
      (scanRound b).Stops inp (d.toCfg (scanRound b).entry) t e ∧ Common ell h m M e.store ∧
      Represents ell m b' (PaddedGaussian.step (ops ell h) s) e.store ∧
      e.reg 62 = d.reg 62 ∧ e.roHead = d.roHead ∧ e.output = d.output := by
  obtain ⟨t₀,c,ht₀,hcs,hcstore,hcb⟩ := scanSetup_stops inp d M hc.state.bounded
  have hcCommon : Common ell h m M c.store := by rw [hcstore];exact hc.scanSetupStore
  have hcRep : Represents ell m b s c.store := by rw [hcstore];exact hr.scanSetupStore
  have hcp : TapeStore.SamePayload c.store d := by rw [hcstore];exact scanSetupStore_payload d
  have hc2 : c.store.reg 2 = 0 := by rw [hcstore];simp [GaussianDriver.scanSetupStore,clear3CopyStore,scanLayout,TapeStore.setReg]
  have hc6 : c.store.reg 6 = 0 := by rw [hcstore];simp [GaussianDriver.scanSetupStore,clear3CopyStore,scanLayout,TapeStore.setReg]
  have hc8 : c.store.reg 8 = 0 := by rw [hcstore];simp [GaussianDriver.scanSetupStore,clear3CopyStore,scanLayout,TapeStore.setReg]
  have hc7 : c.store.reg 7 = m*m := by rw [hcstore];simp [GaussianDriver.scanSetupStore,clear3CopyStore,scanLayout,TapeStore.setReg,hc.cells]
  have hsize : m*m ≤ M := by rw [← hc.cells];exact hc.state.bounded 51
  obtain ⟨t₁,f,ht₁,hfs,hfo,hfb⟩ := pivotScan_table_stops (inputBuffer b) inp s.table c.store M hc.one_le hcb hsize
    hcCommon.state.setup.1 hc2 hc6 hc7 hc8 (hcCommon.selected b).inputMarked
    (hcCommon.selected b).inputHead hcRep.current
  have hfCommon : Common ell h m M f := common_after_scan hcCommon hfo hfb
  have hfRep : Represents ell m b s f := hcRep.of_payload hfo.payload
    (hfo.outside 60 (by decide)) (hfo.outside 61 (by decide)) (hfo.outside 48 (by decide))
  have hfp : TapeStore.SamePayload f d := hfo.payload.trans hcp
  have hf62 : f.reg 62 = d.reg 62 := (hfo.outside 62 (by decide)).trans (by
    rw [hcstore]
    exact scanSetupStore_frame d 62 (by decide) (by decide) (by decide) (by decide) (by decide))
  change t₁ ≤ scanBudget m M at ht₁
  cases hp : PaddedGaussian.pivot s.table with
  | none =>
    have hz := (PaddedGaussian.pivot_none_iff s.table).mp hp
    have hf8 : f.reg 8 = 0 := by simpa [hz] using hfo.found
    have hf61 : f.reg 61 = 0 := by simpa [hdone,bit] using hfRep.done
    have hnone : (TapeMacros.increment (61 : Fin 64)).Stops inp (f.toCfg 0) 1 ((f.setReg 61 1).toCfg 1) := by
      simpa only [hf61,Nat.zero_add] using TapeMacros.increment_stops (61 : Fin 64) inp f
    have hbranch := branchZero_stops_zero (TapeMacros.increment 61) (afterPivot b) 8 inp f hf8 1 _ hnone
    have hall := hcs.seq (hfs.seq hbranch)
    have heCommon : Common ell h m M (f.setReg 61 1) := hfCommon.setReg 61 1
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.one_le
    have heRep : Represents ell m b (PaddedGaussian.step (ops ell h) s) (f.setReg 61 1) := by
      simpa [PaddedGaussian.step,hdone,hp] using hfRep.setDone
    have hep : TapeStore.SamePayload (f.setReg 61 1) d := (TapeStore.setReg_payload f 61 1).trans hfp
    refine ⟨_,_,b,?_,hall,heCommon,heRep,?_,hep.roHead,hep.output⟩
    · unfold scanRoundBudget;omega
    · change (f.setReg 61 1).reg 62 = d.reg 62
      simpa [TapeStore.setReg] using hf62
  | some p =>
    have hp' := (PaddedGaussian.pivot_some_iff s.table p).mp hp
    have hf8 : 0 < f.reg 8 := by rw [hfo.found,if_neg hp'.1];decide
    have hf2 : f.reg 2 = (finProdFinEquiv p).val := hfo.index.trans hp'.2
    have hf6 : f.reg 6 = (Gaussian.toMatrix s.table p.1 p.2).val := hfo.value.trans (PaddedGaussian.pivot_value hp)
    obtain ⟨t₂,e,ht₂,he,heo,her,he62,hero,heout⟩ := afterPivot_stops b ell h m s p inp f M hfCommon hfRep hdone hf2 hf6 hnext
    have hbranch := branchZero_stops_positive (TapeMacros.increment 61) (afterPivot b) 8 inp f hf8 t₂ e he
    have hall := hcs.seq (hfs.seq hbranch)
    refine ⟨_,_,!b,?_,hall,heo,?_,he62.trans hf62,hero.trans hfp.roHead,heout.trans hfp.output⟩
    · unfold scanRoundBudget;omega
    · simpa [PaddedGaussian.step,hdone,hp] using her



theorem round_stops (b : Bool) (ell : ℕ) (h : 0 < ell) (m : ℕ) (s : Model ell m)
    (inp : Inputs) (d : Store) (M : ℕ) (hc : Common ell h m M d) (hr : Represents ell m b s d)
    (hnext : s.rank+1 ≤ M) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 4241) (b' : Bool),t ≤ roundBudget m M ∧
      round.Stops inp (d.toCfg round.entry) t e ∧ Common ell h m M e.store ∧
      Represents ell m b' (PaddedGaussian.step (ops ell h) s) e.store ∧
      e.reg 62 = d.reg 62 ∧ e.roHead = d.roHead ∧ e.output = d.output := by
  cases hd : s.done with
  | false =>
    obtain ⟨t,e,b',ht,he,heo,her,he62,hero,heout⟩ := scanRound_stops b ell h m s inp d M hc hr hd hnext
    have hselect : ∃ (u : ℕ) (g : TapeCfg 64 2 4238),u ≤ t+2 ∧
        (branchZero scanRound₀ scanRound₁ 60).Stops inp
          (d.toCfg (branchZero scanRound₀ scanRound₁ 60).entry) u g ∧ g.store = e.store := by
      cases b with
      | false =>
        have h0 : d.reg 60 = 0 := by simpa [bit] using hr.buffer
        exact ⟨t+1,e.mapPC (zeroLabel 2118),by omega,
          branchZero_stops_zero scanRound₀ scanRound₁ 60 inp d h0 t e he,rfl⟩
      | true =>
        have h1 : 0 < d.reg 60 := by have hh := hr.buffer; simp [bit] at hh;omega
        exact ⟨t+2,e.mapPC (positiveLabel 2118),le_rfl,
          branchZero_stops_positive scanRound₀ scanRound₁ 60 inp d h1 t e he,rfl⟩
    obtain ⟨u,g,hu,hgs,hstore⟩ := hselect
    have hdone0 : d.reg 61 = 0 := by simpa [hd,bit] using hr.done
    have hall := branchZero_stops_zero (branchZero scanRound₀ scanRound₁ 60) skip 61 inp d hdone0 u g hgs
    refine ⟨_,_,b',?_,hall,?_,?_,?_,?_,?_⟩
    · unfold roundBudget scanRoundBudget at *
      omega
    · change Common ell h m M g.store
      rw [hstore]
      exact heo
    · change Represents ell m b' (PaddedGaussian.step (ops ell h) s) g.store
      rw [hstore]
      exact her
    · change g.store.reg 62 = d.reg 62
      exact (congrArg (fun x : Store => x.reg 62) hstore).trans he62
    · change g.store.roHead = d.roHead
      exact (congrArg TapeStore.roHead hstore).trans hero
    · change g.store.output = d.output
      exact (congrArg TapeStore.output hstore).trans heout
  | true =>
    have hdone1 : 0 < d.reg 61 := by have hh := hr.done;simp [hd,bit] at hh;omega
    have hall := branchZero_stops_positive (branchZero scanRound₀ scanRound₁ 60) skip 61 inp d hdone1 0 _ (skip_stops inp d)
    refine ⟨2,_,b,?_,hall,hc,?_,rfl,rfl,rfl⟩
    · unfold roundBudget;omega
    · simpa only [PaddedGaussian.step_done (ops ell h) s hd] using hr



theorem initializeStore_frame (d : Store) (r : Fin 64)
    (h48 : r ≠ 48) (h60 : r ≠ 60) (h61 : r ≠ 61) (h62 : r ≠ 62) (h63 : r ≠ 63) :
    (initializeStore d).reg r = d.reg r := by
  simp [initializeStore,clear3CopyStore,initialLayout,TapeStore.setReg,h48,h60,h61,h62,h63]

theorem Common.initializeStore {ell : ℕ} {h : 0 < ell} {m M : ℕ} {d : Store}
    (hc : Common ell h m M d) : Common ell h m M (initializeStore d) := by
  refine ⟨?_,?_,?_,?_,hc.large⟩
  · exact state_setReg (state_setReg (state_setReg (state_setReg (state_setReg hc.state 48 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)) 60 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)) 61 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)) 62 (d.reg 49)
      (by decide) (by decide) (by decide) (by decide) (hc.state.bounded 49)) 63 0
      (by decide) (by decide) (by decide) (by decide) (Nat.zero_le M)
  · exact (initializeStore_frame d 40 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.columns
  · exact (initializeStore_frame d 49 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.rows
  · exact (initializeStore_frame d 51 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.cells







theorem loop_stops (ell : ℕ) (h : 0 < ell) (m M : ℕ) (initial : Model ell m) (base : Store)
    (inp : Inputs) (remaining : ℕ) (d : Store) (hd : d.reg 62 = remaining)
    (hi : LoopInv ell h m M initial base remaining d) :
    ∃ t e,t ≤ remaining*(roundBudget m M+2)+1 ∧
      loop.Stops inp (d.toCfg (TapeProgram.loopHeader 4241)) t (e.toCfg (TapeProgram.loopExit 4241)) ∧
      LoopInv ell h m M initial base 0 e ∧ e.reg 62 = 0 := by
  apply countedLoop_stops_of_body round 62 inp (roundBudget m M) (LoopInv ell h m M initial base)
    _ remaining d hd hi
  intro r s hs62 hs
  rcases hs with ⟨hc,hro,hout,b,model,hr,hprogress,hfuture⟩
  let s₀ := TapeProgram.decStore (62 : Fin 64) s
  have hp : TapeStore.SamePayload s₀ s := TapeStore.setReg_payload s 62 (s.reg 62-1)
  have hc0 : Common ell h m M s₀ := hc.setReg 62 (s.reg 62-1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ((Nat.sub_le _ _).trans (hc.state.bounded 62))
  have hr0 : Represents ell m b model s₀ := hr.of_payload hp
    (by simp [s₀,TapeProgram.decStore]) (by simp [s₀,TapeProgram.decStore]) (by simp [s₀,TapeProgram.decStore])
  have hmM : m ≤ M := by rw [← hc.rows];exact hc.state.bounded 49
  have hnext : model.rank+1 ≤ M := by omega
  obtain ⟨t,e,b',ht,he,heo,her,he62,hero,heout⟩ := round_stops b ell h m model inp s₀ M hc0 hr0 hnext
  have he62' : e.reg 62 = r := by
    rw [he62]
    simp [s₀,TapeProgram.decStore,hs62]
  have hprogress' : (PaddedGaussian.step (ops ell h) model).rank+r ≤ m := by
    have hh : (PaddedGaussian.step (ops ell h) model).rank ≤ model.rank+1 :=
      model_rank_step_le ell h m model
    omega
  have hfuture' : ((PaddedGaussian.step (ops ell h))^[r] (PaddedGaussian.step (ops ell h) model)) =
      ((PaddedGaussian.step (ops ell h))^[m] initial) := by
    simpa only [Function.iterate_succ_apply] using hfuture
  exact ⟨t,e,ht,he,he62',heo,hero.trans hro,heout.trans hout,b',
    PaddedGaussian.step (ops ell h) model,her,hprogress',hfuture'⟩

/-- Actual physical Gaussian elimination from two encoded square buffers.
The finite code has4260 labels regardless of the runtime field/dimension.
Every source loop is bounded, every field operation is a checked source
program, and the resulting register48 matches the exact padded iteration. -/
theorem rankProgram_stops (ell : ℕ) (h : 0 < ell) (m M : ℕ) (inp : Inputs) (d : Store)
    (hc : Common ell h m M d) (A B : Gaussian.Table (Fin (2^ell)) m m)
    (ha : MatrixStored d 0 A) (hb : MatrixStored d 1 B) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 4260),t ≤ 10*M+13+m*(roundBudget m M+2)+2 ∧
      rankProgram.Stops inp (d.toCfg rankProgram.entry) t e ∧ Common ell h m M e.store ∧
      e.reg 48 = ((PaddedGaussian.step (ops ell h))^[m] (⟨A,0,false⟩ : Model ell m)).rank ∧
      e.reg 62 = 0 ∧ e.roHead = d.roHead ∧ e.output = d.output := by
  let initial : Model ell m := ⟨A,0,false⟩
  obtain ⟨t₀,c,ht₀,hcs,hcstore,hcb⟩ := initialize_stops inp d M hc.state.bounded
  have hcCommon : Common ell h m M c.store := by rw [hcstore];exact hc.initializeStore
  have hcp : TapeStore.SamePayload c.store d := by rw [hcstore];exact initializeStore_payload d
  have hc62 : c.reg 62 = m := by
    change c.store.reg 62 = m
    rw [hcstore]
    simp [GaussianDriver.initializeStore,clear3CopyStore,initialLayout,TapeStore.setReg,hc.rows]
  have hrep : Represents ell m false initial c.store := by
    refine ⟨?_,?_,?_,matrixStored_of_payload ha hcp,⟨B,matrixStored_of_payload hb hcp⟩⟩
    · rw [hcstore];simp [GaussianDriver.initializeStore,clear3CopyStore,initialLayout,TapeStore.setReg,bit]
    · rw [hcstore];simp [GaussianDriver.initializeStore,clear3CopyStore,initialLayout,TapeStore.setReg,initial,bit]
    · rw [hcstore];simp [GaussianDriver.initializeStore,clear3CopyStore,initialLayout,TapeStore.setReg,initial]
  have hi : LoopInv ell h m M initial d m c.store :=
    ⟨hcCommon,hcp.roHead,hcp.output,false,initial,hrep,by simp [initial],rfl⟩
  obtain ⟨t₁,e,ht₁,hes,hend,he62⟩ := loop_stops ell h m M initial d inp m c.store hc62 hi
  rcases hend with ⟨heCommon,hero,heout,b',model,her,hprogress,hfuture⟩
  have hmodel : model = (PaddedGaussian.step (ops ell h))^[m] initial := by simpa using hfuture
  have hall := hcs.seq hes
  refine ⟨_,_,by omega,hall,heCommon,?_,he62,hero,heout⟩
  · exact her.rank.trans (congrArg PaddedGaussian.State.rank hmodel)




end ExpandingCodes.Computation.GaussianDriver

end FlattenModule88

/-! Inlined whole module: ExpandingCodes.Computation.GaussianDriverBounds -/
section FlattenModule89


set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianDriver
open NKtLB GaussianProgram GaussianGrid EncodedGaussian
open ExpandingCodes.PolynomialStretch

theorem sourceBudget_le (m M : ℕ) (hm : m ≤ M) :
    10*M+13+m*(roundBudget m M+2)+2 ≤ 100000*(M+1)^9 := by
  let X := M+1
  have hx : 1 ≤ X := by omega
  have hmX : m ≤ X := by omega
  have hMX : M ≤ X := by omega
  have hp (a b : ℕ) (hab : a ≤ b) : X^a ≤ X^b := Nat.pow_le_pow_right hx hab
  have h1 (a : ℕ) : 1 ≤ X^a := one_le_pow₀ hx
  have hs : (X^2+1)^2 ≤ 4*X^4 := by
    calc
      (X^2+1)^2 ≤ (2*X^2)^2 := Nat.pow_le_pow_left (by have := h1 2;omega) 2
      _ = 4*X^4 := by ring
  have hc : cellBudget M ≤ 25000*X^6 := by
    change 100*X+460*(X^2+1)^2+20000*X^6+3000*X^5+7 ≤ _
    have h16 := hp 1 6 (by decide)
    have h46 := hp 4 6 (by decide)
    have h56 := hp 5 6 (by decide)
    have h06 := h1 6
    simp only [pow_one] at h16
    omega
  have ht : tickBudget M ≤ 26000*X^6 := by
    unfold tickBudget
    have h16 := hp 1 6 (by decide)
    have h06 := h1 6
    simp only [pow_one] at h16
    omega
  have hr : rowBudget m M ≤ 27000*X^7 := by
    calc
      rowBudget m M ≤ X*(26000*X^6+2)+20*X := by
        unfold rowBudget
        exact Nat.add_le_add (Nat.mul_le_mul hmX (by omega)) (by rfl)
      _ = 26000*X^7+22*X := by ring
      _ ≤ 27000*X^7 := by
        have hh := hp 1 7 (by decide)
        simp only [pow_one] at hh
        omega
  have hg : gridBudget m M ≤ 28000*X^8 := by
    calc
      gridBudget m M ≤ 20*X+X*(27000*X^7+2)+2 := by
        unfold gridBudget
        exact Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul hmX (by omega)) _) (by rfl)
      _ = 27000*X^8+22*X+2 := by ring
      _ ≤ 28000*X^8 := by
        have hh := hp 1 8 (by decide)
        have h08 := h1 8
        simp only [pow_one] at hh
        omega
  have hsuccess : successBudget m M ≤ 50000*X^8 := by
    change 21000*X^7+gridBudget m M+10 ≤ _
    have h78 := hp 7 8 (by decide)
    have h08 := h1 8
    omega
  have hscan : scanBudget m M ≤ 500*X^6 := by
    calc
      scanBudget m M ≤ X^2*(400*X^4+5)+1 := by
        unfold scanBudget
        apply Nat.add_le_add_right
        apply Nat.mul_le_mul
        · simpa only [pow_two] using Nat.mul_le_mul hmX hmX
        · change 100*(X^2+1)^2+5 ≤ _
          omega
      _ = 400*X^6+5*X^2+1 := by ring
      _ ≤ 500*X^6 := by
        have hh := hp 2 6 (by decide)
        have h06 := h1 6
        omega
  have hround : roundBudget m M ≤ 51000*X^8 := by
    unfold roundBudget
    have h18 := hp 1 8 (by decide)
    have h68 := hp 6 8 (by decide)
    have h08 := h1 8
    simp only [pow_one] at h18
    omega
  calc
    10*M+13+m*(roundBudget m M+2)+2 ≤ 10*X+13+X*(51000*X^8+2)+2 := by
      exact Nat.add_le_add (Nat.add_le_add (by omega) (Nat.mul_le_mul hmX (by omega))) (by rfl)
    _ = 51000*X^9+12*X+15 := by ring
    _ ≤ 100000*X^9 := by
      have hh := hp 1 9 (by decide)
      have h09 := h1 9
      simp only [pow_one] at hh
      omega














theorem rankProgram_stops_canonical (degree n M : ℕ) (inp : Inputs) (d : Store)
    (y : Word (rowCount degree n))
    (hc : Common (fieldExponent degree n) (fieldExponent_pos degree n) (rowCount degree n) M d)
    (B : Gaussian.Table (Fin (fieldSize degree n)) (rowCount degree n) (rowCount degree n))
    (ha : MatrixStored d 0 (binaryTestTable degree n y)) (hb : MatrixStored d 1 B) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 4260),t ≤ 100000*(M+1)^9 ∧
      rankProgram.Stops inp (d.toCfg rankProgram.entry) t e ∧
      Common (fieldExponent degree n) (fieldExponent_pos degree n) (rowCount degree n) M e.store ∧
      e.reg 48 = (testMatrix (binaryGeometry degree n) y).rank ∧
      e.reg 62 = 0 ∧ e.roHead = d.roHead ∧ e.output = d.output := by
  obtain ⟨t,e,ht,he,heo,hr,h62,hro,hout⟩ := rankProgram_stops
    (fieldExponent degree n) (fieldExponent_pos degree n) (rowCount degree n) M inp d hc
      (binaryTestTable degree n y) B ha hb
  have hm : rowCount degree n ≤ M := by rw [← hc.rows];exact hc.state.bounded 49
  exact ⟨t,e,ht.trans (sourceBudget_le _ _ hm),he,heo,
    hr.trans (PaddedGaussian.binary_iterate_rank degree n y),h62,hro,hout⟩





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


section FlattenModule97





set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch






























open ExpandingCodes.Computation



























































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






@[simp] theorem reverse_zero (r : Fin 6 → Fin R) : reverse r 0 = r 1 := by simp [reverse]
@[simp] theorem reverse_one (r : Fin 6 → Fin R) : reverse r 1 = r 0 := by simp [reverse]
@[simp] theorem reverse_two (r : Fin 6 → Fin R) : reverse r 2 = r 2 := by simp [reverse, Equiv.swap_apply_def]
@[simp] theorem reverse_three (r : Fin 6 → Fin R) : reverse r 3 = r 3 := by simp [reverse, Equiv.swap_apply_def]
@[simp] theorem reverse_four (r : Fin 6 → Fin R) : reverse r 4 = r 4 := by simp [reverse, Equiv.swap_apply_def]
@[simp] theorem reverse_five (r : Fin 6 → Fin R) : reverse r 5 = r 5 := by simp [reverse, Equiv.swap_apply_def]




























































































































































namespace Layout
variable {k : ℕ}








































end Layout


















































































































































































































































































































































































































































































































end NeighborWriter
end ExpandingCodes.Computation

end FlattenModule100


section FlattenModule101


set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation


























































end ExpandingCodes.PolynomialStretch

end FlattenModule101

/-! Inlined whole module: ExpandingCodes.Computation.SamplerRows -/
section FlattenModule102



set_option autoImplicit false

namespace ExpandingCodes.Computation.SamplerRows
open ExpandingCodes.PolynomialStretch EncodedTester

variable {q d k b n : ℕ}

























@[simp] theorem prefix_zero (O : EncodedGaussian.Operations (Fin q))
    (s : Fin (2*k*q*d) → Fin q) (h : Fin (k*q*q*q) → Fin b)
    (hr : 0 ≤ q^d) : rowsBefore (n := n) O s h 0 hr = [] := by
  simp [rowsBefore]










































end ExpandingCodes.Computation.SamplerRows

end FlattenModule102


section FlattenModule103










set_option autoImplicit false
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false
namespace ExpandingCodes.Computation.SamplerAssembly
open NKtLB UnaryArithmetic FieldPrograms ParameterPrograms SamplerEvaluation
open ExpandingCodes.PolynomialStretch
variable {R B : ℕ}
























































































































































































































































































































































































































































































































































































































































































































































































































































































 









































































































































































































































































open ExpandingCodes.PolynomialStretch






























































































































































namespace Concrete
open SamplerProgram









































































































































































































































































































































































































































































































































































































































































































































































end Concrete
end ExpandingCodes.Computation.SamplerAssembly

end FlattenModule103


section FlattenModule104




set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation








































end ExpandingCodes.PolynomialStretch

end FlattenModule104


section FlattenModule105




set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation
open SamplerAssembly.Concrete







































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

open NKtLB

theorem solution (degree n M : ℕ) (inp : Inputs) (d : ExpandingCodes.Computation.GaussianProgram.Store)
    (y : ExpandingCodes.PolynomialStretch.Word (ExpandingCodes.PolynomialStretch.rowCount degree n))
    (hc : ExpandingCodes.Computation.GaussianDriver.Common (ExpandingCodes.PolynomialStretch.fieldExponent degree n) (ExpandingCodes.PolynomialStretch.fieldExponent_pos degree n) (ExpandingCodes.PolynomialStretch.rowCount degree n) M d)
    (B : ExpandingCodes.Computation.Gaussian.Table (Fin (ExpandingCodes.PolynomialStretch.fieldSize degree n)) (ExpandingCodes.PolynomialStretch.rowCount degree n) (ExpandingCodes.PolynomialStretch.rowCount degree n))
    (ha : ExpandingCodes.Computation.GaussianProgram.MatrixStored d 0 (ExpandingCodes.PolynomialStretch.binaryTestTable degree n y)) (hb : ExpandingCodes.Computation.GaussianProgram.MatrixStored d 1 B) :
    ∃ (t : ℕ) (e : ExpandingCodes.Computation.TapeCfg 64 2 4260),t ≤ 100000*(M+1)^9 ∧
      ExpandingCodes.Computation.GaussianDriver.rankProgram.Stops inp (d.toCfg ExpandingCodes.Computation.GaussianDriver.rankProgram.entry) t e ∧
      ExpandingCodes.Computation.GaussianDriver.Common (ExpandingCodes.PolynomialStretch.fieldExponent degree n) (ExpandingCodes.PolynomialStretch.fieldExponent_pos degree n) (ExpandingCodes.PolynomialStretch.rowCount degree n) M e.store ∧
      e.reg 48 = (ExpandingCodes.PolynomialStretch.testMatrix (ExpandingCodes.PolynomialStretch.binaryGeometry degree n) y).rank ∧
      e.reg 62 = 0 ∧ e.roHead = d.roHead ∧ e.output = d.output := by
  exact @ExpandingCodes.Computation.GaussianDriver.rankProgram_stops_canonical degree n M inp d y hc B ha hb

