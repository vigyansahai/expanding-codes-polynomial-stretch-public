import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime
import Mathlib
import Theorems.Thm_ExpandingCodes_Computation_SourceFieldArithmetic_addition_stops
import Theorems.Thm_ExpandingCodes_Computation_SourceFieldArithmetic_multiply_stops

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





























private theorem indexEquiv_inverse_value (ell : ℕ) (c : Coefficients ell) :
    ((indexEquiv ell).symm c).val = ∑ j : Fin ell, (c j).val * 2 ^ j.val := rfl
































































































































































































end ExpandingCodes.PolynomialStretch.BinaryPolynomial

end FlattenModule1

/-! Inlined whole module: ExpandingCodes.Computation.BinaryField -/
section FlattenModule2


set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch.BinaryField

open Polynomial BinaryPolynomial

































































private theorem polynomial_add {ell : ℕ} (a b : Coefficients ell) :
    polynomial (add a b) = polynomial a + polynomial b := by
  simp only [polynomial, add, map_add, Finset.sum_add_distrib]

private theorem decode_add (ell : ℕ) (h : 0 < ell) (a b : Coefficients ell) :
    decode ell h (add a b) = decode ell h a + decode ell h b := by
  simp only [decode, polynomial_add, map_add]







































































































































































































private theorem multiply_inverse (ell : ℕ) (h : 0 < ell) (x : Coefficients ell)
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

private theorem decode_inverse (ell : ℕ) (h : 0 < ell) (x : Coefficients ell) :
    decode ell h (inverse ell h x) = (decode ell h x)⁻¹ := by
  by_cases hx : x = zero ell
  · subst x
    simp [inverse, decode_zero]
  · have hm := congrArg (decode ell h) (multiply_inverse ell h x hx)
    rw [decode_multiply, decode_one] at hm
    exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hm)







private theorem elements_addIndex (ell : ℕ) (h : 0 < ell) (i j : Fin (2 ^ ell)) :
    elements ell h (addIndex ell i j) = elements ell h i + elements ell h j := by
  change decode ell h (indexEquiv ell ((indexEquiv ell).symm
    (add (indexEquiv ell i) (indexEquiv ell j)))) = _
  rw [Equiv.apply_symm_apply, decode_add]
  rfl

private theorem elements_multiplyIndex (ell : ℕ) (h : 0 < ell) (i j : Fin (2 ^ ell)) :
    elements ell h (multiplyIndex ell h (selectedIndex ell h) (indexEquiv ell i)
      (indexEquiv ell j)) = elements ell h i * elements ell h j := by
  exact decode_multiply ell h (indexEquiv ell i) (indexEquiv ell j)

private theorem elements_inverseIndex (ell : ℕ) (h : 0 < ell) (i : Fin (2 ^ ell)) :
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


section FlattenModule4



set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch





















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





 private theorem getD_writeAt (l : List Sym) (h k : ℕ) (a : Sym) :
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

 





 







@[simp] private theorem unary_zero (n : ℕ) : unary n 0 = .bot := by simp [unary]
@[simp] private theorem unary_self_succ (n : ℕ) : unary (n+1) (n+1) = .one := by simp [unary]
@[simp] private theorem unary_after (n : ℕ) : unary n (n+1) = .blank := by simp [unary]

 







 







 


























































 





 












end ExpandingCodes.Computation

end FlattenModule7

/-! Inlined whole module: ExpandingCodes.Computation.Basic -/
section FlattenModule8


set_option autoImplicit false
open scoped Classical

namespace NKtLB.Machine

private theorem step_of_halt (M : NKtLB.Machine) (O : Set (List Bool)) (inp : Inputs)
    (c : Cfg M) (hc : c.state = M.halt) : M.step O inp c = c := by
  simp [step, hc]

private theorem run_succ (M : NKtLB.Machine) (O : Set (List Bool)) (inp : Inputs) (t : ℕ) :
    M.run O inp (t + 1) = M.step O inp (M.run O inp t) := by
  exact Function.iterate_succ_apply' _ _ _

private theorem run_add (M : NKtLB.Machine) (O : Set (List Bool)) (inp : Inputs) (t s : ℕ) :
    M.run O inp (t + s) = (M.step O inp)^[s] (M.run O inp t) := by
  simpa only [run, Nat.add_comm t s] using Function.iterate_add_apply (M.step O inp) s t M.init

private theorem run_stable_of_halt (M : NKtLB.Machine) (O : Set (List Bool)) (inp : Inputs)
    (t : ℕ) (ht : (M.run O inp t).state = M.halt) (s : ℕ) :
    M.run O inp (t + s) = M.run O inp t := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.add_succ, run_succ, ih, step_of_halt M O inp _ ht]

private theorem HaltsWith.mono {M : NKtLB.Machine} {O : Set (List Bool)} {inp : Inputs}
    {t T : ℕ} {z : List Sym} (h : M.HaltsWith O inp t z) (ht : t ≤ T) :
    M.HaltsWith O inp T z := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
  simpa only [HaltsWith, run_stable_of_halt M O inp t h.1 s] using h

private theorem HaltsWith.output_unique {M : NKtLB.Machine} {O : Set (List Bool)} {inp : Inputs}
    {t T : ℕ} {z z' : List Sym} (h : M.HaltsWith O inp t z)
    (h' : M.HaltsWith O inp T z') : z = z' := by
  rcases le_total t T with hle | hle
  · exact (h.mono hle).2.symm.trans h'.2
  · exact h.2.symm.trans (h'.mono hle).2

private theorem Computes.mono {M : NKtLB.Machine} {t T : ℕ} {u v : List Bool}
    (h : M.Computes t u v) (ht : t ≤ T) : M.Computes T u v :=
  HaltsWith.mono h ht

private theorem bitsSym_injective : Function.Injective bitsSym := by
  apply List.map_injective_iff.mpr
  intro a b h
  cases a <;> cases b <;> simp_all [Sym.ofBool]

private theorem Computes.output_unique {M : NKtLB.Machine} {t T : ℕ} {u v v' : List Bool}
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










private def workIdx (r : Fin R) : Fin (R+2) := ⟨r.val, by omega⟩

























































 




 










 



 































 




 












 












































 







 



























 




























 





 


 










 




























@[simp] private theorem workIdx_eq_iff (r s : Fin R) : workIdx r = workIdx s ↔ r = s := by
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







 





 


 





 


@[simp] private theorem bufferIdx_eq_iff (b c : Fin B) : bufferIdx R b = bufferIdx R c ↔ b = c := by
  simp [bufferIdx, Fin.ext_iff]




























































 




 










 



 


































 




 












 

















































 







 
































 

































 





 


 

































@[simp] private theorem workIdx_eq_iff (r s : Fin R) : workIdx B r = workIdx B s ↔ r = s := by
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




@[simp] private theorem store_toCfg (d : TapeStore R B) (j : Fin L) : (d.toCfg j).store = d := by
  cases d
  rfl
end TapeStore

namespace TapeInstr
variable {R B L K : ℕ}











 private theorem relabel_eq_halt (f : Fin L → Fin K) (i : TapeInstr R B L) :
    relabel f i = .halt ↔ i = .halt := by
  cases i <;> simp [relabel]
end TapeInstr

namespace TapeProgram
variable {R B L K : ℕ}















 








 private theorem Exec.one {P : TapeProgram R B L} {inp : Inputs} {c d : TapeCfg R B L}
    (ha : ¬ P.halted c) (hs : P.step inp c = d) : P.Exec inp c 1 d :=
  Exec.step ha hs (Exec.refl d)

 private theorem Exec.trans {P : TapeProgram R B L} {inp : Inputs}
    {c d e : TapeCfg R B L} {t s : ℕ}
    (h : P.Exec inp c t d) (k : P.Exec inp d s e) : P.Exec inp c (t+s) e := by
  induction h with
  | refl c => simpa using k
  | step active next tail ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Exec.step active next (ih k)

 private theorem step_relabel (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (f : Fin L → Fin K) (inp : Inputs) (c : TapeCfg R B L)
    (hc : Q.code (f c.pc) = TapeInstr.relabel f (P.code c.pc)) :
    Q.step inp (c.mapPC f) = (P.step inp c).mapPC f := by
  simp only [step, TapeCfg.mapPC, hc]
  cases h : P.code c.pc <;> simp only [TapeInstr.relabel]
  all_goals try rfl
  split <;> simp_all

/-- Relabeling preserves active traces even when the embedding redirects halt
instructions. Only labels actually executed before halt are constrained. -/
 private theorem Exec.relabel {P : TapeProgram R B L} {Q : TapeProgram R B K}
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






















 private theorem seq_code_left_active (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (j : Fin L) (hj : P.code j ≠ .halt) :
    (TapeProgram.seq P Q).code (leftLabel K j) = (P.code j).relabel (leftLabel K) := by
  simp only [seq, leftLabel, Equiv.symm_apply_apply]

 private theorem seq_code_left_halt (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (j : Fin L) (hj : P.code j = .halt) :
    (TapeProgram.seq P Q).code (leftLabel K j) = .jump (rightLabel L Q.entry) := by
  simp [seq, leftLabel, hj]

 private theorem seq_code_right (P : TapeProgram R B L) (Q : TapeProgram R B K) (j : Fin K) :
    (TapeProgram.seq P Q).code (rightLabel L j) = (Q.code j).relabel (rightLabel L) := by
  simp [seq, rightLabel]

/-- Exact compositional source cost: first routine, one linking jump, second routine. -/
 private theorem Stops.seq {P : TapeProgram R B L} {Q : TapeProgram R B K} {inp : Inputs}
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











 








 




















 private theorem loop_code_body_active (P : TapeProgram R B L) (r : Fin R)
    (j : Fin L) (hj : P.code j ≠ .halt) :
    (countedLoop P r).code (leftLabel 2 j) = (P.code j).relabel (leftLabel 2) := by
  simp only [countedLoop, leftLabel, Equiv.symm_apply_apply]

 private theorem loop_code_body_halt (P : TapeProgram R B L) (r : Fin R)
    (j : Fin L) (hj : P.code j = .halt) :
    (countedLoop P r).code (leftLabel 2 j) = .jump (loopHeader L) := by
  simp [countedLoop, leftLabel, hj]

 private theorem loop_code_header (P : TapeProgram R B L) (r : Fin R) :
    (countedLoop P r).code (loopHeader L) = .dec r (loopExit L) (leftLabel 2 P.entry) := by
  simp [countedLoop, loopHeader, rightLabel]

 private theorem loop_code_exit (P : TapeProgram R B L) (r : Fin R) :
    (countedLoop P r).code (loopExit L) = .halt := by
  simp [countedLoop, loopExit, rightLabel]





 private theorem loop_zero (P : TapeProgram R B L) (r : Fin R) (inp : Inputs)
    (d : TapeStore R B) (hd : d.reg r = 0) :
    (countedLoop P r).Stops inp (d.toCfg (loopHeader L)) 1 (d.toCfg (loopExit L)) := by
  constructor
  · apply Exec.one
    · change (countedLoop P r).code (loopHeader L) ≠ .halt
      rw [loop_code_header]
      simp
    · simp only [step, TapeStore.toCfg, loop_code_header, hd, ite_true]
  · exact loop_code_exit P r

 private theorem loop_positive_header (P : TapeProgram R B L) (r : Fin R) (inp : Inputs)
    (d : TapeStore R B) (hd : d.reg r ≠ 0) :
    (countedLoop P r).Exec inp (d.toCfg (loopHeader L)) 1
      (((decStore r d).toCfg P.entry).mapPC (leftLabel 2)) := by
  apply Exec.one
  · change (countedLoop P r).code (loopHeader L) ≠ .halt
    rw [loop_code_header]
    simp
  · simp only [step, TapeStore.toCfg, loop_code_header, if_neg hd]

 private theorem loop_body_return (P : TapeProgram R B L) (r : Fin R) (inp : Inputs)
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





@[simp] private theorem setReg_same (d : TapeStore R B) (r : Fin R) (m n : ℕ) :
    (d.setReg r m).setReg r n = d.setReg r n := by
  simp [setReg, Function.update_idem]

end TapeStore

namespace TapeMacros
variable {R B : ℕ}






 private theorem increment_stops (r : Fin R) (inp : Inputs) (d : TapeStore R B) :
    (increment r).Stops inp (d.toCfg 0) 1 ((d.setReg r (d.reg r + 1)).toCfg 1) := by
  constructor
  · apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, increment, TapeStore.toCfg]
    · simp [TapeProgram.step, increment, TapeStore.toCfg, TapeStore.setReg]
  · simp [TapeProgram.halted, increment, TapeStore.toCfg]






 private theorem clear_stops (r : Fin R) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
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











 private theorem transferStore_step (d : TapeStore R B) (src dst : Fin R) (hne : src ≠ dst)
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

 private theorem transfer_stops (src dst : Fin R) (hne : src ≠ dst) (inp : Inputs)
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










 private theorem distributeStore_step (d : TapeStore R B) (src dst tmp : Fin R)
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

 private theorem distribute_stops (src dst tmp : Fin R)
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







 private theorem copy_post (d : TapeStore R B) (src dst tmp : Fin R)
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

 private theorem copy_stops (src dst tmp : Fin R)
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





 private theorem addPreserving_post (d : TapeStore R B) (src dst tmp : Fin R)
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

 private theorem addPreserving_stops (src dst tmp : Fin R)
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

@[simp] private theorem setReg_self (d : TapeStore R B) (r : Fin R) :
    d.setReg r (d.reg r) = d := by simp [TapeStore.setReg]

@[simp] private theorem reg_set_same (d : TapeStore R B) (r : Fin R) (n : ℕ) :
    (d.setReg r n).reg r = n := by simp [TapeStore.setReg]




private theorem setReg_comm (d : TapeStore R B) (r s : Fin R) (m n : ℕ) (h : r ≠ s) :
    (d.setReg r m).setReg s n = (d.setReg s n).setReg r m := by
  simp only [TapeStore.setReg]
  congr 1
  exact Function.update_comm h m n d.reg








private theorem mulLoopStore_step (d : TapeStore R B) (a dst tmp count : Fin R)
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
private theorem mulLoop_stops (a dst tmp count : Fin R)
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










private theorem multiply_stops (a b dst tmp count : Fin R)
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








 private theorem SamePayload.refl (d : TapeStore R B) : SamePayload d d :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

 private theorem SamePayload.trans {d e f : TapeStore R B}
    (h : SamePayload d e) (k : SamePayload e f) : SamePayload d f :=
  ⟨h.roHead.trans k.roHead, h.output.trans k.output, fun b n => (h.symbol b n).trans (k.symbol b n)⟩

 private theorem setReg_payload (d : TapeStore R B) (r : Fin R) (n : ℕ) :
    SamePayload (d.setReg r n) d := ⟨rfl, rfl, fun _ _ => rfl⟩
end TapeStore

namespace TapeArrays
variable {R B : ℕ}
open TapeMacros






 private theorem moved_payload (d : TapeStore R B) (b : Fin B) (m : Move) :
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

@[simp] private theorem moved_reg (d : TapeStore R B) (b : Fin B) (m : Move) :
    (moved d b m).reg = d.reg := rfl

@[simp] private theorem moved_head (d : TapeStore R B) (b : Fin B) (m : Move) :
    (moved d b m).bufferHead = Function.update d.bufferHead b (Machine.moveHead m (d.bufferHead b)) := rfl








 private theorem seekRight_stops (r : Fin R) (b : Fin B) (inp : Inputs)
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













 private theorem reset_stops (b : Fin B) (inp : Inputs) (h : ℕ) (d : TapeStore R B)
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






















 





























 






















 








 









 










 



















































 private theorem fillStore_reg (b : Fin B) (s : Sym) (n : ℕ) (d : TapeStore R B) :
    (fillStore b s n d).reg = d.reg := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => exact ih _

 private theorem fillStore_roHead (b : Fin B) (s : Sym) (n : ℕ) (d : TapeStore R B) :
    (fillStore b s n d).roHead = d.roHead := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => exact ih _

 private theorem fillStore_output (b : Fin B) (s : Sym) (n : ℕ) (d : TapeStore R B) :
    (fillStore b s n d).output = d.output := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => exact ih _

 private theorem fillStore_head (b : Fin B) (s : Sym) (n : ℕ) (d : TapeStore R B) :
    (fillStore b s n d).bufferHead = Function.update d.bufferHead b (d.bufferHead b+n) := by
  induction n generalizing d with
  | zero => simp [fillStore]
  | succ n ih =>
    rw [fillStore, ih]
    simp [painted, cellStore, Machine.moveHead, Function.update_idem, Nat.add_assoc, Nat.add_comm]

 private theorem fillStore_symbol (b : Fin B) (s : Sym) (n : ℕ) (d : TapeStore R B)
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







 private theorem writeRun_stops (r : Fin R) (b : Fin B) (s : Sym) (inp : Inputs)
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








 private theorem writeDebit_stops (value width : Fin R) (hne : value ≠ width) (b : Fin B)
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










 private theorem writeBlock_stops (value width : Fin R) (hne : value ≠ width) (b : Fin B)
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






 private theorem writeBlockStore_reg (value width : Fin R) (b : Fin B) (v w : ℕ) (d : TapeStore R B) :
    (writeBlockStore value width b v w d).reg =
      ((d.setReg value 0).setReg width 0).reg := by
  simp [writeBlockStore, fillStore_reg, TapeStore.setReg, Function.update_idem]

 private theorem writeBlockStore_head (value width : Fin R) (b : Fin B) (v w : ℕ)
    (d : TapeStore R B) (hv : v ≤ w) :
    (writeBlockStore value width b v w d).bufferHead =
      Function.update d.bufferHead b (d.bufferHead b+w) := by
  have h : v+(w-v) = w := by omega
  simp [writeBlockStore, fillStore_head, TapeStore.setReg, Function.update_idem, Nat.add_assoc, h]

 private theorem writeBlockStore_roHead (value width : Fin R) (b : Fin B) (v w : ℕ) (d : TapeStore R B) :
    (writeBlockStore value width b v w d).roHead = d.roHead := by
  simp [writeBlockStore, fillStore_roHead, TapeStore.setReg]

 private theorem writeBlockStore_output (value width : Fin R) (b : Fin B) (v w : ℕ) (d : TapeStore R B) :
    (writeBlockStore value width b v w d).output = d.output := by
  simp [writeBlockStore, fillStore_output, TapeStore.setReg]

 private theorem writeBlockStore_symbol (value width : Fin R) (b : Fin B) (v w : ℕ)
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
 private theorem ThermometerAt.tail {d e : TapeStore R B} {b : Fin B} {w v : ℕ}
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


















 private theorem readTick_payload (width value : Fin R) (b : Fin B) (d : TapeStore R B) :
    TapeStore.SamePayload (readTickStore width value b d) d := by
  have hp := (moved_payload (TapeProgram.decStore width d) b .right).trans
    (TapeStore.setReg_payload d width (d.reg width-1))
  unfold readTickStore
  split
  · exact (TapeStore.setReg_payload _ value (d.reg value+1)).trans hp
  · exact hp

 private theorem readTick_head (width value : Fin R) (b : Fin B) (d : TapeStore R B) :
    (readTickStore width value b d).bufferHead =
      Function.update d.bufferHead b (d.bufferHead b+1) := by
  unfold readTickStore
  split <;> rfl

 private theorem readTick_reg (width value : Fin R) (hne : width ≠ value) (b : Fin B) (d : TapeStore R B) :
    (readTickStore width value b d).reg =
      Function.update (Function.update d.reg width (d.reg width-1)) value
        (d.reg value + readDelta d b) := by
  unfold readTickStore readDelta
  split
  · rfl
  · simp [TapeStore.setReg, moved, cellStore, TapeProgram.decStore,
      Function.update_of_ne (Ne.symm hne)]

 private theorem readTick_exec (width value : Fin R) (hne : width ≠ value) (b : Fin B)
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

 private theorem readBlock_stops (width value : Fin R) (hne : width ≠ value) (b : Fin B)
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









 private theorem seekEntry_stops (offset : Fin R) (b : Fin B) (inp : Inputs)
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







 private theorem ThermometerAt.of_payload {d e : TapeStore R B} {b : Fin B} {start w v : ℕ}
    (h : ThermometerAt d b start w v) (hp : TapeStore.SamePayload e d) :
    ThermometerAt e b start w v := by
  refine ⟨h.1, ?_⟩
  intro j hj
  rw [hp.symbol]
  exact h.2 j hj








 private theorem positionEntry_stops (index width offset tmp count : Fin R)
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

 































 private theorem entryAccessBound_le (d : TapeStore R B) (index width offset tmp count : Fin R)
    (b : Fin B) (M : ℕ) (hi : d.reg index ≤ M) (hw : d.reg width ≤ M)
    (ho : d.reg offset ≤ M) (ht : d.reg tmp ≤ M) (hc : d.reg count ≤ M)
    (hh : d.bufferHead b ≤ M) : entryAccessBound d index width offset tmp count b ≤ 50*(M+1)^2 := by
  have hp : d.reg index*d.reg width ≤ M*M := Nat.mul_le_mul hi hw
  have hq : d.reg width*(5*d.reg index+7) ≤ M*(5*M+7) :=
    Nat.mul_le_mul hw (by omega)
  unfold entryAccessBound positionBound entryOffset
  nlinarith






 private theorem readEntry_stops (index width offset tmp count value : Fin R)
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















 

























































 private theorem BottomMarked.marked {d : TapeStore R B} {b : Fin B} (h : BottomMarked d b) :
    Marked d b := ⟨h.1, fun k hk _ => h.2 k hk⟩

 private theorem BottomMarked.of_payload {d e : TapeStore R B} {b : Fin B}
    (h : BottomMarked d b) (hp : TapeStore.SamePayload e d) : BottomMarked e b := by
  constructor
  · rw [hp.symbol]
    exact h.1
  · intro k hk
    rw [hp.symbol]
    exact h.2 k hk

 















 


















































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



















private theorem branchZero_left (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (i : Fin L) : (branchZero r P Q).code (branchLeft K i) =
      (P.code i).relabel (branchLeft K) := by
  simp [branchZero, branchLeft, leftLabel]

private theorem branchZero_right (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K)
    (i : Fin K) : (branchZero r P Q).code (branchRight L i) =
      (Q.code i).relabel (branchRight L) := by
  simp [branchZero, branchRight, leftLabel, rightLabel]

private theorem branchZero_test (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K) :
    (branchZero r P Q).code (branchTest L K) =
      .dec r (branchLeft K P.entry) (branchRestore L K) := by
  simp [branchZero, branchTest, rightLabel]

private theorem branchZero_restore (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K) :
    (branchZero r P Q).code (branchRestore L K) = .inc r (branchRight L Q.entry) := by
  simp [branchZero, branchRestore, rightLabel]

private theorem branchZero_stops_zero (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K)
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

private theorem branchZero_stops_positive (r : Fin R) (P : TapeProgram R B L) (Q : TapeProgram R B K)
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

























private theorem skip_stops (inp : Inputs) (d : TapeStore R B) :
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








































































































































































private theorem setReg_bound (d : TapeStore R B) (r : Fin R) (n M : ℕ)
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
























































private theorem ltLoopStore_step (a b dst : Fin R)
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

private theorem ltLoop_stops (a b dst : Fin R)
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











private theorem reg_layout {N : ℕ} (r : Fin N → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i j : Fin N) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j; simp
  · simp [TapeStore.setReg, h, show r j ≠ r i from fun he => h (hr he)]













private theorem lessThanStore_value (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) :
    (lessThanStore r d).reg (r 2) = if d.reg (r 0)<d.reg (r 1) then 1 else 0 := by
  simp [lessThanStore, lessCore, lessPrepare, ltLoopStore, reg_layout r hr]







private theorem lessThanStore_scratch (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (j : Fin 6) (hj : j = 3 ∨ j = 4 ∨ j = 5) :
    (lessThanStore r d).reg (r j) = 0 := by
  rcases hj with rfl | rfl | rfl
  all_goals simp [lessThanStore, lessCore, lessPrepare, ltLoopStore, reg_layout r hr]

private theorem lessThanStore_bound (r : Fin 6 → Fin R) (hr : Function.Injective r)
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

private theorem lessThan_stops (r : Fin 6 → Fin R) (hr : Function.Injective r)
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












@[simp] private theorem Layout.reg_eq (l : Layout R) (i j : Fin 6) :
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

@[simp] private theorem uniformMean_const (c : ℝ) : uniformMean (fun _ : Ω => c) = c := by
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










































































































































































































































































































































































































































































































































@[simp] private theorem tapeData_setReg (d : TapeStore R B) (i : Fin R) (n : ℕ) :
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

/-! Inlined whole module: ExpandingCodes.Computation.SourceFieldArithmetic -/
section FlattenModule51


set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.SourceFieldArithmetic
open NKtLB FieldPrograms FieldConvolution FieldCertificates
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B L : ℕ}




























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































private theorem setOne_stops (x : Fin R) (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (setOne x).Stops inp (d.toCfg (setOne (B := B) x).entry) (d.reg x+3) e ∧ e.store = d.setReg x 1 := by
  have hc := TapeMacros.clear_stops x inp (d.reg x) d rfl
  have hi := TapeMacros.increment_stops x inp (d.setReg x 0)
  have hz : (d.setReg x 0).reg x = 0 := by simp [TapeStore.setReg]
  rw [hz,zero_add] at hi
  have hall := hc.seq hi
  refine ⟨((d.setReg x 0).setReg x 1).toCfg (1:Fin 2) |>.mapPC (TapeProgram.rightLabel 2),?_,?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · exact TapeStore.setReg_same d x 0 1




































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































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

private theorem reg_layout {L : ℕ} (r : Fin L → Fin R) (hr : Function.Injective r)
    (s : TapeStore R B) (i j : Fin L) (v : ℕ) :
    (s.setReg (r i) v).reg (r j)=if j=i then v else s.reg (r j) := by
  simp [TapeStore.setReg,Function.update,hr.eq_iff]

/-- A physical copy with its caller-counter bound. This does not touch any
buffer, head, output, or register outside destination/scratch. -/
private theorem copy_stops_bound (src dst tmp : Fin R)
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














private theorem lookupPrepare_bound (r : Fin 8 → Fin R) (s : TapeStore R B)
    (M : ℕ) (hs : ∀ j,s.reg j       ≤       M) : ∀ j,(lookupPrepare r s).reg j       ≤       M := by
  apply setReg_bound
  · exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hs (hs (r 1))) (by omega)
  · omega

/-- Actual 48-label source lookup. The index and original width counters remain
available to the caller; the physical buffer head ends after the selected block. -/
private theorem lookup_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ j,s.reg j       ≤       M) (hh : s.bufferHead b       ≤       M)
    (hm : TapeArrays.Marked s b) (v : ℕ)
    (hv : TapeArrays.ThermometerAt s b
      (TapeArrays.entryOffset (s.reg (r 0)) (s.reg (r 1))) (s.reg (r 1)) v) :
    ∃ t e, t       ≤       64*(M+1)^2 ∧
      (lookup r b).Stops inp (s.toCfg (lookup (B := B) r b).entry) t e ∧
      e.reg=lookupRegisters r v s ∧
      e.reg (r 6)=v ∧ e.reg (r 0)=s.reg (r 0) ∧ e.reg (r 1)=s.reg (r 1) ∧
      (∀ j,(∀ i : Fin 8,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j       ≤       M) ∧
      e.bufferHead=Function.update s.bufferHead b
        (TapeArrays.entryOffset (s.reg (r 0)) (s.reg (r 1))+s.reg (r 1)) ∧
      TapeStore.SamePayload e.store s := by
  obtain ⟨a,c,ha,hc,hcs,hcb⟩ := copy_stops_bound (r 1) (r 2) (r 7)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M s hs
  have hclear := TapeMacros.clear_stops (r 6) inp (c.reg (r 6)) c.store rfl
  have hpre : c.store.setReg (r 6) 0=lookupPrepare r s := by rw [hcs]; rfl
  have hpb := lookupPrepare_bound r s M hs
  have hpm : TapeArrays.Marked (lookupPrepare r s) b := hm
  have hpv : (lookupPrepare r s).reg (r 6)=0 := by simp [lookupPrepare]
  have hidx : (lookupPrepare r s).reg (r 0)=s.reg (r 0) := by
    simp [lookupPrepare,reg_layout r hr]
  have hwidth : (lookupPrepare r s).reg (r 2)=s.reg (r 1) := by
    simp [lookupPrepare,reg_layout r hr]
  have hpblock : TapeArrays.ThermometerAt (lookupPrepare r s) b
      (TapeArrays.entryOffset ((lookupPrepare r s).reg (r 0)) ((lookupPrepare r s).reg (r 2)))
      ((lookupPrepare r s).reg (r 2)) v := by rw [hidx,hwidth]; exact hv
  obtain ⟨btime,e,hbt,he,her,heh,hep⟩ := TapeArrays.readEntry_stops
    (r 0) (r 2) (r 3) (r 4) (r 5) (r 6)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    b inp (lookupPrepare r s) hpm hpv v hpblock
  have hlarge := TapeArrays.entryAccessBound_le (lookupPrepare r s)
    (r 0) (r 2) (r 3) (r 4) (r 5) b M
    (hpb _) (hpb _) (hpb _) (hpb _) (hpb _) hh
  have hreg : e.reg=lookupRegisters r v s := by
    rw [her]
    unfold lookupPrepare lookupRegisters
    funext j
    simp only [TapeStore.setReg]
    by_cases h₂ : j=r 2
    · subst j; simp [Function.update,hr.eq_iff]
    by_cases h₃ : j=r 3
    · subst j; simp [Function.update,hr.eq_iff]
    by_cases h₄ : j=r 4
    · subst j; simp [Function.update,hr.eq_iff]
    by_cases h₅ : j=r 5
    · subst j; simp [Function.update,hr.eq_iff]
    by_cases h₆ : j=r 6
    · subst j; simp [Function.update,hr.eq_iff]
    by_cases h₇ : j=r 7
    · subst j; simp [Function.update,hr.eq_iff]
    simp [Function.update,h₂,h₃,h₄,h₅,h₆,h₇]
  rw [← hpre] at he
  have hall := (hc.seq hclear).seq he
  refine ⟨a+1+(c.reg (r 6)+1)+1+btime,_,?_,hall,hreg,?_,?_,?_,?_,?_,?_,?_⟩
  · have hc₆ := hcb (r 6)
    nlinarith
  · rw [hreg]; simp [lookupRegisters,reg_layout r hr]
  · rw [hreg]; simp [lookupRegisters,reg_layout r hr]
  · rw [hreg]; simp [lookupRegisters,reg_layout r hr]
  · intro j hj; rw [hreg]; simp [lookupRegisters,TapeStore.setReg,hj]
  · intro j
    rw [hreg]
    unfold lookupRegisters
    apply setReg_bound
    · apply setReg_bound
      · apply setReg_bound
        · apply setReg_bound
          · apply setReg_bound
            · exact setReg_bound s _ 0 M hs (by omega)
            · omega
          · omega
        · omega
      · exact hv.1.trans (hs (r 1))
    · omega
  · rw [hidx,hwidth] at heh
    exact heh
  · exact hep.trans ⟨rfl,rfl,fun _ _ => rfl⟩










private theorem fieldLayout_injective (r : Fin 30 → Fin R) (hr : Function.Injective r) :
    Function.Injective (fieldLayout r) := by
  intro i j h
  have hh := congrArg Fin.val (hr h)
  exact Fin.ext hh

private theorem additionLayout_injective (r : Fin 30 → Fin R) (hr : Function.Injective r) :
    Function.Injective (additionLayout r) := by
  intro i j h
  by_cases hi : i=3 <;> by_cases hj : j=3
  · exact hi.trans hj.symm
  · simp only [additionLayout,if_pos hi,if_neg hj] at h
    have hh := congrArg Fin.val (hr h)
    simp only [fieldLayout,Fin.val_mk] at hh
    have := j.isLt
    omega
  · simp only [additionLayout,if_neg hi,if_pos hj] at h
    have hh := congrArg Fin.val (hr h)
    simp only [fieldLayout,Fin.val_mk] at hh
    have := i.isLt
    omega
  · simp only [additionLayout,if_neg hi,if_neg hj] at h
    exact fieldLayout_injective r hr h







private theorem addFrom_stops (r : Fin 30 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (a b : Fin (2^ell))
    (M : ℕ) (hM : 1       ≤       M) (s : TapeStore R B) (hs : ∀ j,s.reg j       ≤       M)
    (ha : s.reg (r 27)=a.val) (hb : s.reg (r 28)=b.val)
    (hN : s.reg (r 19)=3*ell+1) (hq : s.reg (r 23)=2^ell) :
    ∃ t e, t       ≤       3100*(M+1)^5 ∧
      (addFrom r).Stops inp (s.toCfg (addFrom (B := B) r).entry) t e ∧
      e.reg (r 29)=(ExpandingCodes.PolynomialStretch.BinaryField.addIndex ell a b).val ∧
      (∀ i : Fin 30,i=3 ∨ i=19 ∨ i=23 ∨ i=24 ∨ i=27 ∨ i=28 → e.reg (r i)=s.reg (r i)) ∧
      (∀ j,(∀ i : Fin 30,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j       ≤       M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨u,c,hu,hc,hcs,hcb⟩ := copy_stops_bound (r 27) (r 0) (r 2)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M s hs
  have hcval (i : Fin 30) : c.reg (r i)=if i=0 then s.reg (r 27) else if i=2 then 0 else s.reg (r i) := by
    change c.store.reg (r i)=_
    rw [hcs]
    simp [reg_layout r hr]
    split <;> split <;> simp_all
  obtain ⟨v,d,hv,hd,hds,hdv,hdi,hdo,hdb,hdt⟩ := SourceFieldArithmetic.addition_stops
    (additionLayout r) (additionLayout_injective r hr) inp ell a b M hM c.store hcb
    (by simpa [additionLayout,fieldLayout,hcval] using ha)
    (by simpa [additionLayout,fieldLayout,hcval] using hb)
    (by simpa [additionLayout,fieldLayout,hcval] using hN)
    (by simpa [additionLayout,fieldLayout,hcval] using hq)
  obtain ⟨w,e,hw,he,hes,heb⟩ := copy_stops_bound (r 20) (r 29) (r 2)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M d.store hdb
  have hall := (hc.seq hd).seq he
  have hd20 : d.reg (r 20)=(ExpandingCodes.PolynomialStretch.BinaryField.addIndex ell a b).val := by
    simpa [additionLayout,fieldLayout] using hdv
  have heval (i : Fin 30) : e.reg (r i)=if i=29 then d.reg (r 20) else if i=2 then 0 else d.reg (r i) := by
    change e.store.reg (r i)=_
    rw [hes]
    simp [reg_layout r hr]
    split <;> split <;> simp_all
  have houtside (i : Fin 30) (hi : i=3 ∨ i=27) :
      ∀ j : Fin 27,r i≠additionLayout r j := by
    intro j hj
    by_cases h3 : j=3
    · rw [additionLayout,if_pos h3] at hj
      have hval := congrArg Fin.val (hr hj)
      rcases hi with rfl|rfl <;> simp at hval
    · rw [additionLayout,if_neg h3] at hj
      have hval := congrArg Fin.val (hr hj)
      rcases hi with rfl|rfl
      · have heq : j=3 := Fin.ext (by simpa [fieldLayout] using hval.symm)
        exact h3 heq
      · have := j.isLt
        simp only [fieldLayout,Fin.val_mk] at hval
        omega
  refine ⟨u+1+v+1+w,_,?_,hall,?_,?_,?_,heb,?_⟩
  · have hp : M+1       ≤       (M+1)^5 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1       ≤       5 by decide)
    omega
  · rw [heval]; simp [hd20]
  · intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · rw [heval]; simp only [show (3:Fin 30)≠29 by decide,show (3:Fin 30)≠2 by decide,if_false]
      rw [hdo (r 3) (houtside 3 (Or.inl rfl))]
      change c.reg (r 3)=_
      simp [hcval]
    · have hh := hdi 19 (by decide) (by decide)
      simpa [heval,additionLayout,fieldLayout,hcval] using hh
    · have hh := hdi 23 (by decide) (by decide)
      simpa [heval,additionLayout,fieldLayout,hcval] using hh
    · have hh := hdi 24 (by decide) (by decide)
      simpa [heval,additionLayout,fieldLayout,hcval] using hh
    · rw [heval]; simp only [show (27:Fin 30)≠29 by decide,show (27:Fin 30)≠2 by decide,if_false]
      rw [hdo (r 27) (houtside 27 (Or.inr rfl))]
      change c.reg (r 27)=_
      simp [hcval]
    · have hh := hdi 3 (by decide) (by decide)
      simpa [heval,additionLayout,fieldLayout,hcval] using hh
  · intro j hj
    change e.store.reg j=_
    rw [hes]
    simp only [TapeStore.setReg,Function.update_of_ne (hj 2),Function.update_of_ne (hj 29)]
    have hjadd : ∀ i : Fin 27,j≠additionLayout r i := by
      intro i
      by_cases hi : i=3
      · simpa [additionLayout,hi] using hj 28
      · simpa [additionLayout,hi,fieldLayout] using hj ⟨i.val,by omega⟩
    rw [hdo j hjadd]
    change c.store.reg j=_
    rw [hcs]
    simp [TapeStore.setReg,hj]
  · change FieldConvolution.tapeData e.store=_
    rw [hes]
    simpa only [FieldConvolution.tapeData_setReg,hcs,FieldConvolution.tapeData_setReg] using hdt







private theorem multiplyFrom_stops (r : Fin 30 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (m a b : Fin (2^ell))
    (M : ℕ) (hM : 1       ≤       M) (s : TapeStore R B) (hs : ∀ j,s.reg j       ≤       M)
    (ha : s.reg (r 27)=a.val) (hb : s.reg (r 28)=b.val)
    (hm : s.reg (r 3)=2^ell+m.val) (hN : s.reg (r 19)=3*ell+1)
    (hq : s.reg (r 23)=2^ell) (hQ : s.reg (r 24)=2^(2*ell)) :
    ∃ t e, t       ≤       10100*(M+1)^6 ∧
      (multiplyFrom r).Stops inp (s.toCfg (multiplyFrom (B := B) r).entry) t e ∧
      e.reg (r 29)=(ExpandingCodes.PolynomialStretch.BinaryField.multiplyIndex ell h m
        (ExpandingCodes.PolynomialStretch.BinaryPolynomial.indexEquiv ell a)
        (ExpandingCodes.PolynomialStretch.BinaryPolynomial.indexEquiv ell b)).val ∧
      (∀ i : Fin 30,i=3 ∨ i=19 ∨ i=23 ∨ i=24 ∨ i=27 ∨ i=28 → e.reg (r i)=s.reg (r i)) ∧
      (∀ j,(∀ i : Fin 30,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j       ≤       M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨u,c,hu,hc,hcs,hcb⟩ := copy_stops_bound (r 27) (r 0) (r 2)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M s hs
  obtain ⟨v,f,hv,hf,hfs,hfb⟩ := copy_stops_bound (r 28) (r 1) (r 2)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M c.store hcb
  have hfval (i : Fin 30) : f.reg (r i)=
      if i=1 then s.reg (r 28) else if i=2 then 0 else if i=0 then s.reg (r 27) else s.reg (r i) := by
    change f.store.reg (r i)=_
    rw [hfs,hcs]
    by_cases h₁ : i=1 <;> by_cases h₂ : i=2 <;> by_cases h₀ : i=0 <;>
      simp_all [reg_layout r hr]
  obtain ⟨vtime,d,hvt,hd,hds,hdv,hdi,hdo,hdb,hdt⟩ := SourceFieldArithmetic.multiply_stops
    (fieldLayout r) (fieldLayout_injective r hr) inp ell h m a b M hM f.store hfb
    (by simpa [fieldLayout,hfval] using ha)
    (by simpa [fieldLayout,hfval] using hb)
    (by simpa [fieldLayout,hfval] using hm)
    (by simpa [fieldLayout,hfval] using hN)
    (by simpa [fieldLayout,hfval] using hq)
    (by simpa [fieldLayout,hfval] using hQ)
  obtain ⟨w,e,hw,he,hes,heb⟩ := copy_stops_bound (r 20) (r 29) (r 2)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M d.store hdb
  have hall := ((hc.seq hf).seq hd).seq he
  have hd20 : d.reg (r 20)=(ExpandingCodes.PolynomialStretch.BinaryField.multiplyIndex ell h m
        (ExpandingCodes.PolynomialStretch.BinaryPolynomial.indexEquiv ell a)
        (ExpandingCodes.PolynomialStretch.BinaryPolynomial.indexEquiv ell b)).val := by
    simpa [fieldLayout] using hdv
  have heval (i : Fin 30) : e.reg (r i)=if i=29 then d.reg (r 20) else if i=2 then 0 else d.reg (r i) := by
    change e.store.reg (r i)=_
    rw [hes]
    simp [reg_layout r hr]
    split <;> split <;> simp_all
  have houtside (i : Fin 30) (hi : 27        ≤        i.val) : ∀ j : Fin 27,r i≠fieldLayout r j := by
    intro j hj
    have hval := congrArg Fin.val (hr hj)
    have := j.isLt
    simp only [fieldLayout,Fin.val_mk] at hval
    omega
  refine ⟨u+1+v+1+vtime+1+w,_,?_,hall,?_,?_,?_,heb,?_⟩
  · have hp : M+1       ≤       (M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1       ≤       6 by decide)
    omega
  · rw [heval]; simp [hd20]
  · intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · have hh := hdi 3 (by decide)
      simpa [heval,fieldLayout,hfval] using hh
    · have hh := hdi 19 (by decide)
      simpa [heval,fieldLayout,hfval] using hh
    · have hh := hdi 23 (by decide)
      simpa [heval,fieldLayout,hfval] using hh
    · have hh := hdi 24 (by decide)
      simpa [heval,fieldLayout,hfval] using hh
    · rw [heval]; simp only [show (27:Fin 30)≠29 by decide,show (27:Fin 30)≠2 by decide,if_false]
      rw [hdo (r 27) (houtside 27 (by decide))]
      change f.reg (r 27)=_
      simp [hfval]
    · rw [heval]; simp only [show (28:Fin 30)≠29 by decide,show (28:Fin 30)≠2 by decide,if_false]
      rw [hdo (r 28) (houtside 28 (by decide))]
      change f.reg (r 28)=_
      simp [hfval]
  · intro j hj
    change e.store.reg j=_
    rw [hes]
    simp only [TapeStore.setReg,Function.update_of_ne (hj 2),Function.update_of_ne (hj 29)]
    have hjfield : ∀ i : Fin 27,j≠fieldLayout r i := by
      intro i
      exact hj ⟨i.val,by omega⟩
    rw [hdo j hjfield]
    change f.store.reg j=_
    rw [hfs,hcs]
    simp [TapeStore.setReg,hj]
  · change FieldConvolution.tapeData e.store=_
    rw [hes]
    simpa only [FieldConvolution.tapeData_setReg,hfs,hcs,FieldConvolution.tapeData_setReg] using hdt





























































































































































































































































































































































































































































































































































































































































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






private theorem decrement_stops (r : Fin R) (inp : Inputs) (d : TapeStore R B) :
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







































private theorem advance_stops (p : Digit R) (hp : p.1≠p.2)
    (inp : Inputs) (s : TapeStore R B) :
    (advance p).Stops inp (s.toCfg (advance (B := B) p).entry) 3
      ((advanceStore p s).toCfg (TapeProgram.rightLabel 2 (1 : Fin 2))) := by
  have h₁ := decrement_stops p.2 inp s
  have h₂ := TapeMacros.increment_stops p.1 inp (s.setReg p.2 (s.reg p.2-1))
  have hall := h₁.seq h₂
  simpa [advance,advanceStore,TapeStore.setReg,hp,TapeCfg.mapPC,TapeStore.toCfg,TapeProgram.seq,decrement] using hall

private theorem reset_stops (q tmp : Fin R) (p : Digit R)
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

private theorem resetStore_bound (q tmp : Fin R) (p : Digit R) (s : TapeStore R B)
    (M : ℕ) (hs : ∀ j,s.reg j ≤ M) : ∀ j,(resetStore q tmp p s).reg j ≤ M := by
  unfold resetStore
  apply setReg_bound
  · apply setReg_bound
    · exact setReg_bound s _ 0 M hs (by omega)
    · exact (Nat.sub_le _ _).trans (hs q)
  · omega

private theorem advanceStore_bound (p : Digit R) (s : TapeStore R B)
    (M : ℕ) (hs : ∀ j,s.reg j ≤ M) : ∀ j,(advanceStore p s).reg j ≤ M+1 := by
  unfold advanceStore
  apply setReg_bound
  · apply setReg_bound
    · exact fun j => (hs j).trans (by omega)
    · exact (Nat.sub_le _ _).trans ((hs p.2).trans (by omega))
  · have := hs p.1; omega

/-- Uniform source bound for the actual finite odometer. It is valid even for
arbitrary scratch contents; canonical digit invariants are proved separately. -/
private theorem program_stops (q tmp : Fin R) (ps : List (Digit R))
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

private theorem nextStore_fresh (q tmp : Fin R) (ps : List (Digit R))
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

private theorem nextStore_payload (q tmp : Fin R) (ps : List (Digit R)) (s : TapeStore R B) :
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












private theorem readings_congr (ps : List (Digit R)) (s e : TapeStore R B)
    (h : ∀ p∈ps,s.reg p.1=e.reg p.1) : readings ps s=readings ps e := by
  exact List.map_congr_left h

private theorem used_mem_left (ps : List (Digit R)) (p : Digit R) (hp : p∈ps) : p.1∈used ps := by
  induction ps with
  | nil => simp at hp
  | cons z ps ih =>
    simp only [List.mem_cons] at hp
    rcases hp with rfl|hp
    · simp [used]
    · simp [used,ih hp]

private theorem used_mem_right (ps : List (Digit R)) (p : Digit R) (hp : p∈ps) : p.2∈used ps := by
  induction ps with
  | nil => simp at hp
  | cons z ps ih =>
    simp only [List.mem_cons] at hp
    rcases hp with rfl|hp
    · simp [used]
    · simp [used,ih hp]

private theorem program_readings (q tmp : Fin R) (ps : List (Digit R))
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















private theorem initializeStore_fresh (q tmp : Fin R) (ps : List (Digit R))
    (s : TapeStore R B) (j : Fin R) (hjt : j≠tmp) (hj : j∉used ps) :
    (initializeStore q tmp ps s).reg j=s.reg j := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [used,List.mem_cons,not_or] at hj
    rw [initializeStore,ih _ hj.2.2]
    simp [resetStore,TapeStore.setReg,hjt,hj.1,hj.2.1]

private theorem initialize_stops (q tmp : Fin R) (ps : List (Digit R))
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

private theorem initializeStore_values (q tmp : Fin R) (ps : List (Digit R))
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

private theorem initializeStore_valid (q tmp : Fin R) (ps : List (Digit R))
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

private theorem program_valid (q tmp : Fin R) (ps : List (Digit R))
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
private theorem successor_number (q : ℕ) (hq : 1<q) (xs : List ℕ)
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

private theorem readings_bounded (q : Fin R) (ps : List (Digit R))
    (s : TapeStore R B) (hv : Valid q ps s) : ∀ x∈readings ps s,x<s.reg q := by
  intro x hx
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
  have := hv p hp
  omega

private theorem program_number (q tmp : Fin R) (ps : List (Digit R))
    (huniq : (q::tmp::used ps).Nodup) (s : TapeStore R B) (hv : Valid q ps s)
    (hq : 1<s.reg q) :
    Nat.ofDigits (s.reg q) (readings ps (nextStore q tmp ps s))=
      (Nat.ofDigits (s.reg q) (readings ps s)+1)%(s.reg q)^ps.length := by
  rw [program_readings q tmp ps huniq s hv,successor_number _ hq _ (readings_bounded q ps s hv)]
  simp [readings]

private theorem number_ofFn (q d : ℕ) (f : Fin d → ℕ) :
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

private theorem number_eq_finFunctionFinEquiv (q d : ℕ) (f : Fin d → Fin q) :
    Nat.ofDigits q (List.ofFn (fun i => (f i).val))=(finFunctionFinEquiv f).val := by
  rw [number_ofFn,finFunctionFinEquiv_apply]

private theorem canonical_digits (q d : ℕ) (f : Fin d → Fin q) (z : Fin (q^d))
    (hz : Nat.ofDigits q (List.ofFn (fun i => (f i).val))=z.val) :
    f=finFunctionFinEquiv.symm z := by
  apply finFunctionFinEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rw [← number_eq_finFunctionFinEquiv]
  exact hz









































private theorem used_mem_iff (ps : List (Digit R)) (j : Fin R) :
    j∈used ps ↔ ∃ p∈ps,j=p.1 ∨ j=p.2 := by
  induction ps with
  | nil => simp [used]
  | cons p ps ih => simp [used,ih,or_assoc]

private theorem nextStore_tmp_le (q tmp : Fin R) (ps : List (Digit R))
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
private theorem nextStore_bound (q tmp : Fin R) (ps : List (Digit R))
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

private theorem program_stops_valid (q tmp : Fin R) (ps : List (Digit R))
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
@[simp] private theorem toMatrix_ofMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    toMatrix (ofMatrix A) = A := by
  ext i j
  simp [toMatrix, ofMatrix]





@[simp] private theorem length_cells (m n : ℕ) : (cells m n).length = m*n := by
  simp [cells, List.length_flatMap, List.length_finRange]

@[simp] private theorem mem_cells {m n : ℕ} (p : Fin m × Fin n) : p ∈ cells m n := by
  simp [cells]
























































































private def Work.total (w : Work) : ℕ :=
  w.comparisons+w.inverses+w.arithmetic+w.reads+w.writes+w.enumerated






@[simp] private theorem Work.total_add (a b : Work) :
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































































@[simp] private theorem pivotEquiv_inl {m : ℕ} (p : Fin (m+1)) (u : PUnit.{1}) :
    pivotEquiv p (Sum.inl u) = p := by
  simp [pivotEquiv]

@[simp] private theorem pivotEquiv_inr {m : ℕ} (p : Fin (m+1)) (i : Fin m) :
    pivotEquiv p (Sum.inr i) = p.succAbove i := by
  simp [pivotEquiv]




































































end ExpandingCodes.Computation.Gaussian

end FlattenModule55

/-! Inlined whole module: ExpandingCodes.Computation.EncodedGaussian -/
section FlattenModule56




set_option autoImplicit false

namespace ExpandingCodes.Computation.EncodedGaussian

open Gaussian
























@[simp] private theorem toMatrix_mapTable {α β : Type*} (f : α → β) {m n : ℕ}
    (A : Table α m n) (i : Fin m) (j : Fin n) :
    toMatrix (mapTable f A) i j = f (toMatrix A i j) := by
  simp [mapTable, toMatrix, ofMatrix]

variable {α : Type*} [DecidableEq α]






























variable {F : Type*} [Field F] [DecidableEq F]
variable {O : Operations α} {decode : α → F}





















































end ExpandingCodes.Computation.EncodedGaussian

namespace ExpandingCodes.PolynomialStretch.BinaryField

open Computation.EncodedGaussian BinaryPolynomial













private theorem elements_zeroIndex (ell : ℕ) (h : 0 < ell) :
    elements ell h (zeroIndex ell) = 0 := by
  change decode ell h (indexEquiv ell ((indexEquiv ell).symm (zero ell))) = 0
  rw [Equiv.apply_symm_apply, decode_zero]

private theorem elements_oneIndex (ell : ℕ) (h : 0 < ell) :
    elements ell h (oneIndex ell) = 1 := by
  change decode ell h (indexEquiv ell ((indexEquiv ell).symm (one ell))) = 1
  rw [Equiv.apply_symm_apply, decode_one]

private theorem indexOperations_interpretation (ell : ℕ) (h : 0 < ell) :
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









@[simp] private theorem fullEvaluationMatrix_good {d n : ℕ} (g : Geometry d n)
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














@[simp] private theorem power_cost (O : Operations α) (x : α) (k : ℕ) :
    (power O x k).2 = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [power, ih]





















variable {F : Type*} [Field F] {O : Operations α} {decode : α → F}













private theorem sum_decode (h : Interpretation O decode) (xs : List (α × ℕ)) :
    decode (sum O xs).1 = (xs.map (fun x => decode x.1)).sum := by
  induction xs with
  | nil => exact h.zero
  | cons a as ih => simp [sum, h.add, ih]



































































































end ExpandingCodes.Computation.EncodedTester

namespace ExpandingCodes.PolynomialStretch

open Computation EncodedGaussian EncodedTester








@[simp] private theorem encodedExponentOrder_val {d n : ℕ} (g : Geometry d n)
    (a : Fin (rowCount d n)) (i : Fin d) :
    (encodedExponentOrder g a i).val = (digits (fieldSize d n) d a i).val := rfl








































































































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



private theorem workspace_injective (r : Fin 31 → Fin R) (hr : Function.Injective r) :
    Function.Injective (workspace r) := by
  intro i j h
  have hh := congrArg Fin.val (hr h)
  exact Fin.ext hh








private theorem Environment.frame {r : Fin 31 → Fin R} {ell : ℕ} {m : Fin (2^ell)}
    {s e : TapeStore R B} (h : Environment r ell m s)
    (hf : ∀ i : Fin 31,i=3 ∨ i=19 ∨ i=23 ∨ i=24 → e.reg (r i)=s.reg (r i)) :
    Environment r ell m e := by
  constructor
  · rw [hf 3 (by decide)]; exact h.modulus
  · rw [hf 19 (by decide)]; exact h.length
  · rw [hf 23 (by decide)]; exact h.cardinal
  · rw [hf 24 (by decide)]; exact h.square

private theorem Environment.setReg {r : Fin 31 → Fin R} (hr : Function.Injective r)
    {ell : ℕ} {m : Fin (2^ell)} {s : TapeStore R B} (h : Environment r ell m s)
    (j : Fin 31) (n : ℕ) (hj : j≠3 ∧ j≠19 ∧ j≠23 ∧ j≠24) :
    Environment r ell m (s.setReg (r j) n) := by
  apply h.frame
  intro i hi
  rcases hi with rfl|rfl|rfl|rfl <;> simp [reg_layout r hr,hj.1,hj.2.1,hj.2.2.1,hj.2.2.2,Ne.symm]

/-- Caller-friendly preserving copy into an arithmetic temporary. -/
private theorem copy_environment (r : Fin 31 → Fin R) (hr : Function.Injective r)
    (src : Fin R) (dst : Fin 31) (hsd : src≠r dst) (hst : src≠r 2)
    (hd : dst≠2) (hdenv : dst≠3 ∧ dst≠19 ∧ dst≠23 ∧ dst≠24)
    (inp : Inputs) (ell : ℕ) (m : Fin (2^ell)) (M : ℕ)
    (s : TapeStore R B) (hs : ∀ j,s.reg j              ≤              M) (henv : Environment r ell m s) :
    ∃ t e, t              ≤              7*M+7 ∧
      (TapeMacros.copy src (r dst) (r 2)).Stops inp
        (s.toCfg (TapeMacros.copy (B := B) src (r dst) (r 2)).entry) t e ∧
      e.store=(s.setReg (r dst) (s.reg src)).setReg (r 2) 0 ∧
      (∀ j,e.reg j              ≤              M) ∧ Environment r ell m e.store := by
  obtain ⟨t,e,ht,he,hes,heb⟩ := copy_stops_bound src (r dst) (r 2)
    hsd hst (hr.ne hd) inp M s hs
  refine ⟨t,e,ht,he,hes,heb,?_⟩
  rw [hes]
  exact (henv.setReg hr dst _ hdenv).setReg hr 2 0 (by decide)











private theorem term_stops (r : Fin 31 → Fin R) (hr : Function.Injective r)
    (x y : Fin R) (hx : ∀ i,x≠r i) (hy : ∀ i,y≠r i)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (m a b c : Fin (2^ell))
    (M : ℕ) (hM : 1              ≤              M) (s : TapeStore R B) (hs : ∀ j,s.reg j              ≤              M)
    (henv : Environment r ell m s) (ha : s.reg x=a.val) (hb : s.reg y=b.val)
    (hc : s.reg (r 30)=c.val) :
    ∃ t e, t              ≤              13300*(M+1)^6 ∧
      (term r x y).Stops inp (s.toCfg (term (B := B) r x y).entry) t e ∧
      e.reg (r 30)=(BinaryField.addIndex ell
        (BinaryField.multiplyIndex ell h m (indexEquiv ell a) (indexEquiv ell b)) c).val ∧
      Environment r ell m e.store ∧
      (∀ j,(∀ i,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j              ≤              M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁,he₁⟩ := copy_environment r hr x 27 (hx _) (hx _)
    (by decide) (by decide) inp ell m M s hs henv
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂,hb₂,he₂⟩ := copy_environment r hr y 28 (hy _) (hy _)
    (by decide) (by decide) inp ell m M c₁.store hb₁ he₁
  have hv₂ (i : Fin 31) : c₂.reg (r i)=
      if i=28 then s.reg y else if i=2 then 0 else if i=27 then s.reg x else s.reg (r i) := by
    change c₂.store.reg (r i)=_
    rw [hs₂,hs₁]
    simp [TapeStore.setReg,hy 27,hy 2]
    by_cases h₂₈ : i=28 <;> by_cases h₂ : i=2 <;> by_cases h₂₇ : i=27 <;>
      simp_all [reg_layout r hr,TapeStore.setReg,Function.update,hr.eq_iff]
  have hwr := workspace_injective r hr
  obtain ⟨t₃,c₃,ht₃,h₃,ha₃,hf₃,ho₃,hb₃,hd₃⟩ := multiplyFrom_stops (workspace r) hwr
    inp ell h m a b M hM c₂.store hb₂
    (by simpa [workspace,hv₂] using ha) (by simpa [workspace,hv₂] using hb)
    he₂.modulus he₂.length he₂.cardinal he₂.square
  have he₃ : Environment r ell m c₃.store := he₂.frame (by
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact hf₃ 3 (by decide)
    · exact hf₃ 19 (by decide)
    · exact hf₃ 23 (by decide)
    · exact hf₃ 24 (by decide))
  have hc₃ : c₃.reg (r 30)=c.val := by
    rw [ho₃ (r 30) (by
      intro i heq
      have hh := congrArg Fin.val (hr heq)
      have := i.isLt
      simp only [workspace,Fin.val_mk] at hh
      omega)]
    simpa [hv₂] using hc
  obtain ⟨t₄,c₄,ht₄,h₄,hs₄,hb₄,he₄⟩ := copy_environment r hr (r 29) 27
    (hr.ne (by decide)) (hr.ne (by decide)) (by decide) (by decide) inp ell m M c₃.store hb₃ he₃
  obtain ⟨t₅,c₅,ht₅,h₅,hs₅,hb₅,he₅⟩ := copy_environment r hr (r 30) 28
    (hr.ne (by decide)) (hr.ne (by decide)) (by decide) (by decide) inp ell m M c₄.store hb₄ he₄
  have hv₅a : c₅.reg (r 27)=(BinaryField.multiplyIndex ell h m (indexEquiv ell a) (indexEquiv ell b)).val := by
    change c₅.store.reg (r 27)=_
    rw [hs₅,hs₄]
    simpa [reg_layout r hr,workspace] using ha₃
  have hv₅b : c₅.reg (r 28)=c.val := by
    change c₅.store.reg (r 28)=_
    rw [hs₅,hs₄]
    simpa [reg_layout r hr] using hc₃
  obtain ⟨t₆,c₆,ht₆,h₆,ha₆,hf₆,ho₆,hb₆,hd₆⟩ := addFrom_stops (workspace r) hwr
    inp ell (BinaryField.multiplyIndex ell h m (indexEquiv ell a) (indexEquiv ell b)) c
    M hM c₅.store hb₅ hv₅a hv₅b he₅.length he₅.cardinal
  have he₆ : Environment r ell m c₆.store := he₅.frame (by
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact hf₆ 3 (by decide)
    · exact hf₆ 19 (by decide)
    · exact hf₆ 23 (by decide)
    · exact hf₆ 24 (by decide))
  obtain ⟨t₇,e,ht₇,h₇,hs₇,hb₇,he₇⟩ := copy_environment r hr (r 29) 30
    (hr.ne (by decide)) (hr.ne (by decide)) (by decide) (by decide) inp ell m M c₆.store hb₆ he₆
  have hall := (((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆).seq h₇
  refine ⟨t₁+1+t₂+1+t₃+1+t₄+1+t₅+1+t₆+1+t₇,_,?_,hall,?_,he₇,?_,hb₇,?_⟩
  · have hp₁ : M+1              ≤              (M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1              ≤              6 by decide)
    have hp₅ : (M+1)^5              ≤              (M+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
    omega
  · change e.store.reg (r 30)=_
    rw [hs₇]
    simpa [reg_layout r hr,workspace] using ha₆
  · intro j hj
    change e.store.reg j=_
    rw [hs₇]
    simp only [TapeStore.setReg,Function.update_of_ne (hj 2),Function.update_of_ne (hj 30)]
    have hjw : ∀ i : Fin 30,j≠workspace r i := fun i => hj ⟨i.val,by omega⟩
    rw [ho₆ j hjw]
    change c₅.store.reg j=_
    rw [hs₅,hs₄]
    simp only [TapeStore.setReg,Function.update_of_ne (hj 2),Function.update_of_ne (hj 28),
      Function.update_of_ne (hj 27)]
    rw [ho₃ j hjw]
    change c₂.store.reg j=_
    rw [hs₂,hs₁]
    simp [TapeStore.setReg,hj]
  · change FieldConvolution.tapeData e.store=_
    rw [hs₇]
    simp only [FieldConvolution.tapeData_setReg]
    rw [hd₆,hs₅,hs₄]
    simp only [FieldConvolution.tapeData_setReg]
    rw [hd₃,hs₂,hs₁]
    simp only [FieldConvolution.tapeData_setReg]






























































private theorem zeroIndex_value (ell : ℕ) : (BinaryField.zeroIndex ell).val=0 := by
  rw [BinaryField.zeroIndex,BinaryPolynomial.indexEquiv_inverse_value]
  simp [BinaryField.zero]























































































private theorem Environment.setExternal {r : Fin 31 → Fin R} {ell : ℕ} {m : Fin (2^ell)}
    {s : TapeStore R B} (h : Environment r ell m s) (j : Fin R) (n : ℕ)
    (hj : ∀ i,j≠r i) : Environment r ell m (s.setReg j n) := by
  apply h.frame
  intro i hi
  simp [TapeStore.setReg,Ne.symm (hj i)]



private theorem powerWorkspace_injective (r : Fin 32 → Fin R) (hr : Function.Injective r) :
    Function.Injective (powerWorkspace r) := by
  intro i j h
  have hh := congrArg Fin.val (hr h)
  exact Fin.ext hh

private theorem powerOutside (r : Fin 32 → Fin R) (hr : Function.Injective r) :
    ∀ i : Fin 31,r 31≠powerWorkspace r i := by
  intro i heq
  change r (31 : Fin 32)=r ⟨i.val,by omega⟩ at heq
  have hh := congrArg (Fin.val : Fin 32 → ℕ) (hr heq)
  have := i.isLt
  simp only [Fin.val_mk] at hh
  omega

private theorem add_zeroIndex_right (ell : ℕ) (h : 0<ell) (a : Fin (2^ell)) :
    BinaryField.addIndex ell a (BinaryField.zeroIndex ell)=a := by
  have hi := BinaryField.indexOperations_interpretation ell h
  apply hi.injective
  change BinaryField.elements ell h ((BinaryField.indexOperations ell h).add a
    (BinaryField.indexOperations ell h).zero)=_
  rw [hi.add,hi.zero,add_zero]







private theorem powerStep_stops (r : Fin 32 → Fin R) (hr : Function.Injective r)
    (x : Fin R) (hx : ∀ i,x≠r i) (inp : Inputs) (ell : ℕ) (h : 0<ell)
    (a alpha : Fin (2^ell)) (M : ℕ) (hM : 1            ≤            M) (s : TapeStore R B)
    (hs : ∀ j,s.reg j            ≤            M) (henv : Environment (powerWorkspace r) ell (selectedIndex ell h) s)
    (ha : s.reg (r 31)=a.val) (hxv : s.reg x=alpha.val) :
    ∃ t e, t            ≤            13400*(M+1)^6 ∧
      (powerStep r x).Stops inp (s.toCfg (powerStep (B := B) r x).entry) t e ∧
      e.reg (r 31)=((BinaryField.indexOperations ell h).mul a alpha).val ∧
      Environment (powerWorkspace r) ell (selectedIndex ell h) e.store ∧
      (∀ j,(∀ i,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j            ≤            M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  have hwr := powerWorkspace_injective r hr
  have hclear := TapeMacros.clear_stops (r 30) inp (s.reg (r 30)) s rfl
  have hs₁ : ∀ j,(s.setReg (r 30) 0).reg j            ≤            M := setReg_bound s _ 0 M hs (by omega)
  have he₁ : Environment (powerWorkspace r) ell (selectedIndex ell h) (s.setReg (r 30) 0) :=
    henv.setReg hwr 30 0 (by decide)
  obtain ⟨t,d,ht,hd,hdv,hde,hdo,hdb,hdt⟩ := term_stops (powerWorkspace r) hwr (r 31) x
    (powerOutside r hr) (fun i => hx ⟨i.val,by omega⟩) inp ell h (selectedIndex ell h)
    a alpha (BinaryField.zeroIndex ell) M hM (s.setReg (r 30) 0) hs₁ he₁
    (by simpa [reg_layout r hr] using ha)
    (by simpa [TapeStore.setReg,hx 30] using hxv)
    (by simp [powerWorkspace,zeroIndex_value])
  obtain ⟨u,e,hu,he,hes,heb⟩ := copy_stops_bound (r 30) (r 31) (r 2)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M d.store hdb
  have hall := (hclear.seq hd).seq he
  refine ⟨s.reg (r 30)+1+1+t+1+u,_,?_,hall,?_,?_,?_,heb,?_⟩
  · have hp : M+1            ≤            (M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1            ≤            6 by decide)
    have hcounter := hs (r 30)
    omega
  · change e.store.reg (r 31)=_
    rw [hes]
    simp only [reg_layout r hr,show (31:Fin 32)≠2 by decide,if_false,if_true]
    rw [add_zeroIndex_right ell h] at hdv
    exact hdv
  · rw [hes]
    exact (hde.setExternal (r 31) _ (powerOutside r hr)).setReg hwr 2 0 (by decide)
  · intro j hj
    change e.store.reg j=_
    rw [hes]
    simp only [TapeStore.setReg,Function.update_of_ne (hj 2),Function.update_of_ne (hj 31)]
    rw [hdo j (fun i => hj ⟨i.val,by omega⟩)]
    simp [TapeStore.setReg,hj 30]
  · change FieldConvolution.tapeData e.store=_
    rw [hes]
    simpa only [FieldConvolution.tapeData_setReg] using hdt









































private theorem oneIndex_value (ell : ℕ) (h : 0<ell) : (BinaryField.oneIndex ell).val=1 := by
  rw [BinaryField.oneIndex,indexEquiv_inverse_value]
  rw [Finset.sum_eq_single (⟨0,h⟩ : Fin ell)]
  · simp [BinaryField.one,ZMod.val_one_eq_one_mod]
  · intro i hi hne
    have hiz : i.val≠0 := fun he => hne (Fin.ext he)
    simp [BinaryField.one,hiz]
  · simp

private theorem power_iterate (ell : ℕ) (h : 0<ell) (alpha : Fin (2^ell)) (j : ℕ) :
    (fun z => (BinaryField.indexOperations ell h).mul z alpha)^[j] (BinaryField.oneIndex ell)=
      (EncodedTester.power (BinaryField.indexOperations ell h) alpha j).1 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih]; rfl

















































































































































































































































































































































































































































































































































































namespace Storage






































@[simp] private theorem point_val (d k : ℕ) (j : Fin d) : (point d k j).val=80+j.val := rfl
@[simp] private theorem countdown_val (d k : ℕ) (j : Fin d) : (countdown d k j).val=80+d+j.val := rfl
@[simp] private theorem coefficient_val (d k : ℕ) (j : Fin d) : (coefficient d k j).val=80+2*d+j.val := rfl

end Storage

namespace Storage






















end Storage





































































namespace Storage



















































































































































































end Storage




namespace Storage





















@[simp] private theorem pointPairs_length (d k : ℕ) : (pointPairs d k).length=d := by simp [pointPairs]












































end Storage

























































































































































































































































































































































































































































































































































































end ExpandingCodes.Computation.SamplerProgram

end FlattenModule61

/-! Inlined whole module: ExpandingCodes.Computation.TesterPowers -/
section FlattenModule62


set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterPowers
open NKtLB SamplerEvaluation SamplerProgram
open ExpandingCodes.PolynomialStretch BinaryPolynomial
open FieldPrograms UnaryArithmetic
variable {R B : ℕ}




private theorem scalar_injective (r : Fin 33 → Fin R) (hr : Function.Injective r) :
    Function.Injective (scalar r) := by
  intro i j hij
  have hh := congrArg (Fin.val : Fin 33 → ℕ) (hr hij)
  exact Fin.ext hh

private theorem count_outside (r : Fin 33 → Fin R) (hr : Function.Injective r) :
    ∀ i : Fin 32,r 32≠scalar r i := by
  intro i heq
  have hh := congrArg Fin.val (hr heq)
  have hi := i.isLt
  simp only [scalar,Fin.val_mk] at hh
  omega






private theorem powerLoop_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (x : Fin R) (hx : ∀ i,x≠r i) (inp : Inputs) (ell : ℕ) (h : 0<ell)
    (alpha : Fin (2^ell)) (M : ℕ) (hM : 1≤M) (n : ℕ)
    (s : TapeStore R B) (hs : ∀ i,s.reg i≤M)
    (henv : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) s)
    (a : Fin (2^ell)) (ha : s.reg (r 31)=a.val) (hxv : s.reg x=alpha.val)
    (hn : s.reg (r 32)=n) :
    ∃ t e, t≤n*(13400*(M+1)^6+2)+1 ∧
      (powerLoop r x).Stops inp (s.toCfg (powerLoop (B := B) r x).entry) t e ∧
      e.reg (r 31)=((fun z => (BinaryField.indexOperations ell h).mul z alpha)^[n] a).val ∧
      e.reg (r 32)=0 ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → e.reg i=s.reg i) ∧
      (∀ i,e.reg i≤M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  induction n generalizing s a with
  | zero =>
    refine ⟨1,s.toCfg (TapeProgram.loopExit 862),by simp,?_,ha,hn,henv,fun _ _ => rfl,hs,rfl⟩
    exact TapeProgram.loop_zero (powerStep (scalar r) x) (r 32) inp s hn
  | succ n ih =>
    let d := s.setReg (r 32) n
    have hd : ∀ i,d.reg i≤M := setReg_bound s _ n M hs (by have := hs (r 32); omega)
    have hde : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) d :=
      henv.setExternal (r 32) n (fun i => count_outside r hr ⟨i.val,by omega⟩)
    have hda : d.reg (r 31)=a.val := by simpa [d,reg_layout r hr] using ha
    have hdx : d.reg x=alpha.val := by simpa [d,TapeStore.setReg,hx 32] using hxv
    obtain ⟨u,c,hu,hc,hcv,hce,hco,hcb,hct⟩ := powerStep_stops (scalar r)
      (scalar_injective r hr) x (fun i => hx ⟨i.val,by omega⟩) inp ell h a alpha M hM d hd hde hda hdx
    have hcn : c.reg (r 32)=n := by
      rw [hco (r 32) (count_outside r hr)]
      simp [d]
    obtain ⟨t,e,ht,he,hev,hen,hee,heo,heb,het⟩ := ih c.store hcb hce
      ((BinaryField.indexOperations ell h).mul a alpha) (by simpa [scalar] using hcv)
      (by change c.reg x=_; rw [hco x (fun i => hx ⟨i.val,by omega⟩)]; exact hdx) hcn
    have hheader := TapeProgram.loop_positive_header (powerStep (scalar r) x) (r 32) inp s (by omega)
    have hdstore : TapeProgram.decStore (r 32) s=d := by
      simp [TapeProgram.decStore,d,TapeStore.setReg,hn]
    rw [hdstore] at hheader
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (powerStep (scalar r) x) (r 32))
    have hreturn := TapeProgram.loop_body_return (powerStep (scalar r) x) (r 32) inp c hc.halted
    have hall := ((hheader.trans hrun).trans hreturn).trans he.exec
    refine ⟨1+u+1+t,e,?_,⟨hall,he.halted⟩,?_,hen,hee,?_,heb,?_⟩
    · rw [Nat.succ_mul]; omega
    · simpa only [Function.iterate_succ_apply] using hev
    · intro i hi
      rw [heo i hi]
      change c.reg i=_
      rw [hco i (fun v => hi ⟨v.val,by omega⟩)]
      simp [d,TapeStore.setReg,hi 32]
    · simpa only [d,FieldConvolution.tapeData_setReg] using het.trans hct







private theorem power_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (x exponent : Fin R) (hx : ∀ i,x≠r i) (he : ∀ i,exponent≠r i)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (alpha : Fin (2^ell))
    (M : ℕ) (hM : 1≤M) (s : TapeStore R B) (hs : ∀ i,s.reg i≤M)
    (henv : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) s)
    (hxv : s.reg x=alpha.val) :
    ∃ t e, t≤(s.reg exponent+1)*(13420*(M+1)^6) ∧
      (power r x exponent).Stops inp (s.toCfg (power (B := B) r x exponent).entry) t e ∧
      e.reg (r 31)=(EncodedTester.power (BinaryField.indexOperations ell h) alpha (s.reg exponent)).1.val ∧
      e.reg (r 32)=0 ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → e.reg i=s.reg i) ∧
      (∀ i,e.reg i≤M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨u,c,hu,hc,hcs,hcb⟩ := copy_stops_bound exponent (r 32) (r 2)
    (he _) (he _) (hr.ne (by decide)) inp M s hs
  obtain ⟨d,hd,hds⟩ := SourceFieldArithmetic.setOne_stops (r 31) inp c.store
  have hdstore : d.store=((s.setReg (r 32) (s.reg exponent)).setReg (r 2) 0).setReg (r 31) 1 := by
    rw [hds,hcs]
  have hdb : ∀ i,d.reg i≤M := by
    change ∀ i,d.store.reg i≤M
    rw [hds]; exact setReg_bound c.store _ 1 M hcb hM
  have hde : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) d.store := by
    rw [hdstore]
    exact ((henv.setExternal (r 32) _ (fun i => count_outside r hr ⟨i.val,by omega⟩)).setReg
      (powerWorkspace_injective _ (scalar_injective r hr)) 2 0 (by decide)).setExternal
      (r 31) 1 (powerOutside _ (scalar_injective r hr))
  obtain ⟨t,e,ht,hloop,hev,hen,hee,heo,heb,het⟩ := powerLoop_stops r hr x hx inp ell h alpha M hM
    (s.reg exponent) d.store hdb hde (BinaryField.oneIndex ell)
    (by rw [hdstore]; simp [oneIndex_value ell h])
    (by rw [hdstore]; simpa [TapeStore.setReg,hx] using hxv)
    (by rw [hdstore]; simp [reg_layout r hr])
  have hall := (hc.seq hd).seq hloop
  refine ⟨u+1+(c.reg (r 31)+3)+1+t,_,?_,hall,?_,hen,hee,?_,heb,?_⟩
  · have hp : M+1≤(M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1≤6 by decide)
    have hb31 := hcb (r 31)
    have hp0 : 1≤(M+1)^6 := by omega
    have hfactor : 13400*(M+1)^6+2≤13420*(M+1)^6 := by omega
    have htime := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (s.reg exponent) hfactor) 1)
    rw [Nat.add_mul,Nat.one_mul]
    omega
  · simpa only [power_iterate ell h alpha (s.reg exponent)] using hev
  · intro i hi
    rw [heo i hi,hdstore]
    simp [TapeStore.setReg,hi]
  · simpa only [hdstore,FieldConvolution.tapeData_setReg] using het










private theorem factor_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (out exponent x : Fin R) (hout : ∀ i,out≠r i) (he : ∀ i,exponent≠r i)
    (hx : ∀ i,x≠r i) (inp : Inputs) (ell : ℕ) (h : 0<ell) (alpha a : Fin (2^ell))
    (M : ℕ) (hM : 1≤M) (s : TapeStore R B) (hs : ∀ i,s.reg i≤M)
    (henv : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) s)
    (hxv : s.reg x=alpha.val) (ha : s.reg out=a.val) :
    ∃ t e,t≤27000*(M+1)^7 ∧
      (factor r out exponent x).Stops inp (s.toCfg (factor (B := B) r out exponent x).entry) t e ∧
      e.reg out=((BinaryField.indexOperations ell h).mul
        (EncodedTester.power (BinaryField.indexOperations ell h) alpha (s.reg exponent)).1 a).val ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → i≠out → e.reg i=s.reg i) ∧
      (∀ i,e.reg i≤M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨t,c,ht,hc,hcv,hcn,hce,hco,hcb,hct⟩ := power_stops r hr x exponent hx he inp ell h alpha M hM s hs henv hxv
  obtain ⟨u,d,hu,hd,hdv,hde,hdo,hdb,hdt⟩ := powerStep_stops (scalar r) (scalar_injective r hr)
    out (fun i => hout ⟨i.val,by omega⟩) inp ell h
    (EncodedTester.power (BinaryField.indexOperations ell h) alpha (s.reg exponent)).1 a M hM c.store hcb hce
    (by simpa [scalar] using hcv) (by change c.reg out=_; rw [hco out hout]; exact ha)
  obtain ⟨v,e,hv,he',hes,heb⟩ := copy_stops_bound (r 31) out (r 2)
    (Ne.symm (hout _)) (hr.ne (by decide)) (hout _) inp M d.store hdb
  have hall := (hc.seq hd).seq he'
  refine ⟨t+1+u+1+v,_,?_,hall,?_,?_,?_,heb,?_⟩
  · have hp : M+1≤(M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1≤6 by decide)
    have hp₆ : (M+1)^6≤(M+1)^7 := Nat.pow_le_pow_right (by omega) (by decide)
    have hpow : (s.reg exponent+1)*(M+1)^6≤(M+1)^7 := by
      calc
        _ ≤ (M+1)*(M+1)^6 := Nat.mul_le_mul_right _ (by have := hs exponent; omega)
        _ = (M+1)^7 := by ring
    have ht' : t≤13420*(M+1)^7 := by nlinarith [ht]
    omega
  · change e.store.reg out=_
    rw [hes]
    simpa [TapeStore.setReg,hout,scalar] using hdv
  · rw [hes]
    exact (hde.setExternal out _ (fun i => hout ⟨i.val,by omega⟩)).setReg
      (powerWorkspace_injective _ (scalar_injective r hr)) 2 0 (by decide)
  · intro i hi hio
    change e.store.reg i=_
    rw [hes]
    simp only [TapeStore.setReg,Function.update_of_ne (hi 2),Function.update_of_ne hio]
    rw [hdo i (fun j => hi ⟨j.val,by omega⟩)]
    change c.reg i=_
    exact hco i hi
  · change FieldConvolution.tapeData e.store=_
    rw [hes]
    simpa only [FieldConvolution.tapeData_setReg] using hdt.trans hct


















private theorem productValue_eq (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell))
    (exponents : Fin R → ℕ) (ps : List (Fin R × Fin R)) :
    productValue ell h values exponents ps=(EncodedTester.product (BinaryField.indexOperations ell h)
      (ps.map fun p => EncodedTester.power (BinaryField.indexOperations ell h) (values p.2) (exponents p.1))).1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [productValue,List.map_cons,EncodedTester.product,ih]

private theorem productCore_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (out : Fin R) (hout : ∀ i,out≠r i) (ps : List (Fin R × Fin R))
    (hp : ∀ p∈ps,(∀ i,p.1≠r i) ∧ (∀ i,p.2≠r i) ∧ p.1≠out ∧ p.2≠out)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell)) (exponents : Fin R → ℕ)
    (M : ℕ) (hM : 1≤M) (s : TapeStore R B) (hs : ∀ i,s.reg i≤M)
    (henv : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) s)
    (hv : ∀ p∈ps,s.reg p.2=(values p.2).val ∧ s.reg p.1=exponents p.1)
    (ha : s.reg out=1) :
    ∃ t e,t≤ps.length*(27000*(M+1)^7+1) ∧
      (productCore r out ps).Stops inp (s.toCfg (productCore (B := B) r out ps).entry) t e ∧
      e.reg out=(productValue ell h values exponents ps).val ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → i≠out → e.reg i=s.reg i) ∧
      (∀ i,e.reg i≤M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  induction ps generalizing s with
  | nil =>
    refine ⟨0,s.toCfg ⟨0,by simp [productLabels]⟩,by simp,TapeProgram.skip_stops inp s,?_,henv,fun _ _ _ => rfl,hs,rfl⟩
    simpa [productValue,oneIndex_value ell h] using ha
  | cons p ps ih =>
    obtain ⟨t,c,ht,hc,hcv,hce,hco,hcb,hct⟩ := ih
      (fun a ha => hp a (by simp [ha])) s hs henv (fun a ha => hv a (by simp [ha])) ha
    have hpp := hp p (by simp)
    have hvp := hv p (by simp)
    have hcexp : c.reg p.1=exponents p.1 := (hco p.1 hpp.1 hpp.2.2.1).trans hvp.2
    obtain ⟨u,e,hu,he,hev,hee,heo,heb,het⟩ := factor_stops r hr out p.1 p.2 hout hpp.1 hpp.2.1
      inp ell h (values p.2) (productValue ell h values exponents ps) M hM c.store hcb hce
      ((hco p.2 hpp.2.1 hpp.2.2.2).trans hvp.1) hcv
    have hall := hc.seq he
    refine ⟨t+1+u,_,?_,hall,?_,hee,?_,heb,het.trans hct⟩
    · change t+1+u≤(ps.length+1)*(27000*(M+1)^7+1)
      rw [Nat.add_mul,Nat.one_mul]; omega
    · simpa only [productValue,hcexp] using hev
    · intro i hi hio
      exact (heo i hi hio).trans (hco i hi hio)







private theorem product_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (out : Fin R) (hout : ∀ i,out≠r i) (ps : List (Fin R × Fin R))
    (hp : ∀ p∈ps,(∀ i,p.1≠r i) ∧ (∀ i,p.2≠r i) ∧ p.1≠out ∧ p.2≠out)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell)) (exponents : Fin R → ℕ)
    (M : ℕ) (hM : 1≤M) (s : TapeStore R B) (hs : ∀ i,s.reg i≤M)
    (henv : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) s)
    (hv : ∀ p∈ps,s.reg p.2=(values p.2).val ∧ s.reg p.1=exponents p.1) :
    ∃ t e,t≤(ps.length+1)*(27020*(M+1)^7) ∧
      (product r out ps).Stops inp (s.toCfg (product (B := B) r out ps).entry) t e ∧
      e.reg out=(productValue ell h values exponents ps).val ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → i≠out → e.reg i=s.reg i) ∧
      (∀ i,e.reg i≤M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨c,hc,hcs⟩ := SourceFieldArithmetic.setOne_stops out inp s
  have hcb : ∀ i,c.reg i≤M := by
    change ∀ i,c.store.reg i≤M
    rw [hcs]; exact setReg_bound s _ 1 M hs hM
  have hce : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) c.store := by
    rw [hcs]; exact henv.setExternal out 1 (fun i => hout ⟨i.val,by omega⟩)
  have hcv : ∀ p∈ps,c.store.reg p.2=(values p.2).val ∧ c.store.reg p.1=exponents p.1 := by
    intro p hpm
    have hh := hp p hpm
    rw [hcs]
    simpa [TapeStore.setReg,hh.2.2.1,hh.2.2.2] using hv p hpm
  obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := productCore_stops r hr out hout ps hp inp ell h values exponents M hM
    c.store hcb hce hcv (by rw [hcs]; simp)
  have hall := hc.seq he
  refine ⟨s.reg out+3+1+t,_,?_,hall,hev,hee,?_,heb,?_⟩
  · have hp₁ : M+1≤(M+1)^7 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1≤7 by decide)
    have hbout := hs out
    have hfactor : 27000*(M+1)^7+1≤27020*(M+1)^7 := by omega
    have htime := ht.trans (Nat.mul_le_mul_left ps.length hfactor)
    rw [Nat.add_mul,Nat.one_mul]; omega
  · intro i hi hio
    rw [heo i hi hio,hcs]
    simp [TapeStore.setReg,hio]
  · simpa only [hcs,FieldConvolution.tapeData_setReg] using het



end ExpandingCodes.Computation.TesterPowers

end FlattenModule62

/-! Inlined whole module: ExpandingCodes.Computation.TesterEvaluation -/
section FlattenModule63



set_option autoImplicit false
open scoped BigOperators
namespace ExpandingCodes.Computation.TesterEvaluation
open NKtLB SamplerEvaluation SamplerProgram TesterPowers
open FieldPrograms UnaryArithmetic
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B : ℕ}











private theorem sumCore_stops (dst tmp : Fin R) (hdt : dst≠tmp) (ps : List (Fin R))
    (hp : ∀ p∈ps,p≠dst ∧ p≠tmp) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i  ≤  M) (htmp : s.reg tmp=0) (hresult : s.reg dst+sumValue s.reg ps  ≤  M) :
    ∃ t e,t  ≤  ps.length*(6*M+6) ∧
      (sumCore dst tmp ps).Stops inp (s.toCfg (sumCore (B := B) dst tmp ps).entry) t e ∧
      e.store=(s.setReg dst (s.reg dst+sumValue s.reg ps)).setReg tmp 0 ∧ ∀ i,e.reg i  ≤  M := by
  induction ps generalizing s with
  | nil =>
    refine ⟨0,s.toCfg ⟨0,by simp [sumLabels]⟩,by simp,TapeProgram.skip_stops inp s,?_,hs⟩
    change s=(s.setReg dst (s.reg dst+sumValue s.reg [])).setReg tmp 0
    simp only [sumValue,List.map_nil,List.sum_nil,Nat.add_zero,setReg_self]
    rw [← htmp,setReg_self]
  | cons p ps ih =>
    have hpp := hp p (by simp)
    have htail : s.reg dst+sumValue s.reg ps  ≤  M := by
      simpa [sumValue] using (show s.reg dst+(ps.map s.reg).sum  ≤  M by
        have hh := hresult
        simp only [sumValue,List.map_cons,List.sum_cons] at hh
        omega)
    obtain ⟨t,c,ht,hc,hcs,hcb⟩ := ih (fun a ha => hp a (by simp [ha])) s hs htmp htail
    obtain ⟨e,he,hes⟩ := TapeMacros.addPreserving_stops p dst tmp hpp.1 hpp.2 hdt inp c.store
    have hcv : c.reg p=s.reg p := by
      change c.store.reg p=_
      rw [hcs]; simp [TapeStore.setReg,hpp]
    have hct : c.reg tmp=0 := by change c.store.reg tmp=_; rw [hcs]; simp
    have hcd : c.reg dst=s.reg dst+sumValue s.reg ps := by
      change c.store.reg dst=_; rw [hcs]; simp [TapeStore.setReg,hdt]
    have hall := hc.seq he
    have hpost : e.store=(s.setReg dst (s.reg dst+sumValue s.reg (p::ps))).setReg tmp 0 := by
      rw [hes,hcs]
      simp only [TapeStore.setReg]
      congr 1
      funext i
      by_cases hit : i=tmp <;> by_cases hid : i=dst <;>
        simp_all [Function.update,sumValue,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    refine ⟨t+1+(c.reg tmp+5*c.reg p+5),_,?_,hall,hpost,?_⟩
    · rw [hct,hcv]
      have hsp := hs p
      change t+1+(0+5*s.reg p+5)  ≤  (ps.length+1)*(6*M+6)
      rw [Nat.add_mul,Nat.one_mul]; omega
    · intro i
      change e.store.reg i  ≤  M
      rw [hpost]
      exact setReg_bound _ _ 0 M (setReg_bound s _ _ M hs hresult) (by omega) i





private theorem sumDigits_stops (dst tmp : Fin R) (hdt : dst≠tmp) (ps : List (Fin R))
    (hp : ∀ p∈ps,p≠dst ∧ p≠tmp) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i  ≤  M) (hresult : sumValue s.reg ps  ≤  M) :
    ∃ t e,t  ≤  (ps.length+1)*(8*M+10) ∧
      (sumDigits dst tmp ps).Stops inp (s.toCfg (sumDigits (B := B) dst tmp ps).entry) t e ∧
      e.store=(s.setReg dst (sumValue s.reg ps)).setReg tmp 0 ∧ ∀ i,e.reg i  ≤  M := by
  have h₁ := TapeMacros.clear_stops dst inp (s.reg dst) s rfl
  have h₂ := TapeMacros.clear_stops tmp inp ((s.setReg dst 0).reg tmp) (s.setReg dst 0) rfl
  let p := (s.setReg dst 0).setReg tmp 0
  have hpbound : ∀ i,p.reg i  ≤  M := setReg_bound _ _ 0 M (setReg_bound s _ 0 M hs (by omega)) (by omega)
  have hvalues : sumValue p.reg ps=sumValue s.reg ps := by
    unfold sumValue
    congr 1
    apply List.map_congr_left
    intro a ha
    simp [p,TapeStore.setReg,hp a ha]
  obtain ⟨t,e,ht,he,hes,heb⟩ := sumCore_stops dst tmp hdt ps hp inp M p hpbound (by simp [p])
    (by
      have hz : p.reg dst=0 := by simp [p,TapeStore.setReg,hdt]
      rw [hz,hvalues]
      simpa using hresult)
  have hall := (h₁.seq h₂).seq he
  refine ⟨s.reg dst+1+1+((s.setReg dst 0).reg tmp+1)+1+t,_,?_,hall,?_,heb⟩
  · have hb₁ := hs dst; have hb₂ := hs tmp
    have htmp : (s.setReg dst 0).reg tmp=s.reg tmp := by simp [TapeStore.setReg,Ne.symm hdt]
    have ht' := ht.trans (Nat.mul_le_mul_left ps.length (show 6*M+6  ≤  8*M+10 by omega))
    rw [htmp,Nat.add_mul,Nat.one_mul]
    omega
  · change e.store=_
    rw [hes,hvalues]
    simp only [p,TapeStore.setReg]
    congr 1
    funext i
    by_cases hit : i=tmp <;> by_cases hid : i=dst <;> simp_all [Function.update]





private theorem comparison_injective (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (c : Fin 4 → Fin R) (hc : Function.Injective c) (hcr : ∀ i j,c i≠r j) :
    Function.Injective (comparison r c) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [comparison,hr.eq_iff,hc.eq_iff,hcr,Ne.symm]









/-- Exact frame of the preserving comparison, convenient for composing a field
workspace without unfolding the scalar comparison's internal source. -/
private theorem lessThanStore_frame (r : Fin 6 → Fin R) (s : TapeStore R B) (j : Fin R)
    (hj : j≠r 2 ∧ j≠r 3 ∧ j≠r 4 ∧ j≠r 5) :
    (ParameterPrograms.lessThanStore r s).reg j=s.reg j := by
  simp [ParameterPrograms.lessThanStore,ParameterPrograms.lessCore,ParameterPrograms.lessPrepare,
    ParameterPrograms.ltLoopStore,TapeStore.setReg,hj]












private theorem evaluate_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (c : Fin 4 → Fin R) (hc : Function.Injective c) (hcr : ∀ i j,c i≠r j)
    (ps : List (Fin R × Fin R))
    (hp : ∀ p∈ps,(∀ i,p.1≠r i) ∧ (∀ i,p.2≠r i) ∧ (∀ i,p.1≠c i) ∧ (∀ i,p.2≠c i))
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell)) (exponents : Fin R → ℕ)
    (M : ℕ) (hM : 1  ≤  M) (s : TapeStore R B) (hs : ∀ i,s.reg i  ≤  M)
    (henv : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) s)
    (hv : ∀ p∈ps,s.reg p.2=(values p.2).val ∧ s.reg p.1=exponents p.1)
    (hsum : sumValue exponents (ps.map Prod.fst)  ≤  M) :
    ∃ t e,t  ≤  timeBound ps.length M ∧
      (evaluate r c ps).Stops inp (s.toCfg (evaluate (B := B) r c ps).entry) t e ∧
      e.reg (c 0)=(value ell h (s.reg (c 1)) values exponents ps).val ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → i≠c 0 → i≠c 2 → i≠c 3 → e.reg i=s.reg i) ∧
      (∀ i,e.reg i  ≤  M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  have hpsum : ∀ p∈ps.map Prod.fst,p≠c 2 ∧ p≠r 2 := by
    intro p hpm
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hpm
    exact ⟨(hp a ha).2.2.1 2,(hp a ha).1 2⟩
  have hsumval : sumValue s.reg (ps.map Prod.fst)=sumValue exponents (ps.map Prod.fst) := by
    unfold sumValue
    congr 1
    apply List.map_congr_left
    intro p hpm
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hpm
    exact (hv a ha).2
  obtain ⟨u,d,hu,hd,hds,hdb⟩ := sumDigits_stops (c 2) (r 2) (hcr 2 2)
    (ps.map Prod.fst) hpsum inp M s hs (by rw [hsumval]; exact hsum)
  have hde : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) d.store := by
    rw [hds]
    exact (henv.setExternal (c 2) _ (fun i => hcr 2 ⟨i.val,by omega⟩)).setReg
      (powerWorkspace_injective _ (scalar_injective r hr)) 2 0 (by decide)
  have hdframe (j : Fin R) (hj : j≠c 2) (hjr : j≠r 2) : d.reg j=s.reg j := by
    change d.store.reg j=_
    rw [hds]; simp [TapeStore.setReg,hj,hjr]
  have hddegree : d.reg (c 1)=s.reg (c 1) := hdframe _ (hc.ne (by decide)) (hcr 1 2)
  have hdsum : d.reg (c 2)=sumValue exponents (ps.map Prod.fst) := by
    change d.store.reg (c 2)=_
    rw [hds]; simp [TapeStore.setReg,hcr,hsumval]
  have hdvalues : ∀ p∈ps,d.store.reg p.2=(values p.2).val ∧ d.store.reg p.1=exponents p.1 := by
    intro p hpm
    have hh := hp p hpm
    exact ⟨(hdframe p.2 (hh.2.2.2 2) (hh.2.1 2)).trans (hv p hpm).1,
      (hdframe p.1 (hh.2.2.1 2) (hh.1 2)).trans (hv p hpm).2⟩
  obtain ⟨v,f,hvtime,hf,hfs⟩ := ParameterPrograms.lessThan_stops (comparison r c)
    (comparison_injective r hr c hc hcr) inp M hM d.store hdb
  have hfb : ∀ j,f.reg j  ≤  M := by
    change ∀ j,f.store.reg j  ≤  M
    rw [hfs]
    exact ParameterPrograms.lessThanStore_bound _ (comparison_injective r hr c hc hcr) d.store M hM hdb
  have hfframe (j : Fin R) (hj : j≠c 3) (hjr : ∀ i : Fin 3,j≠r ⟨i.val,by omega⟩) : f.reg j=d.reg j := by
    change f.store.reg j=_
    rw [hfs]
    exact lessThanStore_frame _ _ _ (by simpa [comparison] using
      (show j≠c 3 ∧ j≠r 0 ∧ j≠r 1 ∧ j≠r 2 from ⟨hj,hjr 0,hjr 1,hjr 2⟩))
  have hfe : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) f.store := by
    apply hde.frame
    intro i hi
    change f.reg (powerWorkspace (scalar r) i)=d.reg (powerWorkspace (scalar r) i)
    exact hfframe _ (Ne.symm (hcr 3 ⟨i.val,by omega⟩)) (by
      intro j heq
      have hval := congrArg Fin.val (hr heq)
      simp only [powerWorkspace,scalar,Fin.val_mk] at hval
      have hjlt := j.isLt
      rcases hi with rfl|rfl|rfl|rfl <;> norm_num at hval <;> omega)
  have hflag : f.reg (c 3)=if s.reg (c 1)<sumValue exponents (ps.map Prod.fst) then 1 else 0 := by
    change f.store.reg ((comparison r c) 2)=_
    rw [hfs,ParameterPrograms.lessThanStore_value _ (comparison_injective r hr c hc hcr)]
    change (if d.reg (c 1)<d.reg (c 2) then 1 else 0)=_
    rw [hddegree,hdsum]
  have hfvalues : ∀ p∈ps,f.store.reg p.2=(values p.2).val ∧ f.store.reg p.1=exponents p.1 := by
    intro p hpm
    have hh := hp p hpm
    exact ⟨(hfframe p.2 (hh.2.2.2 3) (fun i => hh.2.1 ⟨i.val,by omega⟩)).trans (hdvalues p hpm).1,
      (hfframe p.1 (hh.2.2.1 3) (fun i => hh.1 ⟨i.val,by omega⟩)).trans (hdvalues p hpm).2⟩
  have hprefixdata : FieldConvolution.tapeData f.store=FieldConvolution.tapeData s := by
    rw [hfs,hds]
    rfl
  have hprefixframe (i : Fin R) (hi : ∀ v,i≠r v) (hi₂ : i≠c 2) (hi₃ : i≠c 3) : f.reg i=s.reg i :=
    (hfframe i hi₃ (fun j => hi ⟨j.val,by omega⟩)).trans (hdframe i hi₂ (hi 2))
  have hbranch : ∃ t e,t  ≤  max ((ps.length+1)*(27020*(M+1)^7)) (M+1)+2 ∧
      (TapeProgram.branchZero (c 3) (TesterPowers.product r (c 0) ps) (TapeMacros.clear (c 0))).Stops inp
        (f.store.toCfg (TapeProgram.branchZero (c 3) (TesterPowers.product (B := B) r (c 0) ps) (TapeMacros.clear (c 0))).entry) t e ∧
      e.reg (c 0)=(value ell h (s.reg (c 1)) values exponents ps).val ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → i≠c 0 → e.reg i=f.reg i) ∧
      (∀ i,e.reg i  ≤  M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData f.store := by
    by_cases hle : sumValue exponents (ps.map Prod.fst)  ≤  s.reg (c 1)
    · obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := TesterPowers.product_stops r hr (c 0) (hcr 0) ps
        (fun p hpm => ⟨(hp p hpm).1,(hp p hpm).2.1,(hp p hpm).2.2.1 0,(hp p hpm).2.2.2 0⟩)
        inp ell h values exponents M hM f.store hfb hfe hfvalues
      have hz : f.reg (c 3)=0 := by rw [hflag]; simp [show ¬s.reg (c 1)<sumValue exponents (ps.map Prod.fst) by omega]
      have hbr := TapeProgram.branchZero_stops_zero (c 3) (TesterPowers.product r (c 0) ps)
        (TapeMacros.clear (c 0)) inp f.store hz he
      refine ⟨1+t,e.mapPC (TapeProgram.branchLeft 2),?_,hbr,?_,hee,heo,heb,het⟩
      · have hh := le_max_left ((ps.length+1)*(27020*(M+1)^7)) (M+1); omega
      · simpa [value,hle] using hev
    · have hpflag : f.reg (c 3)≠0 := by rw [hflag]; simp [show s.reg (c 1)<sumValue exponents (ps.map Prod.fst) by omega]
      have hclear := TapeMacros.clear_stops (c 0) inp (f.reg (c 0)) f.store rfl
      have hbr := TapeProgram.branchZero_stops_positive (c 3) (TesterPowers.product r (c 0) ps)
        (TapeMacros.clear (c 0)) inp f.store hpflag hclear
      refine ⟨2+(f.reg (c 0)+1),_,?_,hbr,?_,?_,?_,?_,rfl⟩
      · have hh := le_max_right ((ps.length+1)*(27020*(M+1)^7)) (M+1)
        have hbout := hfb (c 0); omega
      · simp [value,hle,TapeCfg.mapPC,TapeStore.toCfg,zeroIndex_value]
      · exact hfe.setExternal (c 0) 0 (fun i => hcr 0 ⟨i.val,by omega⟩)
      · intro i hi hio
        simp [TapeCfg.mapPC,TapeStore.toCfg,TapeStore.setReg,hio]
      · exact setReg_bound f.store _ 0 M hfb (by omega)
  obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := hbranch
  have hall := (hd.seq hf).seq he
  refine ⟨u+1+v+1+t,_,?_,hall,hev,hee,?_,heb,het.trans hprefixdata⟩
  · have hlen : (ps.map Prod.fst).length=ps.length := by simp
    unfold timeBound
    rw [hlen] at hu
    omega
  · intro i hi hi₀ hi₂ hi₃
    exact (heo i hi hi₀).trans (hprefixframe i hi hi₂ hi₃)


private theorem value_canonical {d : ℕ} (ell : ℕ) (h : 0<ell) (degree : ℕ)
    (exp point : Fin d → Fin R) (values : Fin R → Fin (2^ell)) (exponents : Fin R → ℕ)
    (a z : Fin ((2^ell)^d))
    (ha : ∀ i,exponents (exp i)=(EncodedTester.digits (2^ell) d a i).val)
    (hz : ∀ i,values (point i)=EncodedTester.digits (2^ell) d z i) :
    value ell h degree values exponents (List.ofFn fun i => (exp i,point i))=
      (EncodedTester.evaluation (BinaryField.indexOperations ell h) degree a z).1 := by
  have hsum : sumValue exponents ((List.ofFn fun i => (exp i,point i)).map Prod.fst)=
      ∑ i,(EncodedTester.digits (2^ell) d a i).val := by
    simp [sumValue,List.map_ofFn,Function.comp_def,ha,List.sum_ofFn]
  have hprod : productValue ell h values exponents (List.ofFn fun i => (exp i,point i))=
      (EncodedTester.product (BinaryField.indexOperations ell h)
        (List.ofFn fun i => EncodedTester.power (BinaryField.indexOperations ell h)
          (EncodedTester.digits (2^ell) d z i) (EncodedTester.digits (2^ell) d a i).val)).1 := by
    rw [productValue_eq]
    simp [List.map_ofFn,Function.comp_def,ha,hz]
  unfold value EncodedTester.evaluation
  rw [hsum]
  split_ifs
  · exact hprod
  · rfl

/-- Direct canonical evaluation contract for physical digit counters. The finite
source is selected by fixed register maps before the runtime digits are known. -/
private theorem evaluate_canonical_stops {d : ℕ} (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (c : Fin 4 → Fin R) (hc : Function.Injective c) (hcr : ∀ i j,c i≠r j)
    (exp point : Fin d → Fin R)
    (hexp : ∀ j,(∀ i,exp j≠r i) ∧ (∀ i,exp j≠c i))
    (hpoint : ∀ j,(∀ i,point j≠r i) ∧ (∀ i,point j≠c i))
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (a z : Fin ((2^ell)^d))
    (M : ℕ) (hM : 1  ≤  M) (s : TapeStore R B) (hs : ∀ i,s.reg i  ≤  M)
    (henv : Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) s)
    (ha : ∀ i,s.reg (exp i)=(EncodedTester.digits (2^ell) d a i).val)
    (hz : ∀ i,s.reg (point i)=(EncodedTester.digits (2^ell) d z i).val)
    (hdM : d*((2^ell)-1)  ≤  M) :
    ∃ t e,t  ≤  timeBound d M ∧
      (evaluate r c (List.ofFn fun i => (exp i,point i))).Stops inp
        (s.toCfg (evaluate (B := B) r c (List.ofFn fun i => (exp i,point i))).entry) t e ∧
      e.reg (c 0)=(EncodedTester.evaluation (BinaryField.indexOperations ell h) (s.reg (c 1)) a z).1.val ∧
      Environment (powerWorkspace (scalar r)) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → i≠c 0 → i≠c 2 → i≠c 3 → e.reg i=s.reg i) ∧
      (∀ i,e.reg i  ≤  M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  let values (j : Fin R) : Fin (2^ell) := if hj : s.reg j<2^ell then ⟨s.reg j,hj⟩ else BinaryField.zeroIndex ell
  have hvalues (i : Fin d) : values (point i)=EncodedTester.digits (2^ell) d z i := by
    have hj : s.reg (point i)<2^ell := by rw [hz]; exact (EncodedTester.digits (2^ell) d z i).isLt
    apply Fin.ext
    simpa [values,hj] using hz i
  have hp : ∀ p∈List.ofFn (fun i => (exp i,point i)),
      (∀ i,p.1≠r i) ∧ (∀ i,p.2≠r i) ∧ (∀ i,p.1≠c i) ∧ (∀ i,p.2≠c i) := by
    intro p hpm
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hpm
    exact ⟨(hexp i).1,(hpoint i).1,(hexp i).2,(hpoint i).2⟩
  have hv : ∀ p∈List.ofFn (fun i => (exp i,point i)),s.reg p.2=(values p.2).val ∧ s.reg p.1=s.reg p.1 := by
    intro p hpm
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hpm
    exact ⟨by rw [hvalues]; exact hz i,rfl⟩
  have hsum : sumValue s.reg ((List.ofFn fun i => (exp i,point i)).map Prod.fst)  ≤  M := by
    have hle : (∑ i : Fin d,(EncodedTester.digits (2^ell) d a i).val)  ≤  d*((2^ell)-1) := by
      calc
        _  ≤  ∑ _i : Fin d,((2^ell)-1) := Finset.sum_le_sum (by
          intro i hi
          have hh := (EncodedTester.digits (2^ell) d a i).isLt
          omega)
        _ = d*((2^ell)-1) := by simp
    simpa [sumValue,List.map_ofFn,Function.comp_def,ha,List.sum_ofFn] using hle.trans hdM
  obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := evaluate_stops r hr c hc hcr
    (List.ofFn fun i => (exp i,point i)) hp inp ell h values s.reg M hM s hs henv hv hsum
  refine ⟨t,e,by simpa using ht,he,?_,hee,heo,heb,het⟩
  rw [value_canonical ell h (s.reg (c 1)) exp point values s.reg a z ha hvalues] at hev
  exact hev


































































































































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














































































































/-- Source assembly and exact storage/time correctness of `program` are separate:
no correctness axiom, theorem hole or runtime field/array instruction is present
in this concrete finite source table. -/
private theorem scalar_injective (d : ℕ) : Function.Injective (scalar d) := by
  intro i j hij
  exact Fin.ext (congrArg (Fin.val : Registers d → ℕ) hij)



@[simp] private theorem low_eq_iff (d : ℕ) (i j : Fin 80) : low d i=low d j ↔ i=j := by
  constructor
  · intro hij
    exact Fin.ext (congrArg (Fin.val : Registers d → ℕ) hij)
  · exact congrArg (low d)

private theorem low_outside_scalar (d : ℕ) (i : Fin 80) (hi : 33 ≤ i.val) :
    ∀ j,low d i≠scalar d j := by
  intro j hij
  have hh := congrArg (Fin.val : Registers d → ℕ) hij
  have hj := j.isLt
  simp only [low,scalar,Fin.val_mk] at hh
  omega

private theorem digit_ne_low (d : ℕ) (group : Fin 6) (i : Fin d) (j : Fin 80) :
    digit d group i≠low d j := by
  intro hij
  have hh := congrArg (Fin.val : Registers d → ℕ) hij
  have hj := j.isLt
  simp only [digit,low,Fin.val_mk] at hh
  omega

private theorem digit_outside_scalar (d : ℕ) (group : Fin 6) (i : Fin d) :
    ∀ j,digit d group i≠scalar d j :=
  fun j => digit_ne_low d group i ⟨j.val,by omega⟩

private theorem caller_injective (d : ℕ) : Function.Injective (evaluationCaller d) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [evaluationCaller]

private theorem caller_outside_scalar (d : ℕ) : ∀ i j,evaluationCaller d i≠scalar d j := by
  intro i j hij
  have hh := congrArg (Fin.val : Registers d → ℕ) hij
  have hj := j.isLt
  fin_cases i <;> simp [evaluationCaller,scalar,low] at hh <;> omega

private theorem digit_outside_caller (d : ℕ) (group : Fin 6) (i : Fin d) :
    ∀ j,digit d group i≠evaluationCaller d j := by
  intro j
  fin_cases j <;> exact digit_ne_low d group i _

/-- The eager Gram leaf performs two actual canonical monomials, saves the first
value, and uses the checked source field multiply/add to accumulate their product.
All point/exponent counters and every caller register above69 are preserved. -/
private theorem maskedTerm_stops (d ell : ℕ) (h : 0<ell)
    (a b z : Fin ((2^ell)^d)) (acc : Fin (2^ell))
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (s : TapeStore (80+6*d) 3)
    (hs : ∀ i,s.reg i ≤ M)
    (henv : SamplerProgram.Environment (termWorkspace d) ell
      (ExpandingCodes.PolynomialStretch.BinaryPolynomial.selectedIndex ell h) s)
    (ha : ∀ i,s.reg (digit d 0 i)=(EncodedTester.digits (2^ell) d a i).val)
    (hb : ∀ i,s.reg (digit d 2 i)=(EncodedTester.digits (2^ell) d b i).val)
    (hz : ∀ i,s.reg (digit d 4 i)=(EncodedTester.digits (2^ell) d z i).val)
    (hacc : s.reg (low d 69)=acc.val) (hdM : d*((2^ell)-1) ≤ M) :
    ∃ t e,t ≤ 2*TesterEvaluation.timeBound d M+13300*(M+1)^6+28*M+32 ∧
      (maskedTerm d).Stops inp (s.toCfg (maskedTerm d).entry) t e ∧
      e.reg (low d 69)=((ExpandingCodes.PolynomialStretch.BinaryField.indexOperations ell h).add
        ((ExpandingCodes.PolynomialStretch.BinaryField.indexOperations ell h).mul
          (EncodedTester.evaluation (ExpandingCodes.PolynomialStretch.BinaryField.indexOperations ell h) (s.reg (low d 65)) a z).1
          (EncodedTester.evaluation (ExpandingCodes.PolynomialStretch.BinaryField.indexOperations ell h) (s.reg (low d 65)) b z).1) acc).val ∧
      SamplerProgram.Environment (termWorkspace d) ell
        (ExpandingCodes.PolynomialStretch.BinaryPolynomial.selectedIndex ell h) e.store ∧
      (∀ i : Fin 80,70 ≤ i.val → e.reg (low d i)=s.reg (low d i)) ∧
      (∀ g i,e.reg (digit d g i)=s.reg (digit d g i)) ∧
      (∀ i,e.reg i ≤ M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s ∧
      e.reg (low d 65)=s.reg (low d 65) := by
  let O := ExpandingCodes.PolynomialStretch.BinaryField.indexOperations ell h
  let A := (EncodedTester.evaluation O (s.reg (low d 65)) a z).1
  let C := (EncodedTester.evaluation O (s.reg (low d 65)) b z).1
  have hr := scalar_injective d
  have hc := caller_injective d
  have hcr := caller_outside_scalar d
  have hdigit g i : (∀ j,digit d g i≠scalar d j) ∧ (∀ j,digit d g i≠evaluationCaller d j) :=
    ⟨digit_outside_scalar d g i,digit_outside_caller d g i⟩
  obtain ⟨t₁,c₁,ht₁,h₁,hv₁,he₁,hf₁,hb₁,hd₁⟩ := TesterEvaluation.evaluate_canonical_stops
    (scalar d) hr (evaluationCaller d) hc hcr (digit d 0) (digit d 4)
    (hdigit 0) (hdigit 4) inp ell h a z M hM s hs henv ha hz hdM
  have hf₁low (i : Fin 80) (hi : 68 ≤ i.val ∨ i=65) : c₁.reg (low d i)=s.reg (low d i) := by
    apply hf₁
    · apply low_outside_scalar
      rcases hi with hi|rfl <;> simp_all <;> omega
    all_goals simp only [evaluationCaller,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    all_goals apply (low_eq_iff d _ _).not.mpr
    all_goals rcases hi with hi|rfl <;> apply Fin.ne_of_val_ne <;> simp_all <;> omega
  have hf₁digit g i : c₁.reg (digit d g i)=s.reg (digit d g i) :=
    hf₁ _ (digit_outside_scalar d g i) (digit_outside_caller d g i 0)
      (digit_outside_caller d g i 2) (digit_outside_caller d g i 3)
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂,hb₂⟩ := SamplerEvaluation.copy_stops_bound (low d 64) (low d 68) (low d 2)
    (by simp) (by simp) (by simp) inp M c₁.store hb₁
  have he₂ : SamplerProgram.Environment (termWorkspace d) ell
      (ExpandingCodes.PolynomialStretch.BinaryPolynomial.selectedIndex ell h) c₂.store := by
    rw [hs₂]
    exact (he₁.setExternal (low d 68) _ (fun i => low_outside_scalar d 68 (by decide) ⟨i.val,by omega⟩)).setReg
      (SamplerProgram.powerWorkspace_injective _ (TesterPowers.scalar_injective _ hr)) 2 0 (by decide)
  have hf₂ (j : Registers d) (hj : j≠low d 68) (hj₂ : j≠low d 2) : c₂.reg j=c₁.reg j := by
    change c₂.store.reg j=_
    rw [hs₂]; simp [TapeStore.setReg,hj,hj₂]
  have hv₂ : c₂.reg (low d 68)=A.val := by
    change c₂.store.reg (low d 68)=_
    rw [hs₂]
    simpa [TapeStore.setReg,A,O,evaluationCaller] using hv₁
  obtain ⟨t₃,c₃,ht₃,h₃,hv₃,he₃,hf₃,hb₃,hd₃⟩ := TesterEvaluation.evaluate_canonical_stops
    (scalar d) hr (evaluationCaller d) hc hcr (digit d 2) (digit d 4)
    (hdigit 2) (hdigit 4) inp ell h b z M hM c₂.store hb₂ he₂
    (by intro i; change c₂.reg (digit d 2 i)=_; rw [hf₂ _ (digit_ne_low _ _ _ _) (digit_ne_low _ _ _ _),hf₁digit]; exact hb i)
    (by intro i; change c₂.reg (digit d 4 i)=_; rw [hf₂ _ (digit_ne_low _ _ _ _) (digit_ne_low _ _ _ _),hf₁digit]; exact hz i) hdM
  have hf₃low (i : Fin 80) (hi : 68 ≤ i.val ∨ i=65) : c₃.reg (low d i)=c₂.reg (low d i) := by
    apply hf₃
    · apply low_outside_scalar
      rcases hi with hi|rfl <;> simp_all <;> omega
    all_goals simp only [evaluationCaller,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    all_goals apply (low_eq_iff d _ _).not.mpr
    all_goals rcases hi with hi|rfl <;> apply Fin.ne_of_val_ne <;> simp_all <;> omega
  have hf₃digit g i : c₃.reg (digit d g i)=c₂.reg (digit d g i) :=
    hf₃ _ (digit_outside_scalar d g i) (digit_outside_caller d g i 0)
      (digit_outside_caller d g i 2) (digit_outside_caller d g i 3)
  have hdeg : c₂.reg (low d 65)=s.reg (low d 65) :=
    (hf₂ _ (by simp) (by simp)).trans (hf₁low 65 (Or.inr rfl))
  have hv₃' : c₃.reg (low d 64)=C.val := by
    simpa only [evaluationCaller,Matrix.cons_val_zero,Matrix.cons_val_one,hdeg,C,O] using hv₃
  have hv₃A : c₃.reg (low d 68)=A.val := (hf₃low 68 (Or.inl (by decide))).trans hv₂
  have hv₃acc : c₃.reg (low d 69)=acc.val := by
    rw [hf₃low 69 (Or.inl (by decide)),hf₂ _ (by simp) (by simp),hf₁low 69 (Or.inl (by decide))]
    exact hacc
  obtain ⟨t₄,c₄,ht₄,h₄,hs₄,hb₄⟩ := SamplerEvaluation.copy_stops_bound (low d 69) (low d 30) (low d 2)
    (by simp) (by simp) (by simp) inp M c₃.store hb₃
  have he₄ : SamplerProgram.Environment (termWorkspace d) ell
      (ExpandingCodes.PolynomialStretch.BinaryPolynomial.selectedIndex ell h) c₄.store := by
    rw [hs₄]
    exact (he₃.setReg (SamplerProgram.powerWorkspace_injective _ (TesterPowers.scalar_injective _ hr)) 30 _ (by decide)).setReg
      (SamplerProgram.powerWorkspace_injective _ (TesterPowers.scalar_injective _ hr)) 2 0 (by decide)
  have hv₄ (i : Fin 80) : c₄.reg (low d i)=if i=2 then 0 else if i=30 then acc.val else c₃.reg (low d i) := by
    change c₄.store.reg (low d i)=_
    rw [hs₄]
    change Function.update (Function.update c₃.reg (low d 30) (c₃.reg (low d 69))) (low d 2) 0 (low d i)=_
    rw [hv₃acc]
    simp [Function.update,low_eq_iff]
  obtain ⟨t₅,c₅,ht₅,h₅,hv₅,he₅,hf₅,hb₅,hd₅⟩ := SamplerProgram.term_stops (termWorkspace d)
    (SamplerProgram.powerWorkspace_injective _ (TesterPowers.scalar_injective _ hr)) (low d 68) (low d 64)
    (fun i => low_outside_scalar d 68 (by decide) ⟨i.val,by omega⟩)
    (fun i => low_outside_scalar d 64 (by decide) ⟨i.val,by omega⟩) inp ell h
    (ExpandingCodes.PolynomialStretch.BinaryPolynomial.selectedIndex ell h) A C acc M hM c₄.store hb₄ he₄
    (by simpa [termWorkspace,hv₄] using hv₃A) (by simpa [termWorkspace,hv₄] using hv₃')
    (by simp [termWorkspace,hv₄])
  obtain ⟨t₆,e,ht₆,h₆,hs₆,heb⟩ := SamplerEvaluation.copy_stops_bound (low d 30) (low d 69) (low d 2)
    (by simp) (by simp) (by simp) inp M c₅.store hb₅
  have hall := ((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆
  refine ⟨t₁+1+t₂+1+t₃+1+t₄+1+t₅+1+t₆,_,?_,hall,?_,?_,?_,?_,heb,?_,?_⟩
  · omega
  · change e.store.reg (low d 69)=_
    rw [hs₆]
    simpa [TapeStore.setReg,termWorkspace,O,A,C,ExpandingCodes.PolynomialStretch.BinaryField.indexOperations] using hv₅
  · rw [hs₆]
    exact (he₅.setExternal (low d 69) _ (fun i => low_outside_scalar d 69 (by decide) ⟨i.val,by omega⟩)).setReg
      (SamplerProgram.powerWorkspace_injective _ (TesterPowers.scalar_injective _ hr)) 2 0 (by decide)
  · intro i hi
    change e.store.reg (low d i)=_
    rw [hs₆]
    simp only [TapeStore.setReg]
    rw [Function.update_of_ne (by apply (low_eq_iff d _ _).not.mpr; intro hh; have hv := congrArg Fin.val hh; norm_num at hv; omega),
      Function.update_of_ne (by apply (low_eq_iff d _ _).not.mpr; intro hh; have hv := congrArg Fin.val hh; norm_num at hv; omega)]
    rw [hf₅ _ (fun j => low_outside_scalar d i (by omega) ⟨j.val,by omega⟩)]
    change c₄.reg (low d i)=_
    rw [hv₄]
    simp only [show i≠2 by intro hh; subst i; norm_num at hi,show i≠30 by intro hh; subst i; norm_num at hi,if_false]
    rw [hf₃low i (Or.inl (by omega)),hf₂ _ (by apply (low_eq_iff d _ _).not.mpr; intro hh; subst i; norm_num at hi)
      (by apply (low_eq_iff d _ _).not.mpr; intro hh; subst i; norm_num at hi),hf₁low i (Or.inl (by omega))]
  · intro g i
    change e.store.reg (digit d g i)=_
    rw [hs₆]
    simp only [TapeStore.setReg,Function.update_of_ne (digit_ne_low _ _ _ _)]
    rw [hf₅ _ (fun j => digit_ne_low d g i ⟨j.val,by omega⟩)]
    change c₄.store.reg (digit d g i)=_
    rw [hs₄]
    simp only [TapeStore.setReg,Function.update_of_ne (digit_ne_low _ _ _ _)]
    rw [hf₃digit,hf₂ _ (digit_ne_low _ _ _ _) (digit_ne_low _ _ _ _),hf₁digit]
  · change FieldConvolution.tapeData e.store=_
    rw [hs₆]
    simp only [FieldConvolution.tapeData_setReg]
    rw [hd₅,hs₄]
    simp only [FieldConvolution.tapeData_setReg]
    rw [hd₃,hs₂]
    simp only [FieldConvolution.tapeData_setReg]
    exact hd₁
  · change e.store.reg (low d 65)=_
    rw [hs₆]
    simp only [TapeStore.setReg,Function.update_of_ne (show low d 65≠low d 2 by simp),
      Function.update_of_ne (show low d 65≠low d 69 by simp)]
    rw [hf₅ _ (fun j => low_outside_scalar d 65 (by decide) ⟨j.val,by omega⟩)]
    change c₄.store.reg (low d 65)=_
    rw [hs₄]
    simp only [TapeStore.setReg,Function.update_of_ne (show low d 65≠low d 2 by simp),
      Function.update_of_ne (show low d 65≠low d 30 by simp)]
    rw [hf₃low 65 (Or.inr rfl),hf₂ _ (by simp) (by simp),hf₁low 65 (Or.inr rfl)]






























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
































@[simp] private theorem searchLoop_tail (P : TapeProgram R B L) (remaining value index found : Fin R)
    (k : Fin 6) :
    (searchLoop P remaining value index found).code (searchLabel L k) =
      if k = 0 then .dec remaining (searchLabel L 5) (TapeProgram.leftLabel 6 P.entry)
      else if k = 1 then .dec value (searchLabel L 2) (searchLabel L 3)
      else if k = 2 then .inc index (searchLabel L 0)
      else if k = 3 then .inc value (searchLabel L 4)
      else if k = 4 then .inc found (searchLabel L 5) else .halt := by
  simp [searchLoop, searchLabel, TapeProgram.rightLabel]
























































































end SearchLoop






































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































@[simp] private theorem paddedSchur_apply {α : Type*} (O : EncodedGaussian.Operations α) {m n : ℕ}
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




@[simp] private theorem tuple_zero (d : ℕ) : tuple d 0=aDigits d := rfl
@[simp] private theorem tuple_one (d : ℕ) : tuple d 1=bDigits d := rfl
@[simp] private theorem tuple_two (d : ℕ) : tuple d 2=zDigits d := rfl

private theorem digit_injective (d : ℕ) {g h : Fin 6} {i j : Fin d}
    (he : digit d g i=digit d h j) : g=h ∧ i=j := by
  have hv := congrArg (Fin.val : Registers d → ℕ) he
  simp only [digit,Fin.val_mk] at hv
  have hi := i.isLt
  have hj := j.isLt
  have hg : g.val=h.val := by
    rcases lt_trichotomy g.val h.val with hl|he|hl
    · have hm := Nat.mul_le_mul_right d (show g.val+1 ≤ h.val by omega)
      rw [Nat.add_mul,Nat.one_mul] at hm
      omega
    · exact he
    · have hm := Nat.mul_le_mul_right d (show h.val+1 ≤ g.val by omega)
      rw [Nat.add_mul,Nat.one_mul] at hm
      omega
  exact ⟨Fin.ext hg,Fin.ext (by rw [hg] at hv; omega)⟩

private theorem tuple_used (d : ℕ) (g : Fin 3) (j : Registers d) :
    j∈SamplerOdometer.used (tuple d g) ↔
      ∃ i : Fin d,j=digit d ⟨2*g.val,by omega⟩ i ∨ j=digit d ⟨2*g.val+1,by omega⟩ i := by
  rw [SamplerOdometer.used_mem_iff]
  simp only [tuple,List.mem_ofFn]
  constructor
  · rintro ⟨p,⟨i,rfl⟩,hi⟩
    exact ⟨i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨_,⟨i,rfl⟩,hi⟩

private theorem low_not_tuple (d : ℕ) (g : Fin 3) (j : Fin 80) :
    low d j∉SamplerOdometer.used (tuple d g) := by
  rw [tuple_used]
  rintro ⟨i,he|he⟩ <;> exact digit_ne_low d _ i j he.symm

private theorem tuple_nodup (d : ℕ) (g : Fin 3) :
    (SamplerOdometer.used (tuple d g)).Nodup := by
  have hgen (ps : List (SamplerOdometer.Digit (80+6*d)))
      (hl : ps.Pairwise (fun p q => p.1≠q.1 ∧ p.1≠q.2 ∧ p.2≠q.1 ∧ p.2≠q.2))
      (hp : ∀ p∈ps,p.1≠p.2) : (SamplerOdometer.used ps).Nodup := by
    induction ps with
    | nil => simp [SamplerOdometer.used]
    | cons p ps ih =>
      rw [List.pairwise_cons] at hl
      simp only [SamplerOdometer.used,List.nodup_cons,List.mem_cons,not_or]
      refine ⟨⟨hp p (by simp),?_⟩,?_,ih hl.2 (fun q hq => hp q (by simp [hq]))⟩
      · rw [SamplerOdometer.used_mem_iff]
        rintro ⟨q,hq,he|he⟩
        · exact (hl.1 q hq).1 he
        · exact (hl.1 q hq).2.1 he
      · rw [SamplerOdometer.used_mem_iff]
        rintro ⟨q,hq,he|he⟩
        · exact (hl.1 q hq).2.2.1 he
        · exact (hl.1 q hq).2.2.2 he
  apply hgen
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    have hne : i≠j := Fin.ne_of_lt hij
    refine ⟨?_,?_,?_,?_⟩
    · intro he; exact hne (digit_injective d he).2
    · intro he; have hh := congrArg Fin.val (digit_injective d he).1; simp at hh
    · intro he; have hh := congrArg Fin.val (digit_injective d he).1; simp at hh
    · intro he; exact hne (digit_injective d he).2
  · intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    intro he
    have hh := congrArg Fin.val (digit_injective d he).1
    simp at hh

private theorem tuple_unique (d : ℕ) (g : Fin 3) :
    (low d 23::low d 2::SamplerOdometer.used (tuple d g)).Nodup := by
  simp only [List.nodup_cons,List.mem_cons,not_or]
  exact ⟨⟨by simp,low_not_tuple d g 23⟩,low_not_tuple d g 2,tuple_nodup d g⟩





private theorem numbered_digits (d : ℕ) (g : Fin 3) (q k : ℕ) (hq : 1<q)
    (s : TapeStore (80+6*d) 3) (hn : Numbered d g q k s) (hk : k<q^d) :
    ∀ i,s.reg (digit d ⟨2*g.val,by omega⟩ i)=(EncodedTester.digits q d ⟨k,hk⟩ i).val := by
  let f : Fin d → Fin q := fun i => ⟨s.reg (digit d ⟨2*g.val,by omega⟩ i),by
    have hh := hn.2.1 _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simp only [Prod.fst,Prod.snd] at hh
    rw [hn.1] at hh
    omega⟩
  have hnum : Nat.ofDigits q (List.ofFn (fun i => (f i).val))=k := by
    have hh := hn.2.2
    simpa [SamplerOdometer.readings,tuple,List.map_ofFn,Nat.mod_eq_of_lt hk,f,Function.comp_def] using hh
  have hcanon := SamplerOdometer.canonical_digits q d f ⟨k,hk⟩ hnum
  intro i
  exact congrArg Fin.val (congrFun hcanon i)

private theorem numbered_next (d : ℕ) (g : Fin 3) (q k : ℕ) (hq : 1<q)
    (s : TapeStore (80+6*d) 3) (hn : Numbered d g q k s) :
    Numbered d g q (k+1) (SamplerOdometer.nextStore (low d 23) (low d 2) (tuple d g) s) := by
  have hu := tuple_unique d g
  refine ⟨?_,SamplerOdometer.program_valid _ _ _ hu s hn.2.1,?_⟩
  · rw [SamplerOdometer.nextStore_fresh _ _ _ _ _ (by simp) (low_not_tuple d g 23)]
    exact hn.1
  · have hh := SamplerOdometer.program_number _ _ _ hu s hn.2.1 (by rw [hn.1]; exact hq)
    rw [hn.1,hn.2.2] at hh
    simpa [tuple,SamplerOdometer.readings,Nat.mod_add_mod] using hh

private theorem numbered_initialize (d : ℕ) (g : Fin 3) (q : ℕ) (hq : 1<q)
    (s : TapeStore (80+6*d) 3) (hs : s.reg (low d 23)=q) :
    Numbered d g q 0 (SamplerOdometer.initializeStore (low d 23) (low d 2) (tuple d g) s) := by
  have hu := tuple_unique d g
  refine ⟨?_,SamplerOdometer.initializeStore_valid _ _ _ hu s (by omega),?_⟩
  · rw [SamplerOdometer.initializeStore_fresh _ _ _ _ _ (by simp) (low_not_tuple d g 23)]
    exact hs
  · have hv := SamplerOdometer.initializeStore_values _ _ _ hu s
    have hr : SamplerOdometer.readings (tuple d g)
        (SamplerOdometer.initializeStore (low d 23) (low d 2) (tuple d g) s)=List.replicate d 0 := by
      simp only [SamplerOdometer.readings,tuple,List.map_ofFn]
      rw [← List.ofFn_const]
      congr 1
      funext i
      exact (hv _ (List.mem_ofFn.mpr ⟨i,rfl⟩)).1
    rw [hr]
    simp

private theorem Numbered.frame {d : ℕ} {g : Fin 3} {q k : ℕ}
    {s e : TapeStore (80+6*d) 3} (hn : Numbered d g q k s)
    (hq : e.reg (low d 23)=s.reg (low d 23))
    (hf : ∀ j,j∈SamplerOdometer.used (tuple d g) → e.reg j=s.reg j) :
    Numbered d g q k e := by
  refine ⟨hq.trans hn.1,?_,?_⟩
  · intro p hp
    rw [hf _ (SamplerOdometer.used_mem_left _ _ hp),
      hf _ (SamplerOdometer.used_mem_right _ _ hp),hq]
    exact hn.2.1 p hp
  · rw [SamplerOdometer.readings_congr _ e s
      (fun p hp => hf _ (SamplerOdometer.used_mem_left _ _ hp))]
    exact hn.2.2

private theorem tuple_other (d : ℕ) (g h : Fin 3) (hgh : g≠h) (j : Registers d)
    (hj : j∈SamplerOdometer.used (tuple d g)) : j∉SamplerOdometer.used (tuple d h) := by
  rw [tuple_used] at hj ⊢
  obtain ⟨i,rfl|rfl⟩ := hj
  all_goals rintro ⟨k,hk|hk⟩
  all_goals have hh := congrArg Fin.val (digit_injective d hk).1
  all_goals apply hgh; apply Fin.ext; simp only [Fin.val_mk] at hh; omega

private theorem numbered_next_other (d : ℕ) (g h : Fin 3) (hgh : g≠h) (q k : ℕ)
    (s : TapeStore (80+6*d) 3) (hn : Numbered d g q k s) :
    Numbered d g q k (SamplerOdometer.nextStore (low d 23) (low d 2) (tuple d h) s) := by
  apply hn.frame
  · exact SamplerOdometer.nextStore_fresh _ _ _ _ _ (by simp) (low_not_tuple d h 23)
  · intro j hj
    apply SamplerOdometer.nextStore_fresh
    · obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj
      all_goals exact digit_ne_low d _ i 2
    · exact tuple_other d g h hgh j hj

private theorem inputLookup_injective (d : ℕ) : Function.Injective (inputLookup d) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [inputLookup]

private theorem inputLookup_outside (d : ℕ) (j : Fin 80)
    (hj : j≠0 ∧ j≠1 ∧ j≠2 ∧ j≠4 ∧ j≠5 ∧ j≠23 ∧ j≠73 ∧ j≠78) :
    ∀ i,low d j ≠ inputLookup d i := by
  intro i
  fin_cases i <;> simp_all [inputLookup]

private theorem tapeData_payload {R B : ℕ} {s e : TapeStore R B}
    (h : FieldConvolution.tapeData e=FieldConvolution.tapeData s) : TapeStore.SamePayload e s := by
  have hr := congrArg Prod.fst h
  have ho := congrArg (fun x => x.2.1) h
  have ht := congrArg (fun x => x.2.2.1) h
  exact ⟨hr,ho,fun c k => congrArg (fun t => (t c).getD k .blank) ht⟩

private theorem tapeData_head {R B : ℕ} {s e : TapeStore R B}
    (h : FieldConvolution.tapeData e=FieldConvolution.tapeData s) : e.bufferHead=s.bufferHead :=
  congrArg (fun x => x.2.2.2) h























private theorem pointBody_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
    (y : Fin ((2^ell)^d) → Bool) (a b z : Fin ((2^ell)^d)) (acc : Fin (2^ell))
    (inp : Inputs) (s : TapeStore (80+6*d) 3) (hc : Core d ell h D M y s)
    (ha : Numbered d 0 (2^ell) a.val s) (hb : Numbered d 1 (2^ell) b.val s)
    (hz : Numbered d 2 (2^ell) z.val s) (hzi : s.reg (low d 73)=z.val)
    (hacc : s.reg (low d 69)=acc.val) (hdM : d*((2^ell)-1) ≤ M)
    (hhead : 1+(2^ell)^d*(2^ell) ≤ M) :
    ∃ t e,t ≤ pointTime d M ∧ (pointBody d).Stops inp (s.toCfg (pointBody d).entry) t e ∧
      Core d ell h D M y e.store ∧
      e.reg (low d 69)=(pointValue d ell h D y a b z acc).val ∧
      Numbered d 0 (2^ell) a.val e.store ∧ Numbered d 1 (2^ell) b.val e.store ∧
      Numbered d 2 (2^ell) (z.val+1) e.store ∧ e.reg (low d 73)=z.val+1 ∧
      (∀ j : Fin 80,70 ≤ j.val → j≠73 → j≠78 → e.reg (low d j)=s.reg (low d j)) ∧
      TapeStore.SamePayload e.store s ∧ (∀ c : Fin 3,c≠2 → e.bufferHead c=s.bufferHead c) := by
  have hq : 1<2^ell := Nat.one_lt_pow h.ne' (by decide)
  have hq0 : s.reg (low d 23)=2^ell := hc.environment.cardinal
  have hv : TapeArrays.ThermometerAt s 2
      (TapeArrays.entryOffset (s.reg (low d 73)) (s.reg (low d 23))) (s.reg (low d 23))
      (if y z then 1 else 0) := by
    rw [hzi,hq0]
    exact hc.inputTable z
  obtain ⟨t₁,c₁,ht₁,h₁,hr₁,hv₁,hi₁,hq₁,hf₁,hb₁,hh₁,hp₁⟩ :=
    SamplerEvaluation.lookup_stops (inputLookup d) (inputLookup_injective d) 2 inp M s hc.bounded
      hc.inputHead hc.inputMarked.marked (if y z then 1 else 0) hv
  have hf₁low (i : Fin 80) (hi : i≠0 ∧ i≠1 ∧ i≠2 ∧ i≠4 ∧ i≠5 ∧ i≠23 ∧ i≠73 ∧ i≠78) :
      c₁.reg (low d i)=s.reg (low d i) := hf₁ _ (inputLookup_outside d i hi)
  have hf₁dig g i : c₁.reg (digit d g i)=s.reg (digit d g i) := by
    apply hf₁
    intro j
    fin_cases j <;> exact digit_ne_low d g i _
  have he₁ : SamplerProgram.Environment (termWorkspace d) ell (BinaryPolynomial.selectedIndex ell h) c₁.store := by
    apply hc.environment.frame
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact hf₁low 3 (by decide)
    · exact hf₁low 19 (by decide)
    · exact hq₁
    · exact hf₁low 24 (by decide)
  have hD₁ : c₁.reg (low d 65)=D := (hf₁low 65 (by decide)).trans hc.degree
  have hA₁ : c₁.reg (low d 69)=acc.val := (hf₁low 69 (by decide)).trans hacc
  have hdigits (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k s) :
      Numbered d g (2^ell) k c₁.store := by
    apply hn.frame hq₁
    intro j hj
    obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj <;> exact hf₁dig _ i
  obtain ⟨t₂,c₂,ht₂,h₂,hv₂,he₂,hf₂,hd₂,hb₂,hp₂,hh₂,hD₂⟩ :
      ∃ t c,t ≤ 2*TesterEvaluation.timeBound d M+13300*(M+1)^6+28*M+34 ∧
        (TapeProgram.branchZero (low d 78) TapeProgram.skip (maskedTerm d)).Stops inp
          (c₁.store.toCfg (TapeProgram.branchZero (low d 78) TapeProgram.skip (maskedTerm d)).entry) t c ∧
        c.reg (low d 69)=(pointValue d ell h D y a b z acc).val ∧
        SamplerProgram.Environment (termWorkspace d) ell (BinaryPolynomial.selectedIndex ell h) c.store ∧
        (∀ i : Fin 80,70 ≤ i.val → c.reg (low d i)=c₁.reg (low d i)) ∧
        (∀ g i,c.reg (digit d g i)=c₁.reg (digit d g i)) ∧ (∀ j,c.reg j ≤ M) ∧
        TapeStore.SamePayload c.store c₁.store ∧ c.bufferHead=c₁.bufferHead ∧ c.reg (low d 65)=D := by
    cases hy : y z with
    | false =>
      have hz₁ : c₁.reg (low d 78)=0 := by simpa [inputLookup,hy] using hv₁
      have hskip := TapeProgram.skip_stops inp c₁.store
      have hs := TapeProgram.branchZero_stops_zero (low d 78) TapeProgram.skip (maskedTerm d) inp c₁.store hz₁ hskip
      refine ⟨1,_,by omega,hs,?_,he₁,?_,?_,hb₁,TapeStore.SamePayload.refl _,rfl,hD₁⟩
      · simpa [pointValue,hy] using hA₁
      · intro i hi; rfl
      · intro g i; rfl
    | true =>
      obtain ⟨u,c,hu,hc',hcv,hce,hcf,hcd,hcb,hct,hcD⟩ := maskedTerm_stops d ell h a b z acc inp M hM c₁.store hb₁ he₁
        (numbered_digits d 0 _ _ hq _ (hdigits 0 _ ha) a.isLt)
        (numbered_digits d 1 _ _ hq _ (hdigits 1 _ hb) b.isLt)
        (numbered_digits d 2 _ _ hq _ (hdigits 2 _ hz) z.isLt) hA₁ hdM
      have hz₁ : c₁.reg (low d 78)≠0 := by
        have hvv : c₁.reg (low d 78)=1 := by simpa [inputLookup,hy] using hv₁
        omega
      have hs := TapeProgram.branchZero_stops_positive (low d 78) TapeProgram.skip (maskedTerm d) inp c₁.store hz₁ hc'
      refine ⟨2+u,_,by omega,hs,?_,hce,hcf,hcd,hcb,tapeData_payload hct,tapeData_head hct,hcD.trans hD₁⟩
      simpa [pointValue,hy,hD₁] using hcv
  have hq₂ : c₂.reg (low d 23)=s.reg (low d 23) := he₂.cardinal.trans hc.environment.cardinal.symm
  have hn₂ (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k s) :
      Numbered d g (2^ell) k c₂.store := by
    apply hn.frame hq₂
    intro j hj
    obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj
    all_goals exact (hd₂ _ i).trans (hf₁dig _ i)
  obtain ⟨t₃,c₃,ht₃,h₃,hs₃,hb₃⟩ := SamplerOdometer.program_stops_valid
    (low d 23) (low d 2) (tuple d 2) (tuple_unique d 2) inp M c₂.store hb₂ (hn₂ 2 _ hz).2.1
  have hf₃low (i : Fin 80) (hi : i≠2) : c₃.reg (low d i)=c₂.reg (low d i) := by
    change c₃.store.reg (low d i)=_
    rw [hs₃]
    exact SamplerOdometer.nextStore_fresh _ _ _ _ _ ((low_eq_iff d _ _).not.mpr hi) (low_not_tuple d 2 i)
  have hzi₂ : c₂.reg (low d 73)=z.val := (hf₂ 73 (by decide)).trans (hi₁.trans hzi)
  have hzi₃ : c₃.reg (low d 73)=z.val := (hf₃low 73 (by decide)).trans hzi₂
  have h₄ := TapeMacros.increment_stops (low d 73) inp c₃.store
  let e := (c₃.store.setReg (low d 73) (c₃.reg (low d 73)+1)).toCfg (1 : Fin 2)
  have hall := ((h₁.seq h₂).seq h₃).seq h₄
  have hbound : ∀ j,e.reg j ≤ M := by
    apply FieldPrograms.setReg_bound _ _ _ M hb₃
    rw [hzi₃]
    have hm := hc.bounded (low d 70)
    rw [hc.size] at hm
    omega
  have heq (j : Registers d) (hj : j≠low d 73) : e.reg j=c₃.reg j := by
    simp [e,TapeStore.setReg,hj]
  have henv₃ : SamplerProgram.Environment (termWorkspace d) ell (BinaryPolynomial.selectedIndex ell h) c₃.store := by
    apply he₂.frame
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl <;> exact hf₃low _ (by decide)
  have henv : SamplerProgram.Environment (termWorkspace d) ell (BinaryPolynomial.selectedIndex ell h) e.store := by
    apply henv₃.frame
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact heq (low d 3) (by simp)
    · exact heq (low d 19) (by simp)
    · exact heq (low d 23) (by simp)
    · exact heq (low d 24) (by simp)
  have hq₃ : c₃.reg (low d 23)=c₂.reg (low d 23) := hf₃low 23 (by decide)
  have hn₃ (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k c₃.store) :
      Numbered d g (2^ell) k e.store := by
    apply hn.frame (heq (low d 23) (by simp))
    intro j hj
    obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj <;> exact heq _ (digit_ne_low d _ i _)
  have hp₃ : TapeStore.SamePayload c₃.store c₂.store := by
    rw [hs₃]
    have hh := SamplerOdometer.nextStore_payload (low d 23) (low d 2) (tuple d 2) c₂.store
    exact ⟨hh.1,hh.2.1,fun c k => congrArg (fun t => (t c).getD k .blank) hh.2.2.1⟩
  have hh₃ : c₃.bufferHead=c₂.bufferHead := by
    change c₃.store.bufferHead=_
    rw [hs₃]
    exact (SamplerOdometer.nextStore_payload (low d 23) (low d 2) (tuple d 2) c₂.store).2.2.2
  have hp : TapeStore.SamePayload e.store s :=
    (TapeStore.setReg_payload _ _ _).trans (hp₃.trans (hp₂.trans hp₁))
  have hhigh (i : Fin 80) (hi : 70 ≤ i.val) (hi73 : i≠73) (hi78 : i≠78) :
      e.reg (low d i)=s.reg (low d i) := by
    rw [heq _ ((low_eq_iff d _ _).not.mpr hi73),hf₃low i (by intro he; subst i; norm_num at hi),hf₂ i hi]
    apply hf₁low
    have hne (k : Fin 80) (hk : k.val<70) : i≠k := by
      intro he
      subst i
      omega
    exact ⟨hne 0 (by decide),hne 1 (by decide),hne 2 (by decide),hne 4 (by decide),
      hne 5 (by decide),hne 23 (by decide),hi73,hi78⟩
  refine ⟨t₁+1+t₂+1+t₃+1+1,_,?_,hall,?_,?_,?_,?_,?_,?_,hhigh,hp,?_⟩
  · simp only [tuple,List.length_ofFn] at ht₃
    unfold pointTime
    omega
  · refine ⟨hbound,henv,?_,hhigh 70 (by decide) (by decide) (by decide) |>.trans hc.size,
        hc.inputMarked.of_payload hp,?_,?_⟩
    · change e.reg (low d 65)=D
      rw [heq (low d 65) (by simp),hf₃low 65 (by decide),hD₂]
    · intro z
      exact (hc.inputTable z).of_payload hp
    · change c₃.bufferHead 2 ≤ M
      rw [hh₃,hh₂,hh₁]
      simp only [Function.update_self]
      have hzlt := z.isLt
      change TapeArrays.entryOffset (s.reg (low d 73)) (s.reg (low d 23))+s.reg (low d 23) ≤ M
      rw [hzi,hq0]
      unfold TapeArrays.entryOffset
      have hm := Nat.mul_le_mul_right (2^ell) (show z.val+1 ≤ (2^ell)^d by omega)
      rw [Nat.add_mul,Nat.one_mul] at hm
      omega
  · rw [heq (low d 69) (by simp),hf₃low 69 (by decide),hv₂]
  · apply hn₃
    rw [hs₃]
    exact numbered_next_other d 0 2 (by decide) _ _ c₂.store (hn₂ 0 _ ha)
  · apply hn₃
    rw [hs₃]
    exact numbered_next_other d 1 2 (by decide) _ _ c₂.store (hn₂ 1 _ hb)
  · apply hn₃
    rw [hs₃]
    exact numbered_next d 2 _ _ hq c₂.store (hn₂ 2 _ hz)
  · simp [e,TapeStore.setReg,hzi₃]
  · intro c hc2
    change c₃.bufferHead c=s.bufferHead c
    rw [hh₃,hh₂,hh₁,Function.update_of_ne hc2]









@[simp] private theorem pointPrefix_zero (d ell : ℕ) (h : 0<ell) (D : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) :
    pointPrefix d ell h D y a b 0=BinaryField.zeroIndex ell := rfl

private theorem pointPrefix_step (d ell : ℕ) (h : 0<ell) (D : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) (k : ℕ) (hk : k<(2^ell)^d) :
    pointValue d ell h D y a b ⟨k,hk⟩ (pointPrefix d ell h D y a b k)=
      pointPrefix d ell h D y a b (k+1) := by
  let O := BinaryField.indexOperations ell h
  let xs := List.ofFn (fun z : Fin ((2^ell)^d) => EncodedTester.term O D y a b z)
  have hi := BinaryField.indexOperations_interpretation ell h
  have hx : xs.take (k+1)=xs.take k++[EncodedTester.term O D y a b ⟨k,hk⟩] := by
    rw [List.take_succ_eq_append_getElem (by simpa [xs] using hk)]
    simp [xs]
  apply hi.injective
  change BinaryField.elements ell h (pointValue d ell h D y a b ⟨k,hk⟩ (EncodedTester.sum O (xs.take k)).1)=
    BinaryField.elements ell h (EncodedTester.sum O (xs.take (k+1))).1
  rw [hx,EncodedTester.sum_decode hi,List.map_append,List.sum_append]
  cases hy : y ⟨k,hk⟩ <;>
    simp [pointValue,EncodedTester.term,hy,hi.add,hi.mul,hi.zero,EncodedTester.sum_decode hi,O,add_comm]

@[simp] private theorem pointPrefix_full (d ell : ℕ) (h : 0<ell) (D : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) :
    pointPrefix d ell h D y a b ((2^ell)^d)=
      (EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1 := by
  unfold pointPrefix EncodedTester.entry
  rw [List.take_of_length_le (by simp)]

private theorem Core.setReg {d ell : ℕ} {h : 0<ell} {D M : ℕ}
    {y : Fin ((2^ell)^d) → Bool} {s : TapeStore (80+6*d) 3}
    (hc : Core d ell h D M y s) (i : Fin 80) (hi : 70 ≤ i.val) (hi70 : i≠70)
    (v : ℕ) (hv : v ≤ M) : Core d ell h D M y (s.setReg (low d i) v) := by
  have hne (j : Fin 80) (hj : j.val<70) : low d j≠low d i := by
    rw [ne_eq,low_eq_iff]
    intro he
    have hh := congrArg Fin.val he
    omega
  refine ⟨FieldPrograms.setReg_bound _ _ _ _ hc.bounded hv,?_,?_,?_,hc.inputMarked,hc.inputTable,hc.inputHead⟩
  · apply hc.environment.frame
    intro j hj
    rcases hj with rfl|rfl|rfl|rfl
    · exact Function.update_of_ne (hne 3 (by decide)) _ _
    · exact Function.update_of_ne (hne 19 (by decide)) _ _
    · exact Function.update_of_ne (hne 23 (by decide)) _ _
    · exact Function.update_of_ne (hne 24 (by decide)) _ _
  · simpa [TapeStore.setReg,Function.update_of_ne (hne 65 (by decide))] using hc.degree
  · simpa [TapeStore.setReg,Function.update_of_ne ((low_eq_iff d 70 i).not.mpr (Ne.symm hi70))] using hc.size

private theorem Numbered.setReg {d : ℕ} {g : Fin 3} {q k : ℕ}
    {s : TapeStore (80+6*d) 3} (hn : Numbered d g q k s)
    (i : Fin 80) (hi : i≠23) (v : ℕ) : Numbered d g q k (s.setReg (low d i) v) := by
  apply hn.frame
  · simp [TapeStore.setReg,((low_eq_iff d 23 i).not.mpr (Ne.symm hi))]
  · intro j hj
    obtain ⟨k,rfl|rfl⟩ := (tuple_used d g j).mp hj
    all_goals simp [TapeStore.setReg,Function.update_of_ne (digit_ne_low d _ k i)]

/-- The semantic loop rule consumes the actual checked body's preserved countdown. -/
private theorem loop_stops {R B L : ℕ} (P : TapeProgram R B L) (r : Fin R)
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















private theorem pointLoop_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d))
    (inp : Inputs) (s : TapeStore (80+6*d) 3) (hc : Core d ell h D M y s)
    (ha : Numbered d 0 (2^ell) a.val s) (hb : Numbered d 1 (2^ell) b.val s)
    (hz : Numbered d 2 (2^ell) 0 s) (hzi : s.reg (low d 73)=0)
    (hacc : s.reg (low d 69)=0) (hcount : s.reg (low d 76)=(2^ell)^d)
    (hdM : d*((2^ell)-1) ≤ M) (hhead : 1+(2^ell)^d*(2^ell) ≤ M) :
    ∃ t e,t ≤ (2^ell)^d*(pointTime d M+2)+1 ∧
      (TapeProgram.countedLoop (pointBody d) (low d 76)).Stops inp
        (s.toCfg (TapeProgram.countedLoop (pointBody d) (low d 76)).entry) t e ∧
      Core d ell h D M y e.store ∧
      e.reg (low d 69)=(EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1.val ∧
      Numbered d 0 (2^ell) a.val e.store ∧ Numbered d 1 (2^ell) b.val e.store ∧
      e.reg (low d 73)=(2^ell)^d ∧ e.reg (low d 76)=0 ∧
      (∀ i : Fin 80,70 ≤ i.val → i≠73 → i≠76 → i≠78 → e.reg (low d i)=s.reg (low d i)) ∧
      TapeStore.SamePayload e.store s ∧ (∀ c : Fin 3,c≠2 → e.bufferHead c=s.bufferHead c) := by
  let Inv := PointLoopInv d ell h D M y a b s
  have hbody (n : ℕ) (c : TapeStore (80+6*d) 3) (hcn : c.reg (low d 76)=n+1) (hi : Inv (n+1) c) :
      ∃ t e,t ≤ pointTime d M ∧ (pointBody d).Stops inp
        ((TapeProgram.decStore (low d 76) c).toCfg (pointBody d).entry) t e ∧ Inv n e.store ∧ e.reg (low d 76)=n := by
    let k := (2^ell)^d-(n+1)
    have hk : k<(2^ell)^d := by dsimp [k]; have := hi.le; omega
    have hkn : (2^ell)^d-n=k+1 := by dsimp [k]; have := hi.le; omega
    let c' := c.setReg (low d 76) n
    have hc' : TapeProgram.decStore (low d 76) c=c' := by
      simp only [TapeProgram.decStore,c',TapeStore.setReg,hcn,Nat.add_sub_cancel]
    have hbnd : n ≤ M := by have hh := hi.core.bounded (low d 76); rw [hcn] at hh; omega
    have hcore := hi.core.setReg 76 (by decide) (by decide) n hbnd
    have ha' := hi.aTuple.setReg 76 (by decide) n
    have hb' := hi.bTuple.setReg 76 (by decide) n
    have hz' := hi.zTuple.setReg 76 (by decide) n
    have hzi' : c'.reg (low d 73)=k := by simpa [c',TapeStore.setReg,k] using hi.index
    have hac' : c'.reg (low d 69)=(pointPrefix d ell h D y a b k).val := by
      simpa [c',TapeStore.setReg,k] using hi.accumulator
    obtain ⟨t,e,ht,he,hec,hev,hea,heb,hez,hei,hef,hep,heh⟩ :=
      pointBody_stops d ell h D M hM y a b ⟨k,hk⟩ (pointPrefix d ell h D y a b k) inp c'
        hcore ha' hb' hz' hzi' hac' hdM hhead
    refine ⟨t,e,ht,?_,?_,?_⟩
    · simpa only [hc'] using he
    · refine ⟨by have := hi.le; omega,hec,hea,heb,?_,?_,?_,?_,?_,?_⟩
      · simpa only [hkn] using hez
      · simpa only [hkn] using hei
      · change e.reg (low d 69)=_
        rw [hev,pointPrefix_step d ell h D y a b k hk,hkn]
      · intro i hi70 hi73 hi76 hi78
        change e.reg (low d i)=_
        rw [hef i hi70 hi73 hi78]
        change c'.reg (low d i)=_
        simp only [c',TapeStore.setReg,Function.update_of_ne ((low_eq_iff d _ _).not.mpr hi76)]
        exact hi.high i hi70 hi73 hi76 hi78
      · exact hep.trans ((TapeStore.setReg_payload c _ _).trans hi.payload)
      · intro b hb2
        change e.bufferHead b=_
        rw [heh b hb2]
        exact hi.head b hb2
    · rw [hef 76 (by decide) (by decide) (by decide)]
      simp [c',TapeStore.setReg]
  have hi : Inv ((2^ell)^d) s := by
    refine ⟨le_rfl,hc,ha,hb,?_,?_,?_,?_,TapeStore.SamePayload.refl _,?_⟩
    · simpa using hz
    · simpa using hzi
    · simpa [pointPrefix_zero,SamplerProgram.zeroIndex_value] using hacc
    · intro i hi hi73 hi76 hi78; rfl
    · intro c hc; rfl
  obtain ⟨t,e,ht,he,hie,hez⟩ := loop_stops (pointBody d) (low d 76) inp (pointTime d M) Inv hbody
    ((2^ell)^d) s hcount hi
  refine ⟨t,_,ht,he,hie.core,?_,hie.aTuple,hie.bTuple,?_,hez,hie.high,hie.payload,hie.head⟩
  · simpa only [Nat.sub_zero,pointPrefix_full] using hie.accumulator
  · simpa only [Nat.sub_zero] using hie.index



private theorem Core.frame {d ell : ℕ} {h : 0<ell} {D M : ℕ}
    {y : Fin ((2^ell)^d) → Bool} {s e : TapeStore (80+6*d) 3}
    (hc : Core d ell h D M y s) (hb : ∀ j,e.reg j ≤ M)
    (hf : ∀ i : Fin 80,i=3 ∨ i=19 ∨ i=23 ∨ i=24 ∨ i=65 ∨ i=70 → e.reg (low d i)=s.reg (low d i))
    (hp : TapeStore.SamePayload e s) (hh : e.bufferHead 2=s.bufferHead 2) : Core d ell h D M y e := by
  refine ⟨hb,?_,(hf 65 (by tauto)).trans hc.degree,(hf 70 (by tauto)).trans hc.size,
    hc.inputMarked.of_payload hp,fun z => (hc.inputTable z).of_payload hp,?_⟩
  · apply hc.environment.frame
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl <;> exact hf _ (by tauto)
  · rw [hh]
    exact hc.inputHead

private theorem initialize_payload {R B : ℕ} (q tmp : Fin R) (ps : List (SamplerOdometer.Digit R))
    (s : TapeStore R B) :
    FieldConvolution.tapeData (SamplerOdometer.initializeStore q tmp ps s)=FieldConvolution.tapeData s := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    rw [SamplerOdometer.initializeStore,ih]
    rfl

private theorem initialize_other (d : ℕ) (g h : Fin 3) (hgh : g≠h) (q k : ℕ)
    (s : TapeStore (80+6*d) 3) (hn : Numbered d g q k s) :
    Numbered d g q k (SamplerOdometer.initializeStore (low d 23) (low d 2) (tuple d h) s) := by
  apply hn.frame
  · exact SamplerOdometer.initializeStore_fresh _ _ _ _ _ (by simp) (low_not_tuple d h 23)
  · intro j hj
    apply SamplerOdometer.initializeStore_fresh
    · obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj
      all_goals exact digit_ne_low d _ i 2
    · exact tuple_other d g h hgh j hj








private theorem pairPrepare_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d))
    (inp : Inputs) (s : TapeStore (80+6*d) 3) (hc : Core d ell h D M y s)
    (ha : Numbered d 0 (2^ell) a.val s) (hb : Numbered d 1 (2^ell) b.val s) :
    ∃ t e,t ≤ d*(8*M+20)+9*M+12 ∧ (pairPrepare d).Stops inp (s.toCfg (pairPrepare d).entry) t e ∧
      Core d ell h D M y e.store ∧ Numbered d 0 (2^ell) a.val e.store ∧ Numbered d 1 (2^ell) b.val e.store ∧
      Numbered d 2 (2^ell) 0 e.store ∧ e.reg (low d 73)=0 ∧ e.reg (low d 69)=0 ∧
      e.reg (low d 76)=(2^ell)^d ∧
      (∀ i : Fin 80,70 ≤ i.val → i≠73 → i≠76 → e.reg (low d i)=s.reg (low d i)) ∧
      FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  let s₀ := s.setReg (low d 69) 0
  have h₀ := TapeMacros.clear_stops (B := 3) (low d 69) inp (s.reg (low d 69)) s rfl
  have hb₀ : ∀ j,s₀.reg j ≤ M := FieldPrograms.setReg_bound _ _ _ _ hc.bounded (by omega)
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := SamplerOdometer.initialize_stops (low d 23) (low d 2) (tuple d 2)
    (tuple_unique d 2) inp M s₀ hb₀
  have hf₁ (i : Fin 80) (hi : i≠2) : c₁.reg (low d i)=s₀.reg (low d i) := by
    change c₁.store.reg (low d i)=_
    rw [hs₁]
    exact SamplerOdometer.initializeStore_fresh _ _ _ _ _ ((low_eq_iff d _ _).not.mpr hi) (low_not_tuple d 2 i)
  have htape₁ : FieldConvolution.tapeData c₁.store=FieldConvolution.tapeData s := by
    rw [hs₁,initialize_payload]
    rfl
  have h₂ := TapeMacros.clear_stops (low d 73) inp (c₁.reg (low d 73)) c₁.store rfl
  let s₂ := c₁.store.setReg (low d 73) 0
  have hb₂ : ∀ j,s₂.reg j ≤ M := FieldPrograms.setReg_bound _ _ _ _ hb₁ (by omega)
  obtain ⟨t₃,e,ht₃,h₃,hs₃,hb₃⟩ := SamplerEvaluation.copy_stops_bound (low d 70) (low d 76) (low d 2)
    (by simp) (by simp) (by simp) inp M s₂ hb₂
  have h70 : s₂.reg (low d 70)=(2^ell)^d := by
    simp only [s₂,TapeStore.setReg,Function.update_of_ne (show low d 70≠low d 73 by simp)]
    rw [hf₁ 70 (by decide)]
    simpa [s₀,TapeStore.setReg] using hc.size
  have hreg (i : Fin 80) : e.reg (low d i)=
      if i=2 then 0 else if i=76 then (2^ell)^d else if i=73 then 0 else c₁.reg (low d i) := by
    change e.store.reg (low d i)=_
    rw [hs₃]
    simp only [h70,s₂,TapeStore.setReg]
    have h70' : c₁.reg (low d 70)=(2^ell)^d := by simpa [s₂,TapeStore.setReg] using h70
    simp [Function.update,low_eq_iff,h70']
  have hdig (g : Fin 6) (i : Fin d) : e.reg (digit d g i)=c₁.reg (digit d g i) := by
    change e.store.reg (digit d g i)=_
    rw [hs₃]
    simp [s₂,TapeStore.setReg,Function.update_of_ne (digit_ne_low d g i _)]
  have htape : FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
    rw [hs₃]
    simpa only [s₂,FieldConvolution.tapeData_setReg] using htape₁
  have hframe (i : Fin 80) (hi : i≠2 ∧ i≠69 ∧ i≠73 ∧ i≠76) : e.reg (low d i)=s.reg (low d i) := by
    rw [hreg]
    simp only [hi.1,hi.2.2.2,hi.2.2.1,if_false]
    rw [hf₁ i hi.1]
    simp [s₀,TapeStore.setReg,((low_eq_iff d _ _).not.mpr hi.2.1)]
  have hnum (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k c₁.store) : Numbered d g (2^ell) k e.store := by
    apply hn.frame (by simpa [hreg])
    intro j hj
    obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj <;> exact hdig _ i
  have hnum₀ (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k s) : Numbered d g (2^ell) k s₀ :=
    hn.setReg 69 (by decide) 0
  have hall := ((h₀.seq h₁).seq h₂).seq h₃
  refine ⟨_,_,?_,hall,?_,?_,?_,?_,?_,?_,?_,?_,htape⟩
  · have h69 := hc.bounded (low d 69)
    have h73 := hc.bounded (low d 73)
    have hf73 : c₁.reg (low d 73)=s.reg (low d 73) := by rw [hf₁ 73 (by decide)]; simp [s₀,TapeStore.setReg]
    simp only [tuple,List.length_ofFn] at ht₁
    rw [hf73]
    omega
  · apply hc.frame hb₃ _ (tapeData_payload htape) (congrFun (tapeData_head htape) 2)
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> exact hframe _ (by decide)
  · apply hnum
    rw [hs₁]
    exact initialize_other d 0 2 (by decide) _ _ s₀ (hnum₀ 0 _ ha)
  · apply hnum
    rw [hs₁]
    exact initialize_other d 1 2 (by decide) _ _ s₀ (hnum₀ 1 _ hb)
  · apply hnum
    rw [hs₁]
    apply numbered_initialize d 2 _ (Nat.one_lt_pow h.ne' (by decide))
    simpa [s₀,TapeStore.setReg,termWorkspace] using hc.environment.cardinal
  · simp [hreg]
  · rw [hreg]
    simpa [s₀,TapeStore.setReg] using hf₁ 69 (by decide)
  · simp [hreg]
  · intro i hi hi73 hi76
    apply hframe
    refine ⟨?_,?_,hi73,hi76⟩
    all_goals intro he; subst i; norm_num at hi



private theorem Core.frame_input {d ell : ℕ} {h : 0<ell} {D M : ℕ}
    {y : Fin ((2^ell)^d) → Bool} {s e : TapeStore (80+6*d) 3}
    (hc : Core d ell h D M y s) (hb : ∀ j,e.reg j ≤ M)
    (hf : ∀ i : Fin 80,i=3 ∨ i=19 ∨ i=23 ∨ i=24 ∨ i=65 ∨ i=70 → e.reg (low d i)=s.reg (low d i))
    (hs : ∀ k,(e.bufferTape 2).getD k .blank=(s.bufferTape 2).getD k .blank)
    (hh : e.bufferHead 2=s.bufferHead 2) : Core d ell h D M y e := by
  refine ⟨hb,?_,(hf 65 (by tauto)).trans hc.degree,(hf 70 (by tauto)).trans hc.size,?_,?_,?_⟩
  · apply hc.environment.frame
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl <;> exact hf _ (by tauto)
  · exact ⟨by rw [hs]; exact hc.inputMarked.1,fun k hk => by rw [hs]; exact hc.inputMarked.2 k hk⟩
  · intro z
    exact ⟨(hc.inputTable z).1,fun k hk => by rw [hs]; exact (hc.inputTable z).2 k hk⟩
  · rw [hh]
    exact hc.inputHead

















private theorem pairFinishAfter_stops {L : ℕ} (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) (v : Fin (2^ell)) (flat : ℕ)
    (inp : Inputs) (s : TapeStore (80+6*d) 3) (hc : Core d ell h D M y s)
    (ha : Numbered d 0 (2^ell) a.val s) (hb : Numbered d 1 (2^ell) b.val s)
    (hv : s.reg (low d 69)=v.val) (hi : s.reg (low d 72)=b.val)
    (hf : s.reg (low d 77)=flat) (hflat : flat+1 ≤ M)
    (P : TapeProgram (80+6*d) 3 L) (origin : TapeStore (80+6*d) 3) (tP : ℕ)
    (hP : ∃ c,P.Stops inp (origin.toCfg P.entry) tP c ∧ c.store=s) :
    ∃ t e,t ≤ tP+d*(8*M+20)+10*M+17 ∧
      (pairFinishAfter d P).Stops inp (origin.toCfg (pairFinishAfter d P).entry) t e ∧
      Core d ell h D M y e.store ∧ Numbered d 0 (2^ell) a.val e.store ∧
      Numbered d 1 (2^ell) (b.val+1) e.store ∧ e.reg (low d 72)=b.val+1 ∧ e.reg (low d 77)=flat+1 ∧
      (∀ i : Fin 80,70 ≤ i.val → i≠72 → i≠77 → i≠79 → e.reg (low d i)=s.reg (low d i)) ∧
      TapeArrays.EntryWritten s e.store 0 (s.bufferHead 0) (2^ell) v.val := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := SamplerEvaluation.copy_stops_bound (low d 23) (low d 79) (low d 2)
    (by simp) (by simp) (by simp) inp M s hc.bounded
  have hq : s.reg (low d 23)=2^ell := hc.environment.cardinal
  have hv₁ : c₁.reg (low d 69)=v.val := by change c₁.store.reg _=_; rw [hs₁]; simpa [TapeStore.setReg] using hv
  have hw₁ : c₁.reg (low d 79)=2^ell := by change c₁.store.reg _=_; rw [hs₁]; simp [TapeStore.setReg,hq]
  obtain ⟨c₂,h₂,hs₂⟩ := TapeArrays.writeBlock_stops (low d 69) (low d 79) (by simp) 0 inp v.val (2^ell)
    c₁.store hv₁ hw₁ (Nat.le_of_lt v.isLt)
  have hreg₂ : c₂.reg=((c₁.store.setReg (low d 69) 0).setReg (low d 79) 0).reg := by
    change c₂.store.reg=_
    rw [hs₂,TapeArrays.writeBlockStore_reg]
  have hb₂ : ∀ j,c₂.reg j ≤ M := by
    rw [hreg₂]
    exact FieldPrograms.setReg_bound _ _ _ _ (FieldPrograms.setReg_bound _ _ _ _ hb₁ (by omega)) (by omega)
  have hf₂ (i : Fin 80) (hi : i≠2 ∧ i≠69 ∧ i≠79) : c₂.reg (low d i)=s.reg (low d i) := by
    rw [hreg₂]
    simp only [TapeStore.setReg,Function.update_of_ne ((low_eq_iff d _ _).not.mpr hi.2.2),
      Function.update_of_ne ((low_eq_iff d _ _).not.mpr hi.2.1)]
    change c₁.store.reg (low d i)=_
    rw [hs₁]
    simp [TapeStore.setReg,((low_eq_iff d _ _).not.mpr hi.1),((low_eq_iff d _ _).not.mpr hi.2.2)]
  have hd₂ (g : Fin 6) (i : Fin d) : c₂.reg (digit d g i)=s.reg (digit d g i) := by
    rw [hreg₂]
    simp only [TapeStore.setReg,Function.update_of_ne (digit_ne_low d g i _)]
    change c₁.store.reg (digit d g i)=_
    rw [hs₁]
    simp only [TapeStore.setReg,Function.update_of_ne (digit_ne_low d g i _)]
  have hn₂ (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k s) : Numbered d g (2^ell) k c₂.store := by
    apply hn.frame (hf₂ 23 (by decide))
    intro j hj
    obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj <;> exact hd₂ _ i
  have h₃ := TapeMacros.increment_stops (low d 77) inp c₂.store
  let s₃ := c₂.store.setReg (low d 77) (c₂.reg (low d 77)+1)
  have hf₂77 : c₂.reg (low d 77)=flat := (hf₂ 77 (by decide)).trans hf
  have hb₃ : ∀ j,s₃.reg j ≤ M := FieldPrograms.setReg_bound _ _ _ _ hb₂ (by rw [hf₂77]; exact hflat)
  have hn₃ : Numbered d 1 (2^ell) b.val s₃ := (hn₂ 1 _ hb).setReg 77 (by decide) _
  obtain ⟨t₄,c₄,ht₄,h₄,hs₄,hb₄⟩ := SamplerOdometer.program_stops_valid (low d 23) (low d 2) (tuple d 1)
    (tuple_unique d 1) inp M s₃ hb₃ hn₃.2.1
  have hf₄ (i : Fin 80) (hi : i≠2) : c₄.reg (low d i)=s₃.reg (low d i) := by
    change c₄.store.reg (low d i)=_
    rw [hs₄]
    exact SamplerOdometer.nextStore_fresh _ _ _ _ _ ((low_eq_iff d _ _).not.mpr hi) (low_not_tuple d 1 i)
  have hi₄ : c₄.reg (low d 72)=b.val := by rw [hf₄ 72 (by decide)]; simpa [s₃,TapeStore.setReg] using (hf₂ 72 (by decide)).trans hi
  have h₅ := TapeMacros.increment_stops (low d 72) inp c₄.store
  let e := (c₄.store.setReg (low d 72) (c₄.reg (low d 72)+1)).toCfg (1 : Fin 2)
  have hb₅ : ∀ j,e.reg j ≤ M := by
    apply FieldPrograms.setReg_bound _ _ _ _ hb₄
    rw [hi₄]
    have hm := hc.bounded (low d 70)
    rw [hc.size] at hm
    have hh := b.isLt
    omega
  have hreg (i : Fin 80) (hi : i≠2 ∧ i≠72 ∧ i≠77 ∧ i≠69 ∧ i≠79) : e.reg (low d i)=s.reg (low d i) := by
    change (c₄.store.setReg (low d 72) _).reg (low d i)=_
    simp only [TapeStore.setReg,Function.update_of_ne ((low_eq_iff d _ _).not.mpr hi.2.1)]
    rw [hf₄ i hi.1]
    simp only [s₃,TapeStore.setReg,Function.update_of_ne ((low_eq_iff d _ _).not.mpr hi.2.2.1)]
    exact hf₂ i ⟨hi.1,hi.2.2.2⟩
  have hpay₄ : FieldConvolution.tapeData c₄.store=FieldConvolution.tapeData c₂.store := by
    rw [hs₄]
    have hh := SamplerOdometer.nextStore_payload (low d 23) (low d 2) (tuple d 1) s₃
    exact congrArg (fun (x : (Fin 4 → ℕ) × List Bool × (Fin 3 → List Sym) × (Fin 3 → ℕ)) => x)
      (show FieldConvolution.tapeData (SamplerOdometer.nextStore (low d 23) (low d 2) (tuple d 1) s₃)=FieldConvolution.tapeData s₃ by
        simp only [FieldConvolution.tapeData,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2])
  have hpay : FieldConvolution.tapeData e.store=FieldConvolution.tapeData c₂.store := hpay₄
  have hw : TapeArrays.EntryWritten s e.store 0 (s.bufferHead 0) (2^ell) v.val := by
    have hp := tapeData_payload hpay
    have hh := tapeData_head hpay
    have hro : c₂.roHead=s.roHead := by change c₂.store.roHead=_; rw [hs₂,TapeArrays.writeBlockStore_roHead,hs₁]; rfl
    have hout : c₂.output=s.output := by change c₂.store.output=_; rw [hs₂,TapeArrays.writeBlockStore_output,hs₁]; rfl
    refine ⟨hp.roHead.trans hro,hp.output.trans hout,?_,?_⟩
    · rw [hh]
      change c₂.store.bufferHead=_
      rw [hs₂,TapeArrays.writeBlockStore_head _ _ _ _ _ _ (Nat.le_of_lt v.isLt),hs₁]
      rfl
    · intro c k
      rw [hp.symbol]
      change (c₂.store.bufferTape c).getD k .blank=_
      rw [hs₂,TapeArrays.writeBlockStore_symbol _ _ _ _ _ _ (Nat.le_of_lt v.isLt),hs₁]
      rfl
  have hn₅ (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k c₄.store) : Numbered d g (2^ell) k e.store :=
    hn.setReg 72 (by decide) _
  obtain ⟨cP,hP,hPs⟩ := hP
  rw [← hPs] at h₁
  have hall := ((((hP.seq h₁).seq h₂).seq h₃).seq h₄).seq h₅
  refine ⟨_,_,?_,hall,?_,?_,?_,?_,?_,?_,hw⟩
  · have hqM : 2^ell ≤ M := hq ▸ hc.bounded (low d 23)
    have hvM := v.isLt
    simp only [tuple,List.length_ofFn] at ht₄
    omega
  · apply hc.frame_input hb₅ _ _ _
    · intro i hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
      · exact hreg 3 (by decide)
      · exact hreg 19 (by decide)
      · exact hreg 23 (by decide)
      · exact hreg 24 (by decide)
      · exact hreg 65 (by decide)
      · exact hreg 70 (by decide)
    · intro k
      simpa using hw.symbol 2 k
    · rw [hw.head]
      rfl
  · apply hn₅
    rw [hs₄]
    exact numbered_next_other d 0 1 (by decide) _ _ s₃ ((hn₂ 0 _ ha).setReg 77 (by decide) _)
  · apply hn₅
    rw [hs₄]
    exact numbered_next d 1 _ _ (Nat.one_lt_pow h.ne' (by decide)) s₃ hn₃
  · simp [e,TapeStore.setReg,hi₄]
  · change (c₄.store.setReg (low d 72) (c₄.reg (low d 72)+1)).reg (low d 77)=_
    simp only [TapeStore.setReg,Function.update_of_ne (show low d 77≠low d 72 by simp)]
    rw [hf₄ 77 (by decide)]
    simp [s₃,TapeStore.setReg,hf₂77]
  · intro i hi hi72 hi77 hi79
    apply hreg
    refine ⟨?_,hi72,hi77,?_,hi79⟩
    all_goals intro he; subst i; norm_num at hi















private theorem pairBody_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) (flat : ℕ)
    (inp : Inputs) (s : TapeStore (80+6*d) 3) (hc : Core d ell h D M y s)
    (ha : Numbered d 0 (2^ell) a.val s) (hb : Numbered d 1 (2^ell) b.val s)
    (hi : s.reg (low d 72)=b.val) (hf : s.reg (low d 77)=flat)
    (hh : s.bufferHead 0=1+flat*(2^ell)) (hflat : flat+1 ≤ M)
    (hdM : d*((2^ell)-1) ≤ M) (hhead : 1+(2^ell)^d*(2^ell) ≤ M) :
    ∃ t e,t ≤ pairTime d M ((2^ell)^d) ∧ (pairBody d).Stops inp (s.toCfg (pairBody d).entry) t e ∧
      Core d ell h D M y e.store ∧ Numbered d 0 (2^ell) a.val e.store ∧
      Numbered d 1 (2^ell) (b.val+1) e.store ∧ e.reg (low d 72)=b.val+1 ∧ e.reg (low d 77)=flat+1 ∧
      (∀ i : Fin 80,70 ≤ i.val → i≠72 → i≠73 → i≠76 → i≠77 → i≠78 → i≠79 →
        e.reg (low d i)=s.reg (low d i)) ∧
      GramEffect d s e.store (2^ell) flat (EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1.val := by
  obtain ⟨t₁,c₁,ht₁,h₁,hc₁,ha₁,hb₁,hz₁,hi₁,hv₁,hn₁,hf₁,hd₁⟩ := pairPrepare_stops d ell h D M y a b inp s hc ha hb
  obtain ⟨t₂,c₂,ht₂,h₂,hc₂,hv₂,ha₂,hb₂,hi₂,hn₂,hf₂,hp₂,hh₂⟩ := pointLoop_stops d ell h D M hM y a b inp c₁.store
    hc₁ ha₁ hb₁ hz₁ hi₁ hv₁ hn₁ hdM hhead
  have hpre := h₁.seq h₂
  have hreg (i : Fin 80) (hi : 70 ≤ i.val) (hi73 : i≠73) (hi76 : i≠76) (hi78 : i≠78) :
      c₂.reg (low d i)=s.reg (low d i) := (hf₂ i hi hi73 hi76 hi78).trans (hf₁ i hi hi73 hi76)
  have hpay : TapeStore.SamePayload c₂.store s := hp₂.trans (tapeData_payload hd₁)
  have hheads (c : Fin 3) (hc2 : c≠2) : c₂.bufferHead c=s.bufferHead c :=
    (hh₂ c hc2).trans (congrFun (tapeData_head hd₁) c)
  obtain ⟨t₃,e,ht₃,h₃,hce,hae,hbe,hie,hfe,hre,hwrite⟩ := pairFinishAfter_stops d ell h D M y a b
    (EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1 flat inp c₂.store hc₂ ha₂ hb₂ hv₂
    ((hreg 72 (by decide) (by decide) (by decide) (by decide)).trans hi)
    ((hreg 77 (by decide) (by decide) (by decide) (by decide)).trans hf) hflat
    (TapeProgram.seq (pairPrepare d) (TapeProgram.countedLoop (pointBody d) (low d 76))) s (t₁+1+t₂)
    ⟨_,hpre,rfl⟩
  refine ⟨t₃,_,?_,h₃,hce,hae,hbe,hie,hfe,?_,?_⟩
  · unfold pairTime
    omega
  · intro i hi hi72 hi73 hi76 hi77 hi78 hi79
    exact (hre i hi hi72 hi77 hi79).trans (hreg i hi hi73 hi76 hi78)
  · have hstart : c₂.store.bufferHead 0=1+flat*(2^ell) := (hheads 0 (by decide)).trans hh
    refine ⟨hwrite.roHead.trans hpay.roHead,hwrite.output.trans hpay.output,?_,?_,?_⟩
    · change e.store.bufferHead 0=_
      rw [hwrite.head]
      have hstart' : c₂.bufferHead 0=1+flat*(2^ell) := hstart
      simp only [Function.update_self,hstart',Nat.add_mul,Nat.one_mul,Nat.add_assoc]
    · change e.store.bufferHead 1=_
      rw [hwrite.head,Function.update_of_ne (by decide : (1:Fin 3)≠0)]
      exact hheads 1 (by decide)
    · intro c k
      rw [hwrite.symbol,hpay.symbol,hstart]
      simp only [Nat.add_mul,Nat.one_mul,Nat.add_assoc]






private theorem GramEffect.prefix {d q flat v : ℕ} {s e : TapeStore (80+6*d) 3}
    (he : GramEffect d s e q flat v) (value : ℕ → ℕ) (hv : v=value flat) (hvq : v ≤ q)
    (hp : GramPrefix d q value flat s) : GramPrefix d q value (flat+1) e := by
  intro k hk
  by_cases heq : k=flat
  · subst k
    refine ⟨hv ▸ hvq,?_⟩
    intro j hj
    rw [he.symbol]
    have hright : 1+flat*q+j<1+(flat+1)*q := by rw [Nat.add_mul,Nat.one_mul]; omega
    have hleft : 1+flat*q ≤ 1+flat*q+j := by omega
    simp only [true_and,hleft,hright,and_self,if_true]
    rw [← hv]
    split_ifs <;> first | rfl | omega
  · have hkflat : k<flat := by omega
    refine ⟨(hp k hkflat).1,?_⟩
    intro j hj
    rw [he.symbol]
    have hmul := Nat.mul_le_mul_right q (show k+1 ≤ flat by omega)
    rw [Nat.add_mul,Nat.one_mul] at hmul
    have hnot : ¬ (1+flat*q ≤ 1+k*q+j) := by omega
    simp only [hnot,false_and,and_false,if_false]
    exact (hp k hkflat).2 j hj

private theorem GramEffect.bottomMarked {d q flat v : ℕ} {s e : TapeStore (80+6*d) 3}
    (he : GramEffect d s e q flat v) (hm : TapeArrays.BottomMarked s 0) : TapeArrays.BottomMarked e 0 := by
  constructor
  · rw [he.symbol]
    have hh : ¬1+flat*q ≤ 0 := by omega
    simp only [hh,false_and,and_false,if_false]
    exact hm.1
  · intro k hk
    rw [he.symbol]
    split_ifs <;> first | decide | exact hm.2 k hk




private theorem gramValue_pair (d ell : ℕ) (h : 0<ell) (D : ℕ) (y : Fin ((2^ell)^d) → Bool)
    (a b : Fin ((2^ell)^d)) :
    gramValue d ell h D y (a.val*(2^ell)^d+b.val)=
      (EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1.val := by
  have hval : (finProdFinEquiv (a,b)).val=a.val*(2^ell)^d+b.val := by simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  have hk : a.val*(2^ell)^d+b.val<(2^ell)^d*(2^ell)^d := hval ▸ (finProdFinEquiv (a,b)).isLt
  have he : (⟨a.val*(2^ell)^d+b.val,hk⟩ : Fin ((2^ell)^d*(2^ell)^d))=finProdFinEquiv (a,b) := Fin.ext hval.symm
  simp [gramValue,GaussianProgram.flatEntry,dif_pos hk,he,EncodedTester.table,Gaussian.toMatrix,Gaussian.ofMatrix]














private theorem BuildState.frame {d ell : ℕ} {h : 0<ell} {D M flat : ℕ}
    {y : Fin ((2^ell)^d) → Bool} {origin s e : TapeStore (80+6*d) 3}
    (hs : BuildState d ell h D M y origin flat s) (hc : Core d ell h D M y e)
    (hi : e.reg (low d 77)=flat) (ht : FieldConvolution.tapeData e=FieldConvolution.tapeData s) :
    BuildState d ell h D M y origin flat e := by
  have hp := tapeData_payload ht
  have hh := tapeData_head ht
  refine ⟨hc,hi,(congrFun hh 0).trans hs.head,?_,hs.marked.of_payload hp,hs.spareMarked.of_payload hp,
    (congrFun hh 1).trans hs.spareHead,hp.roHead.trans hs.roHead,hp.output.trans hs.output⟩
  intro k hk
  exact (hs.entries k hk).of_payload hp

private theorem BuildState.after_pair {d ell : ℕ} {h : 0<ell} {D M flat : ℕ}
    {y : Fin ((2^ell)^d) → Bool} {origin s e : TapeStore (80+6*d) 3}
    (hs : BuildState d ell h D M y origin flat s) (hc : Core d ell h D M y e)
    (hi : e.reg (low d 77)=flat+1) (a b : Fin ((2^ell)^d))
    (hflat : flat=a.val*(2^ell)^d+b.val)
    (he : GramEffect d s e (2^ell) flat (EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1.val) :
    BuildState d ell h D M y origin (flat+1) e := by
  refine ⟨hc,hi,he.head,?_,he.bottomMarked hs.marked,?_,he.spareHead.trans hs.spareHead,
    he.roHead.trans hs.roHead,he.output.trans hs.output⟩
  · apply he.prefix _ _ (Nat.le_of_lt (EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1.isLt) hs.entries
    rw [hflat,gramValue_pair]
  · constructor
    · rw [he.symbol]
      simpa using hs.spareMarked.1
    · intro k hk
      rw [he.symbol]
      simpa using hs.spareMarked.2 k hk







private theorem rowPrepare_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a : Fin ((2^ell)^d))
    (inp : Inputs) (s : TapeStore (80+6*d) 3) (hc : Core d ell h D M y s)
    (ha : Numbered d 0 (2^ell) a.val s) :
    ∃ t e,t ≤ d*(8*M+20)+8*M+10 ∧ (rowPrepare d).Stops inp (s.toCfg (rowPrepare d).entry) t e ∧
      Core d ell h D M y e.store ∧ Numbered d 0 (2^ell) a.val e.store ∧ Numbered d 1 (2^ell) 0 e.store ∧
      e.reg (low d 72)=0 ∧ e.reg (low d 75)=(2^ell)^d ∧
      (∀ i : Fin 80,70 ≤ i.val → i≠72 → i≠75 → e.reg (low d i)=s.reg (low d i)) ∧
      FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := SamplerOdometer.initialize_stops (low d 23) (low d 2) (tuple d 1)
    (tuple_unique d 1) inp M s hc.bounded
  have hf₁ (i : Fin 80) (hi : i≠2) : c₁.reg (low d i)=s.reg (low d i) := by
    change c₁.store.reg (low d i)=_
    rw [hs₁]
    exact SamplerOdometer.initializeStore_fresh _ _ _ _ _ ((low_eq_iff d _ _).not.mpr hi) (low_not_tuple d 1 i)
  have htape₁ : FieldConvolution.tapeData c₁.store=FieldConvolution.tapeData s := by rw [hs₁,initialize_payload]
  have h₂ := TapeMacros.clear_stops (low d 72) inp (c₁.reg (low d 72)) c₁.store rfl
  let s₂ := c₁.store.setReg (low d 72) 0
  have hb₂ : ∀ j,s₂.reg j ≤ M := FieldPrograms.setReg_bound _ _ _ _ hb₁ (by omega)
  obtain ⟨t₃,e,ht₃,h₃,hs₃,hb₃⟩ := SamplerEvaluation.copy_stops_bound (low d 70) (low d 75) (low d 2)
    (by simp) (by simp) (by simp) inp M s₂ hb₂
  have h70 : c₁.reg (low d 70)=(2^ell)^d := (hf₁ 70 (by decide)).trans hc.size
  have hreg (i : Fin 80) : e.reg (low d i)=
      if i=2 then 0 else if i=75 then (2^ell)^d else if i=72 then 0 else c₁.reg (low d i) := by
    change e.store.reg (low d i)=_
    rw [hs₃]
    simp [s₂,TapeStore.setReg,Function.update,low_eq_iff,h70]
  have hdig (g : Fin 6) (i : Fin d) : e.reg (digit d g i)=c₁.reg (digit d g i) := by
    change e.store.reg (digit d g i)=_
    rw [hs₃]
    simp [s₂,TapeStore.setReg,Function.update_of_ne (digit_ne_low d g i _)]
  have htape : FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
    rw [hs₃]
    simpa only [s₂,FieldConvolution.tapeData_setReg] using htape₁
  have hframe (i : Fin 80) (hi : i≠2 ∧ i≠72 ∧ i≠75) : e.reg (low d i)=s.reg (low d i) := by
    rw [hreg]
    simp only [hi.1,hi.2.2,hi.2.1,if_false]
    exact hf₁ i hi.1
  have hnum (g : Fin 3) (k : ℕ) (hn : Numbered d g (2^ell) k c₁.store) : Numbered d g (2^ell) k e.store := by
    apply hn.frame (by simpa [hreg])
    intro j hj
    obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj <;> exact hdig _ i
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_,_,?_,hall,?_,?_,?_,?_,?_,?_,htape⟩
  · have h72 := hc.bounded (low d 72)
    rw [hf₁ 72 (by decide)]
    simp only [tuple,List.length_ofFn] at ht₁
    omega
  · apply hc.frame hb₃ _ (tapeData_payload htape) (congrFun (tapeData_head htape) 2)
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> exact hframe _ (by decide)
  · apply hnum
    rw [hs₁]
    exact initialize_other d 0 1 (by decide) _ _ s ha
  · apply hnum
    rw [hs₁]
    exact numbered_initialize d 1 _ (Nat.one_lt_pow h.ne' (by decide)) s hc.environment.cardinal
  · simp [hreg]
  · simp [hreg]
  · intro i hi hi72 hi75
    apply hframe
    refine ⟨?_,hi72,hi75⟩
    intro he; subst i; norm_num at hi














private theorem rowLoop_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
    (y : Fin ((2^ell)^d) → Bool) (a : Fin ((2^ell)^d))
    (origin : TapeStore (80+6*d) 3) (inp : Inputs) (s : TapeStore (80+6*d) 3)
    (hc : BuildState d ell h D M y origin (a.val*(2^ell)^d) s)
    (ha : Numbered d 0 (2^ell) a.val s) (hb : Numbered d 1 (2^ell) 0 s)
    (hai : s.reg (low d 71)=a.val) (hbi : s.reg (low d 72)=0)
    (hn : s.reg (low d 75)=(2^ell)^d)
    (hdM : d*((2^ell)-1) ≤ M) (hhead : 1+(2^ell)^d*(2^ell) ≤ M)
    (hmatrix : (2^ell)^d*(2^ell)^d ≤ M) :
    ∃ t e,t ≤ (2^ell)^d*(pairTime d M ((2^ell)^d)+2)+1 ∧
      (TapeProgram.countedLoop (pairBody d) (low d 75)).Stops inp
        (s.toCfg (TapeProgram.countedLoop (pairBody d) (low d 75)).entry) t e ∧
      BuildState d ell h D M y origin ((a.val+1)*(2^ell)^d) e.store ∧
      Numbered d 0 (2^ell) a.val e.store ∧ e.reg (low d 71)=a.val ∧
      e.reg (low d 74)=s.reg (low d 74) ∧ e.reg (low d 75)=0 := by
  let Inv := RowLoopInv d ell h D M y origin a (s.reg (low d 74))
  have hbody (n : ℕ) (c : TapeStore (80+6*d) 3) (hcn : c.reg (low d 75)=n+1) (hi : Inv (n+1) c) :
      ∃ t e,t ≤ pairTime d M ((2^ell)^d) ∧ (pairBody d).Stops inp
        ((TapeProgram.decStore (low d 75) c).toCfg (pairBody d).entry) t e ∧ Inv n e.store ∧ e.reg (low d 75)=n := by
    let k := (2^ell)^d-(n+1)
    have hk : k<(2^ell)^d := by dsimp [k]; have := hi.le; omega
    have hkn : (2^ell)^d-n=k+1 := by dsimp [k]; have := hi.le; omega
    let c' := c.setReg (low d 75) n
    have hc' : TapeProgram.decStore (low d 75) c=c' := by simp [TapeProgram.decStore,c',TapeStore.setReg,hcn]
    have hbnd : n ≤ M := by have hh := hi.build.core.bounded (low d 75); rw [hcn] at hh; omega
    have hcore := hi.build.core.setReg 75 (by decide) (by decide) n hbnd
    have hbuild : BuildState d ell h D M y origin (a.val*(2^ell)^d+k) c' := by
      apply hi.build.frame hcore
      · simpa [c',TapeStore.setReg,k] using hi.build.index
      · rfl
    have hflat : a.val*(2^ell)^d+k+1 ≤ M := by
      have hh := (finProdFinEquiv (a,(⟨k,hk⟩ : Fin ((2^ell)^d)))).isLt
      have hnum : (finProdFinEquiv (a,(⟨k,hk⟩ : Fin ((2^ell)^d)))).val=a.val*(2^ell)^d+k := by simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
      rw [hnum] at hh
      omega
    obtain ⟨t,e,ht,he,hec,hea,heb,hei,hef,her,hew⟩ := pairBody_stops d ell h D M hM y a ⟨k,hk⟩ (a.val*(2^ell)^d+k) inp c'
      hcore (hi.aTuple.setReg 75 (by decide) n) (hi.bTuple.setReg 75 (by decide) n)
      (by simpa [c',TapeStore.setReg,k] using hi.bIndex) hbuild.index hbuild.head hflat hdM hhead
    refine ⟨t,e,ht,?_,?_,?_⟩
    · simpa only [hc'] using he
    · refine ⟨by have := hi.le; omega,?_,hea,?_,?_,?_,?_⟩
      · have hb' := hbuild.after_pair hec hef a ⟨k,hk⟩ rfl hew
        convert hb' using 1 <;> rw [hkn] <;> omega
      · simpa only [hkn] using heb
      · exact (her 71 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          (by simpa [c',TapeStore.setReg] using hi.aIndex)
      · simpa only [hkn] using hei
      · exact (her 74 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          (by simpa [c',TapeStore.setReg] using hi.outer)
    · rw [her 75 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp [c',TapeStore.setReg]
  have hi : Inv ((2^ell)^d) s := by
    refine ⟨le_rfl,?_,ha,?_,hai,?_,rfl⟩
    · simpa using hc
    · simpa using hb
    · simpa using hbi
  obtain ⟨t,e,ht,he,hie,hez⟩ := loop_stops (pairBody d) (low d 75) inp (pairTime d M ((2^ell)^d)) Inv hbody
    ((2^ell)^d) s hn hi
  refine ⟨t,_,ht,he,?_,hie.aTuple,hie.aIndex,hie.outer,hez⟩
  convert hie.build using 1
  simp only [Nat.sub_zero]
  ring







private theorem rowFinishAfter_stops {L : ℕ} (d ell : ℕ) (h : 0<ell) (D M flat : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a : Fin ((2^ell)^d))
    (origin : TapeStore (80+6*d) 3) (inp : Inputs) (s : TapeStore (80+6*d) 3)
    (hs : BuildState d ell h D M y origin flat s) (ha : Numbered d 0 (2^ell) a.val s)
    (hi : s.reg (low d 71)=a.val)
    (P : TapeProgram (80+6*d) 3 L) (start : TapeStore (80+6*d) 3) (tP : ℕ)
    (hP : ∃ c,P.Stops inp (start.toCfg P.entry) tP c ∧ c.store=s) :
    ∃ t e,t ≤ tP+d*(8*M+20)+3 ∧ (rowFinishAfter d P).Stops inp (start.toCfg (rowFinishAfter d P).entry) t e ∧
      BuildState d ell h D M y origin flat e.store ∧ Numbered d 0 (2^ell) (a.val+1) e.store ∧
      e.reg (low d 71)=a.val+1 ∧ e.reg (low d 74)=s.reg (low d 74) := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := SamplerOdometer.program_stops_valid (low d 23) (low d 2) (tuple d 0)
    (tuple_unique d 0) inp M s hs.core.bounded ha.2.1
  have hf₁ (i : Fin 80) (hi : i≠2) : c₁.reg (low d i)=s.reg (low d i) := by
    change c₁.store.reg (low d i)=_
    rw [hs₁]
    exact SamplerOdometer.nextStore_fresh _ _ _ _ _ ((low_eq_iff d _ _).not.mpr hi) (low_not_tuple d 0 i)
  have hi₁ : c₁.reg (low d 71)=a.val := (hf₁ 71 (by decide)).trans hi
  have h₂ := TapeMacros.increment_stops (low d 71) inp c₁.store
  let e := (c₁.store.setReg (low d 71) (c₁.reg (low d 71)+1)).toCfg (1 : Fin 2)
  have hb₂ : ∀ j,e.reg j ≤ M := by
    apply FieldPrograms.setReg_bound _ _ _ _ hb₁
    rw [hi₁]
    have hm := hs.core.bounded (low d 70)
    rw [hs.core.size] at hm
    have hh := a.isLt
    omega
  have hframe (i : Fin 80) (hi : i≠2 ∧ i≠71) : e.reg (low d i)=s.reg (low d i) := by
    change (c₁.store.setReg (low d 71) (c₁.reg (low d 71)+1)).reg (low d i)=_
    simp only [TapeStore.setReg,Function.update_of_ne ((low_eq_iff d _ _).not.mpr hi.2)]
    exact hf₁ i hi.1
  have hdata : FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
    change FieldConvolution.tapeData c₁.store=_
    rw [hs₁]
    have hh := SamplerOdometer.nextStore_payload (low d 23) (low d 2) (tuple d 0) s
    simp only [FieldConvolution.tapeData,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2]
  have hcore : Core d ell h D M y e.store := by
    apply hs.core.frame hb₂ _ (tapeData_payload hdata) (congrFun (tapeData_head hdata) 2)
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hframe 3 (by decide)
    · exact hframe 19 (by decide)
    · exact hframe 23 (by decide)
    · exact hframe 24 (by decide)
    · exact hframe 65 (by decide)
    · exact hframe 70 (by decide)
  obtain ⟨cP,hP,hPs⟩ := hP
  rw [← hPs] at h₁
  have hall := (hP.seq h₁).seq h₂
  refine ⟨_,_,?_,hall,hs.frame hcore ((hframe 77 (by decide)).trans hs.index) hdata,?_,?_,hframe 74 (by decide)⟩
  · simp only [tuple,List.length_ofFn] at ht₁
    omega
  · have hh : Numbered d 0 (2^ell) (a.val+1) c₁.store := by
      rw [hs₁]
      exact numbered_next d 0 _ _ (Nat.one_lt_pow h.ne' (by decide)) s ha
    exact hh.setReg 71 (by decide) _
  · simp [e,TapeStore.setReg,hi₁]



private theorem rowBody_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
    (y : Fin ((2^ell)^d) → Bool) (a : Fin ((2^ell)^d))
    (origin : TapeStore (80+6*d) 3) (inp : Inputs) (s : TapeStore (80+6*d) 3)
    (hs : BuildState d ell h D M y origin (a.val*(2^ell)^d) s)
    (ha : Numbered d 0 (2^ell) a.val s) (hi : s.reg (low d 71)=a.val)
    (hdM : d*((2^ell)-1) ≤ M) (hhead : 1+(2^ell)^d*(2^ell) ≤ M)
    (hmatrix : (2^ell)^d*(2^ell)^d ≤ M) :
    ∃ t e,t ≤ rowTime d M ((2^ell)^d) ∧ (rowBody d).Stops inp (s.toCfg (rowBody d).entry) t e ∧
      BuildState d ell h D M y origin ((a.val+1)*(2^ell)^d) e.store ∧
      Numbered d 0 (2^ell) (a.val+1) e.store ∧ e.reg (low d 71)=a.val+1 ∧ e.reg (low d 74)=s.reg (low d 74) := by
  obtain ⟨t₁,c₁,ht₁,h₁,hc₁,ha₁,hb₁,hi₁,hn₁,hf₁,hd₁⟩ := rowPrepare_stops d ell h D M y a inp s hs.core ha
  have hbuild₁ : BuildState d ell h D M y origin (a.val*(2^ell)^d) c₁.store :=
    hs.frame hc₁ ((hf₁ 77 (by decide) (by decide) (by decide)).trans hs.index) hd₁
  obtain ⟨t₂,c₂,ht₂,h₂,hb₂,ha₂,hi₂,hf₂,hn₂⟩ := rowLoop_stops d ell h D M hM y a origin inp c₁.store hbuild₁ ha₁ hb₁
    ((hf₁ 71 (by decide) (by decide) (by decide)).trans hi) hi₁ hn₁ hdM hhead hmatrix
  have hpre := h₁.seq h₂
  obtain ⟨t₃,e,ht₃,h₃,hbe,hae,hie,hfe⟩ := rowFinishAfter_stops d ell h D M ((a.val+1)*(2^ell)^d) y a origin inp c₂.store
    hb₂ ha₂ hi₂ (TapeProgram.seq (rowPrepare d) (TapeProgram.countedLoop (pairBody d) (low d 75))) s (t₁+1+t₂) ⟨_,hpre,rfl⟩
  refine ⟨t₃,_,?_,h₃,hbe,hae,hie,?_⟩
  · unfold rowTime
    omega
  · exact hfe.trans (hf₂.trans (hf₁ 74 (by decide) (by decide) (by decide)))








private theorem programPrepare_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (inp : Inputs) (s : TapeStore (80+6*d) 3)
    (hc : Core d ell h D M y s) (hh : s.bufferHead 0=1)
    (hm : TapeArrays.BottomMarked s 0) (hsp : TapeArrays.BottomMarked s 1) :
    ∃ t e,t ≤ d*(8*M+20)+9*M+12 ∧ (programPrepare d).Stops inp (s.toCfg (programPrepare d).entry) t e ∧
      BuildState d ell h D M y s 0 e.store ∧ Numbered d 0 (2^ell) 0 e.store ∧
      e.reg (low d 71)=0 ∧ e.reg (low d 74)=(2^ell)^d := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := SamplerOdometer.initialize_stops (low d 23) (low d 2) (tuple d 0)
    (tuple_unique d 0) inp M s hc.bounded
  have hf₁ (i : Fin 80) (hi : i≠2) : c₁.reg (low d i)=s.reg (low d i) := by
    change c₁.store.reg (low d i)=_
    rw [hs₁]
    exact SamplerOdometer.initializeStore_fresh _ _ _ _ _ ((low_eq_iff d _ _).not.mpr hi) (low_not_tuple d 0 i)
  have htape₁ : FieldConvolution.tapeData c₁.store=FieldConvolution.tapeData s := by rw [hs₁,initialize_payload]
  have h₂ := TapeMacros.clear_stops (low d 71) inp (c₁.reg (low d 71)) c₁.store rfl
  let s₂ := c₁.store.setReg (low d 71) 0
  have hb₂ : ∀ j,s₂.reg j ≤ M := FieldPrograms.setReg_bound _ _ _ _ hb₁ (by omega)
  have h₃ := TapeMacros.clear_stops (low d 77) inp (s₂.reg (low d 77)) s₂ rfl
  let s₃ := s₂.setReg (low d 77) 0
  have hb₃ : ∀ j,s₃.reg j ≤ M := FieldPrograms.setReg_bound _ _ _ _ hb₂ (by omega)
  obtain ⟨t₄,e,ht₄,h₄,hs₄,hb₄⟩ := SamplerEvaluation.copy_stops_bound (low d 70) (low d 74) (low d 2)
    (by simp) (by simp) (by simp) inp M s₃ hb₃
  have h70 : c₁.reg (low d 70)=(2^ell)^d := (hf₁ 70 (by decide)).trans hc.size
  have hreg (i : Fin 80) : e.reg (low d i)=
      if i=2 then 0 else if i=74 then (2^ell)^d else if i=77 then 0 else if i=71 then 0 else c₁.reg (low d i) := by
    change e.store.reg (low d i)=_
    rw [hs₄]
    simp [s₃,s₂,TapeStore.setReg,Function.update,low_eq_iff,h70]
  have hdig (g : Fin 6) (i : Fin d) : e.reg (digit d g i)=c₁.reg (digit d g i) := by
    change e.store.reg (digit d g i)=_
    rw [hs₄]
    simp [s₃,s₂,TapeStore.setReg,Function.update_of_ne (digit_ne_low d g i _)]
  have htape : FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
    rw [hs₄]
    simpa only [s₃,s₂,FieldConvolution.tapeData_setReg] using htape₁
  have hframe (i : Fin 80) (hi : i≠2 ∧ i≠71 ∧ i≠74 ∧ i≠77) : e.reg (low d i)=s.reg (low d i) := by
    rw [hreg]
    simp only [hi.1,hi.2.2.1,hi.2.2.2,hi.2.1,if_false]
    exact hf₁ i hi.1
  have hcore : Core d ell h D M y e.store := by
    apply hc.frame hb₄ _ (tapeData_payload htape) (congrFun (tapeData_head htape) 2)
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> exact hframe _ (by decide)
  have hall := ((h₁.seq h₂).seq h₃).seq h₄
  refine ⟨_,_,?_,hall,?_,?_,?_,?_⟩
  · have h71 := hc.bounded (low d 71)
    have h77 := hc.bounded (low d 77)
    rw [show s₂.reg (low d 77)=s.reg (low d 77) by
      simp only [s₂,TapeStore.setReg,Function.update_of_ne (show low d 77≠low d 71 by simp)]
      exact hf₁ 77 (by decide)]
    rw [hf₁ 71 (by decide)]
    simp only [tuple,List.length_ofFn] at ht₁
    omega
  · have hp := tapeData_payload htape
    have hheads := tapeData_head htape
    refine ⟨hcore,by simp [hreg],?_,?_,hm.of_payload hp,hsp.of_payload hp,
      congrFun hheads 1,hp.roHead,hp.output⟩
    · simpa only [Nat.zero_mul,Nat.add_zero] using (congrFun hheads 0).trans hh
    · intro k hk
      omega
  · have hn : Numbered d 0 (2^ell) 0 c₁.store := by
      rw [hs₁]
      exact numbered_initialize d 0 _ (Nat.one_lt_pow h.ne' (by decide)) s hc.environment.cardinal
    apply hn.frame (by simpa [hreg])
    intro j hj
    obtain ⟨i,rfl|rfl⟩ := (tuple_used d 0 j).mp hj <;> exact hdig _ i
  · simp [hreg]
  · simp [hreg]









private theorem programLoop_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
    (y : Fin ((2^ell)^d) → Bool) (origin : TapeStore (80+6*d) 3)
    (inp : Inputs) (s : TapeStore (80+6*d) 3) (hs : BuildState d ell h D M y origin 0 s)
    (ha : Numbered d 0 (2^ell) 0 s) (hi : s.reg (low d 71)=0) (hn : s.reg (low d 74)=(2^ell)^d)
    (hdM : d*((2^ell)-1) ≤ M) (hhead : 1+(2^ell)^d*(2^ell) ≤ M)
    (hmatrix : (2^ell)^d*(2^ell)^d ≤ M) :
    ∃ t e,t ≤ (2^ell)^d*(rowTime d M ((2^ell)^d)+2)+1 ∧
      (TapeProgram.countedLoop (rowBody d) (low d 74)).Stops inp
        (s.toCfg (TapeProgram.countedLoop (rowBody d) (low d 74)).entry) t e ∧
      BuildState d ell h D M y origin ((2^ell)^d*(2^ell)^d) e.store := by
  let Inv := ProgramLoopInv d ell h D M y origin
  have hbody (n : ℕ) (c : TapeStore (80+6*d) 3) (hcn : c.reg (low d 74)=n+1) (hi : Inv (n+1) c) :
      ∃ t e,t ≤ rowTime d M ((2^ell)^d) ∧ (rowBody d).Stops inp
        ((TapeProgram.decStore (low d 74) c).toCfg (rowBody d).entry) t e ∧ Inv n e.store ∧ e.reg (low d 74)=n := by
    let k := (2^ell)^d-(n+1)
    have hk : k<(2^ell)^d := by dsimp [k]; have := hi.le; omega
    have hkn : (2^ell)^d-n=k+1 := by dsimp [k]; have := hi.le; omega
    let c' := c.setReg (low d 74) n
    have hc' : TapeProgram.decStore (low d 74) c=c' := by simp [TapeProgram.decStore,c',TapeStore.setReg,hcn]
    have hbnd : n ≤ M := by have hh := hi.build.core.bounded (low d 74); rw [hcn] at hh; omega
    have hcore := hi.build.core.setReg 74 (by decide) (by decide) n hbnd
    have hbuild : BuildState d ell h D M y origin (k*(2^ell)^d) c' := by
      apply hi.build.frame hcore
      · simpa [c',TapeStore.setReg,k] using hi.build.index
      · rfl
    obtain ⟨t,e,ht,he,heb,hea,hei,her⟩ := rowBody_stops d ell h D M hM y ⟨k,hk⟩ origin inp c'
      hbuild (hi.aTuple.setReg 74 (by decide) n) (by simpa [c',TapeStore.setReg,k] using hi.aIndex) hdM hhead hmatrix
    refine ⟨t,e,ht,?_,?_,?_⟩
    · simpa only [hc'] using he
    · refine ⟨by have := hi.le; omega,?_,?_,?_⟩
      · simpa only [hkn] using heb
      · simpa only [hkn] using hea
      · simpa only [hkn] using hei
    · rw [her]
      simp [c',TapeStore.setReg]
  have hi : Inv ((2^ell)^d) s := by
    refine ⟨le_rfl,?_,?_,?_⟩
    · simpa using hs
    · simpa using ha
    · simpa using hi
  obtain ⟨t,e,ht,he,hie,_⟩ := loop_stops (rowBody d) (low d 74) inp (rowTime d M ((2^ell)^d)) Inv hbody
    ((2^ell)^d) s hn hi
  exact ⟨t,_,ht,he,by simpa only [Nat.sub_zero] using hie.build⟩



theorem program_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
    (y : Fin ((2^ell)^d) → Bool) (inp : Inputs) (s : TapeStore (80+6*d) 3)
    (hc : Core d ell h D M y s) (hh : s.bufferHead 0=1)
    (hm : TapeArrays.BottomMarked s 0) (hsp : TapeArrays.BottomMarked s 1)
    (hdM : d*((2^ell)-1) ≤ M) (hhead : 1+(2^ell)^d*(2^ell) ≤ M)
    (hmatrix : (2^ell)^d*(2^ell)^d ≤ M) :
    ∃ t e,t ≤ programTime d M ((2^ell)^d) ∧ (program d).Stops inp (s.toCfg (program d).entry) t e ∧
      BuildState d ell h D M y s ((2^ell)^d*(2^ell)^d) e.store := by
  obtain ⟨t₁,c₁,ht₁,h₁,hb₁,ha₁,hi₁,hn₁⟩ := programPrepare_stops d ell h D M y inp s hc hh hm hsp
  obtain ⟨t₂,c₂,ht₂,h₂,hb₂⟩ := programLoop_stops d ell h D M hM y s inp c₁.store hb₁ ha₁ hi₁ hn₁ hdM hhead hmatrix
  have hall := h₁.seq h₂
  exact ⟨t₁+1+t₂,_,by unfold programTime; omega,hall,hb₂⟩




















































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



























































































@[simp] private theorem addressStore_D (d : Store) : (addressStore d).reg 9 = d.reg 41+d.reg 42 := by
  simp [addressStore,sumPost,TapeStore.setReg]
@[simp] private theorem addressStore_C (d : Store) : (addressStore d).reg 10 = d.reg 41+d.reg 43 := by
  simp [addressStore,sumPost,TapeStore.setReg]
@[simp] private theorem addressStore_B (d : Store) : (addressStore d).reg 11 = d.reg 44+d.reg 42 := by
  simp [addressStore,sumPost,TapeStore.setReg]
@[simp] private theorem addressStore_target (d : Store) : (addressStore d).reg 12 = d.reg 45 := by
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






























































































@[simp] private theorem step_done (O : Operations (Fin q)) (s : State q m n) (hd : s.done = true) :
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



















@[simp] private theorem branchZero_code_zero (P : TapeProgram R B L) (Q : TapeProgram R B K) (r : Fin R) (j : Fin L) :
    (branchZero P Q r).code (zeroLabel K j) = (P.code j).relabel (zeroLabel K) := by
  simp [branchZero,zeroLabel,TapeProgram.leftLabel]

@[simp] private theorem branchZero_code_positive (P : TapeProgram R B L) (Q : TapeProgram R B K) (r : Fin R) (j : Fin K) :
    (branchZero P Q r).code (positiveLabel L j) = (Q.code j).relabel (positiveLabel L) := by
  simp [branchZero,positiveLabel,TapeProgram.leftLabel,TapeProgram.rightLabel]

@[simp] private theorem branchZero_code_header (P : TapeProgram R B L) (Q : TapeProgram R B K) (r : Fin R) (j : Fin 2) :
    (branchZero P Q r).code (branchLabel L K j) =
      if j = 0 then .dec r (zeroLabel K P.entry) (branchLabel L K 1)
      else .inc r (positiveLabel L Q.entry) := by
  simp [branchZero,branchLabel,TapeProgram.rightLabel]







































end Branch
















@[simp] private theorem inputBuffer_not (b : Bool) : inputBuffer (!b) = outputBuffer b := by cases b <;> rfl
@[simp] private theorem outputBuffer_not (b : Bool) : outputBuffer (!b) = inputBuffer b := by cases b <;> rfl









































































































































































































































































































































































































































































































































































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






@[simp] private theorem reverse_zero (r : Fin 6 → Fin R) : reverse r 0 = r 1 := by simp [reverse]
@[simp] private theorem reverse_one (r : Fin 6 → Fin R) : reverse r 1 = r 0 := by simp [reverse]
@[simp] private theorem reverse_two (r : Fin 6 → Fin R) : reverse r 2 = r 2 := by simp [reverse, Equiv.swap_apply_def]
@[simp] private theorem reverse_three (r : Fin 6 → Fin R) : reverse r 3 = r 3 := by simp [reverse, Equiv.swap_apply_def]
@[simp] private theorem reverse_four (r : Fin 6 → Fin R) : reverse r 4 = r 4 := by simp [reverse, Equiv.swap_apply_def]
@[simp] private theorem reverse_five (r : Fin 6 → Fin R) : reverse r 5 = r 5 := by simp [reverse, Equiv.swap_apply_def]




























































































































































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

























@[simp] private theorem prefix_zero (O : EncodedGaussian.Operations (Fin q))
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

private theorem cache_type_witness_tester_gram (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
    (y : Fin ((2^ell)^d) → Bool) (inp : Inputs) (s : ExpandingCodes.Computation.TapeStore (80+6*d) 3)
    (hc : ExpandingCodes.Computation.TesterGram.Core d ell h D M y s) (hh : s.bufferHead 0=1)
    (hm : ExpandingCodes.Computation.TapeArrays.BottomMarked s 0) (hsp : ExpandingCodes.Computation.TapeArrays.BottomMarked s 1)
    (hdM : d*((2^ell)-1) ≤ M) (hhead : 1+(2^ell)^d*(2^ell) ≤ M)
    (hmatrix : (2^ell)^d*(2^ell)^d ≤ M) :
    ∃ t e,t ≤ ExpandingCodes.Computation.TesterGram.programTime d M ((2^ell)^d) ∧ (ExpandingCodes.Computation.TesterGram.program d).Stops inp (s.toCfg (ExpandingCodes.Computation.TesterGram.program d).entry) t e ∧
      ExpandingCodes.Computation.TesterGram.BuildState d ell h D M y s ((2^ell)^d*(2^ell)^d) e.store := by
  exact @ExpandingCodes.Computation.TesterGram.program_stops d ell h D M hM y inp s hc hh hm hsp hdM hhead hmatrix


open Lean Elab Command
run_meta do
  let env ← getEnv
  let some target := env.find? `ExpandingCodes.Computation.TesterGram.program_stops | throwError "Missing cache target"
  let candidates := env.constants.toList.filterMap fun (n, ci) =>
    if privateToUserName? n == some `cache_type_witness_tester_gram then some ci else none
  unless candidates.length == 1 do throwError "Missing unique cache type witness"
  unless ← Meta.isDefEq target.type candidates.head!.type do
    throwError "Cache target type differs from audited statement"
  let axes ← collectAxioms `ExpandingCodes.Computation.TesterGram.program_stops
  unless axes.all (fun n => #[`propext, `Classical.choice, `Quot.sound].contains n) do
    throwError "Unexpected target axioms: {axes}"
  IO.FS.writeFile "harness/submission/partition/tester_gram-cache-audit.json" (Json.mkObj [("theorem_name",toJson "ExpandingCodes.Computation.TesterGram.program_stops"),("exact_statement_type",toJson true),("axioms",toJson (axes.map Name.toString))]).pretty
  logInfo m!"Closed helper target exact type and standard axioms only: {axes}"
