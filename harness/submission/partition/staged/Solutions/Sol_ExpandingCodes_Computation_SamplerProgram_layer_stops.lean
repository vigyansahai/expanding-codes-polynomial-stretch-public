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

/-! Inlined whole module: ExpandingCodes.Computation.SamplerTables -/
section FlattenModule46



set_option autoImplicit false
set_option linter.style.haveILetI false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch
namespace SamplerTables








theorem flatFour_val {a b c d : ℕ} (i : Fin a) (j : Fin b) (u : Fin c) (v : Fin d) :
    (flatFour a b c d (((i,j),u),v)).val =
      v.val + d * (u.val + c * (j.val + b*i.val)) := by
  simp [flatFour, finProdFinEquiv]












































































































































































































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

/-! Inlined whole module: ExpandingCodes.Computation.SourceFieldArithmetic -/
section FlattenModule51


set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.SourceFieldArithmetic
open NKtLB FieldPrograms FieldConvolution FieldCertificates
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B L : ℕ}




























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































theorem setOne_stops (x : Fin R) (inp : Inputs) (d : TapeStore R B) :
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














theorem lookupPrepare_bound (r : Fin 8 → Fin R) (s : TapeStore R B)
    (M : ℕ) (hs : ∀ j,s.reg j       ≤       M) : ∀ j,(lookupPrepare r s).reg j       ≤       M := by
  apply setReg_bound
  · exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hs (hs (r 1))) (by omega)
  · omega

/-- Actual 48-label source lookup. The index and original width counters remain
available to the caller; the physical buffer head ends after the selected block. -/
theorem lookup_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
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










theorem fieldLayout_injective (r : Fin 30 → Fin R) (hr : Function.Injective r) :
    Function.Injective (fieldLayout r) := by
  intro i j h
  have hh := congrArg Fin.val (hr h)
  exact Fin.ext hh

theorem additionLayout_injective (r : Fin 30 → Fin R) (hr : Function.Injective r) :
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







theorem addFrom_stops (r : Fin 30 → Fin R) (hr : Function.Injective r)
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







theorem multiplyFrom_stops (r : Fin 30 → Fin R) (hr : Function.Injective r)
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














theorem scaleAdd_stops (src dst tmp : Fin R) (hsd : src≠dst) (hst : src≠tmp) (hdt : dst≠tmp)
    (c : ℕ) (inp : Inputs) (s : TapeStore R B) (htmp : s.reg tmp=0) :
    ∃ e, (scaleAdd src dst tmp c).Stops inp
      (s.toCfg (scaleAdd (B := B) src dst tmp c).entry) (c*(5*s.reg src+6)) e ∧
      e.store=scaleStore src dst tmp c s := by
  induction c generalizing s with
  | zero =>
    refine ⟨s.toCfg ⟨0,by simp [scaleLabels]⟩,?_,?_⟩
    · simp only [Nat.zero_mul]
      exact ⟨TapeProgram.Exec.refl _,rfl⟩
    rw [scaleStore,Nat.zero_mul,Nat.add_zero,setReg_self]
    simpa [htmp] using (setReg_self s tmp).symm
  | succ c ih =>
    obtain ⟨d,hd,hds⟩ := TapeMacros.addPreserving_stops src dst tmp hsd hst hdt inp s
    have hda : d.reg src=s.reg src := by
      change d.store.reg src=_; rw [hds]; simp [TapeStore.setReg,hsd,hst]
    have hdtm : d.reg tmp=0 := by
      change d.store.reg tmp=_; rw [hds]; simp
    obtain ⟨e,he,hes⟩ := ih d.store hdtm
    have hall := hd.seq he
    refine ⟨e.mapPC (TapeProgram.rightLabel 9),?_,?_⟩
    · have htime : s.reg tmp+5*s.reg src+5+1+c*(5*d.store.reg src+6)=
          (c+1)*(5*s.reg src+6) := by
        simp only [TapeCfg.store,hda,htmp]
        ring
      rw [htime] at hall
      exact hall
    · change e.store=_
      rw [hes,hds]
      unfold scaleStore
      simp only [TapeStore.setReg]
      congr 1
      funext j
      by_cases htmpj : j=tmp
      · subst j; simp
      by_cases hdstj : j=dst
      · subst j
        simp [Function.update,hdt,Ne.symm hdt,hsd,hst]
        ring
      · simp [Function.update,htmpj,hdstj]


























theorem formIndex_stops (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (c d j : ℕ) (inp : Inputs) (s : TapeStore R B) :
    ∃ t e, t=formIndexTime r c d j s ∧
      (formIndex r c d j).Stops inp (s.toCfg (formIndex (B := B) r c d j).entry) t e ∧
      e.store=formIndexStore r c d j s := by
  obtain ⟨e₁,h₁,hs₁⟩ := TapeMacros.copy_stops (r 0) (r 2) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp s
  have he₁ (i : Fin 5) : e₁.reg (r i)=if i=4 then 0 else if i=2 then s.reg (r 0) else s.reg (r i) := by
    change e₁.store.reg (r i)=_; rw [hs₁]; simp [reg_layout r hr]
  obtain ⟨e₂,h₂,hs₂⟩ := scaleAdd_stops (r 1) (r 2) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) c inp e₁.store (by simp [he₁])
  have he₂ (i : Fin 5) : e₂.reg (r i)=
      if i=4 then 0 else if i=2 then s.reg (r 0)+c*s.reg (r 1) else s.reg (r i) := by
    change e₂.store.reg (r i)=_; rw [hs₂]
    simp [scaleStore,reg_layout r hr,he₁]
    by_cases h₄ : i=4 <;> by_cases h₂ : i=2 <;> simp_all
  have h₃ := TapeMacros.clear_stops (r 3) inp (e₂.reg (r 3)) e₂.store rfl
  obtain ⟨e₄,h₄,hs₄⟩ := scaleAdd_stops (r 2) (r 3) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) d inp (e₂.store.setReg (r 3) 0)
    (by simp [reg_layout r hr,he₂])
  have he₄ (i : Fin 5) : e₄.reg (r i)=if i=4 then 0 else if i=3 then d*(s.reg (r 0)+c*s.reg (r 1))
      else if i=2 then s.reg (r 0)+c*s.reg (r 1) else s.reg (r i) := by
    change e₄.store.reg (r i)=_; rw [hs₄]
    simp [scaleStore,reg_layout r hr,he₂]
    by_cases h₃ : i=3 <;> by_cases h₂ : i=2 <;> by_cases h₄ : i=4 <;> simp_all
  obtain ⟨e₅,h₅,hs₅⟩ := ParameterPrograms.raise_stops (r 3) j inp e₄.store
  have hall := (((h₁.seq h₂).seq h₃).seq h₄).seq h₅
  refine ⟨_,_,?_,hall,?_⟩
  · simp [TapeCfg.store,he₁,he₂,reg_layout r hr]
    unfold formIndexTime
    omega
  · change e₅.store=_
    rw [hs₅,hs₄,hs₂,hs₁]
    unfold scaleStore formIndexStore
    simp only [TapeStore.setReg]
    congr 1
    funext i
    by_cases h₂ : i=r 2
    · subst i; simp [Function.update,hr.eq_iff]
    by_cases h₃ : i=r 3
    · subst i; simp [Function.update,hr.eq_iff]
    by_cases h₄ : i=r 4
    · subst i; simp [Function.update,hr.eq_iff]
    simp [Function.update,h₂,h₃,h₄]

theorem formIndexTime_bound (r : Fin 5 → Fin R) (c d j M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i      ≤      M) :
    formIndexTime r c d j s      ≤      (32+6*c+6*d*(c+1)+2*j)*(M+1) := by
  have h₀ := hs (r 0); have h₁ := hs (r 1); have h₂ := hs (r 2)
  have h₃ := hs (r 3); have h₄ := hs (r 4)
  have hmid : s.reg (r 0)+c*s.reg (r 1)      ≤      (c+1)*M := by
    have hc := Nat.mul_le_mul_left c h₁
    nlinarith
  have hfirst := Nat.mul_le_mul_left c (show 5*s.reg (r 1)+6      ≤      6*(M+1) by omega)
  have hsecond := Nat.mul_le_mul_left d
    (show 5*(s.reg (r 0)+c*s.reg (r 1))+6      ≤      6*(c+1)*(M+1) by nlinarith)
  unfold formIndexTime
  nlinarith















theorem hornerStep_stops (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (s : TapeStore R B) :
    ∃ t e, t     ≤     hornerTime r s ∧
      (hornerStep r).Stops inp (s.toCfg (hornerStep (B := B) r).entry) t e ∧
      e.store=hornerStore r s := by
  obtain ⟨a,c,ha,hc,hcs⟩ := UnaryArithmetic.multiply_stops (r 1) (r 0) (r 3) (r 4) (r 5)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp s
  have hcv (i : Fin 6) : c.reg (r i)=if i=5 then 0 else if i=4 then 0
      else if i=3 then s.reg (r 1)*s.reg (r 0) else s.reg (r i) := by
    change c.store.reg (r i)=_; rw [hcs]; simp [multiplyStore,reg_layout r hr]
  obtain ⟨d,hd,hds⟩ := TapeMacros.copy_stops (r 3) (r 1) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c.store
  have hdv (i : Fin 6) : d.reg (r i)=if i=4 then 0 else if i=1 then s.reg (r 1)*s.reg (r 0)
      else if i=5 then 0 else if i=3 then s.reg (r 1)*s.reg (r 0) else s.reg (r i) := by
    change d.store.reg (r i)=_; rw [hds]
    simp [reg_layout r hr,hcv]
    by_cases h₁ : i=1 <;> by_cases h₃ : i=3 <;> by_cases h₄ : i=4 <;> by_cases h₅ : i=5 <;> simp_all
  obtain ⟨e,he,hes⟩ := TapeMacros.addPreserving_stops (r 2) (r 1) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d.store
  have hall := (hc.seq hd).seq he
  refine ⟨_,_,?_,hall,?_⟩
  · simp [TapeCfg.store,hcv,hdv]
    unfold hornerTime
    nlinarith
  · change e.store=_
    rw [hes,hds,hcs]
    unfold multiplyStore hornerStore
    simp only [TapeStore.setReg]
    congr 1
    funext i
    by_cases h₁ : i=r 1
    · subst i; simp [Function.update,hr.eq_iff]
    by_cases h₃ : i=r 3
    · subst i; simp [Function.update,hr.eq_iff]
    by_cases h₄ : i=r 4
    · subst i; simp [Function.update,hr.eq_iff]
    by_cases h₅ : i=r 5
    · subst i; simp [Function.update,hr.eq_iff]
    simp [Function.update,h₁,h₃,h₄,h₅]

theorem hornerTime_bound (r : Fin 6 → Fin R) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i     ≤     M) : hornerTime r s     ≤     32*(M+1)^2 := by
  have h₀ := hs (r 0); have h₁ := hs (r 1); have h₂ := hs (r 2)
  have h₃ := hs (r 3); have h₄ := hs (r 4); have h₅ := hs (r 5)
  have hm := Nat.mul_le_mul h₁ h₀
  unfold hornerTime
  nlinarith

theorem hornerStore_bound (r : Fin 6 → Fin R) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i     ≤     M) : ∀ i,(hornerStore r s).reg i     ≤     (M+1)^2 := by
  have hm := Nat.mul_le_mul (hs (r 1)) (hs (r 0))
  unfold hornerStore
  apply FieldPrograms.setReg_bound
  · apply FieldPrograms.setReg_bound
    · apply FieldPrograms.setReg_bound
      · apply FieldPrograms.setReg_bound
        · exact fun i => (hs i).trans (by nlinarith)
        · nlinarith
      · omega
    · omega
  · have h₂ := hs (r 2); nlinarith




theorem hashLayout_injective (r : Fin 8 → Fin R) (hr : Function.Injective r) (t : Fin 3) :
    Function.Injective (hashLayout r t) := by
  fin_cases t <;> intro i j hij <;> fin_cases i <;> fin_cases j <;>
    simp_all [hashLayout,hr.eq_iff]




















theorem hashIndexStore_value (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (i : ℕ) (s : TapeStore R B) :
    (hashIndexStore r i s).reg (r 4)=s.reg (r 3)+s.reg (r 0)*
      (s.reg (r 2)+s.reg (r 0)*(s.reg (r 1)+s.reg (r 0)*i)) := by
  simp [hashIndexStore,hornerStore,hashLayout,reg_layout r hr]
  ring










theorem hashIndex_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (i : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j    ≤    M) :
    ∃ t e, t    ≤    hashIndexTimeBound i M ∧
      (hashIndex r i).Stops inp (s.toCfg (hashIndex (B := B) r i).entry) t e ∧
      e.store=hashIndexStore r i s ∧ ∀ j,e.reg j    ≤    hashEnvelope i M 3 := by
  obtain ⟨e₀,h₀,hs₀⟩ := ParameterPrograms.loadConstant_stops (r 4) i inp s
  have hb₀ : ∀ j,e₀.reg j    ≤    hashEnvelope i M 0 := by
    change ∀ j,e₀.store.reg j    ≤    _
    rw [hs₀]
    exact setReg_bound s _ i _ (fun j => (hs j).trans (by simp [hashEnvelope]; omega)) (by simp [hashEnvelope]; omega)
  obtain ⟨t₁,e₁,ht₁,h₁,hs₁⟩ := hornerStep_stops (hashLayout r 0) (hashLayout_injective r hr 0) inp e₀.store
  have hb₁ : ∀ j,e₁.reg j    ≤    hashEnvelope i M 1 := by
    change ∀ j,e₁.store.reg j    ≤    _
    rw [hs₁]
    exact hornerStore_bound _ (hashEnvelope i M 0) e₀.store hb₀
  have hbt₁ : t₁    ≤    32*hashEnvelope i M 1 := ht₁.trans (hornerTime_bound _ _ _ hb₀)
  obtain ⟨t₂,e₂,ht₂,h₂,hs₂⟩ := hornerStep_stops (hashLayout r 1) (hashLayout_injective r hr 1) inp e₁.store
  have hb₂ : ∀ j,e₂.reg j    ≤    hashEnvelope i M 2 := by
    change ∀ j,e₂.store.reg j    ≤    _
    rw [hs₂]
    exact hornerStore_bound _ (hashEnvelope i M 1) e₁.store hb₁
  have hbt₂ : t₂    ≤    32*hashEnvelope i M 2 := ht₂.trans (hornerTime_bound _ _ _ hb₁)
  obtain ⟨t₃,e₃,ht₃,h₃,hs₃⟩ := hornerStep_stops (hashLayout r 2) (hashLayout_injective r hr 2) inp e₂.store
  have hb₃ : ∀ j,e₃.reg j    ≤    hashEnvelope i M 3 := by
    change ∀ j,e₃.store.reg j    ≤    _
    rw [hs₃]
    exact hornerStore_bound _ (hashEnvelope i M 2) e₂.store hb₂
  have hbt₃ : t₃    ≤    32*hashEnvelope i M 3 := ht₃.trans (hornerTime_bound _ _ _ hb₂)
  have hall := ((h₀.seq h₁).seq h₂).seq h₃
  refine ⟨s.reg (r 4)+2*i+2+1+t₁+1+t₂+1+t₃,_,?_,hall,?_,hb₃⟩
  · have hcounter := hs (r 4)
    unfold hashIndexTimeBound
    omega
  · change e₃.store=_
    rw [hs₃,hs₂,hs₁,hs₀]
    rfl

theorem scaleStore_bound_exact (src dst tmp : Fin R) (c M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i   ≤   M) (hresult : s.reg dst+c*s.reg src   ≤   M) :
    ∀ i,(scaleStore src dst tmp c s).reg i   ≤   M := by
  exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hs hresult) (by omega)




















theorem hashIndexStore_flat (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (i : ℕ) (s : TapeStore R B) :
    hashIndexStore r i s=
      ((((s.setReg (r 4) (s.reg (r 3)+s.reg (r 0)*(s.reg (r 2)+s.reg (r 0)*
        (s.reg (r 1)+s.reg (r 0)*i)))).setReg (r 5) (s.reg (r 0)*(s.reg (r 2)+s.reg (r 0)*
          (s.reg (r 1)+s.reg (r 0)*i)))).setReg (r 6) 0).setReg (r 7) 0) := by
  unfold hashIndexStore hornerStore hashLayout
  simp only [TapeStore.setReg]
  congr 1
  funext x
  by_cases h₄ : x=r 4
  · subst x; simp [Function.update,hr.eq_iff]; ring
  by_cases h₅ : x=r 5
  · subst x; simp [Function.update,hr.eq_iff]; ring
  by_cases h₆ : x=r 6
  · subst x; simp [Function.update,hr.eq_iff]
  by_cases h₇ : x=r 7
  · subst x; simp [Function.update,hr.eq_iff]
  simp [Function.update,h₄,h₅,h₆,h₇]

theorem hashIndexStore_bound_exact (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (i M : ℕ) (s : TapeStore R B) (hs : ∀ x,s.reg x   ≤   M)
    (hresult : s.reg (r 3)+s.reg (r 0)*(s.reg (r 2)+s.reg (r 0)*
      (s.reg (r 1)+s.reg (r 0)*i))   ≤   M) :
    ∀ x,(hashIndexStore r i s).reg x   ≤   M := by
  rw [hashIndexStore_flat r hr]
  exact setReg_bound _ _ 0 M (setReg_bound _ _ 0 M
    (setReg_bound _ _ _ M (setReg_bound _ _ _ M hs hresult) (by omega)) (by omega)) (by omega)























theorem coefficientIndexLayout_injective (r : Fin 12 → Fin R) (hr : Function.Injective r) :
    Function.Injective (coefficientIndexLayout r) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [coefficientIndexLayout,hr.eq_iff]

theorem coefficientReadLayout_injective (r : Fin 12 → Fin R) (hr : Function.Injective r) :
    Function.Injective (coefficientReadLayout r) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [coefficientReadLayout,hr.eq_iff]














theorem coefficientLoad_stops (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (c d j : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i   ≤   M) (hhead : s.bufferHead b   ≤   M) (hm : TapeArrays.BottomMarked s b)
    (hmid : s.reg (r 0)+c*s.reg (r 1)   ≤   M) (hindex : coefficientAddress r c d j s   ≤   M)
    (v : ℕ) (hv : TapeArrays.ThermometerAt s b
      (TapeArrays.entryOffset (coefficientAddress r c d j s) (s.reg (r 1))) (s.reg (r 1)) v) :
    ∃ t e, t   ≤   (112+6*c+6*d*(c+1)+2*j)*(M+1)^2 ∧
      (coefficientLoad r b c d j).Stops inp (s.toCfg (coefficientLoad (B := B) r b c d j).entry) t e ∧
      e.reg (r 11)=v ∧ e.reg (r 0)=s.reg (r 0) ∧ e.reg (r 1)=s.reg (r 1) ∧
      (∀ x,(∀ i,x≠r i) → e.reg x=s.reg x) ∧ (∀ x,e.reg x   ≤   M) ∧
      e.bufferHead=Function.update s.bufferHead b
        (TapeArrays.entryOffset (coefficientAddress r c d j s) (s.reg (r 1))+s.reg (r 1)) ∧
      TapeStore.SamePayload e.store s ∧ TapeArrays.BottomMarked e.store b := by
  have hir := coefficientIndexLayout_injective r hr
  have hrr := coefficientReadLayout_injective r hr
  obtain ⟨u,e₁,hu,h₁,hs₁⟩ := formIndex_stops (coefficientIndexLayout r) hir c d j inp s
  have hv₁ (i : Fin 12) : e₁.reg (r i)=if i=4 then 0 else if i=3 then coefficientAddress r c d j s
      else if i=2 then s.reg (r 0)+c*s.reg (r 1) else s.reg (r i) := by
    change e₁.store.reg (r i)=_
    rw [hs₁]
    simp [formIndexStore,coefficientIndexLayout,reg_layout r hr,coefficientAddress]
  have hb₁ : ∀ x,e₁.reg x   ≤   M := by
    change ∀ x,e₁.store.reg x   ≤   M
    rw [hs₁]
    unfold formIndexStore
    apply setReg_bound
    · apply setReg_bound
      · apply setReg_bound
        · exact hs
        · exact hmid
      · exact hindex
    · omega
  have hp₁ : TapeStore.SamePayload e₁.store s := by rw [hs₁]; exact ⟨rfl,rfl,fun _ _ => rfl⟩
  have hh₁ : e₁.bufferHead b   ≤   M := by change e₁.store.bufferHead b   ≤   M; rw [hs₁]; exact hhead
  have hm₁ : TapeArrays.BottomMarked e₁.store b := hm.of_payload hp₁
  have hidx : e₁.store.reg ((coefficientReadLayout r) 0)=coefficientAddress r c d j s := by change e₁.reg ((coefficientReadLayout r) 0)=_; simp [coefficientReadLayout,hv₁]
  have hwidth : e₁.store.reg ((coefficientReadLayout r) 1)=s.reg (r 1) := by
    change e₁.reg ((coefficientReadLayout r) 1)=_; simp [coefficientReadLayout,hv₁]
  have hblock : TapeArrays.ThermometerAt e₁.store b
      (TapeArrays.entryOffset (e₁.store.reg ((coefficientReadLayout r) 0)) (e₁.store.reg ((coefficientReadLayout r) 1)))
      (e₁.store.reg ((coefficientReadLayout r) 1)) v := by
    rw [hidx,hwidth]
    exact hv.of_payload hp₁
  obtain ⟨w,e₂,hw,h₂,hs₂,hvalue,hidx₂,hwidth₂,hout₂,hb₂,hh₂,hp₂⟩ := lookup_stops
    (coefficientReadLayout r) hrr b inp M e₁.store hb₁ hh₁ hm₁.marked v hblock
  obtain ⟨z,e,hz,he,hes,heb⟩ := copy_stops_bound (r 9) (r 11) (r 10)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M e₂.store hb₂
  have hall := (h₁.seq h₂).seq he
  have hp : TapeStore.SamePayload e.store s := by
    have hh : TapeStore.SamePayload e.store e₂.store := by rw [hes]; exact ⟨rfl,rfl,fun _ _ => rfl⟩
    exact (hh.trans hp₂).trans hp₁
  refine ⟨u+1+w+1+z,_,?_,hall,?_,?_,?_,?_,heb,?_,hp,hm.of_payload hp⟩
  · have hpw : M+1   ≤   (M+1)^2 := by nlinarith
    have hti := formIndexTime_bound (coefficientIndexLayout r) c d j M s hs
    have hti' := hti.trans (Nat.mul_le_mul_left (32+6*c+6*d*(c+1)+2*j) hpw)
    rw [hu] at *
    nlinarith
  · change e.store.reg (r 11)=_
    rw [hes]
    simpa [reg_layout r hr,coefficientReadLayout] using hvalue
  · change e.store.reg (r 0)=_
    rw [hes]
    simp only [reg_layout r hr,show (0:Fin 12)≠10 by decide,show (0:Fin 12)≠11 by decide,if_false]
    have hne : ∀ i : Fin 8,r 0≠coefficientReadLayout r i := by
      intro i; fin_cases i <;> simp [coefficientReadLayout,hr.eq_iff]
    rw [hout₂ (r 0) hne]
    change e₁.reg (r 0)=_
    simp [hv₁]
  · change e.store.reg (r 1)=_
    rw [hes]
    simp only [reg_layout r hr,show (1:Fin 12)≠10 by decide,show (1:Fin 12)≠11 by decide,if_false]
    simpa [coefficientReadLayout,hv₁] using hwidth₂
  · intro x hx
    change e.store.reg x=_
    rw [hes]
    simp only [TapeStore.setReg,Function.update_of_ne (hx 10),Function.update_of_ne (hx 11)]
    have hne : ∀ i : Fin 8,x≠coefficientReadLayout r i := by
      intro i; fin_cases i <;> simp [coefficientReadLayout,hx]
    rw [hout₂ x hne]
    change e₁.store.reg x=_
    rw [hs₁]
    simp [formIndexStore,coefficientIndexLayout,TapeStore.setReg,hx]
  · change e.store.bufferHead=_
    rw [hes]
    change e₂.bufferHead=_
    rw [hh₂,hidx,hwidth]
    change Function.update e₁.store.bufferHead b _=_
    rw [hs₁]
    rfl

theorem hashIndexStore_fresh_write (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (i : ℕ) (s : TapeStore R B) (x : Fin R) (hx : ∀ j : Fin 8,4 ≤ j.val → x≠r j) :
    (hashIndexStore r i s).reg x=s.reg x := by
  rw [hashIndexStore_flat r hr]
  simp [TapeStore.setReg,hx 4 (by decide),hx 5 (by decide),hx 6 (by decide),hx 7 (by decide)]

theorem lookupRegisters_fresh_write (r : Fin 8 → Fin R) (v : ℕ) (s : TapeStore R B)
    (x : Fin R) (hx : ∀ j : Fin 8,2 ≤ j.val → x≠r j) : lookupRegisters r v s x=s.reg x := by
  simp [lookupRegisters,TapeStore.setReg,hx 2 (by decide),hx 3 (by decide),hx 4 (by decide),
    hx 5 (by decide),hx 6 (by decide),hx 7 (by decide)]

















theorem hashedColumn_stops (h r : Fin 8 → Fin R) (hh : Function.Injective h) (hr : Function.Injective r)
    (column tmp : Fin R) (hindex : r 0=h 4)
    (hwidth : ∀ j : Fin 8,4 ≤ j.val → r 1≠h j)
    (hcv : r 6≠column) (hct : r 6≠tmp) (hcoltmp : column≠tmp)
    (hwc : r 1≠column) (hwt : r 1≠tmp)
    (b : Fin B) (i : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ x,s.reg x ≤ M) (hhead : s.bufferHead b ≤ M) (hm : TapeArrays.BottomMarked s b)
    (haddr : hashAddress h i s ≤ M) (v : ℕ) (hcolumn : v+i*s.reg (r 1) ≤ M)
    (hend : TapeArrays.entryOffset (hashAddress h i s) (s.reg (r 1))+s.reg (r 1) ≤ M)
    (hblock : TapeArrays.ThermometerAt s b (TapeArrays.entryOffset (hashAddress h i s) (s.reg (r 1))) (s.reg (r 1)) v) :
    ∃ t e, t ≤ hashedColumnTimeBound i M ∧
      (hashedColumn h r column tmp b i).Stops inp (s.toCfg (hashedColumn (B := B) h r column tmp b i).entry) t e ∧
      e.reg column=i*s.reg (r 1)+v ∧
      (∀ x,(∀ j : Fin 8,4 ≤ j.val → x≠h j) → (∀ j : Fin 8,2 ≤ j.val → x≠r j) →
        x≠column → x≠tmp → e.reg x=s.reg x) ∧
      (∀ x,e.reg x ≤ M) ∧
      e.bufferHead=Function.update s.bufferHead b
        (TapeArrays.entryOffset (hashAddress h i s) (s.reg (r 1))+s.reg (r 1)) ∧
      e.bufferHead b ≤ M ∧ TapeStore.SamePayload e.store s ∧ TapeArrays.BottomMarked e.store b := by
  obtain ⟨a,z₁,ha,h₁,hs₁,hb₁old⟩ := hashIndex_stops h hh i inp M s hs
  have hb₁ : ∀ x,z₁.reg x ≤ M := by
    change ∀ x,z₁.store.reg x ≤ M
    rw [hs₁]
    exact hashIndexStore_bound_exact h hh i M s hs haddr
  have hp₁ : TapeStore.SamePayload z₁.store s := by rw [hs₁]; exact ⟨rfl,rfl,fun _ _ => rfl⟩
  have hh₁ : z₁.bufferHead b ≤ M := by change z₁.store.bufferHead b ≤ M; rw [hs₁]; exact hhead
  have hidx₁ : z₁.store.reg (r 0)=hashAddress h i s := by
    rw [hindex,hs₁]
    exact hashIndexStore_value h hh i s
  have hw₁ : z₁.store.reg (r 1)=s.reg (r 1) := by
    rw [hs₁]
    exact hashIndexStore_fresh_write h hh i s _ hwidth
  have hblock₁ : TapeArrays.ThermometerAt z₁.store b
      (TapeArrays.entryOffset (z₁.store.reg (r 0)) (z₁.store.reg (r 1))) (z₁.store.reg (r 1)) v := by
    rw [hidx₁,hw₁]
    exact hblock.of_payload hp₁
  obtain ⟨w,z₂,hw,h₂,hs₂,hvalue,hidx₂,hwidth₂,hout₂,hb₂,hh₂,hp₂⟩ := lookup_stops r hr b inp M z₁.store
    hb₁ hh₁ (hm.of_payload hp₁).marked v hblock₁
  obtain ⟨u,z₃,hu,h₃,hs₃,hb₃⟩ := copy_stops_bound (r 6) column tmp hcv hct hcoltmp inp M z₂.store hb₂
  have hv₃ : z₃.reg column=v := by
    change z₃.store.reg column=_
    rw [hs₃]
    simpa only [TapeStore.setReg,Function.update_of_ne hcoltmp,Function.update_self] using hvalue
  have hw₃ : z₃.reg (r 1)=s.reg (r 1) := by
    change z₃.store.reg (r 1)=_
    rw [hs₃]
    simp only [TapeStore.setReg,Function.update_of_ne hwt,Function.update_of_ne hwc]
    exact hwidth₂.trans hw₁
  have ht₃ : z₃.reg tmp=0 := by change z₃.store.reg tmp=0; rw [hs₃]; simp
  obtain ⟨e,he,hes⟩ := scaleAdd_stops (r 1) column tmp hwc hwt hcoltmp i inp z₃.store ht₃
  have hall := ((h₁.seq h₂).seq h₃).seq he
  have hp : TapeStore.SamePayload e.store s := by
    have hc : TapeStore.SamePayload e.store z₂.store := by rw [hes,hs₃]; exact ⟨rfl,rfl,fun _ _ => rfl⟩
    exact (hc.trans hp₂).trans hp₁
  have hheads : e.bufferHead=Function.update s.bufferHead b
      (TapeArrays.entryOffset (hashAddress h i s) (s.reg (r 1))+s.reg (r 1)) := by
    change e.store.bufferHead=_
    rw [hes]
    change z₃.store.bufferHead=_
    rw [hs₃]
    change z₂.bufferHead=_
    rw [hh₂,hidx₁,hw₁]
    change Function.update z₁.store.bufferHead b _=_
    rw [hs₁]
    rfl
  refine ⟨a+1+w+1+u+1+i*(5*z₃.store.reg (r 1)+6),_,?_,hall,?_,?_,?_,hheads,?_,hp,hm.of_payload hp⟩
  · have hscale := Nat.mul_le_mul_left i (show 5*s.reg (r 1)+6 ≤ 5*M+6 by have := hs (r 1); omega)
    unfold hashedColumnTimeBound
    change a+1+w+1+u+1+i*(5*z₃.reg (r 1)+6) ≤ _
    rw [hw₃]
    omega
  · change e.store.reg column=_
    rw [hes]
    simp only [scaleStore,TapeStore.setReg,Function.update_of_ne hcoltmp,Function.update_self]
    change z₃.reg column+i*z₃.reg (r 1)=_
    rw [hv₃,hw₃]
    omega
  · intro x hxh hxr hxc hxt
    change e.store.reg x=_
    rw [hes]
    simp only [scaleStore,TapeStore.setReg,Function.update_of_ne hxt,Function.update_of_ne hxc]
    change z₃.store.reg x=_
    rw [hs₃]
    simp only [TapeStore.setReg,Function.update_of_ne hxt,Function.update_of_ne hxc]
    change z₂.reg x=_
    rw [hs₂,lookupRegisters_fresh_write r v z₁.store x hxr]
    change z₁.store.reg x=_
    rw [hs₁]
    exact hashIndexStore_fresh_write h hh i s x hxh
  · change ∀ x,e.store.reg x ≤ M
    rw [hes]
    apply scaleStore_bound_exact _ _ _ _ M z₃.store hb₃
    change z₃.reg column+i*z₃.reg (r 1) ≤ M
    rw [hv₃,hw₃]
    exact hcolumn
  · rw [hheads]
    simpa using hend




























end SamplerEvaluation
end ExpandingCodes.Computation

end FlattenModule52


section FlattenModule53



set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
open scoped BigOperators
namespace SamplerOdometer
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}











































































































































































































































































































































































































































































































































































































































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


































































































end ExpandingCodes.PolynomialStretch

end FlattenModule59

/-! Inlined whole module: ExpandingCodes.Computation.SamplerLayerBounds -/
section FlattenModule60



set_option autoImplicit false

namespace ExpandingCodes.Computation.SamplerLayerBounds
open ExpandingCodes.PolynomialStretch
variable {q d k b : ℕ}

theorem table_end {K : ℕ} (width : ℕ) (i : Fin K) :
    1+(i.val+1)*width ≤ 1+K*width :=
  Nat.add_le_add_left (Nat.mul_le_mul_right width i.isLt) 1

theorem form_middle_lt (r : Fin 2) (i : Fin k) (a : Fin q) :
    a.val+(i.val+k*r.val)*q < 2*k*q := by
  have h := (finProdFinEquiv (finProdFinEquiv (r,i),a)).isLt
  simpa [finProdFinEquiv,Nat.mul_comm] using h

theorem form_index_val (r : Fin 2) (i : Fin k) (a : Fin q) (j : Fin d) :
    (SamplerTables.flatFour 2 k q d (((r,i),a),j)).val =
      j.val+d*(a.val+q*(i.val+k*r.val)) := SamplerTables.flatFour_val _ _ _ _










theorem hash_index_val (i : Fin k) (a u v : Fin q) :
    (SamplerTables.flatFour k q q q (((i,a),u),v)).val =
      v.val+q*(u.val+q*(a.val+q*i.val)) := SamplerTables.flatFour_val _ _ _ _










theorem column_lt (i : Fin k) (u : Fin b) : i.val*b+u.val < k*b := by
  have h := (finProdFinEquiv (i,u)).isLt
  simpa [finProdFinEquiv,Nat.mul_comm,Nat.add_comm] using h

theorem neighbor_cached (O : EncodedGaussian.Operations (Fin q))
    (forms : Fin (2*k*q*d) → Fin q) (hashes : Fin (k*q*q*q) → Fin b)
    (hk : k ≤ q) (i : Fin k) (z : Fin d → Fin q) :
    let alpha : Fin q := ⟨i.val,lt_of_lt_of_le i.isLt hk⟩
    let a := (EncodedSampler.fixed O alpha z).1
    let u := (EncodedSampler.linear O
      (fun j => forms (SamplerTables.flatFour 2 k q d (((0,i),a),j))) z).1
    let v := (EncodedSampler.linear O
      (fun j => forms (SamplerTables.flatFour 2 k q d (((1,i),a),j))) z).1
    EncodedSampler.neighbor O forms hashes i z =
      hashes (SamplerTables.flatFour k q q q (((i,a),u),v)) := by
  simp only [EncodedSampler.neighbor,EncodedSampler.address,dif_pos (lt_of_lt_of_le i.isLt hk)]





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



theorem workspace_injective (r : Fin 31 → Fin R) (hr : Function.Injective r) :
    Function.Injective (workspace r) := by
  intro i j h
  have hh := congrArg Fin.val (hr h)
  exact Fin.ext hh








theorem Environment.frame {r : Fin 31 → Fin R} {ell : ℕ} {m : Fin (2^ell)}
    {s e : TapeStore R B} (h : Environment r ell m s)
    (hf : ∀ i : Fin 31,i=3 ∨ i=19 ∨ i=23 ∨ i=24 → e.reg (r i)=s.reg (r i)) :
    Environment r ell m e := by
  constructor
  · rw [hf 3 (by decide)]; exact h.modulus
  · rw [hf 19 (by decide)]; exact h.length
  · rw [hf 23 (by decide)]; exact h.cardinal
  · rw [hf 24 (by decide)]; exact h.square

theorem Environment.setReg {r : Fin 31 → Fin R} (hr : Function.Injective r)
    {ell : ℕ} {m : Fin (2^ell)} {s : TapeStore R B} (h : Environment r ell m s)
    (j : Fin 31) (n : ℕ) (hj : j≠3 ∧ j≠19 ∧ j≠23 ∧ j≠24) :
    Environment r ell m (s.setReg (r j) n) := by
  apply h.frame
  intro i hi
  rcases hi with rfl|rfl|rfl|rfl <;> simp [reg_layout r hr,hj.1,hj.2.1,hj.2.2.1,hj.2.2.2,Ne.symm]

/-- Caller-friendly preserving copy into an arithmetic temporary. -/
theorem copy_environment (r : Fin 31 → Fin R) (hr : Function.Injective r)
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











theorem term_stops (r : Fin 31 → Fin R) (hr : Function.Injective r)
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























/-- Actual bounded source execution of every fixed-dimensional dot product.
The caller's inputs remain on their individual counters throughout the run. -/
theorem dot_stops (r : Fin 31 → Fin R) (hr : Function.Injective r)
    (ps : List (Fin R × Fin R)) (hp : ∀ p∈ps,(∀ i,p.1≠r i) ∧ (∀ i,p.2≠r i))
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (m c : Fin (2^ell))
    (values : Fin R → Fin (2^ell)) (M : ℕ) (hM : 1             ≤             M)
    (s : TapeStore R B) (hs : ∀ j,s.reg j             ≤             M) (henv : Environment r ell m s)
    (hv : ∀ p∈ps,s.reg p.1=(values p.1).val ∧ s.reg p.2=(values p.2).val)
    (hc : s.reg (r 30)=c.val) :
    ∃ t e, t             ≤             ps.length*(13300*(M+1)^6+1) ∧
      (dot r ps).Stops inp (s.toCfg (dot (B := B) r ps).entry) t e ∧
      e.reg (r 30)=(dotValue ell h m values ps c).val ∧ Environment r ell m e.store ∧
      (∀ j,(∀ i,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j             ≤             M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  induction ps generalizing s with
  | nil =>
    exact ⟨0,s.toCfg ⟨0,by simp [dotLabels]⟩,by simp,TapeProgram.skip_stops inp s,hc,
      henv,fun _ _ => rfl,hs,rfl⟩
  | cons p ps ih =>
    have hps : ∀ a∈ps,(∀ i,a.1≠r i) ∧ (∀ i,a.2≠r i) := fun a ha => hp a (by simp [ha])
    have hvs : ∀ a∈ps,s.reg a.1=(values a.1).val ∧ s.reg a.2=(values a.2).val :=
      fun a ha => hv a (by simp [ha])
    obtain ⟨t,d,ht,hd,hdv,hde,hdo,hdb,hdt⟩ := ih hps s hs henv hvs hc
    have hpp := hp p (by simp)
    have hvp := hv p (by simp)
    obtain ⟨u,e,hu,he,hev,hee,heo,heb,het⟩ := term_stops r hr p.1 p.2 hpp.1 hpp.2
      inp ell h m (values p.1) (values p.2) (dotValue ell h m values ps c) M hM d.store hdb hde
      (by change d.reg p.1=_; rw [hdo p.1 hpp.1]; exact hvp.1)
      (by change d.reg p.2=_; rw [hdo p.2 hpp.2]; exact hvp.2) hdv
    have hall := hd.seq he
    refine ⟨t+1+u,_,?_,hall,hev,hee,?_,heb,het.trans hdt⟩
    · change t+1+u             ≤             (ps.length+1)*(13300*(M+1)^6+1)
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · intro j hj
      exact (heo j hj).trans (hdo j hj)



theorem zeroIndex_value (ell : ℕ) : (BinaryField.zeroIndex ell).val=0 := by
  rw [BinaryField.zeroIndex,BinaryPolynomial.indexEquiv_inverse_value]
  simp [BinaryField.zero]

theorem dotValue_sum (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell))
    (ps : List (Fin R × Fin R)) :
    dotValue ell h (BinaryPolynomial.selectedIndex ell h) values ps (BinaryField.zeroIndex ell)=
      (EncodedTester.sum (BinaryField.indexOperations ell h) (ps.map fun p =>
        ((BinaryField.indexOperations ell h).mul (values p.1) (values p.2),1))).1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [dotValue,List.map_cons,EncodedTester.sum,BinaryField.indexOperations,ih]




/-- Actual source evaluation of the exact canonical encoded sum of products. -/
theorem dotFromZero_stops (r : Fin 31 → Fin R) (hr : Function.Injective r)
    (ps : List (Fin R × Fin R)) (hp : ∀ p∈ps,(∀ i,p.1≠r i) ∧ (∀ i,p.2≠r i))
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell))
    (M : ℕ) (hM : 1             ≤             M) (s : TapeStore R B) (hs : ∀ j,s.reg j             ≤             M)
    (henv : Environment r ell (BinaryPolynomial.selectedIndex ell h) s)
    (hv : ∀ p∈ps,s.reg p.1=(values p.1).val ∧ s.reg p.2=(values p.2).val) :
    ∃ t e, t             ≤             (ps.length+1)*(13320*(M+1)^6) ∧
      (dotFromZero r ps).Stops inp (s.toCfg (dotFromZero (B := B) r ps).entry) t e ∧
      e.reg (r 30)=(EncodedTester.sum (BinaryField.indexOperations ell h) (ps.map fun p =>
        ((BinaryField.indexOperations ell h).mul (values p.1) (values p.2),1))).1.val ∧
      Environment r ell (BinaryPolynomial.selectedIndex ell h) e.store ∧
      (∀ j,(∀ i,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j             ≤             M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  have hclear := TapeMacros.clear_stops (r 30) inp (s.reg (r 30)) s rfl
  have hb : ∀ j,(s.setReg (r 30) 0).reg j             ≤             M := setReg_bound s _ 0 M hs (by omega)
  have he := henv.setReg hr 30 0 (by decide)
  have hv' : ∀ p∈ps,(s.setReg (r 30) 0).reg p.1=(values p.1).val ∧
      (s.setReg (r 30) 0).reg p.2=(values p.2).val := by
    intro p hp'
    simpa [TapeStore.setReg,(hp p hp').1 30,(hp p hp').2 30] using hv p hp'
  obtain ⟨t,e,ht,hstop,hev,henv',hframe,heb,het⟩ := dot_stops r hr ps hp inp ell h
    (BinaryPolynomial.selectedIndex ell h) (BinaryField.zeroIndex ell) values M hM
    (s.setReg (r 30) 0) hb he hv' (by simp [zeroIndex_value])
  have hall := hclear.seq hstop
  refine ⟨s.reg (r 30)+1+1+t,_,?_,hall,?_,henv',?_,heb,het⟩
  · have hp₁ : M+1             ≤             (M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1             ≤             6 by decide)
    have hcounter := hs (r 30)
    have hfactor : 13300*(M+1)^6+1             ≤             13320*(M+1)^6 := by
      have hpos : 1             ≤             (M+1)^6 := by omega
      omega
    have htime := ht.trans (Nat.mul_le_mul_left ps.length hfactor)
    rw [Nat.add_mul,Nat.one_mul]
    omega
  · rw [← dotValue_sum ell h values ps]
    exact hev
  · intro j hj
    exact (hframe j hj).trans (by simp [TapeStore.setReg,hj 30])






theorem linear_stops {d : ℕ} (r : Fin 31 → Fin R) (hr : Function.Injective r)
    (coeff point : Fin d → Fin R) (hc : ∀ j i,coeff j≠r i) (hp : ∀ j i,point j≠r i)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell))
    (M : ℕ) (hM : 1            ≤            M) (s : TapeStore R B) (hs : ∀ i,s.reg i            ≤            M)
    (henv : Environment r ell (selectedIndex ell h) s)
    (hvc : ∀ j,s.reg (coeff j)=(values (coeff j)).val)
    (hvp : ∀ j,s.reg (point j)=(values (point j)).val) :
    ∃ t e, t            ≤            (d+1)*(13320*(M+1)^6) ∧
      (linear r coeff point).Stops inp (s.toCfg (linear (B := B) r coeff point).entry) t e ∧
      e.reg (r 30)=(EncodedSampler.linear (BinaryField.indexOperations ell h)
        (fun j => values (coeff j)) (fun j => values (point j))).1.val ∧
      Environment r ell (selectedIndex ell h) e.store ∧
      (∀ j,(∀ i,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j            ≤            M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  have hlist : ∀ p∈List.ofFn (fun i => (coeff i,point i)),(∀ i,p.1≠r i) ∧ (∀ i,p.2≠r i) := by
    intro p hpm
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hpm
    exact ⟨hc j,hp j⟩
  have hvlist : ∀ p∈List.ofFn (fun i => (coeff i,point i)),
      s.reg p.1=(values p.1).val ∧ s.reg p.2=(values p.2).val := by
    intro p hpm
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hpm
    exact ⟨hvc j,hvp j⟩
  have hrun := dotFromZero_stops r hr _ hlist inp ell h values M hM s hs henv hvlist
  simpa only [linear,List.length_ofFn,List.map_ofFn,Function.comp_def,EncodedSampler.linear] using hrun



theorem Environment.setExternal {r : Fin 31 → Fin R} {ell : ℕ} {m : Fin (2^ell)}
    {s : TapeStore R B} (h : Environment r ell m s) (j : Fin R) (n : ℕ)
    (hj : ∀ i,j≠r i) : Environment r ell m (s.setReg j n) := by
  apply h.frame
  intro i hi
  simp [TapeStore.setReg,Ne.symm (hj i)]



theorem powerWorkspace_injective (r : Fin 32 → Fin R) (hr : Function.Injective r) :
    Function.Injective (powerWorkspace r) := by
  intro i j h
  have hh := congrArg Fin.val (hr h)
  exact Fin.ext hh

theorem powerOutside (r : Fin 32 → Fin R) (hr : Function.Injective r) :
    ∀ i : Fin 31,r 31≠powerWorkspace r i := by
  intro i heq
  change r (31 : Fin 32)=r ⟨i.val,by omega⟩ at heq
  have hh := congrArg (Fin.val : Fin 32 → ℕ) (hr heq)
  have := i.isLt
  simp only [Fin.val_mk] at hh
  omega

theorem add_zeroIndex_right (ell : ℕ) (h : 0<ell) (a : Fin (2^ell)) :
    BinaryField.addIndex ell a (BinaryField.zeroIndex ell)=a := by
  have hi := BinaryField.indexOperations_interpretation ell h
  apply hi.injective
  change BinaryField.elements ell h ((BinaryField.indexOperations ell h).add a
    (BinaryField.indexOperations ell h).zero)=_
  rw [hi.add,hi.zero,add_zero]







theorem powerStep_stops (r : Fin 32 → Fin R) (hr : Function.Injective r)
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











theorem powerCore_stops (r : Fin 32 → Fin R) (hr : Function.Injective r)
    (x : Fin R) (hx : ∀ i,x≠r i) (inp : Inputs) (ell : ℕ) (h : 0<ell)
    (alpha : Fin (2^ell)) (M : ℕ) (hM : 1            ≤            M) (j : ℕ)
    (s : TapeStore R B) (hs : ∀ i,s.reg i            ≤            M)
    (henv : Environment (powerWorkspace r) ell (selectedIndex ell h) s)
    (a : Fin (2^ell)) (ha : s.reg (r 31)=a.val) (hxv : s.reg x=alpha.val) :
    ∃ t e, t            ≤            j*(13400*(M+1)^6+1) ∧
      (powerCore r x j).Stops inp (s.toCfg (powerCore (B := B) r x j).entry) t e ∧
      e.reg (r 31)=((fun z => (BinaryField.indexOperations ell h).mul z alpha)^[j] a).val ∧
      Environment (powerWorkspace r) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → e.reg i=s.reg i) ∧
      (∀ i,e.reg i            ≤            M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  induction j generalizing s a with
  | zero =>
    exact ⟨0,s.toCfg ⟨0,by simp [powerLabels]⟩,by simp,TapeProgram.skip_stops inp s,ha,
      henv,fun _ _ => rfl,hs,rfl⟩
  | succ j ih =>
    obtain ⟨u,d,hu,hd,hdv,hde,hdo,hdb,hdt⟩ := powerStep_stops r hr x hx inp ell h a alpha M hM s hs henv ha hxv
    obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := ih d.store hdb hde
      ((BinaryField.indexOperations ell h).mul a alpha) hdv (by
        change d.reg x=_; rw [hdo x hx]; exact hxv)
    have hall := hd.seq he
    refine ⟨u+1+t,_,?_,hall,?_,hee,?_,heb,het.trans hdt⟩
    · change u+1+t            ≤            (j+1)*(13400*(M+1)^6+1)
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · simpa only [Function.iterate_succ_apply] using hev
    · intro i hi
      exact (heo i hi).trans (hdo i hi)

theorem oneIndex_value (ell : ℕ) (h : 0<ell) : (BinaryField.oneIndex ell).val=1 := by
  rw [BinaryField.oneIndex,indexEquiv_inverse_value]
  rw [Finset.sum_eq_single (⟨0,h⟩ : Fin ell)]
  · simp [BinaryField.one,ZMod.val_one_eq_one_mod]
  · intro i hi hne
    have hiz : i.val≠0 := fun he => hne (Fin.ext he)
    simp [BinaryField.one,hiz]
  · simp

theorem power_iterate (ell : ℕ) (h : 0<ell) (alpha : Fin (2^ell)) (j : ℕ) :
    (fun z => (BinaryField.indexOperations ell h).mul z alpha)^[j] (BinaryField.oneIndex ell)=
      (EncodedTester.power (BinaryField.indexOperations ell h) alpha j).1 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih]; rfl






theorem powerFromOne_stops (r : Fin 32 → Fin R) (hr : Function.Injective r)
    (x : Fin R) (hx : ∀ i,x≠r i) (inp : Inputs) (ell : ℕ) (h : 0<ell)
    (alpha : Fin (2^ell)) (M : ℕ) (hM : 1            ≤            M) (j : ℕ)
    (s : TapeStore R B) (hs : ∀ i,s.reg i            ≤            M)
    (henv : Environment (powerWorkspace r) ell (selectedIndex ell h) s) (hxv : s.reg x=alpha.val) :
    ∃ t e, t            ≤            (j+1)*(13420*(M+1)^6) ∧
      (powerFromOne r x j).Stops inp (s.toCfg (powerFromOne (B := B) r x j).entry) t e ∧
      e.reg (r 31)=(EncodedTester.power (BinaryField.indexOperations ell h) alpha j).1.val ∧
      Environment (powerWorkspace r) ell (selectedIndex ell h) e.store ∧
      (∀ i,(∀ v,i≠r v) → e.reg i=s.reg i) ∧
      (∀ i,e.reg i            ≤            M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨c,hc,hcs⟩ := SourceFieldArithmetic.setOne_stops (r 31) inp s
  have hb : ∀ i,c.reg i            ≤            M := by
    change ∀ i,c.store.reg i            ≤            M
    rw [hcs]
    exact setReg_bound s _ 1 M hs hM
  have he : Environment (powerWorkspace r) ell (selectedIndex ell h) c.store := by
    rw [hcs]
    exact henv.setExternal (r 31) 1 (powerOutside r hr)
  obtain ⟨t,e,ht,hstop,hev,henv',hframe,heb,het⟩ := powerCore_stops r hr x hx inp ell h alpha M hM j
    c.store hb he (BinaryField.oneIndex ell)
    (by rw [hcs]; simp [oneIndex_value ell h])
    (by rw [hcs]; simpa [TapeStore.setReg,hx 31] using hxv)
  have hall := hc.seq hstop
  refine ⟨s.reg (r 31)+3+1+t,_,?_,hall,?_,henv',?_,heb,?_⟩
  · have hp₁ : M+1            ≤            (M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1            ≤            6 by decide)
    have hcounter := hs (r 31)
    have hfactor : 13400*(M+1)^6+1            ≤            13420*(M+1)^6 := by omega
    have htime := ht.trans (Nat.mul_le_mul_left j hfactor)
    rw [Nat.add_mul,Nat.one_mul]
    omega
  · simpa only [power_iterate ell h alpha j] using hev
  · intro i hi
    exact (hframe i hi).trans (by rw [hcs]; simp [TapeStore.setReg,hi 31])
  · simpa only [hcs,FieldConvolution.tapeData_setReg] using het







theorem vectorLayout_injective {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R)
    (hr : Function.Injective r) (j : Fin d) : Function.Injective (vectorLayout r j) := by
  intro u v huv
  have heq : vectorIndex j u=vectorIndex j v := hr huv
  by_cases hu : u.val<11 <;> by_cases hv : v.val<11
  · simp only [vectorIndex,dif_pos hu,dif_pos hv] at heq
    have hvv := congrArg Fin.val (Sum.inl.inj heq)
    exact Fin.ext hvv
  · simp only [vectorIndex,dif_pos hu,dif_neg hv] at heq
    cases heq
  · simp only [vectorIndex,dif_neg hu,dif_pos hv] at heq
    cases heq
  · exact Fin.ext (by have := u.isLt; have := v.isLt; omega)

theorem vectorLayout_coefficient_fresh {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R)
    (hr : Function.Injective r) (j a : Fin d) (haj : a≠j) :
    ∀ i,r (.inr a)≠vectorLayout r j i := by
  intro i heq
  have hi : Sum.inr a=vectorIndex j i := hr heq
  unfold vectorIndex at hi
  split at hi
  · cases hi
  · exact haj (Sum.inr.inj hi)

















theorem vectorLoad_stops {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R) (hr : Function.Injective r)
    (b : Fin B) (c : ℕ) (js : List (Fin d)) (hjs : js.Nodup)
    (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ i,s.reg i           ≤           M)
    (hhead : s.bufferHead b           ≤           M) (hm : TapeArrays.BottomMarked s b)
    (hmid : s.reg (r (.inl 0))+c*s.reg (r (.inl 1))           ≤           M)
    (hindex : ∀ j∈js,vectorAddress r c j s           ≤           M)
    (hend : ∀ j∈js,TapeArrays.entryOffset (vectorAddress r c j s) (s.reg (r (.inl 1)))+s.reg (r (.inl 1))           ≤           M)
    (values : Fin d → ℕ) (hvalues : ∀ j∈js,TapeArrays.ThermometerAt s b
      (TapeArrays.entryOffset (vectorAddress r c j s) (s.reg (r (.inl 1)))) (s.reg (r (.inl 1))) (values j)) :
    ∃ t e, t           ≤           js.length*(vectorTimeBound c d M+1) ∧
      (vectorLoad r b c js).Stops inp (s.toCfg (vectorLoad (B := B) r b c js).entry) t e ∧
      (∀ j∈js,e.reg (r (.inr j))=values j) ∧
      (∀ j,j∉js → e.reg (r (.inr j))=s.reg (r (.inr j))) ∧
      e.reg (r (.inl 0))=s.reg (r (.inl 0)) ∧ e.reg (r (.inl 1))=s.reg (r (.inl 1)) ∧
      (∀ x,(∀ i,x≠r i) → e.reg x=s.reg x) ∧ (∀ x,e.reg x           ≤           M) ∧ e.bufferHead b         ≤         M ∧
      (∀ b',b'≠b → e.bufferHead b'=s.bufferHead b') ∧
      TapeStore.SamePayload e.store s ∧ TapeArrays.BottomMarked e.store b := by
  induction js generalizing s with
  | nil =>
    exact ⟨0,s.toCfg ⟨0,by simp [vectorLabels]⟩,by simp,TapeProgram.skip_stops inp s,
      by simp,fun _ _ => rfl,rfl,rfl,fun _ _ => rfl,hs,hhead,(fun _ _ => rfl),TapeStore.SamePayload.refl s,hm⟩
  | cons j js ih =>
    have hjtail : j∉js := (List.nodup_cons.mp hjs).1
    have htail : js.Nodup := (List.nodup_cons.mp hjs).2
    have haddr (a : Fin d) (z : TapeStore R B) : coefficientAddress (vectorLayout r a) c d a.val z=vectorAddress r c a z := by
      simp [coefficientAddress,vectorAddress,vectorLayout,vectorIndex]
    obtain ⟨u,z,hu,hz,hzv,hza,hzq,hzo,hzb,hzh,hzp,hzm⟩ := coefficientLoad_stops
      (vectorLayout r j) (vectorLayout_injective r hr j) b c d j.val inp M s hs hhead hm hmid
      (by rw [haddr]; exact hindex j (by simp)) (values j)
      (by rw [haddr]; exact hvalues j (by simp))
    have hza' : z.reg (r (.inl 0))=s.reg (r (.inl 0)) := hza
    have hzq' : z.reg (r (.inl 1))=s.reg (r (.inl 1)) := hzq
    have hzv' : z.reg (r (.inr j))=values j := hzv
    have hzhead : z.bufferHead b           ≤           M := by
      rw [hzh]
      simpa [coefficientAddress,vectorAddress,vectorLayout,vectorIndex,Function.comp_def] using hend j (by simp)
    have hmidz : z.store.reg (r (.inl 0))+c*z.store.reg (r (.inl 1))           ≤           M := by
      change z.reg (r (.inl 0))+c*z.reg (r (.inl 1))           ≤           M
      rw [hza',hzq']; exact hmid
    have hindexz : ∀ a∈js,vectorAddress r c a z.store           ≤           M := by
      intro a ha
      simpa [vectorAddress,hza',hzq'] using hindex a (by simp [ha])
    have hendz : ∀ a∈js,TapeArrays.entryOffset (vectorAddress r c a z.store)
        (z.store.reg (r (.inl 1)))+z.store.reg (r (.inl 1))           ≤           M := by
      intro a ha
      simpa [vectorAddress,hza',hzq'] using hend a (by simp [ha])
    have hvaluesz : ∀ a∈js,TapeArrays.ThermometerAt z.store b
        (TapeArrays.entryOffset (vectorAddress r c a z.store) (z.store.reg (r (.inl 1))))
        (z.store.reg (r (.inl 1))) (values a) := by
      intro a ha
      have hh := (hvalues a (by simp [ha])).of_payload hzp
      simpa [vectorAddress,hza',hzq'] using hh
    obtain ⟨t,e,ht,he,hev,hef,hea,heq,heo,heb,heh,heheads,hep,hem⟩ := ih htail z.store hzb hzhead hzm
      hmidz hindexz hendz hvaluesz
    have hall := hz.seq he
    refine ⟨u+1+t,_,?_,hall,?_,?_,hea.trans hza',heq.trans hzq',?_,heb,heh,?_,hep.trans hzp,hem⟩
    · have htj : u           ≤           vectorTimeBound c d M := hu.trans (by
        unfold vectorTimeBound
        apply Nat.mul_le_mul_right
        have hj := j.isLt
        omega)
      change u+1+t           ≤           (js.length+1)*(vectorTimeBound c d M+1)
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl|ha
      · exact (hef _ hjtail).trans hzv'
      · exact hev a ha
    · intro a ha
      have haj : a≠j := fun he => ha (by simp [he])
      have hat : a∉js := fun he => ha (by simp [he])
      exact (hef a hat).trans (hzo (r (.inr a)) (vectorLayout_coefficient_fresh r hr j a haj))
    · intro x hx
      exact (heo x hx).trans (hzo x (fun i => hx (vectorIndex j i)))
    · intro b' hne
      exact (heheads b' hne).trans (by
        change z.bufferHead b'=s.bufferHead b'
        rw [hzh]; simp [hne])




theorem allCoefficients_stops {d : ℕ} (r : Fin 11 ⊕ Fin d → Fin R) (hr : Function.Injective r)
    (b : Fin B) (c : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ i,s.reg i          ≤          M)
    (hhead : s.bufferHead b          ≤          M) (hm : TapeArrays.BottomMarked s b)
    (hmid : s.reg (r (.inl 0))+c*s.reg (r (.inl 1))          ≤          M)
    (hindex : ∀ j,vectorAddress r c j s          ≤          M)
    (hend : ∀ j,TapeArrays.entryOffset (vectorAddress r c j s) (s.reg (r (.inl 1)))+s.reg (r (.inl 1))          ≤          M)
    (values : Fin d → ℕ) (hvalues : ∀ j,TapeArrays.ThermometerAt s b
      (TapeArrays.entryOffset (vectorAddress r c j s) (s.reg (r (.inl 1)))) (s.reg (r (.inl 1))) (values j)) :
    ∃ t e, t          ≤          d*(vectorTimeBound c d M+1) ∧
      (allCoefficients r b c).Stops inp (s.toCfg (allCoefficients (B := B) r b c).entry) t e ∧
      (∀ j,e.reg (r (.inr j))=values j) ∧
      e.reg (r (.inl 0))=s.reg (r (.inl 0)) ∧ e.reg (r (.inl 1))=s.reg (r (.inl 1)) ∧
      (∀ x,(∀ i,x≠r i) → e.reg x=s.reg x) ∧ (∀ x,e.reg x          ≤          M) ∧ e.bufferHead b         ≤         M ∧
      (∀ b',b'≠b → e.bufferHead b'=s.bufferHead b') ∧
      TapeStore.SamePayload e.store s ∧ TapeArrays.BottomMarked e.store b := by
  obtain ⟨t,e,ht,he,hev,hef,hea,heq,heo,heb,heh,heheads,hep,hem⟩ := vectorLoad_stops r hr b c (List.finRange d)
    (List.nodup_finRange d) inp M s hs hhead hm hmid (fun j _ => hindex j) (fun j _ => hend j) values (fun j _ => hvalues j)
  exact ⟨t,e,by simpa using ht,he,fun j => hev j (by simp),hea,heq,heo,heb,heh,heheads,hep,hem⟩






theorem scalarValue_eq (ell : ℕ) (s : TapeStore R B) (i : Fin R) (a : Fin (2^ell))
    (ha : s.reg i=a.val) : scalarValue ell s i=a := by
  apply Fin.ext
  simp [scalarValue,ha,a.isLt]

/-- Typed caller interface for the same actual linear-form source. -/
theorem linear_stops_values {d : ℕ} (r : Fin 31 → Fin R) (hr : Function.Injective r)
    (coeff point : Fin d → Fin R) (hc : ∀ j i,coeff j≠r i) (hp : ∀ j i,point j≠r i)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (a z : Fin d → Fin (2^ell))
    (M : ℕ) (hM : 1         ≤         M) (s : TapeStore R B) (hs : ∀ i,s.reg i         ≤         M)
    (henv : Environment r ell (selectedIndex ell h) s)
    (hvc : ∀ j,s.reg (coeff j)=(a j).val) (hvp : ∀ j,s.reg (point j)=(z j).val) :
    ∃ t e, t         ≤         (d+1)*(13320*(M+1)^6) ∧
      (linear r coeff point).Stops inp (s.toCfg (linear (B := B) r coeff point).entry) t e ∧
      e.reg (r 30)=(EncodedSampler.linear (BinaryField.indexOperations ell h) a z).1.val ∧
      Environment r ell (selectedIndex ell h) e.store ∧
      (∀ j,(∀ i,j≠r i) → e.reg j=s.reg j) ∧
      (∀ j,e.reg j         ≤         M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  have hac : ∀ j,scalarValue ell s (coeff j)=a j := fun j => scalarValue_eq ell s _ _ (hvc j)
  have haz : ∀ j,scalarValue ell s (point j)=z j := fun j => scalarValue_eq ell s _ _ (hvp j)
  obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := linear_stops r hr coeff point hc hp inp ell h
    (scalarValue ell s) M hM s hs henv (by intro j; rw [hac j]; exact hvc j)
    (by intro j; rw [haz j]; exact hvp j)
  refine ⟨t,e,ht,he,?_,hee,heo,heb,het⟩
  simpa only [hac,haz] using hev






theorem powerField_injective {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (hr : Function.Injective r) :
    Function.Injective (powerField r) := by
  intro i j heq
  have hh := Sum.inl.inj (hr heq)
  have hv := congrArg Fin.val hh
  exact Fin.ext hv

theorem powerAlpha_fresh {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (hr : Function.Injective r) :
    ∀ i,r (.inl 32)≠powerField r i := by
  intro i heq
  have hh : (32 : Fin 33)=⟨i.val,by omega⟩ := Sum.inl.inj (hr heq)
  have hv := congrArg Fin.val hh
  change (32 : ℕ)=i.val at hv
  have := i.isLt
  omega

theorem powerCoefficient_fresh {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (hr : Function.Injective r)
    (j : Fin d) : ∀ i,r (.inr j)≠powerField r i := by
  intro i heq
  have hh := hr heq
  cases hh










theorem powerCoefficient_stops {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (hr : Function.Injective r)
    (j : Fin d) (inp : Inputs) (ell : ℕ) (h : 0<ell) (alpha : Fin (2^ell))
    (M : ℕ) (hM : 1         ≤         M) (s : TapeStore R B) (hs : ∀ i,s.reg i         ≤         M)
    (henv : Environment (powerWorkspace (powerField r)) ell (selectedIndex ell h) s)
    (halpha : s.reg (r (.inl 32))=alpha.val) :
    ∃ t e, t         ≤         powerCoefficientTimeBound d M ∧
      (powerCoefficient r j).Stops inp (s.toCfg (powerCoefficient (B := B) r j).entry) t e ∧
      e.reg (r (.inr j))=(EncodedTester.power (BinaryField.indexOperations ell h) alpha j.val).1.val ∧
      Environment (powerWorkspace (powerField r)) ell (selectedIndex ell h) e.store ∧
      e.reg (r (.inl 32))=s.reg (r (.inl 32)) ∧
      (∀ a,a≠j → e.reg (r (.inr a))=s.reg (r (.inr a))) ∧
      (∀ x,(∀ i,x≠r i) → e.reg x=s.reg x) ∧
      (∀ x,e.reg x         ≤         M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  have hrf := powerField_injective r hr
  obtain ⟨t,z,ht,hz,hzv,hze,hzo,hzb,hzt⟩ := powerFromOne_stops (powerField r) hrf
    (r (.inl 32)) (powerAlpha_fresh r hr) inp ell h alpha M hM j.val s hs henv halpha
  obtain ⟨u,e,hu,he,hes,heb⟩ := copy_stops_bound (powerField r 31) (r (.inr j)) (powerField r 2)
    (Ne.symm (powerCoefficient_fresh r hr j 31)) (hrf.ne (by decide)) (powerCoefficient_fresh r hr j 2)
    inp M z.store hzb
  have hall := hz.seq he
  refine ⟨t+1+u,_,?_,hall,?_,?_,?_,?_,?_,heb,?_⟩
  · have hp : M+1         ≤         (M+1)^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1         ≤         6 by decide)
    have hj : j.val+1         ≤         d+1 := by have := j.isLt; omega
    have ht' := ht.trans (Nat.mul_le_mul_right (13420*(M+1)^6) hj)
    have hfac : 13420*(M+1)^6         ≤         13440*(M+1)^6 := by omega
    have ht'' := ht'.trans (Nat.mul_le_mul_left (d+1) hfac)
    have hu' : 1+u         ≤         13440*(M+1)^6 := by omega
    unfold powerCoefficientTimeBound
    calc
      t+1+u         ≤         (d+1)*(13440*(M+1)^6)+13440*(M+1)^6 := by omega
      _=(d+2)*(13440*(M+1)^6) := by ring
  · change e.store.reg (r (.inr j))=_
    rw [hes]
    simpa only [TapeStore.setReg,Function.update_of_ne (powerCoefficient_fresh r hr j 2),Function.update_self] using hzv
  · rw [hes]
    have hf : ∀ i : Fin 31,r (.inr j)≠powerWorkspace (powerField r) i := fun i =>
      powerCoefficient_fresh r hr j ⟨i.val,by omega⟩
    exact (hze.setExternal _ _ hf).setReg (powerWorkspace_injective _ hrf) 2 0 (by decide)
  · change e.store.reg (r (.inl 32))=_
    rw [hes]
    have hcoef : r (.inl 32)≠r (.inr j) := by intro hh; have := hr hh; cases this
    simp only [TapeStore.setReg,Function.update_of_ne (powerAlpha_fresh r hr 2),Function.update_of_ne hcoef]
    exact hzo _ (powerAlpha_fresh r hr)
  · intro a haj
    change e.store.reg (r (.inr a))=_
    rw [hes]
    have hcoef : r (.inr a)≠r (.inr j) := fun hh => haj (Sum.inr.inj (hr hh))
    simp only [TapeStore.setReg,Function.update_of_ne (powerCoefficient_fresh r hr a 2),Function.update_of_ne hcoef]
    exact hzo _ (powerCoefficient_fresh r hr a)
  · intro x hx
    change e.store.reg x=_
    rw [hes]
    have htmp : x≠powerField r 2 := hx (.inl ⟨(2 : Fin 32).val,by omega⟩)
    simp only [TapeStore.setReg,Function.update_of_ne htmp,Function.update_of_ne (hx (.inr j))]
    exact hzo x (fun i => hx (.inl ⟨i.val,by omega⟩))
  · change FieldConvolution.tapeData e.store=_
    rw [hes]
    simpa only [FieldConvolution.tapeData_setReg] using hzt












theorem powerVector_stops {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (hr : Function.Injective r)
    (js : List (Fin d)) (hjs : js.Nodup) (inp : Inputs) (ell : ℕ) (h : 0<ell) (alpha : Fin (2^ell))
    (M : ℕ) (hM : 1         ≤         M) (s : TapeStore R B) (hs : ∀ i,s.reg i         ≤         M)
    (henv : Environment (powerWorkspace (powerField r)) ell (selectedIndex ell h) s)
    (halpha : s.reg (r (.inl 32))=alpha.val) :
    ∃ t e, t         ≤         js.length*(powerCoefficientTimeBound d M+1) ∧
      (powerVector r js).Stops inp (s.toCfg (powerVector (B := B) r js).entry) t e ∧
      (∀ j∈js,e.reg (r (.inr j))=(EncodedTester.power (BinaryField.indexOperations ell h) alpha j.val).1.val) ∧
      (∀ j,j∉js → e.reg (r (.inr j))=s.reg (r (.inr j))) ∧
      Environment (powerWorkspace (powerField r)) ell (selectedIndex ell h) e.store ∧
      e.reg (r (.inl 32))=s.reg (r (.inl 32)) ∧
      (∀ x,(∀ i,x≠r i) → e.reg x=s.reg x) ∧
      (∀ x,e.reg x         ≤         M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  induction js generalizing s with
  | nil =>
    exact ⟨0,s.toCfg ⟨0,by simp [powerVectorLabels]⟩,by simp,TapeProgram.skip_stops inp s,
      by simp,fun _ _ => rfl,henv,rfl,fun _ _ => rfl,hs,rfl⟩
  | cons j js ih =>
    have hjtail := (List.nodup_cons.mp hjs).1
    have htail := (List.nodup_cons.mp hjs).2
    obtain ⟨u,z,hu,hz,hzv,hze,hza,hzf,hzo,hzb,hzt⟩ := powerCoefficient_stops r hr j inp ell h alpha M hM s hs henv halpha
    obtain ⟨t,e,ht,he,hev,hef,hee,hea,heo,heb,het⟩ := ih htail z.store hzb hze (by
      change z.reg (r (.inl 32))=_; rw [hza]; exact halpha)
    have hall := hz.seq he
    refine ⟨u+1+t,_,?_,hall,?_,?_,hee,hea.trans hza,?_,heb,het.trans hzt⟩
    · change u+1+t         ≤         (js.length+1)*(powerCoefficientTimeBound d M+1)
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl|ha
      · exact (hef _ hjtail).trans hzv
      · exact hev a ha
    · intro a ha
      have haj : a≠j := fun he => ha (by simp [he])
      have hat : a∉js := fun he => ha (by simp [he])
      exact (hef a hat).trans (hzf a haj)
    · intro x hx
      exact (heo x hx).trans (hzo x hx)




theorem allPowers_stops {d : ℕ} (r : Fin 33 ⊕ Fin d → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (alpha : Fin (2^ell))
    (M : ℕ) (hM : 1         ≤         M) (s : TapeStore R B) (hs : ∀ i,s.reg i         ≤         M)
    (henv : Environment (powerWorkspace (powerField r)) ell (selectedIndex ell h) s)
    (halpha : s.reg (r (.inl 32))=alpha.val) :
    ∃ t e, t         ≤         d*(powerCoefficientTimeBound d M+1) ∧
      (allPowers r).Stops inp (s.toCfg (allPowers (B := B) r).entry) t e ∧
      (∀ j,e.reg (r (.inr j))=(EncodedTester.power (BinaryField.indexOperations ell h) alpha j.val).1.val) ∧
      Environment (powerWorkspace (powerField r)) ell (selectedIndex ell h) e.store ∧
      e.reg (r (.inl 32))=s.reg (r (.inl 32)) ∧
      (∀ x,(∀ i,x≠r i) → e.reg x=s.reg x) ∧
      (∀ x,e.reg x         ≤         M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨t,e,ht,he,hev,hef,hee,hea,heo,heb,het⟩ := powerVector_stops r hr (List.finRange d) (List.nodup_finRange d)
    inp ell h alpha M hM s hs henv halpha
  exact ⟨t,e,by simpa using ht,he,fun j => hev j (by simp),hee,hea,heo,heb,het⟩














theorem fixedPowerLayout_injective {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R)
    (hr : Function.Injective r) : Function.Injective (fixedPowerLayout r) := by
  intro a b hab
  have hh : fixedPowerIndex a=fixedPowerIndex b := hr hab
  cases a <;> cases b <;> simp_all [fixedPowerIndex]

theorem fixedFieldLayout_injective {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R)
    (hr : Function.Injective r) : Function.Injective (fixedFieldLayout r) :=
  powerWorkspace_injective _ (powerField_injective _ (fixedPowerLayout_injective r hr))

theorem fixedCoeff_fresh {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R)
    (hr : Function.Injective r) : ∀ j i,fixedCoeff r j≠fixedFieldLayout r i := by
  intro j i hij
  have hh := hr hij
  cases hh

theorem fixedPoint_fresh {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R)
    (hr : Function.Injective r) : ∀ j i,fixedPoint r j≠fixedFieldLayout r i := by
  intro j i hij
  have hh := hr hij
  cases hh

theorem fixedPoint_power_fresh {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R)
    (hr : Function.Injective r) : ∀ j i,fixedPoint r j≠fixedPowerLayout r i := by
  intro j i hij
  cases i with
  | inl i =>
    have hh : Sum.inr (Sum.inr j)=Sum.inl i := hr hij
    cases hh
  | inr i =>
    have hh : Sum.inr (Sum.inr j)=Sum.inr (Sum.inl i) := hr hij
    cases Sum.inr.inj hh

theorem power_linear_eq_fixed (ell : ℕ) (h : 0<ell) {d : ℕ} (alpha : Fin (2^ell)) (z : Fin d → Fin (2^ell)) :
    (EncodedSampler.linear (BinaryField.indexOperations ell h)
      (fun j => (EncodedTester.power (BinaryField.indexOperations ell h) alpha j.val).1) z).1=
        (EncodedSampler.fixed (BinaryField.indexOperations ell h) alpha z).1 := by
  have hi := BinaryField.indexOperations_interpretation ell h
  apply hi.injective
  rw [EncodedSampler.linear_decode hi,EncodedSampler.fixed_decode hi]
  simp only [EncodedTester.power_decode hi]











theorem fixed_stops {d : ℕ} (r : Fin 33 ⊕ (Fin d ⊕ Fin d) → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (h : 0<ell) (alpha : Fin (2^ell)) (z : Fin d → Fin (2^ell))
    (M : ℕ) (hM : 1        ≤        M) (s : TapeStore R B) (hs : ∀ i,s.reg i        ≤        M)
    (henv : Environment (fixedFieldLayout r) ell (selectedIndex ell h) s)
    (halpha : s.reg (r (.inl 32))=alpha.val) (hz : ∀ j,s.reg (fixedPoint r j)=(z j).val) :
    ∃ t e, t        ≤        fixedTimeBound d M ∧
      (fixed r).Stops inp (s.toCfg (fixed (B := B) r).entry) t e ∧
      e.reg (r (.inl 30))=(EncodedSampler.fixed (BinaryField.indexOperations ell h) alpha z).1.val ∧
      Environment (fixedFieldLayout r) ell (selectedIndex ell h) e.store ∧
      (∀ j,e.reg (fixedPoint r j)=s.reg (fixedPoint r j)) ∧
      (∀ x,(∀ i,x≠r i) → e.reg x=s.reg x) ∧
      (∀ x,e.reg x        ≤        M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  have hpr := fixedPowerLayout_injective r hr
  have hfr := fixedFieldLayout_injective r hr
  obtain ⟨u,c,hu,hc,hcv,hce,hca,hco,hcb,hct⟩ := allPowers_stops (fixedPowerLayout r) hpr inp ell h alpha M hM s hs henv halpha
  have hpoints : ∀ j,c.reg (fixedPoint r j)=(z j).val := by
    intro j
    rw [hco _ (fixedPoint_power_fresh r hr j)]
    exact hz j
  obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := linear_stops_values (fixedFieldLayout r) hfr
    (fixedCoeff r) (fixedPoint r) (fixedCoeff_fresh r hr) (fixedPoint_fresh r hr) inp ell h
    (fun j => (EncodedTester.power (BinaryField.indexOperations ell h) alpha j.val).1) z
    M hM c.store hcb hce hcv hpoints
  have hall := hc.seq he
  refine ⟨u+1+t,_,?_,hall,?_,hee,?_,?_,heb,het.trans hct⟩
  · unfold fixedTimeBound
    omega
  · rw [power_linear_eq_fixed ell h alpha z] at hev
    exact hev
  · intro j
    exact (heo _ (fixedPoint_fresh r hr j)).trans (hco _ (fixedPoint_power_fresh r hr j))
  · intro x hx
    have hxf : ∀ i : Fin 31,x≠fixedFieldLayout r i := fun i => hx (.inl ⟨i.val,by omega⟩)
    have hxp : ∀ i : Fin 33 ⊕ Fin d,x≠fixedPowerLayout r i := fun i => hx (fixedPowerIndex i)
    exact (heo x hxf).trans (hco x hxp)

theorem tapeData_components {s e : TapeStore R B} (h : FieldConvolution.tapeData e=FieldConvolution.tapeData s) :
    e.roHead=s.roHead ∧ e.output=s.output ∧ e.bufferTape=s.bufferTape ∧ e.bufferHead=s.bufferHead := by
  simpa only [FieldConvolution.tapeData,Prod.mk.injEq] using h

theorem tapeData_payload {s e : TapeStore R B} (h : FieldConvolution.tapeData e=FieldConvolution.tapeData s) :
    TapeStore.SamePayload e s := by
  have hh := tapeData_components h
  exact ⟨hh.1,hh.2.1,fun b k => by rw [hh.2.2.1]⟩












theorem randomLinear_stops {d : ℕ} (v : Fin 11 ⊕ Fin d → Fin R) (hv : Function.Injective v)
    (f : Fin 31 → Fin R) (hf : Function.Injective f) (point : Fin d → Fin R)
    (hcf : ∀ j i,v (.inr j)≠f i) (hpf : ∀ j i,point j≠f i) (hpv : ∀ j i,point j≠v i)
    (haddr : ∀ i,v (.inl 0)≠f i) (hq : f 23=v (.inl 1))
    (hmod : ∀ i,f 3≠v i) (hN : ∀ i,f 19≠v i) (hQ : ∀ i,f 24≠v i)
    (b : Fin B) (c : ℕ) (inp : Inputs) (ell : ℕ) (h : 0<ell) (a z : Fin d → Fin (2^ell))
    (M : ℕ) (hM : 1      ≤      M) (s : TapeStore R B) (hs : ∀ i,s.reg i      ≤      M)
    (henv : Environment f ell (selectedIndex ell h) s) (hz : ∀ j,s.reg (point j)=(z j).val)
    (hhead : s.bufferHead b      ≤      M) (hm : TapeArrays.BottomMarked s b)
    (hmid : s.reg (v (.inl 0))+c*s.reg (v (.inl 1))      ≤      M)
    (hindex : ∀ j,vectorAddress v c j s      ≤      M)
    (hend : ∀ j,TapeArrays.entryOffset (vectorAddress v c j s) (s.reg (v (.inl 1)))+s.reg (v (.inl 1))      ≤      M)
    (hvalues : ∀ j,TapeArrays.ThermometerAt s b
      (TapeArrays.entryOffset (vectorAddress v c j s) (s.reg (v (.inl 1)))) (s.reg (v (.inl 1))) (a j).val) :
    ∃ t e, t      ≤      randomLinearTimeBound c d M ∧
      (randomLinear v f point b c).Stops inp (s.toCfg (randomLinear (B := B) v f point b c).entry) t e ∧
      e.reg (f 30)=(EncodedSampler.linear (BinaryField.indexOperations ell h) a z).1.val ∧
      Environment f ell (selectedIndex ell h) e.store ∧
      e.reg (v (.inl 0))=s.reg (v (.inl 0)) ∧ e.reg (v (.inl 1))=s.reg (v (.inl 1)) ∧
      (∀ j,e.reg (point j)=s.reg (point j)) ∧
      (∀ x,(∀ i,x≠f i) → (∀ i,x≠v i) → e.reg x=s.reg x) ∧
      (∀ x,e.reg x      ≤      M) ∧ e.bufferHead b      ≤      M ∧
      (∀ b',b'≠b → e.bufferHead b'=s.bufferHead b') ∧
      TapeStore.SamePayload e.store s ∧ TapeArrays.BottomMarked e.store b := by
  obtain ⟨u,cfg,hu,hc,hcv,hca,hcq,hco,hcb,hch,hchd,hcp,hcm⟩ := allCoefficients_stops v hv b c inp M s hs
    hhead hm hmid hindex hend (fun j => (a j).val) hvalues
  have hce : Environment f ell (selectedIndex ell h) cfg.store := henv.frame (by
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact hco _ hmod
    · exact hco _ hN
    · simpa only [hq] using hcq
    · exact hco _ hQ)
  have hcz : ∀ j,cfg.reg (point j)=(z j).val := by
    intro j; rw [hco _ (hpv j)]; exact hz j
  obtain ⟨t,e,ht,he,hev,hee,heo,heb,het⟩ := linear_stops_values f hf (fun j => v (.inr j)) point hcf hpf
    inp ell h a z M hM cfg.store hcb hce hcv hcz
  have hall := hc.seq he
  have hh : e.bufferHead=cfg.bufferHead := (tapeData_components het).2.2.2
  have hp : TapeStore.SamePayload e.store s := (tapeData_payload het).trans hcp
  refine ⟨u+1+t,_,?_,hall,hev,hee,?_,?_,?_,?_,heb,?_,?_,hp,hm.of_payload hp⟩
  · unfold randomLinearTimeBound; omega
  · exact (heo _ haddr).trans hca
  · have hqs : e.reg (f 23)=s.reg (f 23) := hee.cardinal.trans henv.cardinal.symm
    simpa only [hq] using hqs
  · intro j; exact (heo _ (hpf j)).trans (hco _ (hpv j))
  · intro x hxf hxv; exact (heo x hxf).trans (hco x hxv)
  · rw [hh]; exact hch
  · intro b' hne; rw [hh]; exact hchd b' hne



namespace Storage



























theorem field_injective (d k : ℕ) : Function.Injective (field d k) := by
  intro i j hij
  have hh := congrArg Fin.val hij
  exact Fin.ext hh







@[simp] theorem point_val (d k : ℕ) (j : Fin d) : (point d k j).val=80+j.val := rfl
@[simp] theorem countdown_val (d k : ℕ) (j : Fin d) : (countdown d k j).val=80+d+j.val := rfl
@[simp] theorem coefficient_val (d k : ℕ) (j : Fin d) : (coefficient d k j).val=80+2*d+j.val := rfl

end Storage

namespace Storage






















end Storage





































































namespace Storage

theorem point_injective (d k : ℕ) : Function.Injective (point d k) := by
  intro i j hij; apply Fin.ext
  have hh := congrArg Fin.val hij
  simp only [point_val] at hh
  omega

theorem coefficient_injective (d k : ℕ) : Function.Injective (coefficient d k) := by
  intro i j hij; apply Fin.ext
  have hh := congrArg Fin.val hij
  simp only [coefficient_val] at hh
  omega

theorem neighbor_injective (d k : ℕ) : Function.Injective (neighbor d k) := by
  intro i j hij; apply Fin.ext
  have hh := congrArg Fin.val hij
  simp only [neighbor_val] at hh
  omega

theorem fixedCommon_cases (d k : ℕ) (i : Fin 33) :
    (fixedCommon d k i).val<32 ∨ (fixedCommon d k i).val=69 := by
  by_cases hi : i.val<32
  · left; simpa [fixedCommon,hi,low] using hi
  · right; simp [fixedCommon,hi,alpha,low]

theorem fixedCommon_lt (d k : ℕ) (i : Fin 33) : (fixedCommon d k i).val<80 := by
  rcases fixedCommon_cases d k i with hi|hi <;> omega

theorem fixedCommon_injective (d k : ℕ) : Function.Injective (fixedCommon d k) := by
  intro a b hab; apply Fin.ext
  have hh := congrArg Fin.val hab
  have ha := a.isLt; have hb := b.isLt
  by_cases h₁ : a.val<32 <;> by_cases h₂ : b.val<32 <;>
    simp [fixedCommon,h₁,h₂,alpha,low] at hh <;> omega

theorem fixedLayout_injective (d k : ℕ) : Function.Injective (fixedLayout d k) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (fixedCommon_injective d k hab)
    | inr b =>
      have hs := fixedCommon_lt d k a
      cases b with
      | inl b =>
        have hh := congrArg Fin.val hab
        change (fixedCommon d k a).val=80+2*d+b.val at hh
        omega
      | inr b =>
        have hh := congrArg Fin.val hab
        change (fixedCommon d k a).val=80+b.val at hh
        omega
  | inr a =>
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have hs := fixedCommon_lt d k b
        have hh := congrArg Fin.val hab
        change 80+2*d+a.val=(fixedCommon d k b).val at hh
        omega
      | inr b =>
        cases b with
        | inl b =>
          congr 1; congr 1
          exact coefficient_injective d k hab
        | inr b =>
          have hh := congrArg Fin.val hab
          change 80+2*d+a.val=80+b.val at hh
          have := b.isLt
          omega
    | inr a =>
      cases b with
      | inl b =>
        have hs := fixedCommon_lt d k b
        have hh := congrArg Fin.val hab
        change 80+a.val=(fixedCommon d k b).val at hh
        omega
      | inr b =>
        cases b with
        | inl b =>
          have hh := congrArg Fin.val hab
          change 80+a.val=80+2*d+b.val at hh
          have := a.isLt
          omega
        | inr b =>
          congr 1; congr 1
          exact point_injective d k hab

theorem formCommon_lt (d k : ℕ) (i : Fin 11) : (formCommon d k i).val<80 := by
  fin_cases i <;> simp [formCommon,address,low]

theorem formCommon_injective (d k : ℕ) : Function.Injective (formCommon d k) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [formCommon,address,(low_injective d k).eq_iff]

theorem formLayout_injective (d k : ℕ) : Function.Injective (formLayout d k) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (formCommon_injective d k hab)
    | inr b =>
      have hs := formCommon_lt d k a
      have hh := congrArg Fin.val hab
      change (formCommon d k a).val=80+2*d+b.val at hh
      omega
  | inr a =>
    cases b with
    | inl b =>
      have hs := formCommon_lt d k b
      have hh := congrArg Fin.val hab
      change 80+2*d+a.val=(formCommon d k b).val at hh
      omega
    | inr b => exact congrArg Sum.inr (coefficient_injective d k hab)

theorem hashLayout_injective (d k : ℕ) : Function.Injective (hashLayout d k) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [hashLayout,address,u,v,hashIndex,(low_injective d k).eq_iff]

theorem hashReadLayout_injective (d k : ℕ) : Function.Injective (hashReadLayout d k) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [hashReadLayout,bucket,hashIndex,(low_injective d k).eq_iff]

theorem coefficient_field_fresh (d k : ℕ) : ∀ j i,coefficient d k j≠field d k i := by
  intro j i hij
  have hh := congrArg Fin.val hij
  have hi := i.isLt
  simp [coefficient,field,low] at hh
  omega

theorem point_field_fresh (d k : ℕ) : ∀ j i,point d k j≠field d k i := by
  intro j i hij
  have hh := congrArg Fin.val hij
  have hi := i.isLt
  simp [point,field,low] at hh
  omega

theorem point_form_fresh (d k : ℕ) : ∀ j i,point d k j≠formLayout d k i := by
  intro j i hij
  cases i with
  | inl i =>
    have hs := formCommon_lt d k i
    have hh := congrArg Fin.val hij
    change 80+j.val=(formCommon d k i).val at hh
    omega
  | inr i =>
    have hh := congrArg Fin.val hij
    change 80+j.val=80+2*d+i.val at hh
    have := j.isLt
    omega

theorem address_field_fresh (d k : ℕ) : ∀ i,address d k≠field d k i := by
  intro i hij
  have hh := congrArg Fin.val hij
  have hi := i.isLt
  simp [address,field,low] at hh
  omega

theorem field_form_fresh (d k : ℕ) (a : Fin 31) (ha : a=3 ∨ a=19 ∨ a=24) :
    ∀ i,field d k a≠formLayout d k i := by
  intro i
  cases i with
  | inl i =>
    rcases ha with rfl|rfl|rfl <;> fin_cases i <;>
      simp [field,formLayout,formCommon,address,low,Fin.ext_iff]
  | inr j => exact Ne.symm (coefficient_field_fresh d k j a)

theorem field_form_q (d k : ℕ) : field d k 23=formLayout d k (.inl 1) := rfl

theorem fixedField_eq (d k : ℕ) : SamplerProgram.fixedFieldLayout (fixedLayout d k)=field d k := by
  funext i
  apply Fin.ext
  have hi : i.val<32 := by have := i.isLt; omega
  simp [SamplerProgram.fixedFieldLayout,SamplerProgram.powerWorkspace,SamplerProgram.powerField,
    SamplerProgram.fixedPowerLayout,SamplerProgram.fixedPowerIndex,fixedLayout,fixedCommon,hi,field,low,
    Function.comp_def]
end Storage




namespace Storage





















@[simp] theorem pointPairs_length (d k : ℕ) : (pointPairs d k).length=d := by simp [pointPairs]












































end Storage














theorem PhysicalTables.of_payload {d k ell b : ℕ}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {s e : TapeStore R 2}
    (h : PhysicalTables d k ell b forms hashes s) (hp : TapeStore.SamePayload e s) :
    PhysicalTables d k ell b forms hashes e := by
  exact ⟨h.formMarked.of_payload hp,h.hashMarked.of_payload hp,
    fun i => (h.formTable i).of_payload hp,fun i => (h.hashTable i).of_payload hp⟩






























theorem LayerFrame.trans {d k : ℕ} {i : Fin k} {s e z : TapeStore (Storage.registers d k) 2}
    (h : LayerFrame d k i s e) (g : LayerFrame d k i e z) : LayerFrame d k i s z :=
  fun x hx => (g x hx).trans (h x hx)

theorem writable_field (d k : ℕ) (i : Fin k) (a : Fin 31) : LayerWritable d k i (Storage.field d k a) := by
  left
  change a.val<32
  have := a.isLt
  omega

theorem writable_low (d k : ℕ) (i : Fin k) (a : Fin 80)
    (ha : a.val<32 ∨ (53  ≤  a.val ∧ a.val<60) ∨ (69  ≤  a.val ∧ a.val<75)) :
    LayerWritable d k i (Storage.low d k a) := by
  unfold LayerWritable
  rcases ha with ha|ha|ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))

theorem writable_coefficient (d k : ℕ) (i : Fin k) (j : Fin d) :
    LayerWritable d k i (Storage.coefficient d k j) := by
  right; right; right; left
  simp only [Storage.coefficient_val]
  have := j.isLt
  omega

theorem writable_fixedCommon (d k : ℕ) (i : Fin k) (j : Fin 33) :
    LayerWritable d k i (Storage.fixedCommon d k j) := by
  rcases Storage.fixedCommon_cases d k j with hj|hj
  · exact Or.inl hj
  · right; right; left; omega

theorem writable_formLayout (d k : ℕ) (i : Fin k) :
    ∀ a,LayerWritable d k i (Storage.formLayout d k a) := by
  intro a
  cases a with
  | inl a =>
    fin_cases a <;> first
      | exact writable_low d k i _ (by decide)
      | simpa only [Storage.formLayout,Storage.formCommon,Storage.address] using writable_low d k i (70 : Fin 80) (by decide)
  | inr j => exact writable_coefficient d k i j

theorem point_not_writable (d k : ℕ) (i : Fin k) (j : Fin d) :
    ¬LayerWritable d k i (Storage.point d k j) := by
  have hj := j.isLt
  simp only [LayerWritable,Storage.point_val,Fin.ext_iff,Storage.neighbor_val]
  omega

theorem countdown_not_writable (d k : ℕ) (i : Fin k) (j : Fin d) :
    ¬LayerWritable d k i (Storage.countdown d k j) := by
  have hj := j.isLt
  simp only [LayerWritable,Storage.countdown_val,Fin.ext_iff,Storage.neighbor_val]
  omega

theorem protected_low_not_writable (d k : ℕ) (i : Fin k) (a : Fin 80)
    (ha : (32  ≤  a.val ∧ a.val<46) ∨ (60  ≤  a.val ∧ a.val<69)) :
    ¬LayerWritable d k i (Storage.low d k a) := by
  simp only [LayerWritable,Storage.low_val,Fin.ext_iff,Storage.neighbor_val]
  omega

theorem other_neighbor_not_writable (d k : ℕ) (i a : Fin k) (ha : a≠i) :
    ¬LayerWritable d k i (Storage.neighbor d k a) := by
  have hn : Storage.neighbor d k a≠Storage.neighbor d k i := (Storage.neighbor_injective d k).ne ha
  simp only [LayerWritable,Storage.neighbor_val,hn,or_false]
  omega

theorem LayerInvariant.transport {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    {i : Fin k} {s e : TapeStore (Storage.registers d k) 2}
    (hs : LayerInvariant d k ell b h forms hashes z M s) (hf : LayerFrame d k i s e)
    (he : Environment (Storage.field d k) ell (selectedIndex ell h) e)
    (hc : ∀ x,e.reg x  ≤  M) (hh : ∀ t,e.bufferHead t  ≤  M) (hp : TapeStore.SamePayload e s) :
    LayerInvariant d k ell b h forms hashes z M e := by
  refine ⟨he,?_,?_,hc,hh,hs.tables.of_payload hp⟩
  · rw [hf _ (protected_low_not_writable d k i 39 (by decide))]
    exact hs.buckets
  · intro j
    rw [hf _ (point_not_writable d k i j)]
    exact hs.points j

theorem LayerFrame.setReg {d k : ℕ} {i : Fin k} (s : TapeStore (Storage.registers d k) 2)
    (r : Fin (Storage.registers d k)) (v : ℕ) (hr : LayerWritable d k i r) :
    LayerFrame d k i s (s.setReg r v) := by
  intro x hx
  have hne : x≠r := by intro heq; subst x; exact hx hr
  simp [TapeStore.setReg,hne]

theorem Storage.low_field_fresh (d k : ℕ) (a : Fin 80) (ha : 31  ≤  a.val) :
    ∀ j,Storage.low d k a≠Storage.field d k j := by
  intro j hij
  have hh := congrArg Fin.val hij
  have hj := j.isLt
  simp [Storage.field,Storage.low] at hh
  omega

theorem copy_phase_stops {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (src dst tmp : Fin (Storage.registers d k))
    (hsd : src≠dst) (hst : src≠tmp) (hdt : dst≠tmp)
    (hd : LayerWritable d k i dst) (ht : LayerWritable d k i tmp)
    (hdf : ∀ j,dst≠Storage.field d k j) (htf : ∀ j,tmp≠Storage.field d k j)
    (inp : Inputs) (s : TapeStore (Storage.registers d k) 2)
    (hs : LayerInvariant d k ell b h forms hashes z M s) :
    ∃ t e,t  ≤  7*M+7 ∧ (TapeMacros.copy src dst tmp).Stops inp
      (s.toCfg (TapeMacros.copy (B := 2) src dst tmp).entry) t e ∧
      LayerInvariant d k ell b h forms hashes z M e.store ∧ LayerFrame d k i s e.store ∧
      TapeStore.SamePayload e.store s ∧
      (∀ x,x≠dst → x≠tmp → e.reg x=s.reg x) ∧ e.reg dst=s.reg src := by
  obtain ⟨t,e,htime,he,hes,heb⟩ := copy_stops_bound src dst tmp hsd hst hdt inp M s hs.counters
  have hframe : LayerFrame d k i s e.store := by
    rw [hes]
    exact (LayerFrame.setReg s dst _ hd).trans (LayerFrame.setReg _ tmp 0 ht)
  have henv : Environment (Storage.field d k) ell (selectedIndex ell h) e.store := by
    rw [hes]
    exact (hs.field.setExternal dst _ hdf).setExternal tmp 0 htf
  have hheads : ∀ a,e.bufferHead a  ≤  M := by
    change ∀ a,e.store.bufferHead a  ≤  M
    rw [hes]
    exact hs.heads
  have hp : TapeStore.SamePayload e.store s := by rw [hes]; exact ⟨rfl,rfl,fun _ _ => rfl⟩
  have hprec : ∀ x,x≠dst → x≠tmp → e.reg x=s.reg x := by
    intro x hxd hxt
    change e.store.reg x=_
    rw [hes]
    simp [TapeStore.setReg,hxd,hxt]
  refine ⟨t,e,htime,he,hs.transport hframe henv heb hheads hp,hframe,hp,hprec,?_⟩
  change e.store.reg dst=_
  rw [hes]
  simp [TapeStore.setReg,hdt]

theorem alpha_phase_stops {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (hk : k  ≤  2^ell) (inp : Inputs) (s : TapeStore (Storage.registers d k) 2)
    (hs : LayerInvariant d k ell b h forms hashes z M s) :
    ∃ t e,t  ≤  M+2*i.val+2 ∧ (ParameterPrograms.loadConstant (Storage.alpha d k) i.val).Stops inp
      (s.toCfg (ParameterPrograms.loadConstant (B := 2) (Storage.alpha d k) i.val).entry) t e ∧
      LayerInvariant d k ell b h forms hashes z M e.store ∧ LayerFrame d k i s e.store ∧
      TapeStore.SamePayload e.store s ∧ e.reg (Storage.alpha d k)=i.val := by
  obtain ⟨e,he,hes⟩ := ParameterPrograms.loadConstant_stops (Storage.alpha d k) i.val inp s
  have hi : i.val  ≤  M := by
    have hq := hs.counters (Storage.field d k 23)
    rw [hs.field.cardinal] at hq
    exact (le_trans (le_of_lt i.isLt) hk).trans hq
  have hframe : LayerFrame d k i s e.store := by
    rw [hes]
    exact LayerFrame.setReg s _ _ (writable_low d k i 69 (by decide))
  have henv : Environment (Storage.field d k) ell (selectedIndex ell h) e.store := by
    rw [hes]
    exact hs.field.setExternal _ _ (Storage.low_field_fresh d k 69 (by decide))
  have hb : ∀ x,e.reg x  ≤  M := by change ∀ x,e.store.reg x  ≤  M; rw [hes]; exact setReg_bound _ _ _ M hs.counters hi
  have hh : ∀ a,e.bufferHead a  ≤  M := by change ∀ a,e.store.bufferHead a  ≤  M; rw [hes]; exact hs.heads
  have hp : TapeStore.SamePayload e.store s := by rw [hes]; exact ⟨rfl,rfl,fun _ _ => rfl⟩
  refine ⟨_,e,?_,he,hs.transport hframe henv hb hh hp,hframe,hp,?_⟩
  · have hα := hs.counters (Storage.alpha d k); omega
  · change e.store.reg (Storage.alpha d k)=_; rw [hes]; simp

theorem fixed_phase_stops {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (alpha : Fin (2^ell)) (inp : Inputs) (hM : 1  ≤  M)
    (s : TapeStore (Storage.registers d k) 2) (hs : LayerInvariant d k ell b h forms hashes z M s)
    (ha : s.reg (Storage.alpha d k)=alpha.val) :
    ∃ t e,t  ≤  fixedTimeBound d M ∧ (fixed (Storage.fixedLayout d k)).Stops inp
      (s.toCfg (fixed (B := 2) (Storage.fixedLayout d k)).entry) t e ∧
      LayerInvariant d k ell b h forms hashes z M e.store ∧ LayerFrame d k i s e.store ∧
      TapeStore.SamePayload e.store s ∧
      e.reg (Storage.field d k 30)=(EncodedSampler.fixed (BinaryField.indexOperations ell h) alpha z).1.val := by
  have henv : Environment (fixedFieldLayout (Storage.fixedLayout d k)) ell (selectedIndex ell h) s := by
    rw [Storage.fixedField_eq]
    exact hs.field
  obtain ⟨t,e,ht,he,hev,hee,hep,hef,heb,het⟩ := fixed_stops (Storage.fixedLayout d k)
    (Storage.fixedLayout_injective d k) inp ell h alpha z M hM s hs.counters henv ha hs.points
  have hframe : LayerFrame d k i s e.store := by
    intro x hx
    by_cases hp : ∃ j,x=Storage.point d k j
    · obtain ⟨j,rfl⟩ := hp
      exact hep j
    · apply hef x
      intro a hxa
      cases a with
      | inl a =>
        apply hx
        rw [hxa]
        exact writable_fixedCommon d k i a
      | inr a =>
        cases a with
        | inl j =>
          apply hx
          rw [hxa]
          exact writable_coefficient d k i j
        | inr j => exact hp ⟨j,hxa⟩
  have hee' : Environment (Storage.field d k) ell (selectedIndex ell h) e.store := by
    simpa only [Storage.fixedField_eq] using hee
  have hh : ∀ a,e.bufferHead a  ≤  M := by
    change ∀ a,e.store.bufferHead a  ≤  M
    rw [(tapeData_components het).2.2.2]
    exact hs.heads
  have hp : TapeStore.SamePayload e.store s := tapeData_payload het
  exact ⟨t,e,ht,he,hs.transport hframe hee' heb hh hp,hframe,hp,hev⟩







theorem Storage.saved_form_fresh (d k : ℕ) (a : Fin 80) (ha : a=71 ∨ a=72) :
    ∀ j,Storage.low d k a≠Storage.formLayout d k j := by
  intro j
  cases j with
  | inl j =>
    rcases ha with rfl|rfl <;> fin_cases j <;>
      simp [Storage.formLayout,Storage.formCommon,Storage.address,Storage.low,Fin.ext_iff]
  | inr j =>
    intro heq
    have hh := congrArg Fin.val heq
    have hi := a.isLt
    simp [Storage.formLayout,Storage.coefficient,Storage.low] at hh
    omega

theorem save_phase_stops {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (dst : Fin 80) (hdst : dst=70 ∨ dst=71 ∨ dst=72)
    (inp : Inputs) (s : TapeStore (Storage.registers d k) 2)
    (hs : LayerInvariant d k ell b h forms hashes z M s) :
    ∃ t e,t ≤ 7*M+7 ∧ (saveField d k dst).Stops inp (s.toCfg (saveField d k dst).entry) t e ∧
      LayerInvariant d k ell b h forms hashes z M e.store ∧ LayerFrame d k i s e.store ∧
      TapeStore.SamePayload e.store s ∧
      (∀ a : Fin 80,a≠dst → a≠53 → e.reg (Storage.low d k a)=s.reg (Storage.low d k a)) ∧
      e.reg (Storage.low d k dst)=s.reg (Storage.field d k 30) := by
  obtain ⟨t,e,ht,he,hee,hef,hep,heprec,hev⟩ := copy_phase_stops i
    (Storage.low d k 30) (Storage.low d k dst) (Storage.low d k 53)
    ((Storage.low_injective d k).ne (by rcases hdst with rfl|rfl|rfl <;> decide))
    ((Storage.low_injective d k).ne (by decide))
    ((Storage.low_injective d k).ne (by rcases hdst with rfl|rfl|rfl <;> decide))
    (writable_low d k i dst (by rcases hdst with rfl|rfl|rfl <;> decide))
    (writable_low d k i 53 (by decide))
    (Storage.low_field_fresh d k dst (by rcases hdst with rfl|rfl|rfl <;> decide))
    (Storage.low_field_fresh d k 53 (by decide)) inp s hs
  exact ⟨t,e,ht,he,hee,hef,hep,
    fun a had hat => heprec _ ((Storage.low_injective d k).ne had) ((Storage.low_injective d k).ne hat),hev⟩

theorem random_phase_stops {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (r : Fin 2) (a : Fin (2^ell)) (inp : Inputs) (hM : 1  ≤  M)
    (s : TapeStore (Storage.registers d k) 2) (hs : LayerInvariant d k ell b h forms hashes z M s)
    (caps : LayerCaps d k ell b M) (ha : s.reg (Storage.address d k)=a.val) :
    ∃ t e,t  ≤  randomLinearTimeBound (i.val+k*r.val) d M ∧
      (randomLinear (Storage.formLayout d k) (Storage.field d k) (Storage.point d k) (0 : Fin 2) (i.val+k*r.val)).Stops inp
        (s.toCfg (randomLinear (B := 2) (Storage.formLayout d k) (Storage.field d k) (Storage.point d k) (0 : Fin 2) (i.val+k*r.val)).entry) t e ∧
      LayerInvariant d k ell b h forms hashes z M e.store ∧ LayerFrame d k i s e.store ∧
      TapeStore.SamePayload e.store s ∧
      e.reg (Storage.address d k)=s.reg (Storage.address d k) ∧
      e.reg (Storage.u d k)=s.reg (Storage.u d k) ∧
      e.reg (Storage.field d k 30)=(EncodedSampler.linear (BinaryField.indexOperations ell h) (formSlice forms r i a) z).1.val := by
  have hsa : s.reg (Storage.formLayout d k (.inl 0))=a.val := ha
  have hsq : s.reg (Storage.formLayout d k (.inl 1))=2^ell := hs.field.cardinal
  have hflat (j : Fin d) : vectorAddress (Storage.formLayout d k) (i.val+k*r.val) j s=
      (SamplerTables.flatFour 2 k (2^ell) d (((r,i),a),j)).val := by
    rw [SamplerLayerBounds.form_index_val]
    unfold vectorAddress
    rw [hsa,hsq]
    ring
  have hN : 2*k*(2^ell)*d  ≤  M := by
    have hmul := Nat.le_mul_of_pos_right (2*k*(2^ell)*d) (Nat.two_pow_pos ell)
    have hbound := caps.formHead
    omega
  have hmid : s.reg (Storage.formLayout d k (.inl 0))+(i.val+k*r.val)*s.reg (Storage.formLayout d k (.inl 1))  ≤  M := by
    rw [hsa,hsq]
    exact (SamplerLayerBounds.form_middle_lt r i a).le.trans caps.middle
  have hindex : ∀ j,vectorAddress (Storage.formLayout d k) (i.val+k*r.val) j s  ≤  M := by
    intro j; rw [hflat]
    exact (SamplerTables.flatFour 2 k (2^ell) d (((r,i),a),j)).isLt.le.trans hN
  have hend : ∀ j,TapeArrays.entryOffset (vectorAddress (Storage.formLayout d k) (i.val+k*r.val) j s)
      (s.reg (Storage.formLayout d k (.inl 1)))+s.reg (Storage.formLayout d k (.inl 1))  ≤  M := by
    intro j
    rw [hflat,hsq]
    have hb := (SamplerLayerBounds.table_end (2^ell) (SamplerTables.flatFour 2 k (2^ell) d (((r,i),a),j))).trans caps.formHead
    unfold TapeArrays.entryOffset
    nlinarith
  have hvalues : ∀ j,TapeArrays.ThermometerAt s 0
      (TapeArrays.entryOffset (vectorAddress (Storage.formLayout d k) (i.val+k*r.val) j s) (s.reg (Storage.formLayout d k (.inl 1))))
      (s.reg (Storage.formLayout d k (.inl 1))) (formSlice forms r i a j).val := by
    intro j; rw [hflat,hsq]
    exact hs.tables.formTable _
  obtain ⟨t,e,ht,he,hev,hee,hea,heq,hepoints,heframe,heb,hehead,heheads,hep,hem⟩ := randomLinear_stops
    (Storage.formLayout d k) (Storage.formLayout_injective d k) (Storage.field d k) (Storage.field_injective d k)
    (Storage.point d k) (Storage.coefficient_field_fresh d k) (Storage.point_field_fresh d k)
    (Storage.point_form_fresh d k) (Storage.address_field_fresh d k) (Storage.field_form_q d k)
    (Storage.field_form_fresh d k 3 (by decide)) (Storage.field_form_fresh d k 19 (by decide))
    (Storage.field_form_fresh d k 24 (by decide)) 0 (i.val+k*r.val) inp ell h (formSlice forms r i a) z
    M hM s hs.counters hs.field hs.points (hs.heads 0) hs.tables.formMarked hmid hindex hend hvalues
  have hframe : LayerFrame d k i s e.store := by
    intro x hx
    apply heframe x
    · intro j hxj
      apply hx
      rw [hxj]
      exact writable_field d k i j
    · intro j hxj
      apply hx
      rw [hxj]
      exact writable_formLayout d k i j
  have hheads : ∀ a,e.bufferHead a  ≤  M := by
    intro a
    by_cases ha : a=0
    · subst a; exact hehead
    · rw [heheads a ha]
      exact hs.heads a
  have hU : e.reg (Storage.u d k)=s.reg (Storage.u d k) :=
    heframe _ (Storage.low_field_fresh d k 71 (by decide)) (Storage.saved_form_fresh d k 71 (Or.inl rfl))
  exact ⟨t,e,ht,he,hs.transport hframe hee heb hheads hep,hframe,hep,hea,hU,hev⟩



theorem Storage.low_ne_neighbor (d k : ℕ) (a : Fin 80) (i : Fin k) :
    Storage.low d k a≠Storage.neighbor d k i := by
  intro heq
  have hh := congrArg Fin.val heq
  have ha := a.isLt
  simp only [Storage.low_val,Storage.neighbor_val] at hh
  omega

theorem Storage.hash_scratch_fresh (d k : ℕ) (x : Fin (Storage.registers d k)) (hx : x.val<53) :
    ∀ j : Fin 8,4 ≤ j.val → x≠Storage.hashLayout d k j := by
  intro j hj heq
  have hh := congrArg Fin.val heq
  fin_cases j <;> simp [Storage.hashLayout,Storage.address,Storage.u,Storage.v,Storage.hashIndex,Storage.low] at hh hj <;> omega

theorem Storage.read_scratch_fresh (d k : ℕ) (x : Fin (Storage.registers d k)) (hx : x.val<53) :
    ∀ j : Fin 8,2 ≤ j.val → x≠Storage.hashReadLayout d k j := by
  intro j hj heq
  have hh := congrArg Fin.val heq
  fin_cases j <;> simp [Storage.hashReadLayout,Storage.hashIndex,Storage.bucket,Storage.low] at hh hj <;> omega

theorem writable_hashScratch (d k : ℕ) (i : Fin k) (j : Fin 8) (hj : 4 ≤ j.val) :
    LayerWritable d k i (Storage.hashLayout d k j) := by
  fin_cases j <;> first | omega | exact writable_low d k i _ (by decide)

theorem writable_readScratch (d k : ℕ) (i : Fin k) (j : Fin 8) (hj : 2 ≤ j.val) :
    LayerWritable d k i (Storage.hashReadLayout d k j) := by
  fin_cases j <;> norm_num at hj <;> exact writable_low d k i _ (by decide)

theorem writable_neighbor (d k : ℕ) (i : Fin k) : LayerWritable d k i (Storage.neighbor d k i) :=
  Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem hash_phase_stops {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (a u v : Fin (2^ell)) (inp : Inputs) (hb : 0<b)
    (s : TapeStore (Storage.registers d k) 2) (hs : LayerInvariant d k ell b h forms hashes z M s)
    (caps : LayerCaps d k ell b M)
    (ha : s.reg (Storage.address d k)=a.val) (hu : s.reg (Storage.u d k)=u.val) (hv : s.reg (Storage.v d k)=v.val) :
    let index := SamplerTables.flatFour k (2^ell) (2^ell) (2^ell) (((i,a),u),v)
    ∃ t e,t ≤ hashedColumnTimeBound i.val M ∧
      (hashedColumn (Storage.hashLayout d k) (Storage.hashReadLayout d k) (Storage.neighbor d k i)
        (Storage.low d k 53) (1 : Fin 2) i.val).Stops inp
        (s.toCfg (hashedColumn (B := 2) (Storage.hashLayout d k) (Storage.hashReadLayout d k) (Storage.neighbor d k i)
          (Storage.low d k 53) (1 : Fin 2) i.val).entry) t e ∧
      LayerInvariant d k ell b h forms hashes z M e.store ∧ LayerFrame d k i s e.store ∧
      TapeStore.SamePayload e.store s ∧ e.reg (Storage.neighbor d k i)=i.val*b+(hashes index).val := by
  dsimp only
  let index := SamplerTables.flatFour k (2^ell) (2^ell) (2^ell) (((i,a),u),v)
  have hidx : hashAddress (Storage.hashLayout d k) i.val s=index.val := by
    rw [SamplerLayerBounds.hash_index_val]
    unfold hashAddress
    change s.reg (Storage.v d k)+s.reg (Storage.field d k 23)*
      (s.reg (Storage.u d k)+s.reg (Storage.field d k 23)*(s.reg (Storage.address d k)+s.reg (Storage.field d k 23)*i.val))=_
    rw [hs.field.cardinal,ha,hu,hv]
  have hB : s.reg (Storage.hashReadLayout d k 1)=b := hs.buckets
  have hN : k*(2^ell)*(2^ell)*(2^ell) ≤ M := by
    have hmul := Nat.le_mul_of_pos_right (k*(2^ell)*(2^ell)*(2^ell)) hb
    have hbound := caps.hashHead
    omega
  have haddr : hashAddress (Storage.hashLayout d k) i.val s ≤ M := by
    rw [hidx]; exact index.isLt.le.trans hN
  have hcolumn : (hashes index).val+i.val*s.reg (Storage.hashReadLayout d k 1) ≤ M := by
    rw [hB]
    simpa [Nat.add_comm] using (SamplerLayerBounds.column_lt i (hashes index)).le.trans caps.columns
  have hend : TapeArrays.entryOffset (hashAddress (Storage.hashLayout d k) i.val s)
      (s.reg (Storage.hashReadLayout d k 1))+s.reg (Storage.hashReadLayout d k 1) ≤ M := by
    rw [hidx,hB]
    have hend := (SamplerLayerBounds.table_end b index).trans caps.hashHead
    unfold TapeArrays.entryOffset
    nlinarith
  have hblock : TapeArrays.ThermometerAt s 1
      (TapeArrays.entryOffset (hashAddress (Storage.hashLayout d k) i.val s) (s.reg (Storage.hashReadLayout d k 1)))
      (s.reg (Storage.hashReadLayout d k 1)) (hashes index).val := by
    rw [hidx,hB]
    exact hs.tables.hashTable index
  obtain ⟨t,e,ht,he,hev,hef,hec,heheads,hehead,hep,hem⟩ := hashedColumn_stops
    (Storage.hashLayout d k) (Storage.hashReadLayout d k) (Storage.hashLayout_injective d k) (Storage.hashReadLayout_injective d k)
    (Storage.neighbor d k i) (Storage.low d k 53) rfl
    (Storage.hash_scratch_fresh d k (Storage.low d k 39) (by change (39 : ℕ)<53; decide))
    (Storage.low_ne_neighbor d k 74 i)
    ((Storage.low_injective d k).ne (by decide : (74 : Fin 80)≠53))
    (Ne.symm (Storage.low_ne_neighbor d k 53 i)) (Storage.low_ne_neighbor d k 39 i)
    ((Storage.low_injective d k).ne (by decide : (39 : Fin 80)≠53))
    1 i.val inp M s hs.counters (hs.heads 1) hs.tables.hashMarked haddr (hashes index).val hcolumn hend hblock
  have hframe : LayerFrame d k i s e.store := by
    intro x hx
    apply hef x
    · intro j hj hxj
      apply hx; rw [hxj]; exact writable_hashScratch d k i j hj
    · intro j hj hxj
      apply hx; rw [hxj]; exact writable_readScratch d k i j hj
    · intro hxj; apply hx; rw [hxj]; exact writable_neighbor d k i
    · intro hxj; apply hx; rw [hxj]; exact writable_low d k i 53 (by decide)
  have hfield (j : Fin 31) : e.reg (Storage.field d k j)=s.reg (Storage.field d k j) := by
    have hj : (Storage.field d k j).val<53 := by change j.val<53; have := j.isLt; omega
    exact hef _ (Storage.hash_scratch_fresh d k _ hj) (Storage.read_scratch_fresh d k _ hj)
      (Storage.low_ne_neighbor d k ⟨j.val,by have := j.isLt; omega⟩ i)
      (Ne.symm (Storage.low_field_fresh d k 53 (by decide) j))
  have hee : Environment (Storage.field d k) ell (selectedIndex ell h) e.store := hs.field.frame (fun j _ => hfield j)
  have hh : ∀ j,e.bufferHead j ≤ M := by
    intro j
    by_cases hj : j=1
    · subst j; exact hehead
    · rw [heheads]
      simpa [hj] using hs.heads j
  rw [hB] at hev
  exact ⟨t,e,ht,he,hs.transport hframe hee hec hh hep,hframe,hep,hev⟩



theorem layer_stops {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (hk : k≤2^ell) (hb : 0<b) (hM : 1≤M) (caps : LayerCaps d k ell b M)
    (inp : Inputs) (s : TapeStore (Storage.registers d k) 2)
    (hs : LayerInvariant d k ell b h forms hashes z M s) :
    ∃ t e,t≤layerTimeBound d k i M ∧
      (layer d k i).Stops inp (s.toCfg (layer d k i).entry) t e ∧
      LayerInvariant d k ell b h forms hashes z M e.store ∧ TapeStore.SamePayload e.store s ∧
      e.reg (Storage.neighbor d k i)=i.val*b+
        (EncodedSampler.neighbor (BinaryField.indexOperations ell h) forms hashes i z).val ∧
      (∀ j,e.reg (Storage.point d k j)=s.reg (Storage.point d k j)) ∧
      (∀ j,e.reg (Storage.countdown d k j)=s.reg (Storage.countdown d k j)) ∧
      (∀ a : Fin 80,(32≤a.val ∧ a.val<46) ∨ (60≤a.val ∧ a.val<69) →
        e.reg (Storage.low d k a)=s.reg (Storage.low d k a)) ∧
      e.output=s.output ∧
      (∀ a : Fin k,a≠i → e.reg (Storage.neighbor d k a)=s.reg (Storage.neighbor d k a)) ∧
      LayerFrame d k i s e.store := by
  let alpha : Fin (2^ell) := ⟨i.val,lt_of_lt_of_le i.isLt hk⟩
  let a := (EncodedSampler.fixed (BinaryField.indexOperations ell h) alpha z).1
  let u := (EncodedSampler.linear (BinaryField.indexOperations ell h) (formSlice forms 0 i a) z).1
  let v := (EncodedSampler.linear (BinaryField.indexOperations ell h) (formSlice forms 1 i a) z).1
  obtain ⟨t₁,c₁,ht₁,h₁,hi₁,hf₁,hp₁,hα₁⟩ := alpha_phase_stops i hk inp s hs
  obtain ⟨t₂,c₂,ht₂,h₂,hi₂,hf₂,hp₂,ha₂⟩ := fixed_phase_stops i alpha inp hM c₁.store hi₁ hα₁
  obtain ⟨t₃,c₃,ht₃,h₃,hi₃,hf₃,hp₃,hcf₃,hv₃⟩ := save_phase_stops i 70 (Or.inl rfl) inp c₂.store hi₂
  have ha₃ : c₃.reg (Storage.address d k)=a.val := hv₃.trans ha₂
  obtain ⟨t₄,c₄,ht₄,h₄,hi₄,hf₄,hp₄,hca₄,hcu₄,hu₄⟩ := random_phase_stops i 0 a inp hM c₃.store hi₃ caps ha₃
  have ha₄ : c₄.reg (Storage.address d k)=a.val := hca₄.trans ha₃
  obtain ⟨t₅,c₅,ht₅,h₅,hi₅,hf₅,hp₅,hcf₅,hv₅⟩ := save_phase_stops i 71 (Or.inr (Or.inl rfl)) inp c₄.store hi₄
  have hu₅ : c₅.reg (Storage.u d k)=u.val := hv₅.trans hu₄
  have ha₅ : c₅.reg (Storage.address d k)=a.val := (hcf₅ 70 (by decide) (by decide)).trans ha₄
  obtain ⟨t₆,c₆,ht₆,h₆,hi₆,hf₆,hp₆,hca₆,hcu₆,hv₆⟩ := random_phase_stops i 1 a inp hM c₅.store hi₅ caps ha₅
  have ha₆ : c₆.reg (Storage.address d k)=a.val := hca₆.trans ha₅
  have hu₆ : c₆.reg (Storage.u d k)=u.val := hcu₆.trans hu₅
  obtain ⟨t₇,c₇,ht₇,h₇,hi₇,hf₇,hp₇,hcf₇,hv₇⟩ := save_phase_stops i 72 (Or.inr (Or.inr rfl)) inp c₆.store hi₆
  have ha₇ : c₇.reg (Storage.address d k)=a.val := (hcf₇ 70 (by decide) (by decide)).trans ha₆
  have hu₇ : c₇.reg (Storage.u d k)=u.val := (hcf₇ 71 (by decide) (by decide)).trans hu₆
  have hv₇' : c₇.reg (Storage.v d k)=v.val := hv₇.trans hv₆
  obtain ⟨t₈,c₈,ht₈,h₈,hi₈,hf₈,hp₈,hv₈⟩ := hash_phase_stops i a u v inp hb c₇.store hi₇ caps ha₇ hu₇ hv₇'
  have hall := ((((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆).seq h₇).seq h₈
  have hzero : i.val+k*(0 : Fin 2).val=i.val := by change i.val+k*0=i.val; omega
  have hone : i.val+k*(1 : Fin 2).val=i.val+k := by change i.val+k*1=i.val+k; omega
  rw [hzero,hone] at hall
  rw [hzero] at ht₄
  rw [hone] at ht₆
  have hframe : LayerFrame d k i s c₈.store := ((((((hf₁.trans hf₂).trans hf₃).trans hf₄).trans hf₅).trans hf₆).trans hf₇).trans hf₈
  have hpay : TapeStore.SamePayload c₈.store s := hp₈.trans (hp₇.trans (hp₆.trans (hp₅.trans (hp₄.trans (hp₃.trans (hp₂.trans hp₁))))))
  have hi : i.val<2^ell := lt_of_lt_of_le i.isLt hk
  have hneighbor : EncodedSampler.neighbor (BinaryField.indexOperations ell h) forms hashes i z=
      hashes (SamplerTables.flatFour k (2^ell) (2^ell) (2^ell) (((i,a),u),v)) := by
    exact SamplerLayerBounds.neighbor_cached (BinaryField.indexOperations ell h) forms hashes hk i z
  have hresult : c₈.reg (Storage.neighbor d k i)=i.val*b+
      (EncodedSampler.neighbor (BinaryField.indexOperations ell h) forms hashes i z).val := by
    rw [hneighbor]
    exact hv₈
  let e := c₈.mapPC (TapeProgram.rightLabel
    ((((((2+ParameterPrograms.raiseLabels i.val)+fixedLabels (Storage.fixedLayout d k))+11)+
      randomLinearLabels (Storage.formLayout d k) (Storage.point d k) i.val)+11)+
      randomLinearLabels (Storage.formLayout d k) (Storage.point d k) (i.val+k)+11))
  have hstop : (layer d k i).Stops inp (s.toCfg (layer d k i).entry)
      (t₁+1+t₂+1+t₃+1+t₄+1+t₅+1+t₆+1+t₇+1+t₈) e := by
    exact hall
  refine ⟨_,e,?_,hstop,hi₈,hpay,hresult,?_,?_,?_,hpay.output,?_,hframe⟩
  · unfold layerTimeBound
    omega
  · intro j; exact hframe _ (point_not_writable d k i j)
  · intro j; exact hframe _ (countdown_not_writable d k i j)
  · intro a ha; exact hframe _ (protected_low_not_writable d k i a ha)
  · intro a ha; exact hframe _ (other_neighbor_not_writable d k i a ha)



















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

theorem solution {d k ell b M : ℕ} {h : 0<ell}
    {forms : Fin (2*k*(2^ell)*d) → Fin (2^ell)}
    {hashes : Fin (k*(2^ell)*(2^ell)*(2^ell)) → Fin b} {z : Fin d → Fin (2^ell)}
    (i : Fin k) (hk : k≤2^ell) (hb : 0<b) (hM : 1≤M) (caps : ExpandingCodes.Computation.SamplerProgram.LayerCaps d k ell b M)
    (inp : Inputs) (s : ExpandingCodes.Computation.TapeStore (ExpandingCodes.Computation.SamplerProgram.Storage.registers d k) 2)
    (hs : ExpandingCodes.Computation.SamplerProgram.LayerInvariant d k ell b h forms hashes z M s) :
    ∃ t e,t≤ExpandingCodes.Computation.SamplerProgram.layerTimeBound d k i M ∧
      (ExpandingCodes.Computation.SamplerProgram.layer d k i).Stops inp (s.toCfg (ExpandingCodes.Computation.SamplerProgram.layer d k i).entry) t e ∧
      ExpandingCodes.Computation.SamplerProgram.LayerInvariant d k ell b h forms hashes z M e.store ∧ ExpandingCodes.Computation.TapeStore.SamePayload e.store s ∧
      e.reg (ExpandingCodes.Computation.SamplerProgram.Storage.neighbor d k i)=i.val*b+
        (ExpandingCodes.Computation.EncodedSampler.neighbor (ExpandingCodes.PolynomialStretch.BinaryField.indexOperations ell h) forms hashes i z).val ∧
      (∀ j,e.reg (ExpandingCodes.Computation.SamplerProgram.Storage.point d k j)=s.reg (ExpandingCodes.Computation.SamplerProgram.Storage.point d k j)) ∧
      (∀ j,e.reg (ExpandingCodes.Computation.SamplerProgram.Storage.countdown d k j)=s.reg (ExpandingCodes.Computation.SamplerProgram.Storage.countdown d k j)) ∧
      (∀ a : Fin 80,(32≤a.val ∧ a.val<46) ∨ (60≤a.val ∧ a.val<69) →
        e.reg (ExpandingCodes.Computation.SamplerProgram.Storage.low d k a)=s.reg (ExpandingCodes.Computation.SamplerProgram.Storage.low d k a)) ∧
      e.output=s.output ∧
      (∀ a : Fin k,a≠i → e.reg (ExpandingCodes.Computation.SamplerProgram.Storage.neighbor d k a)=s.reg (ExpandingCodes.Computation.SamplerProgram.Storage.neighbor d k a)) ∧
      ExpandingCodes.Computation.SamplerProgram.LayerFrame d k i s e.store := by
  exact @ExpandingCodes.Computation.SamplerProgram.layer_stops d k ell b M h forms hashes z i hk hb hM caps inp s hs

