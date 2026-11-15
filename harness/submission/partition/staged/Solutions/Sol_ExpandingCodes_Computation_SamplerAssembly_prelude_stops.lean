import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime
import Mathlib
import Theorems.Thm_ExpandingCodes_Computation_SourceFieldSetup_setup_stops

set_option autoImplicit false
open scoped Classical BigOperators


section FlattenModule0


set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch























end ExpandingCodes.PolynomialStretch

end FlattenModule0


section FlattenModule1





set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch.BinaryPolynomial

open Polynomial































































































































































































































end ExpandingCodes.PolynomialStretch.BinaryPolynomial

end FlattenModule1


section FlattenModule2


set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch.BinaryField

open Polynomial BinaryPolynomial






















































































































































































































































































































































































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













 theorem cell_stops (b : Fin B) (action : Sym → Sym × Move) (inp : Inputs)
    (d : TapeStore R B) :
    (cell b action).Stops inp (d.toCfg 0) 1 ((cellStore d b action).toCfg 1) := by
  constructor
  · apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, cell, TapeStore.toCfg]
    · simp [TapeProgram.step, cell, cellStore, TapeStore.toCfg]
  · simp [TapeProgram.halted, cell, TapeStore.toCfg]














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











theorem halveStore_step (d : TapeStore R B) (src quotient parity : Fin R)
    (hsq : src ≠ quotient) (hsp : src ≠ parity) (hqp : quotient ≠ parity) (n : ℕ) :
    halveStore ((d.setReg src n).setReg quotient (d.reg quotient+1)) src quotient parity n =
      halveStore d src quotient parity (n+2) := by
  simp only [halveStore, TapeStore.setReg]
  congr 1
  funext j
  by_cases hp : j = parity
  · subst j
    simp [Function.update, Ne.symm hsp, Ne.symm hqp]
  · simp only [Function.update_of_ne hp]
    by_cases hq : j = quotient
    · subst j
      simp [Function.update, Ne.symm hsq]
      omega
    · simp only [Function.update_of_ne hq]
      by_cases hs : j = src
      · subst j; simp [Function.update]
      · simp [Function.update, hs, hq]

theorem halveLoop_stops (src quotient parity : Fin R)
    (hsq : src ≠ quotient) (hsp : src ≠ parity) (hqp : quotient ≠ parity)
    (inp : Inputs) (n : ℕ) (d : TapeStore R B) (hn : d.reg src = n) :
    (halveLoop src quotient parity).Stops inp (d.toCfg 0)
      (3*(n/2)+2*(n%2)+1) ((halveStore d src quotient parity n).toCfg 4) := by
  induction n using Nat.twoStepInduction generalizing d with
  | zero =>
    have he : halveStore d src quotient parity 0 = d := by
      have hs : d.setReg src 0 = d := by simp [TapeStore.setReg, ← hn]
      simp only [halveStore, Nat.zero_div, Nat.zero_mod, Nat.add_zero, hs, setReg_self]
    constructor
    · apply TapeProgram.Exec.one
      · simp [TapeProgram.halted, halveLoop]
      · simp [TapeProgram.step, halveLoop, TapeStore.toCfg, hn, he]
    · simp [TapeProgram.halted, halveLoop]
  | one =>
    let d₁ := d.setReg src 0
    let e := d₁.setReg parity (d.reg parity+1)
    have hs₁ : (halveLoop src quotient parity).step inp (d.toCfg 0) = d₁.toCfg 1 := by
      simp [TapeProgram.step, halveLoop, TapeStore.toCfg, d₁, TapeStore.setReg, hn]
    have hs₂ : (halveLoop src quotient parity).step inp (d₁.toCfg 1) = d₁.toCfg 3 := by
      simp [TapeProgram.step, halveLoop, TapeStore.toCfg, d₁, TapeStore.setReg]
    have hs₃ : (halveLoop src quotient parity).step inp (d₁.toCfg 3) = e.toCfg 4 := by
      simp [TapeProgram.step, halveLoop, TapeStore.toCfg, d₁, e, TapeStore.setReg, Ne.symm hsp]
    have he : halveStore d src quotient parity 1 = e := by
      have hq : (d.setReg src 0).setReg quotient (d.reg quotient) = d.setReg src 0 := by
        convert setReg_self (d.setReg src 0) quotient using 1
        simp [TapeStore.setReg, Ne.symm hsq]
      simpa only [halveStore, show 1/2 = 0 from rfl, show 1%2 = 1 from rfl,
        Nat.add_zero, hq, e, d₁]
    constructor
    · have h := TapeProgram.Exec.step (by simp [TapeProgram.halted, halveLoop]) hs₁
        (TapeProgram.Exec.step (by simp [TapeProgram.halted, halveLoop]) hs₂
          (TapeProgram.Exec.one (by simp [TapeProgram.halted, halveLoop]) hs₃))
      simpa [he] using h
    · simp [TapeProgram.halted, halveLoop]
  | more n ih _ =>
    let d₁ := d.setReg src (n+1)
    let d₂ := d.setReg src n
    let e := d₂.setReg quotient (d.reg quotient+1)
    have he : e.reg src = n := by simp [e, d₂, TapeStore.setReg, hsq]
    have htail := ih e he
    have hs₁ : (halveLoop src quotient parity).step inp (d.toCfg 0) = d₁.toCfg 1 := by
      simp [TapeProgram.step, halveLoop, TapeStore.toCfg, d₁, TapeStore.setReg, hn]
    have hs₂ : (halveLoop src quotient parity).step inp (d₁.toCfg 1) = d₂.toCfg 2 := by
      simp [TapeProgram.step, halveLoop, TapeStore.toCfg, d₁, d₂, TapeStore.setReg]
    have hs₃ : (halveLoop src quotient parity).step inp (d₂.toCfg 2) = e.toCfg 0 := by
      simp [TapeProgram.step, halveLoop, TapeStore.toCfg, d₂, e, TapeStore.setReg, Ne.symm hsq]
    have hpost : halveStore e src quotient parity n = halveStore d src quotient parity (n+2) :=
      halveStore_step d src quotient parity hsq hsp hqp n
    constructor
    · have h := TapeProgram.Exec.step (by simp [TapeProgram.halted, halveLoop]) hs₁
        (TapeProgram.Exec.step (by simp [TapeProgram.halted, halveLoop]) hs₂
          (TapeProgram.Exec.step (by simp [TapeProgram.halted, halveLoop]) hs₃ htail.exec))
      rw [hpost] at h
      convert h using 1 <;> omega
    · simp [TapeProgram.halted, halveLoop]







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

 










































 








 





 









 































 































































 
























 














 




































































 































 














 





























































 

























































 


 








 















 


















































end TapeArrays
end ExpandingCodes.Computation





















end FlattenModule14


section FlattenModule15


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB
namespace TapeProgram
variable {R B L K : ℕ}












































































































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










theorem halve_stops (src quotient parity : Fin R)
    (hsq : src ≠ quotient) (hsp : src ≠ parity) (hqp : quotient ≠ parity)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (halve src quotient parity).Stops inp
      (d.toCfg (halve (B := B) src quotient parity).entry)
      (d.reg quotient+d.reg parity+3*(d.reg src/2)+2*(d.reg src%2)+5) e ∧
      e.store = halfStore d src quotient parity := by
  let d₁ := d.setReg quotient 0
  let d₂ := d₁.setReg parity 0
  have h₁ := TapeMacros.clear_stops quotient inp (d.reg quotient) d rfl
  have h₂ := TapeMacros.clear_stops parity inp (d.reg parity) d₁
    (by simp [d₁, TapeStore.setReg, Ne.symm hqp])
  have hn : d₂.reg src = d.reg src := by
    simp [d₂, d₁, TapeStore.setReg, hsq, hsp]
  have h₃ := halveLoop_stops src quotient parity hsq hsp hqp inp (d.reg src) d₂ hn
  have hall := (h₁.seq h₂).seq h₃
  have hpost : halveStore d₂ src quotient parity (d.reg src) = halfStore d src quotient parity := by
    simp only [halveStore, halfStore, d₂, d₁, TapeStore.setReg]
    congr 1
    funext j
    by_cases hp : j = parity
    · subst j
      simp [Function.update, Ne.symm hqp]
    · simp only [Function.update_of_ne hp]
      by_cases hq : j = quotient
      · subst j
        simp [Function.update, hqp]
      · simp only [Function.update_of_ne hq]
        by_cases hs : j = src
        · subst j; simp [Function.update]
        · simp [Function.update, hp, hq, hs]
  refine ⟨((halveStore d₂ src quotient parity (d.reg src)).toCfg (4 : Fin 5)).mapPC
    (TapeProgram.rightLabel 4), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change halveStore d₂ src quotient parity (d.reg src) = _
    exact hpost









theorem halfStep_stops (src quotient parity : Fin R)
    (hsq : src ≠ quotient) (hsp : src ≠ parity) (hqp : quotient ≠ parity)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (halfStep src quotient parity).Stops inp
      (d.toCfg (halfStep (B := B) src quotient parity).entry)
      (d.reg quotient+d.reg parity+5*(d.reg src/2)+2*(d.reg src%2)+7) e ∧
      e.store = halfStepStore d src quotient parity := by
  obtain ⟨c, hc, hcs⟩ := halve_stops src quotient parity hsq hsp hqp inp d
  have hcq : c.reg quotient = d.reg src/2 := by
    change c.store.reg quotient = _
    rw [hcs]
    simp [halfStore, TapeStore.setReg, hqp]
  have h₂ := TapeMacros.transfer_stops quotient src (Ne.symm hsq) inp (d.reg src/2) c.store hcq
  have hall := hc.seq h₂
  have hpost : TapeMacros.transferStore c.store quotient src = halfStepStore d src quotient parity := by
    rw [hcs]
    simp only [TapeMacros.transferStore, halfStore, halfStepStore, TapeStore.setReg]
    congr 1
    funext j
    by_cases hp : j = parity
    · subst j
      simp [Function.update, Ne.symm hsp, Ne.symm hqp]
    · by_cases hq : j = quotient
      · subst j
        simp [Function.update, Ne.symm hsq, hqp]
      · by_cases hs : j = src
        · subst j
          simp [Function.update, hsq, hsp, hqp]
        · simp [Function.update, hp, hq, hs]
  refine ⟨((TapeMacros.transferStore c.store quotient src).toCfg (2 : Fin 3)).mapPC
    (TapeProgram.rightLabel 9), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change TapeMacros.transferStore c.store quotient src = _
    exact hpost

theorem halfStep_time_le (n q p : ℕ) : q+p+5*(n/2)+2*(n%2)+7 ≤ q+p+3*n+7 := by omega













































































theorem setReg_bound (d : TapeStore R B) (r : Fin R) (n M : ℕ)
    (hd : ∀ j, d.reg j ≤ M) (hn : n ≤ M) : ∀ j, (d.setReg r n).reg j ≤ M := by
  intro j
  by_cases h : j = r
  · subst j; simpa using hn
  · simpa [TapeStore.setReg, h] using hd j

theorem halfStepStore_bound (d : TapeStore R B) (src quotient parity : Fin R)
    (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (halfStepStore d src quotient parity).reg j ≤ M := by
  apply setReg_bound _ parity _ M
  · apply setReg_bound _ quotient 0 M
    · apply setReg_bound d src _ M hd
      exact (Nat.div_le_self _ _).trans (hd src)
    · omega
  · omega



















theorem shiftStore_fresh (src quotient parity count j : Fin R)
    (hs : j ≠ src) (hq : j ≠ quotient) (hp : j ≠ parity) (hc : j ≠ count)
    (n : ℕ) (d : TapeStore R B) :
    (shiftStore src quotient parity count n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => simp [shiftStore, TapeStore.setReg, hc]
  | succ n ih =>
    rw [shiftStore, ih]
    simp [halfStepStore, TapeStore.setReg, hs, hq, hp, hc]





















































































































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



















 theorem readBit_stops (a : Fin R) (inp : Inputs) (d : TapeStore R B) :
    (readBit a).Stops inp (d.toCfg 0) 2 ((readBitStore a inp d).toCfg 3) := by
  let e : TapeStore R B := { d with roHead := Function.update d.roHead 3 (d.roHead 3+1) }
  let j : Fin 4 := if Machine.readRO inp.rand (d.roHead 3) = .one then 1 else 2
  have h₁ : (readBit a).step inp (d.toCfg 0) = e.toCfg j := by
    simp [TapeProgram.step, readBit, TapeStore.toCfg, e, j, Inputs.get]
    split_ifs with h <;> simp_all
  have h₂ : (readBit a).step inp (e.toCfg j) = (readBitStore a inp d).toCfg 3 := by
    by_cases h : Machine.readRO inp.rand (d.roHead 3) = .one
    · simp [TapeProgram.step, readBit, TapeStore.toCfg, e, j, h, readBitStore,
        TapeStore.setReg, bitAt, bitNat]
    · simp [TapeProgram.step, readBit, TapeStore.toCfg, e, j, h, readBitStore,
        TapeStore.setReg, bitAt, bitNat]
  constructor
  · apply TapeProgram.Exec.step (by simp [TapeProgram.halted, readBit]) h₁
    apply TapeProgram.Exec.one
    · dsimp [j]
      split_ifs <;> simp [TapeProgram.halted, readBit]
    · exact h₂
  · simp [TapeProgram.halted, readBit]









 theorem double_post (l : Layout R) (d : TapeStore R B) :
    TapeMacros.transferStore ((d.setReg l.tmp (d.reg l.acc)).setReg l.scratch 0) l.tmp l.acc =
      doubleStore l d := by
  have hat : l.acc ≠ l.tmp := l.reg.injective.ne (by decide)
  have has : l.acc ≠ l.scratch := l.reg.injective.ne (by decide)
  have hts : l.tmp ≠ l.scratch := l.reg.injective.ne (by decide)
  simp only [TapeMacros.transferStore, doubleStore, TapeStore.setReg]
  congr 1
  funext j
  by_cases ha : j = l.acc
  · subst j
    simp [Function.update, hat, has, Ne.symm hat, Ne.symm has]
    omega
  · by_cases ht : j = l.tmp
    · subst j
      simp [Function.update, hat, has, hts, Ne.symm hat]
    · by_cases hs : j = l.scratch
      · subst j
        simp [Function.update, hat, has, hts, Ne.symm has, Ne.symm hts]
      · simp [Function.update, ha, ht, hs]

 theorem double_stops (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (double l).Stops inp (d.toCfg (double (B := B) l).entry)
      (d.reg l.tmp+d.reg l.scratch+7*d.reg l.acc+9) e ∧ e.store = doubleStore l d := by
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops l.acc l.tmp l.scratch
    (l.reg.injective.ne (by decide)) (l.reg.injective.ne (by decide))
    (l.reg.injective.ne (by decide)) inp d
  have ht : c.store.reg l.tmp = d.reg l.acc := by
    rw [hcs]
    simp [TapeStore.setReg, Layout.tmp, Layout.acc, Layout.scratch, l.reg.injective.ne (by decide : (4 : Fin 6) ≠ 5)]
  have htr := TapeMacros.transfer_stops l.tmp l.acc (l.reg.injective.ne (by decide))
    inp (d.reg l.acc) c.store ht
  have hall := hc.seq htr
  refine ⟨((TapeMacros.transferStore c.store l.tmp l.acc).toCfg (2 : Fin 3)).mapPC
      (TapeProgram.rightLabel 11), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change TapeMacros.transferStore c.store l.tmp l.acc = _
    rw [hcs]
    exact double_post l d








 theorem nextBit_stops (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (nextBit l).Stops inp (d.toCfg (nextBit (B := B) l).entry)
      (d.reg l.tmp+d.reg l.scratch+7*d.reg l.acc+12) e ∧ e.store = nextBitStore l inp d := by
  obtain ⟨c, hc, hcs⟩ := double_stops l inp d
  have hr := readBit_stops l.acc inp c.store
  have hall := hc.seq hr
  refine ⟨((readBitStore l.acc inp c.store).toCfg (3 : Fin 4)).mapPC
      (TapeProgram.rightLabel 14), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change readBitStore l.acc inp c.store = _
    rw [hcs]
    rfl






 

























 theorem nextBitStore_reg (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (nextBitStore l inp d).reg =
      Function.update (Function.update (Function.update d.reg l.acc
        (2*d.reg l.acc+bitNat (bitAt inp (d.roHead 3)))) l.tmp 0) l.scratch 0 := by
  have hat : l.acc ≠ l.tmp := l.reg.injective.ne (by decide)
  have has : l.acc ≠ l.scratch := l.reg.injective.ne (by decide)
  have hts : l.tmp ≠ l.scratch := l.reg.injective.ne (by decide)
  simp only [nextBitStore, readBitStore, doubleStore, TapeStore.setReg]
  funext j
  by_cases ha : j = l.acc
  · subst j
    simp [Function.update, hat, has]
  · by_cases ht : j = l.tmp
    · subst j
      simp [Function.update, hat, hts, Ne.symm hat]
    · by_cases hs : j = l.scratch
      · subst j
        simp [Function.update, Ne.symm has, Ne.symm hts]
      · simp [Function.update, ha, ht, hs]

 theorem nextBitStore_count (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (nextBitStore l inp d).reg l.count = d.reg l.count := by
  rw [nextBitStore_reg]
  simp [Layout.count, Layout.acc, Layout.tmp, Layout.scratch,
    l.reg.injective.ne (by decide : (3 : Fin 6) ≠ 2),
    l.reg.injective.ne (by decide : (3 : Fin 6) ≠ 4),
    l.reg.injective.ne (by decide : (3 : Fin 6) ≠ 5)]

 theorem readBits_stops (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hd : d.reg l.count = n) :
    (readBits l).Stops inp (d.toCfg (TapeProgram.loopHeader 18)) (bitsTime l inp n d)
      ((bitsStore l inp n d).toCfg (TapeProgram.loopExit 18)) := by
  induction n generalizing d with
  | zero => exact TapeProgram.loop_zero (nextBit l) l.count inp d hd
  | succ n ih =>
    let d₁ := TapeProgram.decStore l.count d
    let d₂ := nextBitStore l inp d₁
    have hr : d₂.reg l.count = n := by
      rw [nextBitStore_count]
      simp [d₁, TapeProgram.decStore, hd]
    have ht := ih d₂ hr
    obtain ⟨c, hc, hcs⟩ := nextBit_stops l inp d₁
    have hh := TapeProgram.loop_positive_header (nextBit l) l.count inp d (by omega)
    have hb := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (nextBit l) l.count)
    have hx := TapeProgram.loop_body_return (nextBit l) l.count inp c hc.halted
    have he : c.store.toCfg (TapeProgram.loopHeader 18) = d₂.toCfg (TapeProgram.loopHeader 18) := by
      rw [hcs]
    rw [he] at hx
    constructor
    · have h := ((hh.trans hb).trans hx).trans ht.exec
      convert h using 1 <;> first | rfl | skip
      simp only [bitsTime, d₂, d₁, TapeProgram.decStore, Function.update_of_ne
        (l.reg.injective.ne (by decide : (4 : Fin 6) ≠ 3)), Function.update_of_ne
        (l.reg.injective.ne (by decide : (5 : Fin 6) ≠ 3)), Function.update_of_ne
        (l.reg.injective.ne (by decide : (2 : Fin 6) ≠ 3))]
      simp only [Layout.acc, Layout.tmp, Layout.scratch] at *
      omega
    · exact ht.halted

 theorem bitsStore_roHead (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (bitsStore l inp n d).roHead = Function.update d.roHead 3 (d.roHead 3+n) := by
  induction n generalizing d with
  | zero => simp [bitsStore]
  | succ n ih =>
    rw [bitsStore, ih]
    simp [nextBitStore, readBitStore, doubleStore, TapeStore.setReg,
      TapeProgram.decStore, Function.update_idem, Nat.add_assoc, Nat.add_comm]

 theorem bitsStore_payload (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (bitsStore l inp n d).output = d.output ∧
    (bitsStore l inp n d).bufferTape = d.bufferTape ∧
    (bitsStore l inp n d).bufferHead = d.bufferHead := by
  induction n generalizing d with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih => exact ih _

theorem bitsStore_acc (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (bitsStore l inp n d).reg l.acc = value inp n (d.roHead 3) (d.reg l.acc) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [bitsStore, ih]
    simp [nextBitStore, readBitStore, doubleStore, TapeStore.setReg, TapeProgram.decStore,
      Layout.acc, Layout.count, Layout.tmp, Layout.scratch, value]

 theorem bitsStore_reg_other (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (j : Fin R) (ha : j ≠ l.acc) (hc : j ≠ l.count)
    (ht : j ≠ l.tmp) (hs : j ≠ l.scratch) :
    (bitsStore l inp n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [bitsStore, ih, nextBitStore_reg]
    simp [TapeProgram.decStore, ha, hc, ht, hs]

 theorem bitsStore_count (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (bitsStore l inp n d).reg l.count = d.reg l.count-n := by
  induction n generalizing d with
  | zero => simp [bitsStore]
  | succ n ih =>
    rw [bitsStore, ih, nextBitStore_count]
    simp [TapeProgram.decStore, Nat.sub_sub, Nat.add_comm]

 theorem bitsStore_tmp (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hd : d.reg l.tmp = 0) : (bitsStore l inp n d).reg l.tmp = 0 := by
  induction n generalizing d with
  | zero => exact hd
  | succ n ih =>
    apply ih
    rw [nextBitStore_reg]
    simp [Layout.tmp, Layout.scratch]

 theorem bitsStore_scratch (l : Layout R) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hd : d.reg l.scratch = 0) : (bitsStore l inp n d).reg l.scratch = 0 := by
  induction n generalizing d with
  | zero => exact hd
  | succ n ih =>
    apply ih
    rw [nextBitStore_reg]
    simp

 theorem bitsTime_le (l : Layout R) (inp : Inputs) (n Q : ℕ) (d : TapeStore R B)
    (ht : d.reg l.tmp = 0) (hs : d.reg l.scratch = 0)
    (hQ : 2^n*(d.reg l.acc+1) ≤ Q) :
    bitsTime l inp n d ≤ n*(7*Q+14)+1 := by
  induction n generalizing d with
  | zero => simp [bitsTime]
  | succ n ih =>
    let e := nextBitStore l inp (TapeProgram.decStore l.count d)
    have he : e.reg l.acc = 2*d.reg l.acc + bitNat (bitAt inp (d.roHead 3)) := by
      simp [e, nextBitStore, readBitStore, doubleStore, TapeStore.setReg,
        TapeProgram.decStore, Layout.acc, Layout.count, Layout.tmp, Layout.scratch]
    have het : e.reg l.tmp = 0 := by
      rw [nextBitStore_reg]
      simp [Layout.tmp, Layout.scratch]
    have hes : e.reg l.scratch = 0 := by rw [nextBitStore_reg]; simp
    have hb : bitNat (bitAt inp (d.roHead 3)) ≤ 1 := by unfold bitNat; split <;> omega
    have hQe : 2^n*(e.reg l.acc+1) ≤ Q := by
      rw [he]
      rw [pow_succ] at hQ
      nlinarith
    have hi := ih e het hes hQe
    have hpow : 1 ≤ 2^(n+1) := Nat.one_le_pow _ _ (by omega)
    have ha : d.reg l.acc ≤ Q := by nlinarith
    simp only [bitsTime, ht, hs, zero_add]
    have hd₁ : (TapeProgram.decStore l.count d).reg l.tmp = 0 := by
      simp [TapeProgram.decStore, Layout.tmp, Layout.count, ht]
    have hd₂ : (TapeProgram.decStore l.count d).reg l.scratch = 0 := by
      simp [TapeProgram.decStore, Layout.scratch, Layout.count, hs]
    change 7*d.reg l.acc+14+bitsTime l inp n e ≤ _
    nlinarith










 theorem prepare_stops (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (prepare l).Stops inp (d.toCfg (prepare (B := B) l).entry)
      (d.reg l.count+d.reg l.scratch+5*d.reg l.ell+d.reg l.acc+d.reg l.tmp+11) e ∧
      e.store = prepareStore l d := by
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops l.ell l.count l.scratch
    (l.reg.injective.ne (by decide)) (l.reg.injective.ne (by decide))
    (l.reg.injective.ne (by decide)) inp d
  have ha : c.reg l.acc = d.reg l.acc := by
    change c.store.reg l.acc = _
    rw [hcs]
    simp [TapeStore.setReg, Layout.acc, Layout.count, Layout.scratch]
  let e := c.store.setReg l.acc 0
  have ht : e.reg l.tmp = d.reg l.tmp := by
    simp only [e, TapeStore.setReg]
    change (Function.update c.store.reg l.acc 0) l.tmp = _
    rw [Function.update_of_ne (l.reg.injective.ne (by decide : (4 : Fin 6) ≠ 2)), hcs]
    simp [TapeStore.setReg, Layout.tmp, Layout.count, Layout.scratch]
  have h₁ := TapeMacros.clear_stops l.acc inp (d.reg l.acc) c.store ha
  have h₂ := TapeMacros.clear_stops l.tmp inp (d.reg l.tmp) e ht
  have hall := (hc.seq h₁).seq h₂
  refine ⟨((e.setReg l.tmp 0).toCfg (1 : Fin 2)).mapPC (TapeProgram.rightLabel 13), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change (c.store.setReg l.acc 0).setReg l.tmp 0 = _
    rw [hcs]
    rfl









 theorem randomIndex_stops (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    ∃ t e, t ≤ d.reg l.count+d.reg l.scratch+d.reg l.acc+d.reg l.tmp+
        5*d.reg l.ell+13+d.reg l.ell*(7*2^(d.reg l.ell)+14) ∧
      (randomIndex l).Stops inp (d.toCfg (randomIndex (B := B) l).entry) t e ∧
      e.store = indexStore l inp d := by
  obtain ⟨c, hc, hcs⟩ := prepare_stops l inp d
  have hcount : c.store.reg l.count = d.reg l.ell := by
    rw [hcs]
    simp [prepareStore, TapeStore.setReg, Layout.count, Layout.acc, Layout.tmp, Layout.scratch]
  have htmp : c.store.reg l.tmp = 0 := by rw [hcs]; simp [prepareStore, TapeStore.setReg]
  have hscratch : c.store.reg l.scratch = 0 := by
    rw [hcs]
    simp [prepareStore, TapeStore.setReg, Layout.scratch, Layout.acc, Layout.tmp]
  have hacc : c.store.reg l.acc = 0 := by
    rw [hcs]
    simp [prepareStore, TapeStore.setReg, Layout.acc, Layout.tmp]
  have hr := readBits_stops l inp (d.reg l.ell) c.store hcount
  have hb := bitsTime_le l inp (d.reg l.ell) (2^(d.reg l.ell)) c.store htmp hscratch
    (by rw [hacc]; simp)
  have hall := hc.seq hr
  refine ⟨d.reg l.count+d.reg l.scratch+5*d.reg l.ell+d.reg l.acc+d.reg l.tmp+11+1+
    bitsTime l inp (d.reg l.ell) c.store,
    ((bitsStore l inp (d.reg l.ell) c.store).toCfg (TapeProgram.loopExit 18)).mapPC
    (TapeProgram.rightLabel 15 : Fin 20 → Fin 35), ?_, ?_, ?_⟩
  · omega
  · exact hall
  · change bitsStore l inp (d.reg l.ell) c.store = _
    rw [hcs]
    rfl

 theorem indexStore_acc (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).reg l.acc = value inp (d.reg l.ell) (d.roHead 3) 0 := by
  rw [indexStore, bitsStore_acc]
  simp [prepareStore, TapeStore.setReg, Layout.acc, Layout.tmp]

 theorem indexStore_acc_lt (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).reg l.acc < 2^(d.reg l.ell) := by
  rw [indexStore_acc]
  simpa using value_lt inp (d.reg l.ell) (d.roHead 3) 0

 theorem indexStore_roHead (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).roHead = Function.update d.roHead 3 (d.roHead 3+d.reg l.ell) := by
  rw [indexStore, bitsStore_roHead]
  rfl

 





 theorem indexStore_q (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).reg l.q = d.reg l.q := by
  rw [indexStore, bitsStore_reg_other l inp _ _ l.q]
  · simp [prepareStore, TapeStore.setReg, Layout.q, Layout.count, Layout.acc, Layout.tmp, Layout.scratch]
  all_goals exact l.reg.injective.ne (by decide)

 theorem indexStore_count (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).reg l.count = 0 := by
  rw [indexStore, bitsStore_count]
  simp [prepareStore, TapeStore.setReg, Layout.count, Layout.acc, Layout.tmp, Layout.scratch]

 theorem indexStore_tmp (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).reg l.tmp = 0 := by
  apply bitsStore_tmp
  simp [prepareStore, TapeStore.setReg]

 theorem indexStore_scratch (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).reg l.scratch = 0 := by
  apply bitsStore_scratch
  simp [prepareStore, TapeStore.setReg, Layout.scratch, Layout.acc, Layout.tmp]

 theorem indexStore_payload (l : Layout R) (inp : Inputs) (d : TapeStore R B) :
    (indexStore l inp d).output = d.output ∧
    (indexStore l inp d).bufferTape = d.bufferTape ∧
    (indexStore l inp d).bufferHead = d.bufferHead :=
  bitsStore_payload l inp _ _

/-- A deliberately loose fixed polynomial in q, valid even when the four
mutable counters initially contain arbitrary values bounded by q. -/
 theorem randomIndex_polynomial (l : Layout R) (inp : Inputs) (d : TapeStore R B)
    (hq : d.reg l.q = 2^(d.reg l.ell)) (he : d.reg l.ell ≤ d.reg l.q)
    (hc : d.reg l.count ≤ d.reg l.q) (hs : d.reg l.scratch ≤ d.reg l.q)
    (ha : d.reg l.acc ≤ d.reg l.q) (ht : d.reg l.tmp ≤ d.reg l.q) :
    ∃ t e, t ≤ (d.reg l.q+1)*(7*d.reg l.q+30) ∧
      (randomIndex l).Stops inp (d.toCfg (randomIndex (B := B) l).entry) t e ∧
      e.store = indexStore l inp d := by
  obtain ⟨t, e, hb, hr, hpost⟩ := randomIndex_stops l inp d
  refine ⟨t, e, ?_, hr, hpost⟩
  rw [← hq] at hb
  nlinarith

open scoped BigOperators
open ExpandingCodes.PolynomialStretch













 














 


























 












 


































 

































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





















 theorem entry_stops (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs) (d : TapeStore R B)
    (hq : d.reg l.q = 2^(d.reg l.ell)) (he : d.reg l.ell ≤ d.reg l.q)
    (hc : d.reg l.count ≤ d.reg l.q) (hs : d.reg l.scratch ≤ d.reg l.q)
    (ha : d.reg l.acc ≤ d.reg l.q) (ht : d.reg l.tmp ≤ d.reg l.q) :
    ∃ t e, t ≤ entryBound (d.reg l.q) ∧
      (entry l b).Stops inp (d.toCfg (entry l b).entry) t e ∧
      e.store = entryStore l b inp d := by
  obtain ⟨t, c, hb, hr, hpost⟩ := RandomBits.randomIndex_polynomial l inp d hq he hc hs ha ht
  obtain ⟨e, hcopy, hcopypost⟩ := TapeMacros.copy_stops l.q l.count l.scratch
    (l.reg.injective.ne (by decide)) (l.reg.injective.ne (by decide))
    (l.reg.injective.ne (by decide)) inp c.store
  have hcr : c.store.reg l.count = 0 := by rw [hpost]; exact RandomBits.indexStore_count l inp d
  have hcs : c.store.reg l.scratch = 0 := by rw [hpost]; exact RandomBits.indexStore_scratch l inp d
  have hcq : c.store.reg l.q = d.reg l.q := by rw [hpost]; exact RandomBits.indexStore_q l inp d
  have hec : e.store.reg l.count = d.reg l.q := by
    rw [hcopypost, hcq]
    simp [TapeStore.setReg, RandomBits.Layout.count, RandomBits.Layout.scratch]
  have hea : e.store.reg l.acc = c.store.reg l.acc := by
    rw [hcopypost]
    simp [TapeStore.setReg, RandomBits.Layout.acc, RandomBits.Layout.count, RandomBits.Layout.scratch]
  have hv : c.store.reg l.acc ≤ d.reg l.q := by
    rw [hpost, hq]
    exact (RandomBits.indexStore_acc_lt l inp d).le
  have hw := TapeArrays.writeBlock_stops l.acc l.count (l.reg.injective.ne (by decide)) b inp
    (c.store.reg l.acc) (d.reg l.q) e.store hea hec hv
  obtain ⟨f, hf, hfs⟩ := hw
  have hall := (hr.seq hcopy).seq hf
  refine ⟨t+1+(c.store.reg l.count+c.store.reg l.scratch+5*c.store.reg l.q+7)+1+
    (2*d.reg l.q+c.store.reg l.acc+3), f.mapPC (TapeProgram.rightLabel 46), ?_, ?_, ?_⟩
  · simp only [entryBound]
    change c.reg l.count = 0 at hcr
    change c.reg l.scratch = 0 at hcs
    change c.reg l.q = d.reg l.q at hcq
    change c.reg l.acc ≤ d.reg l.q at hv
    rw [hcr, hcs, hcq]
    omega
  · exact hall
  · change f.store = _
    rw [hfs, hcopypost, hcq, hpost]
    rfl





theorem entryStore_reg (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs)
    (d : TapeStore R B) (j : Fin R) :
    (entryStore l b inp d).reg j =
      if j = l.acc ∨ j = l.count ∨ j = l.tmp ∨ j = l.scratch then 0 else d.reg j := by
  rw [entryStore, TapeArrays.writeBlockStore_reg]
  by_cases ha : j = l.acc
  · subst j
    simp [TapeStore.setReg, RandomBits.Layout.acc, RandomBits.Layout.count, RandomBits.Layout.scratch]
  · by_cases hc : j = l.count
    · subst j
      simp [TapeStore.setReg]
    · by_cases ht : j = l.tmp
      · subst j
        simp [TapeStore.setReg, RandomBits.Layout.tmp, RandomBits.Layout.acc,
          RandomBits.Layout.count, RandomBits.Layout.scratch, RandomBits.indexStore_tmp]
      · by_cases hs : j = l.scratch
        · subst j
          simp [TapeStore.setReg, RandomBits.Layout.scratch, RandomBits.Layout.acc, RandomBits.Layout.count]
        · simp only [ha, hc, ht, hs, or_self, ite_false]
          simp only [TapeStore.setReg, Function.update_of_ne ha, Function.update_of_ne hc,
            Function.update_of_ne hs]
          rw [RandomBits.indexStore, RandomBits.bitsStore_reg_other l inp _ _ j ha hc ht hs]
          simp [RandomBits.prepareStore, TapeStore.setReg, ha, hc, ht, hs]

 theorem entryStore_roHead (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs)
    (d : TapeStore R B) :
    (entryStore l b inp d).roHead = Function.update d.roHead 3 (d.roHead 3+d.reg l.ell) := by
  rw [entryStore, TapeArrays.writeBlockStore_roHead]
  exact RandomBits.indexStore_roHead l inp d

 theorem entryStore_head (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs)
    (d : TapeStore R B) (hq : d.reg l.q = 2^(d.reg l.ell)) :
    (entryStore l b inp d).bufferHead = Function.update d.bufferHead b (d.bufferHead b+d.reg l.q) := by
  have hv : (RandomBits.indexStore l inp d).reg l.acc ≤ d.reg l.q := by
    rw [hq]
    exact (RandomBits.indexStore_acc_lt l inp d).le
  rw [entryStore, TapeArrays.writeBlockStore_head _ _ _ _ _ _ hv]
  exact congrArg (fun f => Function.update f b (f b+d.reg l.q))
    (RandomBits.indexStore_payload l inp d).2.2

 theorem entryStore_output (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs)
    (d : TapeStore R B) : (entryStore l b inp d).output = d.output := by
  rw [entryStore, TapeArrays.writeBlockStore_output]
  exact (RandomBits.indexStore_payload l inp d).1

 theorem entryStore_symbol (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs)
    (d : TapeStore R B) (hq : d.reg l.q = 2^(d.reg l.ell)) (c : Fin B) (k : ℕ) :
    ((entryStore l b inp d).bufferTape c).getD k .blank =
      if c = b ∧ d.bufferHead b ≤ k ∧ k < d.bufferHead b+d.reg l.q then
        if k < d.bufferHead b+RandomBits.value inp (d.reg l.ell) (d.roHead 3) 0 then .one else .zero
      else (d.bufferTape c).getD k .blank := by
  have hv : (RandomBits.indexStore l inp d).reg l.acc ≤ d.reg l.q := by
    rw [hq]
    exact (RandomBits.indexStore_acc_lt l inp d).le
  rw [entryStore, TapeArrays.writeBlockStore_symbol _ _ _ _ _ _ hv]
  simp only [TapeStore.setReg, RandomBits.indexStore_acc,
    (RandomBits.indexStore_payload l inp d).2.1, (RandomBits.indexStore_payload l inp d).2.2]





 theorem entryStore_clean (l : RandomBits.Layout R) (b : Fin B) (inp : Inputs)
    (d : TapeStore R B) : Clean l (entryStore l b inp d) := by
  simp [Clean, entryStore_reg]






 theorem fill_stops (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hn : d.reg l.count = n) (hq : d.reg l.random.q = 2^(d.reg l.random.ell))
    (he : d.reg l.random.ell ≤ d.reg l.random.q) (hclean : Clean l.random d) :
    ∃ t, t ≤ n*(entryBound (d.reg l.random.q)+2)+1 ∧
      (fill l b).Stops inp (d.toCfg (TapeProgram.loopHeader 53)) t
        ((fillStore l b inp n d).toCfg (TapeProgram.loopExit 53)) := by
  induction n generalizing d with
  | zero => exact ⟨1, by omega, TapeProgram.loop_zero (entry l.random b) l.count inp d hn⟩
  | succ n ih =>
    let d₁ := TapeProgram.decStore l.count d
    let d₂ := entryStore l.random b inp d₁
    have hdr (j : Fin 6) : d₁.reg (l.random.reg j) = d.reg (l.random.reg j) := by
      simp [d₁, TapeProgram.decStore, l.fresh j]
    have hq₁ : d₁.reg l.random.q = 2^(d₁.reg l.random.ell) := by simpa only [hdr] using hq
    have he₁ : d₁.reg l.random.ell ≤ d₁.reg l.random.q := by simpa only [hdr] using he
    have hclean₁ : Clean l.random d₁ := by simpa only [Clean, hdr] using hclean
    obtain ⟨s, c, hs, hc, hcs⟩ := entry_stops l.random b inp d₁ hq₁ he₁
      (by rw [hclean₁.2.1]; omega) (by rw [hclean₁.2.2.2]; omega)
      (by rw [hclean₁.1]; omega) (by rw [hclean₁.2.2.1]; omega)
    have hr : d₂.reg l.count = n := by
      rw [entryStore_reg]
      simp [d₂, d₁, TapeProgram.decStore, hn, Ne.symm (l.fresh 2), Ne.symm (l.fresh 3),
        Ne.symm (l.fresh 4), Ne.symm (l.fresh 5)]
    have hq₂ : d₂.reg l.random.q = d.reg l.random.q := by
      rw [entryStore_reg]
      simp [RandomBits.Layout.q, RandomBits.Layout.acc, RandomBits.Layout.count,
        RandomBits.Layout.tmp, RandomBits.Layout.scratch, hdr]
    have he₂ : d₂.reg l.random.ell = d.reg l.random.ell := by
      rw [entryStore_reg]
      simp [RandomBits.Layout.ell, RandomBits.Layout.acc, RandomBits.Layout.count,
        RandomBits.Layout.tmp, RandomBits.Layout.scratch, hdr]
    obtain ⟨t, ht, hstop⟩ := ih d₂ hr (by rw [hq₂, he₂]; exact hq)
      (by rw [hq₂, he₂]; exact he) (entryStore_clean _ _ _ _)
    have hh := TapeProgram.loop_positive_header (entry l.random b) l.count inp d (by omega)
    have hb := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (entry l.random b) l.count)
    have hx := TapeProgram.loop_body_return (entry l.random b) l.count inp c hc.halted
    have hcx : c.store.toCfg (TapeProgram.loopHeader 53) = d₂.toCfg (TapeProgram.loopHeader 53) := by rw [hcs]
    rw [hcx] at hx
    refine ⟨1+s+1+t, ?_, ⟨?_, hstop.halted⟩⟩
    · rw [hq₂] at ht
      rw [hdr 1] at hs
      nlinarith [Nat.add_mul n 1 (entryBound (d.reg l.random.q)+2)]
    · exact ((hh.trans hb).trans hx).trans hstop.exec

theorem fillStore_reg_other (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ)
    (d : TapeStore R B) (j : Fin R) (ha : j ≠ l.random.acc) (hc : j ≠ l.random.count)
    (ht : j ≠ l.random.tmp) (hs : j ≠ l.random.scratch) (hk : j ≠ l.count) :
    (fillStore l b inp n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [fillStore, ih, entryStore_reg]
    simp [ha, hc, ht, hs, hk, TapeProgram.decStore]

theorem fillStore_count (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (fillStore l b inp n d).reg l.count = d.reg l.count-n := by
  induction n generalizing d with
  | zero => simp [fillStore]
  | succ n ih =>
    rw [fillStore, ih, entryStore_reg]
    simp [Ne.symm (l.fresh 2), Ne.symm (l.fresh 3), Ne.symm (l.fresh 4), Ne.symm (l.fresh 5),
      TapeProgram.decStore, Nat.sub_sub, Nat.add_comm]

 theorem fillStore_clean (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hc : Clean l.random d) : Clean l.random (fillStore l b inp n d) := by
  induction n generalizing d with
  | zero => exact hc
  | succ n ih => exact ih _ (entryStore_clean _ _ _ _)

 





 





 theorem entryStore_ell (l : Layout R) (b : Fin B) (inp : Inputs) (d : TapeStore R B) :
    (entryStore l.random b inp (TapeProgram.decStore l.count d)).reg l.random.ell = d.reg l.random.ell := by
  rw [entryStore_reg]
  simp [RandomBits.Layout.ell, RandomBits.Layout.acc, RandomBits.Layout.count,
    RandomBits.Layout.tmp, RandomBits.Layout.scratch, TapeProgram.decStore, l.fresh 0]

 theorem entryStore_q (l : Layout R) (b : Fin B) (inp : Inputs) (d : TapeStore R B) :
    (entryStore l.random b inp (TapeProgram.decStore l.count d)).reg l.random.q = d.reg l.random.q := by
  rw [entryStore_reg]
  simp [RandomBits.Layout.q, RandomBits.Layout.acc, RandomBits.Layout.count,
    RandomBits.Layout.tmp, RandomBits.Layout.scratch, TapeProgram.decStore, l.fresh 1]

 theorem fillStore_roHead (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (fillStore l b inp n d).roHead =
      Function.update d.roHead 3 (d.roHead 3+n*d.reg l.random.ell) := by
  induction n generalizing d with
  | zero => simp [fillStore]
  | succ n ih =>
    rw [fillStore, ih, entryStore_ell, entryStore_roHead]
    simp only [TapeProgram.decStore, Function.update_of_ne (l.fresh 0),
      Function.update_self, Function.update_idem]
    congr 1
    ring

 theorem fillStore_head (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hq : d.reg l.random.q = 2^(d.reg l.random.ell)) :
    (fillStore l b inp n d).bufferHead =
      Function.update d.bufferHead b (d.bufferHead b+n*d.reg l.random.q) := by
  induction n generalizing d with
  | zero => simp [fillStore]
  | succ n ih =>
    have hq₁ : (TapeProgram.decStore l.count d).reg l.random.q =
        2^((TapeProgram.decStore l.count d).reg l.random.ell) := by
      simpa [TapeProgram.decStore, l.fresh 0, l.fresh 1] using hq
    have hq₂ : (entryStore l.random b inp (TapeProgram.decStore l.count d)).reg l.random.q =
        2^((entryStore l.random b inp (TapeProgram.decStore l.count d)).reg l.random.ell) := by
      rw [entryStore_q, entryStore_ell]
      exact hq
    rw [fillStore, ih _ hq₂, entryStore_q, entryStore_head _ _ _ _ hq₁]
    simp only [TapeProgram.decStore, Function.update_of_ne (l.fresh 1),
      Function.update_self, Function.update_idem]
    congr 1
    ring

 theorem fillStore_output (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B) :
    (fillStore l b inp n d).output = d.output := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [fillStore, ih, entryStore_output]

/-- Every physical cell outside the filled interval is preserved. -/
 theorem fillStore_outside (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hq : d.reg l.random.q = 2^(d.reg l.random.ell)) (c : Fin B) (k : ℕ)
    (hout : c ≠ b ∨ k < d.bufferHead b ∨ d.bufferHead b+n*d.reg l.random.q ≤ k) :
    ((fillStore l b inp n d).bufferTape c).getD k .blank = (d.bufferTape c).getD k .blank := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    let e := entryStore l.random b inp (TapeProgram.decStore l.count d)
    have hq₁ : (TapeProgram.decStore l.count d).reg l.random.q =
        2^((TapeProgram.decStore l.count d).reg l.random.ell) := by
      simpa [TapeProgram.decStore, l.fresh 0, l.fresh 1] using hq
    have hq₂ : e.reg l.random.q = 2^(e.reg l.random.ell) := by
      rw [entryStore_q, entryStore_ell]
      exact hq
    have hh : e.bufferHead b = d.bufferHead b+d.reg l.random.q := by
      rw [entryStore_head _ _ _ _ hq₁]
      simp [TapeProgram.decStore, l.fresh 1]
    have hrq : e.reg l.random.q = d.reg l.random.q := entryStore_q l b inp d
    have heout : c ≠ b ∨ k < e.bufferHead b ∨ e.bufferHead b+n*e.reg l.random.q ≤ k := by
      rw [hh, hrq]
      rcases hout with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by nlinarith [Nat.add_mul n 1 (d.reg l.random.q)]))
    rw [fillStore, ih e hq₂ heout, entryStore_symbol _ _ _ _ hq₁]
    have hnot : ¬ (c = b ∧ d.bufferHead b ≤ k ∧ k < d.bufferHead b+d.reg l.random.q) := by
      rcases hout with h | h | h
      · tauto
      · omega
      · intro hc
        nlinarith [Nat.zero_le (n*d.reg l.random.q), Nat.add_mul n 1 (d.reg l.random.q)]
    simpa [TapeProgram.decStore, l.fresh 1, hnot]

/-- Each contiguous q-cell block stores exactly the index from its ell-bit
randomness block, including arbitrary starting heads and input suffixes. -/
 theorem fillStore_table (l : Layout R) (b : Fin B) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hq : d.reg l.random.q = 2^(d.reg l.random.ell)) (i j : ℕ)
    (hi : i < n) (hj : j < d.reg l.random.q) :
    ((fillStore l b inp n d).bufferTape b).getD (d.bufferHead b+i*d.reg l.random.q+j) .blank =
      if j < RandomBits.value inp (d.reg l.random.ell) (d.roHead 3+i*d.reg l.random.ell) 0
      then .one else .zero := by
  induction n generalizing d i with
  | zero => omega
  | succ n ih =>
    let e := entryStore l.random b inp (TapeProgram.decStore l.count d)
    have hq₁ : (TapeProgram.decStore l.count d).reg l.random.q =
        2^((TapeProgram.decStore l.count d).reg l.random.ell) := by
      simpa [TapeProgram.decStore, l.fresh 0, l.fresh 1] using hq
    have hq₂ : e.reg l.random.q = 2^(e.reg l.random.ell) := by
      rw [entryStore_q, entryStore_ell]
      exact hq
    have hh : e.bufferHead b = d.bufferHead b+d.reg l.random.q := by
      rw [entryStore_head _ _ _ _ hq₁]
      simp [TapeProgram.decStore, l.fresh 1]
    have hro : e.roHead 3 = d.roHead 3+d.reg l.random.ell := by
      rw [entryStore_roHead]
      simp [TapeProgram.decStore, l.fresh 0]
    rw [fillStore]
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.add_zero]
      rw [fillStore_outside l b inp n e hq₂ b (d.bufferHead b+j)
        (Or.inr (Or.inl (by rw [hh]; omega)))]
      rw [entryStore_symbol _ _ _ _ hq₁]
      simp only [TapeProgram.decStore, Function.update_of_ne (l.fresh 1),
        Function.update_of_ne (l.fresh 0)]
      have h₁ : d.bufferHead b ≤ d.bufferHead b+j := by omega
      have h₂ : d.bufferHead b+j < d.bufferHead b+d.reg l.random.q := by omega
      have h₃ : d.bufferHead b+j < d.bufferHead b+RandomBits.value inp (d.reg l.random.ell) (d.roHead 3) 0 ↔
          j < RandomBits.value inp (d.reg l.random.ell) (d.roHead 3) 0 := by omega
      simp [h₁, h₂, h₃]
    | succ i =>
      have hi' : i < n := by omega
      have hj' : j < e.reg l.random.q := by rw [entryStore_q]; exact hj
      have ht := ih e hq₂ i hi' hj'
      rw [entryStore_q, entryStore_ell, hh, hro] at ht
      convert ht using 1 <;> congr 2 <;> ring

open ExpandingCodes.PolynomialStretch



















 



 














 

























 theorem fillStore_sampledValues (l : Layout R) (b : Fin B) (inp : Inputs) (K : ℕ)
    (d : TapeStore R B) (hq : d.reg l.random.q = 2^(d.reg l.random.ell)) (i : Fin K) :
    TapeArrays.ThermometerAt (fillStore l b inp K d) b
      (d.bufferHead b+i.val*d.reg l.random.q) (d.reg l.random.q)
      (sampledValues inp K (d.reg l.random.ell) (d.roHead 3) i).val := by
  constructor
  · change RandomBits.value inp _ _ 0 ≤ d.reg l.random.q
    rw [hq]
    exact (by simpa using (RandomBits.value_lt inp (d.reg l.random.ell)
      (d.roHead 3+i.val*d.reg l.random.ell) 0).le)
  · intro j hj
    exact fillStore_table l b inp K d hq i.val j i.isLt hj








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






























































theorem toggleStore_fresh (x y p j : Fin R) (d : TapeStore R B)
    (hjx : j ≠ x) (hjy : j ≠ y) (hjp : j ≠ p) :
    (toggleStore x y p d).reg j = d.reg j := by
  simp only [toggleStore]
  split <;> simp_all [TapeStore.setReg]
  split <;> simp_all [TapeStore.setReg]

















































































theorem testBitStore_fresh (r : Fin 7 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₂ : j ≠ r 2) (h₃ : j ≠ r 3) (h₄ : j ≠ r 4)
    (h₅ : j ≠ r 5) (h₆ : j ≠ r 6) :
    (testBitStore r d).reg j = d.reg j := by
  simp only [testBitStore, halfStore, TapeStore.setReg, Function.update_of_ne h₂,
    Function.update_of_ne h₃, Function.update_of_ne h₄]
  rw [shiftStore_fresh _ _ _ _ _ h₂ h₃ h₄ h₅]
  simp [bitPrepare, TapeStore.setReg, h₂, h₅, h₆]








theorem bodyStore_fresh (r : Fin 12 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₃ : j ≠ r 3) (h₄ : j ≠ r 4) (h₆ : j ≠ r 6) (h₇ : j ≠ r 7)
    (h₈ : j ≠ r 8) (h₉ : j ≠ r 9) (h₁₀ : j ≠ r 10) (h₁₁ : j ≠ r 11) :
    (bodyStore r d).reg j = d.reg j := by
  unfold bodyStore
  simp only [TapeStore.setReg, Function.update_of_ne h₄]
  rw [toggleStore_fresh _ _ _ _ _ h₆ h₇ h₃]
  rw [testBitStore_fresh _ _ _ h₈ h₉ h₇ h₁₀ h₁₁]
  exact testBitStore_fresh _ _ _ h₈ h₉ h₆ h₁₀ h₁₁















































































































































theorem loopStore_fresh (r : Fin 12 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₃ : j ≠ r 3) (h₄ : j ≠ r 4) (h₅ : j ≠ r 5)
    (h₆ : j ≠ r 6) (h₇ : j ≠ r 7) (h₈ : j ≠ r 8) (h₉ : j ≠ r 9)
    (h₁₀ : j ≠ r 10) (h₁₁ : j ≠ r 11) (n : ℕ) :
    (loopStore r n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [loopStore, ih, bodyStore_fresh r _ j h₃ h₄ h₆ h₇ h₈ h₉ h₁₀ h₁₁]
    simp [TapeStore.setReg, h₅]



































































































































































































@[simp] theorem tapeData_setReg (d : TapeStore R B) (i : Fin R) (n : ℕ) :
    tapeData (d.setReg i n) = tapeData d := rfl





























































theorem convolutionStore_fresh (r : Fin 12 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₃ : j ≠ r 3) (h₄ : j ≠ r 4) (h₅ : j ≠ r 5)
    (h₆ : j ≠ r 6) (h₇ : j ≠ r 7) (h₈ : j ≠ r 8) (h₉ : j ≠ r 9)
    (h₁₀ : j ≠ r 10) (h₁₁ : j ≠ r 11) :
    (convolutionStore r d).reg j = d.reg j := by
  rw [convolutionStore, loopStore_fresh r _ j h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁]
  simp [prepareStore, TapeStore.setReg, h₃, h₄, h₅, h₁₁]





































































end ExpandingCodes.Computation.FieldConvolution

end FlattenModule49

/-! Inlined whole module: ExpandingCodes.Computation.FieldCertificates -/
section FlattenModule50


set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.FieldCertificates
open NKtLB FieldPrograms FieldConvolution
open ExpandingCodes.PolynomialStretch
open BinaryPolynomial
variable {R B : ℕ}




































theorem xorStore_fresh (x unit p j : Fin R) (d : TapeStore R B)
    (hjx : j ≠ x) (hju : j ≠ unit) (hjp : j ≠ p) :
    (xorStore x unit p d).reg j = d.reg j := by
  rw [xorStore, toggleStore_fresh x unit p j _ hjx hju hjp]
  simp [TapeStore.setReg, hju]















































theorem requireStore_fresh (x flag j : Fin R) (d : TapeStore R B)
    (hjx : j ≠ x) (hjf : j ≠ flag) : (requireStore x flag d).reg j = d.reg j := by
  unfold requireStore
  split <;> simp_all [TapeStore.setReg]






































































































































































































































































theorem coefficientStore_register (r : Fin 18 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₆ : j ≠ r 6) (h₇ : j ≠ r 7) (h₈ : j ≠ r 8) (h₉ : j ≠ r 9)
    (h₁₀ : j ≠ r 10) (h₁₁ : j ≠ r 11) (h₁₂ : j ≠ r 12) (h₁₃ : j ≠ r 13)
    (h₁₄ : j ≠ r 14) (h₁₅ : j ≠ r 15) (h₁₆ : j ≠ r 16) (h₁₇ : j ≠ r 17) :
    (coefficientStore r d).reg j = d.reg j := by
  unfold coefficientStore
  rw [requireStore_fresh _ _ _ _ h₇ h₆,
    xorStore_fresh _ _ _ _ _ h₉ h₁₆ h₇, xorStore_fresh _ _ _ _ _ h₈ h₁₆ h₇,
    testBitStore_fresh _ _ _ h₁₄ h₁₅ h₉ h₁₆ h₁₇,
    convolutionStore_fresh _ _ _ h₈ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆ h₁₇,
    convolutionStore_fresh _ _ _ h₇ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆ h₁₇]








































































































































































































































































































































theorem certificateStore_outside (r : Fin 19 → Fin R) (n : ℕ) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 19, j ≠ r i) :
    (certificateStore r n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [certificateStore, ih]
    unfold stepStore
    simp only [TapeStore.setReg, Function.update_of_ne (hne 5)]
    rw [coefficientStore_register _ _ _ (hne 6) (hne 7) (hne 8) (hne 9) (hne 10) (hne 11)
      (hne 12) (hne 13) (hne 14) (hne 15) (hne 16) (hne 17)]
    simp [TapeStore.setReg, hne 18]































































































































































































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










































































































































theorem commitStore_fresh (r : Fin 5 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₁ : j ≠ r 1) (h₂ : j ≠ r 2) (h₃ : j ≠ r 3) (h₄ : j ≠ r 4) :
    (commitStore r d).reg j = d.reg j := by
  unfold commitStore
  split <;> simp_all [commitBodyStore, TapeStore.setReg]



















theorem certificateResult_outside (r : Fin 20 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 20, j ≠ r i) :
    (certificateResult r d).reg j = d.reg j := by
  rw [certificateResult, certificateStore_outside]
  · simp [FieldCertificates.prepareStore, TapeStore.setReg, hne 5, hne 6, hne 17, hne 18]
  · intro i
    exact hne i.castSucc














































theorem loopResult_frame (counter : Fin R) (F : TapeStore R B → TapeStore R B)
    (j : Fin R) (hj : j ≠ counter) (hF : ∀ d, (F d).reg j = d.reg j)
    (n : ℕ) (d : TapeStore R B) : (loopResult counter F n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [loopResult, ih, hF]
    simp [TapeStore.setReg, hj]











































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































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





















































































































end ExpandingCodes.Computation.EncodedTester

namespace ExpandingCodes.PolynomialStretch

open Computation EncodedGaussian EncodedTester








@[simp] theorem encodedExponentOrder_val {d n : ℕ} (g : Geometry d n)
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

/-! Inlined whole module: ExpandingCodes.Computation.ParameterPower -/
section FlattenModule65


set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}











theorem powerStepStore_value (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) :
    (powerStepStore r d).reg (r 1) = d.reg (r 0)*d.reg (r 1) := by
  simp [powerStepStore, multiplyStore, reg_layout r hr]

theorem powerStepStore_base (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (powerStepStore r d).reg (r 0) = d.reg (r 0) := by
  simp [powerStepStore, multiplyStore, reg_layout r hr]

theorem powerStepStore_count (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (powerStepStore r d).reg (r 5) = d.reg (r 5) := by
  simp [powerStepStore, multiplyStore, reg_layout r hr]

theorem powerStepStore_bound (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (M : ℕ) (hd : ∀ j, d.reg j ≤ M)
    (hp : d.reg (r 0)*d.reg (r 1) ≤ M) :
    ∀ j, (powerStepStore r d).reg j ≤ M := by
  dsimp [powerStepStore, multiplyStore]
  apply setReg_bound _ _ 0 M
  · apply setReg_bound
    · apply setReg_bound _ _ 0 M
      · apply setReg_bound _ _ 0 M
        · exact setReg_bound d _ _ M hd hp
        · omega
      · omega
    · simpa [multiplyStore, reg_layout r hr] using hp
  · omega

theorem powerStep_stops (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hp : d.reg (r 0)*d.reg (r 1) ≤ M) :
    ∃ t e, t ≤ 64*(M+1)^2 ∧
      (powerStep r).Stops inp (d.toCfg (powerStep (B := B) r).entry) t e ∧
      e.store = powerStepStore r d := by
  obtain ⟨t, c, ht, hc, hcs⟩ := multiply_stops_polynomial (r 0) (r 1) (r 2) (r 3) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    inp d M (hd _) (hd _) (hd _) (hd _) (hd _)
  have hcb : ∀ j, c.reg j ≤ M := by
    change ∀ j, c.store.reg j ≤ M
    rw [hcs]
    exact setReg_bound _ _ 0 M
      (setReg_bound _ _ 0 M (setReg_bound d _ _ M hd hp) (by omega)) (by omega)
  obtain ⟨e, he, hes⟩ := TapeMacros.copy_stops (r 2) (r 1) (r 3)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c.store
  have hall := hc.seq he
  refine ⟨_, _, ?_, hall, ?_⟩
  · have hcopy : c.reg (r 1)+c.reg (r 3)+5*c.reg (r 2)+7 ≤ 7*M+7 := by
      have := hcb (r 1); have := hcb (r 3); have := hcb (r 2); omega
    simp only [TapeCfg.store]
    nlinarith
  · change e.store = _
    rw [hes, hcs]
    rfl










theorem powerLoopStore_base (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) :
    (powerLoopStore r n d).reg (r 0) = d.reg (r 0) := by
  induction n generalizing d with
  | zero => simp [powerLoopStore, reg_layout r hr]
  | succ n ih =>
    rw [powerLoopStore, ih, powerStepStore_base r hr]
    simp [reg_layout r hr]

theorem powerLoopStore_value (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) :
    (powerLoopStore r n d).reg (r 1) = d.reg (r 0)^n*d.reg (r 1) := by
  induction n generalizing d with
  | zero => simp [powerLoopStore, reg_layout r hr]
  | succ n ih =>
    rw [powerLoopStore, ih, powerStepStore_base r hr, powerStepStore_value r hr]
    simp [reg_layout r hr, pow_succ]
    ring







/-- Bound each intermediate unary multiplication result by its eventual power.
The base positivity assumption is satisfied by both mission bases n and q. -/
theorem powerLoop_stops (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M n : ℕ) (d : TapeStore R B)
    (hn : d.reg (r 5) = n) (ha : 1 ≤ d.reg (r 0))
    (hd : ∀ j, d.reg j ≤ M) (hp : d.reg (r 0)^n*d.reg (r 1) ≤ M) :
    ∃ t, t ≤ n*(64*(M+1)^2+2)+1 ∧
      (powerLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 35)) t
        ((powerLoopStore r n d).toCfg (TapeProgram.loopExit 35)) ∧
      ∀ j, (powerLoopStore r n d).reg j ≤ M := by
  induction n generalizing d with
  | zero =>
    have he : d.setReg (r 5) 0 = d := by simp [TapeStore.setReg, ← hn]
    exact ⟨1, by omega, by simpa [powerLoop, powerLoopStore, he] using
      TapeProgram.loop_zero (powerStep r) (r 5) inp d hn,
      by simpa [powerLoopStore, he] using hd⟩
  | succ n ih =>
    let d₁ := d.setReg (r 5) n
    have hd₁ : ∀ j, d₁.reg j ≤ M := setReg_bound d _ n M hd (by have := hd (r 5); omega)
    have hprod : d₁.reg (r 0)*d₁.reg (r 1) ≤ M := by
      have hpw : 1 ≤ d.reg (r 0)^n := Nat.one_le_pow n _ ha
      have hle : d.reg (r 0)*d.reg (r 1) ≤ d.reg (r 0)^(n+1)*d.reg (r 1) := by
        rw [pow_succ]
        simpa using Nat.mul_le_mul_right (d.reg (r 1))
          (Nat.mul_le_mul_right (d.reg (r 0)) hpw)
      simpa [d₁, reg_layout r hr] using hle.trans hp
    obtain ⟨s, c, hs, hc, hcs⟩ := powerStep_stops r hr inp M d₁ hd₁ hprod
    have hcb : ∀ j, c.reg j ≤ M := by
      change ∀ j, c.store.reg j ≤ M
      rw [hcs]
      exact powerStepStore_bound r hr d₁ M hd₁ hprod
    have hcn : c.reg (r 5) = n := by
      change c.store.reg (r 5) = n
      rw [hcs, powerStepStore_count r hr]
      simp [d₁]
    have hca : 1 ≤ c.reg (r 0) := by
      change 1 ≤ c.store.reg (r 0)
      rw [hcs, powerStepStore_base r hr]
      simpa [d₁, reg_layout r hr] using ha
    have hcp : c.reg (r 0)^n*c.reg (r 1) ≤ M := by
      change c.store.reg (r 0)^n*c.store.reg (r 1) ≤ M
      rw [hcs, powerStepStore_base r hr, powerStepStore_value r hr]
      simpa [d₁, reg_layout r hr, pow_succ, Nat.mul_assoc] using hp
    obtain ⟨t, ht, htail, htb⟩ := ih c.store hcn hca hcb hcp
    have hhead := TapeProgram.loop_positive_header (powerStep r) (r 5) inp d (by omega)
    have hdec : TapeProgram.decStore (r 5) d = d₁ := by
      simp [TapeProgram.decStore, d₁, TapeStore.setReg, hn]
    rw [hdec] at hhead
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2) (TapeProgram.loop_code_body_active (powerStep r) (r 5))
    have hreturn := TapeProgram.loop_body_return (powerStep r) (r 5) inp c hc.halted
    have hpost : powerLoopStore r n c.store = powerLoopStore r (n+1) d := by
      rw [powerLoopStore, hcs]
    have hall := ((hhead.trans hrun).trans hreturn).trans htail.exec
    rw [hpost] at hall
    refine ⟨_, ?_, ⟨hall, TapeProgram.loop_code_exit (powerStep r) (r 5)⟩, ?_⟩
    · nlinarith
    · rwa [hpost] at htb















theorem fixedPowerStore_value (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (e : ℕ) (d : TapeStore R B) :
    (fixedPowerStore r e d).reg (r 1) = d.reg (r 0)^e := by
  simp [fixedPowerStore, powerLoopStore_value r hr, powerPrepare, reg_layout r hr]

theorem fixedPowerStore_base (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (e : ℕ) (d : TapeStore R B) :
    (fixedPowerStore r e d).reg (r 0) = d.reg (r 0) := by
  simp [fixedPowerStore, powerLoopStore_base r hr, powerPrepare, reg_layout r hr]

theorem fixedPower_stops (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (e : ℕ) (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) (ha : 1 ≤ d.reg (r 0)) :
    ∃ t z, t ≤ 512*(e+1)^3*(M+1)^(2*(e+1)) ∧
      (fixedPower r e).Stops inp (d.toCfg (fixedPower (B := B) r e).entry) t z ∧
      z.store = fixedPowerStore r e d ∧
      ∀ j, z.reg j ≤ (e+1)*(M+1)^(e+1) := by
  let K := (e+1)*(M+1)^(e+1)
  have hpow₁ : M+1 ≤ (M+1)^(e+1) := by
    simpa using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1≤e+1 by omega)
  have hpowpos : 1 ≤ (M+1)^(e+1) := Nat.one_le_pow _ _ (by omega)
  have hKM : M ≤ K := by dsimp [K]; nlinarith
  have hKe : e ≤ K := by dsimp [K]; nlinarith
  obtain ⟨c, hc, hcs⟩ := loadConstant_stops (r 1) 1 inp d
  obtain ⟨f, hf, hfs⟩ := loadConstant_stops (r 5) e inp c.store
  have hpre : f.store = powerPrepare r e d := by rw [hfs, hcs]; rfl
  have hbd : ∀ j, f.reg j ≤ K := by
    change ∀ j, f.store.reg j ≤ K
    rw [hpre]
    exact setReg_bound _ _ e K
      (setReg_bound d _ 1 K (fun j => (hd j).trans hKM) (by omega)) hKe
  have hn : f.reg (r 5) = e := by change f.store.reg (r 5) = _; rw [hpre]; simp [powerPrepare]
  have hbase : f.reg (r 0) = d.reg (r 0) := by
    change f.store.reg (r 0) = _; rw [hpre]; simp [powerPrepare, reg_layout r hr]
  have hp : f.reg (r 0)^e*f.reg (r 1) ≤ K := by
    have hpw : d.reg (r 0)^e ≤ (M+1)^(e+1) :=
      (Nat.pow_le_pow_left (by have := hd (r 0); omega) e).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
    change f.store.reg (r 0)^e*f.store.reg (r 1) ≤ K
    rw [hpre]
    simp only [powerPrepare, reg_layout r hr]
    simp only [show (0 : Fin 6) ≠ 5 from by decide, show (0 : Fin 6) ≠ 1 from by decide,
      show (1 : Fin 6) ≠ 5 from by decide, ite_false, ite_true, Nat.mul_one]
    dsimp [K]
    nlinarith
  obtain ⟨t, ht, hloop, hzb⟩ := powerLoop_stops r hr inp K e f.store hn
    (by simpa [TapeCfg.store, hbase] using ha) hbd hp
  have hall := (hc.seq hf).seq hloop
  refine ⟨_, _, ?_, hall, ?_, ?_⟩
  · have hct : c.reg (r 5) = d.reg (r 5) := by
      change c.store.reg (r 5) = _; rw [hcs]; simp [reg_layout r hr]
    have h₁ := hd (r 1)
    have h₅ := hd (r 5)
    have hKpos : 1 ≤ K := by omega
    have hKP : K^2 = (e+1)^2*(M+1)^(2*(e+1)) := by
      dsimp [K]
      rw [mul_pow, ← pow_mul]
      congr 2
      omega
    have hsq : (K+1)^2 ≤ 4*K^2 := by nlinarith
    have hKsq : K ≤ K^2 := by nlinarith
    have hbody : 64*(K+1)^2+2 ≤ 258*K^2 := by nlinarith
    have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left e hbody) 1)
    have hsmall : 2*M+2*e+9 ≤ 13*(e+1)*K^2 := by nlinarith
    have hgoal : 512*(e+1)^3*(M+1)^(2*(e+1)) = 512*(e+1)*K^2 := by
      rw [hKP]
      ring
    rw [hgoal]
    simp only [TapeCfg.store, hct]
    nlinarith
  · change powerLoopStore r e f.store = fixedPowerStore r e d
    rw [hpre]
    rfl
  · change ∀ j, (powerLoopStore r e f.store).reg j ≤ K
    exact hzb





end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule65

/-! Inlined whole module: ExpandingCodes.Computation.SizeParameters -/
section FlattenModule66


set_option autoImplicit false
namespace ExpandingCodes.Computation
namespace SizeParameters











/-- A p-step budget is sufficient: every active doubling increases q by at
least one. The separate q<2p invariant bounds all unary arithmetic values. -/
theorem ceilIter_invariant (p t q ell : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hb : q<2*p) (he : q=2^ell)
    (hbudget : p ≤ q+t) (hell : ell+t ≤ p) :
    p ≤ (ceilIter p t (q,ell)).1 ∧ (ceilIter p t (q,ell)).1<2*p ∧
      (ceilIter p t (q,ell)).1=2^(ceilIter p t (q,ell)).2 ∧
      (ceilIter p t (q,ell)).2 ≤ p := by
  induction t generalizing q ell with
  | zero => simpa [ceilIter] using And.intro hbudget ⟨hb,he,hell⟩
  | succ t ih =>
    by_cases hlt : q<p
    · have he' : 2*q=2^(ell+1) := by rw [pow_succ, ← he]; omega
      have ht := ih (2*q) (ell+1) (by omega) (by omega) he' (by omega) (by omega)
      simpa [ceilIter, ceilStep, hlt] using ht
    · have ht := ih q ell hq hb he (by omega) (by omega)
      simpa [ceilIter, ceilStep, hlt] using ht

theorem power_clog_unique (p ell : ℕ) (hp : p ≤ 2^ell) (hb : 2^ell<2*p) :
    ell=Nat.clog 2 p := by
  have hle : Nat.clog 2 p ≤ ell := (Nat.clog_le_iff_le_pow (by decide)).mpr hp
  apply Nat.le_antisymm _ hle
  by_contra hn
  have ht : Nat.clog 2 p+1 ≤ ell := by omega
  have hpw := Nat.pow_le_pow_right (show 0<2 by decide) ht
  have hpc := Nat.le_pow_clog (by decide : 1<2) p
  rw [pow_succ] at hpw
  omega

theorem ceilIter_exact (p : ℕ) (hp : 1 ≤ p) :
    ceilIter p p (1,0) = (2^Nat.clog 2 p,Nat.clog 2 p) := by
  have h := ceilIter_invariant p p 1 0 hp (by omega) (by omega) rfl (by omega) (by omega)
  have he := power_clog_unique p (ceilIter p p (1,0)).2
    (by simpa only [← h.2.2.1] using h.1) (by simpa only [← h.2.2.1] using h.2.1)
  apply Prod.ext
  · simpa [he] using h.2.2.1
  · exact he





















































end SizeParameters
end ExpandingCodes.Computation

end FlattenModule66

/-! Inlined whole module: ExpandingCodes.Computation.ParameterRounding -/
section FlattenModule67



set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}












theorem doubleBody_stops (q ell copy tmp : Fin R)
    (hqe : q≠ell) (hqc : q≠copy) (hqt : q≠tmp)
    (hec : ell≠copy) (het : ell≠tmp) (hct : copy≠tmp)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (doubleBody q ell copy tmp).Stops inp
      (d.toCfg (doubleBody (B := B) q ell copy tmp).entry)
      (d.reg copy+d.reg tmp+10*d.reg q+15) e ∧
      e.store=doubleBodyStore q ell copy tmp d := by
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops q copy tmp hqc hqt hct inp d
  obtain ⟨f, hf, hfs⟩ := TapeMacros.addPreserving_stops copy q tmp
    (Ne.symm hqc) hct hqt inp c.store
  have hg := TapeMacros.increment_stops ell inp f.store
  have hall := (hc.seq hf).seq hg
  refine ⟨((f.store.setReg ell (f.reg ell+1)).toCfg (1 : Fin 2)).mapPC (TapeProgram.rightLabel 20), ?_, ?_⟩
  · have htmp : c.reg tmp=0 := by change c.store.reg tmp=0; rw [hcs]; simp
    have hcopy : c.reg copy=d.reg q := by
      change c.store.reg copy=_; rw [hcs]; simp [TapeStore.setReg, hct]
    convert hall using 1 <;> first | rfl | simp only [TapeCfg.store, htmp, hcopy]; omega
  · change (f.store.setReg ell (f.store.reg ell+1)) = _
    rw [hfs, hcs]
    rfl




theorem ceilCompareLayout_injective (r : Fin 8 → Fin R) (hr : Function.Injective r) :
    Function.Injective (ceilCompareLayout r) := by
  intro i j hij
  have hv := congrArg Fin.val (hr hij)
  exact Fin.ext hv










theorem ceilConditional_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) (hflag : d.reg (r 2) ≤ 1) :
    ∃ t, t ≤ 12*M+18 ∧
      (ceilConditional r).Stops inp (d.toCfg (TapeProgram.loopHeader 22)) t
        ((ceilConditionalStore r d).toCfg (TapeProgram.loopExit 22)) := by
  by_cases hz : d.reg (r 2)=0
  · exact ⟨1, by omega, by simpa [ceilConditional, ceilConditionalStore, hz] using
      TapeProgram.loop_zero (doubleBody (r 0) (r 6) (r 3) (r 5)) (r 2) inp d hz⟩
  · have hone : d.reg (r 2)=1 := by omega
    let d₁ := d.setReg (r 2) 0
    obtain ⟨c, hc, hcs⟩ := doubleBody_stops (r 0) (r 6) (r 3) (r 5)
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d₁
    have hcz : c.reg (r 2)=0 := by
      change c.store.reg (r 2)=0
      rw [hcs]
      simp [doubleBodyStore, d₁, reg_layout r hr]
    have hhead := TapeProgram.loop_positive_header
      (doubleBody (r 0) (r 6) (r 3) (r 5)) (r 2) inp d hz
    have hdec : TapeProgram.decStore (r 2) d=d₁ := by
      simp [TapeProgram.decStore, d₁, TapeStore.setReg, hone]
    rw [hdec] at hhead
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (doubleBody (r 0) (r 6) (r 3) (r 5)) (r 2))
    have hreturn := TapeProgram.loop_body_return
      (doubleBody (r 0) (r 6) (r 3) (r 5)) (r 2) inp c hc.halted
    have htail := TapeProgram.loop_zero
      (doubleBody (r 0) (r 6) (r 3) (r 5)) (r 2) inp c.store hcz
    have hall := ((hhead.trans hrun).trans hreturn).trans htail.exec
    have hpost : c.store=ceilConditionalStore r d := by
      simp only [ceilConditionalStore, hz, ↓reduceIte]
      exact hcs
    rw [hpost] at hall
    refine ⟨_, ?_, ⟨hall, TapeProgram.loop_code_exit _ _⟩⟩
    have hq := hd (r 0); have hcopy := hd (r 3); have htmp := hd (r 5)
    simp [d₁, reg_layout r hr]
    omega









theorem ceilingStep_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 128*(M+1) ∧
      (ceilingStep r).Stops inp (d.toCfg (ceilingStep (B := B) r).entry) t e ∧
      e.store=ceilingStepStore r d := by
  have hr' := ceilCompareLayout_injective r hr
  obtain ⟨t, c, ht, hc, hcs⟩ := lessThan_stops (ceilCompareLayout r) hr' inp M hM d hd
  have hcb : ∀ j, c.reg j ≤ M := by
    change ∀ j, c.store.reg j ≤ M
    rw [hcs]
    exact lessThanStore_bound _ hr' d M hM hd
  have hf : c.reg (r 2) ≤ 1 := by
    change c.store.reg (ceilCompareLayout r 2) ≤ 1
    rw [hcs, lessThanStore_value _ hr']
    split <;> omega
  obtain ⟨s, hs, he⟩ := ceilConditional_stops r hr inp M c.store hcb hf
  have hall := hc.seq he
  refine ⟨_, _, ?_, hall, ?_⟩
  · omega
  · change ceilConditionalStore r c.store=ceilingStepStore r d
    rw [hcs]
    rfl







theorem tapeStore_ext (d e : TapeStore R B)
    (hr : d.reg=e.reg) (hh : d.roHead=e.roHead) (ho : d.output=e.output)
    (hb : d.bufferTape=e.bufferTape) (hbh : d.bufferHead=e.bufferHead) : d=e := by
  cases d
  cases e
  cases hr
  cases hh
  cases ho
  cases hb
  cases hbh
  rfl

theorem ceilingStepStore_flat (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : ceilingStepStore r d=ceilingStepFlatStore r d := by
  have hv : (lessThanStore (ceilCompareLayout r) d).reg (r 2) =
      if d.reg (r 0)<d.reg (r 1) then 1 else 0 :=
    lessThanStore_value _ (ceilCompareLayout_injective r hr) d
  unfold ceilingStepStore ceilConditionalStore
  rw [hv]
  by_cases hlt : d.reg (r 0)<d.reg (r 1)
  all_goals
    simp only [hlt, if_true, if_false, Nat.one_ne_zero]
    apply tapeStore_ext
    · funext j
      by_cases h₀ : j=r 0
      · subst j; simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
          doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
          ceilCompareLayout, reg_layout r hr, hlt, two_mul]
      · by_cases h₂ : j=r 2
        · subst j; simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
            doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
            ceilCompareLayout, reg_layout r hr, hlt]
        · by_cases h₃ : j=r 3
          · subst j; simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
              doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
              ceilCompareLayout, reg_layout r hr, hlt]
          · by_cases h₄ : j=r 4
            · subst j; simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
                doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
                ceilCompareLayout, reg_layout r hr, hlt]
            · by_cases h₅ : j=r 5
              · subst j; simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
                  doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
                  ceilCompareLayout, reg_layout r hr, hlt]
              · by_cases h₆ : j=r 6
                · subst j; simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
                    doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
                    ceilCompareLayout, reg_layout r hr, hlt]
                · simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
                    doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
                    ceilCompareLayout, reg_layout r hr, hlt, TapeStore.setReg,
                    h₀, h₂, h₃, h₄, h₅, h₆]
  
    all_goals simp [ceilingStepStore, ceilingStepFlatStore, ceilConditionalStore,
      doubleBodyStore, lessThanStore, lessCore, lessPrepare, ltLoopStore,
      ceilCompareLayout, reg_layout r hr, hlt, TapeStore.setReg]

theorem ceilingStepStore_q (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (ceilingStepStore r d).reg (r 0) =
      if d.reg (r 0)<d.reg (r 1) then 2*d.reg (r 0) else d.reg (r 0) := by
  rw [ceilingStepStore_flat r hr]
  by_cases hlt : d.reg (r 0)<d.reg (r 1)
  all_goals simp [ceilingStepFlatStore, reg_layout r hr, hlt]

theorem ceilingStepStore_ell (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (ceilingStepStore r d).reg (r 6) =
      if d.reg (r 0)<d.reg (r 1) then d.reg (r 6)+1 else d.reg (r 6) := by
  rw [ceilingStepStore_flat r hr]
  by_cases hlt : d.reg (r 0)<d.reg (r 1)
  all_goals simp [ceilingStepFlatStore, reg_layout r hr, hlt]

theorem ceilingStepStore_p (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (ceilingStepStore r d).reg (r 1)=d.reg (r 1) := by
  rw [ceilingStepStore_flat r hr]
  by_cases hlt : d.reg (r 0)<d.reg (r 1)
  all_goals simp [ceilingStepFlatStore, reg_layout r hr, hlt]

theorem ceilingStepStore_count (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (ceilingStepStore r d).reg (r 7)=d.reg (r 7) := by
  rw [ceilingStepStore_flat r hr]
  by_cases hlt : d.reg (r 0)<d.reg (r 1)
  all_goals simp [ceilingStepFlatStore, reg_layout r hr, hlt]

theorem ceilingStepStore_bound (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (M : ℕ) (hd : ∀ j, d.reg j≤M)
    (hactive : d.reg (r 0)<d.reg (r 1) →
      2*d.reg (r 0)≤M ∧ d.reg (r 6)+1≤M) :
    ∀ j, (ceilingStepStore r d).reg j≤M := by
  rw [ceilingStepStore_flat r hr]
  unfold ceilingStepFlatStore
  split
  · rename_i hlt
    exact setReg_bound _ _ _ M
      (setReg_bound _ _ _ M
        (setReg_bound _ _ _ M
          (setReg_bound _ _ 0 M
            (setReg_bound _ _ 0 M
              (setReg_bound _ _ 0 M (setReg_bound d _ 0 M hd (by omega)) (by omega))
              (by omega)) (by omega)) (hactive hlt).1)
          (hd (r 0))) (hactive hlt).2
  · repeat' apply setReg_bound
    all_goals first | exact hd _ | omega










theorem ceilingLoopStore_pair (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (t : ℕ) (d : TapeStore R B) :
    ((ceilingLoopStore r t d).reg (r 0),(ceilingLoopStore r t d).reg (r 6)) =
      SizeParameters.ceilIter (d.reg (r 1)) t (d.reg (r 0),d.reg (r 6)) := by
  induction t generalizing d with
  | zero => simp [ceilingLoopStore, SizeParameters.ceilIter, reg_layout r hr]
  | succ t ih =>
    rw [ceilingLoopStore, ih, ceilingStepStore_p r hr,
      ceilingStepStore_q r hr, ceilingStepStore_ell r hr]
    by_cases hlt : d.reg (r 0)<d.reg (r 1)
    all_goals simp [SizeParameters.ceilIter, SizeParameters.ceilStep, reg_layout r hr, hlt]

theorem ceilingLoop_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M t : ℕ) (hM : 1≤M) (d : TapeStore R B)
    (ht : d.reg (r 7)=t) (hd : ∀ j, d.reg j≤M)
    (hp : 1≤d.reg (r 1)) (hpM : 2*d.reg (r 1)≤M)
    (hq : 1≤d.reg (r 0)) (hqb : d.reg (r 0)<2*d.reg (r 1))
    (hbudget : d.reg (r 1)≤d.reg (r 0)+t) (hell : d.reg (r 6)+t≤d.reg (r 1)) :
    ∃ s, s≤t*(128*(M+1)+2)+1 ∧
      (ceilingLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 57)) s
        ((ceilingLoopStore r t d).toCfg (TapeProgram.loopExit 57)) ∧
      ∀ j, (ceilingLoopStore r t d).reg j≤M := by
  induction t generalizing d with
  | zero =>
    have he : d.setReg (r 7) 0=d := by simp [TapeStore.setReg, ← ht]
    exact ⟨1, by omega, by simpa [ceilingLoop, ceilingLoopStore, he] using
      TapeProgram.loop_zero (ceilingStep r) (r 7) inp d ht,
      by simpa [ceilingLoopStore, he] using hd⟩
  | succ t ih =>
    let d₁ := d.setReg (r 7) t
    have hdb : ∀ j, d₁.reg j≤M :=
      setReg_bound d _ _ M hd (by have := hd (r 7); omega)
    obtain ⟨s, c, hs, hc, hcs⟩ := ceilingStep_stops r hr inp M hM d₁ hdb
    have hcb : ∀ j, c.reg j≤M := by
      change ∀ j, c.store.reg j≤M
      rw [hcs]
      apply ceilingStepStore_bound r hr _ M hdb
      intro hlt
      simp [d₁, reg_layout r hr] at hlt ⊢
      omega
    have hcp : c.reg (r 1)=d.reg (r 1) := by
      change c.store.reg (r 1)=_
      rw [hcs, ceilingStepStore_p r hr]
      simp [d₁, reg_layout r hr]
    have hcq : c.reg (r 0)=if d.reg (r 0)<d.reg (r 1) then
        2*d.reg (r 0) else d.reg (r 0) := by
      change c.store.reg (r 0)=_
      rw [hcs, ceilingStepStore_q r hr]
      simp [d₁, reg_layout r hr]
    have hce : c.reg (r 6)=if d.reg (r 0)<d.reg (r 1) then
        d.reg (r 6)+1 else d.reg (r 6) := by
      change c.store.reg (r 6)=_
      rw [hcs, ceilingStepStore_ell r hr]
      simp [d₁, reg_layout r hr]
    have hct : c.reg (r 7)=t := by
      change c.store.reg (r 7)=_
      rw [hcs, ceilingStepStore_count r hr]
      simp [d₁]
    have hcqpos : 1≤c.reg (r 0) := by rw [hcq]; split <;> omega
    have hcqb : c.reg (r 0)<2*c.reg (r 1) := by rw [hcq,hcp]; split <;> omega
    have hcbudget : c.reg (r 1)≤c.reg (r 0)+t := by rw [hcq,hcp]; split <;> omega
    have hcell : c.reg (r 6)+t≤c.reg (r 1) := by rw [hce,hcp]; split <;> omega
    obtain ⟨u, hu, htail, hub⟩ := ih c.store hct hcb (by simpa only [TapeCfg.store,hcp] using hp)
      (by simpa only [TapeCfg.store,hcp] using hpM) hcqpos hcqb hcbudget hcell
    have hhead := TapeProgram.loop_positive_header (ceilingStep r) (r 7) inp d (by omega)
    have hdec : TapeProgram.decStore (r 7) d=d₁ := by
      simp [TapeProgram.decStore, d₁, TapeStore.setReg, ht]
    rw [hdec] at hhead
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (ceilingStep r) (r 7))
    have hreturn := TapeProgram.loop_body_return (ceilingStep r) (r 7) inp c hc.halted
    have hpost : ceilingLoopStore r t c.store=ceilingLoopStore r (t+1) d := by
      rw [ceilingLoopStore, hcs]
    have hall := ((hhead.trans hrun).trans hreturn).trans htail.exec
    rw [hpost] at hall
    refine ⟨_, ?_, ⟨hall,TapeProgram.loop_code_exit _ _⟩, ?_⟩
    · nlinarith
    · rwa [hpost] at hub














theorem ceilingPowerStore_exact (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (hp : 1≤d.reg (r 1)) :
    ((ceilingPowerStore r d).reg (r 0),(ceilingPowerStore r d).reg (r 6)) =
      (2^Nat.clog 2 (d.reg (r 1)),Nat.clog 2 (d.reg (r 1))) := by
  unfold ceilingPowerStore
  rw [ceilingLoopStore_pair r hr]
  simpa [ceilingPrepare, reg_layout r hr] using SizeParameters.ceilIter_exact (d.reg (r 1)) hp

theorem ceilingPowerTwo_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1≤M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j≤M) (hp : 1≤d.reg (r 1)) :
    ∃ t z, t≤512*(M+1)^2 ∧
      (ceilingPowerTwo r).Stops inp (d.toCfg (ceilingPowerTwo (B := B) r).entry) t z ∧
      z.store=ceilingPowerStore r d ∧ ∀ j, z.reg j≤2*M+2 := by
  obtain ⟨c, hc, hcs⟩ := loadConstant_stops (r 0) 1 inp d
  have hce : c.reg (r 6)=d.reg (r 6) := by
    change c.store.reg (r 6)=_; rw [hcs]; simp [reg_layout r hr]
  have hf := TapeMacros.clear_stops (r 6) inp (d.reg (r 6)) c.store hce
  obtain ⟨g, hg, hgs⟩ := TapeMacros.copy_stops (r 1) (r 7) (r 5)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp (c.store.setReg (r 6) 0)
  have hpre : g.store=ceilingPrepare r d := by rw [hgs,hcs]; rfl
  have hgb : ∀ j, g.reg j≤2*M+2 := by
    change ∀ j, g.store.reg j≤2*M+2
    rw [hpre]
    dsimp [ceilingPrepare]
    apply setReg_bound _ _ 0 (2*M+2)
    · apply setReg_bound
      · exact setReg_bound _ _ 0 (2*M+2)
          (setReg_bound d _ 1 (2*M+2) (fun j => (hd j).trans (by omega)) (by omega)) (by omega)
      · simp [reg_layout r hr]
        have := hd (r 1); omega
    · omega
  have hgn : g.reg (r 7)=d.reg (r 1) := by
    change g.store.reg (r 7)=_; rw [hpre]; simp [ceilingPrepare,reg_layout r hr]
  have hgp : g.reg (r 1)=d.reg (r 1) := by
    change g.store.reg (r 1)=_; rw [hpre]; simp [ceilingPrepare,reg_layout r hr]
  have hgq : g.reg (r 0)=1 := by
    change g.store.reg (r 0)=_; rw [hpre]; simp [ceilingPrepare,reg_layout r hr]
  have hge : g.reg (r 6)=0 := by
    change g.store.reg (r 6)=_; rw [hpre]; simp [ceilingPrepare,reg_layout r hr]
  obtain ⟨t, ht, hloop, hzb⟩ := ceilingLoop_stops r hr inp (2*M+2) (d.reg (r 1)) (by omega)
    g.store hgn hgb (by simpa only [TapeCfg.store,hgp] using hp)
    (by simp only [TapeCfg.store,hgp]; have := hd (r 1); omega)
    (by simp only [TapeCfg.store,hgq]; omega)
    (by simp only [TapeCfg.store,hgq,hgp]; omega)
    (by simp only [TapeCfg.store,hgq,hgp]; omega)
    (by simp only [TapeCfg.store,hge,hgp]; omega)
  have hall := ((hc.seq hf).seq hg).seq hloop
  refine ⟨_, _, ?_, hall, ?_, hzb⟩
  · have h₀ := hd (r 0); have h₁ := hd (r 1); have h₅ := hd (r 5)
    have h₆ := hd (r 6); have h₇ := hd (r 7)
    have hcost : (c.store.setReg (r 6) 0).reg (r 7)+
        (c.store.setReg (r 6) 0).reg (r 5)+5*(c.store.setReg (r 6) 0).reg (r 1)+7 ≤ 7*M+7 := by
      rw [hcs]
      simp [reg_layout r hr]
      omega
    have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ h₁) 1)
    simp only [TapeCfg.store]
    nlinarith
  · change ceilingLoopStore r (d.reg (r 1)) g.store=ceilingPowerStore r d
    rw [hpre]
    rfl









end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule67

/-! Inlined whole module: ExpandingCodes.Computation.ParameterDivision -/
section FlattenModule68


set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}













theorem divideLoop_stops (src quotient : Fin R) (hsq : src≠quotient)
    (k : ℕ) (hk : 0<k) (inp : Inputs) (n j : ℕ) (hj : j<k)
    (d : TapeStore R B) (hn : d.reg src=n) :
    (divideLoop src quotient k).Stops inp (d.toCfg ⟨j,by omega⟩)
      (n+(n+j)/k+1) ((divideLoopStore src quotient k j n d).toCfg ⟨k+1,by omega⟩) := by
  induction n generalizing j d with
  | zero =>
    have hdiv : (0+j)/k=0 := by simpa using Nat.div_eq_of_lt hj
    have he : divideLoopStore src quotient k j 0 d=d := by
      have hs : d.setReg src 0=d := by simp [TapeStore.setReg,← hn]
      simp [divideLoopStore,Nat.div_eq_of_lt hj,hs]
    rw [hdiv]
    constructor
    · apply TapeProgram.Exec.one
      · simp [TapeProgram.halted,divideLoop,hj]
      · simp [TapeProgram.step,divideLoop,hj,TapeStore.toCfg,hn,he]
    · simp [TapeProgram.halted,divideLoop]
  | succ n ih =>
    let d₁ := d.setReg src n
    by_cases hnext : j+1<k
    · have h₁ : (divideLoop src quotient k).step inp (d.toCfg ⟨j,by omega⟩)=
          d₁.toCfg ⟨j+1,by omega⟩ := by
        simp [TapeProgram.step,divideLoop,hj,hnext,TapeStore.toCfg,hn,d₁,TapeStore.setReg]
      have htail := ih (j+1) hnext d₁ (by simp [d₁])
      have hpost : divideLoopStore src quotient k (j+1) n d₁=
          divideLoopStore src quotient k j (n+1) d := by
        simp [divideLoopStore,d₁,TapeStore.setReg,Ne.symm hsq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      constructor
      · have hall := TapeProgram.Exec.step (by simp [TapeProgram.halted,divideLoop,hj]) h₁ htail.exec
        rw [hpost] at hall
        have hdivsum : (n+1+j)/k=(n+(j+1))/k := congrArg (· / k) (by omega)
        convert hall using 1 <;> first | rfl | omega
      · simp [TapeProgram.halted,divideLoop]
    · have hjk : j+1=k := by omega
      let d₂ := d₁.setReg quotient (d.reg quotient+1)
      have h₁ : (divideLoop src quotient k).step inp (d.toCfg ⟨j,by omega⟩)=
          d₁.toCfg ⟨k,by omega⟩ := by
        simp [TapeProgram.step,divideLoop,hj,hnext,TapeStore.toCfg,hn,d₁,TapeStore.setReg]
      have h₂ : (divideLoop src quotient k).step inp (d₁.toCfg ⟨k,by omega⟩)=
          d₂.toCfg ⟨0,by omega⟩ := by
        simp [TapeProgram.step,divideLoop,TapeStore.toCfg,d₂,d₁,TapeStore.setReg,Ne.symm hsq]
      have htail := ih 0 hk d₂ (by simp [d₂,d₁,TapeStore.setReg,hsq])
      have hdiv : (n+1+j)/k=n/k+1 := by
        have he : n+1+j=n+k := by omega
        rw [he,Nat.add_div_right n hk]
      have hdiv' : (n+(j+1))/k=n/k+1 :=
        (congrArg (· / k) (show n+(j+1)=n+1+j by omega)).trans hdiv
      have hpost : divideLoopStore src quotient k 0 n d₂=
          divideLoopStore src quotient k j (n+1) d := by
        simp only [divideLoopStore,d₂,d₁,TapeStore.setReg]
        congr 1
        funext l
        by_cases hq : l=quotient
        · subst l; simp [Function.update,hdiv,hdiv',hsq,Ne.symm hsq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        · by_cases hs : l=src
          · subst l; simp [Function.update,hsq,hq]
          · simp [Function.update,hq,hs]
      constructor
      · have hall := TapeProgram.Exec.step (by simp [TapeProgram.halted,divideLoop,hj]) h₁
          (TapeProgram.Exec.step (by simp [TapeProgram.halted,divideLoop]) h₂ htail.exec)
        rw [hpost] at hall
        convert hall using 1 <;> first | rfl | simp [hdiv]; omega
      · simp [TapeProgram.halted,divideLoop]













theorem divideConstantStore_value (r : Fin 4 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (d : TapeStore R B) :
    (divideConstantStore r k d).reg (r 1)=d.reg (r 0)/k := by
  simp [divideConstantStore,divideLoopStore,dividePrepare,reg_layout r hr]






theorem divideConstant_stops (r : Fin 4 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (hk : 0<k) (inp : Inputs) (M : ℕ) (d : TapeStore R B)
    (hd : ∀ j, d.reg j≤M) :
    ∃ t z, t≤16*(M+1) ∧
      (divideConstant r k).Stops inp (d.toCfg (divideConstant (B := B) r k).entry) t z ∧
      z.store=divideConstantStore r k d ∧ ∀ j, z.reg j≤M := by
  obtain ⟨c,hc,hcs⟩ := TapeMacros.copy_stops (r 0) (r 2) (r 3)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d
  have hf := TapeMacros.clear_stops (r 1) inp (c.reg (r 1)) c.store rfl
  have hpre : c.store.setReg (r 1) 0=dividePrepare r d := by rw [hcs]; rfl
  have hloop := divideLoop_stops (r 2) (r 1) (hr.ne (by decide)) k hk inp
    (d.reg (r 0)) 0 hk (dividePrepare r d) (by simp [dividePrepare,reg_layout r hr])
  have hpost : divideLoopStore (r 2) (r 1) k 0 (d.reg (r 0)) (dividePrepare r d)=
      divideConstantStore r k d := rfl
  rw [← hpre] at hloop
  have hall := (hc.seq hf).seq hloop
  refine ⟨_,_,?_,hall,?_,?_⟩
  · have hct : c.reg (r 1)=d.reg (r 1) := by
      change c.store.reg (r 1)=_; rw [hcs]; simp [reg_layout r hr]
    have h₀ := hd (r 0); have h₁ := hd (r 1); have h₂ := hd (r 2); have h₃ := hd (r 3)
    have hdiv := Nat.div_le_self (d.reg (r 0)) k
    simp only [TapeCfg.store,hct,Nat.add_zero]
    omega
  · change divideLoopStore (r 2) (r 1) k 0 (d.reg (r 0)) (c.store.setReg (r 1) 0)=_
    rw [hpre]
    rfl
  · change ∀ j, (divideLoopStore (r 2) (r 1) k 0 (d.reg (r 0))
        (c.store.setReg (r 1) 0)).reg j≤M
    rw [hpre]
    unfold divideLoopStore dividePrepare
    apply setReg_bound
    · apply setReg_bound _ _ 0 M
      · exact setReg_bound _ _ 0 M
          (setReg_bound _ _ 0 M (setReg_bound d _ _ M hd (hd (r 0))) (by omega)) (by omega)
      · omega
    · simp [reg_layout r hr]
      exact (Nat.div_le_self _ _).trans (hd (r 0))



end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule68

/-! Inlined whole module: ExpandingCodes.Computation.ParameterFloor -/
section FlattenModule69


set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}






theorem decrement_stops (r : Fin R) (inp : Inputs) (d : TapeStore R B) :
    (decrement r).Stops inp (d.toCfg 0) 1 ((d.setReg r (d.reg r-1)).toCfg 1) := by
  constructor
  · apply TapeProgram.Exec.one
    · simp [TapeProgram.halted,decrement]
    · by_cases h : d.reg r=0
      · have he : d.setReg r (d.reg r-1)=d := by simpa [h] using setReg_self d r
        rw [he]
        simp [TapeProgram.step,decrement,TapeStore.toCfg,h]
      · simp [TapeProgram.step,decrement,TapeStore.toCfg,h,TapeStore.setReg]
  · simp [TapeProgram.halted,decrement]



theorem floorCeilIndex_injective : Function.Injective floorCeilIndex := by decide



theorem floorCeilLayout_injective (r : Fin 9 → Fin R) (hr : Function.Injective r) :
    Function.Injective (floorCeilLayout r) := hr.comp floorCeilIndex_injective


















theorem clog_succ_eq_log_succ (u : ℕ) (hu : 1≤u) :
    Nat.clog 2 (u+1)=Nat.log 2 u+1 := by
  have hlo : 2^Nat.log 2 u<u+1 := by
    have h := Nat.pow_log_le_self 2 (by omega : u≠0)
    omega
  have hup : u+1≤2^(Nat.log 2 u+1) := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1<2) u
    omega
  have hclo := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mpr hlo
  have hcup := (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr hup
  omega

theorem floorPowerStore_exact (r : Fin 9 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (hu : 1≤d.reg (r 1)) :
    ((floorPowerStore r d).reg (r 0),(floorPowerStore r d).reg (r 6)) =
      (2^Nat.log 2 (d.reg (r 1)),Nat.log 2 (d.reg (r 1))) := by
  have hce := ceilingPowerStore_exact (floorCeilLayout r) (floorCeilLayout_injective r hr)
    (floorPrepare r d) (by simp [floorPrepare,floorCeilLayout,floorCeilIndex,reg_layout r hr])
  have hcq : (ceilingPowerStore (floorCeilLayout r) (floorPrepare r d)).reg (r 0)=
      2^(Nat.log 2 (d.reg (r 1))+1) := by
    have h := congrArg Prod.fst hce
    simpa [floorPrepare,floorCeilLayout,floorCeilIndex,reg_layout r hr,
      clog_succ_eq_log_succ _ hu] using h
  have hcb : (ceilingPowerStore (floorCeilLayout r) (floorPrepare r d)).reg (r 6)=
      Nat.log 2 (d.reg (r 1))+1 := by
    have h := congrArg Prod.snd hce
    simpa [floorPrepare,floorCeilLayout,floorCeilIndex,reg_layout r hr,
      clog_succ_eq_log_succ _ hu] using h
  apply Prod.ext
  · simp [floorPowerStore,halfStepStore,reg_layout r hr,hcq,pow_succ]
  · simp [floorPowerStore,halfStepStore,reg_layout r hr,hcb]

theorem floorPowerTwo_stops (r : Fin 9 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1≤M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j≤M) (hu : 1≤d.reg (r 1)) :
    ∃ t z, t≤4096*(M+1)^2 ∧
      (floorPowerTwo r).Stops inp (d.toCfg (floorPowerTwo (B := B) r).entry) t z ∧
      z.store=floorPowerStore r d ∧ ∀ j, z.reg j≤2*M+4 := by
  obtain ⟨c,hc,hcs⟩ := TapeMacros.copy_stops (r 1) (r 8) (r 5)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d
  have hf := TapeMacros.increment_stops (r 8) inp c.store
  let df := c.store.setReg (r 8) (c.reg (r 8)+1)
  have hpre : df=floorPrepare r d := by
    dsimp [df]
    change c.store.setReg (r 8) (c.store.reg (r 8)+1)=_
    rw [hcs]
    simp [floorPrepare,reg_layout r hr]
  have hfb : ∀ j, df.reg j≤M+1 := by
    rw [hpre]
    unfold floorPrepare
    exact setReg_bound _ _ _ (M+1)
      (setReg_bound _ _ 0 (M+1)
        (setReg_bound d _ _ (M+1) (fun j => (hd j).trans (by omega)) ((hd (r 1)).trans (by omega)))
        (by omega)) (by have := hd (r 1); omega)
  obtain ⟨s,g,hs,hg,hgs,hgb⟩ := ceilingPowerTwo_stops (floorCeilLayout r)
    (floorCeilLayout_injective r hr) inp (M+1) (by omega) df hfb
    (by rw [hpre]; simp [floorPrepare,floorCeilLayout,floorCeilIndex,reg_layout r hr])
  obtain ⟨h,hh,hhs⟩ := halfStep_stops (r 0) (r 3) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp g.store
  have hhb : ∀ j, h.reg j≤2*M+4 := by
    change ∀ j, h.store.reg j≤2*M+4
    rw [hhs]
    exact halfStepStore_bound _ _ _ _ _ (by omega) (by intro j; have := hgb j; omega)
  have hi := decrement_stops (r 6) inp h.store
  have hall := (((hc.seq hf).seq hg).seq hh).seq hi
  refine ⟨_,_,?_,hall,?_,?_⟩
  · have hcopy : d.reg (r 8)+d.reg (r 5)+5*d.reg (r 1)+7≤7*M+7 := by
      have := hd (r 8); have := hd (r 5); have := hd (r 1); omega
    have hhalf := halfStep_time_le (g.reg (r 0)) (g.reg (r 3)) (g.reg (r 4))
    have h₀ := hgb (r 0); have h₃ := hgb (r 3); have h₄ := hgb (r 4)
    simp only [TapeCfg.store]
    nlinarith
  · change h.store.setReg (r 6) (h.store.reg (r 6)-1)=floorPowerStore r d
    rw [hhs,hgs,hpre]
    rfl
  · change ∀ j, (h.store.setReg (r 6) (h.reg (r 6)-1)).reg j≤2*M+4
    exact setReg_bound _ _ _ _ hhb ((Nat.sub_le _ _).trans (hhb (r 6)))



end ParameterPrograms
end ExpandingCodes.Computation

end FlattenModule69

/-! Inlined whole module: ExpandingCodes.Computation.ParameterFrames -/
section FlattenModule70





set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}







theorem SamePayload.trans {d e f : TapeStore R B} (h : SamePayload d e) (k : SamePayload e f) :
    SamePayload d f := ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,k.2.2.2.trans h.2.2.2⟩
theorem SamePayload.setReg (d : TapeStore R B) (r : Fin R) (n : ℕ) :
    SamePayload d (d.setReg r n) := ⟨rfl,rfl,rfl,rfl⟩

theorem powerStepStore_fresh (r : Fin 6 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₁ : j≠r 1) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4) :
    (powerStepStore r d).reg j=d.reg j := by
  simp [powerStepStore,multiplyStore,TapeStore.setReg,h₁,h₂,h₃,h₄]

theorem powerLoopStore_fresh (r : Fin 6 → Fin R) (t : ℕ) (d : TapeStore R B) (j : Fin R)
    (h₁ : j≠r 1) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4) (h₅ : j≠r 5) :
    (powerLoopStore r t d).reg j=d.reg j := by
  induction t generalizing d with
  | zero => simp [powerLoopStore,TapeStore.setReg,h₅]
  | succ t ih =>
    rw [powerLoopStore,ih,powerStepStore_fresh r _ j h₁ h₂ h₃ h₄]
    simp [TapeStore.setReg,h₅]

theorem fixedPowerStore_fresh (r : Fin 6 → Fin R) (t : ℕ) (d : TapeStore R B) (j : Fin R)
    (h₁ : j≠r 1) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4) (h₅ : j≠r 5) :
    (fixedPowerStore r t d).reg j=d.reg j := by
  rw [fixedPowerStore,powerLoopStore_fresh r t _ j h₁ h₂ h₃ h₄ h₅]
  simp [powerPrepare,TapeStore.setReg,h₁,h₅]

theorem powerStepStore_payload (r : Fin 6 → Fin R) (d : TapeStore R B) :
    SamePayload d (powerStepStore r d) := ⟨rfl,rfl,rfl,rfl⟩

theorem powerLoopStore_payload (r : Fin 6 → Fin R) (t : ℕ) (d : TapeStore R B) :
    SamePayload d (powerLoopStore r t d) := by
  induction t generalizing d with
  | zero => exact SamePayload.setReg d _ 0
  | succ t ih => exact ((SamePayload.setReg d _ t).trans (powerStepStore_payload r _)).trans (ih _)

theorem fixedPowerStore_payload (r : Fin 6 → Fin R) (t : ℕ) (d : TapeStore R B) :
    SamePayload d (fixedPowerStore r t d) := by
  exact ((SamePayload.setReg d _ 1).trans (SamePayload.setReg _ _ t)).trans (powerLoopStore_payload r t _)

theorem ceilingStepStore_fresh (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (j : Fin R)
    (h₀ : j≠r 0) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4)
    (h₅ : j≠r 5) (h₆ : j≠r 6) : (ceilingStepStore r d).reg j=d.reg j := by
  rw [ceilingStepStore_flat r hr]
  unfold ceilingStepFlatStore
  split <;> simp [TapeStore.setReg,h₀,h₂,h₃,h₄,h₅,h₆]

theorem ceilingLoopStore_fresh (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (t : ℕ) (d : TapeStore R B) (j : Fin R)
    (h₀ : j≠r 0) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4)
    (h₅ : j≠r 5) (h₆ : j≠r 6) (h₇ : j≠r 7) :
    (ceilingLoopStore r t d).reg j=d.reg j := by
  induction t generalizing d with
  | zero => simp [ceilingLoopStore,TapeStore.setReg,h₇]
  | succ t ih =>
    rw [ceilingLoopStore,ih,ceilingStepStore_fresh r hr _ j h₀ h₂ h₃ h₄ h₅ h₆]
    simp [TapeStore.setReg,h₇]

theorem ceilingPowerStore_fresh (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (j : Fin R)
    (h₀ : j≠r 0) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4)
    (h₅ : j≠r 5) (h₆ : j≠r 6) (h₇ : j≠r 7) :
    (ceilingPowerStore r d).reg j=d.reg j := by
  rw [ceilingPowerStore,ceilingLoopStore_fresh r hr _ _ j h₀ h₂ h₃ h₄ h₅ h₆ h₇]
  simp [ceilingPrepare,TapeStore.setReg,h₀,h₅,h₆,h₇]

theorem ceilingStepStore_payload (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : SamePayload d (ceilingStepStore r d) := by
  rw [ceilingStepStore_flat r hr]
  unfold ceilingStepFlatStore
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem ceilingLoopStore_payload (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (t : ℕ) (d : TapeStore R B) : SamePayload d (ceilingLoopStore r t d) := by
  induction t generalizing d with
  | zero => exact SamePayload.setReg d _ 0
  | succ t ih => exact ((SamePayload.setReg d _ t).trans (ceilingStepStore_payload r hr _)).trans (ih _)

theorem ceilingPowerStore_payload (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : SamePayload d (ceilingPowerStore r d) := by
  have hp : SamePayload d (ceilingPrepare r d) := ⟨rfl,rfl,rfl,rfl⟩
  exact hp.trans (ceilingLoopStore_payload r hr _ _)

theorem divideConstantStore_fresh (r : Fin 4 → Fin R) (k : ℕ)
    (d : TapeStore R B) (j : Fin R) (h₁ : j≠r 1) (h₂ : j≠r 2) (h₃ : j≠r 3) :
    (divideConstantStore r k d).reg j=d.reg j := by
  simp [divideConstantStore,divideLoopStore,dividePrepare,TapeStore.setReg,h₁,h₂,h₃]

theorem divideConstantStore_payload (r : Fin 4 → Fin R) (k : ℕ)
    (d : TapeStore R B) : SamePayload d (divideConstantStore r k d) := ⟨rfl,rfl,rfl,rfl⟩

theorem floorPowerStore_fresh (r : Fin 9 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (j : Fin R)
    (h₀ : j≠r 0) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4)
    (h₅ : j≠r 5) (h₆ : j≠r 6) (h₇ : j≠r 7) (h₈ : j≠r 8) :
    (floorPowerStore r d).reg j=d.reg j := by
  have hcfresh := ceilingPowerStore_fresh (floorCeilLayout r) (floorCeilLayout_injective r hr)
    (floorPrepare r d) j
    (by simpa [floorCeilLayout,floorCeilIndex] using h₀)
    (by simpa [floorCeilLayout,floorCeilIndex] using h₂)
    (by simpa [floorCeilLayout,floorCeilIndex] using h₃)
    (by simpa [floorCeilLayout,floorCeilIndex] using h₄)
    (by simpa [floorCeilLayout,floorCeilIndex] using h₅)
    (by simpa [floorCeilLayout,floorCeilIndex] using h₆)
    (by simpa [floorCeilLayout,floorCeilIndex] using h₇)
  simp only [floorPowerStore,halfStepStore,TapeStore.setReg,
    Function.update_of_ne h₀,Function.update_of_ne h₃,Function.update_of_ne h₄,Function.update_of_ne h₆]
  rw [hcfresh]
  simp [floorPrepare,TapeStore.setReg,h₅,h₈]

theorem floorPowerStore_payload (r : Fin 9 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : SamePayload d (floorPowerStore r d) := by
  have hp : SamePayload d (floorPrepare r d) := ⟨rfl,rfl,rfl,rfl⟩
  have hc := ceilingPowerStore_payload (floorCeilLayout r) (floorCeilLayout_injective r hr)
    (floorPrepare r d)
  have hh : SamePayload (ceilingPowerStore (floorCeilLayout r) (floorPrepare r d))
      (halfStepStore (ceilingPowerStore (floorCeilLayout r) (floorPrepare r d)) (r 0) (r 3) (r 4)) :=
    ⟨rfl,rfl,rfl,rfl⟩
  exact ((hp.trans hc).trans hh).trans (SamePayload.setReg _ _ _)







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

/-! Inlined whole module: ExpandingCodes.Computation.SizeReader -/
section FlattenModule72


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB
namespace SizeReader
variable {R B : ℕ}












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





end SizeReader
end ExpandingCodes.Computation

end FlattenModule72

/-! Inlined whole module: ExpandingCodes.Computation.ParameterSetup -/
section FlattenModule73




set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
open UnaryArithmetic FieldPrograms
variable {R B : ℕ}
















theorem setupPowerP_inj (r : Fin 14 → Fin R) (hr : Function.Injective r) :
    Function.Injective (setupPowerPLayout r) := hr.comp (by decide)
theorem setupCeiling_inj (r : Fin 14 → Fin R) (hr : Function.Injective r) :
    Function.Injective (setupCeilingLayout r) := hr.comp (by decide)
theorem setupPowerM_inj (r : Fin 14 → Fin R) (hr : Function.Injective r) :
    Function.Injective (setupPowerMLayout r) := hr.comp (by decide)
theorem setupDivision_inj (r : Fin 14 → Fin R) (hr : Function.Injective r) :
    Function.Injective (setupDivisionLayout r) := hr.comp (by decide)
theorem setupFloor_inj (r : Fin 14 → Fin R) (hr : Function.Injective r) :
    Function.Injective (setupFloorLayout r) := hr.comp (by decide)






















theorem setupStage₁_n (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) : (setupStage₁ r d σ).reg (r 0)=σ.reg (r 0) :=
  fixedPowerStore_base _ (setupPowerP_inj r hr) _ _
theorem setupStage₁_p (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) : (setupStage₁ r d σ).reg (r 1)=σ.reg (r 0)^(2*d) :=
  fixedPowerStore_value _ (setupPowerP_inj r hr) _ _

theorem setupStage₂_frame (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) (j : Fin 14) (hj : j.val<2) :
    (setupStage₂ r d σ).reg (r j)=(setupStage₁ r d σ).reg (r j) := by
  apply ceilingPowerStore_fresh _ (setupCeiling_inj r hr)
  all_goals simp [setupCeilingLayout,setupCeilingIndex,hr.eq_iff]; omega

theorem setupStage₃_frame (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) (j : Fin 14) (hj : j.val<4) :
    (setupStage₃ r d σ).reg (r j)=(setupStage₂ r d σ).reg (r j) := by
  apply fixedPowerStore_fresh
  all_goals simp [setupPowerMLayout,setupPowerMIndex,hr.eq_iff]; omega

theorem setupStage₄_frame (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (σ : TapeStore R B) (j : Fin 14) (hj : j.val<5) :
    (setupStage₄ r d k σ).reg (r j)=(setupStage₃ r d σ).reg (r j) := by
  apply divideConstantStore_fresh
  all_goals simp [setupDivisionLayout,setupDivisionIndex,hr.eq_iff]; omega

theorem setupStore_frame (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (σ : TapeStore R B) (j : Fin 14) (hj : j.val<6) :
    (setupStore r d k σ).reg (r j)=(setupStage₄ r d k σ).reg (r j) := by
  apply floorPowerStore_fresh _ (setupFloor_inj r hr)
  all_goals simp [setupFloorLayout,setupFloorIndex,hr.eq_iff]; omega

theorem setupStage₂_qell (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) (hp : 1≤σ.reg (r 0)^(2*d)) :
    ((setupStage₂ r d σ).reg (r 3),(setupStage₂ r d σ).reg (r 2)) =
      (2^Nat.clog 2 (σ.reg (r 0)^(2*d)),Nat.clog 2 (σ.reg (r 0)^(2*d))) := by
  have h := ceilingPowerStore_exact (setupCeilingLayout r) (setupCeiling_inj r hr)
    (setupStage₁ r d σ) (by simpa only [show setupCeilingLayout r 1=r 1 from rfl,setupStage₁_p r hr] using hp)
  simpa only [setupStage₂,show setupCeilingLayout r 0=r 3 from rfl,
    show setupCeilingLayout r 6=r 2 from rfl,show setupCeilingLayout r 1=r 1 from rfl,setupStage₁_p r hr] using h

theorem setupStage₃_m (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) :
    (setupStage₃ r d σ).reg (r 4)=(setupStage₂ r d σ).reg (r 3)^d :=
  fixedPowerStore_value _ (setupPowerM_inj r hr) _ _

theorem setupStage₄_u (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (σ : TapeStore R B) :
    (setupStage₄ r d k σ).reg (r 5)=σ.reg (r 0)/k := by
  have h := divideConstantStore_value (setupDivisionLayout r) (setupDivision_inj r hr) k (setupStage₃ r d σ)
  change (setupStage₄ r d k σ).reg (r 5)=(setupStage₃ r d σ).reg (r 0)/k at h
  rw [setupStage₃_frame r hr d σ 0 (by decide),setupStage₂_frame r hr d σ 0 (by decide),setupStage₁_n r hr] at h
  exact h

/-- The eight setup counters, exactly identified with the frozen mission sizes.
No modulus-search or field-construction computation is asserted here. -/
theorem setupStore_values (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (hd : 1≤d) (hk : 0<k) (σ : TapeStore R B)
    (hn : 2≤σ.reg (r 0)) (hnk : k≤σ.reg (r 0)) :
    let n := σ.reg (r 0)
    let ell := ExpandingCodes.PolynomialStretch.fieldExponent d n
    let q := ExpandingCodes.PolynomialStretch.fieldSize d n
    (setupStore r d k σ).reg (r 0)=n ∧
    (setupStore r d k σ).reg (r 1)=n^(2*d) ∧
    (setupStore r d k σ).reg (r 2)=ell ∧
    (setupStore r d k σ).reg (r 3)=q ∧
    (setupStore r d k σ).reg (r 4)=ExpandingCodes.PolynomialStretch.rowCount d n ∧
    (setupStore r d k σ).reg (r 5)=n/k ∧
    (setupStore r d k σ).reg (r 6)=Nat.log 2 (n/k) ∧
    (setupStore r d k σ).reg (r 7)=2^Nat.log 2 (n/k) := by
  dsimp only
  have hp : 2≤σ.reg (r 0)^(2*d) := by
    have hpow := Nat.pow_le_pow_right (show 0<σ.reg (r 0) by omega) (show 1≤2*d by omega)
    simp only [pow_one] at hpow
    omega
  have hc : 1≤Nat.clog 2 (σ.reg (r 0)^(2*d)) := Nat.clog_pos (by decide) (by omega)
  have hqell := setupStage₂_qell r hr d σ (by omega)
  have hu : 1≤(setupStage₄ r d k σ).reg (r 5) := by
    rw [setupStage₄_u r hr]
    exact (Nat.le_div_iff_mul_le hk).mpr (by simpa using hnk)
  have hfloor := floorPowerStore_exact (setupFloorLayout r) (setupFloor_inj r hr) (setupStage₄ r d k σ) hu
  change ((setupStore r d k σ).reg (r 7),(setupStore r d k σ).reg (r 6)) = _ at hfloor
  have hfq := congrArg Prod.fst hqell
  have hfe := congrArg Prod.snd hqell
  dsimp only at hfq hfe
  have hfb := congrArg Prod.fst hfloor
  have hfl := congrArg Prod.snd hfloor
  simp only [Prod.fst,Prod.snd,show setupFloorLayout r 1=r 5 from rfl,setupStage₄_u r hr] at hfb hfl
  have hcommon : ∀ j : Fin 14, j.val<4 →
      (setupStore r d k σ).reg (r j)=(setupStage₂ r d σ).reg (r j) := by
    intro j hj
    rw [setupStore_frame r hr d k σ j (by omega),setupStage₄_frame r hr d k σ j (by omega),
      setupStage₃_frame r hr d σ j hj]
  refine ⟨?_,?_,?_,?_,?_,?_,hfl,hfb⟩
  · rw [hcommon 0 (by decide),setupStage₂_frame r hr d σ 0 (by decide),setupStage₁_n r hr]
  · rw [hcommon 1 (by decide),setupStage₂_frame r hr d σ 1 (by decide),setupStage₁_p r hr]
  · rw [hcommon 2 (by decide),hfe]
    simp [ExpandingCodes.PolynomialStretch.fieldExponent,max_eq_right hc]
  · rw [hcommon 3 (by decide),hfq]
    simp [ExpandingCodes.PolynomialStretch.fieldSize,ExpandingCodes.PolynomialStretch.fieldExponent,max_eq_right hc]
  · rw [setupStore_frame r hr d k σ 4 (by decide),setupStage₄_frame r hr d k σ 4 (by decide),setupStage₃_m r hr,hfq]
    simp [ExpandingCodes.PolynomialStretch.rowCount,ExpandingCodes.PolynomialStretch.fieldSize,
      ExpandingCodes.PolynomialStretch.fieldExponent,max_eq_right hc]
  · rw [setupStore_frame r hr d k σ 5 (by decide),setupStage₄_u r hr]

theorem setupStore_payload (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (σ : TapeStore R B) : SamePayload σ (setupStore r d k σ) := by
  exact ((((fixedPowerStore_payload _ _ _).trans
    (ceilingPowerStore_payload _ (setupCeiling_inj r hr) _)).trans
    (fixedPowerStore_payload _ _ _)).trans (divideConstantStore_payload _ _ _)).trans
    (floorPowerStore_payload _ (setupFloor_inj r hr) _)

theorem setupStore_fresh (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (σ : TapeStore R B) (j : Fin R) (h : ∀ i, j≠r i) :
    (setupStore r d k σ).reg j=σ.reg j := by
  calc
    (setupStore r d k σ).reg j=(setupStage₄ r d k σ).reg j :=
      floorPowerStore_fresh _ (setupFloor_inj r hr) _ j (h _) (h _) (h _) (h _) (h _) (h _) (h _) (h _)
    _=(setupStage₃ r d σ).reg j := divideConstantStore_fresh _ _ _ j (h _) (h _) (h _)
    _=(setupStage₂ r d σ).reg j := fixedPowerStore_fresh _ _ _ j (h _) (h _) (h _) (h _) (h _)
    _=(setupStage₁ r d σ).reg j :=
      ceilingPowerStore_fresh _ (setupCeiling_inj r hr) _ j (h _) (h _) (h _) (h _) (h _) (h _) (h _)
    _=σ.reg j := fixedPowerStore_fresh _ _ _ j (h _) (h _) (h _) (h _) (h _)

theorem powerCounterBound_pos (e M : ℕ) : 1≤powerCounterBound e M := by
  have h := Nat.one_le_pow (e+1) (M+1) (by omega)
  unfold powerCounterBound
  nlinarith

theorem setup_stops (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (hk : 0<k) (inp : Inputs) (M : ℕ) (hM : 1≤M)
    (σ : TapeStore R B) (hσ : ∀ j, σ.reg j≤M)
    (hn : 1≤σ.reg (r 0)) (hnk : k≤σ.reg (r 0)) :
    ∃ t z, t≤ setupTimeBound d M ∧
      (setup r d k).Stops inp (σ.toCfg (setup (B := B) r d k).entry) t z ∧
      z.store=setupStore r d k σ ∧ ∀ j, z.reg j≤ setupCounterBound d M := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := fixedPower_stops (setupPowerPLayout r) (setupPowerP_inj r hr)
    (2*d) inp M hM σ hσ hn
  have hs₁' : c₁.store=setupStage₁ r d σ := hs₁
  have hp : 1≤c₁.reg (r 1) := by
    change 1≤c₁.store.reg (r 1)
    rw [hs₁',setupStage₁_p r hr]
    exact Nat.one_le_pow _ _ hn
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂,hb₂⟩ := ceilingPowerTwo_stops (setupCeilingLayout r) (setupCeiling_inj r hr)
    inp (setupBound₁ d M) (powerCounterBound_pos _ _) c₁.store hb₁ hp
  have hs₂' : c₂.store=setupStage₂ r d σ := by rw [hs₂,hs₁']; rfl
  have hq : 1≤c₂.reg (r 3) := by
    change 1≤c₂.store.reg (r 3)
    rw [hs₂']
    have h := ceilingPowerStore_exact (setupCeilingLayout r) (setupCeiling_inj r hr) c₁.store hp
    have hval := congrArg Prod.fst h
    change (ceilingPowerStore (setupCeilingLayout r) c₁.store).reg (r 3)=_ at hval
    rw [hs₁'] at hval
    change (setupStage₂ r d σ).reg (r 3)=_ at hval
    rw [hval]
    exact Nat.one_le_pow _ _ (by decide)
  obtain ⟨t₃,c₃,ht₃,h₃,hs₃,hb₃⟩ := fixedPower_stops (setupPowerMLayout r) (setupPowerM_inj r hr)
    d inp (setupBound₂ d M) (by unfold setupBound₂ ceilingCounterBound; omega) c₂.store hb₂ hq
  have hs₃' : c₃.store=setupStage₃ r d σ := by rw [hs₃,hs₂']; rfl
  obtain ⟨t₄,c₄,ht₄,h₄,hs₄,hb₄⟩ := divideConstant_stops (setupDivisionLayout r) (setupDivision_inj r hr)
    k hk inp (setupBound₃ d M) c₃.store hb₃
  have hs₄' : c₄.store=setupStage₄ r d k σ := by rw [hs₄,hs₃']; rfl
  have hu : 1≤c₄.reg (r 5) := by
    change 1≤c₄.store.reg (r 5)
    rw [hs₄',setupStage₄_u r hr]
    exact (Nat.le_div_iff_mul_le hk).mpr (by simpa using hnk)
  obtain ⟨t₅,c₅,ht₅,h₅,hs₅,hb₅⟩ := floorPowerTwo_stops (setupFloorLayout r) (setupFloor_inj r hr)
    inp (setupBound₃ d M) (powerCounterBound_pos _ _) c₄.store hb₄ hu
  have hall := (((h₁.seq h₂).seq h₃).seq h₄).seq h₅
  refine ⟨_,_,?_,hall,?_,hb₅⟩
  · unfold setupTimeBound powerTimeBound ceilingTimeBound divisionTimeBound floorTimeBound
    omega
  · change c₅.store=setupStore r d k σ
    rw [hs₅,hs₄']
    rfl

























































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

/-! Inlined whole module: ExpandingCodes.Computation.SourceModulus -/
section FlattenModule75



set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.SourceModulus
open NKtLB FieldPrograms FieldConvolution FieldCertificates SourceFieldArithmetic
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B : ℕ}















































































































































































































































































































































































































































































































































































































































































































































































































































































































theorem factorBodyStore_outside (r : Fin 32 → Fin R) (d : TapeStore R B) (j : Fin R) (hne : ∀ i : Fin 32,j ≠ r i) :
    (factorBodyStore r d).reg j = d.reg j := by
  unfold factorBodyStore
  simp only [TapeStore.setReg,Function.update_of_ne (hne 1)]
  rw [requireStore_fresh _ _ _ _ (hne 6) (hne 25)]
  apply certificateResult_outside
  intro i
  exact hne ⟨i.val,by have := i.isLt;omega⟩

theorem innerResult_outside (r : Fin 32 → Fin R) (n : ℕ) (d : TapeStore R B) (j : Fin R) (hne : ∀ i : Fin 32,j ≠ r i) :
    (innerResult r n d).reg j = d.reg j :=
  loopResult_frame (r 30) (factorBodyStore r) j (hne 30) (fun c => factorBodyStore_outside r c j hne) n d

theorem outerBodyStore_outside (r : Fin 32 → Fin R) (d : TapeStore R B) (j : Fin R) (hne : ∀ i : Fin 32,j ≠ r i) :
    (outerBodyStore r d).reg j = d.reg j := by
  unfold outerBodyStore
  simp only [TapeStore.setReg,Function.update_of_ne (hne 0)]
  rw [innerResult_outside r _ _ j hne]
  simp [innerPrepareStore,TapeStore.setReg,hne 1,hne 28,hne 30]

theorem outerResult_outside (r : Fin 32 → Fin R) (n : ℕ) (d : TapeStore R B) (j : Fin R) (hne : ∀ i : Fin 32,j ≠ r i) :
    (outerResult r n d).reg j = d.reg j :=
  loopResult_frame (r 26) (outerBodyStore r) j (hne 26) (fun c => outerBodyStore_outside r c j hne) n d

theorem candidateBodyStore_outside (r : Fin 32 → Fin R) (d : TapeStore R B) (j : Fin R) (hne : ∀ i : Fin 32,j ≠ r i) :
    (candidateBodyStore r d).reg j = d.reg j := by
  rw [candidateBodyStore,commitStore_fresh _ _ _ (hne 27) (hne 28) (hne 29) (hne 25),outerResult_outside r _ _ j hne]
  simp [candidatePrepareStore,TapeStore.setReg,hne 0,hne 2,hne 3,hne 4,hne 25,hne 26,hne 28]

theorem constructResult_outside (r : Fin 32 → Fin R) (d : TapeStore R B) (j : Fin R) (hne : ∀ i : Fin 32,j ≠ r i) :
    (constructResult r d).reg j = d.reg j := by
  rw [constructResult,candidateResult,loopResult_frame (r 31) (candidateBodyStore r) j (hne 31)
    (fun c => candidateBodyStore_outside r c j hne)]
  simp [prepareStore,TapeStore.setReg,hne 24,hne 27,hne 28,hne 29,hne 31]





























end ExpandingCodes.Computation.SourceModulus

end FlattenModule75

/-! Inlined whole module: ExpandingCodes.Computation.SourceFieldSetup -/
section FlattenModule76


set_option autoImplicit false
set_option maxRecDepth 2048

namespace ExpandingCodes.Computation.SourceFieldSetup
open NKtLB FieldPrograms FieldConvolution SourceFieldArithmetic
open ExpandingCodes.PolynomialStretch BinaryPolynomial
variable {R B : ℕ}





























































































































































































theorem setupStore_outside (r : Fin 32 → Fin R) (d : TapeStore R B) (j : Fin R) (hne : ∀ i : Fin 32,j ≠ r i) :
    (setupStore r d).reg j = d.reg j := by
  simp only [setupStore,UnaryArithmetic.multiplyStore,TapeStore.setReg,
    Function.update_of_ne (hne 24),Function.update_of_ne (hne 28),Function.update_of_ne (hne 30)]
  unfold monicStore
  simp only [TapeStore.setReg,Function.update_of_ne (hne 3),Function.update_of_ne (hne 28)]
  rw [SourceModulus.constructResult_outside r _ j hne]
  simp [boundStore,TapeStore.setReg,hne 19,hne 28]






















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

/-! Inlined whole module: ExpandingCodes.Computation.SamplerAssembly -/
section FlattenModule103










set_option autoImplicit false
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false
namespace ExpandingCodes.Computation.SamplerAssembly
open NKtLB UnaryArithmetic FieldPrograms ParameterPrograms SamplerEvaluation
open ExpandingCodes.PolynomialStretch
variable {R B : ℕ}




















theorem sizeLayout_injective (r : Fin 80 → Fin R) (hr : Function.Injective r) :
    Function.Injective (sizeLayout r) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val (hr h)
  simp only [sizeLayout,Fin.val_mk] at hh
  omega











theorem prepareRandom_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (ell width : Fin 80) (he : ell≠46 ∧ ell≠51) (hw : width≠47 ∧ width≠51)
    (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M) :
    ∃ t e,t ≤ 14*M+15 ∧
      (prepareRandom r ell width).Stops inp
        (s.toCfg (prepareRandom (B:=B) r ell width).entry) t e ∧
      e.store=prepareRandomStore r ell width s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := copy_stops_bound (r ell) (r 46) (r 51)
    (hr.ne he.1) (hr.ne he.2) (hr.ne (by decide)) inp M s hs
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂,hb₂⟩ := copy_stops_bound (r width) (r 47) (r 51)
    (hr.ne hw.1) (hr.ne hw.2) (hr.ne (by decide)) inp M c₁.store hb₁
  have hall := h₁.seq h₂
  refine ⟨_,_,by omega,hall,?_,hb₂⟩
  change c₂.store=_
  rw [hs₂,hs₁]
  rfl

theorem prepareRandomStore_values (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (ell width : Fin 80) (hw : width≠46 ∧ width≠51) (s : TapeStore R B) :
    (prepareRandomStore r ell width s).reg (r 46)=s.reg (r ell) ∧
    (prepareRandomStore r ell width s).reg (r 47)=s.reg (r width) ∧
    (prepareRandomStore r ell width s).reg (r 51)=0 := by
  simp [prepareRandomStore,SamplerEvaluation.reg_layout r hr,hw.1,hw.2]

theorem prepareRandomStore_fresh (r : Fin 80 → Fin R) (ell width : Fin 80)
    (s : TapeStore R B) (j : Fin R) (ha : j≠r 46) (hb : j≠r 47) (hc : j≠r 51) :
    (prepareRandomStore r ell width s).reg j=s.reg j := by
  simp [prepareRandomStore,TapeStore.setReg,ha,hb,hc]











theorem initializeStore_head (s : TapeStore R B) (b : Fin B) (hh : s.bufferHead b=0) :
    (initializeStore s b).bufferHead=Function.update s.bufferHead b 1 := by
  simp [initializeStore,TapeArrays.painted,TapeMacros.cellStore,hh,Machine.moveHead]

theorem markedFill_stops (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (hk : s.reg l.count=K)
    (hq : s.reg l.random.q=2^(s.reg l.random.ell))
    (he : s.reg l.random.ell ≤ s.reg l.random.q) (hc : RandomTables.Clean l.random s) :
    ∃ t e,t ≤ K*(RandomTables.entryBound (s.reg l.random.q)+2)+3 ∧
      (markedFill l b).Stops inp (s.toCfg (markedFill (B:=B) l b).entry) t e ∧
      e.store=markedFillStore l b inp K s := by
  have hi := TapeMacros.cell_stops b (fun _ => (.bot,.right)) inp s
  obtain ⟨t,ht,hstop⟩ := RandomTables.fill_stops l b inp K (initializeStore s b) hk hq he hc
  have hall := hi.seq hstop
  change t ≤ K*(RandomTables.entryBound (s.reg l.random.q)+2)+1 at ht
  refine ⟨_,_,by omega,hall,rfl⟩

/-- The physical random fill preserves every counter outside its five mutable
registers; the entry count is actually exhausted. -/
theorem markedFillStore_reg_other (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (j : Fin R)
    (ha : j≠l.random.acc) (hc : j≠l.random.count) (ht : j≠l.random.tmp)
    (hs : j≠l.random.scratch) (hk : j≠l.count) :
    (markedFillStore l b inp K s).reg j=s.reg j :=
  RandomTables.fillStore_reg_other l b inp K (initializeStore s b) j ha hc ht hs hk

theorem markedFillStore_bound (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (M : ℕ) (hs : ∀ j,s.reg j ≤ M)
    (hc : RandomTables.Clean l.random s) :
    ∀ j,(markedFillStore l b inp K s).reg j ≤ M := by
  intro j
  unfold markedFillStore
  have hclean := RandomTables.fillStore_clean l b inp K (initializeStore s b) hc
  by_cases ha : j=l.random.acc
  · subst j; rw [hclean.1];omega
  by_cases hc' : j=l.random.count
  · subst j; rw [hclean.2.1];omega
  by_cases ht : j=l.random.tmp
  · subst j; rw [hclean.2.2.1];omega
  by_cases hsc : j=l.random.scratch
  · subst j; rw [hclean.2.2.2];omega
  by_cases hk : j=l.count
  · subst j
    rw [RandomTables.fillStore_count]
    exact (Nat.sub_le _ _).trans (hs _)
  · change (markedFillStore l b inp K s).reg j ≤ M
    rw [markedFillStore_reg_other l b inp K s j ha hc' ht hsc hk]
    exact hs j

theorem markedFillStore_output (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) : (markedFillStore l b inp K s).output=s.output :=
  RandomTables.fillStore_output l b inp K (initializeStore s b)

theorem markedFillStore_roHead (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) :
    (markedFillStore l b inp K s).roHead=
      Function.update s.roHead 3 (s.roHead 3+K*s.reg l.random.ell) :=
  RandomTables.fillStore_roHead l b inp K (initializeStore s b)

theorem markedFillStore_head (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (hq : s.reg l.random.q=2^(s.reg l.random.ell))
    (hh : s.bufferHead b=0) :
    (markedFillStore l b inp K s).bufferHead=
      Function.update s.bufferHead b (1+K*s.reg l.random.q) := by
  rw [markedFillStore,RandomTables.fillStore_head l b inp K (initializeStore s b) hq,
    initializeStore_head s b hh]
  simp only [Function.update_self,Function.update_idem]
  rfl

theorem markedFillStore_table (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (hq : s.reg l.random.q=2^(s.reg l.random.ell))
    (hh : s.bufferHead b=0) :
    TapeArrays.ThermometerTable (markedFillStore l b inp K s) b (s.reg l.random.q)
      (fun i => (RandomTables.sampledValues inp K (s.reg l.random.ell) (s.roHead 3) i).val) := by
  intro i
  have h := RandomTables.fillStore_sampledValues l b inp K (initializeStore s b) hq i
  simpa [markedFillStore,initializeStore,TapeArrays.painted,TapeMacros.cellStore,Machine.moveHead,hh,
    TapeArrays.entryOffset] using h










theorem staticScale_stops (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (c : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M)
    (hc : c ≤ M) (hp : s.reg (r 0)*c ≤ M) :
    ∃ t e,t ≤ 40*(M+1)^2 ∧
      (staticScale r c).Stops inp (s.toCfg (staticScale (B:=B) r c).entry) t e ∧
      e.store=staticScaleStore r c s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨a,ha,has⟩ := loadConstant_stops (r 1) c inp s
  have hab : ∀ j,a.reg j ≤ M := by
    change ∀ j,a.store.reg j ≤ M
    rw [has];exact setReg_bound _ _ _ M hs hc
  obtain ⟨t,e,ht,he,hes⟩ := multiply_stops_polynomial (r 0) (r 1) (r 2) (r 3) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    inp a.store M (hab _) (hab _) (hab _) (hab _) (hab _)
  have hep : e.store=staticScaleStore r c s := by rw [hes,has];rfl
  have heb : ∀ j,e.reg j ≤ M := by
    change ∀ j,e.store.reg j ≤ M
    rw [hep]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M (setReg_bound s _ c M hs hc)
    simpa [SamplerEvaluation.reg_layout r hr] using hp
  have hall := ha.seq he
  refine ⟨_,_,?_,hall,hep,heb⟩
  have := hs (r 1)
  nlinarith

theorem staticScaleStore_value (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (c : ℕ) (s : TapeStore R B) :
    (staticScaleStore r c s).reg (r 2)=s.reg (r 0)*c := by
  simp [staticScaleStore,multiplyStore,SamplerEvaluation.reg_layout r hr]

theorem staticScaleStore_fresh (r : Fin 5 → Fin R) (c : ℕ) (s : TapeStore R B)
    (j : Fin R) (h₁ : j≠r 1) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4) :
    (staticScaleStore r c s).reg j=s.reg j := by
  simp [staticScaleStore,multiplyStore,TapeStore.setReg,h₁,h₂,h₃,h₄]












theorem cube_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M)
    (hQ : (s.reg (r 35))^2 ≤ M) (hC : (s.reg (r 35))^3 ≤ M) :
    ∃ t e,t ≤ 65*(M+1)^2 ∧
      (cube r).Stops inp (s.toCfg (cube (B:=B) r).entry) t e ∧
      e.store=cubeStore r s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,a,ht₁,ha,has⟩ := multiply_stops_polynomial (r 35) (r 35) (r 53) (r 54) (r 55)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    inp s M (hs _) (hs _) (hs _) (hs _) (hs _)
  have ha' : a.store=cubeSquare r s := has
  have hab : ∀ j,a.reg j ≤ M := by
    change ∀ j,a.store.reg j ≤ M
    rw [has,multiplyStore]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M hs
    simpa [pow_two] using hQ
  obtain ⟨t₂,e,ht₂,he,hes⟩ := multiply_stops_polynomial (r 35) (r 53) (r 56) (r 54) (r 55)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    inp a.store M (hab _) (hab _) (hab _) (hab _) (hab _)
  have hep : e.store=cubeStore r s := by rw [hes,ha'];rfl
  have heb : ∀ j,e.reg j ≤ M := by
    change ∀ j,e.store.reg j ≤ M
    rw [hes,multiplyStore]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M hab
    rw [has]
    simpa [multiplyStore,SamplerEvaluation.reg_layout r hr,pow_succ,pow_two,Nat.mul_assoc] using hC
  exact ⟨_,_,by nlinarith,ha.seq he,hep,heb⟩

theorem cubeStore_value (r : Fin 80 → Fin R) (hr : Function.Injective r) (s : TapeStore R B) :
    (cubeStore r s).reg (r 56)=(s.reg (r 35))^3 := by
  simp [cubeStore,cubeSquare,multiplyStore,SamplerEvaluation.reg_layout r hr,pow_succ,pow_two,Nat.mul_assoc]

theorem cubeStore_fresh (r : Fin 80 → Fin R) (s : TapeStore R B)
    (j : Fin R) (h₁ : j≠r 53) (h₂ : j≠r 54) (h₃ : j≠r 55) (h₄ : j≠r 56) :
    (cubeStore r s).reg j=s.reg j := by
  simp [cubeStore,cubeSquare,multiplyStore,TapeStore.setReg,h₁,h₂,h₃,h₄]

theorem fillStore_bottomMarked (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (hq : s.reg l.random.q=2^(s.reg l.random.ell))
    (hh : 0<s.bufferHead b) (hm : TapeArrays.BottomMarked s b) :
    TapeArrays.BottomMarked (RandomTables.fillStore l b inp K s) b := by
  induction K generalizing s with
  | zero => exact hm
  | succ K ih =>
    let c := TapeProgram.decStore l.count s
    let e := RandomTables.entryStore l.random b inp c
    have hcq : c.reg l.random.q=2^(c.reg l.random.ell) := by
      simpa [c,TapeProgram.decStore,l.fresh 0,l.fresh 1] using hq
    have heq : e.reg l.random.q=2^(e.reg l.random.ell) := by
      rw [RandomTables.entryStore_reg,RandomTables.entryStore_reg]
      simpa [RandomBits.Layout.q,RandomBits.Layout.ell,RandomBits.Layout.acc,
        RandomBits.Layout.count,RandomBits.Layout.tmp,RandomBits.Layout.scratch] using hcq
    have heh : 0<e.bufferHead b := by
      rw [RandomTables.entryStore_head l.random b inp c hcq]
      simp only [Function.update_self]
      change 0<s.bufferHead b+c.reg l.random.q
      omega
    have hem : TapeArrays.BottomMarked e b := by
      constructor
      · rw [RandomTables.entryStore_symbol l.random b inp c hcq]
        have hc0 : ¬c.bufferHead b ≤ 0 := by change ¬s.bufferHead b ≤ 0;omega
        simpa [hc0] using hm.1
      · intro j hj
        rw [RandomTables.entryStore_symbol l.random b inp c hcq]
        split_ifs <;> first | decide | exact hm.2 j hj
    exact ih e heq heh hem

theorem markedFillStore_bottomMarked (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (hq : s.reg l.random.q=2^(s.reg l.random.ell))
    (hh : s.bufferHead b=0) (hb : ∀ j,(s.bufferTape b).getD j .blank=.blank) :
    TapeArrays.BottomMarked (markedFillStore l b inp K s) b := by
  have hm : TapeArrays.BottomMarked (initializeStore s b) b := by
    constructor
    · simp only [initializeStore,TapeArrays.painted,TapeMacros.cellStore,Function.update_self,hh,
        getD_writeAt,if_pos rfl,if_true]
    · intro j hj
      simp only [initializeStore,TapeArrays.painted,TapeMacros.cellStore,Function.update_self,hh,
        getD_writeAt]
      rw [if_neg (by omega : j≠0),hb j]
      decide
  exact fillStore_bottomMarked l b inp K (initializeStore s b) hq
    (by rw [initializeStore_head s b hh];simp) hm

theorem markedFillStore_other_symbol (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (hq : s.reg l.random.q=2^(s.reg l.random.ell))
    (c : Fin B) (hcb : c≠b) (j : ℕ) :
    ((markedFillStore l b inp K s).bufferTape c).getD j .blank=(s.bufferTape c).getD j .blank := by
  rw [markedFillStore,RandomTables.fillStore_outside l b inp K (initializeStore s b) hq c j
    (Or.inl hcb)]
  simp [initializeStore,TapeArrays.painted,TapeMacros.cellStore,hcb]









theorem formCountLayout_injective (r : Fin 80 → Fin R) (hr : Function.Injective r) :
    Function.Injective (formCountLayout r) := hr.comp (by decide)

theorem formCount_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M)
    (hc : 2*k*d ≤ M) (hp : 2*k*s.reg (r 35)*d ≤ M) :
    ∃ t e,t ≤ 40*(M+1)^2 ∧
      (formCount r d k).Stops inp (s.toCfg (formCount (B:=B) r d k).entry) t e ∧
      e.store=formCountStore r d k s ∧ (∀ j,e.reg j ≤ M) := by
  apply staticScale_stops (formCountLayout r) (formCountLayout_injective r hr) (2*k*d) inp M s hs hc
  change s.reg (r 35)*(2*k*d) ≤ M
  nlinarith [hp]

theorem formCountStore_value (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (s : TapeStore R B) :
    (formCountStore r d k s).reg (r 52)=2*k*s.reg (r 35)*d := by
  have h := staticScaleStore_value (formCountLayout r) (formCountLayout_injective r hr) (2*k*d) s
  change (formCountStore r d k s).reg (r 52)=s.reg (r 35)*(2*k*d) at h
  rw [h]
  ring









theorem hashScaleLayout_injective (r : Fin 80 → Fin R) (hr : Function.Injective r) :
    Function.Injective (hashScaleLayout r) := hr.comp (by decide)

theorem hashCount_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M)
    (hk : k ≤ M) (hQ : (s.reg (r 35))^2 ≤ M) (hC : (s.reg (r 35))^3 ≤ M)
    (hp : k*(s.reg (r 35))^3 ≤ M) :
    ∃ t e,t ≤ 106*(M+1)^2 ∧
      (hashCount r k).Stops inp (s.toCfg (hashCount (B:=B) r k).entry) t e ∧
      e.store=hashCountStore r k s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,a,ht₁,ha,has,hab⟩ := cube_stops r hr inp M s hs hQ hC
  have hap : a.reg (r 56)*k ≤ M := by
    change a.store.reg (r 56)*k ≤ M
    rw [has,cubeStore_value r hr]
    simpa [Nat.mul_comm] using hp
  obtain ⟨t₂,e,ht₂,he,hes,heb⟩ := staticScale_stops (hashScaleLayout r)
    (hashScaleLayout_injective r hr) k inp M a.store hab hk hap
  have hall := ha.seq he
  refine ⟨_,_,by nlinarith,hall,?_,heb⟩
  change e.store=_
  rw [hes,has]
  rfl

theorem hashCountStore_value (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (s : TapeStore R B) :
    (hashCountStore r k s).reg (r 52)=k*(s.reg (r 35))^3 := by
  have h := staticScaleStore_value (hashScaleLayout r) (hashScaleLayout_injective r hr) k (cubeStore r s)
  change (hashCountStore r k s).reg (r 52)=(cubeStore r s).reg (r 56)*k at h
  rw [h,cubeStore_value r hr]
  ring

theorem formCountStore_fresh (r : Fin 80 → Fin R) (d k : ℕ) (s : TapeStore R B)
    (j : Fin R) (h₁ : j≠r 53) (h₂ : j≠r 52) (h₃ : j≠r 54) (h₄ : j≠r 55) :
    (formCountStore r d k s).reg j=s.reg j :=
  staticScaleStore_fresh (formCountLayout r) (2*k*d) s j h₁ h₂ h₃ h₄

theorem hashCountStore_fresh (r : Fin 80 → Fin R) (k : ℕ) (s : TapeStore R B)
    (j : Fin R) (h₁ : j≠r 52) (h₂ : j≠r 53) (h₃ : j≠r 54) (h₄ : j≠r 55)
    (h₅ : j≠r 56) (h₆ : j≠r 57) :
    (hashCountStore r k s).reg j=s.reg j := by
  unfold hashCountStore
  rw [staticScaleStore_fresh (hashScaleLayout r) k (cubeStore r s) j h₆ h₁ h₃ h₄]
  exact cubeStore_fresh r s j h₂ h₃ h₄ h₅









theorem entryBound_le (q M : ℕ) (hq : q ≤ M) :
    RandomTables.entryBound q+2 ≤ 80*(M+1)^2 := by
  unfold RandomTables.entryBound
  nlinarith [Nat.mul_self_le_mul_self hq]

theorem markedFill_stops_bound (l : RandomTables.Layout R) (b : Fin B) (inp : Inputs)
    (K : ℕ) (s : TapeStore R B) (M : ℕ) (hk : s.reg l.count=K)
    (hK : K ≤ M) (hQ : s.reg l.random.q ≤ M)
    (hq : s.reg l.random.q=2^(s.reg l.random.ell))
    (he : s.reg l.random.ell ≤ s.reg l.random.q) (hc : RandomTables.Clean l.random s) :
    ∃ t e,t ≤ 100*(M+1)^3 ∧
      (markedFill l b).Stops inp (s.toCfg (markedFill (B:=B) l b).entry) t e ∧
      e.store=markedFillStore l b inp K s := by
  obtain ⟨t,e,ht,he,hes⟩ := markedFill_stops l b inp K s hk hq he hc
  refine ⟨t,e,ht.trans ?_,he,hes⟩
  have hb := Nat.mul_le_mul hK (entryBound_le _ M hQ)
  nlinarith














theorem formPrepareStore_values (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (s : TapeStore R B) :
    (formPrepareStore r d k s).reg (r 46)=s.reg (r 34) ∧
    (formPrepareStore r d k s).reg (r 47)=s.reg (r 35) ∧
    (formPrepareStore r d k s).reg (r 52)=2*k*s.reg (r 35)*d := by
  have h := prepareRandomStore_values r hr 34 35 (by decide) (formCountStore r d k s)
  refine ⟨?_,?_,?_⟩
  · rw [show (formPrepareStore r d k s).reg (r 46)=(formCountStore r d k s).reg (r 34) from h.1]
    exact formCountStore_fresh r d k s _ (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) (hr.ne (by decide))
  · rw [show (formPrepareStore r d k s).reg (r 47)=(formCountStore r d k s).reg (r 35) from h.2.1]
    exact formCountStore_fresh r d k s _ (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) (hr.ne (by decide))
  · rw [formPrepareStore,prepareRandomStore_fresh r 34 35 _ _
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)),formCountStore_value r hr]

theorem formPrepareStore_clean (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (s : TapeStore R B) (hc : RandomTables.Clean (randomLayout r hr).random s) :
    RandomTables.Clean (randomLayout r hr).random (formPrepareStore r d k s) := by
  change s.reg (r 48)=0 ∧ s.reg (r 49)=0 ∧ s.reg (r 50)=0 ∧ s.reg (r 51)=0 at hc
  change (formPrepareStore r d k s).reg (r 48)=0 ∧
    (formPrepareStore r d k s).reg (r 49)=0 ∧
    (formPrepareStore r d k s).reg (r 50)=0 ∧ (formPrepareStore r d k s).reg (r 51)=0
  rcases hc with ⟨h48,h49,h50,h51⟩
  simp [formPrepareStore,prepareRandomStore,formCountStore,staticScaleStore,formCountLayout,
    multiplyStore,SamplerEvaluation.reg_layout r hr,h48,h49,h50]

theorem formFill_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ j,s.reg j ≤ M) (hc : 2*k*d ≤ M) (hp : 2*k*s.reg (r 35)*d ≤ M)
    (hq : s.reg (r 35)=2^(s.reg (r 34))) (he : s.reg (r 34) ≤ s.reg (r 35))
    (hclean : RandomTables.Clean (randomLayout r hr).random s) :
    ∃ t e,t ≤ 160*(M+1)^3 ∧
      (formFill r hr d k b).Stops inp (s.toCfg (formFill r hr d k b).entry) t e ∧
      e.store=formFillStore r hr d k b inp s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,a,ht₁,ha,has,hab⟩ := formCount_stops r hr d k inp M s hs hc hp
  obtain ⟨t₂,c,ht₂,hc,hcs,hcb⟩ := prepareRandom_stops r hr 34 35 (by decide) (by decide)
    inp M a.store hab
  have hcp : c.store=formPrepareStore r d k s := by rw [hcs,has];rfl
  have hcv := formPrepareStore_values r hr d k s
  have hcc : RandomTables.Clean (randomLayout r hr).random c.store := by
    rw [hcp];exact formPrepareStore_clean r hr d k s hclean
  have hcq : c.reg (randomLayout r hr).random.q=2^(c.reg (randomLayout r hr).random.ell) := by
    change c.store.reg (r 47)=2^(c.store.reg (r 46))
    rw [hcp,hcv.1,hcv.2.1]
    exact hq
  have hce : c.reg (randomLayout r hr).random.ell ≤ c.reg (randomLayout r hr).random.q := by
    change c.store.reg (r 46) ≤ c.store.reg (r 47)
    rw [hcp,hcv.1,hcv.2.1]
    exact he
  have hck : c.reg (randomLayout r hr).count=2*k*s.reg (r 35)*d := by change c.store.reg (r 52)=_;rw [hcp];exact hcv.2.2
  obtain ⟨t₃,e,ht₃,he,hes⟩ := markedFill_stops_bound (randomLayout r hr) b inp
    (2*k*s.reg (r 35)*d) c.store M hck hp (hcb _) hcq hce hcc
  have hall := (ha.seq hc).seq he
  refine ⟨_,_,?_,hall,?_,?_⟩
  · nlinarith
  · change e.store=_
    rw [hes,hcp]
    rfl
  · change ∀ j,e.store.reg j ≤ M
    rw [hes]
    exact markedFillStore_bound _ _ _ _ _ M hcb hcc














theorem hashPrepareStore_values (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (s : TapeStore R B) :
    (hashPrepareStore r k s).reg (r 46)=s.reg (r 38) ∧
    (hashPrepareStore r k s).reg (r 47)=s.reg (r 39) ∧
    (hashPrepareStore r k s).reg (r 52)=k*(s.reg (r 35))^3 := by
  have h := prepareRandomStore_values r hr 38 39 (by decide) (hashCountStore r k s)
  refine ⟨?_,?_,?_⟩
  · rw [show (hashPrepareStore r k s).reg (r 46)=(hashCountStore r k s).reg (r 38) from h.1]
    exact hashCountStore_fresh r k s _ (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
  · rw [show (hashPrepareStore r k s).reg (r 47)=(hashCountStore r k s).reg (r 39) from h.2.1]
    exact hashCountStore_fresh r k s _ (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
  · rw [hashPrepareStore,prepareRandomStore_fresh r 38 39 _ _
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)),hashCountStore_value r hr]

theorem hashPrepareStore_clean (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (s : TapeStore R B) (hc : RandomTables.Clean (randomLayout r hr).random s) :
    RandomTables.Clean (randomLayout r hr).random (hashPrepareStore r k s) := by
  change s.reg (r 48)=0 ∧ s.reg (r 49)=0 ∧ s.reg (r 50)=0 ∧ s.reg (r 51)=0 at hc
  change (hashPrepareStore r k s).reg (r 48)=0 ∧
    (hashPrepareStore r k s).reg (r 49)=0 ∧
    (hashPrepareStore r k s).reg (r 50)=0 ∧ (hashPrepareStore r k s).reg (r 51)=0
  rcases hc with ⟨h48,h49,h50,h51⟩
  simp [hashPrepareStore,prepareRandomStore,hashCountStore,staticScaleStore,hashScaleLayout,
    cubeStore,cubeSquare,multiplyStore,SamplerEvaluation.reg_layout r hr,h48,h49,h50]

theorem hashFill_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (b : Fin B) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ j,s.reg j ≤ M) (hk : k ≤ M)
    (hQ : (s.reg (r 35))^2 ≤ M) (hC : (s.reg (r 35))^3 ≤ M)
    (hp : k*(s.reg (r 35))^3 ≤ M)
    (hq : s.reg (r 39)=2^(s.reg (r 38))) (he : s.reg (r 38) ≤ s.reg (r 39))
    (hclean : RandomTables.Clean (randomLayout r hr).random s) :
    ∃ t e,t ≤ 230*(M+1)^3 ∧
      (hashFill r hr k b).Stops inp (s.toCfg (hashFill r hr k b).entry) t e ∧
      e.store=hashFillStore r hr k b inp s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,a,ht₁,ha,has,hab⟩ := hashCount_stops r hr k inp M s hs hk hQ hC hp
  obtain ⟨t₂,c,ht₂,hc,hcs,hcb⟩ := prepareRandom_stops r hr 38 39 (by decide) (by decide)
    inp M a.store hab
  have hcp : c.store=hashPrepareStore r k s := by rw [hcs,has];rfl
  have hcv := hashPrepareStore_values r hr k s
  have hcc : RandomTables.Clean (randomLayout r hr).random c.store := by
    rw [hcp];exact hashPrepareStore_clean r hr k s hclean
  have hcq : c.reg (randomLayout r hr).random.q=2^(c.reg (randomLayout r hr).random.ell) := by
    change c.store.reg (r 47)=2^(c.store.reg (r 46))
    rw [hcp,hcv.1,hcv.2.1]
    exact hq
  have hce : c.reg (randomLayout r hr).random.ell ≤ c.reg (randomLayout r hr).random.q := by
    change c.store.reg (r 46) ≤ c.store.reg (r 47)
    rw [hcp,hcv.1,hcv.2.1]
    exact he
  have hck : c.reg (randomLayout r hr).count=k*(s.reg (r 35))^3 := by change c.store.reg (r 52)=_;rw [hcp];exact hcv.2.2
  obtain ⟨t₃,e,ht₃,he,hes⟩ := markedFill_stops_bound (randomLayout r hr) b inp
    (k*(s.reg (r 35))^3) c.store M hck hp (hcb _) hcq hce hcc
  have hall := (ha.seq hc).seq he
  refine ⟨_,_,?_,hall,?_,?_⟩
  · nlinarith
  · change e.store=_
    rw [hes,hcp]
    rfl
  · change ∀ j,e.store.reg j ≤ M
    rw [hes]
    exact markedFillStore_bound _ _ _ _ _ M hcb hcc

theorem formFillStore_low (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B) (j : Fin 80) (hj : j.val<46) :
    (formFillStore r hr d k b inp s).reg (r j)=s.reg (r j) := by
  unfold formFillStore
  rw [markedFillStore_reg_other]
  · rw [formPrepareStore,prepareRandomStore_fresh]
    · exact formCountStore_fresh r d k s _ (hr.ne (by omega)) (hr.ne (by omega))
        (hr.ne (by omega)) (hr.ne (by omega))
    all_goals exact hr.ne (by omega)
  all_goals apply hr.ne;apply Fin.ne_of_val_ne; dsimp [randomLayout,randomRegisters,
    RandomBits.Layout.acc,RandomBits.Layout.count,RandomBits.Layout.tmp,RandomBits.Layout.scratch];omega

theorem hashFillStore_low (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B) (j : Fin 80) (hj : j.val<46) :
    (hashFillStore r hr k b inp s).reg (r j)=s.reg (r j) := by
  unfold hashFillStore
  rw [markedFillStore_reg_other]
  · rw [hashPrepareStore,prepareRandomStore_fresh]
    · exact hashCountStore_fresh r k s _ (hr.ne (by omega)) (hr.ne (by omega))
        (hr.ne (by omega)) (hr.ne (by omega)) (hr.ne (by omega)) (hr.ne (by omega))
    all_goals exact hr.ne (by omega)
  all_goals apply hr.ne;apply Fin.ne_of_val_ne; dsimp [randomLayout,randomRegisters,
    RandomBits.Layout.acc,RandomBits.Layout.count,RandomBits.Layout.tmp,RandomBits.Layout.scratch];omega

theorem formFillStore_clean (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hc : RandomTables.Clean (randomLayout r hr).random s) :
    RandomTables.Clean (randomLayout r hr).random (formFillStore r hr d k b inp s) :=
  RandomTables.fillStore_clean _ _ _ _ _ (formPrepareStore_clean r hr d k s hc)

theorem formFillStore_roHead (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B) :
    (formFillStore r hr d k b inp s).roHead=
      Function.update s.roHead 3 (s.roHead 3+(2*k*s.reg (r 35)*d)*s.reg (r 34)) := by
  unfold formFillStore
  rw [markedFillStore_roHead]
  change Function.update s.roHead 3
    (s.roHead 3+(2*k*s.reg (r 35)*d)*(formPrepareStore r d k s).reg (r 46))=_
  rw [(formPrepareStore_values r hr d k s).1]











theorem formFillStore_table (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 35)=2^(s.reg (r 34))) (hh : s.bufferHead b=0) :
    TapeArrays.ThermometerTable (formFillStore r hr d k b inp s) b (s.reg (r 35))
      (fun i => (RandomTables.sampledValues inp (2*k*s.reg (r 35)*d) (s.reg (r 34)) (s.roHead 3) i).val) := by
  have hv := formPrepareStore_values r hr d k s
  have hpq : (formPrepareStore r d k s).reg (randomLayout r hr).random.q=
      2^((formPrepareStore r d k s).reg (randomLayout r hr).random.ell) := by
    change (formPrepareStore r d k s).reg (r 47)=2^((formPrepareStore r d k s).reg (r 46))
    rw [hv.1,hv.2.1];exact hq
  have h := markedFillStore_table (randomLayout r hr) b inp (2*k*s.reg (r 35)*d)
    (formPrepareStore r d k s) hpq hh
  change TapeArrays.ThermometerTable (formFillStore r hr d k b inp s) b
    ((formPrepareStore r d k s).reg (r 47))
    (fun i => (RandomTables.sampledValues inp (2*k*s.reg (r 35)*d)
      ((formPrepareStore r d k s).reg (r 46)) (s.roHead 3) i).val) at h
  simpa [RandomTables.sampledValues,hv.1,hv.2.1] using h

theorem hashFillStore_table (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 39)=2^(s.reg (r 38))) (hh : s.bufferHead b=0) :
    TapeArrays.ThermometerTable (hashFillStore r hr k b inp s) b (s.reg (r 39))
      (fun i => (RandomTables.sampledValues inp (k*(s.reg (r 35))^3) (s.reg (r 38)) (s.roHead 3) i).val) := by
  have hv := hashPrepareStore_values r hr k s
  have hpq : (hashPrepareStore r k s).reg (randomLayout r hr).random.q=
      2^((hashPrepareStore r k s).reg (randomLayout r hr).random.ell) := by
    change (hashPrepareStore r k s).reg (r 47)=2^((hashPrepareStore r k s).reg (r 46))
    rw [hv.1,hv.2.1];exact hq
  have h := markedFillStore_table (randomLayout r hr) b inp (k*(s.reg (r 35))^3)
    (hashPrepareStore r k s) hpq hh
  change TapeArrays.ThermometerTable (hashFillStore r hr k b inp s) b
    ((hashPrepareStore r k s).reg (r 47))
    (fun i => (RandomTables.sampledValues inp (k*(s.reg (r 35))^3)
      ((hashPrepareStore r k s).reg (r 46)) (s.roHead 3) i).val) at h
  simpa [RandomTables.sampledValues,hv.1,hv.2.1] using h







theorem formFillStore_head (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 35)=2^(s.reg (r 34))) (hh : s.bufferHead b=0) :
    (formFillStore r hr d k b inp s).bufferHead=
      Function.update s.bufferHead b (1+(2*k*s.reg (r 35)*d)*s.reg (r 35)) := by
  have hv := formPrepareStore_values r hr d k s
  have hpq : (formPrepareStore r d k s).reg (randomLayout r hr).random.q=
      2^((formPrepareStore r d k s).reg (randomLayout r hr).random.ell) := by
    change (formPrepareStore r d k s).reg (r 47)=2^((formPrepareStore r d k s).reg (r 46))
    rw [hv.1,hv.2.1];exact hq
  rw [formFillStore,markedFillStore_head _ _ _ _ _ hpq hh]
  change Function.update s.bufferHead b
    (1+(2*k*s.reg (r 35)*d)*(formPrepareStore r d k s).reg (r 47))=_
  rw [hv.2.1]

theorem hashFillStore_head (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 39)=2^(s.reg (r 38))) (hh : s.bufferHead b=0) :
    (hashFillStore r hr k b inp s).bufferHead=
      Function.update s.bufferHead b (1+(k*(s.reg (r 35))^3)*s.reg (r 39)) := by
  have hv := hashPrepareStore_values r hr k s
  have hpq : (hashPrepareStore r k s).reg (randomLayout r hr).random.q=
      2^((hashPrepareStore r k s).reg (randomLayout r hr).random.ell) := by
    change (hashPrepareStore r k s).reg (r 47)=2^((hashPrepareStore r k s).reg (r 46))
    rw [hv.1,hv.2.1];exact hq
  rw [hashFillStore,markedFillStore_head _ _ _ _ _ hpq hh]
  change Function.update s.bufferHead b
    (1+(k*(s.reg (r 35))^3)*(hashPrepareStore r k s).reg (r 47))=_
  rw [hv.2.1]










theorem tables_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (bf bh : Fin B) (inp : Inputs) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ j,s.reg j ≤ M) (hc : 2*k*d ≤ M) (hf : 2*k*s.reg (r 35)*d ≤ M)
    (hk : k ≤ M) (hQ : (s.reg (r 35))^2 ≤ M) (hC : (s.reg (r 35))^3 ≤ M)
    (hh : k*(s.reg (r 35))^3 ≤ M)
    (hq : s.reg (r 35)=2^(s.reg (r 34))) (he : s.reg (r 34) ≤ s.reg (r 35))
    (hb : s.reg (r 39)=2^(s.reg (r 38))) (hbe : s.reg (r 38) ≤ s.reg (r 39))
    (hclean : RandomTables.Clean (randomLayout r hr).random s) :
    ∃ t e,t ≤ 391*(M+1)^3 ∧
      (tables r hr d k bf bh).Stops inp (s.toCfg (tables r hr d k bf bh).entry) t e ∧
      e.store=tablesStore r hr d k bf bh inp s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,a,ht₁,ha,has,hab⟩ := formFill_stops r hr d k bf inp M s hs hc hf hq he hclean
  have hav (j : Fin 80) (hj : j.val<46) : a.reg (r j)=s.reg (r j) := by
    change a.store.reg (r j)=_
    rw [has];exact formFillStore_low r hr d k bf inp s j hj
  have hac : RandomTables.Clean (randomLayout r hr).random a.store := by
    rw [has];exact formFillStore_clean r hr d k bf inp s hclean
  obtain ⟨t₂,e,ht₂,he,hes,heb⟩ := hashFill_stops r hr k bh inp M a.store hab hk
    (by simpa only [TapeCfg.store,hav 35 (by decide)] using hQ)
    (by simpa only [TapeCfg.store,hav 35 (by decide)] using hC)
    (by simpa only [TapeCfg.store,hav 35 (by decide)] using hh)
    (by simpa only [TapeCfg.store,hav 39 (by decide),hav 38 (by decide)] using hb)
    (by simpa only [TapeCfg.store,hav 39 (by decide),hav 38 (by decide)] using hbe) hac
  have hpos : 1 ≤ (M+1)^3 := Nat.one_le_pow _ _ (by omega)
  refine ⟨_,_,by omega,ha.seq he,?_,heb⟩
  change e.store=_
  rw [hes,has]
  rfl





theorem fieldLayout_injective (r : Fin 80 → Fin R) (hr : Function.Injective r) :
    Function.Injective (fieldLayout r) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val (hr h)
  exact hh








theorem prepareField_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M) :
    ∃ t e,t ≤ 14*M+15 ∧
      (prepareField r).Stops inp (s.toCfg (prepareField (B:=B) r).entry) t e ∧
      e.store=prepareFieldStore r s ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := copy_stops_bound (r 34) (r 20) (r 31)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M s hs
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂,hb₂⟩ := copy_stops_bound (r 35) (r 23) (r 31)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M c₁.store hb₁
  refine ⟨_,_,by omega,h₁.seq h₂,?_,hb₂⟩
  change c₂.store=_
  rw [hs₂,hs₁]
  rfl






theorem fieldSetup_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (hell : 0<ell) (M : ℕ) (s : TapeStore R B)
    (hs : ∀ j,s.reg j ≤ M) (he : s.reg (r 34)=ell) (hq : s.reg (r 35)=2^ell)
    (hN : 3*ell+1 ≤ M) (h2q : 2*(2^ell) ≤ M) (hQ : 2^(2*ell) ≤ M) :
    ∃ t e,t ≤ 40020*(M+1)^7 ∧
      (fieldSetup r).Stops inp (s.toCfg (fieldSetup (B:=B) r).entry) t e ∧
      e.store=fieldSetupStore r s ∧
      SamplerProgram.Environment (scalarLayout r) ell (ExpandingCodes.PolynomialStretch.BinaryPolynomial.selectedIndex ell hell) e.store ∧
      (∀ j,e.reg j ≤ M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨t₁,c,ht₁,hc,hcs,hcb⟩ := prepareField_stops r hr inp M s hs
  have hce : c.reg (fieldLayout r 20)=ell := by
    change c.store.reg (r 20)=ell
    rw [hcs]
    simpa [prepareFieldStore,SamplerEvaluation.reg_layout r hr] using he
  have hcq : c.reg (fieldLayout r 23)=2^ell := by
    change c.store.reg (r 23)=2^ell
    rw [hcs]
    simpa [prepareFieldStore,SamplerEvaluation.reg_layout r hr] using hq
  obtain ⟨t₂,e,ht₂,he,hes,henv,hef,heb,het⟩ := SourceFieldSetup.setup_stops (fieldLayout r)
    (fieldLayout_injective r hr) inp ell hell M c.store hcb hce hcq hN h2q hQ
  have hep : e.store=fieldSetupStore r s := by rw [hes,hcs];rfl
  refine ⟨_,_,?_,hc.seq he,hep,?_,heb,?_⟩
  · have hp : M+1 ≤ (M+1)^7 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 0<M+1 by omega) (show 1 ≤ 7 by decide)
    omega
  · exact ⟨henv.2.2.2.1,henv.2.2.1,henv.2.1,henv.2.2.2.2.1⟩
  · rw [het,hcs]
    rfl

theorem fieldSetupStore_fresh (r : Fin 80 → Fin R) (s : TapeStore R B)
    (j : Fin R) (hj : ∀ i : Fin 32,j≠fieldLayout r i) :
    (fieldSetupStore r s).reg j=s.reg j := by
  rw [fieldSetupStore,SourceFieldSetup.setupStore_outside (fieldLayout r) _ j hj]
  have h20 := hj 20
  have h23 := hj 23
  have h31 := hj 31
  simp [prepareFieldStore,TapeStore.setReg,fieldLayout] at h20 h23 h31 ⊢
  simp [h20,h23,h31]









































theorem Sizes.frame {r : Fin 80 → Fin R} {d n k : ℕ} {s e : TapeStore R B}
    (h : Sizes r d n k s) (hf : ∀ j : Fin 80,32 ≤ j.val → j.val<40 → e.reg (r j)=s.reg (r j)) :
    Sizes r d n k e := by
  rcases h with ⟨a,b,c,d,e,f,g,h⟩
  constructor
  all_goals first | rw [hf _ (by decide) (by decide)];assumption

 theorem sizeStageStore_sizes (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) (hd : 1 ≤ d) (hk : 0<k) (hn : 2 ≤ n) (hnk : k ≤ n) :
    Sizes r d n k (sizeStageStore (B:=B) r d n k) := by
  have h := setupStore_values (sizeLayout r) (sizeLayout_injective r hr) d k hd hk
    (SizeReader.sizeStore (r 32) n (initialStore R B))
    (by simpa [sizeLayout,SizeReader.sizeStore] using hn)
    (by simpa [sizeLayout,SizeReader.sizeStore] using hnk)
  constructor
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.1
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.2.1
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.2.2.1
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.2.2.2.1
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.2.2.2.2.1
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.2.2.2.2.2.1
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.2.2.2.2.2.2.1
  · simpa [sizeStageStore,sizeLayout,SizeReader.sizeStore] using h.2.2.2.2.2.2.2

theorem sizeStage_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) (hk : 0<k) (hn : 2 ≤ n) (hnk : k ≤ n) (inp : Inputs)
    (hi : inp.input=ExpandingCodes.PolynomialStretch.sizeInput n) :
    ∃ t e,t ≤ sizeStageTime d n ∧
      (setupInput (sizeLayout r) d k).Stops inp
        ((initialStore R B).toCfg (setupInput (B:=B) (sizeLayout r) d k).entry) t e ∧
      e.store=sizeStageStore r d n k ∧ (∀ j,e.reg j ≤ setupCounterBound d (n+1)) := by
  have hread := SizeReader.sizeInput_unary (r 32) inp n [] (initialStore R B) rfl hi
  have hb : ∀ j,(SizeReader.sizeStore (r 32) n (initialStore R B)).reg j ≤ n+1 := by
    intro j
    by_cases h:j=r 32
    · subst j;simp [SizeReader.sizeStore,initialStore,TapeStore.setReg]
    · simp [SizeReader.sizeStore,initialStore,TapeStore.setReg,h]
  obtain ⟨t,e,ht,he,hes,heb⟩ := setup_stops (sizeLayout r) (sizeLayout_injective r hr)
    d k hk inp (n+1) (by omega) (SizeReader.sizeStore (r 32) n (initialStore R B)) hb
    (by simp [sizeLayout,SizeReader.sizeStore];omega)
    (by simpa [sizeLayout,SizeReader.sizeStore] using hnk)
  have hall := hread.seq he
  refine ⟨_,_,?_,hall,hes,heb⟩
  change 0+2*n+3+1+t ≤ 2*n+4+setupTimeBound d (n+1)
  omega









theorem sizeStageStore_outside (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) (j : Fin R) (hj : ∀ i,j≠sizeLayout r i) :
    (sizeStageStore (B:=B) r d n k).reg j=0 := by
  rw [sizeStageStore,setupStore_fresh (sizeLayout r) (sizeLayout_injective r hr) d k _ j hj]
  have h32 : j≠r 32 := hj 0
  simp [SizeReader.sizeStore,TapeStore.setReg,h32,initialStore]

theorem sizeStageStore_clean (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) : RandomTables.Clean (randomLayout r hr).random (sizeStageStore (B:=B) r d n k) := by
  constructor
  · apply sizeStageStore_outside r hr
    intro i heq
    have hh := congrArg Fin.val (hr heq)
    have := i.isLt
    change (48 : ℕ)=32+i.val at hh
    omega
  constructor
  · apply sizeStageStore_outside r hr
    intro i heq
    have hh := congrArg Fin.val (hr heq)
    have := i.isLt
    change (49 : ℕ)=32+i.val at hh
    omega
  constructor
  · apply sizeStageStore_outside r hr
    intro i heq
    have hh := congrArg Fin.val (hr heq)
    have := i.isLt
    change (50 : ℕ)=32+i.val at hh
    omega
  · apply sizeStageStore_outside r hr
    intro i heq
    have hh := congrArg Fin.val (hr heq)
    have := i.isLt
    change (51 : ℕ)=32+i.val at hh
    omega

theorem sizeStageStore_tapeData (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) : FieldConvolution.tapeData (sizeStageStore (B:=B) r d n k)=
      FieldConvolution.tapeData (SizeReader.sizeStore (r 32) n (initialStore R B)) := by
  have h := setupStore_payload (sizeLayout r) (sizeLayout_injective r hr) d k
    (SizeReader.sizeStore (r 32) n (initialStore R B))
  exact congrArg₂ Prod.mk h.1 (congrArg₂ Prod.mk h.2.1 (congrArg₂ Prod.mk h.2.2.1 h.2.2.2))

theorem formPrepareStore_q (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (s : TapeStore R B) (hq : s.reg (r 35)=2^(s.reg (r 34))) :
    (formPrepareStore r d k s).reg (randomLayout r hr).random.q=
      2^((formPrepareStore r d k s).reg (randomLayout r hr).random.ell) := by
  change (formPrepareStore r d k s).reg (r 47)=2^((formPrepareStore r d k s).reg (r 46))
  rw [(formPrepareStore_values r hr d k s).1,(formPrepareStore_values r hr d k s).2.1]
  exact hq

theorem hashPrepareStore_q (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (s : TapeStore R B) (hq : s.reg (r 39)=2^(s.reg (r 38))) :
    (hashPrepareStore r k s).reg (randomLayout r hr).random.q=
      2^((hashPrepareStore r k s).reg (randomLayout r hr).random.ell) := by
  change (hashPrepareStore r k s).reg (r 47)=2^((hashPrepareStore r k s).reg (r 46))
  rw [(hashPrepareStore_values r hr k s).1,(hashPrepareStore_values r hr k s).2.1]
  exact hq

theorem formFillStore_other_symbol (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 35)=2^(s.reg (r 34))) (c : Fin B) (hcb : c≠b) (j : ℕ) :
    ((formFillStore r hr d k b inp s).bufferTape c).getD j .blank=(s.bufferTape c).getD j .blank :=
  markedFillStore_other_symbol _ b inp _ (formPrepareStore r d k s)
    (formPrepareStore_q r hr d k s hq) c hcb j

theorem hashFillStore_other_symbol (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 39)=2^(s.reg (r 38))) (c : Fin B) (hcb : c≠b) (j : ℕ) :
    ((hashFillStore r hr k b inp s).bufferTape c).getD j .blank=(s.bufferTape c).getD j .blank :=
  markedFillStore_other_symbol _ b inp _ (hashPrepareStore r k s)
    (hashPrepareStore_q r hr k s hq) c hcb j

theorem formFillStore_bottomMarked (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 35)=2^(s.reg (r 34))) (hh : s.bufferHead b=0)
    (hb : ∀ j,(s.bufferTape b).getD j .blank=.blank) :
    TapeArrays.BottomMarked (formFillStore r hr d k b inp s) b :=
  markedFillStore_bottomMarked _ b inp _ (formPrepareStore r d k s)
    (formPrepareStore_q r hr d k s hq) hh hb

theorem hashFillStore_bottomMarked (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B)
    (hq : s.reg (r 39)=2^(s.reg (r 38))) (hh : s.bufferHead b=0)
    (hb : ∀ j,(s.bufferTape b).getD j .blank=.blank) :
    TapeArrays.BottomMarked (hashFillStore r hr k b inp s) b :=
  markedFillStore_bottomMarked _ b inp _ (hashPrepareStore r k s)
    (hashPrepareStore_q r hr k s hq) hh hb

theorem formFillStore_output (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B) :
    (formFillStore r hr d k b inp s).output=s.output :=
  markedFillStore_output _ _ _ _ _

theorem hashFillStore_output (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (b : Fin B) (inp : Inputs) (s : TapeStore R B) :
    (hashFillStore r hr k b inp s).output=s.output :=
  markedFillStore_output _ _ _ _ _

theorem tablesStore_output (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (bf bh : Fin B) (inp : Inputs) (s : TapeStore R B) :
    (tablesStore r hr d k bf bh inp s).output=s.output := by
  rw [tablesStore,hashFillStore_output,formFillStore_output]

theorem tablesStore_sizes (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) (bf bh : Fin B) (inp : Inputs) (s : TapeStore R B) (hs : Sizes r d n k s) :
    Sizes r d n k (tablesStore r hr d k bf bh inp s) := by
  apply hs.frame
  intro j hj hj'
  rw [tablesStore,hashFillStore_low r hr k bh inp _ j (by omega),
    formFillStore_low r hr d k bf inp s j (by omega)]

















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

theorem tablesStore_ready (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) (inp : Inputs) (M : ℕ) (s : TapeStore R 2) (hs : Sizes r d n k s)
    (hro : s.roHead 3=0) (hhead : ∀ b,s.bufferHead b=0)
    (hblank : ∀ b j,(s.bufferTape b).getD j .blank=.blank)
    (hfM : 1+2*k*ExpandingCodes.PolynomialStretch.fieldSize d n*d*
      ExpandingCodes.PolynomialStretch.fieldSize d n ≤ M)
    (hhM : 1+k*(ExpandingCodes.PolynomialStretch.fieldSize d n)^3*2^Nat.log 2 (n/k) ≤ M) :
    TablesReady d n k inp M (tablesStore r hr d k 0 1 inp s) := by
  let a := formFillStore r hr d k (0 : Fin 2) inp s
  have hq : s.reg (r 35)=2^(s.reg (r 34)) := by rw [hs.field,hs.ell];rfl
  have hav (j : Fin 80) (hj : j.val<46) : a.reg (r j)=s.reg (r j) :=
    formFillStore_low r hr d k 0 inp s j hj
  have haβ : a.reg (r 39)=2^(a.reg (r 38)) := by
    rw [hav 39 (by decide),hav 38 (by decide),hs.buckets,hs.beta]
  have hah : a.bufferHead 1=0 := by
    have ht := formFillStore_head r hr d k (0 : Fin 2) inp s hq (hhead 0)
    change a.bufferHead=Function.update s.bufferHead 0 (1+(2*k*s.reg (r 35)*d)*s.reg (r 35)) at ht
    rw [ht]
    simpa using hhead 1
  have hab : ∀ j,(a.bufferTape 1).getD j .blank=.blank := by
    intro j
    rw [formFillStore_other_symbol r hr d k 0 inp s hq 1 (by decide)]
    exact hblank 1 j
  have hf : TapeArrays.ThermometerTable a 0 (ExpandingCodes.PolynomialStretch.fieldSize d n)
      (fun i => (RandomTables.sampledValues inp (2*k*ExpandingCodes.PolynomialStretch.fieldSize d n*d)
        (ExpandingCodes.PolynomialStretch.fieldExponent d n) 0 i).val) := by
    have ht := formFillStore_table r hr d k 0 inp s hq (hhead 0)
    rw [hs.field,hs.ell,hro] at ht
    simpa [RandomTables.sampledValues] using ht
  have hhash : TapeArrays.ThermometerTable (hashFillStore r hr k 1 inp a) 1 (2^Nat.log 2 (n/k))
      (fun i => (RandomTables.sampledValues inp
        (k*ExpandingCodes.PolynomialStretch.fieldSize d n*ExpandingCodes.PolynomialStretch.fieldSize d n*
          ExpandingCodes.PolynomialStretch.fieldSize d n) (Nat.log 2 (n/k))
        ((2*k*ExpandingCodes.PolynomialStretch.fieldSize d n*d)*ExpandingCodes.PolynomialStretch.fieldExponent d n) i).val) := by
    have ht := hashFillStore_table r hr k 1 inp a haβ hah
    have har : a.roHead 3=(2*k*ExpandingCodes.PolynomialStretch.fieldSize d n*d)*
        ExpandingCodes.PolynomialStretch.fieldExponent d n := by
      rw [formFillStore_roHead]
      simp [hro,hs.field,hs.ell]
    rw [hav 35 (by decide),hav 38 (by decide),hav 39 (by decide),hs.field,hs.beta,hs.buckets,har] at ht
    rw [show k*(fieldSize d n)^3=k*fieldSize d n*fieldSize d n*fieldSize d n by ring] at ht
    simpa [RandomTables.sampledValues,Nat.mul_assoc] using ht
  have hfm : TapeArrays.BottomMarked a 0 :=
    formFillStore_bottomMarked r hr d k 0 inp s hq (hhead 0) (hblank 0)
  have hhm : TapeArrays.BottomMarked (hashFillStore r hr k 1 inp a) 1 :=
    hashFillStore_bottomMarked r hr k 1 inp a haβ hah hab
  constructor
  · intro i
    refine ⟨(hf i).1,?_⟩
    intro j hj
    change ((hashFillStore r hr k 1 inp a).bufferTape 0).getD _ .blank=_
    rw [hashFillStore_other_symbol r hr k 1 inp a haβ 0 (by decide)]
    exact (hf i).2 j hj
  · exact hhash
  · intro b
    fin_cases b
    · constructor
      · change ((hashFillStore r hr k 1 inp a).bufferTape 0).getD 0 .blank=.bot
        rw [hashFillStore_other_symbol r hr k 1 inp a haβ 0 (by decide)]
        exact hfm.1
      · intro j hj
        change ((hashFillStore r hr k 1 inp a).bufferTape 0).getD j .blank≠.bot
        rw [hashFillStore_other_symbol r hr k 1 inp a haβ 0 (by decide)]
        exact hfm.2 j hj
    · exact hhm
  · intro b
    change (hashFillStore r hr k 1 inp a).bufferHead b ≤ M
    rw [hashFillStore_head r hr k 1 inp a haβ hah]
    fin_cases b
    · simp only [Function.update_of_ne (by decide : (0 : Fin 2)≠1)]
      change (formFillStore r hr d k 0 inp s).bufferHead 0 ≤ M
      rw [formFillStore_head r hr d k 0 inp s hq (hhead 0)]
      simp only [Function.update_self]
      simpa [hs.field,Nat.mul_assoc] using hfM
    · simp only [Function.update_self]
      simpa [hav 35 (by decide),hav 39 (by decide),hs.field,hs.buckets] using hhM

open ExpandingCodes.PolynomialStretch


















theorem prelude_stops (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) (hd : 1 ≤ d) (hk : 0<k) (hn : 2 ≤ n) (hnk : k ≤ n)
    (inp : Inputs) (hi : inp.input=sizeInput n) (M : ℕ) (hM : SamplerEnvelopeCovers d k n M) :
    ∃ t e,t ≤ preludeTime d n M ∧
      (samplerFrontendProgram r hr d k).Stops inp ((initialStore R 2).toCfg (samplerFrontendProgram r hr d k).entry) t e ∧
      e.store=preludeStore r hr d n k inp ∧ RuntimeReady r d n k inp M e.store ∧ e.output=[] := by
  obtain ⟨t₁,a,ht₁,ha,has,hab⟩ := sizeStage_stops (B:=2) r hr d n k hk hn hnk inp hi
  have haSizes : Sizes r d n k a.store := by rw [has];exact sizeStageStore_sizes r hr d n k hd hk hn hnk
  have haBounds : ∀ j,a.reg j ≤ M := fun j => (hab j).trans hM.setup
  have haField : a.reg (r 35)=fieldSize d n := haSizes.field
  have haEll : a.reg (r 34)=fieldExponent d n := haSizes.ell
  have haBeta : a.reg (r 38)=Nat.log 2 (n/k) := haSizes.beta
  have haBucket : a.reg (r 39)=2^Nat.log 2 (n/k) := haSizes.buckets
  have haClean : RandomTables.Clean (randomLayout r hr).random a.store := by
    rw [has];exact sizeStageStore_clean r hr d n k
  have haq : a.reg (r 35)=2^(a.reg (r 34)) := by rw [haField,haEll];rfl
  have hae : a.reg (r 34) ≤ a.reg (r 35) := by
    change a.store.reg _ ≤ a.store.reg _
    rw [haSizes.field,haSizes.ell]
    exact (Nat.lt_two_pow_self : fieldExponent d n<2^(fieldExponent d n)).le
  have haβ : a.reg (r 39)=2^(a.reg (r 38)) := by
    rw [haBucket,haBeta]
  have habe : a.reg (r 38) ≤ a.reg (r 39) := by
    change a.store.reg _ ≤ a.store.reg _
    rw [haSizes.buckets,haSizes.beta]
    exact (Nat.lt_two_pow_self : Nat.log 2 (n/k)<2^Nat.log 2 (n/k)).le
  have hq1 : 1 ≤ fieldSize d n := Nat.one_le_pow _ _ (by decide)
  have hb1 : 1 ≤ samplerBucketCount k n := Nat.one_le_pow _ _ (by decide)
  have hkc : k ≤ M := by have := hM.constants;omega
  have hc : 2*k*d ≤ M := by have := hM.constants;omega
  have hf : 2*k*fieldSize d n*d ≤ M := by
    have hp := Nat.mul_le_mul_left (2*k*fieldSize d n*d) hq1
    have hc := hM.forms
    nlinarith
  have hh : k*(fieldSize d n)^3 ≤ M := by
    have hp := Nat.mul_le_mul_left (k*(fieldSize d n)^3) hb1
    have hc := hM.hashes
    unfold samplerBucketCount at hp hc
    nlinarith
  have hC : (fieldSize d n)^3 ≤ M := by
    have hp := Nat.mul_le_mul_right ((fieldSize d n)^3) (show 1 ≤ k by omega)
    simpa only [one_mul] using hp.trans hh
  obtain ⟨t₂,c,ht₂,hc,hcs,hcb⟩ := tables_stops r hr d k 0 1 inp M a.store haBounds hc
    (by simpa only [haField] using hf) hkc
    (by simpa only [haField] using hM.square)
    (by simpa only [haField] using hC)
    (by simpa only [haField] using hh) haq hae haβ habe haClean
  have hcSizes : Sizes r d n k c.store := by rw [hcs];exact tablesStore_sizes r hr d n k 0 1 inp a.store haSizes
  have haTape := sizeStageStore_tapeData (B:=2) r hr d n k
  have har : a.roHead 3=0 := by
    change a.store.roHead 3=0
    rw [has]
    exact congrArg (fun z => z.1 3) haTape
  have hah : ∀ b,a.bufferHead b=0 := by
    intro b
    change a.store.bufferHead b=0
    rw [has]
    exact congrArg (fun z => z.2.2.2 b) haTape
  have hab : ∀ b j,(a.bufferTape b).getD j .blank=.blank := by
    intro b j
    have h := congrArg (fun z => (z.2.2.1 b).getD j .blank) haTape
    change (a.store.bufferTape b).getD j .blank=.blank
    rw [has]
    exact h
  have hcTables : TablesReady d n k inp M c.store := by
    rw [hcs]
    apply tablesStore_ready r hr d n k inp M a.store haSizes har hah hab
    · simpa only [Nat.add_comm,Nat.mul_assoc] using hM.forms
    · simpa only [samplerBucketCount,Nat.add_comm] using hM.hashes
  have hQ : 2^(2*fieldExponent d n) ≤ M := by
    rw [show 2*fieldExponent d n=fieldExponent d n*2 by omega,pow_mul]
    exact hM.square
  obtain ⟨t₃,e,ht₃,he,hes,henv,heb,het⟩ := fieldSetup_stops r hr inp (fieldExponent d n)
    (fieldExponent_pos d n) M c.store hcb hcSizes.ell hcSizes.field hM.coefficients hM.twiceField hQ
  have hep : e.store=preludeStore r hr d n k inp := by rw [hes,hcs,has];rfl
  have heSizes : Sizes r d n k e.store := by
    apply hcSizes.frame
    intro j hj hj'
    rw [hes]
    apply fieldSetupStore_fresh
    intro i heq
    have h := congrArg Fin.val (hr heq)
    change j.val=i.val at h
    have := i.isLt
    omega
  have heTables : TablesReady d n k inp M e.store := by
    apply hcTables.frame
    · intro b j
      exact congrArg (fun z => (z.2.2.1 b).getD j .blank) het
    · intro b
      have hh := congrArg (fun z => z.2.2.2 b) het
      exact hh.le.trans (hcTables.heads b)
  have heOut : e.output=[] := by
    have heo := congrArg (fun z => z.2.1) het
    change e.store.output=c.store.output at heo
    change e.store.output=[]
    rw [heo,hcs,tablesStore_output,has]
    exact congrArg (fun z => z.2.1) haTape
  refine ⟨_,_,?_,(ha.seq hc).seq he,hep,⟨heSizes,henv,heTables,heb⟩,heOut⟩
  unfold preludeTime
  omega







































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

theorem solution {R : ℕ} (r : Fin 80 → Fin R) (hr : Function.Injective r)
    (d n k : ℕ) (hd : 1 ≤ d) (hk : 0<k) (hn : 2 ≤ n) (hnk : k ≤ n)
    (inp : Inputs) (hi : inp.input=ExpandingCodes.PolynomialStretch.sizeInput n) (M : ℕ) (hM : ExpandingCodes.PolynomialStretch.SamplerEnvelopeCovers d k n M) :
    ∃ t e,t ≤ ExpandingCodes.Computation.SamplerAssembly.preludeTime d n M ∧
      (ExpandingCodes.Computation.SamplerAssembly.samplerFrontendProgram r hr d k).Stops inp ((ExpandingCodes.Computation.SamplerAssembly.initialStore R 2).toCfg (ExpandingCodes.Computation.SamplerAssembly.samplerFrontendProgram r hr d k).entry) t e ∧
      e.store=ExpandingCodes.Computation.SamplerAssembly.preludeStore r hr d n k inp ∧ ExpandingCodes.Computation.SamplerAssembly.RuntimeReady r d n k inp M e.store ∧ e.output=[] := by
  exact @ExpandingCodes.Computation.SamplerAssembly.prelude_stops R r hr d n k hd hk hn hnk inp hi M hM

