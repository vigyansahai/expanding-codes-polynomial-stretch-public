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

/-! Inlined whole module: ExpandingCodes.Construction.Geometry -/
section FlattenModule3



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch





private theorem fieldSize_pos (d n : ℕ) : 0 < fieldSize d n := by
  exact pow_pos (by decide) _

private theorem fieldSize_ge_two (d n : ℕ) : 2 ≤ fieldSize d n := by
  unfold fieldSize
  have h := fieldExponent_pos d n
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ fieldExponent d n := Nat.pow_le_pow_right (by decide) h



























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













 private theorem cell_stops (b : Fin B) (action : Sym → Sym × Move) (inp : Inputs)
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

@[simp] private theorem setReg_self (d : TapeStore R B) (r : Fin R) :
    d.setReg r (d.reg r) = d := by simp [TapeStore.setReg]

@[simp] private theorem reg_set_same (d : TapeStore R B) (r : Fin R) (n : ℕ) :
    (d.setReg r n).reg r = n := by simp [TapeStore.setReg]

















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

private theorem multiply_stops_polynomial (a b dst tmp count : Fin R)
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











private theorem halveStore_step (d : TapeStore R B) (src quotient parity : Fin R)
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

private theorem halveLoop_stops (src quotient parity : Fin R)
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

private theorem halveLoop_time_le (n : ℕ) : 3*(n/2)+2*(n%2)+1 ≤ 2*n+1 := by omega





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






 












@[simp] private theorem moved_reg (d : TapeStore R B) (b : Fin B) (m : Move) :
    (moved d b m).reg = d.reg := rfl

@[simp] private theorem moved_head (d : TapeStore R B) (b : Fin B) (m : Move) :
    (moved d b m).bufferHead = Function.update d.bufferHead b (Machine.moveHead m (d.bufferHead b)) := rfl








 















































 





























































 





























 






















 








 









 










 



















































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

 










































 








 





 









 































 































































 
























 














 




































































 































 














 





























































 

























































 


 








 private theorem EntryWritten.bottomMarked {d e : TapeStore R B} {b : Fin B} {start w v : ℕ}
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










private theorem halve_stops (src quotient parity : Fin R)
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









private theorem halfStep_stops (src quotient parity : Fin R)
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

private theorem halfStep_time_le (n q p : ℕ) : q+p+5*(n/2)+2*(n%2)+7 ≤ q+p+3*n+7 := by omega













































































private theorem setReg_bound (d : TapeStore R B) (r : Fin R) (n M : ℕ)
    (hd : ∀ j, d.reg j ≤ M) (hn : n ≤ M) : ∀ j, (d.setReg r n).reg j ≤ M := by
  intro j
  by_cases h : j = r
  · subst j; simpa using hn
  · simpa [TapeStore.setReg, h] using hd j

private theorem halfStepStore_bound (d : TapeStore R B) (src quotient parity : Fin R)
    (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (halfStepStore d src quotient parity).reg j ≤ M := by
  apply setReg_bound _ parity _ M
  · apply setReg_bound _ quotient 0 M
    · apply setReg_bound d src _ M hd
      exact (Nat.div_le_self _ _).trans (hd src)
    · omega
  · omega

















































































































































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











private theorem raise_stops (r : Fin R) (c : ℕ) (inp : Inputs) (d : TapeStore R B) :
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





private theorem loadConstant_stops (r : Fin R) (c : ℕ) (inp : Inputs) (d : TapeStore R B) :
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

















































































































































































/-- Modular exact loop execution allowing a body temporarily to use its loop
counter, provided that it restores the counter before returning. -/
private theorem loop_stops (P : TapeProgram R B L) (counter : Fin R)
    (F : TapeStore R B → TapeStore R B) (inp : Inputs) (C : ℕ)
    (Inv : ℕ → TapeStore R B → Prop)
    (hcounter : ∀ d, (F d).reg counter = d.reg counter)
    (hbody : ∀ n d, d.reg counter = n+1 → Inv (n+1) d →
      ∃ t c, t ≤ C ∧ P.Stops inp ((d.setReg counter n).toCfg P.entry) t c ∧
        c.store = F (d.setReg counter n) ∧ Inv n c.store)
    (n : ℕ) (d : TapeStore R B) (hn : d.reg counter = n) (hi : Inv n d) :
    ∃ t, t ≤ n*(C+2)+1 ∧
      (TapeProgram.countedLoop P counter).Stops inp (d.toCfg (TapeProgram.loopHeader L)) t
        ((loopResult counter F n d).toCfg (TapeProgram.loopExit L)) ∧
      Inv 0 (loopResult counter F n d) := by
  induction n generalizing d with
  | zero => exact ⟨1, by omega, TapeProgram.loop_zero P counter inp d hn, hi⟩
  | succ n ih =>
    obtain ⟨s, c, hs, hc, hcs, hci⟩ := hbody n d hn hi
    have hcn : c.reg counter = n := by
      change c.store.reg counter = _
      rw [hcs, hcounter]
      simp [TapeStore.setReg]
    obtain ⟨t, ht, he, hei⟩ := ih c.store hcn hci
    have hhead := TapeProgram.loop_positive_header P counter inp d (by omega)
    have hdec : TapeProgram.decStore counter d = d.setReg counter n := by
      simp [TapeProgram.decStore, TapeStore.setReg, hn]
    rw [hdec] at hhead
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2) (TapeProgram.loop_code_body_active P counter)
    have hreturn := TapeProgram.loop_body_return P counter inp c hc.halted
    have hpost : loopResult counter F n c.store = loopResult counter F (n+1) d := by
      rw [loopResult, hcs]
    have hall := ((hhead.trans hrun).trans hreturn).trans he.exec
    rw [hpost] at hall hei
    refine ⟨_, ?_, ⟨hall, TapeProgram.loop_code_exit P counter⟩, hei⟩
    calc
      1+s+1+t ≤ 1+C+1+(n*(C+2)+1) := by omega
      _ = (n+1)*(C+2)+1 := by ring

private theorem loopResult_frame (counter : Fin R) (F : TapeStore R B → TapeStore R B)
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





















































































































































































































































































































































private theorem scaleAdd_stops (src dst tmp : Fin R) (hsd : src≠dst) (hst : src≠tmp) (hdt : dst≠tmp)
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



















































































































































































































































private theorem scaleStore_bound_exact (src dst tmp : Fin R) (c M : ℕ) (s : TapeStore R B)
    (hs : ∀ i,s.reg i   ≤   M) (hresult : s.reg dst+c*s.reg src   ≤   M) :
    ∀ i,(scaleStore src dst tmp c s).reg i   ≤   M := by
  exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hs hresult) (by omega)
















































































































































































































































































































































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
















private theorem Environment.frame {r : Fin 31 → Fin R} {ell : ℕ} {m : Fin (2^ell)}
    {s e : TapeStore R B} (h : Environment r ell m s)
    (hf : ∀ i : Fin 31,i=3 ∨ i=19 ∨ i=23 ∨ i=24 → e.reg (r i)=s.reg (r i)) :
    Environment r ell m e := by
  constructor
  · rw [hf 3 (by decide)]; exact h.modulus
  · rw [hf 19 (by decide)]; exact h.length
  · rw [hf 23 (by decide)]; exact h.cardinal
  · rw [hf 24 (by decide)]; exact h.square



























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































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


section FlattenModule62


set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterPowers
open NKtLB SamplerEvaluation SamplerProgram
open ExpandingCodes.PolynomialStretch BinaryPolynomial
open FieldPrograms UnaryArithmetic
variable {R B : ℕ}



































































































































































































































































































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








































































































































































































































































































































/-- Frozen integer-floor cutoff agrees with its nonnegative unary formula
for the construction parameter range. -/
private theorem auxiliaryDegree_nat (q d : ℕ) (hd : 4 ≤ d) (hq : 2 ≤ q) :
    auxiliaryDegree q d=((d-3)*(q-1)-1)/2 := by
  have hdcast : ((d-3 : ℕ) : ℤ)=(d : ℤ)-3 := by omega
  have hqcast : ((q-1 : ℕ) : ℤ)=(q : ℤ)-1 := by omega
  have hprod : 1 ≤ (d-3)*(q-1) := by
    have hh := Nat.mul_le_mul (show 1 ≤ d-3 by omega) (show 1 ≤ q-1 by omega)
    simpa using hh
  have hnum : (((d-3)*(q-1)-1 : ℕ) : ℤ)=((d : ℤ)-3)*((q : ℤ)-1)-1 := by
    rw [Nat.cast_sub hprod,Nat.cast_mul,hdcast,hqcast]
    norm_num
  unfold auxiliaryDegree
  rw [← hnum]
  rfl


















private theorem degree_stops (r : Fin 5 → Fin R) (hr : Function.Injective r) (d : ℕ)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (s : TapeStore R B) (hs : ∀ i,s.reg i ≤ M)
    (hprod : (d-3)*(s.reg (r 0)-1) ≤ M) :
    ∃ t e,t ≤ (d+1)*(30*(M+1)) ∧
      (degree r d).Stops inp (s.toCfg (degree (B := B) r d).entry) t e ∧
      e.store=degreeStore r d s ∧
      e.reg (r 4)=((d-3)*(s.reg (r 0)-1)-1)/2 ∧
      (∀ i,(∀ j,i≠r j) → e.reg i=s.reg i) ∧
      (∀ i,e.reg i ≤ M) ∧ FieldConvolution.tapeData e.store=FieldConvolution.tapeData s := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := copy_stops_bound (r 0) (r 1) (r 3)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M s hs
  have h₂ := SamplerOdometer.decrement_stops (r 1) inp c₁.store
  have hpred : c₁.store.setReg (r 1) (c₁.reg (r 1)-1)=
      (s.setReg (r 1) (s.reg (r 0)-1)).setReg (r 3) 0 := by
    rw [show c₁.reg (r 1)=s.reg (r 0) by rw [show c₁.reg (r 1)=c₁.store.reg (r 1) from rfl,hs₁]; simp [reg_layout r hr]]
    rw [hs₁]
    simp only [TapeStore.setReg]
    congr 1
    funext i
    by_cases h₁ : i=r 1 <;> by_cases h₃ : i=r 3 <;> simp_all [Function.update,hr.eq_iff]
  have h₃ := TapeMacros.clear_stops (r 2) inp ((c₁.store.setReg (r 1) (c₁.reg (r 1)-1)).reg (r 2))
    (c₁.store.setReg (r 1) (c₁.reg (r 1)-1)) rfl
  have hprepare : (c₁.store.setReg (r 1) (c₁.reg (r 1)-1)).setReg (r 2) 0=degreePrepare r s := by rw [hpred]; rfl
  obtain ⟨c₄,h₄,hs₄⟩ := SamplerEvaluation.scaleAdd_stops (r 1) (r 2) (r 3)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) (d-3) inp (degreePrepare r s)
    (by simp [degreePrepare,reg_layout r hr])
  have hscaled : c₄.store=degreeScaled r d s := hs₄
  have hv₄ : c₄.reg (r 2)=(d-3)*(s.reg (r 0)-1) := by
    change c₄.store.reg (r 2)=_
    rw [hscaled]
    simp [degreeScaled,scaleStore,degreePrepare,reg_layout r hr]
  have h₅ := SamplerOdometer.decrement_stops (r 2) inp c₄.store
  obtain ⟨e,h₆,hs₆⟩ := FieldPrograms.halve_stops (r 2) (r 4) (r 3)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp (c₄.store.setReg (r 2) (c₄.reg (r 2)-1))
  rw [← hprepare] at h₄
  have hall := ((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆
  have hpost : e.store=degreeStore r d s := by rw [hs₆,hv₄,hscaled]; rfl
  have hpb : ∀ i,(degreePrepare r s).reg i ≤ M := by
    unfold degreePrepare
    exact setReg_bound _ _ 0 M (setReg_bound _ _ 0 M
      (setReg_bound s _ _ M hs ((Nat.sub_le _ _).trans (hs (r 0)))) (by omega)) (by omega)
  have hsb : ∀ i,(degreeScaled r d s).reg i ≤ M := by
    apply SamplerEvaluation.scaleStore_bound_exact _ _ _ _ M _ hpb
    simpa [degreePrepare,reg_layout r hr] using hprod
  have hfinal : ∀ i,(degreeStore r d s).reg i ≤ M := by
    unfold degreeStore FieldPrograms.halfStore
    apply setReg_bound
    · apply setReg_bound
      · exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hsb ((Nat.sub_le _ _).trans hprod)) (by omega)
      · simpa [reg_layout r hr] using (Nat.div_le_self ((d-3)*(s.reg (r 0)-1)-1) 2).trans ((Nat.sub_le _ _).trans hprod)
    · simp only [reg_layout r hr,ite_true]
      have hh := Nat.mod_lt ((d-3)*(s.reg (r 0)-1)-1) (by omega : 0<2)
      omega
  refine ⟨_,_,?_,hall,hpost,?_,?_,?_,?_⟩
  · have hq := hs (r 0)
    have hb₂ := hs (r 2)
    have hb₄ : c₄.reg (r 4) ≤ M := by
      change c₄.store.reg (r 4) ≤ M
      rw [hscaled]; exact hsb (r 4)
    have hzero : c₄.reg (r 3)=0 := by
      change c₄.store.reg (r 3)=_
      rw [hscaled]; simp [degreeScaled,scaleStore]
    have hc₁₂ : c₁.reg (r 2)=s.reg (r 2) := by
      change c₁.store.reg (r 2)=_
      rw [hs₁]; simp [reg_layout r hr]
    have hc₁₁ : c₁.reg (r 1)=s.reg (r 0) := by
      change c₁.store.reg (r 1)=_
      rw [hs₁]; simp [reg_layout r hr]
    have hpredbound : (d-3)*(s.reg (r 0)-1)-1 ≤ M := (Nat.sub_le _ _).trans hprod
    have htime : 3*(((d-3)*(s.reg (r 0)-1)-1)/2)+2*(((d-3)*(s.reg (r 0)-1)-1)%2)+1 ≤ 2*((d-3)*(s.reg (r 0)-1)-1)+1 :=
      UnaryArithmetic.halveLoop_time_le _
    have hscale : (d-3)*(5*(s.reg (r 0)-1)+6) ≤ d*(5*M+6) :=
      Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
    change _ ≤ (d+1)*(30*(M+1))
    simp only [reg_layout r hr,show (2:Fin 5)≠1 by decide,show (4:Fin 5)≠2 by decide,
      show (3:Fin 5)≠2 by decide,show (1:Fin 5)≠2 by decide,if_false,if_true,hv₄,hzero,hc₁₂,hc₁₁]
    nlinarith
  · change e.store.reg (r 4)=_
    rw [hpost]
    simp [degreeStore,FieldPrograms.halfStore,reg_layout r hr]
  · intro i hi
    change e.store.reg i=_
    rw [hpost]
    simp [degreeStore,FieldPrograms.halfStore,degreeScaled,scaleStore,degreePrepare,TapeStore.setReg,hi]
  · change ∀ i,e.store.reg i ≤ M
    rw [hpost]; exact hfinal
  · change FieldConvolution.tapeData e.store=_
    rw [hpost]; rfl



end ExpandingCodes.Computation.TesterEvaluation

end FlattenModule63

/-! Inlined whole module: ExpandingCodes.Computation.TesterInput -/
section FlattenModule64



set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterInput
open NKtLB SamplerEvaluation
open FieldPrograms UnaryArithmetic
variable {R B : ℕ}




private theorem bit_le_one (inp : Inputs) (p : ℕ) : bit inp p ≤ 1 := by unfold bit; split <;> omega










private theorem readBit_stops (a : Fin R) (inp : Inputs) (s : TapeStore R B) :
    (readBit a).Stops inp (s.toCfg 0) 2 ((readBitStore a inp s).toCfg 3) := by
  let e : TapeStore R B := {s with roHead := Function.update s.roHead 0 (s.roHead 0+1)}
  let j : Fin 4 := if Machine.readRO inp.input (s.roHead 0)=.one then 1 else 2
  have h₁ : (readBit a).step inp (s.toCfg 0)=e.toCfg j := by
    simp [TapeProgram.step,readBit,TapeStore.toCfg,e,j,Inputs.get]
    split_ifs <;> simp_all
  have h₂ : (readBit a).step inp (e.toCfg j)=(readBitStore a inp s).toCfg 3 := by
    by_cases h : Machine.readRO inp.input (s.roHead 0)=.one <;>
      simp [TapeProgram.step,readBit,TapeStore.toCfg,e,j,h,readBitStore,TapeStore.setReg,bit]
  constructor
  · apply TapeProgram.Exec.step (by simp [TapeProgram.halted,readBit]) h₁
    apply TapeProgram.Exec.one
    · dsimp [j]; split_ifs <;> simp [TapeProgram.halted,readBit]
    · exact h₂
  · simp [TapeProgram.halted,readBit]













private theorem blockStore_reg (r : Fin 4 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (s : TapeStore R B) :
    (blockStore r b inp s).reg=(((s.setReg (r 1) 0).setReg (r 2) 0).setReg (r 3) 0).reg := by
  rw [blockStore,TapeArrays.writeBlockStore_reg]
  funext j
  simp only [blockPrepare,readBitStore,TapeStore.setReg]
  by_cases h₁ : j=r 1 <;> by_cases h₂ : j=r 2 <;> by_cases h₃ : j=r 3 <;>
    simp_all [Function.update,hr.eq_iff]




private theorem blockStore_written (r : Fin 4 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (s : TapeStore R B) (hq : 1 ≤ s.reg (r 0)) :
    TapeArrays.EntryWritten (advanced s) (blockStore r b inp s) b (s.bufferHead b) (s.reg (r 0))
      (bit inp (s.roHead 0)) := by
  have hb : bit inp (s.roHead 0) ≤ s.reg (r 0) := (bit_le_one _ _).trans hq
  constructor
  · simp [blockStore,TapeArrays.writeBlockStore_roHead,blockPrepare,readBitStore,advanced,TapeStore.setReg]
  · simp [blockStore,TapeArrays.writeBlockStore_output,blockPrepare,readBitStore,advanced,TapeStore.setReg]
  · simp [blockStore,TapeArrays.writeBlockStore_head _ _ _ _ _ _ hb,blockPrepare,readBitStore,advanced,TapeStore.setReg]
  · intro c k
    rw [blockStore,TapeArrays.writeBlockStore_symbol _ _ _ _ _ _ hb]
    rfl

private theorem block_stops (r : Fin 4 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (M : ℕ) (hM : 1 ≤ M)
    (s : TapeStore R B) (hs : ∀ j,s.reg j ≤ M) (hq : 1 ≤ s.reg (r 0)) :
    ∃ t e, t ≤ 20*(M+1) ∧
      (block r b).Stops inp (s.toCfg (block (B := B) r b).entry) t e ∧
      e.store=blockStore r b inp s ∧ ∀ j,e.reg j ≤ M := by
  have hclear := TapeMacros.clear_stops (r 2) inp (s.reg (r 2)) s rfl
  have hread := readBit_stops (r 2) inp (s.setReg (r 2) 0)
  let d := readBitStore (r 2) inp (s.setReg (r 2) 0)
  have hdb : ∀ j,d.reg j ≤ M := by
    intro j
    simpa [d,readBitStore,TapeStore.setReg] using
      setReg_bound s (r 2) (bit inp (s.roHead 0)) M hs ((bit_le_one _ _).trans hM) j
  obtain ⟨u,c,hu,hcopy,hcs,hcb⟩ := copy_stops_bound (r 0) (r 1) (r 3)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M d hdb
  have hcpre : c.store=blockPrepare r inp s := by
    rw [hcs]
    have hdq : d.reg (r 0)=s.reg (r 0) := by simp [d,readBitStore,reg_layout r hr]
    rw [hdq]; rfl
  have hcv : c.reg (r 2)=bit inp (s.roHead 0) := by
    change c.store.reg (r 2)=_
    rw [hcpre]
    simp [blockPrepare,readBitStore,TapeStore.setReg,Function.update,hr.eq_iff]
  have hcw : c.reg (r 1)=s.reg (r 0) := by
    change c.store.reg (r 1)=_
    rw [hcpre]
    simp [blockPrepare,reg_layout r hr]
  obtain ⟨e,he,hes⟩ := TapeArrays.writeBlock_stops (r 2) (r 1) (hr.ne (by decide)) b inp
    (bit inp (s.roHead 0)) (s.reg (r 0)) c.store hcv hcw ((bit_le_one _ _).trans hq)
  have hall := ((hclear.seq hread).seq hcopy).seq he
  refine ⟨s.reg (r 2)+1+1+2+1+u+1+(2*s.reg (r 0)+bit inp (s.roHead 0)+3),_,?_,hall,?_,?_⟩
  · have hb₂ := hs (r 2); have hb₀ := hs (r 0); have hbit := bit_le_one inp (s.roHead 0); omega
  · rw [hes,hcpre]; rfl
  · intro j
    change e.store.reg j ≤ M
    rw [hes,hcpre]
    change (blockStore r b inp s).reg j ≤ M
    rw [blockStore_reg r hr]
    exact setReg_bound _ _ 0 M (setReg_bound _ _ 0 M (setReg_bound s _ 0 M hs (by omega)) (by omega)) (by omega) j




private theorem loadLayout_injective (r : Fin 5 → Fin R) (hr : Function.Injective r) :
    Function.Injective (loadLayout r) := by
  intro i j hij
  have hh := congrArg (Fin.val : Fin 5 → ℕ) (hr hij)
  exact Fin.ext hh







private theorem load_counter (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (s : TapeStore R B) :
    (blockStore (loadLayout r) b inp s).reg (r 4)=s.reg (r 4) := by
  rw [blockStore_reg _ (loadLayout_injective r hr)]
  simp [loadLayout,reg_layout r hr]














private theorem load_stops (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (M : ℕ) (hM : 1 ≤ M)
    (N start : ℕ) (y : Fin N → Bool) (s : TapeStore R B)
    (hs : ∀ j,s.reg j ≤ M) (hq : 1 ≤ s.reg (r 0)) (hn : s.reg (r 4)=N)
    (hro : s.roHead 0=start) (hh : s.bufferHead b=1) (hm : TapeArrays.BottomMarked s b)
    (hy : ∀ j : Fin N,Machine.readRO inp.input (start+j.val)=if y j then .one else .zero) :
    ∃ t, t ≤ N*(20*(M+1)+2)+1 ∧
      (load r b).Stops inp (s.toCfg (load (B := B) r b).entry) t
        ((loadStore r b inp N s).toCfg (TapeProgram.loopExit 24)) ∧
      (∀ j,(loadStore r b inp N s).reg j ≤ M) ∧
      (loadStore r b inp N s).roHead 0=start+N ∧
      (loadStore r b inp N s).bufferHead b=1+N*s.reg (r 0) ∧
      TapeArrays.BottomMarked (loadStore r b inp N s) b ∧
      TapeArrays.ThermometerTable (loadStore r b inp N s) b (s.reg (r 0)) (fun j => if y j then 1 else 0) := by
  let Inv := Loading r b (s.reg (r 0)) M start N y
  have hi : Inv N s := ⟨by omega,hs,rfl,hq,by simpa using hro,by simpa using hh,hm,by simp⟩
  have hbody : ∀ n d, d.reg (r 4)=n+1 → Inv (n+1) d →
      ∃ t c,t ≤ 20*(M+1) ∧ (block (loadLayout r) b).Stops inp
        ((d.setReg (r 4) n).toCfg (block (B := B) (loadLayout r) b).entry) t c ∧
        c.store=blockStore (loadLayout r) b inp (d.setReg (r 4) n) ∧ Inv n c.store := by
    intro n d hdn hdi
    let p := d.setReg (r 4) n
    have hpb : ∀ j,p.reg j ≤ M := setReg_bound d _ n M hdi.bounded (by have := hdi.bounded (r 4); omega)
    have hpq : p.reg ((loadLayout r) 0)=s.reg (r 0) := by
      simpa [p,loadLayout,reg_layout r hr] using hdi.width
    obtain ⟨t,c,ht,hc,hcs,hcb⟩ := block_stops (loadLayout r) (loadLayout_injective r hr)
      b inp M hM p hpb (by rw [hpq]; exact hq)
    let j : Fin N := ⟨N-(n+1),by have := hdi.remaining; omega⟩
    have hj : j.val=N-(n+1) := rfl
    have hnN : n+1 ≤ N := hdi.remaining
    have hbit : bit inp (p.roHead 0)=(if y j then 1 else 0) := by
      have hsym : Machine.readRO inp.input (p.roHead 0)=if y j then .one else .zero := by
        rw [show p.roHead 0=start+j.val by simpa [p,hj,TapeStore.setReg] using hdi.inputHead]
        exact hy j
      simp only [bit,hsym]
      cases y j <;> rfl
    have hw := blockStore_written (loadLayout r) (loadLayout_injective r hr) b inp p (by rw [hpq]; exact hq)
    have hphead : p.bufferHead b=1+j.val*s.reg (r 0) := by simpa [p,hj,TapeStore.setReg] using hdi.head
    refine ⟨t,c,ht,hc,hcs,?_⟩
    rw [hcs]
    constructor
    · omega
    · change ∀ j,c.store.reg j ≤ M at hcb
      rw [hcs] at hcb
      exact hcb
    · rw [blockStore_reg _ (loadLayout_injective r hr)]
      simpa [loadLayout,reg_layout r hr] using hpq
    · exact hq
    · rw [hw.roHead]
      change p.roHead 0+1=start+(N-n)
      simp only [p,TapeStore.setReg,hdi.inputHead]
      omega
    · rw [hw.head]
      simp only [Function.update_self,hphead,hpq]
      have hcount : N-n=j.val+1 := by omega
      rw [hcount,Nat.add_mul,Nat.one_mul]
      omega
    · exact hw.bottomMarked (by simp [hphead]) hdi.marked
    · intro k hk
      by_cases hkj : k=j
      · subst k
        have hstart : TapeArrays.entryOffset j.val (s.reg (r 0))=p.bufferHead b := by
          simp [TapeArrays.entryOffset,hphead]
        rw [hstart,← hbit,← hpq]
        exact ⟨(bit_le_one _ _).trans (by rw [hpq]; exact hq),by
          intro u hu
          rw [hw.symbol]
          have h₁ : p.bufferHead b ≤ p.bufferHead b+u := by omega
          have h₂ : p.bufferHead b+u<p.bufferHead b+p.reg ((loadLayout r) 0) := by omega
          simp [h₁,h₂,Nat.add_lt_add_iff_left]⟩
      · have hkjlt : k.val<j.val := by
          have hne : k.val≠j.val := fun heq => hkj (Fin.ext heq)
          omega
        have hprior := hdi.table k (by omega)
        refine ⟨hprior.1,?_⟩
        intro u hu
        rw [hw.symbol]
        have hout : ¬(b=b ∧ p.bufferHead b ≤ TapeArrays.entryOffset k.val (s.reg (r 0))+u ∧
            TapeArrays.entryOffset k.val (s.reg (r 0))+u<p.bufferHead b+p.reg ((loadLayout r) 0)) := by
          rw [hphead,TapeArrays.entryOffset]
          have hmul : (k.val+1)*s.reg (r 0) ≤ j.val*s.reg (r 0) := Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul,Nat.one_mul] at hmul
          omega
        rw [if_neg hout]
        exact hprior.2 u hu
  obtain ⟨t,ht,hstop,hfinal⟩ := SourceFieldArithmetic.loop_stops
    (block (loadLayout r) b) (r 4) (blockStore (loadLayout r) b inp) inp (20*(M+1)) Inv
    (load_counter r hr b inp) hbody N s hn hi
  refine ⟨t,ht,hstop,hfinal.bounded,?_,?_,hfinal.marked,?_⟩
  · simpa [loadStore] using hfinal.inputHead
  · simpa [loadStore] using hfinal.head
  · intro j
    exact hfinal.table j (by simpa using j.isLt)




private theorem loadStore_register_frame (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (n : ℕ) (s : TapeStore R B)
    (j : Fin R) (hj : j≠r 1 ∧ j≠r 2 ∧ j≠r 3 ∧ j≠r 4) :
    (loadStore r b inp n s).reg j=s.reg j := by
  apply SourceFieldArithmetic.loopResult_frame _ _ j hj.2.2.2
  intro d
  rw [blockStore_reg _ (loadLayout_injective r hr)]
  simp [loadLayout,TapeStore.setReg,hj]






private theorem loadStore_output (r : Fin 5 → Fin R) (b : Fin B) (inp : Inputs)
    (n : ℕ) (s : TapeStore R B) : (loadStore r b inp n s).output=s.output := by
  unfold loadStore
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [SourceFieldArithmetic.loopResult,ih]
    simp [blockStore,TapeArrays.writeBlockStore_output,blockPrepare,readBitStore,TapeStore.setReg]











private theorem loadStore_bufferHead_frame (r : Fin 5 → Fin R) (b c : Fin B) (hcb : c≠b) (inp : Inputs)
    (n : ℕ) (s : TapeStore R B) : (loadStore r b inp n s).bufferHead c=s.bufferHead c := by
  unfold loadStore
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [SourceFieldArithmetic.loopResult,ih]
    simp [blockStore,TapeArrays.writeBlockStore,TapeArrays.fillStore_head,blockPrepare,readBitStore,TapeStore.setReg,hcb]

private theorem loadStore_bufferSymbol_frame (r : Fin 5 → Fin R) (b c : Fin B) (hcb : c≠b) (inp : Inputs)
    (n : ℕ) (s : TapeStore R B) (k : ℕ) :
    ((loadStore r b inp n s).bufferTape c).getD k .blank=(s.bufferTape c).getD k .blank := by
  unfold loadStore
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [SourceFieldArithmetic.loopResult,ih]
    simp only [blockStore,TapeArrays.writeBlockStore,TapeArrays.fillStore_symbol,hcb,false_and,if_false,blockPrepare,readBitStore,TapeStore.setReg]

/-- Exact current-cell symbols after an arbitrary prefix, including sizeInput. -/
private theorem input_symbols (inp : Inputs) (pre : List Bool) {N : ℕ} (y : Fin N → Bool)
    (hi : inp.input=pre++List.ofFn y) (j : Fin N) :
    Machine.readRO inp.input (pre.length+j.val)=if y j then .one else .zero := by
  unfold Machine.readRO
  rw [hi,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,List.getElem?_ofFn]
  simp only [j.isLt,dite_true]
  cases y j <;> rfl

private theorem word_symbols (inp : Inputs) (n N : ℕ) (y : ExpandingCodes.PolynomialStretch.Word N)
    (hi : inp.input=ExpandingCodes.PolynomialStretch.sizeInput n++ExpandingCodes.PolynomialStretch.wordBits y)
    (j : Fin N) : Machine.readRO inp.input (n+1+j.val)=if y j≠0 then .one else .zero := by
  have hh := input_symbols inp (ExpandingCodes.PolynomialStretch.sizeInput n)
    (fun j => decide (y j≠0)) hi j
  simpa [ExpandingCodes.PolynomialStretch.sizeInput] using hh



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











private theorem powerStepStore_value (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) :
    (powerStepStore r d).reg (r 1) = d.reg (r 0)*d.reg (r 1) := by
  simp [powerStepStore, multiplyStore, reg_layout r hr]

private theorem powerStepStore_base (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (powerStepStore r d).reg (r 0) = d.reg (r 0) := by
  simp [powerStepStore, multiplyStore, reg_layout r hr]

private theorem powerStepStore_count (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (powerStepStore r d).reg (r 5) = d.reg (r 5) := by
  simp [powerStepStore, multiplyStore, reg_layout r hr]

private theorem powerStepStore_bound (r : Fin 6 → Fin R) (hr : Function.Injective r)
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

private theorem powerStep_stops (r : Fin 6 → Fin R) (hr : Function.Injective r)
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










private theorem powerLoopStore_base (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) :
    (powerLoopStore r n d).reg (r 0) = d.reg (r 0) := by
  induction n generalizing d with
  | zero => simp [powerLoopStore, reg_layout r hr]
  | succ n ih =>
    rw [powerLoopStore, ih, powerStepStore_base r hr]
    simp [reg_layout r hr]

private theorem powerLoopStore_value (r : Fin 6 → Fin R) (hr : Function.Injective r)
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
private theorem powerLoop_stops (r : Fin 6 → Fin R) (hr : Function.Injective r)
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















private theorem fixedPowerStore_value (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (e : ℕ) (d : TapeStore R B) :
    (fixedPowerStore r e d).reg (r 1) = d.reg (r 0)^e := by
  simp [fixedPowerStore, powerLoopStore_value r hr, powerPrepare, reg_layout r hr]

private theorem fixedPowerStore_base (r : Fin 6 → Fin R) (hr : Function.Injective r)
    (e : ℕ) (d : TapeStore R B) :
    (fixedPowerStore r e d).reg (r 0) = d.reg (r 0) := by
  simp [fixedPowerStore, powerLoopStore_base r hr, powerPrepare, reg_layout r hr]

private theorem fixedPower_stops (r : Fin 6 → Fin R) (hr : Function.Injective r)
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
private theorem ceilIter_invariant (p t q ell : ℕ)
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

private theorem power_clog_unique (p ell : ℕ) (hp : p ≤ 2^ell) (hb : 2^ell<2*p) :
    ell=Nat.clog 2 p := by
  have hle : Nat.clog 2 p ≤ ell := (Nat.clog_le_iff_le_pow (by decide)).mpr hp
  apply Nat.le_antisymm _ hle
  by_contra hn
  have ht : Nat.clog 2 p+1 ≤ ell := by omega
  have hpw := Nat.pow_le_pow_right (show 0<2 by decide) ht
  have hpc := Nat.le_pow_clog (by decide : 1<2) p
  rw [pow_succ] at hpw
  omega

private theorem ceilIter_exact (p : ℕ) (hp : 1 ≤ p) :
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












private theorem doubleBody_stops (q ell copy tmp : Fin R)
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




private theorem ceilCompareLayout_injective (r : Fin 8 → Fin R) (hr : Function.Injective r) :
    Function.Injective (ceilCompareLayout r) := by
  intro i j hij
  have hv := congrArg Fin.val (hr hij)
  exact Fin.ext hv










private theorem ceilConditional_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
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









private theorem ceilingStep_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
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







private theorem tapeStore_ext (d e : TapeStore R B)
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

private theorem ceilingStepStore_flat (r : Fin 8 → Fin R) (hr : Function.Injective r)
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

private theorem ceilingStepStore_q (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (ceilingStepStore r d).reg (r 0) =
      if d.reg (r 0)<d.reg (r 1) then 2*d.reg (r 0) else d.reg (r 0) := by
  rw [ceilingStepStore_flat r hr]
  by_cases hlt : d.reg (r 0)<d.reg (r 1)
  all_goals simp [ceilingStepFlatStore, reg_layout r hr, hlt]

private theorem ceilingStepStore_ell (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (ceilingStepStore r d).reg (r 6) =
      if d.reg (r 0)<d.reg (r 1) then d.reg (r 6)+1 else d.reg (r 6) := by
  rw [ceilingStepStore_flat r hr]
  by_cases hlt : d.reg (r 0)<d.reg (r 1)
  all_goals simp [ceilingStepFlatStore, reg_layout r hr, hlt]

private theorem ceilingStepStore_p (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (ceilingStepStore r d).reg (r 1)=d.reg (r 1) := by
  rw [ceilingStepStore_flat r hr]
  by_cases hlt : d.reg (r 0)<d.reg (r 1)
  all_goals simp [ceilingStepFlatStore, reg_layout r hr, hlt]

private theorem ceilingStepStore_count (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (ceilingStepStore r d).reg (r 7)=d.reg (r 7) := by
  rw [ceilingStepStore_flat r hr]
  by_cases hlt : d.reg (r 0)<d.reg (r 1)
  all_goals simp [ceilingStepFlatStore, reg_layout r hr, hlt]

private theorem ceilingStepStore_bound (r : Fin 8 → Fin R) (hr : Function.Injective r)
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










private theorem ceilingLoopStore_pair (r : Fin 8 → Fin R) (hr : Function.Injective r)
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

private theorem ceilingLoop_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
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














private theorem ceilingPowerStore_exact (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (hp : 1≤d.reg (r 1)) :
    ((ceilingPowerStore r d).reg (r 0),(ceilingPowerStore r d).reg (r 6)) =
      (2^Nat.clog 2 (d.reg (r 1)),Nat.clog 2 (d.reg (r 1))) := by
  unfold ceilingPowerStore
  rw [ceilingLoopStore_pair r hr]
  simpa [ceilingPrepare, reg_layout r hr] using SizeParameters.ceilIter_exact (d.reg (r 1)) hp

private theorem ceilingPowerTwo_stops (r : Fin 8 → Fin R) (hr : Function.Injective r)
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













private theorem divideLoop_stops (src quotient : Fin R) (hsq : src≠quotient)
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













private theorem divideConstantStore_value (r : Fin 4 → Fin R) (hr : Function.Injective r)
    (k : ℕ) (d : TapeStore R B) :
    (divideConstantStore r k d).reg (r 1)=d.reg (r 0)/k := by
  simp [divideConstantStore,divideLoopStore,dividePrepare,reg_layout r hr]






private theorem divideConstant_stops (r : Fin 4 → Fin R) (hr : Function.Injective r)
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






private theorem decrement_stops (r : Fin R) (inp : Inputs) (d : TapeStore R B) :
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



private theorem floorCeilIndex_injective : Function.Injective floorCeilIndex := by decide



private theorem floorCeilLayout_injective (r : Fin 9 → Fin R) (hr : Function.Injective r) :
    Function.Injective (floorCeilLayout r) := hr.comp floorCeilIndex_injective


















private theorem clog_succ_eq_log_succ (u : ℕ) (hu : 1≤u) :
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

private theorem floorPowerStore_exact (r : Fin 9 → Fin R) (hr : Function.Injective r)
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

private theorem floorPowerTwo_stops (r : Fin 9 → Fin R) (hr : Function.Injective r)
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







private theorem SamePayload.trans {d e f : TapeStore R B} (h : SamePayload d e) (k : SamePayload e f) :
    SamePayload d f := ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,k.2.2.2.trans h.2.2.2⟩
private theorem SamePayload.setReg (d : TapeStore R B) (r : Fin R) (n : ℕ) :
    SamePayload d (d.setReg r n) := ⟨rfl,rfl,rfl,rfl⟩

private theorem powerStepStore_fresh (r : Fin 6 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₁ : j≠r 1) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4) :
    (powerStepStore r d).reg j=d.reg j := by
  simp [powerStepStore,multiplyStore,TapeStore.setReg,h₁,h₂,h₃,h₄]

private theorem powerLoopStore_fresh (r : Fin 6 → Fin R) (t : ℕ) (d : TapeStore R B) (j : Fin R)
    (h₁ : j≠r 1) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4) (h₅ : j≠r 5) :
    (powerLoopStore r t d).reg j=d.reg j := by
  induction t generalizing d with
  | zero => simp [powerLoopStore,TapeStore.setReg,h₅]
  | succ t ih =>
    rw [powerLoopStore,ih,powerStepStore_fresh r _ j h₁ h₂ h₃ h₄]
    simp [TapeStore.setReg,h₅]

private theorem fixedPowerStore_fresh (r : Fin 6 → Fin R) (t : ℕ) (d : TapeStore R B) (j : Fin R)
    (h₁ : j≠r 1) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4) (h₅ : j≠r 5) :
    (fixedPowerStore r t d).reg j=d.reg j := by
  rw [fixedPowerStore,powerLoopStore_fresh r t _ j h₁ h₂ h₃ h₄ h₅]
  simp [powerPrepare,TapeStore.setReg,h₁,h₅]

private theorem powerStepStore_payload (r : Fin 6 → Fin R) (d : TapeStore R B) :
    SamePayload d (powerStepStore r d) := ⟨rfl,rfl,rfl,rfl⟩

private theorem powerLoopStore_payload (r : Fin 6 → Fin R) (t : ℕ) (d : TapeStore R B) :
    SamePayload d (powerLoopStore r t d) := by
  induction t generalizing d with
  | zero => exact SamePayload.setReg d _ 0
  | succ t ih => exact ((SamePayload.setReg d _ t).trans (powerStepStore_payload r _)).trans (ih _)

private theorem fixedPowerStore_payload (r : Fin 6 → Fin R) (t : ℕ) (d : TapeStore R B) :
    SamePayload d (fixedPowerStore r t d) := by
  exact ((SamePayload.setReg d _ 1).trans (SamePayload.setReg _ _ t)).trans (powerLoopStore_payload r t _)

private theorem ceilingStepStore_fresh (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (j : Fin R)
    (h₀ : j≠r 0) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4)
    (h₅ : j≠r 5) (h₆ : j≠r 6) : (ceilingStepStore r d).reg j=d.reg j := by
  rw [ceilingStepStore_flat r hr]
  unfold ceilingStepFlatStore
  split <;> simp [TapeStore.setReg,h₀,h₂,h₃,h₄,h₅,h₆]

private theorem ceilingLoopStore_fresh (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (t : ℕ) (d : TapeStore R B) (j : Fin R)
    (h₀ : j≠r 0) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4)
    (h₅ : j≠r 5) (h₆ : j≠r 6) (h₇ : j≠r 7) :
    (ceilingLoopStore r t d).reg j=d.reg j := by
  induction t generalizing d with
  | zero => simp [ceilingLoopStore,TapeStore.setReg,h₇]
  | succ t ih =>
    rw [ceilingLoopStore,ih,ceilingStepStore_fresh r hr _ j h₀ h₂ h₃ h₄ h₅ h₆]
    simp [TapeStore.setReg,h₇]

private theorem ceilingPowerStore_fresh (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (j : Fin R)
    (h₀ : j≠r 0) (h₂ : j≠r 2) (h₃ : j≠r 3) (h₄ : j≠r 4)
    (h₅ : j≠r 5) (h₆ : j≠r 6) (h₇ : j≠r 7) :
    (ceilingPowerStore r d).reg j=d.reg j := by
  rw [ceilingPowerStore,ceilingLoopStore_fresh r hr _ _ j h₀ h₂ h₃ h₄ h₅ h₆ h₇]
  simp [ceilingPrepare,TapeStore.setReg,h₀,h₅,h₆,h₇]

private theorem ceilingStepStore_payload (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : SamePayload d (ceilingStepStore r d) := by
  rw [ceilingStepStore_flat r hr]
  unfold ceilingStepFlatStore
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩

private theorem ceilingLoopStore_payload (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (t : ℕ) (d : TapeStore R B) : SamePayload d (ceilingLoopStore r t d) := by
  induction t generalizing d with
  | zero => exact SamePayload.setReg d _ 0
  | succ t ih => exact ((SamePayload.setReg d _ t).trans (ceilingStepStore_payload r hr _)).trans (ih _)

private theorem ceilingPowerStore_payload (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : SamePayload d (ceilingPowerStore r d) := by
  have hp : SamePayload d (ceilingPrepare r d) := ⟨rfl,rfl,rfl,rfl⟩
  exact hp.trans (ceilingLoopStore_payload r hr _ _)

private theorem divideConstantStore_fresh (r : Fin 4 → Fin R) (k : ℕ)
    (d : TapeStore R B) (j : Fin R) (h₁ : j≠r 1) (h₂ : j≠r 2) (h₃ : j≠r 3) :
    (divideConstantStore r k d).reg j=d.reg j := by
  simp [divideConstantStore,divideLoopStore,dividePrepare,TapeStore.setReg,h₁,h₂,h₃]

private theorem divideConstantStore_payload (r : Fin 4 → Fin R) (k : ℕ)
    (d : TapeStore R B) : SamePayload d (divideConstantStore r k d) := ⟨rfl,rfl,rfl,rfl⟩

private theorem floorPowerStore_fresh (r : Fin 9 → Fin R) (hr : Function.Injective r)
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

private theorem floorPowerStore_payload (r : Fin 9 → Fin R) (hr : Function.Injective r)
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












 private theorem scan_stops (r : Fin R) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
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








 private theorem sizeInput_stops (r : Fin R) (inp : Inputs) (n : ℕ) (d : TapeStore R B)
    (hones : ∀ j, j < n → Machine.readRO inp.input (d.roHead 0+j) = .one)
    (hend : Machine.readRO inp.input (d.roHead 0+n) ≠ .one) :
    (sizeInput r).Stops inp (d.toCfg (sizeInput (B := B) r).entry) (d.reg r+2*n+3)
      ((sizeStore r n d).toCfg (2 : Fin 3) |>.mapPC (TapeProgram.rightLabel 2)) := by
  have hc := TapeMacros.clear_stops r inp (d.reg r) d rfl
  have hs := scan_stops r inp n (d.setReg r 0) hones hend
  have hall := hc.seq hs
  convert hall using 1 <;> first | rfl | simp [scanStore, sizeStore, TapeStore.setReg, Function.update_idem] | omega

private theorem sizeInput_unary (r : Fin R) (inp : Inputs) (n : ℕ) (tail : List Bool)
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
















private theorem setupPowerP_inj (r : Fin 14 → Fin R) (hr : Function.Injective r) :
    Function.Injective (setupPowerPLayout r) := hr.comp (by decide)
private theorem setupCeiling_inj (r : Fin 14 → Fin R) (hr : Function.Injective r) :
    Function.Injective (setupCeilingLayout r) := hr.comp (by decide)
private theorem setupPowerM_inj (r : Fin 14 → Fin R) (hr : Function.Injective r) :
    Function.Injective (setupPowerMLayout r) := hr.comp (by decide)
private theorem setupDivision_inj (r : Fin 14 → Fin R) (hr : Function.Injective r) :
    Function.Injective (setupDivisionLayout r) := hr.comp (by decide)
private theorem setupFloor_inj (r : Fin 14 → Fin R) (hr : Function.Injective r) :
    Function.Injective (setupFloorLayout r) := hr.comp (by decide)






















private theorem setupStage₁_n (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) : (setupStage₁ r d σ).reg (r 0)=σ.reg (r 0) :=
  fixedPowerStore_base _ (setupPowerP_inj r hr) _ _
private theorem setupStage₁_p (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) : (setupStage₁ r d σ).reg (r 1)=σ.reg (r 0)^(2*d) :=
  fixedPowerStore_value _ (setupPowerP_inj r hr) _ _

private theorem setupStage₂_frame (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) (j : Fin 14) (hj : j.val<2) :
    (setupStage₂ r d σ).reg (r j)=(setupStage₁ r d σ).reg (r j) := by
  apply ceilingPowerStore_fresh _ (setupCeiling_inj r hr)
  all_goals simp [setupCeilingLayout,setupCeilingIndex,hr.eq_iff]; omega

private theorem setupStage₃_frame (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) (j : Fin 14) (hj : j.val<4) :
    (setupStage₃ r d σ).reg (r j)=(setupStage₂ r d σ).reg (r j) := by
  apply fixedPowerStore_fresh
  all_goals simp [setupPowerMLayout,setupPowerMIndex,hr.eq_iff]; omega

private theorem setupStage₄_frame (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (σ : TapeStore R B) (j : Fin 14) (hj : j.val<5) :
    (setupStage₄ r d k σ).reg (r j)=(setupStage₃ r d σ).reg (r j) := by
  apply divideConstantStore_fresh
  all_goals simp [setupDivisionLayout,setupDivisionIndex,hr.eq_iff]; omega

private theorem setupStore_frame (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (σ : TapeStore R B) (j : Fin 14) (hj : j.val<6) :
    (setupStore r d k σ).reg (r j)=(setupStage₄ r d k σ).reg (r j) := by
  apply floorPowerStore_fresh _ (setupFloor_inj r hr)
  all_goals simp [setupFloorLayout,setupFloorIndex,hr.eq_iff]; omega

private theorem setupStage₂_qell (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) (hp : 1≤σ.reg (r 0)^(2*d)) :
    ((setupStage₂ r d σ).reg (r 3),(setupStage₂ r d σ).reg (r 2)) =
      (2^Nat.clog 2 (σ.reg (r 0)^(2*d)),Nat.clog 2 (σ.reg (r 0)^(2*d))) := by
  have h := ceilingPowerStore_exact (setupCeilingLayout r) (setupCeiling_inj r hr)
    (setupStage₁ r d σ) (by simpa only [show setupCeilingLayout r 1=r 1 from rfl,setupStage₁_p r hr] using hp)
  simpa only [setupStage₂,show setupCeilingLayout r 0=r 3 from rfl,
    show setupCeilingLayout r 6=r 2 from rfl,show setupCeilingLayout r 1=r 1 from rfl,setupStage₁_p r hr] using h

private theorem setupStage₃_m (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d : ℕ) (σ : TapeStore R B) :
    (setupStage₃ r d σ).reg (r 4)=(setupStage₂ r d σ).reg (r 3)^d :=
  fixedPowerStore_value _ (setupPowerM_inj r hr) _ _

private theorem setupStage₄_u (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (σ : TapeStore R B) :
    (setupStage₄ r d k σ).reg (r 5)=σ.reg (r 0)/k := by
  have h := divideConstantStore_value (setupDivisionLayout r) (setupDivision_inj r hr) k (setupStage₃ r d σ)
  change (setupStage₄ r d k σ).reg (r 5)=(setupStage₃ r d σ).reg (r 0)/k at h
  rw [setupStage₃_frame r hr d σ 0 (by decide),setupStage₂_frame r hr d σ 0 (by decide),setupStage₁_n r hr] at h
  exact h

/-- The eight setup counters, exactly identified with the frozen mission sizes.
No modulus-search or field-construction computation is asserted here. -/
private theorem setupStore_values (r : Fin 14 → Fin R) (hr : Function.Injective r)
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

private theorem setupStore_payload (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (σ : TapeStore R B) : SamePayload σ (setupStore r d k σ) := by
  exact ((((fixedPowerStore_payload _ _ _).trans
    (ceilingPowerStore_payload _ (setupCeiling_inj r hr) _)).trans
    (fixedPowerStore_payload _ _ _)).trans (divideConstantStore_payload _ _ _)).trans
    (floorPowerStore_payload _ (setupFloor_inj r hr) _)













private theorem powerCounterBound_pos (e M : ℕ) : 1≤powerCounterBound e M := by
  have h := Nat.one_le_pow (e+1) (M+1) (by omega)
  unfold powerCounterBound
  nlinarith

private theorem setup_stops (r : Fin 14 → Fin R) (hr : Function.Injective r)
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























































































































@[simp] private theorem low_eq_iff (d : ℕ) (i j : Fin 80) : low d i=low d j ↔ i=j := by
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


























































































































































































































































































































































































@[simp] private theorem pointPrefix_zero (d ell : ℕ) (h : 0<ell) (D : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) :
    pointPrefix d ell h D y a b 0=BinaryField.zeroIndex ell := rfl


















@[simp] private theorem pointPrefix_full (d ell : ℕ) (h : 0<ell) (D : ℕ)
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

/-! Inlined whole module: ExpandingCodes.Computation.TesterPrefix -/
section FlattenModule83



set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterPrefix
open NKtLB TesterGram FieldPrograms
open ExpandingCodes.PolynomialStretch




private theorem parameter_injective (d : ℕ) : Function.Injective (parameterLayout d) := by
  intro i j h; apply Fin.ext
  exact congrArg (fun x : Registers d => x.val) h
private theorem field_injective (d : ℕ) : Function.Injective (fieldSetupLayout d) := by
  intro i j h; apply Fin.ext
  exact congrArg (fun x : Registers d => x.val) h


























private theorem setup_initial_stops (d n M : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (inp : Inputs) (tail : List Bool) (hi : inp.input=sizeInput n++tail)
    (hcover : TesterEnvelopeCovers d n M) :
    ∃ t e,t ≤ setupTime d n M ∧
      (TesterGram.setup d).Stops inp ((initialStore d).toCfg (TesterGram.setup d).entry) t e ∧
      e.store=setupResult d n ∧ SetupReady d n M e.store := by
  have hread := SizeReader.sizeInput_unary (low d 0) inp n tail (initialStore d) rfl (by
    simpa only [sizeInput,List.append_assoc,List.singleton_append] using hi)
  have hb : ∀ j,(SizeReader.sizeStore (low d 0) n (initialStore d)).reg j ≤ n+1 := by
    intro j
    by_cases h:j=low d 0
    · subst j; simp [SizeReader.sizeStore,initialStore,TapeStore.setReg]
    · simp [SizeReader.sizeStore,initialStore,TapeStore.setReg,h]
  obtain ⟨t₀,c₀,ht₀,h₀,hs₀,hb₀⟩ := ParameterPrograms.setup_stops (parameterLayout d)
    (parameter_injective d) d 1 (by decide) inp (n+1) (by omega)
    (SizeReader.sizeStore (low d 0) n (initialStore d)) hb
    (by simp [parameterLayout,SizeReader.sizeStore]; omega)
    (by simp [parameterLayout,SizeReader.sizeStore]; omega)
  have hs₀' : c₀.store=sizeResult d n := hs₀
  have hvalues := ParameterPrograms.setupStore_values (parameterLayout d) (parameter_injective d)
    d 1 hd (by decide) (SizeReader.sizeStore (low d 0) n (initialStore d))
    (by simpa [parameterLayout,SizeReader.sizeStore] using hn)
    (by simp [parameterLayout,SizeReader.sizeStore]; omega)
  have hv4 : c₀.reg (low d 4)=rowCount d n := by
    change c₀.store.reg (low d 4)=_
    rw [hs₀]
    simpa [parameterLayout,SizeReader.sizeStore] using hvalues.2.2.2.2.1
  have hv2 : c₀.reg (low d 2)=fieldExponent d n := by
    change c₀.store.reg (low d 2)=_
    rw [hs₀]
    simpa [parameterLayout,SizeReader.sizeStore] using hvalues.2.2.1
  have hv3 : c₀.reg (low d 3)=fieldSize d n := by
    change c₀.store.reg (low d 3)=_
    rw [hs₀]
    simpa [parameterLayout,SizeReader.sizeStore] using hvalues.2.2.2.1
  have hb₀' : ∀ j,c₀.reg j ≤ M := fun j => (hb₀ j).trans hcover.setup
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := SamplerEvaluation.copy_stops_bound
    (low d 4) (low d 70) (low d 79) (by simp [low]) (by simp [low]) (by simp [low]) inp M c₀.store hb₀'
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂,hb₂⟩ := SamplerEvaluation.copy_stops_bound
    (low d 2) (low d 20) (low d 79) (by simp [low]) (by simp [low]) (by simp [low]) inp M c₁.store hb₁
  obtain ⟨t₃,c₃,ht₃,h₃,hs₃,hb₃⟩ := SamplerEvaluation.copy_stops_bound
    (low d 3) (low d 23) (low d 79) (by simp [low]) (by simp [low]) (by simp [low]) inp M c₂.store hb₂
  have hp : c₃.store=copyParameters d (sizeResult d n) := by
    rw [hs₃,hs₂,hs₁,hs₀']
    simp [copyParameters,TapeStore.setReg,low]
  have hell : c₃.reg (fieldSetupLayout d 20)=fieldExponent d n := by
    change c₃.store.reg (fieldSetupLayout d 20)=_
    rw [hs₃,hs₂,hs₁]
    simpa [fieldSetupLayout,TapeStore.setReg,low] using hv2
  have hq : c₃.reg (fieldSetupLayout d 23)=2^fieldExponent d n := by
    change c₃.store.reg (fieldSetupLayout d 23)=_
    rw [hs₃,hs₂,hs₁]
    simpa [fieldSetupLayout,TapeStore.setReg,low,fieldSize] using hv3
  have hm : c₃.reg (low d 70)=rowCount d n := by
    change c₃.store.reg (low d 70)=_
    rw [hs₃,hs₂,hs₁]
    simpa [TapeStore.setReg,low] using hv4
  obtain ⟨t₄,c₄,ht₄,h₄,hs₄,henv,hframe,hb₄,hdata⟩ := SourceFieldSetup.setup_stops
    (fieldSetupLayout d) (field_injective d) inp (fieldExponent d n) (fieldExponent_pos d n) M
    c₃.store hb₃ hell hq hcover.coefficients hcover.twiceField (by
      simpa only [fieldSize,pow_two,← pow_add,two_mul] using hcover.square)
  have houtside : ∀ i : Fin 32, low d 70 ≠ fieldSetupLayout d i := by
    intro i h
    have hh := congrArg (fun x : Registers d => x.val) h
    change 70=i.val at hh
    have := i.isLt
    omega
  have hro : FieldConvolution.tapeData c₃.store =
      FieldConvolution.tapeData (SizeReader.sizeStore (low d 0) n (initialStore d)) := by
    rw [hs₃,hs₂,hs₁]
    simp only [FieldConvolution.tapeData_setReg]
    rw [hs₀]
    have h := ParameterPrograms.setupStore_payload (parameterLayout d) (parameter_injective d) d 1
      (SizeReader.sizeStore (low d 0) n (initialStore d))
    exact congrArg₂ Prod.mk h.1 (congrArg₂ Prod.mk h.2.1
      (congrArg₂ Prod.mk h.2.2.1 h.2.2.2))
  have hfinalData := hdata.trans hro
  have hall := ((((hread.seq h₀).seq h₁).seq h₂).seq h₃).seq h₄
  refine ⟨_,c₄.mapPC (TapeProgram.rightLabel _),?_,hall,?_,?_⟩
  · change 0+2*n+3+1+t₀+1+t₁+1+t₂+1+t₃+1+t₄ ≤ setupTime d n M
    unfold setupTime
    omega
  · change c₄.store=setupResult d n
    rw [hs₄,hp]
    rfl
  · change SetupReady d n M c₄.store
    refine ⟨hb₄,?_,(hframe _ houtside).trans hm,?_,?_,?_,?_⟩
    · exact ⟨henv.2.2.2.1,henv.2.2.1,henv.2.1,henv.2.2.2.2.1⟩
    · have hh := congrArg (fun v => v.1 0) hfinalData
      simpa [FieldConvolution.tapeData,SizeReader.sizeStore,initialStore,TapeStore.setReg] using hh
    · exact congrArg (fun v => v.2.1) hfinalData
    · exact congrArg (fun v => v.2.2.1) hfinalData
    · exact congrArg (fun v => v.2.2.2) hfinalData









private theorem markers_stops (d : ℕ) (inp : Inputs) (s : TapeStore (80+6*d) 3) :
    (markers d).Stops inp (s.toCfg (markers d).entry) 5
      ((markedStore d s).toCfg (TapeProgram.rightLabel 4 (1 : Fin 2))) := by
  have h₀ := TapeMacros.cell_stops (0 : Fin 3) (fun _ => (Sym.bot,Move.right)) inp s
  have h₁ := TapeMacros.cell_stops (1 : Fin 3) (fun _ => (Sym.bot,Move.right)) inp
    (TapeArrays.painted s 0 .bot)
  have h₂ := TapeMacros.cell_stops (2 : Fin 3) (fun _ => (Sym.bot,Move.right)) inp
    (TapeArrays.painted (TapeArrays.painted s 0 .bot) 1 .bot)
  exact (h₀.seq h₁).seq h₂

private theorem markedStore_tapes (d : ℕ) (s : TapeStore (80+6*d) 3)
    (ht : s.bufferTape=fun _ => []) (hh : s.bufferHead=fun _ => 0) :
    (markedStore d s).bufferTape=(fun _ => [.bot]) ∧
    (markedStore d s).bufferHead=(fun _ => 1) := by
  constructor <;> funext b <;> fin_cases b <;>
    simp [markedStore,TapeArrays.painted,TapeMacros.cellStore,ht,hh,Machine.writeAt,Machine.moveHead]

private theorem markedStore_bottom (d : ℕ) (s : TapeStore (80+6*d) 3)
    (ht : s.bufferTape=fun _ => []) (hh : s.bufferHead=fun _ => 0) (b : Fin 3) :
    TapeArrays.BottomMarked (markedStore d s) b := by
  rw [TapeArrays.BottomMarked,(markedStore_tapes d s ht hh).1]
  constructor
  · rfl
  · intro k hk
    cases k with
    | zero => omega
    | succ k => simp

















private theorem input_stops (d n M : ℕ) (inp : Inputs) (y : Word (rowCount d n))
    (hi : inp.input=sizeInput n++wordBits y) (s : TapeStore (80+6*d) 3)
    (hs : SetupReady d n M s) (hcover : TesterEnvelopeCovers d n M) :
    ∃ t e,t ≤ inputTime d n M ∧ (TesterGram.input d).Stops inp
      (s.toCfg (TesterGram.input d).entry) t e ∧ InputReady d n M y e.store := by
  have hmarks := markers_stops d inp s
  let marked := markedStore d s
  have htapes := markedStore_tapes d s hs.buffers hs.heads
  have hb : ∀ j,marked.reg j ≤ M := hs.bounded
  obtain ⟨t,c,ht,hc,hcs,hcb⟩ := SamplerEvaluation.copy_stops_bound
    (low d 70) (low d 76) (low d 2) (by simp [low]) (by simp [low]) (by simp [low]) inp M marked hb
  have hr (j : Fin 80) (hj : j≠76) (hj2 : j≠2) : c.reg (low d j)=s.reg (low d j) := by
    change c.store.reg (low d j)=_
    rw [hcs]
    simp [Fin.ext_iff] at hj hj2
    simp [TapeStore.setReg,low,Function.update,Fin.ext_iff,hj,hj2,marked,markedStore,TapeArrays.painted,TapeMacros.cellStore]
  have hcount : c.reg (inputLayout d 4)=rowCount d n := by
    change c.store.reg (inputLayout d 4)=_
    rw [hcs]
    simpa [inputLayout,TapeStore.setReg,low,marked,markedStore,TapeArrays.painted,TapeMacros.cellStore] using hs.size
  have hwidth : c.store.reg (inputLayout d 0)=fieldSize d n := hr 23 (by decide) (by decide) |>.trans hs.environment.cardinal
  have hro : c.roHead 0=n+1 := by
    change c.store.roHead 0=_
    rw [hcs]
    exact hs.inputHead
  have hhead : c.bufferHead 2=1 := by
    change c.store.bufferHead 2=_
    rw [hcs]
    exact congrFun htapes.2 2
  have hmarked (b : Fin 3) : TapeArrays.BottomMarked c.store b := by
    rw [hcs]
    exact markedStore_bottom d s hs.buffers hs.heads b
  have hri : Function.Injective (inputLayout d) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [inputLayout,low]
  obtain ⟨u,hu,hload,hloadB,hloadRO,hloadH,hloadMark,hloadTable⟩ := TesterInput.load_stops
    (inputLayout d) hri 2 inp M (by have := hcover.two;omega)
    (rowCount d n) (n+1) (fun z => decide (y z≠0)) c.store hcb
    (by rw [hwidth];exact (fieldSize_pos d n)) hcount hro hhead (hmarked 2) (by
      intro j
      simpa using TesterInput.word_symbols inp n _ y hi j)
  let post := TesterInput.loadStore (inputLayout d) 2 inp (rowCount d n) c.store
  have hframe (j : Fin 80) (hj1 : j≠79) (hj2 : j≠78) (hj3 : j≠5) (hj4 : j≠76)
      (hj5 : j≠2) : post.reg (low d j)=s.reg (low d j) := by
    rw [TesterInput.loadStore_register_frame (inputLayout d) hri 2 inp _ c.store]
    · exact hr j hj4 hj5
    · simpa [inputLayout,low,Fin.ext_iff] using And.intro hj1 (And.intro hj2 (And.intro hj3 hj4))
  refine ⟨5+1+t+1+u,_,?_,(hmarks.seq hc).seq hload,?_⟩
  · unfold inputTime
    omega
  · change InputReady d n M y post
    refine ⟨hloadB,?_,hframe 70 (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans hs.size,?_,?_,?_,?_,?_,?_⟩
    · apply hs.environment.frame
      intro i hi
      rcases hi with rfl|rfl|rfl|rfl <;>
        exact hframe _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [TesterInput.loadStore_output]
      rw [hcs]
      exact hs.output
    · have hw : c.reg (inputLayout d 0)=fieldSize d n := hwidth
      simpa only [hw,decide_eq_true_eq] using hloadTable
    · rw [hloadH,hwidth]
      exact hcover.word
    · rw [TesterInput.loadStore_bufferHead_frame _ _ _ (by decide)]
      rw [hcs]
      exact congrFun htapes.2 0
    · rw [TesterInput.loadStore_bufferHead_frame _ _ _ (by decide)]
      rw [hcs]
      exact congrFun htapes.2 1
    · intro b
      by_cases hb : b=2
      · subst b;exact hloadMark
      · have hz (k : ℕ) := TesterInput.loadStore_bufferSymbol_frame (inputLayout d) 2 b hb inp
          (rowCount d n) c.store k
        exact ⟨(hz 0).trans (hmarked b).1,fun k hk => by rw [hz];exact (hmarked b).2 k hk⟩



end ExpandingCodes.Computation.TesterPrefix

end FlattenModule83

/-! Inlined whole module: ExpandingCodes.Computation.TesterFrontend -/
section FlattenModule84


set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterFrontend
open NKtLB TesterGram TesterPrefix
open ExpandingCodes.PolynomialStretch





private theorem degree_injective (d : ℕ) : Function.Injective (degreeLayout d) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [degreeLayout,low]

private theorem degree_width (d : ℕ) (s : TapeStore (80+6*d) 3) :
    (TesterEvaluation.degreeStore (degreeLayout d) d s).reg (low d 23)=s.reg (low d 23) := by
  simp [TesterEvaluation.degreeStore,TesterEvaluation.degreeScaled,TesterEvaluation.degreePrepare,
    FieldPrograms.halfStore,SamplerEvaluation.scaleStore,degreeLayout,TapeStore.setReg,low]

private theorem degree_stops (d n M : ℕ) (hd : 4 ≤ d) (inp : Inputs)
    (y : Word (rowCount d n)) (s : TapeStore (80+6*d) 3)
    (hs : InputReady d n M y s) (hcover : TesterEnvelopeCovers d n M) :
    ∃ t e,t ≤ (d+1)*(30*(M+1)) ∧
      (TesterEvaluation.degree (degreeLayout d) d).Stops inp
        (s.toCfg (TesterEvaluation.degree (B := 3) (degreeLayout d) d).entry) t e ∧
      Core d (fieldExponent d n) (fieldExponent_pos d n) (auxiliaryDegree (fieldSize d n) d) M
        (fun z => decide (y z≠0)) e.store ∧
      e.output=[] ∧ e.bufferHead 0=1 ∧ e.bufferHead 1=1 ∧
      (∀ b,TapeArrays.BottomMarked e.store b) := by
  have hq : s.reg (degreeLayout d 0)=fieldSize d n := hs.environment.cardinal
  obtain ⟨t,e,ht,he,hes,hval,hframe,heb,hed⟩ := TesterEvaluation.degree_stops
    (degreeLayout d) (degree_injective d) d inp M (by have := hcover.two;omega) s hs.bounded
    (by rw [hq];exact hcover.cutoff)
  have hfield (j : Fin 80) (hj : j≠23 ∧ j≠0 ∧ j≠1 ∧ j≠2 ∧ j≠65) :
      e.reg (low d j)=s.reg (low d j) := by
    apply hframe
    intro i
    rcases hj with ⟨hj23,hj0,hj1,hj2,hj65⟩
    fin_cases i
    · exact (low_eq_iff d j 23).not.mpr hj23
    · exact (low_eq_iff d j 0).not.mpr hj0
    · exact (low_eq_iff d j 1).not.mpr hj1
    · exact (low_eq_iff d j 2).not.mpr hj2
    · exact (low_eq_iff d j 65).not.mpr hj65
  have htapes : e.bufferTape=s.bufferTape := congrArg (fun v => v.2.2.1) hed
  have hheads : e.store.bufferHead=s.bufferHead := congrArg (fun v => v.2.2.2) hed
  refine ⟨t,e,ht,he,?_,?_,?_,?_,?_⟩
  · refine ⟨heb,?_,?_,?_,?_,?_,?_⟩
    · constructor
      · exact (hfield 3 (by decide)).trans hs.environment.modulus
      · exact (hfield 19 (by decide)).trans hs.environment.length
      · change e.store.reg (low d 23)=_
        rw [hes,degree_width]
        exact hs.environment.cardinal
      · exact (hfield 24 (by decide)).trans hs.environment.square
    · change e.reg (low d 65)=_
      rw [TesterEvaluation.auxiliaryDegree_nat _ _ hd (fieldSize_ge_two d n)]
      change e.reg (low d 65)=((d-3)*(s.reg (low d 23)-1)-1)/2 at hval
      have hhq : s.reg (low d 23)=fieldSize d n := hs.environment.cardinal
      rw [hhq] at hval
      exact hval
    · exact (hfield 70 (by decide)).trans hs.size
    · simpa only [TapeArrays.BottomMarked,htapes] using hs.marked 2
    · simpa only [TapeArrays.ThermometerTable,TapeArrays.ThermometerAt,htapes,
        decide_eq_true_eq,fieldSize,rowCount] using hs.table
    · rw [hheads]
      exact hs.inputHead
  · exact (congrArg (fun v => v.2.1) hed).trans hs.output
  · change e.store.bufferHead 0=1
    rw [hheads]
    exact hs.gramHead
  · change e.store.bufferHead 1=1
    rw [hheads]
    exact hs.spareHead
  · intro b
    simpa only [TapeArrays.BottomMarked,htapes] using hs.marked b



theorem program_stops (d n M : ℕ) (hd : 4 ≤ d) (hn : 2 ≤ n)
    (inp : Inputs) (y : Word (rowCount d n)) (hi : inp.input=sizeInput n++wordBits y)
    (hcover : TesterEnvelopeCovers d n M) :
    ∃ t e,t ≤ time d n M ∧
      (program d).Stops inp ((initialStore d).toCfg (program d).entry) t e ∧
      Core d (fieldExponent d n) (fieldExponent_pos d n) (auxiliaryDegree (fieldSize d n) d) M
        (fun z => decide (y z≠0)) e.store ∧
      e.output=[] ∧ e.bufferHead 0=1 ∧ e.bufferHead 1=1 ∧
      (∀ b,TapeArrays.BottomMarked e.store b) := by
  obtain ⟨t₁,c₁,ht₁,h₁,_,hr₁⟩ := setup_initial_stops d n M (by omega) hn inp (wordBits y) hi hcover
  obtain ⟨t₂,c₂,ht₂,h₂,hr₂⟩ := input_stops d n M inp y hi c₁.store hr₁ hcover
  obtain ⟨t₃,c₃,ht₃,h₃,hcore,hout,hh0,hh1,hmarks⟩ := degree_stops d n M hd inp y c₂.store hr₂ hcover
  exact ⟨t₁+1+t₂+1+t₃,c₃.mapPC (TapeProgram.rightLabel _),by unfold time;omega,
    (h₁.seq h₂).seq h₃,hcore,hout,hh0,hh1,hmarks⟩



































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

private theorem cache_type_witness_tester_frontend (d n M : ℕ) (hd : 4 ≤ d) (hn : 2 ≤ n)
    (inp : Inputs) (y : ExpandingCodes.PolynomialStretch.Word (ExpandingCodes.PolynomialStretch.rowCount d n)) (hi : inp.input=ExpandingCodes.PolynomialStretch.sizeInput n++ExpandingCodes.PolynomialStretch.wordBits y)
    (hcover : ExpandingCodes.PolynomialStretch.TesterEnvelopeCovers d n M) :
    ∃ t e,t ≤ ExpandingCodes.Computation.TesterFrontend.time d n M ∧
      (ExpandingCodes.Computation.TesterFrontend.program d).Stops inp ((ExpandingCodes.Computation.TesterPrefix.initialStore d).toCfg (ExpandingCodes.Computation.TesterFrontend.program d).entry) t e ∧
      ExpandingCodes.Computation.TesterGram.Core d (ExpandingCodes.PolynomialStretch.fieldExponent d n) (ExpandingCodes.PolynomialStretch.fieldExponent_pos d n) (ExpandingCodes.PolynomialStretch.auxiliaryDegree (ExpandingCodes.PolynomialStretch.fieldSize d n) d) M
        (fun z => decide (y z≠0)) e.store ∧
      e.output=[] ∧ e.bufferHead 0=1 ∧ e.bufferHead 1=1 ∧
      (∀ b,ExpandingCodes.Computation.TapeArrays.BottomMarked e.store b) := by
  exact @ExpandingCodes.Computation.TesterFrontend.program_stops d n M hd hn inp y hi hcover


open Lean Elab Command
run_meta do
  let env ← getEnv
  let some target := env.find? `ExpandingCodes.Computation.TesterFrontend.program_stops | throwError "Missing cache target"
  let candidates := env.constants.toList.filterMap fun (n, ci) =>
    if privateToUserName? n == some `cache_type_witness_tester_frontend then some ci else none
  unless candidates.length == 1 do throwError "Missing unique cache type witness"
  unless ← Meta.isDefEq target.type candidates.head!.type do
    throwError "Cache target type differs from audited statement"
  let axes ← collectAxioms `ExpandingCodes.Computation.TesterFrontend.program_stops
  unless axes.all (fun n => #[`propext, `Classical.choice, `Quot.sound].contains n) do
    throwError "Unexpected target axioms: {axes}"
  IO.FS.writeFile "harness/submission/partition/tester_frontend-cache-audit.json" (Json.mkObj [("theorem_name",toJson "ExpandingCodes.Computation.TesterFrontend.program_stops"),("exact_statement_type",toJson true),("axioms",toJson (axes.map Name.toString))]).pretty
  logInfo m!"Closed helper target exact type and standard axioms only: {axes}"
