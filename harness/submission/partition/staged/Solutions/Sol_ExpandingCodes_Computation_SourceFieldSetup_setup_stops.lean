import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime
import Mathlib

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



















theorem bitEquiv_false : bitEquiv false = 0 := rfl

theorem bitEquiv_true : bitEquiv true = 1 := rfl

























































































































































































theorem selectedIndex_le (ell : ℕ) (h : 0 < ell) (i : Fin (2 ^ ell))
    (hi : FactorFree ell i) : selectedIndex ell h ≤ i := by
  exact Finset.min'_le _ _ (by simpa using hi)













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

theorem halveLoop_time_le (n : ℕ) : 3*(n/2)+2*(n%2)+1 ≤ 2*n+1 := by omega





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











theorem shiftStore_src (src quotient parity count : Fin R)
    (hsq : src ≠ quotient) (hsp : src ≠ parity) (hsc : src ≠ count)
    (n : ℕ) (d : TapeStore R B) :
    (shiftStore src quotient parity count n d).reg src = d.reg src/2^n := by
  induction n generalizing d with
  | zero => simp [shiftStore, TapeStore.setReg, hsc]
  | succ n ih =>
    rw [shiftStore, ih]
    have hsrc : (halfStepStore (d.setReg count n) src quotient parity).reg src = d.reg src/2 := by
      simp [halfStepStore, TapeStore.setReg, hsp, hsq, hsc]
    rw [hsrc, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm 2]

theorem shiftRight_stops (src quotient parity count : Fin R)
    (hsq : src ≠ quotient) (hsp : src ≠ parity) (hsc : src ≠ count)
    (hqp : quotient ≠ parity) (hqc : quotient ≠ count) (hpc : parity ≠ count)
    (inp : Inputs) (M n : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hn : d.reg count = n) (hs : d.reg src ≤ M)
    (hq : d.reg quotient ≤ M) (hp : d.reg parity ≤ M) :
    ∃ t, t ≤ n*(5*M+9)+1 ∧
      (shiftRight src quotient parity count).Stops inp
        (d.toCfg (TapeProgram.loopHeader 12)) t
        ((shiftStore src quotient parity count n d).toCfg (TapeProgram.loopExit 12)) := by
  induction n generalizing d with
  | zero =>
    have he : d.setReg count 0 = d := by simp [TapeStore.setReg, ← hn]
    exact ⟨1, by omega, by simpa [shiftRight, shiftStore, he] using
      TapeProgram.loop_zero (halfStep src quotient parity) count inp d hn⟩
  | succ n ih =>
    let d₁ := d.setReg count n
    obtain ⟨c, hc, hcs⟩ := halfStep_stops src quotient parity hsq hsp hqp inp d₁
    have hcsrc : c.reg src = d.reg src/2 := by
      change c.store.reg src = _
      rw [hcs]
      simp [halfStepStore, d₁, TapeStore.setReg, hsq, hsp, hsc]
    have hcq : c.reg quotient = 0 := by
      change c.store.reg quotient = _
      rw [hcs]
      simp [halfStepStore, TapeStore.setReg, hqp]
    have hcp : c.reg parity = d.reg src%2 := by
      change c.store.reg parity = _
      rw [hcs]
      simp [halfStepStore, d₁, TapeStore.setReg, hsc]
    have hcn : c.reg count = n := by
      change c.store.reg count = _
      rw [hcs]
      simp [halfStepStore, d₁, TapeStore.setReg, Ne.symm hsc, Ne.symm hqc, Ne.symm hpc]
    obtain ⟨t, ht, htail⟩ := ih c.store hcn (by simp only [TapeCfg.store, hcsrc]; omega)
      (by simp only [TapeCfg.store, hcq]; omega) (by simp only [TapeCfg.store, hcp]; omega)
    have hhead := TapeProgram.loop_positive_header (halfStep src quotient parity) count inp d (by omega)
    have hdec : TapeProgram.decStore count d = d₁ := by
      simp [TapeProgram.decStore, d₁, TapeStore.setReg, hn]
    rw [hdec] at hhead
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (halfStep src quotient parity) count)
    have hreturn := TapeProgram.loop_body_return (halfStep src quotient parity) count inp c hc.halted
    have hpost : shiftStore src quotient parity count n c.store =
        shiftStore src quotient parity count (n+1) d := by rw [shiftStore, hcs]
    have hall := ((hhead.trans hrun).trans hreturn).trans htail.exec
    rw [hpost] at hall
    refine ⟨_, ?_, ⟨hall, ?_⟩⟩
    · have hbody := halfStep_time_le (d.reg src) (d.reg quotient) (d.reg parity)
      simp only [d₁, TapeStore.setReg, Function.update_of_ne hqc,
        Function.update_of_ne hpc, Function.update_of_ne hsc]
      nlinarith
    · exact TapeProgram.loop_code_exit (halfStep src quotient parity) count

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

theorem shiftStore_bound (src quotient parity count : Fin R)
    (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) (hn : n ≤ M) :
    ∀ j, (shiftStore src quotient parity count n d).reg j ≤ M := by
  induction n generalizing d with
  | zero => exact setReg_bound d count 0 M hd (by omega)
  | succ n ih =>
    rw [shiftStore]
    exact ih _ (halfStepStore_bound _ src quotient parity M hM
      (setReg_bound d count n M hd (by omega))) (by omega)








theorem shiftStore_fresh (src quotient parity count j : Fin R)
    (hs : j ≠ src) (hq : j ≠ quotient) (hp : j ≠ parity) (hc : j ≠ count)
    (n : ℕ) (d : TapeStore R B) :
    (shiftStore src quotient parity count n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => simp [shiftStore, TapeStore.setReg, hc]
  | succ n ih =>
    rw [shiftStore, ih]
    simp [halfStepStore, TapeStore.setReg, hs, hq, hp, hc]

theorem reg_set_layout (r : Fin 7 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i j : Fin 7) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j; simp
  · simp [TapeStore.setReg, h, show r j ≠ r i from fun he => h (hr he)]



















theorem testBitStore_bit (r : Fin 7 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) :
    (testBitStore r d).reg (r 4) = if Nat.testBit (d.reg (r 0)) (d.reg (r 1)) then 1 else 0 := by
  have hs := shiftStore_src (r 2) (r 3) (r 4) (r 5)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (d.reg (r 1)) (bitPrepare r d)
  have hprep : (bitPrepare r d).reg (r 2) = d.reg (r 0) := by
    simp [bitPrepare, reg_set_layout r hr]
  rw [hprep] at hs
  have hbit : (testBitStore r d).reg (r 4) = d.reg (r 0)/2^d.reg (r 1)%2 := by
    simp only [testBitStore, halfStore, reg_set_layout r hr, ite_true]
    exact congrArg (· % 2) hs
  rw [hbit, Nat.testBit_eq_decide_div_mod_eq]
  by_cases hb : d.reg (r 0)/2^d.reg (r 1)%2 = 1
  · simp [hb]
  · have hz : d.reg (r 0)/2^d.reg (r 1)%2 = 0 := by omega
    simp [hb, hz]














theorem testBit_stops (r : Fin 7 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 64*(M+1)^2 ∧
      (testBit r).Stops inp (d.toCfg (testBit (B := B) r).entry) t e ∧
      e.store = testBitStore r d := by
  obtain ⟨c₁, h₁, hcs₁⟩ := TapeMacros.copy_stops (r 0) (r 2) (r 6)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d
  have hbound₁ : ∀ j, c₁.reg j ≤ M := by
    change ∀ j, c₁.store.reg j ≤ M
    rw [hcs₁]
    exact setReg_bound _ _ 0 M (setReg_bound d _ _ M hd (hd (r 0))) (by omega)
  obtain ⟨c₂, h₂, hcs₂⟩ := TapeMacros.copy_stops (r 1) (r 5) (r 6)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₁.store
  rw [hcs₁] at hcs₂
  change c₂.store = bitPrepare r d at hcs₂
  have hbound₂ : ∀ j, c₂.reg j ≤ M := by
    change ∀ j, c₂.store.reg j ≤ M
    rw [hcs₂]
    dsimp [bitPrepare]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M
    · exact setReg_bound _ _ 0 M (setReg_bound d _ _ M hd (hd (r 0))) (by omega)
    · simp [reg_set_layout r hr]
      exact hd (r 1)
  have hcount : c₂.reg (r 5) = d.reg (r 1) := by
    change c₂.store.reg (r 5) = _
    rw [hcs₂]
    simp [bitPrepare, reg_set_layout r hr]
  obtain ⟨t, ht, h₃⟩ := shiftRight_stops (r 2) (r 3) (r 4) (r 5)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp M (d.reg (r 1)) hM
    c₂.store hcount (hbound₂ (r 2)) (hbound₂ (r 3)) (hbound₂ (r 4))
  let d₃ := shiftStore (r 2) (r 3) (r 4) (r 5) (d.reg (r 1)) c₂.store
  have hbound₃ : ∀ j, d₃.reg j ≤ M :=
    shiftStore_bound _ _ _ _ M hM _ _ hbound₂ (hd (r 1))
  obtain ⟨c₄, h₄, hcs₄⟩ := halve_stops (r 2) (r 3) (r 4)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d₃
  have hall := ((h₁.seq h₂).seq h₃).seq h₄
  have hpost : c₄.store = testBitStore r d := by
    rw [hcs₄]
    simp only [d₃, hcs₂, testBitStore]
  refine ⟨_, _, ?_, hall, hpost⟩
  have htime₁ : d.reg (r 2)+d.reg (r 6)+5*d.reg (r 0)+7 ≤ 7*M+7 := by
    have := hd (r 2); have := hd (r 6); have := hd (r 0); omega
  have htime₂ : c₁.reg (r 5)+c₁.reg (r 6)+5*c₁.reg (r 1)+7 ≤ 7*M+7 := by
    have := hbound₁ (r 5); have := hbound₁ (r 6); have := hbound₁ (r 1); omega
  have htime₄ : d₃.reg (r 3)+d₃.reg (r 4)+3*(d₃.reg (r 2)/2)+2*(d₃.reg (r 2)%2)+5 ≤ 4*M+5 := by
    have := hbound₃ (r 3); have := hbound₃ (r 4); have := hbound₃ (r 2)
    have := halveLoop_time_le (d₃.reg (r 2)); omega
  have ht' := ht.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right (5*M+9) (hd (r 1))) 1)
  simp only [TapeCfg.store]
  nlinarith







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

/-! Inlined whole module: ExpandingCodes.Computation.FieldCoefficients -/
section FlattenModule48



set_option autoImplicit false

namespace ExpandingCodes.Computation.FieldPrograms
open NKtLB
open ExpandingCodes.PolynomialStretch.BinaryPolynomial

/-- The existing finite-field coefficient enumeration is exactly ordinary
binary digits, including its least-significant-first convention. -/
theorem indexEquiv_value (ell : ℕ) (a : Fin (2^ell)) (j : Fin ell) :
    (indexEquiv ell a j).val = a.val/2^j.val%2 := rfl

theorem indexEquiv_bit (ell : ℕ) (a : Fin (2^ell)) (j : Fin ell) :
    indexEquiv ell a j = bitEquiv (Nat.testBit a.val j.val) := by
  apply ZMod.val_injective 2
  rw [indexEquiv_value]
  change a.val/2^j.val%2 = (if Nat.testBit a.val j.val then (1 : ZMod 2) else 0).val
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases hb : a.val/2^j.val%2 = 1
  · simp [hb]
    rfl
  · have hz : a.val/2^j.val%2 = 0 := by omega
    simp [hb, hz]

/-- The monic modulus candidate has the ordinary binary index `2^ell+a`.
The equality covers every coefficient position, including the monic bit and
all the zero padding needed by the bounded convolution certificates. -/
theorem candidateCoefficient_bit (ell : ℕ) (a : Fin (2^ell)) (j : ℕ) :
    candidateCoefficient ell a j = bitEquiv (Nat.testBit (2^ell+a.val) j) := by
  by_cases he : j = ell
  · subst j
    rw [candidateCoefficient, if_pos rfl, Nat.testBit_two_pow_add_eq,
      Nat.testBit_lt_two_pow a.isLt]
    rfl
  · by_cases hj : j < ell
    · rw [candidateCoefficient, if_neg he, dif_pos hj, Nat.testBit_two_pow_add_gt hj]
      exact indexEquiv_bit ell a ⟨j, hj⟩
    · have hl : ell+1 ≤ j := by omega
      have hx : 2^ell+a.val < 2^j := by
        have hp : 2^ell+a.val < 2^(ell+1) := by
          rw [pow_succ]
          have := a.isLt
          omega
        exact hp.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hl)
      rw [candidateCoefficient, if_neg he, dif_neg hj, Nat.testBit_lt_two_pow hx]
      rfl

























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















theorem toggle_stops (x y p : Fin R) (hxy : x ≠ y) (hxp : x ≠ p) (hyp : y ≠ p)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ t, t ≤ 4 ∧ (toggle x y p).Stops inp (d.toCfg 0) t
      ((toggleStore x y p d).toCfg 4) := by
  have ha (i : Fin 5) (hi : i ≠ 4) : ¬ (toggle (B := B) x y p).halted (d.toCfg i) := by
    fin_cases i <;> simp_all [TapeProgram.halted, toggle]
  have hh (e : TapeStore R B) : (toggle x y p).halted (e.toCfg (4 : Fin 5)) := by
    simp [TapeProgram.halted, toggle]
  by_cases hx : d.reg x = 0
  · refine ⟨1, by omega, ⟨?_, hh _⟩⟩
    apply TapeProgram.Exec.one (ha 0 (by decide))
    simp [TapeProgram.step, toggle, toggleStore, hx]
  · let d₁ := d.setReg x (d.reg x-1)
    have hs₁ : (toggle x y p).step inp (d.toCfg 0) = d₁.toCfg 1 := by
      simp [TapeProgram.step, toggle, hx, d₁, TapeStore.setReg]
    have ha₁ : ¬ (toggle x y p).halted (d₁.toCfg (1 : Fin 5)) := by
      simp [TapeProgram.halted, toggle]
    by_cases hy : d.reg y = 0
    · refine ⟨2, by omega, ⟨?_, hh _⟩⟩
      apply TapeProgram.Exec.step (ha 0 (by decide)) hs₁
      apply TapeProgram.Exec.one ha₁
      simp [TapeProgram.step, toggle, toggleStore, hx, hy, d₁, TapeStore.setReg, Ne.symm hxy]
    · let d₂ := d₁.setReg y (d.reg y-1)
      have hs₂ : (toggle x y p).step inp (d₁.toCfg 1) = d₂.toCfg 2 := by
        simp [TapeProgram.step, toggle, d₂, d₁, TapeStore.setReg, Ne.symm hxy, hy]
      have ha₂ : ¬ (toggle x y p).halted (d₂.toCfg (2 : Fin 5)) := by
        simp [TapeProgram.halted, toggle]
      by_cases hp : d.reg p = 0
      · let d₃ := d₂.setReg p 0
        have hs₃ : (toggle x y p).step inp (d₂.toCfg 2) = d₃.toCfg 3 := by
          simp [TapeProgram.step, toggle, d₃, d₂, d₁, TapeStore.setReg,
            Ne.symm hxp, Ne.symm hyp, hp]
        refine ⟨4, by omega, ⟨?_, hh _⟩⟩
        apply TapeProgram.Exec.step (ha 0 (by decide)) hs₁
        apply TapeProgram.Exec.step ha₁ hs₂
        apply TapeProgram.Exec.step ha₂ hs₃
        apply TapeProgram.Exec.one
        · simp [TapeProgram.halted, toggle]
        · simp [TapeProgram.step, toggle, toggleStore, hx, hy, hp, d₃, d₂, d₁,
            TapeStore.setReg, Ne.symm hxp, Ne.symm hyp]
      · refine ⟨3, by omega, ⟨?_, hh _⟩⟩
        apply TapeProgram.Exec.step (ha 0 (by decide)) hs₁
        apply TapeProgram.Exec.step ha₁ hs₂
        apply TapeProgram.Exec.one ha₂
        simp [TapeProgram.step, toggle, toggleStore, hx, hy, hp, d₂, d₁,
          TapeStore.setReg, Ne.symm hxp, Ne.symm hyp]

theorem toggleStore_fresh (x y p j : Fin R) (d : TapeStore R B)
    (hjx : j ≠ x) (hjy : j ≠ y) (hjp : j ≠ p) :
    (toggleStore x y p d).reg j = d.reg j := by
  simp only [toggleStore]
  split <;> simp_all [TapeStore.setReg]
  split <;> simp_all [TapeStore.setReg]

theorem toggleStore_bound (x y p : Fin R) (d : TapeStore R B)
    (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (toggleStore x y p d).reg j ≤ M := by
  unfold toggleStore
  split
  · exact hd
  · split
    · exact setReg_bound _ _ _ M hd ((Nat.sub_le _ _).trans (hd x))
    · apply setReg_bound _ _ _ M
      · apply setReg_bound _ _ _ M
        · exact setReg_bound _ _ _ M hd ((Nat.sub_le _ _).trans (hd x))
        · exact (Nat.sub_le _ _).trans (hd y)
      · have := hd p
        split <;> omega

theorem toggleStore_parity (x y p : Fin R) (hxp : x ≠ p) (hyp : y ≠ p)
    (d : TapeStore R B) (hx : d.reg x ≤ 1) (hy : d.reg y ≤ 1) (hp : d.reg p ≤ 1) :
    (toggleStore x y p d).reg p = (d.reg p + d.reg x*d.reg y)%2 := by
  by_cases hx0 : d.reg x = 0
  · simp [toggleStore, hx0, Nat.mod_eq_of_lt (show d.reg p < 2 by omega)]
  · have hx1 : d.reg x = 1 := by omega
    by_cases hy0 : d.reg y = 0
    · simp [toggleStore, hx0, hy0, TapeStore.setReg, Ne.symm hxp,
        Nat.mod_eq_of_lt (show d.reg p < 2 by omega)]
    · have hy1 : d.reg y = 1 := by omega
      by_cases hp0 : d.reg p = 0
      · simp [toggleStore, hx1, hy1, hp0, TapeStore.setReg]
      · have hp1 : d.reg p = 1 := by omega
        simp [toggleStore, hx1, hy1, hp1, TapeStore.setReg]







theorem leftLayout_injective (r : Fin 12 → Fin R) (hr : Function.Injective r) :
    Function.Injective (leftLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [leftLayout]

theorem rightLayout_injective (r : Fin 12 → Fin R) (hr : Function.Injective r) :
    Function.Injective (rightLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [rightLayout]














theorem testBitStore_bound (r : Fin 7 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (testBitStore r d).reg j ≤ M := by
  have hprep : ∀ j, (bitPrepare r d).reg j ≤ M := by
    unfold bitPrepare
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M
    · exact setReg_bound _ _ 0 M (setReg_bound d _ _ M hd (hd (r 0))) (by omega)
    · simp [reg_set_layout r hr]
      exact hd (r 1)
  have hs := shiftStore_bound (r 2) (r 3) (r 4) (r 5) M hM (d.reg (r 1))
    (bitPrepare r d) hprep (hd (r 1))
  unfold testBitStore halfStore
  apply setReg_bound _ _ _ M
  · apply setReg_bound _ _ _ M
    · exact setReg_bound _ _ 0 M hs (by omega)
    · exact (Nat.div_le_self _ _).trans (hs (r 2))
  · omega

theorem testBitStore_fresh (r : Fin 7 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₂ : j ≠ r 2) (h₃ : j ≠ r 3) (h₄ : j ≠ r 4)
    (h₅ : j ≠ r 5) (h₆ : j ≠ r 6) :
    (testBitStore r d).reg j = d.reg j := by
  simp only [testBitStore, halfStore, TapeStore.setReg, Function.update_of_ne h₂,
    Function.update_of_ne h₃, Function.update_of_ne h₄]
  rw [shiftStore_fresh _ _ _ _ _ h₂ h₃ h₄ h₅]
  simp [bitPrepare, TapeStore.setReg, h₂, h₅, h₆]

theorem reg_set (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i j : Fin 12) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j; simp
  · simp [TapeStore.setReg, h, hr.ne h]

theorem bodyStore_fresh (r : Fin 12 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₃ : j ≠ r 3) (h₄ : j ≠ r 4) (h₆ : j ≠ r 6) (h₇ : j ≠ r 7)
    (h₈ : j ≠ r 8) (h₉ : j ≠ r 9) (h₁₀ : j ≠ r 10) (h₁₁ : j ≠ r 11) :
    (bodyStore r d).reg j = d.reg j := by
  unfold bodyStore
  simp only [TapeStore.setReg, Function.update_of_ne h₄]
  rw [toggleStore_fresh _ _ _ _ _ h₆ h₇ h₃]
  rw [testBitStore_fresh _ _ _ h₈ h₉ h₇ h₁₀ h₁₁]
  exact testBitStore_fresh _ _ _ h₈ h₉ h₆ h₁₀ h₁₁

theorem bodyStore_index (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (bodyStore r d).reg (r 4) = d.reg (r 4)+1 := by
  unfold bodyStore
  simp only [TapeStore.setReg, Function.update_self]
  rw [toggleStore_fresh _ _ _ _ _ (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))]
  rw [testBitStore_fresh _ _ _ (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))]
  rw [testBitStore_fresh _ _ _ (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))]








theorem bitValue_le (a j : ℕ) : bitValue a j ≤ 1 := by
  unfold bitValue; split <;> omega

theorem bodyStore_parity (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (hp : d.reg (r 3) ≤ 1) :
    (bodyStore r d).reg (r 3) =
      (d.reg (r 3) + bitValue (d.reg (r 0)) (d.reg (r 4)) *
        bitValue (d.reg (r 1)) (d.reg (r 5)))%2 := by
  let d₁ := testBitStore (leftLayout r) d
  let d₂ := testBitStore (rightLayout r) d₁
  have hf₁ (i : Fin 12) (h₂ : i ≠ 8) (h₃ : i ≠ 9) (h₄ : i ≠ 6)
      (h₅ : i ≠ 10) (h₆ : i ≠ 11) : d₁.reg (r i) = d.reg (r i) :=
    testBitStore_fresh _ _ _ (hr.ne h₂) (hr.ne h₃) (hr.ne h₄) (hr.ne h₅) (hr.ne h₆)
  have hf₂ (i : Fin 12) (h₂ : i ≠ 8) (h₃ : i ≠ 9) (h₄ : i ≠ 7)
      (h₅ : i ≠ 10) (h₆ : i ≠ 11) : d₂.reg (r i) = d₁.reg (r i) :=
    testBitStore_fresh _ _ _ (hr.ne h₂) (hr.ne h₃) (hr.ne h₄) (hr.ne h₅) (hr.ne h₆)
  have hp₂ : d₂.reg (r 3) = d.reg (r 3) := by
    rw [hf₂ 3 (by decide) (by decide) (by decide) (by decide) (by decide),
      hf₁ 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
  have hx : d₂.reg (r 6) = bitValue (d.reg (r 0)) (d.reg (r 4)) := by
    rw [hf₂ 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact testBitStore_bit (leftLayout r) (leftLayout_injective r hr) d
  have hy : d₂.reg (r 7) = bitValue (d.reg (r 1)) (d.reg (r 5)) := by
    have h := testBitStore_bit (rightLayout r) (rightLayout_injective r hr) d₁
    change d₂.reg (r 7) = bitValue (d₁.reg (r 1)) (d₁.reg (r 5)) at h
    rw [h, hf₁ 1 (by decide) (by decide) (by decide) (by decide) (by decide),
      hf₁ 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  change ((toggleStore (r 6) (r 7) (r 3) d₂).setReg (r 4) _).reg (r 3) = _
  rw [reg_set r hr]
  simp only [show (3 : Fin 12) ≠ 4 from by decide, ite_false]
  rw [toggleStore_parity _ _ _ (hr.ne (by decide)) (hr.ne (by decide)) _
    (by rw [hx]; exact bitValue_le _ _) (by rw [hy]; exact bitValue_le _ _)
    (by rw [hp₂]; exact hp), hp₂, hx, hy]

theorem body_stops (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 128*(M+1)^2+8 ∧
      (body r).Stops inp (d.toCfg (body (B := B) r).entry) t e ∧
      e.store = bodyStore r d := by
  obtain ⟨t₁, c₁, ht₁, h₁, hs₁⟩ := testBit_stops (leftLayout r)
    (leftLayout_injective r hr) inp M hM d hd
  have hb₁ : ∀ j, c₁.store.reg j ≤ M := by
    rw [hs₁]; exact testBitStore_bound _ (leftLayout_injective r hr) _ M hM hd
  obtain ⟨t₂, c₂, ht₂, h₂, hs₂⟩ := testBit_stops (rightLayout r)
    (rightLayout_injective r hr) inp M hM c₁.store hb₁
  obtain ⟨t₃, ht₃, h₃⟩ := toggle_stops (r 6) (r 7) (r 3)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₂.store
  have h₄ := TapeMacros.increment_stops (r 4) inp (toggleStore (r 6) (r 7) (r 3) c₂.store)
  have hall := ((h₁.seq h₂).seq h₃).seq h₄
  refine ⟨_, _, by omega, hall, ?_⟩
  change (toggleStore (r 6) (r 7) (r 3) c₂.store).setReg (r 4) _ = _
  rw [hs₂, hs₁]
  rfl

theorem bodyStore_bound (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M)
    (hj : d.reg (r 4)+1 ≤ M) : ∀ j, (bodyStore r d).reg j ≤ M := by
  have h₁ := testBitStore_bound (leftLayout r) (leftLayout_injective r hr) d M hM hd
  have h₂ := testBitStore_bound (rightLayout r) (rightLayout_injective r hr) _ M hM h₁
  have h₃ := toggleStore_bound (r 6) (r 7) (r 3) _ M hM h₂
  apply setReg_bound _ _ _ M h₃
  have he := bodyStore_index r hr d
  have he' : (toggleStore (r 6) (r 7) (r 3)
      (testBitStore (rightLayout r) (testBitStore (leftLayout r) d))).reg (r 4)+1 =
      d.reg (r 4)+1 := by
    simpa only [bodyStore, TapeStore.setReg, Function.update_self] using he
  rw [he']
  exact hj










theorem loop_stops (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hn : d.reg (r 5) = n) (hd : ∀ j, d.reg j ≤ M)
    (hj : d.reg (r 4)+n ≤ M) :
    ∃ t, t ≤ n*(128*(M+1)^2+10)+1 ∧
      (loop r).Stops inp (d.toCfg (TapeProgram.loopHeader 97)) t
        ((loopStore r n d).toCfg (TapeProgram.loopExit 97)) := by
  induction n generalizing d with
  | zero => exact ⟨1, by omega, TapeProgram.loop_zero (body r) (r 5) inp d hn⟩
  | succ n ih =>
    let d₁ := d.setReg (r 5) n
    have hb₁ : ∀ j, d₁.reg j ≤ M :=
      setReg_bound d _ n M hd (by have := hd (r 5); omega)
    obtain ⟨s, c, hs, hc, hcs⟩ := body_stops r hr inp M hM d₁ hb₁
    have hcn : c.reg (r 5) = n := by
      change c.store.reg (r 5) = _
      rw [hcs, bodyStore_fresh r d₁ (r 5) (hr.ne (by decide)) (hr.ne (by decide))
        (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
        (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))]
      simp [d₁]
    have hcj : c.reg (r 4) = d.reg (r 4)+1 := by
      change c.store.reg (r 4) = _
      rw [hcs, bodyStore_index r hr]
      simp [d₁, reg_set r hr]
    have hcb : ∀ j, c.store.reg j ≤ M := by
      rw [hcs]
      apply bodyStore_bound r hr d₁ M hM hb₁
      simp only [d₁, reg_set r hr, show (4 : Fin 12) ≠ 5 from by decide, ite_false]
      omega
    obtain ⟨t, ht, htail⟩ := ih c.store hcn hcb (by change c.reg (r 4)+n ≤ M; omega)
    have hhead := TapeProgram.loop_positive_header (body r) (r 5) inp d (by omega)
    have hdec : TapeProgram.decStore (r 5) d = d₁ := by
      simp [TapeProgram.decStore, d₁, TapeStore.setReg, hn]
    rw [hdec] at hhead
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (body r) (r 5))
    have hreturn := TapeProgram.loop_body_return (body r) (r 5) inp c hc.halted
    have hpost : loopStore r n c.store = loopStore r (n+1) d := by rw [loopStore, hcs]
    have hall := ((hhead.trans hrun).trans hreturn).trans htail.exec
    rw [hpost] at hall
    refine ⟨_, ?_, ⟨hall, TapeProgram.loop_code_exit (body r) (r 5)⟩⟩
    change 1+s+1+t ≤ (n+1)*(128*(M+1)^2+10)+1
    calc
      1+s+1+t ≤ 1+(128*(M+1)^2+8)+1+(n*(128*(M+1)^2+10)+1) := by omega
      _ = (n+1)*(128*(M+1)^2+10)+1 := by ring

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














theorem bitValue_cast (a j : ℕ) : (bitValue a j : ZMod 2) = bitEquiv (Nat.testBit a j) := by
  cases h : Nat.testBit a j <;> simp [bitValue, h, bitEquiv]

theorem bodyStore_parity_cast (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (hp : d.reg (r 3) ≤ 1) :
    ((bodyStore r d).reg (r 3) : ZMod 2) = (d.reg (r 3) : ZMod 2) +
      bitEquiv (Nat.testBit (d.reg (r 0)) (d.reg (r 4))) *
      bitEquiv (Nat.testBit (d.reg (r 1)) (d.reg (r 5))) := by
  rw [bodyStore_parity r hr d hp, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul,
    bitValue_cast, bitValue_cast]

theorem loopStore_parity (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (a b k n : ℕ) (d : TapeStore R B) (ha : d.reg (r 0) = a) (hb : d.reg (r 1) = b)
    (hp : d.reg (r 3) ≤ 1) (hj : d.reg (r 4)+n = k+1)
    (hpar : (d.reg (r 3) : ZMod 2) = ∑ j ∈ Finset.range (d.reg (r 4)),
      bitEquiv (Nat.testBit a j)*bitEquiv (Nat.testBit b (k-j))) :
    ((loopStore r n d).reg (r 3) : ZMod 2) = rawConvolution a b k := by
  induction n generalizing d with
  | zero => simpa [loopStore, rawConvolution, show d.reg (r 4) = k+1 by omega] using hpar
  | succ n ih =>
    let d₁ := d.setReg (r 5) n
    have hframe (i : Fin 12) (hi : i = 0 ∨ i = 1) :
        (bodyStore r d₁).reg (r i) = d.reg (r i) := by
      rcases hi with rfl | rfl
      all_goals
        rw [bodyStore_fresh r _ _ (hr.ne (by decide)) (hr.ne (by decide))
          (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
          (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))]
        simp [d₁, reg_set r hr]
    have hp₁ : d₁.reg (r 3) = d.reg (r 3) := by simp [d₁, reg_set r hr]
    have hj₁ : d₁.reg (r 4) = d.reg (r 4) := by simp [d₁, reg_set r hr]
    have hnextj : (bodyStore r d₁).reg (r 4) = d.reg (r 4)+1 := by
      rw [bodyStore_index r hr, hj₁]
    rw [loopStore]
    apply ih (bodyStore r d₁) ((hframe 0 (Or.inl rfl)).trans ha)
      ((hframe 1 (Or.inr rfl)).trans hb)
    · rw [bodyStore_parity r hr d₁ (by rw [hp₁]; exact hp)]
      omega
    · omega
    · rw [bodyStore_parity_cast r hr d₁ (by rw [hp₁]; exact hp), hp₁, hpar,
        hnextj, Finset.sum_range_succ]
      have ha₁ : d₁.reg (r 0) = a := by simp [d₁, reg_set r hr, ha]
      have hb₁ : d₁.reg (r 1) = b := by simp [d₁, reg_set r hr, hb]
      have hc₁ : d₁.reg (r 5) = k-d.reg (r 4) := by simp [d₁]; omega
      rw [ha₁, hb₁, hj₁, hc₁]












theorem prepare_stops (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (prepare r).Stops inp (d.toCfg (prepare (B := B) r).entry)
      (d.reg (r 3)+d.reg (r 4)+d.reg (r 5)+d.reg (r 11)+5*d.reg (r 2)+13) e ∧
      e.store = prepareStore r d := by
  have h₁ := TapeMacros.clear_stops (r 3) inp (d.reg (r 3)) d rfl
  have h₂ := TapeMacros.clear_stops (r 4) inp (d.reg (r 4)) (d.setReg (r 3) 0)
    (by simp [reg_set r hr])
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops (r 2) (r 5) (r 11)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp
    ((d.setReg (r 3) 0).setReg (r 4) 0)
  have h₄ := TapeMacros.increment_stops (r 5) inp c.store
  have hall := ((h₁.seq h₂).seq hc).seq h₄
  refine ⟨((c.store.setReg (r 5) (c.store.reg (r 5)+1)).toCfg (1 : Fin 2)).mapPC
    (TapeProgram.rightLabel 15), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | (simp [reg_set r hr]; omega)
  · change c.store.setReg (r 5) _ = _
    rw [hcs]
    rfl

theorem prepareStore_reg (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 12) :
    (prepareStore r d).reg (r i) =
      if i = 5 then d.reg (r 2)+1 else if i = 3 ∨ i = 4 ∨ i = 11 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [prepareStore, reg_set r hr]

theorem prepareStore_bound (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (M : ℕ) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (prepareStore r d).reg j ≤ M+1 := by
  unfold prepareStore
  apply setReg_bound _ _ _ (M+1)
  · apply setReg_bound _ _ 0 (M+1) _ (by omega)
    apply setReg_bound _ _ _ (M+1)
    · apply setReg_bound _ _ 0 (M+1) _ (by omega)
      exact setReg_bound d _ 0 (M+1) (fun j => (hd j).trans (by omega)) (by omega)
    · simp only [reg_set r hr]
      simp
      have := hd (r 2); omega
  · simp [reg_set r hr]
    exact hd (r 2)









theorem convolution_stops_exact (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 1000*(M+1)^3 ∧
      (convolution r).Stops inp (d.toCfg (convolution (B := B) r).entry) t e ∧
      e.store = convolutionStore r d := by
  obtain ⟨c, hc, hcs⟩ := prepare_stops r hr inp d
  have hcb : ∀ j, c.store.reg j ≤ M+1 := by rw [hcs]; exact prepareStore_bound r hr d M hd
  have hcn : c.reg (r 5) = d.reg (r 2)+1 := by
    change c.store.reg (r 5) = _
    rw [hcs, prepareStore_reg r hr]; simp
  have hcj : c.reg (r 4) = 0 := by
    change c.store.reg (r 4) = _
    rw [hcs, prepareStore_reg r hr]; simp
  obtain ⟨t, ht, he⟩ := loop_stops r hr inp (M+1) (by omega)
    (d.reg (r 2)+1) c.store hcn hcb (by simp only [TapeCfg.store, hcj]; have := hd (r 2); omega)
  have hall := hc.seq he
  refine ⟨_, _, ?_, hall, ?_⟩
  · have hp : d.reg (r 3)+d.reg (r 4)+d.reg (r 5)+d.reg (r 11)+5*d.reg (r 2)+13 ≤ 9*M+13 := by
      have := hd (r 3); have := hd (r 4); have := hd (r 5)
      have := hd (r 11); have := hd (r 2); omega
    have hb : 128*(M+1+1)^2+10 ≤ 522*(M+1)^2 := by nlinarith
    have hm := Nat.mul_le_mul (Nat.add_le_add_right (hd (r 2)) 1) hb
    have heq : (M+1)*(522*(M+1)^2) = 522*(M+1)^3 := by ring
    rw [heq] at hm
    have ht' : t ≤ 522*(M+1)^3+1 := ht.trans (Nat.add_le_add_right hm 1)
    have hcub : M+1 ≤ (M+1)^3 := by nlinarith
    change d.reg (r 3)+d.reg (r 4)+d.reg (r 5)+d.reg (r 11)+5*d.reg (r 2)+13+1+t ≤ _
    omega
  · change loopStore r (d.reg (r 2)+1) c.store = _
    rw [hcs]
    rfl

theorem loopStore_parity_le (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) (hp : d.reg (r 3) ≤ 1) :
    (loopStore r n d).reg (r 3) ≤ 1 := by
  induction n generalizing d with
  | zero => exact hp
  | succ n ih =>
    rw [loopStore]
    apply ih
    rw [bodyStore_parity r hr _ (by simpa [reg_set r hr] using hp)]
    omega

theorem convolutionStore_parity (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) :
    ((convolutionStore r d).reg (r 3) : ZMod 2) =
      rawConvolution (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 2)) := by
  apply loopStore_parity r hr _ _ _ _ (prepareStore r d)
  · simp [prepareStore_reg r hr]
  · simp [prepareStore_reg r hr]
  · simp [prepareStore_reg r hr]
  · simp [prepareStore_reg r hr]
  · simp [prepareStore_reg r hr]

theorem convolutionStore_bit (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (convolutionStore r d).reg (r 3) ≤ 1 := by
  apply loopStore_parity_le r hr
  simp [prepareStore_reg r hr]
















@[simp] theorem tapeData_setReg (d : TapeStore R B) (i : Fin R) (n : ℕ) :
    tapeData (d.setReg i n) = tapeData d := rfl

theorem shiftStore_tapeData (s q p c : Fin R) (n : ℕ) (d : TapeStore R B) :
    tapeData (shiftStore s q p c n d) = tapeData d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [shiftStore, ih]
    rfl

theorem testBitStore_tapeData (r : Fin 7 → Fin R) (d : TapeStore R B) :
    tapeData (testBitStore r d) = tapeData d := by
  unfold testBitStore halfStore
  simp only [tapeData_setReg, shiftStore_tapeData]
  rfl

theorem toggleStore_tapeData (x y p : Fin R) (d : TapeStore R B) :
    tapeData (toggleStore x y p d) = tapeData d := by
  unfold toggleStore
  split
  · rfl
  · split <;> rfl

theorem bodyStore_tapeData (r : Fin 12 → Fin R) (d : TapeStore R B) :
    tapeData (bodyStore r d) = tapeData d := by
  simp only [bodyStore, tapeData_setReg, toggleStore_tapeData, testBitStore_tapeData]

theorem loopStore_tapeData (r : Fin 12 → Fin R) (n : ℕ) (d : TapeStore R B) :
    tapeData (loopStore r n d) = tapeData d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [loopStore, ih, bodyStore_tapeData, tapeData_setReg]

theorem convolutionStore_tapeData (r : Fin 12 → Fin R) (d : TapeStore R B) :
    tapeData (convolutionStore r d) = tapeData d := by
  rw [convolutionStore, loopStore_tapeData]
  rfl

/-- Runtime bounds for every working counter, including the final position. -/
theorem loopStore_bound (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) (hj : d.reg (r 4)+n ≤ M) (hn : n ≤ M) :
    ∀ j, (loopStore r n d).reg j ≤ M := by
  induction n generalizing d with
  | zero => exact hd
  | succ n ih =>
    rw [loopStore]
    have hb := setReg_bound d (r 5) n M hd (by omega)
    apply ih _ (bodyStore_bound r hr _ M hM hb (by simp [reg_set r hr]; omega))
    · rw [bodyStore_index r hr]
      simp only [reg_set r hr, show (4 : Fin 12) ≠ 5 from by decide, ite_false]
      omega
    · omega









theorem convolutionStore_fresh (r : Fin 12 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₃ : j ≠ r 3) (h₄ : j ≠ r 4) (h₅ : j ≠ r 5)
    (h₆ : j ≠ r 6) (h₇ : j ≠ r 7) (h₈ : j ≠ r 8) (h₉ : j ≠ r 9)
    (h₁₀ : j ≠ r 10) (h₁₁ : j ≠ r 11) :
    (convolutionStore r d).reg j = d.reg j := by
  rw [convolutionStore, loopStore_fresh r _ j h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁]
  simp [prepareStore, TapeStore.setReg, h₃, h₄, h₅, h₁₁]

theorem prepareStore_bound_of (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (M : ℕ) (hd : ∀ j, d.reg j ≤ M) (hk : d.reg (r 2)+1 ≤ M) :
    ∀ j, (prepareStore r d).reg j ≤ M := by
  unfold prepareStore
  apply setReg_bound _ _ _ M
  · apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M
    · exact setReg_bound _ _ 0 M (setReg_bound d _ 0 M hd (by omega)) (by omega)
    · simp [reg_set r hr]
      exact hd (r 2)
  · simpa [reg_set r hr] using hk

theorem convolutionStore_bound_of (r : Fin 12 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hk : d.reg (r 2)+1 ≤ M) : ∀ j, (convolutionStore r d).reg j ≤ M := by
  apply loopStore_bound r hr M hM _ _ (prepareStore_bound_of r hr d M hd hk)
  · simpa [prepareStore_reg r hr] using hk
  · exact hk

/-- Exact coefficient encoding, including high zero padding. -/
theorem bufferCoefficient_bit (ell : ℕ) (a : Fin (2^ell)) (j : ℕ) :
    BinaryField.bufferCoefficient (indexEquiv ell a) j = bitEquiv (Nat.testBit a.val j) := by
  unfold BinaryField.bufferCoefficient
  split_ifs with hj
  · exact indexEquiv_bit ell a ⟨j, hj⟩
  · rw [Nat.testBit_lt_two_pow (a.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
    rfl

theorem rawConvolution_eq_convolution (ell₁ ell₂ : ℕ) (a : Fin (2^ell₁))
    (b : Fin (2^ell₂)) (k : ℕ) :
    rawConvolution a.val b.val k =
      BinaryField.convolution (indexEquiv ell₁ a) (indexEquiv ell₂ b) k := by
  simp only [rawConvolution, BinaryField.convolution, bufferCoefficient_bit]



































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










theorem xorInto_stops (x unit p : Fin R) (hxu : x ≠ unit) (hxp : x ≠ p) (hup : unit ≠ p)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ t e, t ≤ d.reg unit+8 ∧
      (xorInto x unit p).Stops inp (d.toCfg (xorInto (B := B) x unit p).entry) t e ∧
      e.store = xorStore x unit p d := by
  have h₁ := TapeMacros.clear_stops unit inp (d.reg unit) d rfl
  have h₂ := TapeMacros.increment_stops unit inp (d.setReg unit 0)
  have hz : (d.setReg unit 0).reg unit = 0 := by simp [TapeStore.setReg]
  rw [hz, zero_add] at h₂
  obtain ⟨t, ht, h₃⟩ := toggle_stops x unit p hxu hxp hup inp ((d.setReg unit 0).setReg unit 1)
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_, _, by omega, hall, ?_⟩
  change toggleStore x unit p ((d.setReg unit 0).setReg unit 1) = _
  simp only [TapeStore.setReg_same]
  rfl

theorem xorStore_parity (x unit p : Fin R) (hxu : x ≠ unit) (hxp : x ≠ p) (hup : unit ≠ p)
    (d : TapeStore R B) (hx : d.reg x ≤ 1) (hp : d.reg p ≤ 1) :
    (xorStore x unit p d).reg p = (d.reg p+d.reg x)%2 := by
  unfold xorStore
  rw [toggleStore_parity x unit p hxp hup]
  · simp [TapeStore.setReg, hxu, Ne.symm hup]
  · simpa [TapeStore.setReg, hxu] using hx
  · simp [TapeStore.setReg]
  · simpa [TapeStore.setReg, Ne.symm hup] using hp

theorem xorStore_fresh (x unit p j : Fin R) (d : TapeStore R B)
    (hjx : j ≠ x) (hju : j ≠ unit) (hjp : j ≠ p) :
    (xorStore x unit p d).reg j = d.reg j := by
  rw [xorStore, toggleStore_fresh x unit p j _ hjx hju hjp]
  simp [TapeStore.setReg, hju]

theorem xorStore_bound (x unit p : Fin R) (d : TapeStore R B)
    (M : ℕ) (hM : 1 ≤ M) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (xorStore x unit p d).reg j ≤ M :=
  toggleStore_bound x unit p _ M hM (setReg_bound d unit 1 M hd hM)

theorem xorStore_tapeData (x unit p : Fin R) (d : TapeStore R B) :
    tapeData (xorStore x unit p d) = tapeData d := by
  rw [xorStore, toggleStore_tapeData, tapeData_setReg]









theorem requireZero_stops (x flag : Fin R) (hxf : x ≠ flag)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ t, t ≤ 2 ∧ (requireZero x flag).Stops inp (d.toCfg 0) t
      ((requireStore x flag d).toCfg 2) := by
  by_cases hx : d.reg x = 0
  · refine ⟨1, by omega, ⟨?_, ?_⟩⟩
    · apply TapeProgram.Exec.one
      · simp [TapeProgram.halted, requireZero]
      · simp [TapeProgram.step, requireZero, requireStore, hx]
    · simp [TapeProgram.halted, requireZero]
  · refine ⟨2, by omega, ⟨?_, ?_⟩⟩
    · apply TapeProgram.Exec.step (d := (d.setReg x (d.reg x-1)).toCfg 1)
      · simp [TapeProgram.halted, requireZero]
      · simp [TapeProgram.step, requireZero, hx, TapeStore.setReg]
      · apply TapeProgram.Exec.one
        · simp [TapeProgram.halted, requireZero]
        · by_cases hf : d.reg flag = 0
          · simp [TapeProgram.step, requireZero, requireStore, hx, hf, TapeStore.setReg, Ne.symm hxf]
          · simp [TapeProgram.step, requireZero, requireStore, hx, hf, TapeStore.setReg, Ne.symm hxf]
    · simp [TapeProgram.halted, requireZero]

theorem requireStore_flag (x flag : Fin R) (hxf : x ≠ flag)
    (d : TapeStore R B) (hf : d.reg flag ≤ 1) :
    (requireStore x flag d).reg flag = if d.reg x = 0 then d.reg flag else 0 := by
  by_cases hx : d.reg x = 0
  · simp [requireStore, hx]
  · simp [requireStore, hx, TapeStore.setReg]
    omega

theorem requireStore_fresh (x flag j : Fin R) (d : TapeStore R B)
    (hjx : j ≠ x) (hjf : j ≠ flag) : (requireStore x flag d).reg j = d.reg j := by
  unfold requireStore
  split <;> simp_all [TapeStore.setReg]

theorem requireStore_bound (x flag : Fin R) (d : TapeStore R B)
    (M : ℕ) (hd : ∀ j, d.reg j ≤ M) : ∀ j, (requireStore x flag d).reg j ≤ M := by
  unfold requireStore
  split
  · exact hd
  · apply setReg_bound _ _ _ M
    · exact setReg_bound d x _ M hd ((Nat.sub_le _ _).trans (hd x))
    · exact (Nat.sub_le _ _).trans (hd flag)

theorem requireStore_tapeData (x flag : Fin R) (d : TapeStore R B) :
    tapeData (requireStore x flag d) = tapeData d := by
  unfold requireStore
  split <;> rfl










theorem leftLayout_injective (r : Fin 18 → Fin R) (hr : Function.Injective r) :
    Function.Injective (leftLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [leftLayout]

theorem rightLayout_injective (r : Fin 18 → Fin R) (hr : Function.Injective r) :
    Function.Injective (rightLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [rightLayout]

theorem remainderLayout_injective (r : Fin 18 → Fin R) (hr : Function.Injective r) :
    Function.Injective (remainderLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [remainderLayout]
























theorem leftStore_fresh (r : Fin 18 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 18) (hi : i ≠ 7) (hlt : i < 10) :
    (convolutionStore (leftLayout r) d).reg (r i) = d.reg (r i) := by
  exact convolutionStore_fresh _ _ _
    (hr.ne hi)
    (hr.ne (show i ≠ (10:Fin 18) from by omega))
    (hr.ne (show i ≠ (11:Fin 18) from by omega))
    (hr.ne (show i ≠ (12:Fin 18) from by omega))
    (hr.ne (show i ≠ (13:Fin 18) from by omega))
    (hr.ne (show i ≠ (14:Fin 18) from by omega))
    (hr.ne (show i ≠ (15:Fin 18) from by omega))
    (hr.ne (show i ≠ (16:Fin 18) from by omega))
    (hr.ne (show i ≠ (17:Fin 18) from by omega))


theorem rightStore_fresh (r : Fin 18 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 18) (hi : i ≠ 8) (hlt : i < 10) :
    (convolutionStore (rightLayout r) d).reg (r i) = d.reg (r i) := by
  exact convolutionStore_fresh _ _ _
    (hr.ne hi)
    (hr.ne (show i ≠ (10:Fin 18) from by omega))
    (hr.ne (show i ≠ (11:Fin 18) from by omega))
    (hr.ne (show i ≠ (12:Fin 18) from by omega))
    (hr.ne (show i ≠ (13:Fin 18) from by omega))
    (hr.ne (show i ≠ (14:Fin 18) from by omega))
    (hr.ne (show i ≠ (15:Fin 18) from by omega))
    (hr.ne (show i ≠ (16:Fin 18) from by omega))
    (hr.ne (show i ≠ (17:Fin 18) from by omega))


theorem remainderStore_fresh (r : Fin 18 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 18) (hi : i ≠ 9) (hlt : i < 14) :
    (testBitStore (remainderLayout r) d).reg (r i) = d.reg (r i) := by
  exact testBitStore_fresh _ _ _
    (hr.ne (show i ≠ (14:Fin 18) from by omega))
    (hr.ne (show i ≠ (15:Fin 18) from by omega)) (hr.ne hi)
    (hr.ne (show i ≠ (16:Fin 18) from by omega))
    (hr.ne (show i ≠ (17:Fin 18) from by omega))

theorem coefficient_stops_exact (r : Fin 18 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) (hk : d.reg (r 5)+1 ≤ M) :
    ∃ t e, t ≤ 2200*(M+1)^3 ∧
      (coefficient r).Stops inp (d.toCfg (coefficient (B := B) r).entry) t e ∧
      e.store = coefficientStore r d := by
  obtain ⟨t₁, c₁, ht₁, h₁, hs₁⟩ := convolution_stops_exact (leftLayout r)
    (leftLayout_injective r hr) inp M hM d hd
  have hb₁ : ∀ j, c₁.store.reg j ≤ M := by
    rw [hs₁]; exact convolutionStore_bound_of _ (leftLayout_injective r hr) M hM d hd hk
  have hk₁ : c₁.reg (r 5)+1 ≤ M := by
    change c₁.store.reg (r 5)+1 ≤ M
    rw [hs₁, leftStore_fresh r hr _ 5 (by decide) (by decide)]
    exact hk
  obtain ⟨t₂, c₂, ht₂, h₂, hs₂⟩ := convolution_stops_exact (rightLayout r)
    (rightLayout_injective r hr) inp M hM c₁.store hb₁
  have hb₂ : ∀ j, c₂.store.reg j ≤ M := by
    rw [hs₂]; exact convolutionStore_bound_of _ (rightLayout_injective r hr) M hM _ hb₁ hk₁
  obtain ⟨t₃, c₃, ht₃, h₃, hs₃⟩ := testBit_stops (remainderLayout r)
    (remainderLayout_injective r hr) inp M hM c₂.store hb₂
  have hb₃ : ∀ j, c₃.store.reg j ≤ M := by
    rw [hs₃]; exact testBitStore_bound _ (remainderLayout_injective r hr) _ M hM hb₂
  obtain ⟨t₄, c₄, ht₄, h₄, hs₄⟩ := xorInto_stops (r 8) (r 16) (r 7)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₃.store
  have hb₄ : ∀ j, c₄.store.reg j ≤ M := by
    rw [hs₄]; exact xorStore_bound _ _ _ _ M hM hb₃
  obtain ⟨t₅, c₅, ht₅, h₅, hs₅⟩ := xorInto_stops (r 9) (r 16) (r 7)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₄.store
  obtain ⟨t₆, ht₆, h₆⟩ := requireZero_stops (r 7) (r 6) (hr.ne (by decide)) inp c₅.store
  have hall := ((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆
  refine ⟨_, _, ?_, hall, ?_⟩
  · have h₄' : t₄ ≤ M+8 := ht₄.trans (Nat.add_le_add_right (hb₃ (r 16)) 8)
    have h₅' : t₅ ≤ M+8 := ht₅.trans (Nat.add_le_add_right (hb₄ (r 16)) 8)
    have hpow : (M+1)^2 ≤ (M+1)^3 := by nlinarith
    have hM' : M+1 ≤ (M+1)^3 := by nlinarith
    omega
  · change requireStore (r 7) (r 6) c₅.store = _
    rw [hs₅, hs₄, hs₃, hs₂, hs₁]
    rfl

theorem coefficientStore_fresh (r : Fin 18 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 18) (hi : i < 6) :
    (coefficientStore r d).reg (r i) = d.reg (r i) := by
  unfold coefficientStore
  rw [requireStore_fresh _ _ _ _ (hr.ne (by omega)) (hr.ne (by omega)),
    xorStore_fresh _ _ _ _ _ (hr.ne (by omega)) (hr.ne (by omega)) (hr.ne (by omega)),
    xorStore_fresh _ _ _ _ _ (hr.ne (by omega)) (hr.ne (by omega)) (hr.ne (by omega)),
    remainderStore_fresh r hr _ i (by omega) (by omega),
    rightStore_fresh r hr _ i (by omega) (by omega), leftStore_fresh r hr _ i (by omega) (by omega)]

theorem coefficientStore_bound (r : Fin 18 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hk : d.reg (r 5)+1 ≤ M) : ∀ j, (coefficientStore r d).reg j ≤ M := by
  have h₁ := convolutionStore_bound_of (leftLayout r) (leftLayout_injective r hr) M hM d hd hk
  have h₂ := convolutionStore_bound_of (rightLayout r) (rightLayout_injective r hr) M hM _ h₁
    (by change (convolutionStore (leftLayout r) d).reg (r 5)+1 ≤ M
        rw [leftStore_fresh r hr _ 5 (by decide) (by decide)]; exact hk)
  exact requireStore_bound _ _ _ M (xorStore_bound _ _ _ _ M hM
    (xorStore_bound _ _ _ _ M hM (testBitStore_bound _ (remainderLayout_injective r hr) _ M hM h₂)))

theorem coefficientStore_tapeData (r : Fin 18 → Fin R) (d : TapeStore R B) :
    tapeData (coefficientStore r d) = tapeData d := by
  simp only [coefficientStore, requireStore_tapeData, xorStore_tapeData,
    testBitStore_tapeData, convolutionStore_tapeData]









theorem xorStore_parity_cast (x unit p : Fin R) (hxu : x ≠ unit) (hxp : x ≠ p) (hup : unit ≠ p)
    (d : TapeStore R B) (hx : d.reg x ≤ 1) (hp : d.reg p ≤ 1) :
    ((xorStore x unit p d).reg p : ZMod 2) = (d.reg p : ZMod 2) + (d.reg x : ZMod 2) := by
  rw [xorStore_parity x unit p hxu hxp hup d hx hp, ZMod.natCast_mod, Nat.cast_add]

theorem coefficientStore_flag (r : Fin 18 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (hf : d.reg (r 6) ≤ 1) :
    (coefficientStore r d).reg (r 6) =
      if CoefficientMatches (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 2))
        (d.reg (r 3)) (d.reg (r 4)) (d.reg (r 5)) then d.reg (r 6) else 0 := by
  let d₁ := convolutionStore (leftLayout r) d
  let d₂ := convolutionStore (rightLayout r) d₁
  let d₃ := testBitStore (remainderLayout r) d₂
  let d₄ := xorStore (r 8) (r 16) (r 7) d₃
  let d₅ := xorStore (r 9) (r 16) (r 7) d₄
  have f₁ (i : Fin 18) (hi : i ≠ 7) (hlt : i < 10) : d₁.reg (r i) = d.reg (r i) :=
    leftStore_fresh r hr d i hi hlt
  have f₂ (i : Fin 18) (hi : i ≠ 8) (hlt : i < 10) : d₂.reg (r i) = d₁.reg (r i) :=
    rightStore_fresh r hr d₁ i hi hlt
  have f₃ (i : Fin 18) (hi : i ≠ 9) (hlt : i < 14) : d₃.reg (r i) = d₂.reg (r i) :=
    remainderStore_fresh r hr d₂ i hi hlt
  have f₄ (i : Fin 18) (hx : i ≠ 8) (hu : i ≠ 16) (hp : i ≠ 7) :
      d₄.reg (r i) = d₃.reg (r i) :=
    xorStore_fresh _ _ _ _ _ (hr.ne hx) (hr.ne hu) (hr.ne hp)
  have f₅ (i : Fin 18) (hx : i ≠ 9) (hu : i ≠ 16) (hp : i ≠ 7) :
      d₅.reg (r i) = d₄.reg (r i) :=
    xorStore_fresh _ _ _ _ _ (hr.ne hx) (hr.ne hu) (hr.ne hp)
  have hp₃ : d₃.reg (r 7) ≤ 1 := by
    rw [f₃ 7 (by decide) (by decide), f₂ 7 (by decide) (by decide)]
    exact convolutionStore_bit (leftLayout r) (leftLayout_injective r hr) d
  have hx₃ : d₃.reg (r 8) ≤ 1 := by
    rw [f₃ 8 (by decide) (by decide)]
    exact convolutionStore_bit (rightLayout r) (rightLayout_injective r hr) d₁
  have hy₃ : d₃.reg (r 9) ≤ 1 := by
    have h := testBitStore_bit (remainderLayout r) (remainderLayout_injective r hr) d₂
    change d₃.reg (r 9) = _ at h
    rw [h]
    split <;> omega
  have hp₄ : d₄.reg (r 7) ≤ 1 := by
    rw [xorStore_parity _ _ _ (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) _ hx₃ hp₃]
    omega
  have hy₄ : d₄.reg (r 9) ≤ 1 := by
    rw [f₄ 9 (by decide) (by decide) (by decide)]; exact hy₃
  have hp₅ : d₅.reg (r 7) ≤ 1 := by
    rw [xorStore_parity _ _ _ (hr.ne (by decide)) (hr.ne (by decide))
      (hr.ne (by decide)) _ hy₄ hp₄]
    omega
  have hflag : d₅.reg (r 6) = d.reg (r 6) := by
    rw [f₅ 6 (by decide) (by decide) (by decide), f₄ 6 (by decide) (by decide) (by decide),
      f₃ 6 (by decide) (by decide), f₂ 6 (by decide) (by decide), f₁ 6 (by decide) (by decide)]
  have hpval : (d₃.reg (r 7) : ZMod 2) = rawConvolution (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 5)) := by
    rw [f₃ 7 (by decide) (by decide), f₂ 7 (by decide) (by decide)]
    exact convolutionStore_parity (leftLayout r) (leftLayout_injective r hr) d
  have hxval : (d₃.reg (r 8) : ZMod 2) = rawConvolution (d.reg (r 3)) (d.reg (r 4)) (d.reg (r 5)) := by
    rw [f₃ 8 (by decide) (by decide)]
    have h := convolutionStore_parity (rightLayout r) (rightLayout_injective r hr) d₁
    change (d₂.reg (r 8) : ZMod 2) = rawConvolution (d₁.reg (r 3)) (d₁.reg (r 4)) (d₁.reg (r 5)) at h
    rw [h, f₁ 3 (by decide) (by decide), f₁ 4 (by decide) (by decide), f₁ 5 (by decide) (by decide)]
  have hyval : (d₃.reg (r 9) : ZMod 2) = bitEquiv (Nat.testBit (d.reg (r 2)) (d.reg (r 5))) := by
    have h := testBitStore_bit (remainderLayout r) (remainderLayout_injective r hr) d₂
    change d₃.reg (r 9) = bitValue (d₂.reg (r 2)) (d₂.reg (r 5)) at h
    rw [h, bitValue_cast, f₂ 2 (by decide) (by decide), f₁ 2 (by decide) (by decide),
      f₂ 5 (by decide) (by decide), f₁ 5 (by decide) (by decide)]
  have hv : (d₅.reg (r 7) : ZMod 2) =
      rawConvolution (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 5)) +
      rawConvolution (d.reg (r 3)) (d.reg (r 4)) (d.reg (r 5)) +
      bitEquiv (Nat.testBit (d.reg (r 2)) (d.reg (r 5))) := by
    rw [xorStore_parity_cast _ _ _ (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
      _ hy₄ hp₄, xorStore_parity_cast _ _ _ (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
      _ hx₃ hp₃, f₄ 9 (by decide) (by decide) (by decide), hpval, hxval, hyval]
  have hz : d₅.reg (r 7) = 0 ↔ CoefficientMatches (d.reg (r 0)) (d.reg (r 1))
      (d.reg (r 2)) (d.reg (r 3)) (d.reg (r 4)) (d.reg (r 5)) := by
    have hc : d₅.reg (r 7) = 0 ↔ (d₅.reg (r 7) : ZMod 2) = 0 := by
      by_cases hh : d₅.reg (r 7) = 0
      · simp [hh]
      · have h1 : d₅.reg (r 7) = 1 := by omega
        simp [h1]
    rw [hc, hv, add_assoc, add_eq_zero_iff_eq_neg, ZMod.neg_eq_self_mod_two]
    change _ = _ ↔ _ = _
    rw [add_comm (rawConvolution (d.reg (r 3)) (d.reg (r 4)) (d.reg (r 5)))]
  change (requireStore (r 7) (r 6) d₅).reg (r 6) = _
  rw [requireStore_flag _ _ (hr.ne (by decide)) _ (by rw [hflag]; exact hf), hflag]
  simp only [hz]

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



















theorem restrict_injective (r : Fin 19 → Fin R) (hr : Function.Injective r) :
    Function.Injective (restrict r) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin 19 => z.val) (hr h)

theorem reg_set19 (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i j : Fin 19) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j; simp
  · simp [TapeStore.setReg, h, hr.ne h]










theorem step_stops (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) (hk : d.reg (r 5)+1 ≤ M) :
    ∃ t e, t ≤ 2200*(M+1)^3+2 ∧
      (step r).Stops inp (d.toCfg (step (B := B) r).entry) t e ∧ e.store = stepStore r d := by
  obtain ⟨t, c, ht, hc, hcs⟩ := coefficient_stops_exact (restrict r)
    (restrict_injective r hr) inp M hM d hd hk
  have hinc := TapeMacros.increment_stops (r 5) inp c.store
  have hall := hc.seq hinc
  refine ⟨_, _, by omega, hall, ?_⟩
  change c.store.setReg (r 5) _ = _
  rw [hcs]
  rfl

theorem stepStore_index (r : Fin 19 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    (stepStore r d).reg (r 5) = d.reg (r 5)+1 := by
  simp only [stepStore, TapeStore.setReg, Function.update_self]
  have h := coefficientStore_fresh (restrict r) (restrict_injective r hr) d 5 (by decide)
  change (coefficientStore (restrict r) d).reg (r 5) = d.reg (r 5) at h
  rw [h]

theorem stepStore_count (r : Fin 19 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    (stepStore r d).reg (r 18) = d.reg (r 18) := by
  unfold stepStore
  simp only [reg_set19 r hr, show (18 : Fin 19) ≠ 5 from by decide, ite_false]
  exact coefficientStore_register _ d _
    (hr.ne (show (18:Fin 19) ≠ 6 from by decide)) (hr.ne (show (18:Fin 19) ≠ 7 from by decide))
    (hr.ne (show (18:Fin 19) ≠ 8 from by decide)) (hr.ne (show (18:Fin 19) ≠ 9 from by decide))
    (hr.ne (show (18:Fin 19) ≠ 10 from by decide)) (hr.ne (show (18:Fin 19) ≠ 11 from by decide))
    (hr.ne (show (18:Fin 19) ≠ 12 from by decide)) (hr.ne (show (18:Fin 19) ≠ 13 from by decide))
    (hr.ne (show (18:Fin 19) ≠ 14 from by decide)) (hr.ne (show (18:Fin 19) ≠ 15 from by decide))
    (hr.ne (show (18:Fin 19) ≠ 16 from by decide)) (hr.ne (show (18:Fin 19) ≠ 17 from by decide))

theorem stepStore_input (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 18) (hi : i < 5) :
    (stepStore r d).reg (restrict r i) = d.reg (restrict r i) := by
  unfold stepStore
  have hne : restrict r i ≠ r 5 := hr.ne (show i.castSucc ≠ (5:Fin 19) from by
    intro h
    have he := congrArg (fun z : Fin 19 => z.val) h
    change i.val = 5 at he
    change i.val < 5 at hi
    omega)
  simp only [TapeStore.setReg, Function.update_of_ne hne]
  exact coefficientStore_fresh (restrict r) (restrict_injective r hr) d i (by omega)

theorem stepStore_flag (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (hf : d.reg (r 6) ≤ 1) :
    (stepStore r d).reg (r 6) =
      if CoefficientMatches (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 2))
        (d.reg (r 3)) (d.reg (r 4)) (d.reg (r 5)) then d.reg (r 6) else 0 := by
  unfold stepStore
  simp only [reg_set19 r hr, show (6:Fin 19) ≠ 5 from by decide, ite_false]
  exact coefficientStore_flag (restrict r) (restrict_injective r hr) d hf

theorem stepStore_bound (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hk : d.reg (r 5)+1 ≤ M) : ∀ j, (stepStore r d).reg j ≤ M := by
  apply setReg_bound _ _ _ M (coefficientStore_bound (restrict r) (restrict_injective r hr) M hM d hd hk)
  have h := coefficientStore_fresh (restrict r) (restrict_injective r hr) d 5 (by decide)
  change (coefficientStore (restrict r) d).reg (r 5) = d.reg (r 5) at h
  rw [h]; exact hk

theorem stepStore_tapeData (r : Fin 19 → Fin R) (d : TapeStore R B) :
    tapeData (stepStore r d) = tapeData d := by
  rw [stepStore, tapeData_setReg, coefficientStore_tapeData]










theorem certificateLoop_stops_exact (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hn : d.reg (r 18) = n) (hd : ∀ j, d.reg j ≤ M) (hk : d.reg (r 5)+n ≤ M) :
    ∃ t, t ≤ n*(2200*(M+1)^3+4)+1 ∧
      (certificateLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 300)) t
        ((certificateStore r n d).toCfg (TapeProgram.loopExit 300)) := by
  induction n generalizing d with
  | zero => exact ⟨1, by omega, TapeProgram.loop_zero (step r) (r 18) inp d hn⟩
  | succ n ih =>
    let d₁ := d.setReg (r 18) n
    have hb₁ : ∀ j, d₁.reg j ≤ M := setReg_bound d _ n M hd (by have := hd (r 18); omega)
    have hk₁ : d₁.reg (r 5)+1 ≤ M := by simp only [d₁, reg_set19 r hr]; simp; omega
    obtain ⟨s, c, hs, hc, hcs⟩ := step_stops r hr inp M hM d₁ hb₁ hk₁
    have hcn : c.reg (r 18) = n := by
      change c.store.reg (r 18) = _
      rw [hcs, stepStore_count r hr]
      simp [d₁]
    have hck : c.reg (r 5) = d.reg (r 5)+1 := by
      change c.store.reg (r 5) = _
      rw [hcs, stepStore_index r hr]
      simp [d₁, reg_set19 r hr]
    have hcb : ∀ j, c.store.reg j ≤ M := by
      rw [hcs]; exact stepStore_bound r hr M hM d₁ hb₁ hk₁
    obtain ⟨t, ht, htail⟩ := ih c.store hcn hcb (by change c.reg (r 5)+n ≤ M; omega)
    have hhead := TapeProgram.loop_positive_header (step r) (r 18) inp d (by omega)
    have hdec : TapeProgram.decStore (r 18) d = d₁ := by
      simp [TapeProgram.decStore, d₁, TapeStore.setReg, hn]
    rw [hdec] at hhead
    have hrun := hc.exec.relabel (TapeProgram.leftLabel 2)
      (TapeProgram.loop_code_body_active (step r) (r 18))
    have hreturn := TapeProgram.loop_body_return (step r) (r 18) inp c hc.halted
    have hpost : certificateStore r n c.store = certificateStore r (n+1) d := by
      rw [certificateStore, hcs]
    have hall := ((hhead.trans hrun).trans hreturn).trans htail.exec
    rw [hpost] at hall
    refine ⟨_, ?_, ⟨hall, TapeProgram.loop_code_exit (step r) (r 18)⟩⟩
    calc
      1+s+1+t ≤ 1+(2200*(M+1)^3+2)+1+(n*(2200*(M+1)^3+4)+1) := by omega
      _ = (n+1)*(2200*(M+1)^3+4)+1 := by ring

theorem certificateStore_tapeData (r : Fin 19 → Fin R) (n : ℕ) (d : TapeStore R B) :
    tapeData (certificateStore r n d) = tapeData d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [certificateStore, ih, stepStore_tapeData, tapeData_setReg]

theorem certificateStore_input (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) (i : Fin 18) (hi : i < 5) :
    (certificateStore r n d).reg (restrict r i) = d.reg (restrict r i) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [certificateStore, ih, stepStore_input r hr _ i hi]
    have hne : restrict r i ≠ r 18 := hr.ne (show i.castSucc ≠ (18:Fin 19) from by
      intro h
      have he := congrArg (fun z : Fin 19 => z.val) h
      change i.val = 18 at he
      have := i.isLt
      omega)
    simp [TapeStore.setReg, hne]






















theorem certificateStore_flag_le (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) (hf : d.reg (r 6) ≤ 1) :
    (certificateStore r n d).reg (r 6) ≤ 1 := by
  induction n generalizing d with
  | zero => exact hf
  | succ n ih =>
    rw [certificateStore]
    apply ih
    rw [stepStore_flag r hr _ (by simpa [reg_set19 r hr] using hf)]
    split <;> simp [reg_set19 r hr] <;> omega

theorem certificateStore_bound (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hd : ∀ j, d.reg j ≤ M) (hk : d.reg (r 5)+n ≤ M) (hn : n ≤ M) :
    ∀ j, (certificateStore r n d).reg j ≤ M := by
  induction n generalizing d with
  | zero => exact hd
  | succ n ih =>
    rw [certificateStore]
    have hb := setReg_bound d (r 18) n M hd (by omega)
    apply ih _ (stepStore_bound r hr M hM _ hb (by simp [reg_set19 r hr]; omega))
    · rw [stepStore_index r hr]
      simp only [reg_set19 r hr, show (5:Fin 19) ≠ 18 from by decide, ite_false]
      omega
    · omega

/-- An accumulator invariant: success exactly means all positions already
visited satisfy the coefficient equation. -/
theorem certificateStore_flag_correct (r : Fin 19 → Fin R) (hr : Function.Injective r)
    (a b rem monic quotient N n : ℕ) (d : TapeStore R B)
    (ha : d.reg (r 0) = a) (hb : d.reg (r 1) = b) (hrm : d.reg (r 2) = rem)
    (hm : d.reg (r 3) = monic) (hs : d.reg (r 4) = quotient)
    (hf : d.reg (r 6) ≤ 1) (hk : d.reg (r 5)+n = N)
    (hInv : d.reg (r 6) = 1 ↔ ∀ j < d.reg (r 5), CoefficientMatches a b rem monic quotient j) :
    (certificateStore r n d).reg (r 6) = 1 ↔
      ∀ j < N, CoefficientMatches a b rem monic quotient j := by
  induction n generalizing d with
  | zero => simpa only [certificateStore, show d.reg (r 5) = N by omega] using hInv
  | succ n ih =>
    let d₁ := d.setReg (r 18) n
    let d₂ := stepStore r d₁
    have hinput (i : Fin 18) (hi : i < 5) : d₂.reg (restrict r i) = d.reg (restrict r i) := by
      rw [stepStore_input r hr _ i hi]
      have hne : restrict r i ≠ r 18 := hr.ne (show i.castSucc ≠ (18:Fin 19) from by
        intro h
        have he := congrArg (fun z : Fin 19 => z.val) h
        change i.val = 18 at he
        have := i.isLt
        omega)
      simp [d₁, TapeStore.setReg, hne]
    have hf₁ : d₁.reg (r 6) = d.reg (r 6) := by simp [d₁, reg_set19 r hr]
    have hk₁ : d₁.reg (r 5) = d.reg (r 5) := by simp [d₁, reg_set19 r hr]
    have hk₂ : d₂.reg (r 5) = d.reg (r 5)+1 := by rw [stepStore_index r hr, hk₁]
    have hflag : d₂.reg (r 6) =
        if CoefficientMatches a b rem monic quotient (d.reg (r 5)) then d.reg (r 6) else 0 := by
      rw [stepStore_flag r hr d₁ (by rw [hf₁]; exact hf)]
      simp only [d₁, reg_set19 r hr]
      simp [ha, hb, hrm, hm, hs]
    have hflag_le : d₂.reg (r 6) ≤ 1 := by rw [hflag]; split <;> omega
    have hnext : d₂.reg (r 6) = 1 ↔
        d.reg (r 6) = 1 ∧ CoefficientMatches a b rem monic quotient (d.reg (r 5)) := by
      rw [hflag]
      by_cases h : CoefficientMatches a b rem monic quotient (d.reg (r 5)) <;> simp [h]
    have hnextInv : d₂.reg (r 6) = 1 ↔
        ∀ j < d₂.reg (r 5), CoefficientMatches a b rem monic quotient j := by
      rw [hnext, hInv, hk₂]
      constructor
      · rintro ⟨hbefore, hcurrent⟩ j hj
        by_cases hj' : j < d.reg (r 5)
        · exact hbefore j hj'
        · have he : j = d.reg (r 5) := by omega
          simpa [he] using hcurrent
      · intro h
        exact ⟨fun j hj => h j (by omega), h (d.reg (r 5)) (by omega)⟩
    rw [certificateStore]
    apply ih d₂ ((hinput 0 (by decide)).trans ha) ((hinput 1 (by decide)).trans hb)
      ((hinput 2 (by decide)).trans hrm) ((hinput 3 (by decide)).trans hm)
      ((hinput 4 (by decide)).trans hs) hflag_le (by omega) hnextInv



















































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




theorem restrict19_injective (r : Fin 20 → Fin R) (hr : Function.Injective r) :
    Function.Injective (restrict19 r) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin 20 => z.val) (hr h)

theorem reg_set20 (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i j : Fin 20) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j; simp
  · simp [TapeStore.setReg, h, hr.ne h]












theorem prepare_stops (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (prepare r).Stops inp (d.toCfg (prepare (B := B) r).entry)
      (d.reg (r 5)+d.reg (r 6)+d.reg (r 18)+d.reg (r 17)+5*d.reg (r 19)+13) e ∧
      e.store = prepareStore r d := by
  have h₁ := TapeMacros.clear_stops (r 5) inp (d.reg (r 5)) d rfl
  have h₂ := TapeMacros.clear_stops (r 6) inp (d.reg (r 6)) (d.setReg (r 5) 0)
    (by simp [reg_set20 r hr])
  have h₃ := TapeMacros.increment_stops (r 6) inp ((d.setReg (r 5) 0).setReg (r 6) 0)
  have hz : ((d.setReg (r 5) 0).setReg (r 6) 0).reg (r 6) = 0 := by simp [TapeStore.setReg]
  rw [hz, zero_add] at h₃
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops (r 19) (r 18) (r 17)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp
    (((d.setReg (r 5) 0).setReg (r 6) 0).setReg (r 6) 1)
  have hall := ((h₁.seq h₂).seq h₃).seq hc
  refine ⟨c.mapPC (TapeProgram.rightLabel 6), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | (simp [reg_set20 r hr]; omega)
  · change c.store = _
    rw [hcs, TapeStore.setReg_same]
    rfl

theorem prepareStore_reg (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 20) :
    (prepareStore r d).reg (r i) =
      if i = 5 then 0 else if i = 6 then 1 else if i = 18 then d.reg (r 19)
      else if i = 17 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [prepareStore, reg_set20 r hr]

theorem prepareStore_bound (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (prepareStore r d).reg j ≤ M := by
  unfold prepareStore
  apply setReg_bound _ _ 0 M _ (by omega)
  apply setReg_bound _ _ _ M
  · exact setReg_bound _ _ 1 M (setReg_bound d _ 0 M hd (by omega)) hM
  · simp only [reg_set20 r hr]
    simpa using hd (r 19)









theorem certificate_stops_exact (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 2300*(M+1)^4 ∧
      (certificate r).Stops inp (d.toCfg (certificate (B := B) r).entry) t e ∧
      e.store = certificateResult r d := by
  obtain ⟨c, hc, hcs⟩ := prepare_stops r hr inp d
  have hcb : ∀ j, c.store.reg j ≤ M := by rw [hcs]; exact prepareStore_bound r hr M hM d hd
  have hcn : c.reg (r 18) = d.reg (r 19) := by
    change c.store.reg (r 18) = _
    rw [hcs, prepareStore_reg r hr]; simp
  have hck : c.reg (r 5) = 0 := by
    change c.store.reg (r 5) = _
    rw [hcs, prepareStore_reg r hr]; simp
  obtain ⟨t, ht, he⟩ := certificateLoop_stops_exact (restrict19 r) (restrict19_injective r hr)
    inp M hM (d.reg (r 19)) c.store hcn hcb (by change c.reg (r 5)+d.reg (r 19) ≤ M; rw [hck]; simpa using hd (r 19))
  have hall := hc.seq he
  refine ⟨_, _, ?_, hall, ?_⟩
  · have hp : d.reg (r 5)+d.reg (r 6)+d.reg (r 18)+d.reg (r 17)+5*d.reg (r 19)+13 ≤ 9*M+13 := by
      have := hd (r 5); have := hd (r 6); have := hd (r 18)
      have := hd (r 17); have := hd (r 19); omega
    have hpow := Nat.le_self_pow (by decide : (4:ℕ) ≠ 0) (M+1)
    have hM4 : M ≤ (M+1)^4 := (by omega : M ≤ M+1).trans hpow
    have h14 : 1 ≤ (M+1)^4 := by omega
    have hmul : 2200*M*(M+1)^3 ≤ 2200*(M+1)^4 := by
      calc
        2200*M*(M+1)^3 ≤ 2200*(M+1)*(M+1)^3 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2200 (by omega : M ≤ M+1))
        _ = 2200*(M+1)^4 := by ring
    have hmul' := Nat.mul_le_mul_right (2200*(M+1)^3+4) (hd (r 19))
    have heq : M*(2200*(M+1)^3+4) = 2200*M*(M+1)^3+4*M := by ring
    rw [heq] at hmul'
    change d.reg (r 5)+d.reg (r 6)+d.reg (r 18)+d.reg (r 17)+5*d.reg (r 19)+13+1+t ≤ _
    omega
  · change certificateStore (restrict19 r) (d.reg (r 19)) c.store = _
    rw [hcs]
    rfl

theorem certificateResult_flag_le (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (certificateResult r d).reg (r 6) ≤ 1 := by
  apply certificateStore_flag_le (restrict19 r) (restrict19_injective r hr)
  change (prepareStore r d).reg (r 6) ≤ 1
  simp [prepareStore_reg r hr]

theorem certificateResult_correct (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) :
    (certificateResult r d).reg (r 6) = 1 ↔ ∀ j < d.reg (r 19),
      CoefficientMatches (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 2))
        (d.reg (r 3)) (d.reg (r 4)) j := by
  apply certificateStore_flag_correct (restrict19 r) (restrict19_injective r hr)
    (d.reg (r 0)) (d.reg (r 1)) (d.reg (r 2)) (d.reg (r 3)) (d.reg (r 4))
    (d.reg (r 19)) (d.reg (r 19)) (prepareStore r d)
  all_goals simp [restrict19, Fin.castSucc, prepareStore, reg_set20 r hr]

theorem certificateResult_tapeData (r : Fin 20 → Fin R) (d : TapeStore R B) :
    tapeData (certificateResult r d) = tapeData d := by
  rw [certificateResult, certificateStore_tapeData]
  rfl

theorem certificateResult_bound (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (certificateResult r d).reg j ≤ M := by
  apply certificateStore_bound (restrict19 r) (restrict19_injective r hr) M hM _ _
    (prepareStore_bound r hr M hM d hd)
  · change (prepareStore r d).reg (r 5)+d.reg (r 19) ≤ M
    simpa [prepareStore_reg r hr] using hd (r 19)
  · exact hd (r 19)

theorem certificateResult_input (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 18) (hi : i < 5) :
    (certificateResult r d).reg (r i.castSucc.castSucc) = d.reg (r i.castSucc.castSucc) := by
  change (certificateStore (restrict19 r) (d.reg (r 19)) (prepareStore r d)).reg
    (restrict (restrict19 r) i) = _
  rw [certificateStore_input (restrict19 r) (restrict19_injective r hr) _ _ i hi]
  fin_cases i <;> simp_all [restrict, restrict19, Fin.castSucc, prepareStore, reg_set20 r hr]

theorem certificateResult_runtimeBound (r : Fin 20 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (certificateResult r d).reg (r 19) = d.reg (r 19) := by
  rw [certificateResult, certificateStore_outside]
  · simp [prepareStore_reg r hr]
  · intro i
    apply hr.ne
    intro h
    have hv := congrArg (fun z : Fin 20 => z.val) h
    change 19 = i.val at hv
    have := i.isLt
    omega































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










theorem onPositive_code_left (P : TapeProgram R B L) (flag : Fin R) (i : Fin L) :
    (onPositive P flag).code (TapeProgram.leftLabel 2 i) =
      (P.code i).relabel (TapeProgram.leftLabel 2) := by
  simp [onPositive, TapeProgram.leftLabel]

theorem onPositive_zero (P : TapeProgram R B L) (flag : Fin R) (inp : Inputs)
    (d : TapeStore R B) (hf : d.reg flag = 0) :
    (onPositive P flag).Stops inp (d.toCfg (TapeProgram.loopHeader L)) 1
      (d.toCfg (TapeProgram.loopExit L)) := by
  constructor
  · apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, onPositive, TapeProgram.loopHeader, TapeProgram.rightLabel]
    · simp [TapeProgram.step, onPositive, TapeProgram.loopHeader, TapeProgram.loopExit,
        TapeProgram.rightLabel, hf]
  · simp [TapeProgram.halted, onPositive, TapeProgram.loopExit, TapeProgram.rightLabel]

theorem onPositive_positive (P : TapeProgram R B L) (flag : Fin R) (inp : Inputs)
    (d : TapeStore R B) (hf : d.reg flag ≠ 0) (t : ℕ) (e : TapeCfg R B L)
    (he : P.Stops inp ((d.setReg flag (d.reg flag-1)).toCfg P.entry) t e) :
    (onPositive P flag).Stops inp (d.toCfg (TapeProgram.loopHeader L)) (1+t)
      (e.mapPC (TapeProgram.leftLabel 2)) := by
  have hhead : (onPositive P flag).Exec inp (d.toCfg (TapeProgram.loopHeader L)) 1
      (((d.setReg flag (d.reg flag-1)).toCfg P.entry).mapPC (TapeProgram.leftLabel 2)) := by
    apply TapeProgram.Exec.one
    · simp [TapeProgram.halted, onPositive, TapeProgram.loopHeader, TapeProgram.rightLabel]
    · simp [TapeProgram.step, onPositive, TapeProgram.loopHeader, TapeProgram.loopExit,
        TapeProgram.rightLabel, hf, TapeStore.setReg]
  constructor
  · exact hhead.trans (he.exec.relabel (TapeProgram.leftLabel 2)
      (fun i _ => onPositive_code_left P flag i))
  · change (onPositive P flag).code (TapeProgram.leftLabel 2 e.pc) = .halt
    rw [onPositive_code_left, he.halted]
    rfl










theorem reg_set (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i j : Fin 5) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j; simp
  · simp [TapeStore.setReg, h, hr.ne h]

theorem commitBody_stops (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (commitBody r).Stops inp (d.toCfg (commitBody (B := B) r).entry)
      (d.reg (r 1)+d.reg (r 2)+5*d.reg (r 0)+d.reg (r 3)+11) e ∧
      e.store = commitBodyStore r d := by
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops (r 0) (r 1) (r 2)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d
  have hcf : c.reg (r 3) = d.reg (r 3) := by
    change c.store.reg (r 3) = _
    rw [hcs]; simp [reg_set r hr]
  have hclear := TapeMacros.clear_stops (r 3) inp (d.reg (r 3)) c.store hcf
  have hinc := TapeMacros.increment_stops (r 3) inp (c.store.setReg (r 3) 0)
  have hz : (c.store.setReg (r 3) 0).reg (r 3) = 0 := by simp [TapeStore.setReg]
  rw [hz, zero_add] at hinc
  have hall := (hc.seq hclear).seq hinc
  refine ⟨((c.store.setReg (r 3) 0).setReg (r 3) 1).toCfg (1:Fin 2) |>.mapPC
    (TapeProgram.rightLabel 13), ?_, ?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change (c.store.setReg (r 3) 0).setReg (r 3) 1 = _
    rw [TapeStore.setReg_same, hcs]
    rfl








theorem commit_stops (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 8*M+12 ∧
      (commit r).Stops inp (d.toCfg (commit (B := B) r).entry) t e ∧
      e.store = commitStore r d := by
  by_cases hf : d.reg (r 4) = 0
  · refine ⟨1, d.toCfg (TapeProgram.loopExit 15), by omega,
      onPositive_zero (commitBody r) (r 4) inp d hf, ?_⟩
    simp [commitStore, hf]
  · obtain ⟨c, hc, hcs⟩ := commitBody_stops r hr inp (d.setReg (r 4) (d.reg (r 4)-1))
    have hall := onPositive_positive (commitBody r) (r 4) inp d hf _ c hc
    refine ⟨_, _, ?_, hall, ?_⟩
    · simp only [reg_set r hr]
      simp
      have := hd (r 0); have := hd (r 1); have := hd (r 2); have := hd (r 3)
      omega
    · change c.store = _
      rw [hcs]
      simp only [commitStore, if_neg hf]






























theorem commitStore_fresh (r : Fin 5 → Fin R) (d : TapeStore R B) (j : Fin R)
    (h₁ : j ≠ r 1) (h₂ : j ≠ r 2) (h₃ : j ≠ r 3) (h₄ : j ≠ r 4) :
    (commitStore r d).reg j = d.reg j := by
  unfold commitStore
  split <;> simp_all [commitBodyStore, TapeStore.setReg]

theorem commitStore_bound (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (commitStore r d).reg j ≤ M := by
  unfold commitStore commitBodyStore
  split
  · exact hd
  · apply setReg_bound _ _ 1 M _ hM
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M
    · exact setReg_bound _ _ _ M hd ((Nat.sub_le _ _).trans (hd (r 4)))
    · simp only [reg_set r hr]
      simpa using hd (r 0)

theorem commitStore_tapeData (r : Fin 5 → Fin R) (d : TapeStore R B) :
    tapeData (commitStore r d) = tapeData d := by
  unfold commitStore
  split <;> rfl

theorem certificateResult_outside (r : Fin 20 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 20, j ≠ r i) :
    (certificateResult r d).reg j = d.reg j := by
  rw [certificateResult, certificateStore_outside]
  · simp [FieldCertificates.prepareStore, TapeStore.setReg, hne 5, hne 6, hne 17, hne 18]
  · intro i
    exact hne i.castSucc








/-- Modular exact loop execution allowing a body temporarily to use its loop
counter, provided that it restores the counter before returning. -/
theorem loop_stops (P : TapeProgram R B L) (counter : Fin R)
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

theorem loopResult_frame (counter : Fin R) (F : TapeStore R B → TapeStore R B)
    (j : Fin R) (hj : j ≠ counter) (hF : ∀ d, (F d).reg j = d.reg j)
    (n : ℕ) (d : TapeStore R B) : (loopResult counter F n d).reg j = d.reg j := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [loopResult, ih, hF]
    simp [TapeStore.setReg, hj]






















theorem loopResult_tapeData (counter : Fin R) (F : TapeStore R B → TapeStore R B)
    (hF : ∀ d, tapeData (F d) = tapeData d) (n : ℕ) (d : TapeStore R B) :
    tapeData (loopResult counter F n d) = tapeData d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [loopResult, ih, hF, tapeData_setReg]

































































































































































































































































































































































































































































































































































































































































































































































































































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







































































































































































































































































































































































































































/-- Generic bounded one-counter source scan with an incrementing candidate. -/
theorem singleLoop_stops (P : TapeProgram R B L) (counter candidate : Fin R) (hne : candidate ≠ counter)
    (F : TapeStore R B → TapeStore R B) (inp : Inputs) (M C : ℕ)
    (hf : ∀ d,(F d).reg counter = d.reg counter)
    (hc : ∀ d,(F d).reg candidate = d.reg candidate+1)
    (hb : ∀ d,(∀ j,d.reg j ≤ M) → d.reg candidate+1 ≤ M → ∀ j,(F d).reg j ≤ M)
    (hs : ∀ d,(∀ j,d.reg j ≤ M) → ∃ t e,t ≤ C ∧ P.Stops inp (d.toCfg P.entry) t e ∧ e.store = F d)
    (n : ℕ) (d : TapeStore R B) (hn : d.reg counter = n) (hd : ∀ j,d.reg j ≤ M) (hi : d.reg candidate+n ≤ M) :
    ∃ t,t ≤ n*(C+2)+1 ∧ (TapeProgram.countedLoop P counter).Stops inp
      (d.toCfg (TapeProgram.loopHeader L)) t ((loopResult counter F n d).toCfg (TapeProgram.loopExit L)) ∧
      (∀ j,(loopResult counter F n d).reg j ≤ M) := by
  let Inv : ℕ → TapeStore R B → Prop := fun n c => (∀ j,c.reg j ≤ M) ∧ c.reg candidate+n ≤ M
  have hbody : ∀ n c,c.reg counter = n+1 → Inv (n+1) c → ∃ t e,t ≤ C ∧
      P.Stops inp ((c.setReg counter n).toCfg P.entry) t e ∧ e.store = F (c.setReg counter n) ∧ Inv n e.store := by
    intro n c hcn hInv
    have hcb := setReg_bound c counter n M hInv.1 (by have := hInv.1 counter;omega)
    have hci : (c.setReg counter n).reg candidate+1 ≤ M := by
      simp only [TapeStore.setReg,Function.update_of_ne hne]
      have := hInv.2;omega
    obtain ⟨t,e,ht,he,hes⟩ := hs _ hcb
    refine ⟨t,e,ht,he,hes,?_⟩
    rw [hes]
    refine ⟨hb _ hcb hci,?_⟩
    rw [hc]
    simp only [TapeStore.setReg,Function.update_of_ne hne]
    have := hInv.2;omega
  obtain ⟨t,ht,he,hInv⟩ := loop_stops P counter F inp C Inv hf hbody n d hn ⟨hd,hi⟩
  exact ⟨t,ht,he,hInv.1⟩

































































































































































































































































































































































































































































































































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

/-! Inlined whole module: ExpandingCodes.Computation.RawIrreducibility -/
section FlattenModule74


set_option autoImplicit false
open scoped BigOperators

namespace ExpandingCodes.Computation.RawIrreducibility
open Polynomial
open ExpandingCodes.PolynomialStretch BinaryPolynomial BinaryField
open FieldConvolution FieldCertificates FieldPrograms




theorem poly_coeff (ell : ℕ) (a : Fin (2^ell)) (j : ℕ) :
    (poly ell a).coeff j = bitEquiv (Nat.testBit a.val j) :=
  (bufferCoefficient_eq (indexEquiv ell a) j).symm.trans (bufferCoefficient_bit ell a j)

theorem poly_zero (ell : ℕ) (a : Fin (2^ell)) (ha : a.val = 0) : poly ell a = 0 := by
  ext j
  simp [poly_coeff,ha,bitEquiv_false]

theorem poly_one (ell : ℕ) (a : Fin (2^ell)) (ha : a.val = 1) : poly ell a = 1 := by
  ext j
  rw [poly_coeff,ha]
  cases j <;> simp [Polynomial.coeff_one,Nat.testBit_succ,bitEquiv_false,bitEquiv_true]

theorem val_one_of_poly_one (ell : ℕ) (a : Fin (2^ell)) (ha : poly ell a = 1) : a.val = 1 := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply bitEquiv.injective
  rw [← poly_coeff,ha]
  cases j <;> simp [Polynomial.coeff_one,Nat.testBit_succ,bitEquiv_false,bitEquiv_true]

theorem poly_isUnit_iff (ell : ℕ) (a : Fin (2^ell)) : IsUnit (poly ell a) ↔ a.val = 1 := by
  constructor
  · intro hu
    obtain ⟨c,hc,hcp⟩ := Polynomial.isUnit_iff.mp hu
    have hc₁ : c = 1 := by
      have hcn : c ≠ 0 := hc.ne_zero
      fin_cases c
      · exact (hcn rfl).elim
      · rfl
    apply val_one_of_poly_one ell a
    rw [← hcp,hc₁]
    simp
  · intro ha
    rw [poly_one ell a ha]
    exact isUnit_one

















theorem factorMatches_iff (ell : ℕ) (hell : 0 < ell) (p a b : Fin (2^ell)) :
    FactorMatches ell p a b ↔ poly ell a * poly ell b = candidate ell p := by
  have hraw (j : ℕ) : CoefficientMatches a.val b.val (2^ell+p.val) 0 0 j ↔
      (poly ell a * poly ell b).coeff j = (candidate ell p).coeff j := by
    have hz : rawConvolution 0 0 j = 0 := by simp [rawConvolution,bitEquiv_false]
    rw [CoefficientMatches,rawConvolution_eq_convolution ell ell a b j,convolution_eq,hz,add_zero,
      ← candidateCoefficient_bit, candidateCoefficient_eq]
    rfl
  constructor
  · intro h
    have ha := natDegree_polynomial_lt hell (indexEquiv ell a)
    have hb := natDegree_polynomial_lt hell (indexEquiv ell b)
    have hl : (poly ell a * poly ell b).natDegree ≤ 3*ell :=
      natDegree_mul_le.trans (by change (polynomial _).natDegree + (polynomial _).natDegree ≤ _; omega)
    have hr : (candidate ell p).natDegree ≤ 3*ell := by rw [candidate_natDegree]; omega
    apply (ext_iff_natDegree_le hl hr).mpr
    intro j hj
    exact (hraw j).mp (h j (by omega))
  · intro h j _
    apply (hraw j).mpr
    rw [h]

theorem factorFree_iff_irreducible (ell : ℕ) (hell : 0 < ell) (p : Fin (2^ell)) :
    FactorFree ell p ↔ Irreducible (candidate ell p) := by
  constructor
  · intro hfree
    refine ⟨fun hu => candidate_ne_one hell p ((candidate_monic ell p).eq_one_of_isUnit hu), ?_⟩
    intro f g hfg
    by_contra hu
    have hf : ¬ IsUnit f := fun h => hu (Or.inl h)
    have hg : ¬ IsUnit g := fun h => hu (Or.inr h)
    have hp0 : candidate ell p ≠ 0 := (candidate_monic ell p).ne_zero
    have hf0 : f ≠ 0 := by intro hh; simp [hh] at hfg; exact hp0 hfg
    have hg0 : g ≠ 0 := by intro hh; simp [hh] at hfg; exact hp0 hfg
    have hfd : 0 < f.natDegree :=
      Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic (candidate_monic ell p) hf ⟨g,hfg⟩
    have hgd : 0 < g.natDegree :=
      Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic (candidate_monic ell p) hg ⟨f,by rw [mul_comm]; exact hfg⟩
    have hsum : f.natDegree+g.natDegree = ell := by
      rw [← natDegree_mul hf0 hg0,← hfg,candidate_natDegree]
    have hflt : f.degree < ell := (natDegree_lt_iff_degree_lt hf0).mp (by omega : f.natDegree < ell)
    have hglt : g.degree < ell := (natDegree_lt_iff_degree_lt hg0).mp (by omega : g.natDegree < ell)
    let a := (indexEquiv ell).symm (fun j : Fin ell => f.coeff j)
    let b := (indexEquiv ell).symm (fun j : Fin ell => g.coeff j)
    have ha : poly ell a = f := by
      rw [poly,show indexEquiv ell a = (fun j : Fin ell => f.coeff j) from Equiv.apply_symm_apply _ _]
      exact polynomial_coefficients f hflt
    have hb : poly ell b = g := by
      rw [poly,show indexEquiv ell b = (fun j : Fin ell => g.coeff j) from Equiv.apply_symm_apply _ _]
      exact polynomial_coefficients g hglt
    have hav : 1 < a.val := by
      have ha₀ : a.val ≠ 0 := by intro he; have hh := poly_zero ell a he; rw [ha] at hh; exact hf0 hh
      have ha₁ : a.val ≠ 1 := by intro he; apply hf; rw [← ha]; exact (poly_isUnit_iff ell a).mpr he
      omega
    have hbv : 1 < b.val := by
      have hb₀ : b.val ≠ 0 := by intro he; have hh := poly_zero ell b he; rw [hb] at hh; exact hg0 hh
      have hb₁ : b.val ≠ 1 := by intro he; apply hg; rw [← hb]; exact (poly_isUnit_iff ell b).mpr he
      omega
    apply hfree a b hav hbv
    apply (factorMatches_iff ell hell p a b).mpr
    rw [ha,hb]
    exact hfg.symm
  · intro hi a b ha hb hm
    have hp := (factorMatches_iff ell hell p a b).mp hm
    rcases hi.isUnit_or_isUnit hp.symm with hu | hu
    · have := (poly_isUnit_iff ell a).mp hu
      omega
    · have := (poly_isUnit_iff ell b).mp hu
      omega

theorem factorFree_iff_canonical (ell : ℕ) (hell : 0 < ell) (p : Fin (2^ell)) :
    FactorFree ell p ↔ BinaryPolynomial.FactorFree ell p :=
  (factorFree_iff_irreducible ell hell p).trans (BinaryPolynomial.factorFree_iff_irreducible hell p).symm

theorem selectedIndex_factorFree (ell : ℕ) (hell : 0 < ell) :
    FactorFree ell (selectedIndex ell hell) :=
  (factorFree_iff_canonical ell hell _).mpr (BinaryPolynomial.selectedIndex_factorFree ell hell)

theorem selectedIndex_le (ell : ℕ) (hell : 0 < ell) (p : Fin (2^ell))
    (hp : FactorFree ell p) : selectedIndex ell hell ≤ p :=
  BinaryPolynomial.selectedIndex_le ell hell p ((factorFree_iff_canonical ell hell p).mp hp)




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








theorem certificateLayout_injective (r : Fin 32 → Fin R) (hr : Function.Injective r) :
    Function.Injective (certificateLayout r) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin 32 => z.val) (hr h)

theorem commitLayout_injective (r : Fin 32 → Fin R) (hr : Function.Injective r) :
    Function.Injective (commitLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [commitLayout]

theorem reg_set (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i j : Fin 32) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j;simp
  · simp [TapeStore.setReg,h,hr.ne h]





theorem decrement_stops (x : Fin R) (inp : Inputs) (d : TapeStore R B) :
    (decrement x).Stops inp (d.toCfg 0) 1 ((d.setReg x (d.reg x-1)).toCfg 1) := by
  constructor
  · apply TapeProgram.Exec.one
    · simp [TapeProgram.halted,decrement]
    · by_cases hx : d.reg x = 0
      · have he : d.setReg x 0 = d := by
          unfold TapeStore.setReg
          rw [← hx]
          simp
        simp [TapeProgram.step,decrement,hx,he]
      · simp [TapeProgram.step,decrement,hx,TapeStore.setReg]
  · simp [TapeProgram.halted,decrement]


theorem subtractTwo_stops (x : Fin R) (inp : Inputs) (d : TapeStore R B) :
    ∃ e,(subtractTwo x).Stops inp (d.toCfg (subtractTwo (B:=B) x).entry) 3 e ∧ e.store = d.setReg x (d.reg x-2) := by
  have h₁ := decrement_stops x inp d
  have h₂ := decrement_stops x inp (d.setReg x (d.reg x-1))
  have hall := h₁.seq h₂
  refine ⟨_,hall,?_⟩
  change (d.setReg x (d.reg x-1)).setReg x _ = _
  simp [TapeStore.setReg_same,TapeStore.setReg,Nat.sub_sub]


theorem setTwo_stops (x : Fin R) (inp : Inputs) (d : TapeStore R B) :
    ∃ e,(setTwo x).Stops inp (d.toCfg (setTwo (B:=B) x).entry) (d.reg x+5) e ∧ e.store = d.setReg x 2 := by
  obtain ⟨c,hc,hcs⟩ := setOne_stops x inp d
  have hi := TapeMacros.increment_stops x inp c.store
  have hall := hc.seq hi
  refine ⟨((c.store.setReg x (c.store.reg x+1)).toCfg (1:Fin 2)).mapPC (TapeProgram.rightLabel 4),?_,?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change c.store.setReg x _ = _
    rw [hcs]
    simp [TapeStore.setReg_same,TapeStore.setReg]

theorem certificate_preserves (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 32) (hi : i < 5 ∨ i = 19 ∨ 20 ≤ i) :
    (certificateResult (certificateLayout r) d).reg (r i) = d.reg (r i) := by
  rcases hi with hi|rfl|hi
  · let j : Fin 18 := ⟨i.val,by change i.val < 5 at hi;omega⟩
    have h := certificateResult_input (certificateLayout r) (certificateLayout_injective r hr) d j (by change i.val < 5;exact hi)
    simpa [certificateLayout,j] using h
  · exact certificateResult_runtimeBound (certificateLayout r) (certificateLayout_injective r hr) d
  · apply certificateResult_outside
    intro j
    apply hr.ne
    intro h
    have hv := congrArg (fun z : Fin 32 => z.val) h
    change i.val = j.val at hv
    change 20 ≤ i.val at hi
    have := j.isLt;omega









theorem factorBodyStore_fresh (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 32) (hi : i < 5 ∨ i = 19 ∨ 20 ≤ i) (h1 : i ≠ 1) (h25 : i ≠ 25) :
    (factorBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold factorBodyStore
  simp only [reg_set r hr,if_neg h1]
  rw [requireStore_fresh _ _ _ _
    (hr.ne (show i ≠ (6:Fin 32) from by rcases hi with h|h|h <;> omega)) (hr.ne h25)]
  exact certificate_preserves r hr d i hi

theorem factorBodyStore_index (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    (factorBodyStore r d).reg (r 1) = d.reg (r 1)+1 := by
  unfold factorBodyStore
  simp only [TapeStore.setReg,Function.update_self]
  rw [requireStore_fresh _ _ _ _ (hr.ne (by decide)) (hr.ne (by decide)),
    certificate_preserves r hr d 1 (Or.inl (by decide))]

theorem factorBodyStore_tapeData (r : Fin 32 → Fin R) (d : TapeStore R B) :
    tapeData (factorBodyStore r d) = tapeData d := by
  rw [factorBodyStore,tapeData_setReg,requireStore_tapeData,certificateResult_tapeData]

theorem factorBodyStore_bound (r : Fin 32 → Fin R) (hr : Function.Injective r) (M : ℕ) (hM : 1 ≤ M)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 1)+1 ≤ M) :
    ∀ j,(factorBodyStore r d).reg j ≤ M := by
  apply setReg_bound _ _ _ M (requireStore_bound _ _ _ M
    (certificateResult_bound _ (certificateLayout_injective r hr) M hM d hd))
  have he := factorBodyStore_index r hr d
  have he' : (requireStore (r 6) (r 25) (certificateResult (certificateLayout r) d)).reg (r 1)+1 = d.reg (r 1)+1 := by
    simpa only [factorBodyStore,TapeStore.setReg,Function.update_self] using he
  rw [he'];exact hc

theorem factorBody_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∃ t e,t ≤ 2400*(M+1)^4 ∧ (factorBody r).Stops inp (d.toCfg (factorBody (B:=B) r).entry) t e ∧ e.store = factorBodyStore r d := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁⟩ := certificate_stops_exact (certificateLayout r) (certificateLayout_injective r hr) inp M hM d hd
  obtain ⟨t₂,ht₂,h₂⟩ := requireZero_stops (r 6) (r 25) (hr.ne (by decide)) inp c₁.store
  have h₃ := TapeMacros.increment_stops (r 1) inp (requireStore (r 6) (r 25) c₁.store)
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_,_,?_,hall,?_⟩
  · have hp := Nat.le_self_pow (by decide : (4:ℕ) ≠ 0) (M+1)
    omega
  · change (requireStore (r 6) (r 25) c₁.store).setReg (r 1) _ = _
    rw [hs₁];rfl




theorem innerLoop_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B) (hn : d.reg (r 30) = n)
    (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 1)+n ≤ M) :
    ∃ t,t ≤ n*(2400*(M+1)^4+2)+1 ∧ (innerLoop r).Stops inp
      (d.toCfg (TapeProgram.loopHeader 324)) t ((innerResult r n d).toCfg (TapeProgram.loopExit 324)) ∧
      (∀ j,(innerResult r n d).reg j ≤ M) :=
  singleLoop_stops (factorBody r) (r 30) (r 1) (hr.ne (by decide)) (factorBodyStore r) inp M _
    (fun c => factorBodyStore_fresh r hr c 30 (Or.inr (Or.inr (by decide))) (by decide) (by decide))
    (factorBodyStore_index r hr) (factorBodyStore_bound r hr M hM) (factorBody_stops r hr inp M hM) n d hn hd hc

theorem innerResult_frame (r : Fin 32 → Fin R) (hr : Function.Injective r) (n : ℕ) (d : TapeStore R B)
    (i : Fin 32) (hi : i < 5 ∨ i = 19 ∨ 20 ≤ i) (h1 : i ≠ 1) (h25 : i ≠ 25) (h30 : i ≠ 30) :
    (innerResult r n d).reg (r i) = d.reg (r i) :=
  loopResult_frame (r 30) (factorBodyStore r) (r i) (hr.ne h30)
    (fun c => factorBodyStore_fresh r hr c i hi h1 h25) n d

theorem innerResult_bound (r : Fin 32 → Fin R) (hr : Function.Injective r) (M : ℕ) (hM : 1 ≤ M)
    (n : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 1)+n ≤ M) :
    ∀ j,(innerResult r n d).reg j ≤ M := by
  induction n generalizing d with
  | zero => exact hd
  | succ n ih =>
    change ∀ j,(innerResult r n (factorBodyStore r (d.setReg (r 30) n))).reg j ≤ M
    have hb := setReg_bound d (r 30) n M hd (by omega)
    apply ih _ (factorBodyStore_bound r hr M hM _ hb (by simp [reg_set r hr];omega))
    rw [factorBodyStore_index r hr]
    simp only [reg_set r hr,show (1:Fin 32) ≠ 30 from by decide,ite_false]
    omega

theorem innerResult_tapeData (r : Fin 32 → Fin R) (n : ℕ) (d : TapeStore R B) :
    tapeData (innerResult r n d) = tapeData d :=
  loopResult_tapeData (r 30) (factorBodyStore r) (factorBodyStore_tapeData r) n d







theorem innerPrepare_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs) (d : TapeStore R B) :
    ∃ e,(innerPrepare r).Stops inp (d.toCfg (innerPrepare (B:=B) r).entry)
      (d.reg (r 1)+d.reg (r 30)+d.reg (r 28)+5*d.reg (r 24)+13) e ∧ e.store = innerPrepareStore r d := by
  obtain ⟨c,hc,hcs⟩ := setTwo_stops (r 1) inp d
  obtain ⟨e,he,hes⟩ := TapeMacros.copy_stops (r 24) (r 30) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c.store
  have hcreg (i : Fin 32) (hi : i ≠ 1) : c.store.reg (r i) = d.reg (r i) := by
    rw [hcs];simp [reg_set r hr,hi]
  have h30 := hcreg 30 (by decide)
  have h28 := hcreg 28 (by decide)
  have h24 := hcreg 24 (by decide)
  have hall := hc.seq he
  refine ⟨e.mapPC (TapeProgram.rightLabel 6),?_,?_⟩
  · convert hall using 1 <;> first | rfl | omega
  · change e.store = _
    rw [hes,hcs];rfl

theorem innerPrepareStore_reg (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i : Fin 32) :
    (innerPrepareStore r d).reg (r i) = if i = 28 then 0 else if i = 30 then d.reg (r 24)
      else if i = 1 then 2 else d.reg (r i) := by
  fin_cases i <;> simp [innerPrepareStore,reg_set r hr]

theorem innerPrepareStore_bound (r : Fin 32 → Fin R) (hr : Function.Injective r) (M : ℕ) (hM : 2 ≤ M)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) : ∀ j,(innerPrepareStore r d).reg j ≤ M := by
  unfold innerPrepareStore
  apply setReg_bound _ _ 0 M _ (by omega)
  apply setReg_bound _ _ _ M
  · exact setReg_bound d _ 2 M hd hM
  · simpa [reg_set r hr] using hd (r 24)







theorem outerBodyStore_index (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    (outerBodyStore r d).reg (r 0) = d.reg (r 0)+1 := by
  unfold outerBodyStore
  simp only [TapeStore.setReg,Function.update_self]
  rw [innerResult_frame r hr _ _ 0 (Or.inl (by decide)) (by decide) (by decide) (by decide),innerPrepareStore_reg r hr]
  simp

theorem outerBodyStore_fresh (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 32) (hi : i < 5 ∨ i = 19 ∨ 20 ≤ i)
    (h0 : i ≠ 0) (h1 : i ≠ 1) (h25 : i ≠ 25) (h28 : i ≠ 28) (h30 : i ≠ 30) :
    (outerBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold outerBodyStore
  simp only [reg_set r hr,if_neg h0]
  rw [innerResult_frame r hr _ _ i hi h1 h25 h30,innerPrepareStore_reg r hr]
  simp [h28,h30,h1]

theorem outerBodyStore_bound (r : Fin 32 → Fin R) (hr : Function.Injective r) (M : ℕ) (hM : 2 ≤ M)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hQ : 2+d.reg (r 24) ≤ M) (hc : d.reg (r 0)+1 ≤ M) :
    ∀ j,(outerBodyStore r d).reg j ≤ M := by
  have hb := innerResult_bound r hr M (by omega) (d.reg (r 24)) (innerPrepareStore r d)
    (innerPrepareStore_bound r hr M hM d hd) (by simpa [innerPrepareStore_reg r hr] using hQ)
  apply setReg_bound _ _ _ M hb
  have he := outerBodyStore_index r hr d
  have he' : (innerResult r (d.reg (r 24)) (innerPrepareStore r d)).reg (r 0)+1 = d.reg (r 0)+1 := by
    simpa only [outerBodyStore,TapeStore.setReg,Function.update_self] using he
  rw [he'];exact hc

theorem outerBodyStore_tapeData (r : Fin 32 → Fin R) (d : TapeStore R B) :
    tapeData (outerBodyStore r d) = tapeData d := by
  rw [outerBodyStore,tapeData_setReg,innerResult_tapeData]
  rfl

theorem outerBody_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 2 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hQ : 2+d.reg (r 24) ≤ M) :
    ∃ t e,t ≤ 2500*(M+1)^5 ∧ (outerBody r).Stops inp (d.toCfg (outerBody (B:=B) r).entry) t e ∧ e.store = outerBodyStore r d := by
  obtain ⟨c₁,h₁,hs₁⟩ := innerPrepare_stops r hr inp d
  have hb₁ : ∀ j,c₁.store.reg j ≤ M := by rw [hs₁];exact innerPrepareStore_bound r hr M hM d hd
  have hn : c₁.reg (r 30) = d.reg (r 24) := by change c₁.store.reg (r 30) = _;rw [hs₁,innerPrepareStore_reg r hr];simp
  have hc : c₁.reg (r 1) = 2 := by change c₁.store.reg (r 1) = _;rw [hs₁,innerPrepareStore_reg r hr];simp
  obtain ⟨t,ht,h₂,_⟩ := innerLoop_stops r hr inp M (by omega) (d.reg (r 24)) c₁.store hn hb₁
    (by change c₁.reg (r 1)+d.reg (r 24) ≤ M;rw [hc];exact hQ)
  have h₃ := TapeMacros.increment_stops (r 0) inp (innerResult r (d.reg (r 24)) c₁.store)
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_,_,?_,hall,?_⟩
  · have hp : d.reg (r 1)+d.reg (r 30)+d.reg (r 28)+5*d.reg (r 24)+13 ≤ 8*M+13 := by
      have := hd (r 1);have := hd (r 30);have := hd (r 28);have := hd (r 24);omega
    have hpow := Nat.le_self_pow (by decide : (5:ℕ) ≠ 0) (M+1)
    have hM5 : M ≤ (M+1)^5 := (by omega : M ≤ M+1).trans hpow
    have h15 : 1 ≤ (M+1)^5 := by omega
    have hm : 2400*M*(M+1)^4 ≤ 2400*(M+1)^5 := by
      calc
        2400*M*(M+1)^4 ≤ 2400*(M+1)*(M+1)^4 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega : M ≤ M+1))
        _ = 2400*(M+1)^5 := by ring
    have ht' := Nat.mul_le_mul_right (2400*(M+1)^4+2) (hd (r 24))
    have heq : M*(2400*(M+1)^4+2) = 2400*M*(M+1)^4+2*M := by ring
    rw [heq] at ht'
    omega
  · change (innerResult r (d.reg (r 24)) c₁.store).setReg (r 0) _ = _
    rw [hs₁];rfl




theorem outerLoop_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 2 ≤ M) (n : ℕ) (d : TapeStore R B) (hn : d.reg (r 26) = n)
    (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 0)+n ≤ M) (hQ : 2+d.reg (r 24) ≤ M) :
    ∃ t,t ≤ n*(2500*(M+1)^5+2)+1 ∧ (outerLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 345)) t
      ((outerResult r n d).toCfg (TapeProgram.loopExit 345)) ∧ (∀ j,(outerResult r n d).reg j ≤ M) := by
  let Inv : ℕ → TapeStore R B → Prop := fun n c => (∀ j,c.reg j ≤ M) ∧ c.reg (r 0)+n ≤ M ∧ 2+c.reg (r 24) ≤ M
  have hf (c : TapeStore R B) : (outerBodyStore r c).reg (r 26) = c.reg (r 26) :=
    outerBodyStore_fresh r hr c 26 (Or.inr (Or.inr (by decide))) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hb : ∀ n c,c.reg (r 26) = n+1 → Inv (n+1) c → ∃ t e,t ≤ 2500*(M+1)^5 ∧
      (outerBody r).Stops inp ((c.setReg (r 26) n).toCfg (outerBody (B:=B) r).entry) t e ∧
      e.store = outerBodyStore r (c.setReg (r 26) n) ∧ Inv n e.store := by
    intro n c hcn hi
    have hcb := setReg_bound c (r 26) n M hi.1 (by have := hi.1 (r 26);omega)
    have hQ' : 2+(c.setReg (r 26) n).reg (r 24) ≤ M := by simpa [reg_set r hr] using hi.2.2
    have hci : (c.setReg (r 26) n).reg (r 0)+1 ≤ M := by simp [reg_set r hr];have := hi.2.1;omega
    obtain ⟨t,e,ht,he,hs⟩ := outerBody_stops r hr inp M hM _ hcb hQ'
    refine ⟨t,e,ht,he,hs,?_⟩
    rw [hs]
    refine ⟨outerBodyStore_bound r hr M hM _ hcb hQ' hci,?_,?_⟩
    · rw [outerBodyStore_index r hr]
      simp only [reg_set r hr,show (0:Fin 32) ≠ 26 from by decide,ite_false]
      have := hi.2.1;omega
    · rw [outerBodyStore_fresh r hr _ 24 (Or.inr (Or.inr (by decide))) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hQ'
  obtain ⟨t,ht,he,hi⟩ := loop_stops (outerBody r) (r 26) (outerBodyStore r) inp (2500*(M+1)^5) Inv hf hb n d hn ⟨hd,hc,hQ⟩
  exact ⟨t,ht,he,hi.1⟩

theorem outerResult_frame (r : Fin 32 → Fin R) (hr : Function.Injective r) (n : ℕ) (d : TapeStore R B)
    (i : Fin 32) (hi : i < 5 ∨ i = 19 ∨ 20 ≤ i)
    (h0 : i ≠ 0) (h1 : i ≠ 1) (h25 : i ≠ 25) (h26 : i ≠ 26) (h28 : i ≠ 28) (h30 : i ≠ 30) :
    (outerResult r n d).reg (r i) = d.reg (r i) :=
  loopResult_frame (r 26) (outerBodyStore r) (r i) (hr.ne h26)
    (fun c => outerBodyStore_fresh r hr c i hi h0 h1 h25 h28 h30) n d

theorem outerResult_tapeData (r : Fin 32 → Fin R) (n : ℕ) (d : TapeStore R B) :
    tapeData (outerResult r n d) = tapeData d :=
  loopResult_tapeData (r 26) (outerBodyStore r) (outerBodyStore_tapeData r) n d












theorem candidatePrepare_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 2 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M)
    (hsum : d.reg (r 23)+d.reg (r 31) ≤ M) :
    ∃ t e,t ≤ 100*M+100 ∧ (candidatePrepare r).Stops inp (d.toCfg (candidatePrepare (B:=B) r).entry) t e ∧
      e.store = candidatePrepareStore r d ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨c₁,h₁,hs₁⟩ := TapeMacros.copy_stops (r 23) (r 2) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d
  have hb₁ : ∀ j,c₁.store.reg j ≤ M := by
    rw [hs₁]
    exact setReg_bound _ _ 0 M (setReg_bound d _ _ M hd (hd (r 23))) (by omega)
  obtain ⟨c₂,h₂,hs₂⟩ := TapeMacros.addPreserving_stops (r 31) (r 2) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₁.store
  have hsum₁ : c₁.reg (r 2)+c₁.reg (r 31) ≤ M := by
    change c₁.store.reg (r 2)+c₁.store.reg (r 31) ≤ M
    rw [hs₁];simpa [reg_set r hr] using hsum
  have hb₂ : ∀ j,c₂.store.reg j ≤ M := by
    rw [hs₂]
    exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hb₁ hsum₁) (by omega)
  have h₃ := TapeMacros.clear_stops (r 3) inp (c₂.reg (r 3)) c₂.store rfl
  let c₃ := c₂.store.setReg (r 3) 0
  have hb₃ : ∀ j,c₃.reg j ≤ M := setReg_bound _ _ 0 M hb₂ (by omega)
  have h₄ := TapeMacros.clear_stops (r 4) inp (c₂.reg (r 4)) c₃ (by simp [c₃,reg_set r hr])
  let c₄ := c₃.setReg (r 4) 0
  have hb₄ : ∀ j,c₄.reg j ≤ M := setReg_bound _ _ 0 M hb₃ (by omega)
  obtain ⟨c₅,h₅,hs₅⟩ := setTwo_stops (r 0) inp c₄
  have hb₅ : ∀ j,c₅.store.reg j ≤ M := by rw [hs₅];exact setReg_bound _ _ 2 M hb₄ hM
  obtain ⟨c₆,h₆,hs₆⟩ := setOne_stops (r 25) inp c₅.store
  have hb₆ : ∀ j,c₆.store.reg j ≤ M := by rw [hs₆];exact setReg_bound _ _ 1 M hb₅ (by omega)
  obtain ⟨c₇,h₇,hs₇⟩ := TapeMacros.copy_stops (r 24) (r 26) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₆.store
  have hb₇ : ∀ j,c₇.store.reg j ≤ M := by
    rw [hs₇]
    exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hb₆ (hb₆ (r 24))) (by omega)
  have hall := (((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆).seq h₇
  refine ⟨_,_,?_,hall,?_,hb₇⟩
  · have hc₂3 : c₂.reg (r 3) ≤ M := hb₂ (r 3)
    have hc₂4 : c₂.reg (r 4) ≤ M := hb₂ (r 4)
    have := hd (r 2);have := hd (r 28);have := hd (r 23)
    have := hb₁ (r 28);have := hb₁ (r 31);have := hb₂ (r 3);have := hb₂ (r 4)
    have := hb₄ (r 0);have := hb₅ (r 25);have := hb₆ (r 26);have := hb₆ (r 28);have := hb₆ (r 24)
    omega
  · change c₇.store = _
    rw [hs₇,hs₆,hs₅]
    simp only [c₄,c₃]
    rw [hs₂,hs₁]
    rfl

theorem candidatePrepareStore_reg (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i : Fin 32) :
    (candidatePrepareStore r d).reg (r i) = if i = 2 then d.reg (r 23)+d.reg (r 31)
      else if i = 28 ∨ i = 3 ∨ i = 4 then 0 else if i = 0 then 2 else if i = 25 then 1
      else if i = 26 then d.reg (r 24) else d.reg (r i) := by
  fin_cases i <;> simp [candidatePrepareStore,reg_set r hr]






theorem candidateBodyStore_fresh (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 32) (hi : i = 19 ∨ i = 23 ∨ i = 24 ∨ i = 31) :
    (candidateBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold candidateBodyStore
  rw [commitStore_fresh _ _ _
    (hr.ne (show i ≠ (27:Fin 32) from by rcases hi with h|h|h|h <;> omega))
    (hr.ne (show i ≠ (28:Fin 32) from by rcases hi with h|h|h|h <;> omega))
    (hr.ne (show i ≠ (29:Fin 32) from by rcases hi with h|h|h|h <;> omega))
    (hr.ne (show i ≠ (25:Fin 32) from by rcases hi with h|h|h|h <;> omega)),
    outerResult_frame r hr _ _ i (by rcases hi with h|h|h|h <;> simp_all)
      (by rcases hi with h|h|h|h <;> omega) (by rcases hi with h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h <;> omega) (by rcases hi with h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h <;> omega) (by rcases hi with h|h|h|h <;> omega),
    candidatePrepareStore_reg r hr]
  rcases hi with rfl|rfl|rfl|rfl <;> simp

theorem candidateBody_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 2 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M)
    (hQ : 2+d.reg (r 24) ≤ M) (hsum : d.reg (r 23)+d.reg (r 31) ≤ M) :
    ∃ t e,t ≤ 10000*(M+1)^6 ∧ (candidateBody r).Stops inp (d.toCfg (candidateBody (B:=B) r).entry) t e ∧
      e.store = candidateBodyStore r d ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := candidatePrepare_stops r hr inp M hM d hd hsum
  have hn : c₁.reg (r 26) = d.reg (r 24) := by change c₁.store.reg (r 26) = _;rw [hs₁,candidatePrepareStore_reg r hr];simp
  have hc : c₁.reg (r 0) = 2 := by change c₁.store.reg (r 0) = _;rw [hs₁,candidatePrepareStore_reg r hr];simp
  have hQ₁ : 2+c₁.reg (r 24) ≤ M := by change 2+c₁.store.reg (r 24) ≤ M;rw [hs₁,candidatePrepareStore_reg r hr];simpa using hQ
  obtain ⟨t₂,ht₂,h₂,hb₂⟩ := outerLoop_stops r hr inp M hM (d.reg (r 24)) c₁.store hn hb₁
    (by change c₁.reg (r 0)+d.reg (r 24) ≤ M;rw [hc];exact hQ) hQ₁
  obtain ⟨t₃,c₃,ht₃,h₃,hs₃⟩ := commit_stops (commitLayout r) (commitLayout_injective r hr) inp M
    (outerResult r (d.reg (r 24)) c₁.store) hb₂
  have hb₃ : ∀ j,c₃.store.reg j ≤ M := by
    rw [hs₃];exact commitStore_bound _ (commitLayout_injective r hr) M (by omega) _ hb₂
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_,_,?_,hall,?_,hb₃⟩
  · have hpow := Nat.le_self_pow (by decide : (6:ℕ) ≠ 0) (M+1)
    have hM6 : M ≤ (M+1)^6 := (by omega : M ≤ M+1).trans hpow
    have h16 : 1 ≤ (M+1)^6 := by omega
    have hm : 2500*M*(M+1)^5 ≤ 2500*(M+1)^6 := by
      calc
        2500*M*(M+1)^5 ≤ 2500*(M+1)*(M+1)^5 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega : M ≤ M+1))
        _ = 2500*(M+1)^6 := by ring
    have ht' := Nat.mul_le_mul_right (2500*(M+1)^5+2) (hd (r 24))
    have heq : M*(2500*(M+1)^5+2) = 2500*M*(M+1)^5+2*M := by ring
    rw [heq] at ht'
    omega
  · change c₃.store = _
    rw [hs₃,hs₁];rfl




theorem candidateLoop_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 2 ≤ M) (n : ℕ) (d : TapeStore R B) (hn : d.reg (r 31) = n)
    (hd : ∀ j,d.reg j ≤ M) (hQ : 2+d.reg (r 24) ≤ M) (hq : 2*d.reg (r 23) ≤ M) (hnq : n ≤ d.reg (r 23)) :
    ∃ t,t ≤ n*(10000*(M+1)^6+2)+1 ∧ (candidateLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 409)) t
      ((candidateResult r n d).toCfg (TapeProgram.loopExit 409)) ∧ (∀ j,(candidateResult r n d).reg j ≤ M) := by
  let Inv : ℕ → TapeStore R B → Prop := fun n c =>
    (∀ j,c.reg j ≤ M) ∧ 2+c.reg (r 24) ≤ M ∧ 2*c.reg (r 23) ≤ M ∧ n ≤ c.reg (r 23)
  have hf (c : TapeStore R B) : (candidateBodyStore r c).reg (r 31) = c.reg (r 31) :=
    candidateBodyStore_fresh r hr c 31 (Or.inr (Or.inr (Or.inr rfl)))
  have hb : ∀ n c,c.reg (r 31) = n+1 → Inv (n+1) c → ∃ t e,t ≤ 10000*(M+1)^6 ∧
      (candidateBody r).Stops inp ((c.setReg (r 31) n).toCfg (candidateBody (B:=B) r).entry) t e ∧
      e.store = candidateBodyStore r (c.setReg (r 31) n) ∧ Inv n e.store := by
    intro n c hcn hi
    have hcb := setReg_bound c (r 31) n M hi.1 (by have := hi.1 (r 31);omega)
    have hQ' : 2+(c.setReg (r 31) n).reg (r 24) ≤ M := by simpa [reg_set r hr] using hi.2.1
    have hsum : (c.setReg (r 31) n).reg (r 23)+(c.setReg (r 31) n).reg (r 31) ≤ M := by
      simp [reg_set r hr]
      have := hi.2.2.1;have := hi.2.2.2;omega
    obtain ⟨t,e,ht,he,hs,hbound⟩ := candidateBody_stops r hr inp M hM _ hcb hQ' hsum
    refine ⟨t,e,ht,he,hs,hbound,?_,?_,?_⟩
    · rw [hs,candidateBodyStore_fresh r hr _ 24 (Or.inr (Or.inr (Or.inl rfl)))]
      exact hQ'
    · rw [hs,candidateBodyStore_fresh r hr _ 23 (Or.inr (Or.inl rfl))]
      simpa [reg_set r hr] using hi.2.2.1
    · rw [hs,candidateBodyStore_fresh r hr _ 23 (Or.inr (Or.inl rfl))]
      simp only [reg_set r hr,show (23:Fin 32) ≠ 31 from by decide,ite_false]
      have := hi.2.2.2;omega
  obtain ⟨t,ht,he,hi⟩ := loop_stops (candidateBody r) (r 31) (candidateBodyStore r) inp (10000*(M+1)^6)
    Inv hf hb n d hn ⟨hd,hQ,hq,hnq⟩
  exact ⟨t,ht,he,hi.1⟩











theorem prepare_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∃ t e,t ≤ 20*M+30 ∧ (prepare r).Stops inp (d.toCfg (prepare (B:=B) r).entry) t e ∧
      e.store = prepareStore r d ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨c₁,h₁,hs₁⟩ := TapeMacros.copy_stops (r 23) (r 24) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d
  have hb₁ : ∀ j,c₁.store.reg j ≤ M := by
    rw [hs₁];exact setReg_bound _ _ 0 M (setReg_bound d _ _ M hd (hd (r 23))) (by omega)
  obtain ⟨c₂,h₂,hs₂⟩ := subtractTwo_stops (r 24) inp c₁.store
  have hb₂ : ∀ j,c₂.store.reg j ≤ M := by rw [hs₂];exact setReg_bound _ _ _ M hb₁ ((Nat.sub_le _ _).trans (hb₁ (r 24)))
  obtain ⟨c₃,h₃,hs₃⟩ := TapeMacros.copy_stops (r 23) (r 31) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₂.store
  have hb₃ : ∀ j,c₃.store.reg j ≤ M := by
    rw [hs₃];exact setReg_bound _ _ 0 M (setReg_bound _ _ _ M hb₂ (hb₂ (r 23))) (by omega)
  have h₄ := TapeMacros.clear_stops (r 27) inp (c₃.reg (r 27)) c₃.store rfl
  let c₄ := c₃.store.setReg (r 27) 0
  have hb₄ : ∀ j,c₄.reg j ≤ M := setReg_bound _ _ 0 M hb₃ (by omega)
  have h₅ := TapeMacros.clear_stops (r 29) inp (c₃.reg (r 29)) c₄ (by simp [c₄,reg_set r hr])
  have hall := (((h₁.seq h₂).seq h₃).seq h₄).seq h₅
  refine ⟨_,_,?_,hall,?_,setReg_bound _ _ 0 M hb₄ (by omega)⟩
  · have hc₃27 : c₃.reg (r 27) ≤ M := hb₃ (r 27)
    have hc₃29 : c₃.reg (r 29) ≤ M := hb₃ (r 29)
    have := hd (r 24);have := hd (r 28);have := hd (r 23)
    have := hb₂ (r 31);have := hb₂ (r 28);have := hb₂ (r 23)
    have := hb₃ (r 27);have := hb₃ (r 29);omega
  · change (c₃.store.setReg (r 27) 0).setReg (r 29) 0 = _
    rw [hs₃,hs₂,hs₁];rfl

theorem prepareStore_reg (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i : Fin 32) :
    (prepareStore r d).reg (r i) = if i = 29 ∨ i = 27 ∨ i = 28 then 0
      else if i = 24 then d.reg (r 23)-2 else if i = 31 then d.reg (r 23) else d.reg (r i) := by
  fin_cases i <;> simp [prepareStore,reg_set r hr]







theorem construct_stops_exact (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hq : 2 ≤ d.reg (r 23)) (h2q : 2*d.reg (r 23) ≤ M) :
    ∃ t e,t ≤ 30000*(M+1)^7 ∧ (construct r).Stops inp (d.toCfg (construct (B:=B) r).entry) t e ∧
      e.store = constructResult r d ∧ (∀ j,e.reg j ≤ M) := by
  have hM : 2 ≤ M := by omega
  obtain ⟨t₁,c,ht₁,hc,hcs,hbound⟩ := prepare_stops r hr inp M d hd
  have hn : c.reg (r 31) = d.reg (r 23) := by change c.store.reg (r 31) = _;rw [hcs,prepareStore_reg r hr];simp
  have hQ : 2+c.reg (r 24) ≤ M := by
    change 2+c.store.reg (r 24) ≤ M
    rw [hcs,prepareStore_reg r hr]
    simp
    have := hd (r 23);omega
  have hq' : c.reg (r 23) = d.reg (r 23) := by change c.store.reg (r 23) = _;rw [hcs,prepareStore_reg r hr];simp
  obtain ⟨t₂,ht₂,h₂,hb₂⟩ := candidateLoop_stops r hr inp M hM (d.reg (r 23)) c.store hn hbound hQ
    (by change 2*c.reg (r 23) ≤ M;rw [hq'];exact h2q) (by change d.reg (r 23) ≤ c.reg (r 23);omega)
  have hall := hc.seq h₂
  refine ⟨_,_,?_,hall,?_,hb₂⟩
  · have hpow := Nat.le_self_pow (by decide : (7:ℕ) ≠ 0) (M+1)
    have hM7 : M ≤ (M+1)^7 := (by omega : M ≤ M+1).trans hpow
    have h17 : 1 ≤ (M+1)^7 := by omega
    have hm : 10000*M*(M+1)^6 ≤ 10000*(M+1)^7 := by
      calc
        10000*M*(M+1)^6 ≤ 10000*(M+1)*(M+1)^6 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega : M ≤ M+1))
        _ = 10000*(M+1)^7 := by ring
    have ht' := Nat.mul_le_mul_right (10000*(M+1)^6+2) (hd (r 23))
    have heq : M*(10000*(M+1)^6+2) = 10000*M*(M+1)^6+2*M := by ring
    rw [heq] at ht'
    omega
  · change candidateResult r (d.reg (r 23)) c.store = _
    rw [hcs];rfl







theorem factorSetup_setReg (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target n : ℕ)
    (d : TapeStore R B) (i : Fin 32) (h2 : i ≠ 2) (h3 : i ≠ 3) (h4 : i ≠ 4) (h19 : i ≠ 19)
    (hs : FactorSetup r N target d) : FactorSetup r N target (d.setReg (r i) n) := by
  simpa [FactorSetup,reg_set r hr,Ne.symm h2,Ne.symm h3,Ne.symm h4,Ne.symm h19] using hs

theorem factorBodyStore_setup (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) : FactorSetup r N target (factorBodyStore r d) := by
  rcases hs with ⟨h2,h3,h4,h19⟩
  exact ⟨(factorBodyStore_fresh r hr d 2 (Or.inl (by decide)) (by decide) (by decide)).trans h2,
    (factorBodyStore_fresh r hr d 3 (Or.inl (by decide)) (by decide) (by decide)).trans h3,
    (factorBodyStore_fresh r hr d 4 (Or.inl (by decide)) (by decide) (by decide)).trans h4,
    (factorBodyStore_fresh r hr d 19 (Or.inr (Or.inl rfl)) (by decide) (by decide)).trans h19⟩

theorem factorBodyStore_valid (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) (hv : d.reg (r 25) ≤ 1) :
    (factorBodyStore r d).reg (r 25) =
      if FactorTest N target (d.reg (r 0)) (d.reg (r 1)) then 0 else d.reg (r 25) := by
  let c := certificateResult (certificateLayout r) d
  have hflag : c.reg (r 6) ≤ 1 := certificateResult_flag_le _ (certificateLayout_injective r hr) d
  have hsuccess : c.reg (r 6) = 1 ↔ FactorTest N target (d.reg (r 0)) (d.reg (r 1)) := by
    have h := certificateResult_correct (certificateLayout r) (certificateLayout_injective r hr) d
    rcases hs with ⟨h2,h3,h4,h19⟩
    change c.reg (r 6) = 1 ↔ ∀ j < d.reg (r 19),CoefficientMatches (d.reg (r 0)) (d.reg (r 1))
      (d.reg (r 2)) (d.reg (r 3)) (d.reg (r 4)) j at h
    simpa only [h2,h3,h4,h19,FactorTest] using h
  have hvalid : c.reg (r 25) = d.reg (r 25) := certificate_preserves r hr d 25 (Or.inr (Or.inr (by decide)))
  change ((requireStore (r 6) (r 25) c).setReg (r 1) _).reg (r 25) = _
  rw [reg_set r hr]
  simp only [show (25:Fin 32) ≠ 1 from by decide,ite_false]
  rw [requireStore_flag _ _ (hr.ne (by decide)) c (by rw [hvalid];exact hv),hvalid]
  by_cases ht : FactorTest N target (d.reg (r 0)) (d.reg (r 1))
  · have hf := hsuccess.mpr ht
    simp [ht,hf]
  · have hf : c.reg (r 6) = 0 := by
      have hn : c.reg (r 6) ≠ 1 := fun h => ht (hsuccess.mp h)
      omega
    simp [ht,hf]

theorem forall_lt_succ_shift (P : ℕ → Prop) (n start : ℕ) :
    (P start ∧ ∀ i < n,P (start+1+i)) ↔ ∀ i < n+1,P (start+i) := by
  constructor
  · rintro ⟨h0,ht⟩ i hi
    by_cases hz : i = 0
    · subst i;simpa using h0
    · have h := ht (i-1) (by omega)
      have he : start+1+(i-1) = start+i := by omega
      simpa only [he] using h
  · intro h
    refine ⟨by simpa using h 0 (by omega),?_⟩
    intro i hi
    have he : start+(i+1) = start+1+i := by omega
    simpa only [he] using h (i+1) (by omega)

theorem innerResult_setup (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target n : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) : FactorSetup r N target (innerResult r n d) := by
  rcases hs with ⟨h2,h3,h4,h19⟩
  exact ⟨(innerResult_frame r hr n d 2 (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans h2,
    (innerResult_frame r hr n d 3 (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans h3,
    (innerResult_frame r hr n d 4 (Or.inl (by decide)) (by decide) (by decide) (by decide)).trans h4,
    (innerResult_frame r hr n d 19 (Or.inr (Or.inl rfl)) (by decide) (by decide) (by decide)).trans h19⟩

theorem innerResult_valid (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target n : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) (hv : d.reg (r 25) ≤ 1) :
    (innerResult r n d).reg (r 25) ≤ 1 ∧
      ((innerResult r n d).reg (r 25) = 1 ↔ d.reg (r 25) = 1 ∧
        ∀ i < n,¬ FactorTest N target (d.reg (r 0)) (d.reg (r 1)+i)) := by
  induction n generalizing d with
  | zero => exact ⟨hv,by simp [innerResult,loopResult]⟩
  | succ n ih =>
    let c := d.setReg (r 30) n
    have hsetup := factorSetup_setReg r hr N target n d 30 (by decide) (by decide) (by decide) (by decide) hs
    have hcv : c.reg (r 25) = d.reg (r 25) := by simp [c,reg_set r hr]
    have hc0 : c.reg (r 0) = d.reg (r 0) := by simp [c,reg_set r hr]
    have hc1 : c.reg (r 1) = d.reg (r 1) := by simp [c,reg_set r hr]
    have hfv : (factorBodyStore r c).reg (r 25) ≤ 1 := by
      rw [factorBodyStore_valid r hr N target c hsetup (by omega)]
      split <;> omega
    have ihc := ih (factorBodyStore r c) (factorBodyStore_setup r hr N target c hsetup) hfv
    have hstep : (factorBodyStore r c).reg (r 25) = 1 ↔ d.reg (r 25) = 1 ∧
        ¬ FactorTest N target (d.reg (r 0)) (d.reg (r 1)) := by
      rw [factorBodyStore_valid r hr N target c hsetup (by omega),hcv,hc0,hc1]
      by_cases ht : FactorTest N target (d.reg (r 0)) (d.reg (r 1)) <;> simp [ht]
    change (innerResult r n (factorBodyStore r c)).reg (r 25) ≤ 1 ∧ _
    refine ⟨ihc.1,?_⟩
    change (innerResult r n (factorBodyStore r c)).reg (r 25) = 1 ↔ _
    rw [ihc.2,hstep,factorBodyStore_fresh r hr c 0 (Or.inl (by decide)) (by decide) (by decide),hc0,
      factorBodyStore_index r hr c,hc1,and_assoc]
    exact and_congr_right (fun _ => forall_lt_succ_shift
      (fun b => ¬ FactorTest N target (d.reg (r 0)) b) n (d.reg (r 1)))

theorem innerPrepareStore_setup (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) : FactorSetup r N target (innerPrepareStore r d) := by
  simpa [FactorSetup,innerPrepareStore_reg r hr] using hs

theorem outerBodyStore_setup (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) : FactorSetup r N target (outerBodyStore r d) := by
  have hi := innerResult_setup r hr N target (d.reg (r 24)) (innerPrepareStore r d) (innerPrepareStore_setup r hr N target d hs)
  simpa [FactorSetup,outerBodyStore,reg_set r hr] using hi

theorem outerBodyStore_valid (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) (hv : d.reg (r 25) ≤ 1) :
    (outerBodyStore r d).reg (r 25) ≤ 1 ∧
      ((outerBodyStore r d).reg (r 25) = 1 ↔ d.reg (r 25) = 1 ∧
        ∀ b < d.reg (r 24),¬ FactorTest N target (d.reg (r 0)) (2+b)) := by
  have hi := innerResult_valid r hr N target (d.reg (r 24)) (innerPrepareStore r d)
    (innerPrepareStore_setup r hr N target d hs) (by simpa [innerPrepareStore_reg r hr] using hv)
  simpa [outerBodyStore,reg_set r hr,innerPrepareStore_reg r hr] using hi

theorem outerResult_valid (r : Fin 32 → Fin R) (hr : Function.Injective r) (N target n : ℕ)
    (d : TapeStore R B) (hs : FactorSetup r N target d) (hv : d.reg (r 25) ≤ 1) :
    (outerResult r n d).reg (r 25) ≤ 1 ∧
      ((outerResult r n d).reg (r 25) = 1 ↔ d.reg (r 25) = 1 ∧
        ∀ a < n,∀ b < d.reg (r 24),¬ FactorTest N target (d.reg (r 0)+a) (2+b)) := by
  induction n generalizing d with
  | zero => exact ⟨hv,by simp [outerResult,loopResult]⟩
  | succ n ih =>
    let c := d.setReg (r 26) n
    have hsetup := factorSetup_setReg r hr N target n d 26 (by decide) (by decide) (by decide) (by decide) hs
    have hcv : c.reg (r 25) = d.reg (r 25) := by simp [c,reg_set r hr]
    have hc0 : c.reg (r 0) = d.reg (r 0) := by simp [c,reg_set r hr]
    have hc24 : c.reg (r 24) = d.reg (r 24) := by simp [c,reg_set r hr]
    have hf := outerBodyStore_valid r hr N target c hsetup (by omega)
    have ihc := ih (outerBodyStore r c) (outerBodyStore_setup r hr N target c hsetup) hf.1
    have hstep : (outerBodyStore r c).reg (r 25) = 1 ↔ d.reg (r 25) = 1 ∧
        ∀ b < d.reg (r 24),¬ FactorTest N target (d.reg (r 0)) (2+b) := by simpa only [hcv,hc0,hc24] using hf.2
    change (outerResult r n (outerBodyStore r c)).reg (r 25) ≤ 1 ∧ _
    refine ⟨ihc.1,?_⟩
    change (outerResult r n (outerBodyStore r c)).reg (r 25) = 1 ↔ _
    rw [ihc.2,hstep,outerBodyStore_fresh r hr c 24 (Or.inr (Or.inr (by decide)))
      (by decide) (by decide) (by decide) (by decide) (by decide),hc24,outerBodyStore_index r hr c,hc0,
      and_assoc]
    exact and_congr_right (fun _ => forall_lt_succ_shift
      (fun a => ∀ b < d.reg (r 24),¬ FactorTest N target a (2+b)) n (d.reg (r 0)))




theorem offsetFactorFree_iff (ell : ℕ) (h : 0 < ell) (p : Fin (2^ell)) :
    OffsetFactorFree ell p ↔ RawIrreducibility.FactorFree ell p := by
  have hq : 2 ≤ 2^ell := Nat.one_lt_two_pow (by omega)
  constructor
  · intro hfree a b ha hb
    have hia : a.val-2 < 2^ell-2 := by have := a.isLt;omega
    have hib : b.val-2 < 2^ell-2 := by have := b.isLt;omega
    have hf := hfree (a.val-2) hia (b.val-2) hib
    change ¬ FactorTest (3*ell+1) (2^ell+p.val) a.val b.val
    have hea : 2+(a.val-2) = a.val := by omega
    have heb : 2+(b.val-2) = b.val := by omega
    simpa only [hea,heb] using hf
  · intro hfree a ha b hb
    have hia : 2+a < 2^ell := by omega
    have hib : 2+b < 2^ell := by omega
    exact hfree ⟨2+a,hia⟩ ⟨2+b,hib⟩ (by change 1 < 2+a;omega) (by change 1 < 2+b;omega)




theorem modulusSetup_setReg (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell n : ℕ)
    (d : TapeStore R B) (hs : ModulusSetup r ell d) : ModulusSetup r ell (d.setReg (r 31) n) := by
  simpa [ModulusSetup,reg_set r hr] using hs

theorem candidateBodyStore_setup (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell : ℕ)
    (d : TapeStore R B) (hs : ModulusSetup r ell d) : ModulusSetup r ell (candidateBodyStore r d) := by
  rcases hs with ⟨hq,hQ,hN⟩
  exact ⟨(candidateBodyStore_fresh r hr d 23 (Or.inr (Or.inl rfl))).trans hq,
    (candidateBodyStore_fresh r hr d 24 (Or.inr (Or.inr (Or.inl rfl)))).trans hQ,
    (candidateBodyStore_fresh r hr d 19 (Or.inl rfl)).trans hN⟩

theorem candidateValid_correct (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (d : TapeStore R B) (hs : ModulusSetup r ell d) (hc : d.reg (r 31) < 2^ell) :
    let c := outerResult r (d.reg (r 24)) (candidatePrepareStore r d)
    c.reg (r 25) ≤ 1 ∧ (c.reg (r 25) = 1 ↔ RawIrreducibility.FactorFree ell ⟨d.reg (r 31),hc⟩) := by
  have hp : FactorSetup r (3*ell+1) (2^ell+d.reg (r 31)) (candidatePrepareStore r d) := by
    rcases hs with ⟨hq,hQ,hN⟩
    simp [FactorSetup,candidatePrepareStore_reg r hr,hq,hN]
  have hi := outerResult_valid r hr (3*ell+1) (2^ell+d.reg (r 31)) (d.reg (r 24))
    (candidatePrepareStore r d) hp (by simp [candidatePrepareStore_reg r hr])
  refine ⟨hi.1,?_⟩
  have hiff : (outerResult r (d.reg (r 24)) (candidatePrepareStore r d)).reg (r 25) = 1 ↔
      OffsetFactorFree ell ⟨d.reg (r 31),hc⟩ := by
    simpa [OffsetFactorFree,candidatePrepareStore_reg r hr,hs.2.1] using hi.2
  exact hiff.trans (offsetFactorFree_iff ell h _)







theorem modulusAnswer_setReg (r : Fin 32 → Fin R) (d : TapeStore R B) (j : Fin R) (n : ℕ)
    (h27 : r 27 ≠ j) (h29 : r 29 ≠ j) : modulusAnswer r (d.setReg j n) = modulusAnswer r d := by
  simp [modulusAnswer,TapeStore.setReg,h27,h29]

theorem candidateBodyStore_answer (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (d : TapeStore R B) (hs : ModulusSetup r ell d) (hc : d.reg (r 31) < 2^ell) :
    modulusAnswer r (candidateBodyStore r d) =
      if modulusTest ell (d.reg (r 31)) then some (d.reg (r 31)) else modulusAnswer r d := by
  let c := outerResult r (d.reg (r 24)) (candidatePrepareStore r d)
  have hv := candidateValid_correct r hr ell h d hs hc
  have hbit : c.reg (r 25) ≤ 1 := hv.1
  have htest : modulusTest ell (d.reg (r 31)) = true ↔ RawIrreducibility.FactorFree ell ⟨d.reg (r 31),hc⟩ := by
    simp [modulusTest,hc]
  have hsuccess : c.reg (r 25) = 1 ↔ modulusTest ell (d.reg (r 31)) = true := hv.2.trans htest.symm
  have hreg (i : Fin 32) (hi : i = 27 ∨ i = 29 ∨ i = 31) : c.reg (r i) = d.reg (r i) := by
    rw [outerResult_frame r hr _ _ i (by rcases hi with h|h|h <;> simp_all)
      (by rcases hi with h|h|h <;> omega) (by rcases hi with h|h|h <;> omega)
      (by rcases hi with h|h|h <;> omega) (by rcases hi with h|h|h <;> omega)
      (by rcases hi with h|h|h <;> omega) (by rcases hi with h|h|h <;> omega),candidatePrepareStore_reg r hr]
    rcases hi with rfl|rfl|rfl <;> simp
  have h27 := hreg 27 (Or.inl rfl)
  have h29 := hreg 29 (Or.inr (Or.inl rfl))
  have h31 := hreg 31 (Or.inr (Or.inr rfl))
  change modulusAnswer r (commitStore (commitLayout r) c) = _
  by_cases hf : c.reg (r 25) = 0
  · have hac : modulusTest ell (d.reg (r 31)) ≠ true := by
      intro hacc
      have := hsuccess.mpr hacc
      omega
    simp [modulusAnswer,commitStore,commitLayout,hf,hac,h27,h29]
  · have hf1 : c.reg (r 25) = 1 := by omega
    have hac := hsuccess.mp hf1
    simp [modulusAnswer,commitStore,commitBodyStore,commitLayout,reg_set r hr,hf,hac,h31]






theorem descend_skip (test : ℕ → Bool) (n : ℕ) (state : Option ℕ) (hs : ∀ i < n,test i = false) :
    descend test n state = state := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
    rw [descend,hs n (by omega)]
    simp only [Bool.false_eq_true,reduceIte]
    exact ih state (fun i hi => hs i (by omega))

theorem descend_least (test : ℕ → Bool) (n target : ℕ) (state : Option ℕ)
    (ht : target < n) (hp : test target = true) (hm : ∀ i < n,test i = true → target ≤ i) :
    descend test n state = some target := by
  induction n generalizing state with
  | zero => omega
  | succ n ih =>
    rw [descend]
    by_cases he : target = n
    · subst target
      rw [hp,if_pos rfl]
      apply descend_skip
      intro i hi
      apply Bool.eq_false_iff.mpr
      intro hh
      have := hm i (by omega) hh
      omega
    · apply ih _ (by omega) (fun i hi => hm i (by omega))

theorem candidateResult_answer (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (n : ℕ) (d : TapeStore R B) (hs : ModulusSetup r ell d) (hn : n ≤ 2^ell) :
    modulusAnswer r (candidateResult r n d) = descend (modulusTest ell) n (modulusAnswer r d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    let c := d.setReg (r 31) n
    have hsetup := modulusSetup_setReg r hr ell n d hs
    have hc : c.reg (r 31) = n := by simp [c,reg_set r hr]
    have ha : modulusAnswer r c = modulusAnswer r d := modulusAnswer_setReg r d _ n (hr.ne (by decide)) (hr.ne (by decide))
    change modulusAnswer r (candidateResult r n (candidateBodyStore r c)) = _
    rw [ih (candidateBodyStore r c) (candidateBodyStore_setup r hr ell c hsetup) (by omega),
      candidateBodyStore_answer r hr ell h c hsetup (by omega),hc,ha]
    rfl

theorem constructResult_answer (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (d : TapeStore R B) (hq : d.reg (r 23) = 2^ell) (hN : d.reg (r 19) = 3*ell+1) :
    modulusAnswer r (constructResult r d) = descend (modulusTest ell) (2^ell) none := by
  have hs : ModulusSetup r ell (prepareStore r d) := by simp [ModulusSetup,prepareStore_reg r hr,hq,hN]
  rw [constructResult,hq,candidateResult_answer r hr ell h _ _ hs (by omega)]
  simp [modulusAnswer,prepareStore_reg r hr]

/-- The actual descending source search returns the exact canonical minimum
irreducible modulus index, not an alternate field representation. -/
theorem constructResult_index (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (d : TapeStore R B) (hq : d.reg (r 23) = 2^ell) (hN : d.reg (r 19) = 3*ell+1) :
    (constructResult r d).reg (r 27) = (selectedIndex ell h).val := by
  have hp : modulusTest ell (selectedIndex ell h).val = true := by
    simp [modulusTest,(selectedIndex ell h).isLt,RawIrreducibility.selectedIndex_factorFree ell h]
  have hm : ∀ i < 2^ell,modulusTest ell i = true → (selectedIndex ell h).val ≤ i := by
    intro i hi ht
    have hfree : RawIrreducibility.FactorFree ell ⟨i,hi⟩ := by simpa [modulusTest,hi] using ht
    exact RawIrreducibility.selectedIndex_le ell h ⟨i,hi⟩ hfree
  have han : modulusAnswer r (constructResult r d) = some (selectedIndex ell h).val := by
    rw [constructResult_answer r hr ell h d hq hN]
    exact descend_least (modulusTest ell) (2^ell) (selectedIndex ell h).val none (selectedIndex ell h).isLt hp hm
  unfold modulusAnswer at han
  split at han
  · contradiction
  · exact Option.some.inj han

theorem candidateBodyStore_input (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 32) (hi : i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23) :
    (candidateBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold candidateBodyStore
  rw [commitStore_fresh _ _ _
    (hr.ne (show i ≠ (27:Fin 32) from by rcases hi with h|h|h|h|h <;> omega))
    (hr.ne (show i ≠ (28:Fin 32) from by rcases hi with h|h|h|h|h <;> omega))
    (hr.ne (show i ≠ (29:Fin 32) from by rcases hi with h|h|h|h|h <;> omega))
    (hr.ne (show i ≠ (25:Fin 32) from by rcases hi with h|h|h|h|h <;> omega)),
    outerResult_frame r hr _ _ i (by rcases hi with h|h|h|h|h <;> simp_all)
      (by rcases hi with h|h|h|h|h <;> omega) (by rcases hi with h|h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h|h <;> omega) (by rcases hi with h|h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h|h <;> omega) (by rcases hi with h|h|h|h|h <;> omega),
    candidatePrepareStore_reg r hr]
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> simp

theorem constructResult_input (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 32) (hi : i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23) :
    (constructResult r d).reg (r i) = d.reg (r i) := by
  rw [constructResult,candidateResult,loopResult_frame (r 31) (candidateBodyStore r) (r i)
    (hr.ne (show i ≠ (31:Fin 32) from by rcases hi with h|h|h|h|h <;> omega))
    (fun c => candidateBodyStore_input r hr c i hi),prepareStore_reg r hr]
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> simp

theorem candidateBodyStore_tapeData (r : Fin 32 → Fin R) (d : TapeStore R B) :
    tapeData (candidateBodyStore r d) = tapeData d := by
  rw [candidateBodyStore,commitStore_tapeData,outerResult_tapeData]
  rfl

theorem constructResult_tapeData (r : Fin 32 → Fin R) (d : TapeStore R B) :
    tapeData (constructResult r d) = tapeData d := by
  rw [constructResult,candidateResult,loopResult_tapeData (r 31) (candidateBodyStore r) (candidateBodyStore_tapeData r)]
  rfl

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

/-- Complete canonical modulus source contract, including every caller/tape
frame and the polynomial source-step bound. -/
theorem construct_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (ell : ℕ) (h : 0 < ell) (M : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M)
    (hq : d.reg (r 23) = 2^ell) (hN : d.reg (r 19) = 3*ell+1) (h2q : 2*(2^ell) ≤ M) :
    ∃ t e,t ≤ 30000*(M+1)^7 ∧ (construct r).Stops inp (d.toCfg (construct (B:=B) r).entry) t e ∧
      e.store = constructResult r d ∧ e.reg (r 27) = (selectedIndex ell h).val ∧
      (∀ i,i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ tapeData e.store = tapeData d := by
  obtain ⟨t,e,ht,he,hes,hbound⟩ := construct_stops_exact r hr inp M d hd
    (by rw [hq];exact Nat.one_lt_two_pow (by omega)) (by rw [hq];exact h2q)
  refine ⟨t,e,ht,he,hes,?_,?_,?_,hbound,?_⟩
  · change e.store.reg (r 27) = _
    rw [hes];exact constructResult_index r hr ell h d hq hN
  · intro i hi
    change e.store.reg (r i) = _
    rw [hes];exact constructResult_input r hr d i hi
  · intro j hj
    change e.store.reg j = _
    rw [hes];exact constructResult_outside r d j hj
  · rw [hes];exact constructResult_tapeData r d







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













theorem coefficientBound_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hN : 3*d.reg (r 20)+1 ≤ M) :
    ∃ t e,t ≤ 100*M+100 ∧ (coefficientBound r).Stops inp (d.toCfg (coefficientBound (B:=B) r).entry) t e ∧
      e.store = boundStore r d ∧ (∀ j,e.reg j ≤ M) := by
  have h₀ := TapeMacros.clear_stops (r 19) inp (d.reg (r 19)) d rfl
  let c₀ := d.setReg (r 19) 0
  have hb₀ : ∀ j,c₀.reg j ≤ M := setReg_bound _ _ 0 M hd (by omega)
  obtain ⟨c₁,h₁,hs₁⟩ := TapeMacros.addPreserving_stops (r 20) (r 19) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₀
  have hb₁ : ∀ j,c₁.store.reg j ≤ M := by
    rw [hs₁]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M hb₀
    simp [c₀,SourceModulus.reg_set r hr]
    omega
  obtain ⟨c₂,h₂,hs₂⟩ := TapeMacros.addPreserving_stops (r 20) (r 19) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₁.store
  have hb₂ : ∀ j,c₂.store.reg j ≤ M := by
    rw [hs₂]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M hb₁
    rw [hs₁]
    simp [c₀,SourceModulus.reg_set r hr]
    omega
  obtain ⟨c₃,h₃,hs₃⟩ := TapeMacros.addPreserving_stops (r 20) (r 19) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₂.store
  have hb₃ : ∀ j,c₃.store.reg j ≤ M := by
    rw [hs₃]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M hb₂
    rw [hs₂,hs₁]
    simp [c₀,SourceModulus.reg_set r hr]
    omega
  have hi := TapeMacros.increment_stops (r 19) inp c₃.store
  have hsum : c₃.store.reg (r 19)+1 ≤ M := by
    rw [hs₃,hs₂,hs₁]
    simp [c₀,SourceModulus.reg_set r hr]
    omega
  have hall := (((h₀.seq h₁).seq h₂).seq h₃).seq hi
  refine ⟨_,_,?_,hall,?_,setReg_bound _ _ _ M hb₃ hsum⟩
  · have := hd (r 19);have := hb₀ (r 28);have := hb₀ (r 20)
    have := hb₁ (r 28);have := hb₁ (r 20);have := hb₂ (r 28);have := hb₂ (r 20);omega
  · change c₃.store.setReg (r 19) _ = _
    rw [hs₃,hs₂,hs₁]
    rfl

theorem boundStore_reg (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i : Fin 32) :
    (boundStore r d).reg (r i) = if i = 19 then 3*d.reg (r 20)+1 else if i = 28 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [boundStore,SourceModulus.reg_set r hr] <;> omega








theorem monicWord_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hsum : d.reg (r 23)+d.reg (r 27) ≤ M) :
    ∃ t e,t ≤ 20*M+20 ∧ (monicWord r).Stops inp (d.toCfg (monicWord (B:=B) r).entry) t e ∧
      e.store = monicStore r d ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨c₁,h₁,hs₁⟩ := TapeMacros.copy_stops (r 23) (r 3) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp d
  have hb₁ : ∀ j,c₁.store.reg j ≤ M := by
    rw [hs₁];exact setReg_bound _ _ 0 M (setReg_bound d _ _ M hd (hd (r 23))) (by omega)
  obtain ⟨c₂,h₂,hs₂⟩ := TapeMacros.addPreserving_stops (r 27) (r 3) (r 28)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₁.store
  have hb₂ : ∀ j,c₂.store.reg j ≤ M := by
    rw [hs₂]
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M hb₁
    rw [hs₁]
    simpa [SourceModulus.reg_set r hr] using hsum
  have hall := h₁.seq h₂
  refine ⟨_,_,?_,hall,?_,hb₂⟩
  · have := hd (r 3);have := hd (r 28);have := hd (r 23);have := hb₁ (r 28);have := hb₁ (r 27);omega
  · change c₂.store = _
    rw [hs₂,hs₁];rfl

theorem monicStore_reg (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i : Fin 32) :
    (monicStore r d).reg (r i) = if i = 3 then d.reg (r 23)+d.reg (r 27) else if i = 28 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [monicStore,SourceModulus.reg_set r hr]









theorem squareStore_reg (r : Fin 32 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i : Fin 32) :
    (UnaryArithmetic.multiplyStore d (r 23) (r 23) (r 24) (r 28) (r 30)).reg (r i) =
      if i = 30 ∨ i = 28 then 0 else if i = 24 then d.reg (r 23)*d.reg (r 23) else d.reg (r i) := by
  fin_cases i <;> simp [UnaryArithmetic.multiplyStore,SourceModulus.reg_set r hr]





theorem setupStore_environment (r : Fin 32 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (d : TapeStore R B) (hell : d.reg (r 20) = ell) (hq : d.reg (r 23) = 2^ell) :
    Environment r ell h (setupStore r d) := by
  let c₁ := boundStore r d
  let c₂ := SourceModulus.constructResult r c₁
  let c₃ := monicStore r c₂
  have hq₁ : c₁.reg (r 23) = 2^ell := by simp [c₁,boundStore_reg r hr,hq]
  have hN₁ : c₁.reg (r 19) = 3*ell+1 := by simp [c₁,boundStore_reg r hr,hell]
  have hell₁ : c₁.reg (r 20) = ell := by simp [c₁,boundStore_reg r hr,hell]
  have hp₂ : c₂.reg (r 27) = (selectedIndex ell h).val := SourceModulus.constructResult_index r hr ell h c₁ hq₁ hN₁
  have hq₂ : c₂.reg (r 23) = 2^ell :=
    (SourceModulus.constructResult_input r hr c₁ 23 (by decide)).trans hq₁
  have hN₂ : c₂.reg (r 19) = 3*ell+1 :=
    (SourceModulus.constructResult_input r hr c₁ 19 (by decide)).trans hN₁
  have hell₂ : c₂.reg (r 20) = ell :=
    (SourceModulus.constructResult_input r hr c₁ 20 (by decide)).trans hell₁
  have hfinal (i : Fin 32) : (setupStore r d).reg (r i) =
      if i = 30 ∨ i = 28 then 0 else if i = 24 then c₃.reg (r 23)*c₃.reg (r 23) else c₃.reg (r i) :=
    squareStore_reg r hr c₃ i
  have hp : (2^ell)*(2^ell) = 2^(2*ell) := by rw [← pow_add];congr 1;omega
  simp [Environment,hfinal,c₃,monicStore_reg r hr,hq₂,hN₂,hell₂,hp₂,hp]

theorem setup_stops_exact (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (ell : ℕ) (h : 0 < ell) (M : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M)
    (hell : d.reg (r 20) = ell) (hq : d.reg (r 23) = 2^ell)
    (hN : 3*ell+1 ≤ M) (h2q : 2*(2^ell) ≤ M) (hQ : 2^(2*ell) ≤ M) :
    ∃ t e,t ≤ 40000*(M+1)^7 ∧ (setup r).Stops inp (d.toCfg (setup (B:=B) r).entry) t e ∧
      e.store = setupStore r d ∧ (∀ j,e.reg j ≤ M) := by
  have hM : 1 ≤ M := by have : 0 < 2^ell := Nat.two_pow_pos ell;omega
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := coefficientBound_stops r hr inp M d hd (by simpa only [hell] using hN)
  have hq₁ : c₁.reg (r 23) = 2^ell := by change c₁.store.reg (r 23) = _;rw [hs₁,boundStore_reg r hr];simp [hq]
  have hN₁ : c₁.reg (r 19) = 3*ell+1 := by change c₁.store.reg (r 19) = _;rw [hs₁,boundStore_reg r hr];simp [hell]
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂,hp₂,hpres₂,_,hb₂,_⟩ := SourceModulus.construct_stops r hr inp ell h M c₁.store hb₁ hq₁ hN₁ h2q
  have hq₂ : c₂.reg (r 23) = 2^ell := (hpres₂ 23 (by decide)).trans hq₁
  have hsum : c₂.reg (r 23)+c₂.reg (r 27) ≤ M := by
    rw [hq₂,hp₂]
    have := (selectedIndex ell h).isLt
    omega
  obtain ⟨t₃,c₃,ht₃,h₃,hs₃,hb₃⟩ := monicWord_stops r hr inp M c₂.store hb₂ hsum
  have hq₃ : c₃.reg (r 23) = 2^ell := by
    change c₃.store.reg (r 23) = _
    rw [hs₃,monicStore_reg r hr];simpa using hq₂
  obtain ⟨t₄,c₄,ht₄,h₄,hs₄⟩ := UnaryArithmetic.multiply_stops_polynomial
    (r 23) (r 23) (r 24) (r 28) (r 30)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp c₃.store M
    (hb₃ (r 23)) (hb₃ (r 23)) (hb₃ (r 24)) (hb₃ (r 28)) (hb₃ (r 30))
  have hb₄ : ∀ j,c₄.store.reg j ≤ M := by
    rw [hs₄]
    unfold UnaryArithmetic.multiplyStore
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ 0 M _ (by omega)
    apply setReg_bound _ _ _ M hb₃
    change c₃.reg (r 23)*c₃.reg (r 23) ≤ M
    rw [hq₃,← pow_add]
    have he : ell+ell = 2*ell := by omega
    simpa only [he] using hQ
  have hall := ((h₁.seq h₂).seq h₃).seq h₄
  refine ⟨_,_,?_,hall,?_,hb₄⟩
  · have hp7 := Nat.le_self_pow (by decide : (7:ℕ) ≠ 0) (M+1)
    have hM7 : M ≤ (M+1)^7 := (by omega : M ≤ M+1).trans hp7
    have h17 : 1 ≤ (M+1)^7 := by omega
    have h27 : (M+1)^2 ≤ (M+1)^7 := Nat.pow_le_pow_right (by omega) (by decide)
    omega
  · change c₄.store = _
    rw [hs₄,hs₃,hs₂,hs₁]
    rfl

theorem setupStore_tapeData (r : Fin 32 → Fin R) (d : TapeStore R B) : tapeData (setupStore r d) = tapeData d := by
  simp only [setupStore,UnaryArithmetic.multiplyStore,tapeData_setReg]
  unfold monicStore
  simp only [tapeData_setReg]
  rw [SourceModulus.constructResult_tapeData]
  rfl

theorem setupStore_outside (r : Fin 32 → Fin R) (d : TapeStore R B) (j : Fin R) (hne : ∀ i : Fin 32,j ≠ r i) :
    (setupStore r d).reg j = d.reg j := by
  simp only [setupStore,UnaryArithmetic.multiplyStore,TapeStore.setReg,
    Function.update_of_ne (hne 24),Function.update_of_ne (hne 28),Function.update_of_ne (hne 30)]
  unfold monicStore
  simp only [TapeStore.setReg,Function.update_of_ne (hne 3),Function.update_of_ne (hne 28)]
  rw [SourceModulus.constructResult_outside r _ j hne]
  simp [boundStore,TapeStore.setReg,hne 19,hne 28]

/-- Complete source setup from preserved runtime ell/q, with the exact
canonical field environment needed by all arithmetic routines. -/
theorem setup_stops (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (ell : ℕ) (h : 0 < ell) (M : ℕ) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M)
    (hell : d.reg (r 20) = ell) (hq : d.reg (r 23) = 2^ell)
    (hN : 3*ell+1 ≤ M) (h2q : 2*(2^ell) ≤ M) (hQ : 2^(2*ell) ≤ M) :
    ∃ t e,t ≤ 40000*(M+1)^7 ∧ (setup r).Stops inp (d.toCfg (setup (B:=B) r).entry) t e ∧
      e.store = setupStore r d ∧ Environment r ell h e.store ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ tapeData e.store = tapeData d := by
  obtain ⟨t,e,ht,he,hes,hbound⟩ := setup_stops_exact r hr inp ell h M d hd hell hq hN h2q hQ
  refine ⟨t,e,ht,he,hes,?_,?_,hbound,?_⟩
  · rw [hes];exact setupStore_environment r hr ell h d hell hq
  · intro j hj
    change e.store.reg j = _
    rw [hes];exact setupStore_outside r d j hj
  · rw [hes];exact setupStore_tapeData r d





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

theorem solution {R B : ℕ} (r : Fin 32 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (ell : ℕ) (h : 0 < ell) (M : ℕ) (d : ExpandingCodes.Computation.TapeStore R B) (hd : ∀ j,d.reg j ≤ M)
    (hell : d.reg (r 20) = ell) (hq : d.reg (r 23) = 2^ell)
    (hN : 3*ell+1 ≤ M) (h2q : 2*(2^ell) ≤ M) (hQ : 2^(2*ell) ≤ M) :
    ∃ t e,t ≤ 40000*(M+1)^7 ∧ (ExpandingCodes.Computation.SourceFieldSetup.setup r).Stops inp (d.toCfg (ExpandingCodes.Computation.SourceFieldSetup.setup (B:=B) r).entry) t e ∧
      e.store = ExpandingCodes.Computation.SourceFieldSetup.setupStore r d ∧ ExpandingCodes.Computation.SourceFieldSetup.Environment r ell h e.store ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ ExpandingCodes.Computation.FieldConvolution.tapeData e.store = ExpandingCodes.Computation.FieldConvolution.tapeData d := by
  exact @ExpandingCodes.Computation.SourceFieldSetup.setup_stops R B r hr inp ell h M d hd hell hq hN h2q hQ

