import Mathlib
import Definitions.Def_ExpandingCodes_PolynomialStretch_OperationalFamily
import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime
import Theorems.Thm_ExpandingCodes_PolynomialStretch_binary_sampler_implementation_source
import Theorems.Thm_ExpandingCodes_PolynomialStretch_binary_tester_implementation_source
import Theorems.Thm_ExpandingCodes_PolynomialStretch_auxiliary_rate

set_option autoImplicit false

/-! Inlined whole module: ExpandingCodes.Construction.Geometry -/
section FlattenModule3



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch





theorem fieldSize_pos (d n : ℕ) : 0 < fieldSize d n := by
  exact pow_pos (by decide) _












/-- Honest finite characteristic-two fields and public enumerations exist.
No algorithmic, rank, or expansion assertion is inserted into this data. -/
noncomputable def standardGeometry (d n : ℕ) : Geometry d n := by
  let F := GaloisField 2 (fieldExponent d n)
  letI : Fintype F := Fintype.ofFinite F
  have he : fieldExponent d n ≠ 0 := (fieldExponent_pos d n).ne'
  have hcard : Fintype.card F = fieldSize d n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (fieldExponent d n) he
  exact {
    F := F
    field := inferInstance
    finite := inferInstance
    charTwo := inferInstance
    elements := Fintype.equivOfCardEq (by simpa using hcard.symm)
    rowOrder := Fintype.equivOfCardEq (by
      simp only [Fintype.card_fin, Fintype.card_fun, hcard]
      rfl) }




end ExpandingCodes.PolynomialStretch

end FlattenModule3

/-! Inlined whole module: ExpandingCodes.Computation.CounterMachine -/
section FlattenModule6


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

/-- A deliberately small instruction language. Every branch has a finite target;
there is no instruction for evaluating an arbitrary function of register values. -/
inductive CounterInstr (registers labels : ℕ) where
  | halt
  | jump (next : Fin labels)
  | inc (reg : Fin registers) (next : Fin labels)
  | dec (reg : Fin registers) (zero positive : Fin labels)
  | emit (bit : Bool) (next : Fin labels)
  | read (tape : Fin 4) (next : Sym → Fin labels)

structure CounterProgram (registers labels : ℕ) where
  entry : Fin labels
  code : Fin labels → CounterInstr registers labels

structure CounterCfg (registers labels : ℕ) where
  pc : Fin labels
  reg : Fin registers → ℕ
  roHead : Fin 4 → ℕ
  output : List Bool

namespace CounterProgram
variable {R L : ℕ}




def halted (P : CounterProgram R L) (c : CounterCfg R L) : Prop :=
  P.code c.pc = .halt

instance (P : CounterProgram R L) (c : CounterCfg R L) : Decidable (P.halted c) := by
  unfold halted
  cases P.code c.pc
  · exact isTrue rfl
  all_goals exact isFalse (by intro h; cases h)































 



 








 



 





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

 theorem TapeRep.write {l : List Sym} {f : ℕ → Sym} (hr : TapeRep l f)
    (h : ℕ) (a : Sym) : TapeRep (Machine.writeAt l h a) (Function.update f h a) := by
  intro k
  rw [getD_writeAt, hr]
  simp [Function.update_apply, eq_comm]

 theorem TapeRep.write_same {l : List Sym} {f : ℕ → Sym} (hr : TapeRep l f)
    (h : ℕ) : TapeRep (Machine.writeAt l h (f h)) f := by
  simpa only [Function.update_eq_self] using hr.write h (f h)





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

 






























 











































 

















 theorem tape_write_scanned {l : List Sym} {f : ℕ → Sym}
    (hr : TapeRep l f) (h : ℕ) : TapeRep (Machine.writeAt l h (l.getD h .blank)) f := by
  rw [hr h]
  exact hr.write_same h

 




































 












































 








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
  getD_append_singleton tape_write_scanned)
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











 


end TapeInstr

namespace TapeProgram
variable {R B L K : ℕ}















 








 



 







 
















































 




 




 


































 








 




















 




 




 



 







 










 









 









































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

theorem dimension_upper_bound (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    (dimension ε : ℝ) ≤ 2048 * ε⁻¹ ^ 2 := by
  have hi := parameter_inv_ge_one ε hε
  have hs : (1 : ℝ) ≤ ε⁻¹ ^ 2 := by nlinarith
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 512 * ε⁻¹ ^ 2 by positivity)
  unfold dimension
  push_cast
  nlinarith

theorem arity_upper_bound (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    (arity ε : ℝ) ≤ 33554432 * ε⁻¹ ^ 6 := by
  have hi := parameter_inv_ge_one ε hε
  have hsix : (1 : ℝ) ≤ ε⁻¹ ^ 6 := one_le_pow₀ hi
  have hd := dimension_upper_bound ε hε
  have hdsq : (dimension ε : ℝ) ^ 2 ≤ (2048 * ε⁻¹ ^ 2) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (dimension ε : ℝ) from Nat.cast_nonneg _]
  have hp := mul_le_mul_of_nonneg_right hdsq (sq_nonneg (ε⁻¹ : ℝ))
  have hc := Nat.ceil_lt_add_one
    (show 0 ≤ 4 * (dimension ε : ℝ) ^ 2 * ε⁻¹ ^ 2 by positivity)
  unfold arity
  nlinarith

/-- Rational construction parameters retain absolute bounds for every real ε.
The constants are deliberately loose; their independence of ε is the obligation. -/
theorem rational_parameter_bounds (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    ∃ θ : ℚ, ε / 2 < (θ : ℝ) ∧ (θ : ℝ) < ε ∧
      (dimension (θ : ℝ) : ℝ) ≤ 8192 * ε⁻¹ ^ 2 ∧
      (arity (θ : ℝ) : ℝ) ≤ 2147483648 * ε⁻¹ ^ 6 := by
  obtain ⟨θ, hlo, hhi⟩ := exists_rat_btwn (show ε / 2 < ε by linarith [hε.1])
  have hθpos : 0 < (θ : ℝ) := lt_trans (half_pos hε.1) hlo
  have hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1 / 2 := ⟨hθpos, hhi.trans hε.2⟩
  have hi : (θ : ℝ)⁻¹ ≤ 2 * ε⁻¹ := by
    calc
      (θ : ℝ)⁻¹ ≤ (ε / 2)⁻¹ := (inv_le_inv₀ hθpos (half_pos hε.1)).2 hlo.le
      _ = 2 * ε⁻¹ := by rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
  have htwo : (θ : ℝ)⁻¹ ^ 2 ≤ 4 * ε⁻¹ ^ 2 := by
    calc
      (θ : ℝ)⁻¹ ^ 2 ≤ (2 * ε⁻¹) ^ 2 := by gcongr
      _ = 4 * ε⁻¹ ^ 2 := by ring
  have hsix : (θ : ℝ)⁻¹ ^ 6 ≤ 64 * ε⁻¹ ^ 6 := by
    calc
      (θ : ℝ)⁻¹ ^ 6 ≤ (2 * ε⁻¹) ^ 6 := by gcongr
      _ = 64 * ε⁻¹ ^ 6 := by ring
  refine ⟨θ, hlo, hhi, ?_, ?_⟩
  · have hd := dimension_upper_bound (θ : ℝ) hθ
    nlinarith
  · have hk := arity_upper_bound (θ : ℝ) hθ
    nlinarith

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

theorem rowCount_lower (d n : ℕ) : n ^ (2 * d ^ 2) ≤ rowCount d n := by
  have h := Nat.pow_le_pow_left (fieldSize_lower d n) d
  simpa only [rowCount, ← pow_mul, show 2 * d * d = 2 * d ^ 2 by ring] using h

theorem rowCount_upper (d n : ℕ) (hd : 0 < d) (hn : 2 ≤ n) :
    rowCount d n < 2 ^ d * n ^ (2 * d ^ 2) := by
  have h := Nat.pow_lt_pow_left (fieldSize_upper d n hd hn) hd.ne'
  simpa only [rowCount, mul_pow, ← pow_mul, show 2 * d * d = 2 * d ^ 2 by ring] using h

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

/-- The deterministic row count has polynomial stretch with the specified arity. -/
theorem eventually_rowCount_bounds (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      n < rowCount (dimension ε) n ∧ rowCount (dimension ε) n < n ^ arity ε := by
  let d := dimension ε
  let k := arity ε
  have hd : 0 < d := lt_of_lt_of_le (by decide : 0 < 4) (dimension_ge_four ε hε)
  have hk : 2 * d ^ 2 + 1 ≤ k := arity_exceeds_row_exponent ε hε
  apply Filter.eventually_atTop.2
  refine ⟨max 2 (2 ^ d + 1), ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnp : 0 < n := by omega
  have hnlarge : 2 ^ d < n := by have := (le_max_right _ _).trans hn; omega
  constructor
  · have he : 1 < 2 * d ^ 2 := by have := pow_pos hd 2; omega
    exact (lt_self_pow₀ (by omega : 1 < n) he).trans_le (rowCount_lower d n)
  · calc
      rowCount d n < 2 ^ d * n ^ (2 * d ^ 2) := rowCount_upper d n hd hn2
      _ < n ^ (2 * d ^ 2 + 1) := by
        rw [pow_succ n (2 * d ^ 2)]
        exact (Nat.mul_lt_mul_of_pos_right hnlarge (pow_pos hnp (2 * d ^ 2))).trans_eq
          (Nat.mul_comm n (n ^ (2 * d ^ 2)))
      _ ≤ n ^ k := Nat.pow_le_pow_right (by omega) hk

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

theorem uniformProb_true {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    uniformProb (fun _ : Ω => True) = 1 := by
  rw [uniformProb_eq_card_filter]
  simp [Fintype.card_ne_zero]

theorem uniformProb_pi {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] (E : ∀ i, Ω i → Prop) :
    uniformProb (fun ω : ∀ i, Ω i => ∀ i, E i (ω i)) =
      ∏ i, uniformProb (E i) := by
  classical
  let ec : {ω : (∀ i, Ω i) // ∀ i, E i (ω i)} ≃ (∀ i, {ω // E i ω}) :=
    { toFun := fun ω i => ⟨ω.val i, ω.property i⟩
      invFun := fun ω => ⟨fun i => (ω i).val, fun i => (ω i).property⟩
      left_inv := fun ω => rfl
      right_inv := fun ω => rfl }
  simp_rw [uniformProb_eq_card_subtype]
  calc
    _ = (Fintype.card (∀ i, {ω // E i ω}) : ℝ) /
        Fintype.card (∀ i, Ω i) := by
      congr 1
      norm_cast
      convert Fintype.card_congr ec using 1
      congr 1
      exact Subsingleton.elim _ _
    _ = _ := by simp [Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]

theorem uniformProb_pi_finset {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] (S : Finset I)
    (E : ∀ i, Ω i → Prop) :
    uniformProb (fun ω : ∀ i, Ω i => ∀ i ∈ S, E i (ω i)) =
      ∏ i ∈ S, uniformProb (E i) := by
  classical
  have h := uniformProb_pi (fun i ω => i ∈ S → E i ω)
  rw [show (fun ω : ∀ i, Ω i => ∀ i ∈ S, E i (ω i)) =
    (fun ω => ∀ i, i ∈ S → E i (ω i)) from rfl, h]
  rw [← Finset.prod_subset (Finset.subset_univ S) (by
    intro i _ hi
    simpa [hi] using (uniformProb_true (Ω := Ω i)))]
  apply Finset.prod_congr rfl
  intro i hi
  simp [hi]

theorem uniformProb_eval {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] [Nonempty Ω]
    (i : I) (E : Ω → Prop) :
    uniformProb (fun ω : I → Ω => E (ω i)) = uniformProb E := by
  classical
  simpa using uniformProb_pi_finset (Ω := fun _ : I => Ω) {i} (fun _ => E)

theorem uniformProb_addHom_eq {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    uniformProb (fun x => f x = y) = 1 / (Fintype.card H : ℝ) := by
  classical
  have hsame (z : H) : (Finset.univ.filter fun x => f x = z).card =
      (Finset.univ.filter fun x => f x = y).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf z) (hf y)
  have hcard : Fintype.card G =
      Fintype.card H * (Finset.univ.filter fun x => f x = y).card := by
    calc
      Fintype.card G = ∑ z : H, (Finset.univ.filter fun x => f x = z).card := by
        exact Finset.card_eq_sum_card_fiberwise (by simp)
      _ = _ := by simp_rw [hsame]; simp
  have hpos : 0 < (Finset.univ.filter fun x => f x = y).card := by
    obtain ⟨x, hx⟩ := hf y
    exact Finset.card_pos.mpr ⟨x, by simp [hx]⟩
  rw [uniformProb_eq_card_filter, hcard, Nat.cast_mul]
  have hne : ((Finset.univ.filter fun x => f x = y).card : ℝ) ≠ 0 := by positivity
  field_simp

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

/-! Inlined whole module: ExpandingCodes.Construction.AffineGeometry -/
section FlattenModule23



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- The public layer parameters are distinct whenever all layer indices fit in the field. -/
theorem alpha_injective {d n k : ℕ} (g : Geometry d n) (hk : k ≤ fieldSize d n) :
    Function.Injective (alpha g : Fin k → g.F) := by
  intro i j hij
  have hi : i.val < fieldSize d n := lt_of_lt_of_le i.isLt hk
  have hj : j.val < fieldSize d n := lt_of_lt_of_le j.isLt hk
  have he : (⟨i.val, hi⟩ : Fin (fieldSize d n)) = ⟨j.val, hj⟩ := by
    apply g.elements.injective
    simpa only [alpha, dif_pos hi, dif_pos hj] using hij
  exact Fin.ext (congrArg (fun x : Fin (fieldSize d n) => x.val) he)

/-- Values of the fixed forms on any `d` distinct layers determine the point. -/
theorem fixedForm_layers_injective {d n k : ℕ} (g : Geometry d n)
    (hk : k ≤ fieldSize d n) (layers : Fin d ↪ Fin k) :
    Function.Injective (fun z : Fin d → g.F => fun j : Fin d => fixedForm g (layers j) z) := by
  have hv : Function.Injective (fun j : Fin d => alpha g (layers j)) :=
    (alpha_injective g hk).comp layers.injective
  apply Matrix.mulVec_injective_of_det_ne_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr hv)

/-- Equality of `d` fixed-form evaluations on distinct layers forces equality of points. -/
theorem eq_of_fixedForm_eq {d n k : ℕ} (g : Geometry d n)
    (hk : k ≤ fieldSize d n) (layers : Fin d ↪ Fin k)
    {z z' : Fin d → g.F}
    (h : ∀ j, fixedForm g (layers j) z = fixedForm g (layers j) z') : z = z' :=
  fixedForm_layers_injective g hk layers (funext h)

end ExpandingCodes.PolynomialStretch

end FlattenModule23

/-! Inlined whole module: ExpandingCodes.Construction.ActivePairs -/
section FlattenModule24


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- Layers whose fixed level at `z` belongs to a prescribed set of level pairs. -/
noncomputable def activeLayers {d n k : ℕ} (g : Geometry d n)
    (A : Finset (Fin k × g.F)) (z : Fin d → g.F) : Finset (Fin k) :=
  Finset.univ.filter (fun i => (i, fixedForm g i z) ∈ A)

/-- The deterministic candidate set `W_A` of paper Lemma 2.6. -/
noncomputable def activePointSet {d n k : ℕ} (g : Geometry d n)
    (A : Finset (Fin k × g.F)) : Finset (Fin d → g.F) :=
  Finset.univ.filter (fun z => d ≤ (activeLayers g A z).card)

@[simp] theorem mem_activeLayers {d n k : ℕ} (g : Geometry d n)
    (A : Finset (Fin k × g.F)) (z : Fin d → g.F) (i : Fin k) :
    i ∈ activeLayers g A z ↔ (i, fixedForm g i z) ∈ A := by
  simp [activeLayers]

@[simp] theorem mem_activePointSet {d n k : ℕ} (g : Geometry d n)
    (A : Finset (Fin k × g.F)) (z : Fin d → g.F) :
    z ∈ activePointSet g A ↔ d ≤ (activeLayers g A z).card := by
  simp [activePointSet]

/-- Every candidate point admits `d` distinct active layers. -/
theorem exists_active_layers {d n k : ℕ} (g : Geometry d n)
    (A : Finset (Fin k × g.F)) {z : Fin d → g.F}
    (hz : z ∈ activePointSet g A) :
    ∃ layers : Fin d ↪ Fin k, ∀ j, (layers j, fixedForm g (layers j) z) ∈ A := by
  classical
  have hc : Fintype.card (Fin d) ≤ (activeLayers g A z).card := by
    simpa using (mem_activePointSet g A z).mp hz
  obtain ⟨layers, hlayers⟩ := Function.Embedding.exists_of_card_le_finset hc
  refine ⟨layers, fun j => (mem_activeLayers g A z (layers j)).mp ?_⟩
  exact hlayers ⟨j, rfl⟩

/-- Choosing `d` active level pairs determines a point, so `|W_A| ≤ |A|^d`.
This statement depends only on the fixed forms, before sampling any random forms. -/
theorem activePointSet_card_le {d n k : ℕ} (g : Geometry d n)
    (hk : k ≤ fieldSize d n) (A : Finset (Fin k × g.F)) :
    (activePointSet g A).card ≤ A.card ^ d := by
  classical
  have hchoose : ∀ z : activePointSet g A,
      ∃ layers : Fin d ↪ Fin k,
        ∀ j, (layers j, fixedForm g (layers j) z.val) ∈ A :=
    fun z => exists_active_layers g A z.property
  choose layers hlayers using hchoose
  let encode : activePointSet g A → (Fin d → A) := fun z j =>
    ⟨(layers z j, fixedForm g (layers z j) z.val), hlayers z j⟩
  have hinj : Function.Injective encode := by
    intro z z' heq
    apply Subtype.ext
    apply eq_of_fixedForm_eq g hk (layers z)
    intro j
    have hj := congrFun heq j
    have hi : layers z j = layers z' j :=
      congrArg (fun p : A => p.val.1) hj
    have hv : fixedForm g (layers z j) z.val = fixedForm g (layers z' j) z'.val :=
      congrArg (fun p : A => p.val.2) hj
    simpa only [← hi] using hv
  have hc := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] using hc

end ExpandingCodes.PolynomialStretch

end FlattenModule24

/-! Inlined whole module: ExpandingCodes.Construction.Peeling -/
section FlattenModule25


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- Neighbors of a row set in an arbitrary graph with one neighbor per layer. -/
noncomputable def layeredNeighbors {I V : Type*} {k : ℕ}
    (f : I → Fin k → V) (S : Finset I) : Finset (Fin k × V) := by
  classical
  exact S.biUnion (fun z => Finset.univ.image (fun i => (i, f z i)))

/-- Layers in which a row has a second row with the same neighbor. -/
noncomputable def collisionLayers {I V : Type*} {k : ℕ}
    (f : I → Fin k → V) (S : Finset I) (z : I) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (fun i => ∃ z' ∈ S, z' ≠ z ∧ f z' i = f z i)

@[simp] theorem mem_layeredNeighbors {I V : Type*} {k : ℕ}
    (f : I → Fin k → V) (S : Finset I) (p : Fin k × V) :
    p ∈ layeredNeighbors f S ↔ ∃ z ∈ S, f z p.1 = p.2 := by
  classical
  rcases p with ⟨l, v⟩
  simp only [layeredNeighbors, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨z, hz, i, hi, hv⟩
    subst i
    exact ⟨z, hz, hv⟩
  · rintro ⟨z, hz, hv⟩
    exact ⟨z, hz, l, rfl, hv⟩

@[simp] theorem mem_collisionLayers {I V : Type*} {k : ℕ}
    (f : I → Fin k → V) (S : Finset I) (z : I) (i : Fin k) :
    i ∈ collisionLayers f S z ↔ ∃ z' ∈ S, z' ≠ z ∧ f z' i = f z i := by
  classical
  simp [collisionLayers]

@[simp] theorem layeredNeighbors_empty {I V : Type*} {k : ℕ}
    (f : I → Fin k → V) : layeredNeighbors f ∅ = ∅ := by
  classical
  ext p
  simp

/-- The exact neighbor-deficit increment when one row is removed. -/
theorem layeredNeighbors_erase_card {I V : Type*} {k : ℕ}
    (f : I → Fin k → V) (S : Finset I) {z : I} (hz : z ∈ S) :
    (layeredNeighbors f S).card + (collisionLayers f S z).card =
      (layeredNeighbors f (S.erase z)).card + k := by
  classical
  let R : Finset (Fin k × V) := Finset.univ.image (fun i => (i, f z i))
  have hR : R.card = k := by
    rw [Finset.card_image_of_injective _ (fun i j h => congrArg Prod.fst h)]
    exact Finset.card_fin k
  have hu : layeredNeighbors f S = layeredNeighbors f (S.erase z) ∪ R := by
    ext ⟨l, v⟩
    simp only [mem_layeredNeighbors, Finset.mem_union, R, Finset.mem_image,
      Finset.mem_univ, true_and, Prod.mk.injEq, Finset.mem_erase]
    constructor
    · rintro ⟨w, hw, hf⟩
      by_cases h : w = z
      · subst w
        exact Or.inr ⟨l, rfl, hf⟩
      · exact Or.inl ⟨w, ⟨h, hw⟩, hf⟩
    · rintro (⟨w, ⟨_, hw⟩, hf⟩ | ⟨i, hi, hf⟩)
      · exact ⟨w, hw, hf⟩
      · subst i
        exact ⟨z, hz, hf⟩
  have hi : layeredNeighbors f (S.erase z) ∩ R =
      (collisionLayers f S z).image (fun i => (i, f z i)) := by
    ext ⟨l, v⟩
    simp only [Finset.mem_inter, mem_layeredNeighbors, Finset.mem_erase,
      R, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq,
      mem_collisionLayers]
    constructor
    · rintro ⟨⟨w, ⟨hwz, hw⟩, hfw⟩, i, hi, hfi⟩
      subst i
      exact ⟨l, ⟨w, hw, hwz, hfw.trans hfi.symm⟩, rfl, hfi⟩
    · rintro ⟨i, ⟨w, hw, hwz, hfw⟩, hi, hfi⟩
      subst i
      exact ⟨⟨w, ⟨hwz, hw⟩, hfw.trans hfi⟩, l, rfl, hfi⟩
  have hic : (layeredNeighbors f (S.erase z) ∩ R).card =
      (collisionLayers f S z).card := by
    rw [hi, Finset.card_image_of_injective _ (fun i j h => congrArg Prod.fst h)]
  rw [hu, ← hic, Finset.card_union_add_card_inter, hR]

/-- Repeated removal of rows colliding in fewer than `d` layers proves expansion. -/
theorem layeredNeighbors_expansion_of_peeling {I V : Type*} {d k : ℕ}
    (f : I → Fin k → V) (S : Finset I)
    (h : ∀ T ⊆ S, T.Nonempty → ∃ z ∈ T, (collisionLayers f T z).card < d) :
    (k + 1) * S.card ≤ (layeredNeighbors f S).card + d * S.card := by
  classical
  revert h
  refine Finset.strongInductionOn S ?_
  intro S ih h
  by_cases he : S = ∅
  · subst S
    simp
  · obtain ⟨z, hz, hzc⟩ := h S (Finset.Subset.refl S) (Finset.nonempty_iff_ne_empty.mpr he)
    have herase : S.erase z ⊂ S := Finset.erase_ssubset hz
    have hsmall := ih (S.erase z) herase (fun T hT hne =>
      h T (Finset.Subset.trans hT (Finset.erase_subset _ _)) hne)
    have hcard := Finset.card_erase_add_one hz
    have hneighbor := layeredNeighbors_erase_card f S hz
    nlinarith

/-- Failure of expansion has a nonempty subset every row of which collides in at least `d` layers. -/
theorem exists_collision_core {I V : Type*} {d k : ℕ}
    (f : I → Fin k → V) (S : Finset I)
    (hbad : (layeredNeighbors f S).card + d * S.card < (k + 1) * S.card) :
    ∃ T ⊆ S, T.Nonempty ∧ ∀ z ∈ T, d ≤ (collisionLayers f T z).card := by
  classical
  by_contra hnone
  have hpeel : ∀ T ⊆ S, T.Nonempty → ∃ z ∈ T, (collisionLayers f T z).card < d := by
    intro T hT hne
    by_contra h
    push Not at h
    exact hnone ⟨T, hT, hne, h⟩
  exact (not_lt_of_ge (layeredNeighbors_expansion_of_peeling f S hpeel)) hbad

/-- The layered description agrees exactly with the canonical preliminary matrix. -/
theorem preliminary_neighbors_eq {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (S : Finset (Fin (rowCount d n))) :
    neighbors (preliminary g s) S =
      layeredNeighbors (fun z i => address g s i (g.rowOrder z)) S := by
  classical
  ext p
  simp only [neighbors, QuantumExpander.Decoder.nbhdA, Finset.mem_filter,
    Finset.mem_univ, true_and, mem_layeredNeighbors, preliminary]
  congr! 2
  simp

/-- Exact canonical failure produces a collision core without changing the row enumeration. -/
theorem preliminary_bad_has_collision_core (ε : ℝ) (n : ℕ)
    (g : Geometry (dimension ε) n) (s : Forms g.F (dimension ε) (arity ε))
    (hbad : ¬ PreliminaryGood ε n g s) :
    ∃ S : Finset (Fin (rowCount (dimension ε) n)),
      S.Nonempty ∧ (S.card : ℝ) ≤ (n : ℝ) ^ (1 - ε) ∧
      ∀ z ∈ S, dimension ε ≤
        (collisionLayers (fun z i => address g s i (g.rowOrder z)) S z).card := by
  classical
  unfold PreliminaryGood at hbad
  push Not at hbad
  obtain ⟨S, hsize, hbad⟩ := hbad
  rw [preliminary_neighbors_eq] at hbad
  have hn : (layeredNeighbors (fun z i => address g s i (g.rowOrder z)) S).card +
      dimension ε * S.card < (arity ε + 1) * S.card := by
    have hr : ((layeredNeighbors (fun z i => address g s i (g.rowOrder z)) S).card : ℝ) +
        (dimension ε : ℝ) * S.card < ((arity ε : ℝ) + 1) * S.card := by
      nlinarith
    exact_mod_cast hr
  obtain ⟨T, hT, hne, hc⟩ := exists_collision_core _ S hn
  refine ⟨T, hne, ?_, hc⟩
  exact le_trans (Nat.cast_le.mpr (Finset.card_le_card hT)) hsize

/-- Level pairs supporting at least one collision among the chosen rows. -/
noncomputable def preliminaryActivePairs {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (S : Finset (Fin (rowCount d n))) : Finset (Fin k × g.F) :=
  Finset.univ.filter (fun p => ∃ z ∈ S, ∃ z' ∈ S, z ≠ z' ∧
    fixedForm g p.1 (g.rowOrder z) = p.2 ∧
    address g s p.1 (g.rowOrder z) = address g s p.1 (g.rowOrder z'))

@[simp] theorem mem_preliminaryActivePairs {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (S : Finset (Fin (rowCount d n))) (p : Fin k × g.F) :
    p ∈ preliminaryActivePairs g s S ↔ ∃ z ∈ S, ∃ z' ∈ S, z ≠ z' ∧
      fixedForm g p.1 (g.rowOrder z) = p.2 ∧
      address g s p.1 (g.rowOrder z) = address g s p.1 (g.rowOrder z') := by
  classical
  simp [preliminaryActivePairs]

/-- An active level pair consumes at least two distinct row-layer incidences. -/
theorem preliminaryActivePairs_card_le {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (S : Finset (Fin (rowCount d n))) :
    2 * (preliminaryActivePairs g s S).card ≤ k * S.card := by
  classical
  let I := S.product (Finset.univ : Finset (Fin k))
  let f : (Fin (rowCount d n) × Fin k) → Fin k × g.F :=
    fun zi => (zi.2, fixedForm g zi.2 (g.rowOrder zi.1))
  have hfiber : ∀ p ∈ preliminaryActivePairs g s S,
      2 ≤ (I.filter (fun zi => f zi = p)).card := by
    intro p hp
    obtain ⟨z, hz, z', hz', hne, hf, ha⟩ := (mem_preliminaryActivePairs g s S p).mp hp
    have hfirst : fixedForm g p.1 (g.rowOrder z) =
        fixedForm g p.1 (g.rowOrder z') := congrArg Prod.fst ha
    have htwo : 1 < (I.filter (fun zi => f zi = p)).card := by
      apply Finset.one_lt_card.mpr
      refine ⟨(z, p.1), ?_, (z', p.1), ?_, ?_⟩
      · simp [I, f, hz, hf]
      · simp [I, f, hz', ← hfirst, hf]
      · intro he
        exact hne (congrArg Prod.fst he)
    omega
  calc
    2 * (preliminaryActivePairs g s S).card =
        ∑ _p ∈ preliminaryActivePairs g s S, 2 := by simp [mul_comm]
    _ ≤ ∑ p ∈ preliminaryActivePairs g s S,
        (I.filter (fun zi => f zi = p)).card := Finset.sum_le_sum hfiber
    _ = (I.filter (fun zi => f zi ∈ preliminaryActivePairs g s S)).card :=
      Finset.sum_card_fiberwise_eq_card_filter I (preliminaryActivePairs g s S) f
    _ ≤ I.card := Finset.card_filter_le _ _
    _ = k * S.card := by simp [I, mul_comm]

/-- Every collision layer is one of the point's active fixed-form layers. -/
theorem collisionLayers_subset_activeLayers {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (S : Finset (Fin (rowCount d n)))
    {z : Fin (rowCount d n)} (hz : z ∈ S) :
    collisionLayers (fun z i => address g s i (g.rowOrder z)) S z ⊆
      activeLayers g (preliminaryActivePairs g s S) (g.rowOrder z) := by
  intro i hi
  obtain ⟨z', hz', hne, ha⟩ := (mem_collisionLayers _ S z i).mp hi
  exact (mem_activeLayers _ _ _ _).mpr ((mem_preliminaryActivePairs g s S _).mpr
    ⟨z, hz, z', hz', hne.symm, rfl, ha.symm⟩)

/-- All rows of a collision core lie in the deterministic candidate set `W_A`. -/
theorem collision_core_rows_mem_activePointSet {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (S : Finset (Fin (rowCount d n)))
    (hcore : ∀ z ∈ S, d ≤
      (collisionLayers (fun z i => address g s i (g.rowOrder z)) S z).card) :
    ∀ z ∈ S, g.rowOrder z ∈ activePointSet g (preliminaryActivePairs g s S) := by
  intro z hz
  exact (mem_activePointSet _ _ _).mpr ((hcore z hz).trans
    (Finset.card_le_card (collisionLayers_subset_activeLayers g s S hz)))

/-- Positive-dimensional collision cores activate at least one level pair. -/
theorem collision_core_activePairs_nonempty {d n k : ℕ} (g : Geometry d n)
    (hd : 0 < d) (s : Forms g.F d k) (S : Finset (Fin (rowCount d n)))
    (hne : S.Nonempty) (hcore : ∀ z ∈ S, d ≤
      (collisionLayers (fun z i => address g s i (g.rowOrder z)) S z).card) :
    (preliminaryActivePairs g s S).Nonempty := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (hd.trans_le (hcore z hz))
  exact ⟨(i, fixedForm g i (g.rowOrder z)),
    (mem_activeLayers _ _ _ _).mp (collisionLayers_subset_activeLayers g s S hz hi)⟩

end ExpandingCodes.PolynomialStretch

end FlattenModule25

/-! Inlined whole module: ExpandingCodes.Probability.UniformLinear -/
section FlattenModule26



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

theorem uniformProb_sum_mul_eq {I F : Type*} [Fintype I] [DecidableEq I]
    [Field F] [Fintype F]
    (z : I → F) (hz : z ≠ 0) (y : F) :
    uniformProb (fun a : I → F => ∑ i, a i * z i = y) =
      1 / (Fintype.card F : ℝ) := by
  classical
  let f : (I → F) →+ F :=
    { toFun := fun a => ∑ i, a i * z i
      map_zero' := by simp
      map_add' := by intro a b; simp [add_mul, Finset.sum_add_distrib] }
  obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
    simpa only [ne_eq, funext_iff, not_forall, Pi.zero_apply] using hz
  have hf : Function.Surjective f := by
    intro t
    refine ⟨Pi.single j (t / z j), ?_⟩
    simp [f, Pi.single_apply, ite_mul, hj]
  exact uniformProb_addHom_eq f hf y

theorem uniformProb_sum_mul_collision {I F : Type*} [Fintype I] [DecidableEq I]
    [Field F] [Fintype F]
    (z z' : I → F) (hne : z ≠ z') :
    uniformProb (fun a : I → F => ∑ i, a i * z i = ∑ i, a i * z' i) =
      1 / (Fintype.card F : ℝ) := by
  have hz : z - z' ≠ 0 := sub_ne_zero.mpr hne
  calc
    _ = uniformProb (fun a : I → F => ∑ i, a i * (z - z') i = 0) := by
      apply uniformProb_congr
      intro a
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_eq_zero]
    _ = _ := uniformProb_sum_mul_eq (z - z') hz 0

theorem uniformProb_linearForm_collision {F : Type*} [Field F] [Fintype F]
    {d : ℕ} (z z' : Fin d → F) (hne : z ≠ z') :
    uniformProb (fun a : Fin d → F => linearForm a z = linearForm a z') =
      1 / (Fintype.card F : ℝ) := by
  simpa only [linearForm] using uniformProb_sum_mul_collision z z' hne

theorem uniformProb_two_linearForm_collision {F : Type*} [Field F] [Fintype F]
    {d : ℕ} (z z' : Fin d → F) (hne : z ≠ z') :
    uniformProb (fun a : Fin 2 → Fin d → F =>
      linearForm (a 0) z = linearForm (a 0) z' ∧
      linearForm (a 1) z = linearForm (a 1) z') =
      1 / (Fintype.card F : ℝ) ^ 2 := by
  have hp := uniformProb_pi (fun _ : Fin 2 =>
    fun a : Fin d → F => linearForm a z = linearForm a z')
  have he : (fun a : Fin 2 → Fin d → F =>
      ∀ j, linearForm (a j) z = linearForm (a j) z') =
      (fun a => linearForm (a 0) z = linearForm (a 0) z' ∧
        linearForm (a 1) z = linearForm (a 1) z') := by
    funext a
    simp only [Fin.forall_fin_two]
  rw [he] at hp
  calc
    _ = ∏ _j : Fin 2, uniformProb (fun a : Fin d → F =>
        linearForm a z = linearForm a z') := by
      exact hp
    _ = _ := by
      simp [uniformProb_linearForm_collision z z' hne, pow_two]

/-- Re-index the exact canonical sampler forms by independent layer/level pairs. -/
def formsPairEquiv (F : Type*) (d k : ℕ) :
    Forms F d k ≃ ((Fin k × F) → Fin 2 → Fin d → F) where
  toFun s p j := s j p.1 p.2
  invFun s j i a := s (i, a) j
  left_inv _ := rfl
  right_inv _ := rfl

theorem uniformProb_forms_events {F : Type*} [Field F] [Fintype F]
    {d k : ℕ} (A : Finset (Fin k × F))
    (E : (Fin k × F) → (Fin 2 → Fin d → F) → Prop) :
    uniformProb (fun s : Forms F d k =>
      ∀ p ∈ A, E p (fun j => s j p.1 p.2)) =
      ∏ p ∈ A, uniformProb (E p) := by
  rw [← uniformProb_pi_finset A E]
  exact uniformProb_equiv (formsPairEquiv F d k)
    (fun s => ∀ p ∈ A, E p (s p))


















end ExpandingCodes.PolynomialStretch

end FlattenModule26

/-! Inlined whole module: ExpandingCodes.Probability.FiniteEvents -/
section FlattenModule27


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

theorem uniformProb_mono {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {E F : Ω → Prop} (h : ∀ x, E x → F x) : uniformProb E ≤ uniformProb F := by
  classical
  rw [uniformProb_eq_card_filter, uniformProb_eq_card_filter]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (show (Finset.univ.filter E) ⊆ Finset.univ.filter F by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h x (Finset.mem_filter.mp hx).2⟩)

theorem uniformProb_exists_finset {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    (s : Finset ι) (E : ι → Ω → Prop) :
    uniformProb (fun x => ∃ i ∈ s, E i x) ≤ ∑ i ∈ s, uniformProb (E i) := by
  classical
  simp_rw [uniformProb_eq_card_filter]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hc := Finset.card_biUnion_le (s := s)
    (t := fun i => Finset.univ.filter (E i))
  have hr : ((s.biUnion (fun i => Finset.univ.filter (E i))).card : ℝ) ≤
      ∑ i ∈ s, ((Finset.univ.filter (E i)).card : ℝ) := by exact_mod_cast hc
  convert hr using 1
  · rfl
  · apply congrArg (fun A : Finset Ω => (A.card : ℝ))
    ext x
    simp

end ExpandingCodes.PolynomialStretch

end FlattenModule27

/-! Inlined whole module: ExpandingCodes.Probability.PreliminaryCounting -/
section FlattenModule28





set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- A pair of sampled linear forms collides on some distinct pair of candidates. -/
noncomputable def candidateCollision {F : Type*} [Field F] {d : ℕ}
    (W : Finset (Fin d → F)) (a : Fin 2 → Fin d → F) : Prop :=
  ∃ z ∈ W, ∃ z' ∈ W, z ≠ z' ∧
    linearForm (a 0) z = linearForm (a 0) z' ∧
    linearForm (a 1) z = linearForm (a 1) z'

/-- All prescribed active pairs have distinct collision witnesses in deterministic `W_A`. -/
noncomputable def activeWitnessEvent {d n k : ℕ} (g : Geometry d n)
    (A : Finset (Fin k × g.F)) (s : Forms g.F d k) : Prop :=
  ∀ p ∈ A, candidateCollision (activePointSet g A) (fun j => s j p.1 p.2)

/-- A union bound over ordered pairs of candidates. -/
theorem uniformProb_candidateCollision_le {F : Type*} [Field F] [Fintype F]
    {d : ℕ} (W : Finset (Fin d → F)) :
    uniformProb (candidateCollision W) ≤ (W.card : ℝ) ^ 2 / (Fintype.card F : ℝ) ^ 2 := by
  classical
  let E := fun p : (Fin d → F) × (Fin d → F) =>
    fun a : Fin 2 → Fin d → F => p.1 ≠ p.2 ∧
      linearForm (a 0) p.1 = linearForm (a 0) p.2 ∧
      linearForm (a 1) p.1 = linearForm (a 1) p.2
  have hE : ∀ p, uniformProb (E p) ≤ 1 / (Fintype.card F : ℝ) ^ 2 := by
    intro p
    by_cases hne : p.1 ≠ p.2
    · have heq : uniformProb (E p) = uniformProb (fun a : Fin 2 → Fin d → F =>
          linearForm (a 0) p.1 = linearForm (a 0) p.2 ∧
          linearForm (a 1) p.1 = linearForm (a 1) p.2) := by
        apply uniformProb_congr
        intro a
        change (_ ∧ _) ↔ _
        exact ⟨fun h => h.2, fun h => ⟨hne, h⟩⟩
      rw [heq, uniformProb_two_linearForm_collision _ _ hne]
    · have heq : uniformProb (E p) = 0 := by
        rw [uniformProb_eq_card_filter]
        simp [E, hne]
      rw [heq]
      positivity
  have heq : uniformProb (candidateCollision W) =
      uniformProb (fun a => ∃ p ∈ W.product W, E p a) := by
    apply uniformProb_congr
    intro a
    simp only [candidateCollision, Finset.mem_product, E]
    aesop
  rw [heq]
  calc
    _ ≤ ∑ p ∈ W.product W, uniformProb (E p) := uniformProb_exists_finset _ _
    _ ≤ ∑ _p ∈ W.product W, 1 / (Fintype.card F : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun p _ => hE p)
    _ = _ := by simp [pow_two, div_eq_mul_inv, mul_assoc]

/-- Finite witness counting, with independence even when witness pairs overlap. -/
theorem uniformProb_activeWitnessEvent_le {d n k : ℕ} (g : Geometry d n)
    (hk : k ≤ fieldSize d n) (A : Finset (Fin k × g.F)) :
    uniformProb (activeWitnessEvent g A) ≤
      ((A.card : ℝ) ^ (2 * d) / (fieldSize d n : ℝ) ^ 2) ^ A.card := by
  classical
  rw [show activeWitnessEvent g A = (fun s : Forms g.F d k =>
    ∀ p ∈ A, candidateCollision (activePointSet g A) (fun j => s j p.1 p.2)) from rfl]
  rw [uniformProb_forms_events]
  have hc : ((activePointSet g A).card : ℝ) ≤ (A.card : ℝ) ^ d := by
    exact_mod_cast activePointSet_card_le g hk A
  have hq : Fintype.card g.F = fieldSize d n := geometry_card g
  calc
    _ ≤ ∏ _p ∈ A, ((A.card : ℝ) ^ (2 * d) / (fieldSize d n : ℝ) ^ 2) := by
      apply Finset.prod_le_prod
      · intro p hp
        rw [uniformProb_eq_card_filter]
        positivity
      · intro p hp
        have hw := uniformProb_candidateCollision_le (activePointSet g A)
        rw [hq] at hw
        apply hw.trans
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc
          ((activePointSet g A).card : ℝ) ^ 2 ≤ ((A.card : ℝ) ^ d) ^ 2 := by
            gcongr
          _ = (A.card : ℝ) ^ (2 * d) := by rw [← pow_mul, Nat.mul_comm]
    _ = _ := by simp [div_pow]

/-- The canonical failure event is covered by nonempty active sets and their witnesses. -/
theorem preliminary_bad_implies_activeWitnessEvent (ε : ℝ) (n : ℕ)
    (g : Geometry (dimension ε) n) (hd : 0 < dimension ε)
    (s : Forms g.F (dimension ε) (arity ε))
    (hbad : ¬ PreliminaryGood ε n g s) :
    ∃ A : Finset (Fin (arity ε) × g.F), A.Nonempty ∧
      (A.card : ℝ) ≤ (arity ε : ℝ) * (n : ℝ) ^ (1 - ε) ∧ activeWitnessEvent g A s := by
  classical
  obtain ⟨S, hne, hsize, hcore⟩ := preliminary_bad_has_collision_core ε n g s hbad
  let A := preliminaryActivePairs g s S
  have hA : A.Nonempty := collision_core_activePairs_nonempty g hd s S hne hcore
  have hc : (A.card : ℝ) ≤ (arity ε : ℝ) * S.card := by
    have hi := preliminaryActivePairs_card_le g s S
    have hi' : 2 * (A.card : ℝ) ≤ (arity ε : ℝ) * S.card := by exact_mod_cast hi
    nlinarith [show 0 ≤ (A.card : ℝ) from Nat.cast_nonneg _]
  refine ⟨A, hA, hc.trans (mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg _)), ?_⟩
  intro p hp
  obtain ⟨z, hz, z', hz', hneq, hf, ha⟩ := (mem_preliminaryActivePairs g s S p).mp hp
  have hw := collision_core_rows_mem_activePointSet g s S hcore
  have hf' : fixedForm g p.1 (g.rowOrder z') = p.2 := by
    have hh : fixedForm g p.1 (g.rowOrder z) =
        fixedForm g p.1 (g.rowOrder z') := congrArg Prod.fst ha
    exact hh.symm.trans hf
  refine ⟨g.rowOrder z, hw z hz, g.rowOrder z', hw z' hz',
    fun he => hneq (g.rowOrder.injective he), ?_⟩
  change (fixedForm g p.1 (g.rowOrder z),
      linearForm (s 0 p.1 (fixedForm g p.1 (g.rowOrder z))) (g.rowOrder z),
      linearForm (s 1 p.1 (fixedForm g p.1 (g.rowOrder z))) (g.rowOrder z)) =
    (fixedForm g p.1 (g.rowOrder z'),
      linearForm (s 0 p.1 (fixedForm g p.1 (g.rowOrder z'))) (g.rowOrder z'),
      linearForm (s 1 p.1 (fixedForm g p.1 (g.rowOrder z'))) (g.rowOrder z')) at ha
  simp only [hf, hf', Prod.mk.injEq, true_and] at ha
  exact ha

/-- Union-bound active sets of one fixed cardinality, using the coarse count `(kq)^a`. -/
theorem uniformProb_exists_active_sets_le_pow {d n k : ℕ} (g : Geometry d n)
    (hk : k ≤ fieldSize d n) (a : ℕ) (B : ℝ)
    (hbase : (k : ℝ) * (a : ℝ) ^ (2 * d) / (fieldSize d n : ℝ) ≤ B) :
    uniformProb (fun s : Forms g.F d k =>
      ∃ A ∈ (Finset.univ : Finset (Fin k × g.F)).powersetCard a,
        activeWitnessEvent g A s) ≤ B ^ a := by
  classical
  let C : ℝ := (a : ℝ) ^ (2 * d) / (fieldSize d n : ℝ) ^ 2
  have hC : 0 ≤ C := by positivity
  have hcount : (((Finset.univ : Finset (Fin k × g.F)).powersetCard a).card : ℝ) ≤
      ((k * fieldSize d n : ℕ) : ℝ) ^ a := by
    have hnat : ((Finset.univ : Finset (Fin k × g.F)).powersetCard a).card ≤
        (k * fieldSize d n) ^ a := by
      rw [Finset.card_powersetCard]
      simpa [Fintype.card_prod, geometry_card g] using
        Nat.choose_le_pow (k * fieldSize d n) a
    exact_mod_cast hnat
  calc
    _ ≤ ∑ A ∈ (Finset.univ : Finset (Fin k × g.F)).powersetCard a,
        uniformProb (activeWitnessEvent g A) := uniformProb_exists_finset _ _
    _ ≤ ∑ _A ∈ (Finset.univ : Finset (Fin k × g.F)).powersetCard a, C ^ a := by
      apply Finset.sum_le_sum
      intro A hA
      have ha : A.card = a := (Finset.mem_powersetCard.mp hA).2
      simpa [C, ha] using uniformProb_activeWitnessEvent_le g hk A
    _ = (((Finset.univ : Finset (Fin k × g.F)).powersetCard a).card : ℝ) * C ^ a := by
      simp
    _ ≤ ((k * fieldSize d n : ℕ) : ℝ) ^ a * C ^ a :=
      mul_le_mul_of_nonneg_right hcount (pow_nonneg hC a)
    _ = (((k * fieldSize d n : ℕ) : ℝ) * C) ^ a := (mul_pow _ _ _).symm
    _ ≤ B ^ a := by
      apply pow_le_pow_left₀ (by positivity)
      have hq : (fieldSize d n : ℝ) ≠ 0 := by exact_mod_cast (fieldSize_pos d n).ne'
      have he : (((k * fieldSize d n : ℕ) : ℝ) * C) =
          (k : ℝ) * (a : ℝ) ^ (2 * d) / (fieldSize d n : ℝ) := by
        dsimp [C]
        push_cast
        field_simp
      rw [he]
      exact hbase

/-- Positive finite geometric sums are at most twice their first term when the ratio is at most `1/2`. -/
theorem sum_pow_succ_le_two_mul (B : ℝ) (hB : 0 ≤ B) (hhalf : B ≤ 1 / 2) (N : ℕ) :
    (∑ j ∈ Finset.range N, B ^ (j + 1)) ≤ 2 * B := by
  calc
    _ = B * ∑ j ∈ Finset.range N, B ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ, mul_comm]
    _ ≤ B * ∑ j ∈ Finset.range N, (1 / (2 : ℝ)) ^ j := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply Finset.sum_le_sum
      intro j hj
      exact pow_le_pow_left₀ hB hhalf j
    _ ≤ B * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le N) hB
    _ = _ := mul_comm _ _

/-- A finite, quantitative version of the exact canonical preliminary expansion estimate.
Only the parameter-dependent geometric ratio remains for the asymptotic step. -/
theorem preliminary_bad_prob_le_two_base (ε : ℝ) (n : ℕ)
    (g : Geometry (dimension ε) n) (hd : 0 < dimension ε)
    (hk : arity ε ≤ fieldSize (dimension ε) n)
    (hhalf : (arity ε : ℝ) *
      ((arity ε : ℝ) * (n : ℝ) ^ (1 - ε)) ^ (2 * dimension ε) /
        (fieldSize (dimension ε) n : ℝ) ≤ 1 / 2) :
    uniformProb (fun s : Forms g.F (dimension ε) (arity ε) =>
      ¬ PreliminaryGood ε n g s) ≤
      2 * ((arity ε : ℝ) *
        ((arity ε : ℝ) * (n : ℝ) ^ (1 - ε)) ^ (2 * dimension ε) /
          (fieldSize (dimension ε) n : ℝ)) := by
  classical
  let t : ℝ := (arity ε : ℝ) * (n : ℝ) ^ (1 - ε)
  let N := ⌊t⌋₊
  let B : ℝ := (arity ε : ℝ) * t ^ (2 * dimension ε) /
    (fieldSize (dimension ε) n : ℝ)
  have ht : 0 ≤ t := by positivity
  have hB : 0 ≤ B := by positivity
  have hcover : ∀ s : Forms g.F (dimension ε) (arity ε),
      ¬ PreliminaryGood ε n g s →
      ∃ j ∈ Finset.range N,
        ∃ A ∈ (Finset.univ : Finset (Fin (arity ε) × g.F)).powersetCard (j + 1),
          activeWitnessEvent g A s := by
    intro s hs
    obtain ⟨A, hne, hsize, hevent⟩ := preliminary_bad_implies_activeWitnessEvent ε n g hd s hs
    have hpos : 0 < A.card := Finset.card_pos.mpr hne
    have hcard : A.card ≤ N := Nat.le_floor hsize
    refine ⟨A.card - 1, Finset.mem_range.mpr (by omega), A, ?_, hevent⟩
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ A, by omega⟩
  calc
    _ ≤ uniformProb (fun s : Forms g.F (dimension ε) (arity ε) =>
        ∃ j ∈ Finset.range N,
          ∃ A ∈ (Finset.univ : Finset (Fin (arity ε) × g.F)).powersetCard (j + 1),
            activeWitnessEvent g A s) := uniformProb_mono hcover
    _ ≤ ∑ j ∈ Finset.range N,
        uniformProb (fun s : Forms g.F (dimension ε) (arity ε) =>
          ∃ A ∈ (Finset.univ : Finset (Fin (arity ε) × g.F)).powersetCard (j + 1),
            activeWitnessEvent g A s) := uniformProb_exists_finset _ _
    _ ≤ ∑ j ∈ Finset.range N, B ^ (j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      apply uniformProb_exists_active_sets_le_pow g hk (j + 1) B
      have hjt : ((j + 1 : ℕ) : ℝ) ≤ t :=
        (Nat.cast_le.mpr (Nat.succ_le_of_lt (Finset.mem_range.mp hj))).trans (Nat.floor_le ht)
      dsimp [B]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hjt _
    _ ≤ 2 * B := sum_pow_succ_le_two_mul B hB hhalf N
    _ = _ := rfl

end ExpandingCodes.PolynomialStretch

end FlattenModule28

/-! Inlined whole module: ExpandingCodes.Algebra.ReedMullerDimension -/
section FlattenModule31



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

universe u
























/-- The exponent vector of an exact canonical monomial, as a finitely supported function. -/
noncomputable def reducedMonomialExponent {F : Type*} [Fintype F] {d R : ℕ}
    (a : Monomials F d R) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a.val i).val)

@[simp] theorem reducedMonomialExponent_apply {F : Type*} [Fintype F] {d R : ℕ}
    (a : Monomials F d R) (i : Fin d) :
    reducedMonomialExponent a i = (a.val i).val := rfl







































































end ExpandingCodes.PolynomialStretch

end FlattenModule31

/-! Inlined whole module: ExpandingCodes.Probability.RateLimit -/
section FlattenModule32




set_option autoImplicit false

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace ExpandingCodes.PolynomialStretch























































/-- The mission's field size tends to infinity at every positive fixed dimension. -/
theorem tendsto_fieldSize_atTop (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n => fieldSize d n) atTop atTop := by
  exact tendsto_atTop_mono (fieldSize_lower d) (tendsto_pow_atTop (by omega))












end ExpandingCodes.PolynomialStretch

end FlattenModule32

/-! Inlined whole module: ExpandingCodes.Construction.ExpansionParameters -/
section FlattenModule33



set_option autoImplicit false
open Filter Topology

namespace ExpandingCodes.PolynomialStretch

noncomputable def preliminaryRatio (ε : ℝ) (n : ℕ) : ℝ :=
  (arity ε : ℝ) * ((arity ε : ℝ) * (n : ℝ) ^ (1 - ε)) ^ (2 * dimension ε) /
    fieldSize (dimension ε) n

theorem preliminary_exponent_gap (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    1 / ε < 2 * (dimension ε : ℝ) * ε := by
  have hc : 512 * ε⁻¹ ^ 2 ≤ (⌈512 * ε⁻¹ ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hd : 1024 * ε⁻¹ ^ 2 ≤ (dimension ε : ℝ) := by
    unfold dimension
    push_cast
    linarith
  have hp := mul_le_mul_of_nonneg_right hd (sq_nonneg ε)
  have hi : ε⁻¹ ^ 2 * ε ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hε.1.ne', one_pow]
  have hg : 1 < 2 * (dimension ε : ℝ) * ε ^ 2 := by nlinarith
  apply (div_lt_iff₀ hε.1).2
  nlinarith

theorem preliminaryRatio_le (ε : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    preliminaryRatio ε n ≤ (arity ε : ℝ) ^ (2 * dimension ε + 1) *
      (n : ℝ) ^ (-2 * (dimension ε : ℝ) * ε) := by
  let L := 2 * dimension ε
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : (n : ℝ) ^ L ≤ fieldSize (dimension ε) n := by
    exact_mod_cast fieldSize_lower (dimension ε) n
  have ht : ((n : ℝ) ^ (1 - ε)) ^ L = (n : ℝ) ^ ((1 - ε) * (L : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
  have hr : ((n : ℝ) ^ (1 - ε)) ^ L / (n : ℝ) ^ L =
      (n : ℝ) ^ (-2 * (dimension ε : ℝ) * ε) := by
    rw [ht, ← Real.rpow_natCast (n : ℝ) L, ← Real.rpow_sub hnpos]
    congr 1
    dsimp [L]
    push_cast
    ring
  calc
    preliminaryRatio ε n ≤
        (arity ε : ℝ) * ((arity ε : ℝ) * (n : ℝ) ^ (1 - ε)) ^ L / (n : ℝ) ^ L := by
      apply div_le_div_of_nonneg_left (by positivity) (pow_pos hnpos _) hq
    _ = (arity ε : ℝ) ^ (L + 1) * (((n : ℝ) ^ (1 - ε)) ^ L / (n : ℝ) ^ L) := by
      rw [mul_pow, pow_succ]
      ring
    _ = _ := by rw [hr]

theorem tendsto_preliminaryRatio_scaled (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    Tendsto (fun n : ℕ => preliminaryRatio ε n * (n : ℝ) ^ (1 / ε)) atTop (𝓝 0) := by
  let C : ℝ := (arity ε : ℝ) ^ (2 * dimension ε + 1)
  have hg : 0 < 2 * (dimension ε : ℝ) * ε - 1 / ε := by
    linarith [preliminary_exponent_gap ε hε]
  have hz : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (1 / ε - 2 * (dimension ε : ℝ) * ε))
      atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop hg).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply, neg_sub, mul_zero] using tendsto_const_nhds.mul hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz
  · exact Eventually.of_forall (fun n => by unfold preliminaryRatio; positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc
      _ ≤ C * (n : ℝ) ^ (-2 * (dimension ε : ℝ) * ε) * (n : ℝ) ^ (1 / ε) :=
        mul_le_mul_of_nonneg_right (preliminaryRatio_le ε n hn) (by positivity)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hnpos]
        congr 2
        ring

theorem tendsto_preliminaryRatio (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    Tendsto (preliminaryRatio ε) atTop (𝓝 0) := by
  have hg : 0 < 2 * (dimension ε : ℝ) * ε := by
    have hd := dimension_ge_four ε hε
    have hd' : (4 : ℝ) ≤ dimension ε := by exact_mod_cast hd
    have hdpos : (0 : ℝ) < dimension ε := lt_of_lt_of_le (by norm_num) hd'
    exact mul_pos (mul_pos (by norm_num) hdpos) hε.1
  have hz := (tendsto_rpow_neg_atTop hg).comp tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ => (arity ε : ℝ) ^ (2 * dimension ε + 1) *
      (n : ℝ) ^ (-2 * (dimension ε : ℝ) * ε)) atTop (𝓝 0) := by
    simpa [Function.comp_apply, neg_mul] using tendsto_const_nhds.mul hz
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
  · exact Eventually.of_forall (fun n => by unfold preliminaryRatio; positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact preliminaryRatio_le ε n hn

theorem eventually_preliminary_parameters (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, arity ε ≤ fieldSize (dimension ε) n ∧ preliminaryRatio ε n ≤ 1 / 2 := by
  have hd : 0 < dimension ε := (by decide : 0 < 4).trans_le (dimension_ge_four ε hε)
  filter_upwards [(tendsto_fieldSize_atTop (dimension ε) hd).eventually
      (eventually_ge_atTop (arity ε)),
    (tendsto_preliminaryRatio ε hε).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with n hk hb
  exact ⟨hk, hb.le⟩

end ExpandingCodes.PolynomialStretch

end FlattenModule33

/-! Inlined whole module: ExpandingCodes.Probability.PreliminaryExpansion -/
section FlattenModule34



set_option autoImplicit false
open scoped Classical
open Filter Topology

namespace ExpandingCodes.PolynomialStretch

/-- The exact canonical little-o assertion for preliminary expansion, uniformly in public geometry. -/
theorem preliminary_expansion_limit (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2)
    (g : ∀ n, Geometry (dimension ε) n) :
    Tendsto (fun n =>
      uniformProb (fun s : Forms (g n).F (dimension ε) (arity ε) =>
        ¬ PreliminaryGood ε n (g n) s) * (n : ℝ) ^ (1 / ε))
      atTop (nhds 0) := by
  have hd : 0 < dimension ε := (by decide : 0 < 4).trans_le (dimension_ge_four ε hε)
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ uniformProb (fun s : Forms (g n).F (dimension ε) (arity ε) =>
        ¬ PreliminaryGood ε n (g n) s) * (n : ℝ) ^ (1 / ε) := by
    apply Eventually.of_forall
    intro n
    rw [uniformProb_eq_card_filter]
    positivity
  have hupper : ∀ᶠ n : ℕ in atTop,
      uniformProb (fun s : Forms (g n).F (dimension ε) (arity ε) =>
        ¬ PreliminaryGood ε n (g n) s) * (n : ℝ) ^ (1 / ε) ≤
      2 * (preliminaryRatio ε n * (n : ℝ) ^ (1 / ε)) := by
    filter_upwards [eventually_preliminary_parameters ε hε] with n hn
    have hfinite := preliminary_bad_prob_le_two_base ε n (g n) hd hn.1 hn.2
    calc
      _ ≤ (2 * preliminaryRatio ε n) * (n : ℝ) ^ (1 / ε) :=
        mul_le_mul_of_nonneg_right hfinite (by positivity)
      _ = _ := mul_assoc _ _ _
  apply squeeze_zero' hnonneg hupper
  simpa only [mul_zero] using (tendsto_preliminaryRatio_scaled ε hε).const_mul 2

end ExpandingCodes.PolynomialStretch

end FlattenModule34

/-! Inlined whole module: ExpandingCodes.Probability.HashOccupancy -/
section FlattenModule35


set_option autoImplicit false
set_option maxRecDepth 2048
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- Uniform probability on a finite product is the average of the fiber probabilities. -/
theorem uniformProb_prod_fibers {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (E : A × B → Prop) :
    uniformProb E = (∑ a : A, uniformProb (fun b : B => E (a, b))) / Fintype.card A := by
  classical
  simp_rw [uniformProb_eq_card_filter]
  have hc : ((Finset.univ.filter E).card : ℝ) =
      ∑ a : A, ((Finset.univ.filter (fun b : B => E (a, b))).card : ℝ) := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
    push_cast
    rfl
  rw [hc, Fintype.card_prod, Nat.cast_mul]
  simp_rw [← Finset.sum_div]
  ring

/-- A uniform upper bound on every fiber bounds the product event. -/
theorem uniformProb_prod_le_of_fibers {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (E : A × B → Prop) (C : ℝ)
    (h : ∀ a, uniformProb (fun b : B => E (a, b)) ≤ C) : uniformProb E ≤ C := by
  rw [uniformProb_prod_fibers]
  have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hc).2
  calc
    _ ≤ ∑ _a : A, C := Finset.sum_le_sum (fun a _ => h a)
    _ = _ := by simp [mul_comm]

/-- Every finite image has a subset of distinct representatives. -/
theorem exists_image_representatives {I V : Type*} [DecidableEq I] [DecidableEq V] (D : Finset I) (f : I → V) :
    ∃ R ⊆ D, R.card = (D.image f).card ∧ R.image f = D.image f := by
  classical
  obtain ⟨R, hR, hinj, him⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn (D : Set I) (D.image f)
      (by simpa using (Set.surjOn_image f (D : Set I)))
  refine ⟨R, hR, ?_, him⟩
  rw [← him, Finset.card_image_of_injOn hinj]

/-- If an image has at least `r` fewer values, a set of `|D|-r` representatives covers it. -/
theorem exists_image_cover_of_loss {I V : Type*} [DecidableEq I] [DecidableEq V] (D : Finset I) (f : I → V) (r : ℕ)
    (hloss : (D.image f).card + r ≤ D.card) :
    ∃ R ∈ D.powersetCard (D.card - r), D.image f ⊆ R.image f := by
  classical
  obtain ⟨R, hRD, hc, hi⟩ := exists_image_representatives D f
  obtain ⟨T, hRT, hTD, hT⟩ := Finset.exists_subsuperset_card_eq hRD
    (by omega : R.card ≤ D.card - r) (Nat.sub_le _ _)
  exact ⟨T, Finset.mem_powersetCard.mpr ⟨hTD, hT⟩, hi ▸ Finset.image_subset_image hRT⟩

/-- Once representative hash values are fixed, all other prescribed inputs hit their image
with probability at most one factor `|R|/|V|` per input. -/
theorem uniformProb_image_covered_le {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
    [Nonempty V] (D R : Finset I) (hRD : R ⊆ D) :
    uniformProb (fun f : I → V => D.image f ⊆ R.image f) ≤
      ((R.card : ℝ) / Fintype.card V) ^ (D.card - R.card) := by
  classical
  let J := {i : I // i ∉ R}
  let A : Finset J := (D \ R).attach.image
    (fun i => (⟨i.val, (Finset.mem_sdiff.mp i.property).2⟩ : J))
  have hAc : A.card = D.card - R.card := by
    rw [Finset.card_image_of_injective]
    · simp only [Finset.card_attach, Finset.card_sdiff_of_subset hRD]
    · intro i j h
      exact Subtype.ext (congrArg (fun x : J => x.val) h)
  let e := Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ R) (fun _ => V)
  rw [← uniformProb_equiv e.symm]
  apply uniformProb_prod_le_of_fibers
  intro a
  have hcov : ∀ c : J → V,
      D.image (e.symm (a, c)) ⊆ R.image (e.symm (a, c)) →
      ∀ i ∈ A, c i ∈ Finset.univ.image a := by
    intro c hc i hi
    obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hi
    have hjD : j.val ∈ D := (Finset.mem_sdiff.mp j.property).1
    have hx := hc (Finset.mem_image.mpr ⟨j.val, hjD, rfl⟩)
    obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨⟨w, hw⟩, Finset.mem_univ _, ?_⟩
    subst i
    simpa [e, Equiv.piEquivPiSubtypeProd, hw, (Finset.mem_sdiff.mp j.property).2]
      using hwe
  calc
    _ ≤ uniformProb (fun c : J → V => ∀ i ∈ A, c i ∈ Finset.univ.image a) :=
      uniformProb_mono hcov
    _ = ∏ _i ∈ A, uniformProb (fun v : V => v ∈ Finset.univ.image a) :=
      uniformProb_pi_finset A (fun _ v => v ∈ Finset.univ.image a)
    _ = (((Finset.univ.image a).card : ℝ) / Fintype.card V) ^ A.card := by
      have hp : uniformProb (fun v : V => v ∈ Finset.univ.image a) =
          ((Finset.univ.image a).card : ℝ) / Fintype.card V := by
        rw [uniformProb_eq_card_filter]
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      simp only [hp, Finset.prod_const]
    _ ≤ ((R.card : ℝ) / Fintype.card V) ^ (D.card - R.card) := by
      rw [hAc]
      apply pow_le_pow_left₀ (by positivity)
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (Finset.card_image_le (s := Finset.univ) (f := a)).trans_eq
        (by simp)

/-- Finite occupancy bound for independent values of a full uniformly sampled function.
The witness is a subset of representative inputs, so no adaptively exposed value is assumed
independent of its own past. -/
theorem uniformProb_image_loss_le {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
    [Nonempty V] (D : Finset I) (r : ℕ) :
    uniformProb (fun f : I → V => (D.image f).card + r ≤ D.card) ≤
      (2 : ℝ) ^ D.card * ((D.card : ℝ) / Fintype.card V) ^ r := by
  classical
  by_cases hr : r ≤ D.card
  · have hcover : ∀ f : I → V, (D.image f).card + r ≤ D.card →
        ∃ R ∈ D.powersetCard (D.card - r), D.image f ⊆ R.image f :=
      fun f hf => exists_image_cover_of_loss D f r hf
    calc
      _ ≤ uniformProb (fun f : I → V =>
          ∃ R ∈ D.powersetCard (D.card - r), D.image f ⊆ R.image f) :=
        uniformProb_mono hcover
      _ ≤ ∑ R ∈ D.powersetCard (D.card - r),
          uniformProb (fun f : I → V => D.image f ⊆ R.image f) :=
        uniformProb_exists_finset _ _
      _ ≤ ∑ _R ∈ D.powersetCard (D.card - r),
          ((D.card : ℝ) / Fintype.card V) ^ r := by
        apply Finset.sum_le_sum
        intro R hR
        obtain ⟨hRD, hc⟩ := Finset.mem_powersetCard.mp hR
        have hexp : D.card - R.card = r := by omega
        calc
          _ ≤ ((R.card : ℝ) / Fintype.card V) ^ (D.card - R.card) :=
            uniformProb_image_covered_le D R hRD
          _ ≤ ((D.card : ℝ) / Fintype.card V) ^ r := by
            rw [hexp]
            apply pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact_mod_cast Finset.card_le_card hRD
      _ = ((D.powersetCard (D.card - r)).card : ℝ) *
          ((D.card : ℝ) / Fintype.card V) ^ r := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ D.card * ((D.card : ℝ) / Fintype.card V) ^ r := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (Finset.card_le_card
          (show D.powersetCard (D.card - r) ⊆ D.powerset from by
            intro R hR
            exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hR).1)).trans_eq
          (Finset.card_powerset D)
  · have hzero : uniformProb (fun f : I → V => (D.image f).card + r ≤ D.card) = 0 := by
      have he : uniformProb (fun f : I → V => (D.image f).card + r ≤ D.card) =
          uniformProb (fun _f : I → V => False) := by
        apply uniformProb_congr
        intro f
        constructor
        · intro h
          omega
        · exact False.elim
      rw [he, uniformProb_eq_card_filter]
      simp only [Finset.filter_false, Finset.card_empty, Nat.cast_zero, zero_div]
    rw [hzero]
    positivity

end ExpandingCodes.PolynomialStretch

end FlattenModule35

/-! Inlined whole module: ExpandingCodes.Construction.RowWeight -/
section FlattenModule36


set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

























/-- The column selected by one layer lies in its disjoint block of `b` columns. -/
noncomputable def rowNeighbor {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hfit : k * b ≤ n)
    (z : Fin (rowCount d n)) (i : Fin k) : Fin n :=
  ⟨i.val * b + (h i (address g s i (g.rowOrder z))).val, by
    have hu := (h i (address g s i (g.rowOrder z))).isLt
    have hi : (i.val + 1) * b ≤ k * b := Nat.mul_le_mul_right b i.isLt
    have heq : (i.val + 1) * b = i.val * b + b := by rw [Nat.add_mul, Nat.one_mul]
    omega⟩

theorem rowNeighbor_injective {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hb : 0 < b) (hfit : k * b ≤ n)
    (z : Fin (rowCount d n)) : Function.Injective (rowNeighbor g s h hfit z) := by
  intro i i' heq
  have hquot (j : Fin k) : (rowNeighbor g s h hfit z j).val / b = j.val := by
    change (j.val * b + (h j (address g s j (g.rowOrder z))).val) / b = j.val
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb,
      Nat.div_eq_of_lt (h j (address g s j (g.rowOrder z))).isLt, Nat.zero_add]
  apply Fin.ext
  have heq' := congrArg (fun j : Fin n => j.val / b) heq
  simpa only [hquot] using heq'

/-- A combined row is supported exactly on the columns selected by its layers. -/
theorem combined_row_support {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hfit : k * b ≤ n)
    (z : Fin (rowCount d n)) :
    (Finset.univ.filter fun j => combined g s h z j ≠ 0) =
      Finset.univ.image (rowNeighbor g s h hfit z) := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    combined, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
  constructor
  · rintro ⟨i, u, hj, hu⟩
    refine ⟨i, Fin.ext ?_⟩
    change i.val * b + (h i (address g s i (g.rowOrder z))).val = j.val
    rw [hu]
    exact hj.symm
  · rintro ⟨i, hi⟩
    refine ⟨i, h i (address g s i (g.rowOrder z)), ?_, rfl⟩
    exact (congrArg Fin.val hi).symm

/-- Combining preserves exact row weight whenever all layer blocks fit. -/
theorem combined_rowWeight {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hb : 0 < b) (hfit : k * b ≤ n) :
    RowWeight (combined g s h) k := by
  classical
  intro z
  have hcard := congrArg Finset.card (combined_row_support g s h hfit z)
  rw [Finset.card_image_of_injective _ (rowNeighbor_injective g s h hb hfit z)] at hcard
  simpa [weight, combined] using hcard

end ExpandingCodes.PolynomialStretch

end FlattenModule36

/-! Inlined whole module: ExpandingCodes.Construction.HashNeighbors -/
section FlattenModule37



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- Preliminary neighbors are a union of at most `k` columns per row. -/
theorem preliminary_neighbors_card_le {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (S : Finset (Fin (rowCount d n))) :
    (neighbors (preliminary g s) S).card ≤ k * S.card := by
  classical
  let _ : DecidableEq (g.F × g.F × g.F) := fun _ _ => Classical.propDecidable _
  rw [preliminary_neighbors_eq]
  unfold layeredNeighbors
  apply (Finset.card_biUnion_le).trans
  calc
    _ ≤ ∑ _z ∈ S, k := by
      apply Finset.sum_le_sum
      intro z hz
      exact (Finset.card_image_le).trans_eq (Finset.card_fin k)
    _ = _ := by simp [mul_comm]

/-- The column of the combined matrix associated with a preliminary neighbor. -/
noncomputable def hashColumn {F : Type*} {n k b : ℕ}
    (h : Hashes F k b) (hfit : k * b ≤ n) (p : Fin k × (F × F × F)) : Fin n :=
  ⟨p.1.val * b + (h p.1 p.2).val, by
    have hu := (h p.1 p.2).isLt
    have hi : (p.1.val + 1) * b ≤ k * b := Nat.mul_le_mul_right b p.1.isLt
    have heq : (p.1.val + 1) * b = p.1.val * b + b := by rw [Nat.add_mul, Nat.one_mul]
    omega⟩

/-- Padding columns contribute no extra neighbors: the combined neighbor set is exactly
an image of the preliminary neighbor set. -/
theorem combined_neighbors_eq_hashColumn_image {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hfit : k * b ≤ n)
    (S : Finset (Fin (rowCount d n))) :
    neighbors (combined g s h) S =
      (neighbors (preliminary g s) S).image (hashColumn h hfit) := by
  classical
  ext j
  simp only [neighbors, QuantumExpander.Decoder.nbhdA, Finset.mem_filter,
    Finset.mem_univ, true_and, combined, ne_eq, ite_eq_right_iff,
    one_ne_zero, imp_false, not_not, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, i, u, hj, hu⟩
    refine ⟨(i, address g s i (g.rowOrder z)), ?_, ?_⟩
    · refine ⟨z, hz, ?_⟩
      simp only [preliminary, ite_true, one_ne_zero, not_false_eq_true]
    · apply Fin.ext
      change i.val * b + (h i (address g s i (g.rowOrder z))).val = j.val
      rw [hu]
      exact hj.symm
  · rintro ⟨⟨i, a⟩, ⟨z, hz, hza⟩, hp⟩
    have ha : address g s i (g.rowOrder z) = a := by simpa [preliminary] using hza
    refine ⟨z, hz, i, h i a, ?_, ?_⟩
    · exact (congrArg Fin.val hp).symm
    · rw [ha]

/-- Erasing layer tags from bucket values can only reduce the combined neighbor count. -/
theorem global_hash_image_card_le {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hb : 0 < b) (hfit : k * b ≤ n)
    (S : Finset (Fin (rowCount d n))) :
    ((neighbors (preliminary g s) S).image (fun p => h p.1 p.2)).card ≤
      (neighbors (combined g s h) S).card := by
  classical
  let project : Fin n → Fin b := fun j => ⟨j.val % b, Nat.mod_lt _ hb⟩
  have heq : (neighbors (combined g s h) S).image project =
      (neighbors (preliminary g s) S).image (fun p => h p.1 p.2) := by
    rw [combined_neighbors_eq_hashColumn_image g s h hfit S, Finset.image_image]
    apply Finset.image_congr
    intro p hp
    apply Fin.ext
    change (p.1.val * b + (h p.1 p.2).val) % b = (h p.1 p.2).val
    rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
      Nat.mod_eq_of_lt (h p.1 p.2).isLt, Nat.mod_eq_of_lt (h p.1 p.2).isLt]
  rw [← heq]
  exact Finset.card_image_le

/-- The complete hash sample is exactly a full function on layer-address pairs. -/
noncomputable def hashesEquiv {F : Type*} (k b : ℕ) :
    Hashes F k b ≃ ((Fin k × (F × F × F)) → Fin b) where
  toFun h p := h p.1 p.2
  invFun f i a := f (i, a)
  left_inv _h := rfl
  right_inv _f := rfl

/-- A canonical expanding failure has a nonempty row-set witness of the canonical size. -/
theorem combined_not_expanding_witness {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hb : 0 < b) (hfit : k * b ≤ n)
    (ε t : ℝ) (hbad : ¬ Expanding (combined g s h) (1 - ε) k t) :
    ∃ S : Finset (Fin (rowCount d n)), S.Nonempty ∧ (S.card : ℝ) ≤ t ∧
      ((neighbors (combined g s h) S).card : ℝ) < (1 - ε) * k * S.card := by
  classical
  have hw := combined_rowWeight g s h hb hfit
  have hm : 0 < rowCount d n := by unfold rowCount fieldSize; positivity
  have hmc : (rowCount d n : ℝ) ≠ 0 := by
    exact_mod_cast hm.ne'
  unfold Expanding at hbad
  simp only [hw, true_and, Fintype.card_fin, Nat.ne_of_gt hm, ↓reduceIte,
    QuantumExpander.Decoder.IsLeftExpanding] at hbad
  push Not at hbad
  obtain ⟨S, hS, hbad⟩ := hbad
  have hsize : (S.card : ℝ) ≤ t := by
    simpa only [div_mul_cancel₀ _ hmc] using hS
  have hfail : ((neighbors (combined g s h) S).card : ℝ) < (1 - ε) * k * S.card := by
    simpa only [neighbors, sub_sub_cancel] using hbad
  refine ⟨S, ?_, hsize, hfail⟩
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  subst S
  simp [neighbors, QuantumExpander.Decoder.nbhdA] at hfail

/-- Preliminary expansion forces a definite occupancy loss whenever combined expansion
fails for a fixed row set. -/
theorem combined_failure_implies_image_loss (ε : ℝ) (n : ℕ)
    (g : Geometry (dimension ε) n) (s : Forms g.F (dimension ε) (arity ε))
    (h : Hashes g.F (arity ε) (buckets ε n)) (hfit : arity ε * buckets ε n ≤ n)
    (hgood : PreliminaryGood ε n g s) (L : ℕ)
    (hL : (L : ℝ) ≤ ε * arity ε - dimension ε + 1)
    (S : Finset (Fin (rowCount (dimension ε) n)))
    (hsize : (S.card : ℝ) ≤ (n : ℝ) ^ (1 - ε))
    (hbad : ((neighbors (combined g s h) S).card : ℝ) <
      (1 - ε) * arity ε * S.card) :
    ((neighbors (preliminary g s) S).image (fun p => h p.1 p.2)).card + L * S.card ≤
      (neighbors (preliminary g s) S).card := by
  have hpre := hgood S hsize
  have himage := global_hash_image_card_le g s h (by unfold buckets; positivity) hfit S
  have hi : (((neighbors (preliminary g s) S).image (fun p => h p.1 p.2)).card : ℝ) ≤
      (neighbors (combined g s h) S).card := by exact_mod_cast himage
  have hLs := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg S.card)
  have hc : ((((neighbors (preliminary g s) S).image (fun p => h p.1 p.2)).card +
      L * S.card : ℕ) : ℝ) ≤ (neighbors (preliminary g s) S).card := by
    push_cast
    nlinarith
  exact_mod_cast hc

end ExpandingCodes.PolynomialStretch

end FlattenModule37

/-! Inlined whole module: ExpandingCodes.Construction.SamplerSupport -/
section FlattenModule38



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

/-- Every choice of forms and hashes has positive sampling mass, and these are
exactly the matrices in the support of the canonical law. -/
theorem sampleLaw_ne_zero_iff (ε : ℝ) (n : ℕ) (g : Geometry (dimension ε) n)
    (G : Generator (rowCount (dimension ε) n) n) :
    sampleLaw ε n g G ≠ 0 ↔
      ∃ (s : Forms g.F (dimension ε) (arity ε))
        (h : Hashes g.F (arity ε) (buckets ε n)), combined g s h = G := by
  classical
  change G ∈ (sampleLaw ε n g).support ↔ _
  simp only [sampleLaw, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨⟨s, h⟩, _, heq⟩
    exact ⟨s, h, heq⟩
  · rintro ⟨s, h, heq⟩
    exact ⟨(s, h), PMF.mem_support_uniformOfFintype _, heq⟩

/-- The rounded-down power-of-two bucket count is always positive. -/
theorem sampler_buckets_pos (ε : ℝ) (n : ℕ) : 0 < buckets ε n := by
  unfold buckets
  exact pow_pos (by decide) _

/-- All layer blocks fit once there are at least as many columns as layers. -/
theorem arity_mul_buckets_le (ε : ℝ) (n : ℕ)
    (hk : 0 < arity ε) (hn : arity ε ≤ n) : arity ε * buckets ε n ≤ n := by
  have hdiv : n / arity ε ≠ 0 := Nat.ne_of_gt ((Nat.one_le_div_iff hk).2 hn)
  unfold buckets
  exact (Nat.mul_le_mul_left (arity ε) (Nat.pow_log_le_self 2 hdiv)).trans
    (by simpa [Nat.mul_comm] using Nat.div_mul_le_self n (arity ε))

private theorem sampler_arity_pos (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    0 < arity ε := by
  have hd : (0 : ℝ) < dimension ε := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) (dimension_ge_four ε hε)
  have he : 0 < ε := hε.1
  unfold arity
  apply Nat.ceil_pos.2
  positivity

/-- Every actual sampler output has exact row weight at all sufficiently large sizes. -/
theorem sampleLaw_output_rowWeight (ε : ℝ) (n : ℕ)
    (hε : 0 < ε ∧ ε < 1 / 2) (hn : arity ε ≤ n)
    (g : Geometry (dimension ε) n)
    (G : Generator (rowCount (dimension ε) n) n)
    (hG : sampleLaw ε n g G ≠ 0) : RowWeight G (arity ε) := by
  obtain ⟨s, h, rfl⟩ := (sampleLaw_ne_zero_iff ε n g G).1 hG
  exact combined_rowWeight g s h (sampler_buckets_pos ε n)
    (arity_mul_buckets_le ε n (sampler_arity_pos ε hε) hn)

/-- The support conclusion is uniform over geometry and every matrix in the law. -/
theorem eventual_sampleLaw_rowWeight (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (g : Geometry (dimension ε) n)
      (G : Generator (rowCount (dimension ε) n) n),
      sampleLaw ε n g G ≠ 0 → RowWeight G (arity ε) := by
  filter_upwards [Filter.eventually_ge_atTop (arity ε)] with n hn
  intro g G hG
  exact sampleLaw_output_rowWeight ε n hε hn g G hG

end ExpandingCodes.PolynomialStretch

end FlattenModule38

/-! Inlined whole module: ExpandingCodes.Construction.HashParameters -/
section FlattenModule39



set_option autoImplicit false
open Filter Topology

namespace ExpandingCodes.PolynomialStretch

noncomputable def hashRepeatThreshold (ε : ℝ) : ℕ :=
  ⌊ε * (arity ε : ℝ) - (dimension ε : ℝ) + 1⌋₊

noncomputable def hashRatio (ε : ℝ) (n : ℕ) : ℝ :=
  (rowCount (dimension ε) n : ℝ) * 2 ^ arity ε *
    (2 * (arity ε : ℝ) ^ 2 * (n : ℝ) ^ (-ε)) ^ hashRepeatThreshold ε

private theorem hash_arity_scaled_lower (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    4 * (dimension ε : ℝ) ^ 2 ≤ ε ^ 2 * (arity ε : ℝ) := by
  have hc : 4 * (dimension ε : ℝ) ^ 2 * ε⁻¹ ^ 2 ≤ (arity ε : ℝ) := Nat.le_ceil _
  have hp := mul_le_mul_of_nonneg_left hc (sq_nonneg ε)
  have hi : ε ^ 2 * ε⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hε.1.ne', one_pow]
  nlinarith

private theorem hash_threshold_argument_nonneg (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    0 ≤ ε * (arity ε : ℝ) - (dimension ε : ℝ) + 1 := by
  have hd : (4 : ℝ) ≤ dimension ε := by exact_mod_cast dimension_ge_four ε hε
  have hk := hash_arity_scaled_lower ε hε
  have hs : ε ^ 2 ≤ ε := by nlinarith [hε.1, hε.2]
  have hm := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (arity ε) : (0 : ℝ) ≤ arity ε)
  nlinarith

theorem hashRepeatThreshold_le (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    (hashRepeatThreshold ε : ℝ) ≤ ε * (arity ε : ℝ) - (dimension ε : ℝ) + 1 :=
  Nat.floor_le (hash_threshold_argument_nonneg ε hε)

theorem hash_exponent_gap (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    1 / ε < ε * (hashRepeatThreshold ε : ℝ) - 2 * (dimension ε : ℝ) ^ 2 := by
  have hf : ε * (arity ε : ℝ) - (dimension ε : ℝ) < (hashRepeatThreshold ε : ℝ) := by
    have := Nat.lt_floor_add_one (ε * (arity ε : ℝ) - (dimension ε : ℝ) + 1)
    dsimp [hashRepeatThreshold]
    linarith
  have hm := mul_lt_mul_of_pos_left hf hε.1
  have hk := hash_arity_scaled_lower ε hε
  have hg := preliminary_exponent_gap ε hε
  have hd : (4 : ℝ) ≤ dimension ε := by exact_mod_cast dimension_ge_four ε hε
  have he : ε * (dimension ε : ℝ) < (dimension ε : ℝ) / 2 := by nlinarith [hε.2]
  nlinarith

theorem hash_arity_pos (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) : 0 < arity ε := by
  have := arity_exceeds_row_exponent ε hε
  omega

theorem lt_two_arity_mul_buckets (ε : ℝ) (n : ℕ) (hk : 0 < arity ε) :
    n < 2 * arity ε * buckets ε n := by
  have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n / arity ε)
  have hh' : n / arity ε < 2 * buckets ε n := by
    simpa [buckets, pow_succ, Nat.mul_comm] using hh
  have := (Nat.div_lt_iff_lt_mul hk).1 hh'
  nlinarith

theorem hash_bucket_ratio_le (ε : ℝ) (n : ℕ) (hk : 0 < arity ε) (hn : 0 < n) :
    (arity ε : ℝ) * (n : ℝ) ^ (1 - ε) / (buckets ε n : ℝ) ≤
      2 * (arity ε : ℝ) ^ 2 * (n : ℝ) ^ (-ε) := by
  have hb : (0 : ℝ) < buckets ε n := by exact_mod_cast sampler_buckets_pos ε n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnb : (n : ℝ) / (buckets ε n : ℝ) ≤ 2 * (arity ε : ℝ) := by
    apply (div_le_iff₀ hb).2
    exact_mod_cast (lt_two_arity_mul_buckets ε n hk).le
  have hr : (n : ℝ) ^ (1 - ε) = (n : ℝ) * (n : ℝ) ^ (-ε) := by
    rw [show 1 - ε = 1 + -ε by ring, Real.rpow_add hnpos, Real.rpow_one]
  calc
    _ = ((arity ε : ℝ) * (n : ℝ) ^ (-ε)) * ((n : ℝ) / (buckets ε n : ℝ)) := by
      rw [hr]
      ring
    _ ≤ ((arity ε : ℝ) * (n : ℝ) ^ (-ε)) * (2 * (arity ε : ℝ)) :=
      mul_le_mul_of_nonneg_left hnb (by positivity)
    _ = _ := by ring

noncomputable def hashRatioConstant (ε : ℝ) : ℝ :=
  2 ^ dimension ε * 2 ^ arity ε * (2 * (arity ε : ℝ) ^ 2) ^ hashRepeatThreshold ε

theorem hashRatio_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ hashRatio ε n := by
  unfold hashRatio
  positivity

theorem hashRatio_le (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) (n : ℕ) (hn : 2 ≤ n) :
    hashRatio ε n ≤ hashRatioConstant ε *
      (n : ℝ) ^ (2 * (dimension ε : ℝ) ^ 2 - ε * (hashRepeatThreshold ε : ℝ)) := by
  have hd : 0 < dimension ε := lt_of_lt_of_le (by decide : 0 < 4) (dimension_ge_four ε hε)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : (rowCount (dimension ε) n : ℝ) ≤
      2 ^ dimension ε * (n : ℝ) ^ (2 * dimension ε ^ 2) := by
    exact_mod_cast (rowCount_upper (dimension ε) n hd hn).le
  have hp : ((n : ℝ) ^ (-ε)) ^ hashRepeatThreshold ε =
      (n : ℝ) ^ (-ε * (hashRepeatThreshold ε : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
  calc
    hashRatio ε n ≤ (2 ^ dimension ε * (n : ℝ) ^ (2 * dimension ε ^ 2)) *
        2 ^ arity ε * (2 * (arity ε : ℝ) ^ 2 * (n : ℝ) ^ (-ε)) ^ hashRepeatThreshold ε := by
      unfold hashRatio
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr (by positivity)) (by positivity)
    _ = hashRatioConstant ε *
        ((n : ℝ) ^ (2 * dimension ε ^ 2) * ((n : ℝ) ^ (-ε)) ^ hashRepeatThreshold ε) := by
      unfold hashRatioConstant
      rw [mul_pow]
      ring
    _ = _ := by
      rw [hp, ← Real.rpow_natCast (n : ℝ) (2 * dimension ε ^ 2), ← Real.rpow_add hnpos]
      congr 2
      push_cast
      ring

theorem tendsto_hashRatio_mul_rpow (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) (a : ℝ)
    (ha : a < ε * (hashRepeatThreshold ε : ℝ) - 2 * (dimension ε : ℝ) ^ 2) :
    Tendsto (fun n : ℕ => hashRatio ε n * (n : ℝ) ^ a) atTop (𝓝 0) := by
  have hg : 0 < ε * (hashRepeatThreshold ε : ℝ) - 2 * (dimension ε : ℝ) ^ 2 - a := by
    linarith
  have hz : Tendsto (fun n : ℕ => hashRatioConstant ε *
      (n : ℝ) ^ (2 * (dimension ε : ℝ) ^ 2 - ε * (hashRepeatThreshold ε : ℝ) + a))
      atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop hg).comp tendsto_natCast_atTop_atTop
    have he : -(ε * (hashRepeatThreshold ε : ℝ) - 2 * (dimension ε : ℝ) ^ 2 - a) =
      2 * (dimension ε : ℝ) ^ 2 - ε * (hashRepeatThreshold ε : ℝ) + a := by ring
    simpa only [Function.comp_apply, he, mul_zero] using tendsto_const_nhds.mul hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz
  · exact Eventually.of_forall (fun n => mul_nonneg (hashRatio_nonneg ε n) (by positivity))
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc
      _ ≤ hashRatioConstant ε *
          (n : ℝ) ^ (2 * (dimension ε : ℝ) ^ 2 - ε * (hashRepeatThreshold ε : ℝ)) *
          (n : ℝ) ^ a := mul_le_mul_of_nonneg_right (hashRatio_le ε hε n hn) (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hnpos]

theorem tendsto_hashRatio_scaled (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    Tendsto (fun n : ℕ => hashRatio ε n * (n : ℝ) ^ (1 / ε)) atTop (𝓝 0) :=
  tendsto_hashRatio_mul_rpow ε hε (1 / ε) (hash_exponent_gap ε hε)

theorem tendsto_hashRatio (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    Tendsto (hashRatio ε) atTop (𝓝 0) := by
  have hg : 0 < ε * (hashRepeatThreshold ε : ℝ) - 2 * (dimension ε : ℝ) ^ 2 :=
    lt_trans (one_div_pos.mpr hε.1) (hash_exponent_gap ε hε)
  simpa using tendsto_hashRatio_mul_rpow ε hε 0 hg

theorem eventually_hash_parameters (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ arity ε * buckets ε n ≤ n ∧ hashRatio ε n ≤ 1 / 2 := by
  filter_upwards [eventually_ge_atTop (max 1 (arity ε)),
    (tendsto_hashRatio ε hε).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with n hn hb
  exact ⟨by omega, arity_mul_buckets_le ε n (hash_arity_pos ε hε) (by omega), hb.le⟩

end ExpandingCodes.PolynomialStretch

end FlattenModule39

/-! Inlined whole module: ExpandingCodes.Probability.HashExpansion -/
section FlattenModule40





set_option autoImplicit false
set_option maxRecDepth 2048
open scoped Classical BigOperators
open Filter Topology

namespace ExpandingCodes.PolynomialStretch

/-- A fixed row-set failure requires independent hash occupancy losses. -/
theorem uniformProb_combined_fixed_set_le (ε : ℝ) (n : ℕ)
    (g : Geometry (dimension ε) n) (s : Forms g.F (dimension ε) (arity ε))
    (hfit : arity ε * buckets ε n ≤ n) (hgood : PreliminaryGood ε n g s)
    (L : ℕ) (hL : (L : ℝ) ≤ ε * arity ε - dimension ε + 1)
    (S : Finset (Fin (rowCount (dimension ε) n)))
    (hsize : (S.card : ℝ) ≤ (n : ℝ) ^ (1 - ε)) (C : ℝ)
    (_hC : 0 ≤ C) (hbase : (arity ε : ℝ) * S.card / (buckets ε n : ℝ) ≤ C) :
    uniformProb (fun h : Hashes g.F (arity ε) (buckets ε n) =>
      ((neighbors (combined g s h) S).card : ℝ) < (1 - ε) * arity ε * S.card) ≤
      ((2 : ℝ) ^ arity ε * C ^ L) ^ S.card := by
  classical
  let D := neighbors (preliminary g s) S
  have hD : D.card ≤ arity ε * S.card := preliminary_neighbors_card_le g s S
  have hocc := uniformProb_image_loss_le (V := Fin (buckets ε n)) D (L * S.card)
  have heq := uniformProb_equiv (hashesEquiv (F := g.F) (arity ε) (buckets ε n))
    (fun f : (Fin (arity ε) × (g.F × g.F × g.F)) → Fin (buckets ε n) =>
      (D.image f).card + L * S.card ≤ D.card)
  have hoccH := heq.le.trans hocc
  calc
    _ ≤ uniformProb (fun h : Hashes g.F (arity ε) (buckets ε n) =>
        (D.image (fun p => h p.1 p.2)).card + L * S.card ≤ D.card) := by
      apply uniformProb_mono
      intro h hh
      exact combined_failure_implies_image_loss ε n g s h hfit hgood L hL S hsize hh
    _ ≤ (2 : ℝ) ^ D.card * ((D.card : ℝ) / (buckets ε n : ℝ)) ^ (L * S.card) := by
      simpa only [hashesEquiv, Equiv.coe_fn_mk, Fintype.card_fin] using hoccH
    _ ≤ (2 : ℝ) ^ (arity ε * S.card) * C ^ (L * S.card) := by
      apply mul_le_mul
      · exact pow_le_pow_right₀ (by norm_num) hD
      · apply pow_le_pow_left₀ (by positivity)
        calc
          (D.card : ℝ) / (buckets ε n : ℝ) ≤
              (arity ε : ℝ) * S.card / (buckets ε n : ℝ) := by
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            exact_mod_cast hD
          _ ≤ C := hbase
      · positivity
      · positivity
    _ = _ := by simp only [mul_pow, pow_mul]

/-- Union over row subsets of a prescribed size, counted by the elementary bound `m^a`. -/
theorem uniformProb_exists_combined_sets_le_pow (ε : ℝ) (n : ℕ)
    (g : Geometry (dimension ε) n) (s : Forms g.F (dimension ε) (arity ε))
    (hfit : arity ε * buckets ε n ≤ n) (hgood : PreliminaryGood ε n g s)
    (L : ℕ) (hL : (L : ℝ) ≤ ε * arity ε - dimension ε + 1)
    (a : ℕ) (hsize : (a : ℝ) ≤ (n : ℝ) ^ (1 - ε)) (C : ℝ)
    (hC : 0 ≤ C) (hbase : (arity ε : ℝ) * (n : ℝ) ^ (1 - ε) /
      (buckets ε n : ℝ) ≤ C) :
    uniformProb (fun h : Hashes g.F (arity ε) (buckets ε n) =>
      ∃ S ∈ (Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard a,
        ((neighbors (combined g s h) S).card : ℝ) < (1 - ε) * arity ε * S.card) ≤
      ((rowCount (dimension ε) n : ℝ) * 2 ^ arity ε * C ^ L) ^ a := by
  classical
  let Q : ℝ := (2 : ℝ) ^ arity ε * C ^ L
  have hQ : 0 ≤ Q := by positivity
  have hcount : (((Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard a).card : ℝ) ≤
      (rowCount (dimension ε) n : ℝ) ^ a := by
    have hnat : ((Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard a).card ≤
        rowCount (dimension ε) n ^ a := by
      simpa only [Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin] using Nat.choose_le_pow (rowCount (dimension ε) n) a
    exact_mod_cast hnat
  calc
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard a,
        uniformProb (fun h : Hashes g.F (arity ε) (buckets ε n) =>
          ((neighbors (combined g s h) S).card : ℝ) <
            (1 - ε) * arity ε * S.card) := uniformProb_exists_finset _ _
    _ ≤ ∑ _S ∈ (Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard a,
        Q ^ a := by
      apply Finset.sum_le_sum
      intro S hS
      have hc : S.card = a := (Finset.mem_powersetCard.mp hS).2
      have hb : (arity ε : ℝ) * S.card / (buckets ε n : ℝ) ≤ C := by
        apply le_trans _ hbase
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_left (by simpa only [hc] using hsize) (Nat.cast_nonneg _)
      simpa only [Q, hc] using uniformProb_combined_fixed_set_le ε n g s hfit hgood
        L hL S (by simpa only [hc] using hsize) C hC hb
    _ = (((Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard a).card : ℝ) *
        Q ^ a := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (rowCount (dimension ε) n : ℝ) ^ a * Q ^ a :=
      mul_le_mul_of_nonneg_right hcount (pow_nonneg hQ a)
    _ = _ := by rw [← mul_pow]; congr 1; dsimp [Q]; ring

/-- A quantitative finite hash expansion estimate, uniform over all admissible forms. -/
theorem combined_bad_prob_le_two_base (ε : ℝ) (n : ℕ)
    (g : Geometry (dimension ε) n) (s : Forms g.F (dimension ε) (arity ε))
    (hfit : arity ε * buckets ε n ≤ n) (hgood : PreliminaryGood ε n g s)
    (L : ℕ) (hL : (L : ℝ) ≤ ε * arity ε - dimension ε + 1)
    (C : ℝ) (hC : 0 ≤ C) (hbase : (arity ε : ℝ) * (n : ℝ) ^ (1 - ε) /
      (buckets ε n : ℝ) ≤ C)
    (hhalf : (rowCount (dimension ε) n : ℝ) * 2 ^ arity ε * C ^ L ≤ 1 / 2) :
    uniformProb (fun h : Hashes g.F (arity ε) (buckets ε n) =>
      ¬ Expanding (combined g s h) (1 - ε) (arity ε) ((n : ℝ) ^ (1 - ε))) ≤
      2 * ((rowCount (dimension ε) n : ℝ) * 2 ^ arity ε * C ^ L) := by
  classical
  let t := (n : ℝ) ^ (1 - ε)
  let N := ⌊t⌋₊
  let B : ℝ := (rowCount (dimension ε) n : ℝ) * 2 ^ arity ε * C ^ L
  have ht : 0 ≤ t := by positivity
  have hB : 0 ≤ B := by positivity
  have hcover : ∀ h : Hashes g.F (arity ε) (buckets ε n),
      ¬ Expanding (combined g s h) (1 - ε) (arity ε) t →
      ∃ j ∈ Finset.range N,
        ∃ S ∈ (Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard (j + 1),
          ((neighbors (combined g s h) S).card : ℝ) < (1 - ε) * arity ε * S.card := by
    intro h hh
    obtain ⟨S, hne, hsize, hbad⟩ := combined_not_expanding_witness g s h
      (sampler_buckets_pos ε n) hfit ε t hh
    have hpos : 0 < S.card := Finset.card_pos.mpr hne
    have hc : S.card ≤ N := Nat.le_floor hsize
    refine ⟨S.card - 1, Finset.mem_range.mpr (by omega), S, ?_, hbad⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by omega⟩
  calc
    _ ≤ uniformProb (fun h : Hashes g.F (arity ε) (buckets ε n) =>
        ∃ j ∈ Finset.range N,
          ∃ S ∈ (Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard (j + 1),
            ((neighbors (combined g s h) S).card : ℝ) < (1 - ε) * arity ε * S.card) :=
      uniformProb_mono hcover
    _ ≤ ∑ j ∈ Finset.range N,
        uniformProb (fun h : Hashes g.F (arity ε) (buckets ε n) =>
          ∃ S ∈ (Finset.univ : Finset (Fin (rowCount (dimension ε) n))).powersetCard (j + 1),
            ((neighbors (combined g s h) S).card : ℝ) < (1 - ε) * arity ε * S.card) :=
      uniformProb_exists_finset _ _
    _ ≤ ∑ j ∈ Finset.range N, B ^ (j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjs : ((j + 1 : ℕ) : ℝ) ≤ t :=
        (Nat.cast_le.mpr (Nat.succ_le_of_lt (Finset.mem_range.mp hj))).trans (Nat.floor_le ht)
      exact uniformProb_exists_combined_sets_le_pow ε n g s hfit hgood L hL
        (j + 1) hjs C hC hbase
    _ ≤ 2 * B := sum_pow_succ_le_two_mul B hB hhalf N

/-- The exact canonical hash-expansion envelope, uniform over arbitrary public geometry
and all preliminary-good sampled forms. -/
theorem hash_expansion_envelope (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2)
    (g : ∀ n, Geometry (dimension ε) n) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) ∧
      Tendsto (fun n => δ n * (n : ℝ) ^ (1 / ε)) atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ s : Forms (g n).F (dimension ε) (arity ε),
        PreliminaryGood ε n (g n) s →
        uniformProb (fun h : Hashes (g n).F (arity ε) (buckets ε n) =>
          ¬ Expanding (combined (g n) s h) (1 - ε) (arity ε) ((n : ℝ) ^ (1 - ε))) ≤ δ n := by
  refine ⟨fun n => 2 * hashRatio ε n, fun n => mul_nonneg (by norm_num) (hashRatio_nonneg ε n), ?_, ?_⟩
  · have hh := (tendsto_hashRatio_scaled ε hε).const_mul 2
    simpa only [mul_assoc, mul_zero] using hh
  · filter_upwards [eventually_hash_parameters ε hε] with n hn
    intro s hs
    exact combined_bad_prob_le_two_base ε n (g n) s hn.2.1 hs (hashRepeatThreshold ε)
      (hashRepeatThreshold_le ε hε) (2 * (arity ε : ℝ) ^ 2 * (n : ℝ) ^ (-ε))
      (by positivity) (hash_bucket_ratio_le ε n (hash_arity_pos ε hε) hn.1) hn.2.2

end ExpandingCodes.PolynomialStretch

end FlattenModule40

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

theorem uniformMean_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    uniformMean f ≤ uniformMean g := by
  unfold uniformMean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (by positivity)

omit [Nonempty Ω] in
theorem uniformMean_add (f g : Ω → ℝ) :
    uniformMean (fun x => f x + g x) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

omit [Nonempty Ω] in
theorem uniformMean_sub (f g : Ω → ℝ) :
    uniformMean (fun x => f x - g x) = uniformMean f - uniformMean g := by
  simp [uniformMean, Finset.sum_sub_distrib, sub_div]

omit [Nonempty Ω] in
theorem uniformMean_mul (c : ℝ) (f : Ω → ℝ) :
    uniformMean (fun x => c * f x) = c * uniformMean f := by
  simp [uniformMean, ← Finset.mul_sum, mul_div_assoc]

theorem uniformMean_abs_sub_le {f g : Ω → ℝ} (h : ∀ x, |f x - g x| ≤ 1) :
    |uniformMean f - uniformMean g| ≤ 1 := by
  rw [← uniformMean_sub, abs_le]
  constructor
  · simpa using uniformMean_mono (fun x => (abs_le.mp (h x)).1)
  · simpa using uniformMean_mono (fun x => (abs_le.mp (h x)).2)

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

/-- A change to one Boolean coordinate changes the value by at most one. -/
def HasUnitBoundedDifferences {m : ℕ} (f : (Fin m → Bool) → ℝ) : Prop :=
  ∀ x i b, |f (Function.update x i b) - f x| ≤ 1

theorem uniformMean_cons {m : ℕ} (f : (Fin (m + 1) → Bool) → ℝ) :
    uniformMean f =
      (uniformMean (fun x => f (Fin.cons true x)) +
        uniformMean (fun x => f (Fin.cons false x))) / 2 := by
  have hs : (∑ x, f x) =
      (∑ x, f (Fin.cons true x)) + ∑ x, f (Fin.cons false x) := by
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+1) => Bool))
      (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [uniformMean, hs, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    pow_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

theorem HasUnitBoundedDifferences.cons {m : ℕ} {f : (Fin (m+1) → Bool) → ℝ}
    (h : HasUnitBoundedDifferences f) (b : Bool) :
    HasUnitBoundedDifferences (fun x => f (Fin.cons b x)) := by
  intro x i c
  simpa only [Fin.cons_update] using h (Fin.cons b x) i.succ c

theorem HasUnitBoundedDifferences.mean_slice_gap {m : ℕ}
    {f : (Fin (m+1) → Bool) → ℝ} (h : HasUnitBoundedDifferences f) :
    |uniformMean (fun x => f (Fin.cons true x)) -
      uniformMean (fun x => f (Fin.cons false x))| ≤ 1 := by
  apply uniformMean_abs_sub_le
  intro x
  simpa only [Fin.update_cons_zero] using h (Fin.cons false x) 0 true

/-- The elementary two-point Hoeffding estimate, with its sharp constant. -/
theorem two_point_centered_exp_le (a b s : ℝ) (h : |a-b| ≤ 1) :
    (Real.exp (s * (a-(a+b)/2)) + Real.exp (s * (b-(a+b)/2))) / 2 ≤
      Real.exp (s^2 / 8) := by
  have h₁ : s * (a-(a+b)/2) = s*(a-b)/2 := by ring
  have h₂ : s * (b-(a+b)/2) = -(s*(a-b)/2) := by ring
  rw [h₁, h₂, ← Real.cosh_eq]
  apply (Real.cosh_le_exp_half_sq _).trans
  apply Real.exp_le_exp.mpr
  have hab := abs_le.mp h
  have hs : (a-b)^2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1-(a-b) by linarith)
      (show 0 ≤ 1+(a-b) by linarith)]
  nlinarith [mul_nonneg (sq_nonneg s) (show 0 ≤ 1-(a-b)^2 by linarith)]

/-- The centered moment generating function on an independent uniform Boolean cube. -/
theorem boundedDifferences_mgf {m : ℕ} (f : (Fin m → Bool) → ℝ)
    (hf : HasUnitBoundedDifferences f) (s : ℝ) :
    uniformMean (fun x => Real.exp (s * (f x - uniformMean f))) ≤
      Real.exp ((m : ℝ) * s^2 / 8) := by
  induction m with
  | zero => simp [uniformMean]
  | succ m ih =>
    let a := uniformMean (fun x => f (Fin.cons true x))
    let b := uniformMean (fun x => f (Fin.cons false x))
    have hm : uniformMean f = (a+b)/2 := uniformMean_cons f
    have hs (c : Bool) :
        uniformMean (fun x => Real.exp (s * (f (Fin.cons c x) - uniformMean f))) =
        Real.exp (s * (uniformMean (fun x => f (Fin.cons c x)) - uniformMean f)) *
          uniformMean (fun x => Real.exp (s * (f (Fin.cons c x) -
            uniformMean (fun x => f (Fin.cons c x))))) := by
      rw [← uniformMean_mul]
      congr 1
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    rw [uniformMean_cons, hs true, hs false]
    have ht := ih (fun x => f (Fin.cons true x)) (hf.cons true)
    have hb := ih (fun x => f (Fin.cons false x)) (hf.cons false)
    have hp := two_point_centered_exp_le a b s hf.mean_slice_gap
    calc
      _ ≤ (Real.exp (s*(a-uniformMean f)) * Real.exp ((m : ℝ)*s^2/8) +
            Real.exp (s*(b-uniformMean f)) * Real.exp ((m : ℝ)*s^2/8)) / 2 := by
        exact div_le_div_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _))
            (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _))) (by norm_num)
      _ = Real.exp ((m : ℝ)*s^2/8) *
            ((Real.exp (s*(a-(a+b)/2)) + Real.exp (s*(b-(a+b)/2))) / 2) := by
        rw [hm]
        ring
      _ ≤ Real.exp ((m : ℝ)*s^2/8) * Real.exp (s^2/8) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)
      _ = Real.exp ((↑(m+1) : ℝ)*s^2/8) := by
        rw [← Real.exp_add, Nat.cast_add, Nat.cast_one]
        congr 1
        ring

/-- Finite exponential Markov inequality for a lower deviation. -/
theorem uniformProb_lower_tail_le_mgf {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (t s : ℝ) (hs : 0 ≤ s) :
    uniformProb (fun x => f x ≤ uniformMean f - t) ≤
      Real.exp (-s*t) * uniformMean (fun x => Real.exp ((-s)*(f x-uniformMean f))) := by
  classical
  have hp : Real.exp (s*t) * uniformProb (fun x => f x ≤ uniformMean f - t) ≤
      uniformMean (fun x => Real.exp ((-s)*(f x-uniformMean f))) := by
    rw [uniformProb_eq_uniformMean, ← uniformMean_mul]
    apply uniformMean_mono
    intro x
    split_ifs with hx
    · simp only [mul_one]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hs (show 0 ≤ uniformMean f-t-f x by linarith)]
    · simp only [mul_zero]
      exact Real.exp_nonneg _
  calc
    _ = Real.exp (-s*t) * (Real.exp (s*t) *
          uniformProb (fun x => f x ≤ uniformMean f - t)) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)

/-- Sharp bounded-differences lower tail for the exact finite uniform Boolean cube. -/
theorem boundedDifferences_lower_tail {m : ℕ} (hm : 0 < m)
    (f : (Fin m → Bool) → ℝ) (hf : HasUnitBoundedDifferences f)
    (t : ℝ) (ht : 0 ≤ t) :
    uniformProb (fun x => f x ≤ uniformMean f - t) ≤
      Real.exp (-2*t^2/(m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let s := 4*t/(m : ℝ)
  have hs : 0 ≤ s := by positivity
  calc
    _ ≤ Real.exp (-s*t) * uniformMean (fun x => Real.exp ((-s)*(f x-uniformMean f))) :=
      uniformProb_lower_tail_le_mgf f t s hs
    _ ≤ Real.exp (-s*t) * Real.exp ((m : ℝ)*(-s)^2/8) :=
      mul_le_mul_of_nonneg_left (boundedDifferences_mgf f hf (-s)) (Real.exp_nonneg _)
    _ = Real.exp (-2*t^2/(m : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [s]
      field_simp
      ring

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

theorem uniformProb_compl {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → Prop) :
    uniformProb E + uniformProb (fun x => ¬ E x) = 1 := by
  classical
  rw [uniformProb_eq_uniformMean, uniformProb_eq_uniformMean, ← uniformMean_add]
  calc
    _ = uniformMean (fun _ : Ω => (1 : ℝ)) := by
      apply congrArg (uniformMean (Ω := Ω))
      funext x
      by_cases hx : E x <;> simp [hx]
    _ = 1 := uniformMean_const _

theorem uniformProb_le_one {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → Prop) :
    uniformProb E ≤ 1 := by
  have hh : uniformProb E ≤ uniformProb (fun _ : Ω => True) :=
    uniformProb_mono (E := E) (F := fun _ : Ω => True) (fun _ _ => trivial)
  simpa only [uniformProb_true] using hh

theorem uniformProb_prod_left {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [Nonempty Ω] [Nonempty Ξ] (E : Ω × Ξ → Prop) :
    uniformProb E = uniformMean (fun x => uniformProb (fun y => E (x,y))) := by
  rw [← uniformProb_equiv (Equiv.prodComm Ξ Ω) E, uniformProb_prod]
  rfl

theorem uniformProb_conditional_bad_le {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [Nonempty Ω] [Nonempty Ξ] (Good : Ω → Prop) (Bad : Ω × Ξ → Prop)
    (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ x, Good x → uniformProb (fun y => Bad (x,y)) ≤ δ) :
    uniformProb Bad ≤ uniformProb (fun x => ¬ Good x) + δ := by
  classical
  rw [uniformProb_prod_left]
  calc
    _ ≤ uniformMean (fun x => (if ¬ Good x then (1 : ℝ) else 0) + δ) := by
      apply uniformMean_mono
      intro x
      by_cases hx : Good x
      · simpa only [not_true_eq_false, if_false, zero_add, hx] using h x hx
      · simpa only [hx, not_false_eq_true, if_true] using
          (uniformProb_le_one (fun y => Bad (x,y))).trans (by linarith : (1 : ℝ) ≤ 1+δ)
    _ = _ := by
      rw [uniformMean_add, uniformMean_const, uniformProb_eq_uniformMean]
      congr 1
      apply congrArg (uniformMean (Ω := Ω))
      funext x
      by_cases hx : Good x <;> simp [hx]

theorem Expanding.mono {I J : Type*} [Fintype I] [Fintype J]
    {G : Matrix I J Bit} {k : ℕ} {γ γ' t t' : ℝ}
    (h : Expanding G γ k t) (hγ : γ' ≤ γ) (ht : t' ≤ t) :
    Expanding G γ' k t' := by
  classical
  rcases h with ⟨hw, he⟩
  refine ⟨hw, ?_⟩
  by_cases hc : Fintype.card I = 0
  · simp [hc]
  · simp only [if_neg hc] at he ⊢
    intro S hs
    have hcp : (0 : ℝ) < Fintype.card I := by exact_mod_cast (Nat.pos_of_ne_zero hc)
    rw [div_mul_cancel₀ _ hcp.ne'] at hs
    have hs' : (S.card : ℝ) ≤ t / Fintype.card I * Fintype.card I := by
      rw [div_mul_cancel₀ _ hcp.ne']
      exact hs.trans ht
    have hh := he S hs'
    simp only [sub_sub_cancel] at hh ⊢
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg k)) (Nat.cast_nonneg S.card)).trans hh

end ExpandingCodes.PolynomialStretch

end FlattenModule45

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

/-! Inlined whole module: ExpandingCodes.Computation.ProgramObligations -/
section FlattenModule106





set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

/-- The actual uniform sampler, with exact random-table law, physical
generator evaluation, complete matrix output, and a polynomial clock. -/
theorem binary_sampler_implementation (θ : ℚ)
    (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2) :
    SamplerImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) :=
  binary_sampler_implementation_source θ hθ

/-- The actual deterministic tester, including physical Gram construction,
finite-field rank computation, exact rational comparison, and polynomial clock. -/
theorem binary_tester_implementation (θ : ℚ)
    (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2) :
    TesterImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) :=
  binary_tester_implementation_source θ hθ

end ExpandingCodes.PolynomialStretch

end FlattenModule106

/-! Inlined whole module: ExpandingCodes.Construction.Programs -/
section FlattenModule107


set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch

theorem rational_geometry_programs (θ : ℚ) (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2) :
    ∃ g : ∀ n, Geometry (dimension (θ : ℝ)) n,
      SamplerImplementation θ g ∧ TesterImplementation θ g := by
  exact ⟨fun n => binaryGeometry (dimension (θ : ℝ)) n,
    binary_sampler_implementation θ hθ, binary_tester_implementation θ hθ⟩

end ExpandingCodes.PolynomialStretch

end FlattenModule107

/-! Inlined whole module: ExpandingCodes.Construction.SamplerExpansion -/
section FlattenModule108


set_option autoImplicit false
open scoped Classical BigOperators Topology
open Filter

namespace ExpandingCodes.PolynomialStretch

theorem eventProb_sampleLaw (θ : ℝ) (n : ℕ) (g : Geometry (dimension θ) n)
    (E : Generator (rowCount (dimension θ) n) n → Prop) :
    eventProb (sampleLaw θ n g) E =
      uniformProb (fun p : Forms g.F (dimension θ) (arity θ) ×
        Hashes g.F (arity θ) (buckets θ n) => E (combined g p.1 p.2)) := by
  unfold sampleLaw
  rw [eventProb_map]
  rfl

theorem eventual_sampler_expansion (ε θ : ℝ)
    (hε : 0 < ε ∧ ε < 1/2) (hθ : ε/2 < θ ∧ θ < ε)
    (g : ∀ n, Geometry (dimension θ) n) :
    ∀ᶠ n : ℕ in atTop,
      1 - (n : ℝ) ^ (-1/ε) ≤ eventProb (sampleLaw θ n (g n))
        (fun G => Expanding G (1-ε) (arity θ) ((n : ℝ) ^ (1-ε))) := by
  have hθrange : 0 < θ ∧ θ < 1/2 :=
    ⟨(half_pos hε.1).trans hθ.1, hθ.2.trans hε.2⟩
  obtain ⟨δ, hδpos, hδlim, hδgood⟩ := hash_expansion_envelope θ hθrange g
  let pbad : ℕ → ℝ := fun n => uniformProb
    (fun s : Forms (g n).F (dimension θ) (arity θ) => ¬ PreliminaryGood θ n (g n) s)
  have hlim : Tendsto (fun n => (pbad n + δ n) * (n : ℝ) ^ (1/θ)) atTop (𝓝 0) := by
    simpa only [pbad, add_mul, zero_add] using
      (preliminary_expansion_limit θ hθrange g).add hδlim
  have hsmall := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hδgood, hsmall, eventually_ge_atTop 1] with n hn hnorm hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpow : (0 : ℝ) < (n : ℝ) ^ (1/θ) := by positivity
  have hinv : ε⁻¹ ≤ θ⁻¹ := (inv_le_inv₀ hε.1 hθrange.1).2 hθ.2.le
  have hexp : 0 ≤ -1/ε + 1/θ := by
    simp only [div_eq_mul_inv, neg_one_mul, one_mul]
    linarith
  have hbad : pbad n + δ n ≤ (n : ℝ) ^ (-1/ε) := by
    apply (mul_le_mul_iff_left₀ hpow).mp
    calc
      (pbad n + δ n) * (n : ℝ) ^ (1/θ) ≤ 1 := hnorm.le
      _ ≤ (n : ℝ) ^ (-1/ε) * (n : ℝ) ^ (1/θ) := by
        rw [← Real.rpow_add hnp]
        exact Real.one_le_rpow hnR hexp
  let Ω := Forms (g n).F (dimension θ) (arity θ) ×
    Hashes (g n).F (arity θ) (buckets θ n)
  let Good : Forms (g n).F (dimension θ) (arity θ) → Prop := PreliminaryGood θ n (g n)
  let E : Ω → Prop := fun p => Expanding (combined (g n) p.1 p.2)
    (1-θ) (arity θ) ((n : ℝ) ^ (1-θ))
  have hf : uniformProb (fun p : Ω => ¬ E p) ≤ pbad n + δ n := by
    exact uniformProb_conditional_bad_le Good (fun p => ¬ E p) (δ n) (hδpos n) hn
  have hc := uniformProb_compl E
  have hs : 1 - (pbad n + δ n) ≤ uniformProb E := by linarith
  rw [eventProb_sampleLaw]
  apply (show 1 - (n : ℝ) ^ (-1/ε) ≤ uniformProb E by linarith).trans
  apply uniformProb_mono
  intro p hp
  exact Expanding.mono hp (by linarith [hθ.2])
    (Real.rpow_le_rpow_of_exponent_le hnR (by linarith [hθ.2]))

end ExpandingCodes.PolynomialStretch

end FlattenModule108

/-! Inlined whole module: ExpandingCodes.Algebra.PolynomialSum -/
section FlattenModule109





/-!
Finite-field polynomial summation used in the proof of paper Lemma 2.2.
These interfaces are local and provisional, not the unavailable mission preamble.
-/

set_option autoImplicit false

namespace ExpandingCodes

open scoped BigOperators

variable {K σ : Type*} [Field K] [Fintype K] [Fintype σ] [DecidableEq σ]

/-- Summation of a monomial factors into independent one-coordinate sums. -/
theorem sum_eval_monomial (s : σ →₀ ℕ) (c : K) :
    (∑ x : σ → K, MvPolynomial.eval x (MvPolynomial.monomial s c)) =
      c * ∏ i : σ, ∑ a : K, a ^ s i := by
  classical
  simp_rw [MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [← Finset.mul_sum, Fintype.prod_sum]

/-- One exponent below `|K|-1` suffices for monomial orthogonality. -/
theorem sum_eval_monomial_eq_zero (s : σ →₀ ℕ) (c : K)
    (h : ∃ i, s i < Fintype.card K - 1) :
    (∑ x : σ → K, MvPolynomial.eval x (MvPolynomial.monomial s c)) = 0 := by
  classical
  rw [sum_eval_monomial]
  obtain ⟨i, hi⟩ := h
  have hz : (∏ j : σ, ∑ a : K, a ^ s j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (FiniteField.sum_pow_lt_card_sub_one K _ hi)
  rw [hz, mul_zero]

/-- A polynomial of total degree below `d(|K|-1)` sums to zero on `K^d`. -/
theorem sum_eval_eq_zero_of_totalDegree_lt (p : MvPolynomial σ K)
    (hp : p.totalDegree < Fintype.card σ * (Fintype.card K - 1)) :
    (∑ x : σ → K, MvPolynomial.eval x p) = 0 := by
  classical
  have heval (x : σ → K) :
      MvPolynomial.eval x p = ∑ s ∈ p.support,
        MvPolynomial.eval x (MvPolynomial.monomial s (p.coeff s)) := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum]
  simp_rw [heval]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro s hs
  apply sum_eval_monomial_eq_zero
  exact MvPolynomial.exists_degree_lt p (Fintype.card K - 1)
    (by simpa [Nat.mul_comm] using hp) hs









/-- The degree calculation for two row polynomials and a generator-column polynomial. -/
theorem sum_eval_triple_eq_zero (p q a : MvPolynomial σ K) (R S : ℕ)
    (hp : p.totalDegree ≤ R) (hq : q.totalDegree ≤ R) (ha : a.totalDegree ≤ S)
    (h : 2 * R + S < Fintype.card σ * (Fintype.card K - 1)) :
    (∑ x : σ → K,
      MvPolynomial.eval x p * MvPolynomial.eval x q * MvPolynomial.eval x a) = 0 := by
  have hdegree : ((p * q) * a).totalDegree <
      Fintype.card σ * (Fintype.card K - 1) := by
    calc
      ((p * q) * a).totalDegree ≤ (p * q).totalDegree + a.totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ p.totalDegree + q.totalDegree + a.totalDegree :=
        Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _
      _ ≤ R + R + S := Nat.add_le_add (Nat.add_le_add hp hq) ha
      _ = 2 * R + S := by omega
      _ < Fintype.card σ * (Fintype.card K - 1) := h
  simpa only [map_mul] using sum_eval_eq_zero_of_totalDegree_lt ((p * q) * a) hdegree

end ExpandingCodes

end FlattenModule109

/-! Inlined whole module: ExpandingCodes.Algebra.FlatIndicator -/
section FlattenModule110



/-!
Polynomial indicators for finite families of affine equations, including the
three equations defining a preliminary generator column in paper Section 2.1.
These interfaces are local and provisional, not platform-canonical statements.
-/

set_option autoImplicit false

namespace ExpandingCodes

open scoped BigOperators

variable {K σ ι : Type*} [Field K]

/-- A polynomial representation of a scalar affine form. -/
noncomputable def affinePolynomial [Fintype σ] (coefficients : σ → K) (constant : K) :
    MvPolynomial σ K :=
  MvPolynomial.C constant + ∑ i, MvPolynomial.C (coefficients i) * MvPolynomial.X i

theorem eval_affinePolynomial [Fintype σ] (coefficients : σ → K) (constant : K)
    (x : σ → K) :
    MvPolynomial.eval x (affinePolynomial coefficients constant) =
      constant + ∑ i, coefficients i * x i := by
  simp [affinePolynomial]

theorem totalDegree_affinePolynomial_le [Fintype σ]
    (coefficients : σ → K) (constant : K) :
    (affinePolynomial coefficients constant).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

variable [Fintype K]

/-- A polynomial taking value one precisely where `p` has value `a`. -/
noncomputable def equationIndicator (p : MvPolynomial σ K) (a : K) : MvPolynomial σ K :=
  1 - (p - MvPolynomial.C a) ^ (Fintype.card K - 1)

theorem eval_equationIndicator [DecidableEq K]
    (p : MvPolynomial σ K) (a : K) (x : σ → K) :
    MvPolynomial.eval x (equationIndicator p a) =
      if MvPolynomial.eval x p = a then 1 else 0 := by
  classical
  have hpos : Fintype.card K - 1 ≠ 0 := by
    have := Fintype.one_lt_card (α := K)
    omega
  simp only [equationIndicator, map_sub, map_pow, map_one, MvPolynomial.eval_C]
  split_ifs with h
  · rw [h, sub_self, zero_pow hpos, sub_zero]
  · rw [FiniteField.pow_card_sub_one_eq_one _ (sub_ne_zero.mpr h), sub_self]

theorem totalDegree_equationIndicator (p : MvPolynomial σ K) (a : K) :
    (equationIndicator p a).totalDegree ≤
      (Fintype.card K - 1) * p.totalDegree := by
  calc
    (equationIndicator p a).totalDegree ≤
        ((p - MvPolynomial.C a) ^ (Fintype.card K - 1)).totalDegree := by
      exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
    _ ≤ (Fintype.card K - 1) * (p - MvPolynomial.C a).totalDegree :=
      MvPolynomial.totalDegree_pow _ _
    _ ≤ (Fintype.card K - 1) * p.totalDegree :=
      Nat.mul_le_mul_left _ (MvPolynomial.totalDegree_sub_C_le _ _)

/-- The product indicator of a finite system of polynomial equations. -/
noncomputable def flatIndicator [Fintype ι]
    (forms : ι → MvPolynomial σ K) (values : ι → K) : MvPolynomial σ K :=
  ∏ i, equationIndicator (forms i) (values i)

theorem eval_flatIndicator [Fintype ι] [DecidableEq K]
    (forms : ι → MvPolynomial σ K) (values : ι → K) (x : σ → K) :
    MvPolynomial.eval x (flatIndicator forms values) =
      if ∀ i, MvPolynomial.eval x (forms i) = values i then 1 else 0 := by
  classical
  simp only [flatIndicator, map_prod, eval_equationIndicator]
  split_ifs with h
  · exact Finset.prod_eq_one fun i _ => if_pos (h i)
  · obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Affine equations have total degree at most one, so each contributes `|K|-1`. -/
theorem totalDegree_flatIndicator_le [Fintype ι]
    (forms : ι → MvPolynomial σ K) (values : ι → K)
    (hforms : ∀ i, (forms i).totalDegree ≤ 1) :
    (flatIndicator forms values).totalDegree ≤ Fintype.card ι * (Fintype.card K - 1) := by
  calc
    (flatIndicator forms values).totalDegree ≤
        ∑ i, (equationIndicator (forms i) (values i)).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _i : ι, (Fintype.card K - 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_equationIndicator _ _).trans
        (by simpa using Nat.mul_le_mul_left (Fintype.card K - 1) (hforms i))
    _ = Fintype.card ι * (Fintype.card K - 1) := by simp













end ExpandingCodes

end FlattenModule110

/-! Inlined whole module: ExpandingCodes.Algebra.PreliminaryOrthogonality -/
section FlattenModule111



/-!
Bridge from the exact platform sampler and monomial-evaluation definitions to
finite-field polynomial orthogonality. All declarations here are local helpers.
-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- The three affine forms for one fixed preliminary column. The sampled forms
are selected using the fixed column address `a`. -/
noncomputable def preliminaryColumnForms {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (i : Fin k) (a : g.F) :
    Fin 3 → MvPolynomial (Fin d) g.F :=
  ![ExpandingCodes.affinePolynomial (fun j => alpha g i ^ j.val) 0,
    ExpandingCodes.affinePolynomial (s 0 i a) 0,
    ExpandingCodes.affinePolynomial (s 1 i a) 0]

/-- Polynomial whose evaluation is the indicator of a preliminary column. -/
noncomputable def preliminaryColumnPolynomial {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (c : Fin k × (g.F × g.F × g.F)) :
    MvPolynomial (Fin d) g.F :=
  ExpandingCodes.flatIndicator (preliminaryColumnForms g s c.1 c.2.1)
    ![c.2.1, c.2.2.1, c.2.2.2]

theorem totalDegree_preliminaryColumnPolynomial_le {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (c : Fin k × (g.F × g.F × g.F)) :
    (preliminaryColumnPolynomial g s c).totalDegree ≤ 3 * (Fintype.card g.F - 1) := by
  have hforms : ∀ i : Fin 3, (preliminaryColumnForms g s c.1 c.2.1 i).totalDegree ≤ 1 := by
    intro i
    fin_cases i <;>
      exact ExpandingCodes.totalDegree_affinePolynomial_le _ _
  simpa [preliminaryColumnPolynomial] using
    ExpandingCodes.totalDegree_flatIndicator_le
      (preliminaryColumnForms g s c.1 c.2.1) ![c.2.1, c.2.2.1, c.2.2.2] hforms

theorem eval_preliminaryColumnPolynomial {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (c : Fin k × (g.F × g.F × g.F)) (z : Fin d → g.F) :
    MvPolynomial.eval z (preliminaryColumnPolynomial g s c) =
      if address g s c.1 z = c.2 then 1 else 0 := by
  rw [preliminaryColumnPolynomial, ExpandingCodes.eval_flatIndicator]
  have hpred :
      (∀ i : Fin 3, MvPolynomial.eval z (preliminaryColumnForms g s c.1 c.2.1 i) =
        ![c.2.1, c.2.2.1, c.2.2.2] i) ↔ address g s c.1 z = c.2 := by
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, preliminaryColumnForms,
      Matrix.cons_val_zero, Matrix.cons_val_succ, ExpandingCodes.eval_affinePolynomial,
      zero_add, and_true]
    change (fixedForm g c.1 z = c.2.1 ∧
      linearForm (s 0 c.1 c.2.1) z = c.2.2.1 ∧
      linearForm (s 1 c.1 c.2.1) z = c.2.2.2) ↔ _
    by_cases hfirst : fixedForm g c.1 z = c.2.1
    · simp [address, Prod.ext_iff, hfirst]
    · simp [address, Prod.ext_iff, hfirst]
  simp only [hpred]

theorem eval_preliminaryColumnPolynomial_row {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (c : Fin k × (g.F × g.F × g.F)) (z : Fin (rowCount d n)) :
    MvPolynomial.eval (g.rowOrder z) (preliminaryColumnPolynomial g s c) =
      if preliminary g s z c = 0 then (0 : g.F) else 1 := by
  rw [eval_preliminaryColumnPolynomial]
  by_cases hx : address g s c.1 (g.rowOrder z) = c.2 <;> simp [preliminary, hx]

/-- Polynomial representing a platform monomial row; no individual-degree reduction is needed. -/
noncomputable def rowMonomialPolynomial {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (a : Monomials F d R) : MvPolynomial (Fin d) F :=
  ∏ i, MvPolynomial.X i ^ (a.val i).val

theorem eval_rowMonomialPolynomial {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (a : Monomials F d R) (z : Fin d → F) :
    MvPolynomial.eval z (rowMonomialPolynomial a) = monomialEval a z := by
  simp [rowMonomialPolynomial, monomialEval]

theorem totalDegree_rowMonomialPolynomial_le {F : Type*} [Field F] [Fintype F] {d R : ℕ}
    (a : Monomials F d R) : (rowMonomialPolynomial a).totalDegree ≤ R := by
  exact (MvPolynomial.totalDegree_finsetProd _ _).trans
    (by simpa using a.property)

/-- Every product of two degree-`R` platform monomial rows is orthogonal to
every preliminary column, under the paper's explicit strict degree inequality. -/
theorem preliminary_monomial_pair_orthogonal {d n k R : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (c : Fin k × (g.F × g.F × g.F))
    (a b : Monomials g.F d R)
    (hdegree : 2 * R + 3 * (Fintype.card g.F - 1) < d * (Fintype.card g.F - 1)) :
    (∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
      monomialEval b (g.rowOrder z) *
      (if preliminary g s z c = 0 then (0 : g.F) else 1)) = 0 := by
  have hsum := ExpandingCodes.sum_eval_triple_eq_zero
    (rowMonomialPolynomial a) (rowMonomialPolynomial b) (preliminaryColumnPolynomial g s c)
    R (3 * (Fintype.card g.F - 1))
    (totalDegree_rowMonomialPolynomial_le a) (totalDegree_rowMonomialPolynomial_le b)
    (totalDegree_preliminaryColumnPolynomial_le g s c)
    (by simpa using hdegree)
  rw [← g.rowOrder.sum_comp] at hsum
  simpa only [eval_rowMonomialPolynomial, eval_preliminaryColumnPolynomial_row] using hsum

end ExpandingCodes.PolynomialStretch

end FlattenModule111

/-! Inlined whole module: ExpandingCodes.Algebra.AuxiliaryDegree -/
section FlattenModule112


set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch

/-- The exact platform integer-floor choice satisfies the strict orthogonality bound. -/
theorem auxiliaryDegree_strict_degree_bound (q d : ℕ) (hd : 4 ≤ d) (hq : 2 ≤ q) :
    2 * auxiliaryDegree q d + 3 * (q - 1) < d * (q - 1) := by
  have hd' : (4 : ℤ) ≤ d := by exact_mod_cast hd
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hnum : 0 ≤ ((d : ℤ) - 3) * ((q : ℤ) - 1) - 1 := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (d : ℤ) - 4 by omega)
      (show (0 : ℤ) ≤ (q : ℤ) - 2 by omega)]
  have hdiv : 0 ≤ (((d : ℤ) - 3) * ((q : ℤ) - 1) - 1) / 2 :=
    Int.ediv_nonneg hnum (by norm_num)
  have hcast : ((auxiliaryDegree q d : ℕ) : ℤ) =
      (((d : ℤ) - 3) * ((q : ℤ) - 1) - 1) / 2 := by
    exact Int.toNat_of_nonneg hdiv
  have hfloor : 2 * ((((d : ℤ) - 3) * ((q : ℤ) - 1) - 1) / 2) ≤
      ((d : ℤ) - 3) * ((q : ℤ) - 1) - 1 := by omega
  have hqcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  have hfinal : (2 : ℤ) * (auxiliaryDegree q d : ℤ) + 3 * ((q - 1 : ℕ) : ℤ) <
      (d : ℤ) * ((q - 1 : ℕ) : ℤ) := by
    rw [hcast, hqcast]
    nlinarith
  exact_mod_cast hfinal

end ExpandingCodes.PolynomialStretch

end FlattenModule112

/-! Inlined whole module: ExpandingCodes.Algebra.CombinedOrthogonality -/
section FlattenModule113



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- The unique prime-field map realizes binary coordinates in a characteristic-two field. -/
noncomputable def bitToField (F : Type*) [Field F] [CharP F 2] : Bit →+* F :=
  ZMod.castHom (dvd_refl 2) F

theorem bitToField_apply {F : Type*} [Field F] [CharP F 2] (v : Bit) :
    bitToField F v = if v = 0 then 0 else 1 := by
  fin_cases v
  · change bitToField F 0 = if (0 : Bit) = 0 then 0 else 1
    simp
  · change bitToField F 1 = if (1 : Bit) = 0 then 0 else 1
    simp

/-- Each combined column is a binary sum of preliminary columns. Positivity of
the bucket count gives uniqueness of the layer/bucket position; no size cutoff is used. -/
theorem combined_eq_sum_preliminary {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hb : 0 < b)
    (z : Fin (rowCount d n)) (j : Fin n) :
    combined g s h z j =
      ∑ c : Fin k × (g.F × g.F × g.F),
        (if j.val = c.1.val * b + (h c.1 c.2).val then 1 else 0) * preliminary g s z c := by
  rw [Fintype.sum_prod_type]
  simp only [preliminary, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hpred :
      (∃ i : Fin k, ∃ u : Fin b, j.val = i.val * b + u.val ∧
        h i (address g s i (g.rowOrder z)) = u) ↔
      ∃ i : Fin k, j.val = i.val * b + (h i (address g s i (g.rowOrder z))).val := by
    constructor
    · rintro ⟨i, u, hi, hu⟩
      exact ⟨i, by simpa [hu] using hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, _, hi, rfl⟩
  simp only [combined, hpred]
  let P (i : Fin k) := j.val = i.val * b + (h i (address g s i (g.rowOrder z))).val
  have hquot (i : Fin k) :
      (i.val * b + (h i (address g s i (g.rowOrder z))).val) / b = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb,
      Nat.div_eq_of_lt (h i (address g s i (g.rowOrder z))).isLt, Nat.zero_add]
  have hunique (i i' : Fin k) (hi : P i) (hi' : P i') : i = i' := by
    apply Fin.ext
    have heq := congrArg (fun m : ℕ => m / b) (hi.symm.trans hi')
    simpa only [hquot] using heq
  change (if ∃ i, P i then (1 : Bit) else 0) = ∑ i, if P i then 1 else 0
  by_cases hex : ∃ i, P i
  · rw [if_pos hex]
    obtain ⟨i, hi⟩ := hex
    symm
    calc
      (∑ i', if P i' then (1 : Bit) else 0) = if P i then 1 else 0 := by
        apply Finset.sum_eq_single i
        · intro i' _ hne
          apply if_neg
          intro hi'
          exact hne (hunique i' i hi' hi)
        · simp
      _ = 1 := if_pos hi
  · rw [if_neg hex]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg fun hi => hex ⟨i, hi⟩

/-- Preliminary-column orthogonality with the exact auxiliary-degree choice. -/
theorem preliminary_auxiliary_pair_orthogonal {d n k : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (c : Fin k × (g.F × g.F × g.F))
    (a b : Monomials g.F d (auxiliaryDegree (Fintype.card g.F) d)) (hd : 4 ≤ d) :
    (∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
      monomialEval b (g.rowOrder z) * bitToField g.F (preliminary g s z c)) = 0 := by
  simpa only [bitToField_apply] using preliminary_monomial_pair_orthogonal g s c a b
    (auxiliaryDegree_strict_degree_bound _ _ hd Fintype.one_lt_card)

/-- Column combining preserves the preliminary monomial-pair orthogonality. -/
theorem combined_auxiliary_pair_orthogonal {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (hb : 0 < b)
    (a a' : Monomials g.F d (auxiliaryDegree (Fintype.card g.F) d))
    (j : Fin n) (hd : 4 ≤ d) :
    (∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
      monomialEval a' (g.rowOrder z) * bitToField g.F (combined g s h z j)) = 0 := by
  let coefficient (c : Fin k × (g.F × g.F × g.F)) : g.F :=
    bitToField g.F (if j.val = c.1.val * b + (h c.1 c.2).val then 1 else 0)
  have hmap (z : Fin (rowCount d n)) :
      bitToField g.F (combined g s h z j) =
        ∑ c : Fin k × (g.F × g.F × g.F),
          coefficient c * bitToField g.F (preliminary g s z c) := by
    rw [combined_eq_sum_preliminary g s h hb]
    simp only [map_sum, map_mul, coefficient]
  simp_rw [hmap, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro c _
  calc
    (∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
        monomialEval a' (g.rowOrder z) *
        (coefficient c * bitToField g.F (preliminary g s z c))) =
        coefficient c * ∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
          monomialEval a' (g.rowOrder z) * bitToField g.F (preliminary g s z c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = 0 := by rw [preliminary_auxiliary_pair_orthogonal g s c a a' hd, mul_zero]

/-- Exact coordinate formula for the canonical test matrix. -/
theorem testMatrix_apply {d n : ℕ} (g : Geometry d n) (y : Word (rowCount d n))
    (a a' : Monomials g.F d (auxiliaryDegree (Fintype.card g.F) d)) :
    testMatrix g y a a' =
      ∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
        monomialEval a' (g.rowOrder z) * bitToField g.F (y z) := by
  rw [testMatrix, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply,
    evaluationMatrix, bitToField_apply]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- The algebraic annihilation assertion holds for every input size, once the
dimension and bucket count satisfy their elementary standing bounds. -/
theorem testMatrix_combined_mulVec_eq_zero {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (x : Word n)
    (hd : 4 ≤ d) (hb : 0 < b) : testMatrix g ((combined g s h).mulVec x) = 0 := by
  ext a a'
  rw [testMatrix_apply]
  simp only [Matrix.zero_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  calc
    (∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
        monomialEval a' (g.rowOrder z) *
        (bitToField g.F (combined g s h z j) * bitToField g.F (x j))) =
        (∑ z : Fin (rowCount d n), monomialEval a (g.rowOrder z) *
          monomialEval a' (g.rowOrder z) * bitToField g.F (combined g s h z j)) *
          bitToField g.F (x j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = 0 := by rw [combined_auxiliary_pair_orthogonal g s h hb a a' j hd, zero_mul]

/-- The canonical test matrix is additive on binary words. -/
theorem testMatrix_add {d n : ℕ} (g : Geometry d n)
    (y e : Word (rowCount d n)) :
    testMatrix g (y + e) = testMatrix g y + testMatrix g e := by
  ext a a'
  simp only [testMatrix_apply, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib,
    Matrix.add_apply]

/-- A test matrix supported on `e` has rank at most the binary Hamming weight. -/
theorem testMatrix_rank_le_weight {d n : ℕ} (g : Geometry d n)
    (e : Word (rowCount d n)) : (testMatrix g e).rank ≤ weight e := by
  have hrank := ((Matrix.rank_mul_le_left
      (evaluationMatrix g * Matrix.diagonal (fun z => if e z = 0 then (0 : g.F) else 1))
      (evaluationMatrix g).transpose).trans
      (Matrix.rank_mul_le_right (evaluationMatrix g)
        (Matrix.diagonal (fun z => if e z = 0 then (0 : g.F) else 1)))).trans_eq
      (Matrix.rank_diagonal (fun z => if e z = 0 then (0 : g.F) else 1))
  simpa [testMatrix, weight, Fintype.card_subtype] using hrank

/-- Full arbitrary-error conclusion after algebraic annihilation. -/
theorem testMatrix_combined_corruption_rank_le_weight {d n k b : ℕ} (g : Geometry d n)
    (s : Forms g.F d k) (h : Hashes g.F k b) (x : Word n)
    (e : Word (rowCount d n)) (hd : 4 ≤ d) (hb : 0 < b) :
    (testMatrix g ((combined g s h).mulVec x + e)).rank ≤ weight e := by
  rw [testMatrix_add, testMatrix_combined_mulVec_eq_zero g s h x hd hb, zero_add]
  exact testMatrix_rank_le_weight g e

end ExpandingCodes.PolynomialStretch

end FlattenModule113

/-! Inlined whole module: ExpandingCodes.Algebra.RankBounds -/
section FlattenModule114




/-!
# Algebraic rank ingredients for the canonical polynomial test

The statements use the mission's exact matrices, auxiliary code and ambiguity.
The point support is transported through the exact `Geometry.rowOrder` equivalence.
Sylvester's inequality, coordinate restriction rank-nullity, and a restricted
Gram factorization prove the rank lower bound. A one-coordinate difference has
weight at most one, which proves the real-valued rank has unit bounded differences.
No erasure or probabilistic hypotheses occur in these algebraic statements.
-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

open Module

/-- Sylvester's inequality for finite matrices over an arbitrary field. -/
theorem matrix_rank_add_rank_le_rank_mul_add {F I J K : Type*} [Field F]
    [Fintype I] [Fintype J] [Fintype K]
    (A : Matrix I J F) (B : Matrix J K F) :
    A.rank + B.rank ≤ (A*B).rank + Fintype.card J := by
  let f := A.mulVecLin
  let g := B.mulVecLin
  let h := f.domRestrict (LinearMap.range g)
  let e : LinearMap.ker h →ₗ[F] LinearMap.ker f :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker f => z.val) hxy
  have hk := LinearMap.finrank_le_finrank_of_injective he
  have hn := h.finrank_range_add_finrank_ker
  have hf := f.finrank_range_add_finrank_ker
  have hr : LinearMap.range h = LinearMap.range (f.comp g) := by
    rw [LinearMap.range_domRestrict, LinearMap.range_comp]
  rw [hr] at hn
  change A.rank + B.rank ≤ (A*B).rank + Fintype.card J
  change Module.finrank F (LinearMap.range f) + Module.finrank F (LinearMap.range g) ≤
    Module.finrank F (LinearMap.range (A*B).mulVecLin) + Fintype.card J
  rw [Matrix.mulVecLin_mul]
  change Module.finrank F (LinearMap.range f) + Module.finrank F (LinearMap.range g) ≤
    Module.finrank F (LinearMap.range (f.comp g)) + Fintype.card J
  rw [Module.finrank_pi] at hf
  omega

/-- Subadditivity of matrix rank, using the sum of the two image spaces. -/
theorem matrix_rank_add_le {F I J : Type*} [Field F] [Fintype I] [Fintype J]
    (A B : Matrix I J F) : (A+B).rank ≤ A.rank + B.rank := by
  have hr : LinearMap.range (A+B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    rw [Matrix.mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  exact (Submodule.finrank_mono hr).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- Restrict a codeword to a finite set of observed coordinates. -/
def codeRestriction {F I : Type*} [Field F] [Fintype I]
    (C : Submodule F (I → F)) (S : Finset I) : C →ₗ[F] (S → F) where
  toFun c i := c.val i.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem codeRestriction_ker {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (C : Submodule F (I → F)) (S : Finset I) :
    LinearMap.ker (codeRestriction C S) = (ambiguity C Sᶜ).comap C.subtype := by
  ext c
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · intro h
    exact ⟨c.property, fun i hi => congrFun h ⟨i, by simpa using hi⟩⟩
  · intro h
    funext i
    exact h.2 i.val (by simp)

/-- Rank-nullity identifies the exact loss under coordinate restriction. -/
theorem finrank_codeRestriction_add_ambiguity {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (C : Submodule F (I → F)) (S : Finset I) :
    finrank F (LinearMap.range (codeRestriction C S)) +
      finrank F (ambiguity C Sᶜ) = finrank F C := by
  have hle : ambiguity C Sᶜ ≤ C := fun _ hc => hc.1
  have he := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  rw [← he, ← codeRestriction_ker]
  exact LinearMap.finrank_range_add_finrank_ker _

/-- Restricting a row generator matrix is exactly restriction of its row code. -/
theorem matrix_restriction_rank_add_ambiguity {F I J : Type*} [Field F]
    [Fintype I] [Fintype J] [DecidableEq I] (A : Matrix J I F) (S : Finset I) :
    (A.submatrix id (Subtype.val : S → I)).rank +
      finrank F (ambiguity (Submodule.span F (Set.range A.row)) Sᶜ) =
        finrank F (Submodule.span F (Set.range A.row)) := by
  let C := Submodule.span F (Set.range A.row)
  let r : (I → F) →ₗ[F] (S → F) := LinearMap.funLeft F F Subtype.val
  have hr : LinearMap.range (codeRestriction C S) =
      Submodule.span F (Set.range (A.submatrix id (Subtype.val : S → I)).row) := by
    change LinearMap.range (r.domRestrict C) = _
    rw [LinearMap.range_domRestrict]
    dsimp [C]
    rw [LinearMap.map_span]
    congr 1
    ext v
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨A.row j, ⟨j, rfl⟩, rfl⟩
  rw [Matrix.rank_eq_finrank_span_row, ← hr]
  exact finrank_codeRestriction_add_ambiguity C S

/-- Actual support of a binary word, indexed by the canonical geometric points. -/
noncomputable def supportPoints {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) : Finset (Fin d → g.F) :=
  (Finset.univ.filter (fun z => y z ≠ 0)).image g.rowOrder

@[simp] theorem mem_supportPoints {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) (z : Fin d → g.F) :
    z ∈ supportPoints g y ↔ y (g.rowOrder.symm z) ≠ 0 := by
  simp only [supportPoints, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, hiz⟩
    simpa only [← hiz, g.rowOrder.symm_apply_apply] using hi
  · intro hz
    exact ⟨g.rowOrder.symm z, hz, g.rowOrder.apply_symm_apply z⟩

@[simp] theorem card_supportPoints {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) : (supportPoints g y).card = weight y := by
  unfold supportPoints
  rw [Finset.card_image_of_injective _ g.rowOrder.injective]
  unfold weight
  congr 1
  ext z
  simp

/-- Evaluation matrix with precisely the columns on a specified geometric set. -/
noncomputable def restrictedEvaluationMatrix {d n : ℕ} (g : Geometry d n)
    (S : Finset (Fin d → g.F)) :
    Matrix (Monomials g.F d (auxiliaryDegree (Fintype.card g.F) d)) S g.F :=
  fun a z => monomialEval a z.val










/-- Restriction loses exactly the ambiguity supported outside the observed points. -/
theorem restrictedEvaluationMatrix_rank_add_ambiguity {d n : ℕ} (g : Geometry d n)
    (S : Finset (Fin d → g.F)) :
    (restrictedEvaluationMatrix g S).rank +
      finrank g.F (ambiguity (auxiliaryCode g) Sᶜ) = finrank g.F (auxiliaryCode g) := by
  exact matrix_restriction_rank_add_ambiguity
    (fun a z => monomialEval (F := g.F) (d := d)
      (R := auxiliaryDegree (Fintype.card g.F) d) a z) S








/-- The diagonal binary mask is exactly restriction to the nonzero columns. -/
theorem testMatrix_eq_restricted_mul_transpose {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) :
    testMatrix g y = restrictedEvaluationMatrix g (supportPoints g y) *
      (restrictedEvaluationMatrix g (supportPoints g y)).transpose := by
  ext a b
  rw [testMatrix_apply, Matrix.mul_apply]
  simp only [restrictedEvaluationMatrix, Matrix.transpose_apply]
  rw [Finset.sum_coe_sort (supportPoints g y)
    (fun z => monomialEval a z * monomialEval b z)]
  have he : (∑ i, monomialEval a (g.rowOrder i) * monomialEval b (g.rowOrder i) *
      bitToField g.F (y i)) =
      ∑ z : Fin d → g.F, monomialEval a z * monomialEval b z *
        bitToField g.F (y (g.rowOrder.symm z)) := by
    exact Fintype.sum_equiv g.rowOrder _ _ (by intro i; simp)
  rw [he]
  calc
    _ = ∑ z ∈ supportPoints g y, monomialEval a z * monomialEval b z *
          bitToField g.F (y (g.rowOrder.symm z)) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro z _ hz
      have hy : y (g.rowOrder.symm z) = 0 := by simpa using hz
      simp [hy]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [bitToField_apply, if_neg ((mem_supportPoints g y z).mp hz), mul_one]

/-- The algebraic rank lower bound used in Proposition 2.5, in additive natural form. -/
theorem testMatrix_rank_lower_additive {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) :
    2 * finrank g.F (auxiliaryCode g) ≤ (testMatrix g y).rank +
      2 * finrank g.F (ambiguity (auxiliaryCode g) (supportPoints g y)ᶜ) + weight y := by
  have hs := matrix_rank_add_rank_le_rank_mul_add
    (restrictedEvaluationMatrix g (supportPoints g y))
    (restrictedEvaluationMatrix g (supportPoints g y)).transpose
  rw [Matrix.rank_transpose, ← testMatrix_eq_restricted_mul_transpose,
    Fintype.card_coe, card_supportPoints] at hs
  have hr := restrictedEvaluationMatrix_rank_add_ambiguity g (supportPoints g y)
  omega

/-- Real-valued form avoids truncation in the two ambiguity corrections. -/
theorem testMatrix_rank_lower {d n : ℕ} (g : Geometry d n)
    (y : Word (rowCount d n)) :
    2 * (finrank g.F (auxiliaryCode g) : ℝ) -
      2 * (finrank g.F (ambiguity (auxiliaryCode g) (supportPoints g y)ᶜ) : ℝ) -
        (weight y : ℝ) ≤ ((testMatrix g y).rank : ℝ) := by
  have h : 2 * (finrank g.F (auxiliaryCode g) : ℝ) ≤
      ((testMatrix g y).rank : ℝ) + 2 * (finrank g.F
        (ambiguity (auxiliaryCode g) (supportPoints g y)ᶜ) : ℝ) + (weight y : ℝ) := by
    exact_mod_cast testMatrix_rank_lower_additive g y
  linarith

/-- A word supported at one coordinate has Hamming weight at most one. -/
theorem weight_le_one_of_eq_zero_off {m : ℕ} (e : Word m) (i : Fin m)
    (he : ∀ j, j ≠ i → e j = 0) : weight e ≤ 1 := by
  unfold weight
  have hsub : (Finset.univ.filter (fun j => e j ≠ 0)) ⊆ {i} := by
    intro j hj
    simp only [Finset.mem_singleton]
    by_contra hji
    exact (Finset.mem_filter.mp hj).2 (he j hji)
  simpa using Finset.card_le_card hsub

/-- Changing one coordinate changes the matrix rank by at most one. -/
theorem testMatrix_rank_abs_sub_le_one {d n : ℕ} (g : Geometry d n)
    (y y' : Word (rowCount d n)) (i : Fin (rowCount d n))
    (h : ∀ j, j ≠ i → y' j = y j) :
    |((testMatrix g y').rank : ℝ) - ((testMatrix g y).rank : ℝ)| ≤ 1 := by
  have hdir (u v : Word (rowCount d n)) (huv : ∀ j, j ≠ i → v j = u j) :
      (testMatrix g v).rank ≤ (testMatrix g u).rank + 1 := by
    have hw : weight (v-u) ≤ 1 := weight_le_one_of_eq_zero_off _ i (by
      intro j hj
      simp [huv j hj])
    have hv : v = u + (v-u) := by abel
    calc
      _ = (testMatrix g u + testMatrix g (v-u)).rank := by
        rw [← testMatrix_add, ← hv]
      _ ≤ (testMatrix g u).rank + (testMatrix g (v-u)).rank := matrix_rank_add_le _ _
      _ ≤ (testMatrix g u).rank + 1 :=
        Nat.add_le_add_left ((testMatrix_rank_le_weight g _).trans hw) _
  have h₁ : ((testMatrix g y').rank : ℝ) ≤ ((testMatrix g y).rank : ℝ) + 1 := by
    exact_mod_cast hdir y y' h
  have h₂ : ((testMatrix g y).rank : ℝ) ≤ ((testMatrix g y').rank : ℝ) + 1 := by
    exact_mod_cast hdir y' y (fun j hj => (h j hj).symm)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Identify a Boolean cube point with the mission's binary word. -/
def boolWord {m : ℕ} (x : Fin m → Bool) : Word m := fun i => if x i then 1 else 0

theorem testMatrix_rank_boundedDifferences {d n : ℕ} (g : Geometry d n) :
    HasUnitBoundedDifferences
      (fun x : Fin (rowCount d n) → Bool => ((testMatrix g (boolWord x)).rank : ℝ)) := by
  intro x i b
  apply testMatrix_rank_abs_sub_le_one g (boolWord x) (boolWord (Function.update x i b)) i
  intro j hj
  simp [boolWord, Function.update_of_ne hj]

end ExpandingCodes.PolynomialStretch

end FlattenModule114

/-! Inlined whole module: ExpandingCodes.Probability.RankExpectation -/
section FlattenModule115



set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

open Module

/-- Uniform finite means are invariant under a bijective reindexing. -/
theorem uniformMean_equiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (f : Ξ → ℝ) : uniformMean (fun x => f (e x)) = uniformMean f := by
  unfold uniformMean
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem uniformMean_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (f : I → Ω → ℝ) :
    uniformMean (fun x => ∑ i, f i x) = ∑ i, uniformMean (f i) := by
  simp only [uniformMean, Finset.sum_div]
  exact Finset.sum_comm

/-- The mission's two-element field and a Boolean bit have identical values. -/
def boolBitEquiv : Bool ≃ Bit where
  toFun b := if b then 1 else 0
  invFun b := decide (b ≠ 0)
  left_inv b := by cases b <;> simp
  right_inv b := by
    fin_cases b
    · change (if (0 : Bit) = 0 then (0 : Bit) else 1) = 0
      simp
    · change (if (1 : Bit) = 0 then (0 : Bit) else 1) = 1
      simp

/-- Exact Boolean cube parametrization of the mission's binary words. -/
def boolWordEquiv (m : ℕ) : (Fin m → Bool) ≃ Word m :=
  Equiv.piCongrRight (fun _ => boolBitEquiv)

@[simp] theorem boolWordEquiv_apply (m : ℕ) (x : Fin m → Bool) :
    boolWordEquiv m x = boolWord x := rfl

/-- The erased geometric points are exactly the zero coordinates of the word. -/
noncomputable def boolErasureEquiv {d n : ℕ} (g : Geometry d n) :
    (Fin (rowCount d n) → Bool) ≃ Finset (Fin d → g.F) where
  toFun x := (supportPoints g (boolWord x))ᶜ
  invFun E i := decide (g.rowOrder i ∉ E)
  left_inv x := by
    funext i
    cases hx : x i <;> simp [boolWord, hx]
  right_inv E := by
    ext z
    simp [boolWord]

/-- The uniform mean of a binary coordinate is exactly one half. -/
theorem uniformMean_bool_coordinate {m : ℕ} (i : Fin m) :
    uniformMean (fun x : Fin m → Bool => if x i then (1 : ℝ) else 0) = 1/2 := by
  calc
    _ = uniformMean (fun x : Fin m → Bool => if x i = true then (1 : ℝ) else 0) := rfl
    _ = uniformProb (fun x : Fin m → Bool => x i = true) := by
      rw [uniformProb_eq_uniformMean]
      exact congrArg uniformMean (funext fun x => by
        by_cases hx : x i = true <;> simp [hx])
    _ = uniformProb (fun b : Bool => b = true) :=
      uniformProb_eval (Ω := Bool) i (fun b : Bool => b = true)
    _ = _ := by
      rw [uniformProb_eq_uniformMean]
      norm_num [uniformMean, Fintype.sum_bool]

/-- Exact first moment of Hamming weight on the uniform Boolean cube. -/
theorem uniformMean_weight_boolWord (m : ℕ) :
    uniformMean (fun x : Fin m → Bool => (weight (boolWord x) : ℝ)) = (m : ℝ)/2 := by
  have hw (x : Fin m → Bool) : (weight (boolWord x) : ℝ) =
      ∑ i, if x i then (1 : ℝ) else 0 := by
    unfold weight
    rw [Finset.natCast_card_filter]
    apply Finset.sum_congr rfl
    intro i _
    cases hx : x i <;> simp [boolWord, hx]
  simp_rw [hw]
  rw [uniformMean_sum]
  simp [uniformMean_bool_coordinate, div_eq_mul_inv]

/-- At half erasure every coordinate pattern has the same exact finite weight. -/
theorem half_pattern_weight {I : Type*} [Fintype I] (E : Finset I) :
    (1/2 : ℝ)^E.card * (1-(1/2 : ℝ))^(Fintype.card I-E.card) =
      (1/2 : ℝ)^(Fintype.card I) := by
  rw [show (1-(1/2 : ℝ)) = 1/2 by norm_num, ← pow_add]
  congr 1
  exact Nat.add_sub_of_le (Finset.card_le_univ E)

/-- Canonical half-erasure expectation is the uniform mean over all finite subsets. -/
theorem erasureExpectation_half_eq_uniformMean {F I : Type*} [Field F] [Fintype I]
    (C : Submodule F (I → F)) :
    erasureExpectation C (1/2) =
      uniformMean (fun E : Finset I => (finrank F (ambiguity C E) : ℝ)) := by
  unfold erasureExpectation uniformMean
  simp_rw [half_pattern_weight]
  rw [← Finset.mul_sum, Fintype.card_finset, Nat.cast_pow, Nat.cast_ofNat]
  apply (eq_div_iff (by positivity : (2 : ℝ)^Fintype.card I ≠ 0)).mpr
  have hp : (1/2 : ℝ)^Fintype.card I * (2 : ℝ)^Fintype.card I = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((1/2 : ℝ)^Fintype.card I * (2 : ℝ)^Fintype.card I) *
        ∑ E : Finset I, (finrank F (ambiguity C E) : ℝ) := by ring
    _ = _ := by rw [hp, one_mul]

/-- The ambiguity correction in the rank bound has the canonical half-erasure mean. -/
theorem uniformMean_ambiguity_support_compl {d n : ℕ} (g : Geometry d n) :
    uniformMean (fun x : Fin (rowCount d n) → Bool =>
      (finrank g.F (ambiguity (auxiliaryCode g) (supportPoints g (boolWord x))ᶜ) : ℝ)) =
        erasureExpectation (auxiliaryCode g) (1/2) := by
  rw [erasureExpectation_half_eq_uniformMean]
  have hE (x : Fin (rowCount d n) → Bool) :
      boolErasureEquiv g x = (supportPoints g (boolWord x))ᶜ := by
    ext z
    simp [boolErasureEquiv]
  apply Eq.trans ?_ (uniformMean_equiv (boolErasureEquiv g)
    (fun E : Finset (Fin d → g.F) => (finrank g.F (ambiguity (auxiliaryCode g) E) : ℝ)))
  apply congrArg uniformMean
  funext x
  rw [hE x]

/-- Exact finite mean-rank lower bound, before any limiting or rate assumptions. -/
theorem testMatrix_rank_mean_lower {d n : ℕ} (g : Geometry d n) :
    2 * (finrank g.F (auxiliaryCode g) : ℝ) -
      2 * erasureExpectation (auxiliaryCode g) (1/2) - (rowCount d n : ℝ)/2 ≤
        uniformMean (fun x : Fin (rowCount d n) → Bool =>
          ((testMatrix g (boolWord x)).rank : ℝ)) := by
  have h := uniformMean_mono (fun x : Fin (rowCount d n) → Bool =>
    testMatrix_rank_lower g (boolWord x))
  simpa only [uniformMean_sub, uniformMean_mul, uniformMean_const,
    uniformMean_ambiguity_support_compl, uniformMean_weight_boolWord] using h













end ExpandingCodes.PolynomialStretch

end FlattenModule115

/-! Inlined whole module: ExpandingCodes.Algebra.CodeReindex -/
section FlattenModule119


set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

noncomputable def coordinateLinearEquiv {F I J : Type*} [Field F] (e : J ≃ I) :
    (I → F) ≃ₗ[F] (J → F) where
  toFun c := c ∘ e
  invFun c := c ∘ e.symm
  left_inv c := by funext i; simp
  right_inv c := by funext j; simp
  map_add' c c' := rfl
  map_smul' a c := rfl

noncomputable def codeReindex {F I J : Type*} [Field F] (e : J ≃ I)
    (C : Submodule F (I → F)) : Submodule F (J → F) :=
  C.map (coordinateLinearEquiv (F := F) e).toLinearMap

@[simp] theorem mem_codeReindex {F I J : Type*} [Field F] (e : J ≃ I)
    (C : Submodule F (I → F)) (c : J → F) :
    c ∈ codeReindex e C ↔ (fun i => c (e.symm i)) ∈ C := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa [coordinateLinearEquiv] using hv
  · intro hc
    refine ⟨(fun i => c (e.symm i)), hc, ?_⟩
    funext j
    simp [coordinateLinearEquiv]

@[simp] theorem finrank_codeReindex {F I J : Type*} [Field F] (e : J ≃ I)
    (C : Submodule F (I → F)) :
    Module.finrank F (codeReindex e C) = Module.finrank F C :=
  (coordinateLinearEquiv (F := F) e).finrank_map_eq C




































































end ExpandingCodes.PolynomialStretch

end FlattenModule119

/-! Inlined whole module: ExpandingCodes.Probability.Erasure -/
section FlattenModule121









/-!
# Erasure ambiguity and the finite Boolean reduction

These interfaces are provisional local formulations of paper Lemma 2.3,
not definitions obtained from the Prove2 platform. The scalar field is arbitrary
and may vary with the sequence index. In particular, no fixed alphabet assumption
is used. The remaining Boolean sharp-threshold obligations are recorded in
`harness/tasks/erasure_capacity.json`.
-/

set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.Erasure

open Module Filter Finset

variable {K I : Type*} [Field K]

/-- Words in `C` supported on the erased set `E`. -/
def ambiguity (C : Submodule K (I → K)) (E : Set I) : Submodule K (I → K) where
  carrier := {c | c ∈ C ∧ ∀ i ∉ E, c i = 0}
  zero_mem' := ⟨C.zero_mem, by simp⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨C.add_mem hx.1 hy.1, fun i hi => by simp [hx.2 i hi, hy.2 i hi]⟩
  smul_mem' := by
    intro a x hx
    exact ⟨C.smul_mem a hx.1, fun i hi => by simp [hx.2 i hi]⟩

@[simp] theorem mem_ambiguity (C : Submodule K (I → K)) (E : Set I) (c : I → K) :
    c ∈ ambiguity C E ↔ c ∈ C ∧ ∀ i ∉ E, c i = 0 := Iff.rfl









@[simp] theorem ambiguity_empty (C : Submodule K (I → K)) :
    ambiguity C ∅ = ⊥ := by
  apply le_antisymm
  · intro c hc
    exact show c = 0 from funext fun i => hc.2 i (by simp)
  · exact bot_le

@[simp] theorem ambiguity_univ (C : Submodule K (I → K)) :
    ambiguity C Set.univ = C := by
  ext c
  simp





























































































variable [Fintype I]



























































/-- Probability of a particular independently erased coordinate set. -/
noncomputable def patternWeight (p : ℝ) (E : Finset I) : ℝ :=
  p ^ E.card * (1 - p) ^ (Fintype.card I - E.card)





theorem sum_patternWeight (p : ℝ) : ∑ E : Finset I, patternWeight p E = 1 := by
  classical
  simpa [patternWeight] using (Fintype.sum_pow_mul_eq_add_pow I p (1 - p))

/-- Finite Bernoulli expectation. The weights sum to one and are nonnegative
on `[0,1]`; no measurable-space or fixed-field convention is hidden here. -/
noncomputable def expectation (p : ℝ) (f : Finset I → ℝ) : ℝ :=
  ∑ E : Finset I, patternWeight p E * f E

/-- The same independent erasure expectation on a specified finite coordinate set. -/
noncomputable def expectationOn (s : Finset I) (p : ℝ) (f : Finset I → ℝ) : ℝ :=
  ∑ E ∈ s.powerset, p ^ E.card * (1 - p) ^ (s.card - E.card) * f E















@[simp] theorem expectationOn_const (s : Finset I) (p a : ℝ) :
    expectationOn s p (fun _ => a) = a := by
  classical
  unfold expectationOn
  rw [← Finset.sum_mul, Finset.sum_pow_mul_eq_add_pow]
  simp















































































































































































































































@[simp] theorem expectation_const (p a : ℝ) : expectation (I := I) p (fun _ => a) = a := by
  classical
  rw [expectation, ← Finset.sum_mul, sum_patternWeight, one_mul]







































































































































































end ExpandingCodes.Erasure

end FlattenModule121

/-! Inlined whole module: ExpandingCodes.Probability.SharpThreshold.Basic -/
section FlattenModule122






/-!
# A qualitative Boolean sharp-threshold route

These are independent, provisional Boolean-analysis interfaces, not platform
axioms or a completed sharp-threshold proof. The remaining analytic obligations
are explicitly registered in `harness/tasks/sharp_threshold.json`.

The proposed route uses a fixed Fourier cutoff and only then takes the cutoff
to infinity. It does not require the quantitative logarithmic KKL inequality.
-/

set_option autoImplicit false

namespace ExpandingCodes.SharpThreshold

open Finset
open ExpandingCodes.Erasure

variable {I : Type*} [Fintype I]


























/-- The centered, normalized biased coordinate. -/
noncomputable def coordinate (p : ℝ) (i : I) (E : Finset I) : ℝ := by
  classical
  exact ((if i ∈ E then 1 else 0) - p) / Real.sqrt (p * (1 - p))

noncomputable def character (p : ℝ) (S E : Finset I) : ℝ :=
  ∏ i ∈ S, coordinate p i E

noncomputable def fourier (p : ℝ) (f : Finset I → ℝ) (S : Finset I) : ℝ :=
  expectation p (fun E => f E * character p S E)








































































































































































end ExpandingCodes.SharpThreshold

end FlattenModule122

/-! Inlined whole module: ExpandingCodes.Probability.SharpThreshold.FourierBasis -/
section FlattenModule126




/-! Finite biased Fourier analysis from an explicit tensor-product delta kernel. -/

set_option autoImplicit false
open scoped Classical
namespace ExpandingCodes.SharpThreshold
open Finset
open ExpandingCodes.Erasure
variable {I : Type*} [Fintype I]




























































































































@[simp] lemma fourier_empty (p : ℝ) (f : Finset I → ℝ) :
    fourier p f ∅ = expectation p f := by
  simp [fourier, character]

end ExpandingCodes.SharpThreshold

end FlattenModule126

/-! Inlined whole module: ExpandingCodes.Probability.Distinguishing -/
section FlattenModule137







/-!
# Exact rank-test distinguishing bounds

The uniform lower tail uses finite rank expectation and sharp bounded differences.
The biased upper tail uses Mathlib's scalar Hoeffding lemma followed by an exact
finite Bernoulli generating function and Chernoff optimization. The asymptotic
input is the mission's canonical `auxiliary_rate`; no target or construction
obligation is imported. The final assembly preserves both Proposition 2.5 constants.
-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

open Filter Module

/-- A quantitative mean-rank bound implies the sharp finite uniform test bound. -/
theorem rankTest_uniformProb_le_of_mean (ε : ℝ) (hε : 0 ≤ ε)
    {d n : ℕ} (g : Geometry d n)
    (hmean : (1/2-3*ε/8) * (rowCount d n : ℝ) ≤
      uniformMean (fun x : Fin (rowCount d n) → Bool =>
        ((testMatrix g (boolWord x)).rank : ℝ))) :
    uniformProb (fun y : Word (rowCount d n) => rankTest ε g y = true) ≤
      Real.exp (-(ε^2/32) * (rowCount d n : ℝ)) := by
  let f := fun x : Fin (rowCount d n) → Bool => ((testMatrix g (boolWord x)).rank : ℝ)
  have hm : 0 < rowCount d n := pow_pos (fieldSize_pos d n) d
  have hmR : (0 : ℝ) < rowCount d n := by exact_mod_cast hm
  have ht : 0 ≤ ε * (rowCount d n : ℝ) / 8 := by positivity
  have hb := boundedDifferences_lower_tail hm f (testMatrix_rank_boundedDifferences g)
    (ε * (rowCount d n : ℝ) / 8) ht
  calc
    _ = uniformProb (fun x : Fin (rowCount d n) → Bool =>
        rankTest ε g (boolWord x) = true) := by
      symm
      simpa only [boolWordEquiv_apply] using uniformProb_equiv (boolWordEquiv (rowCount d n))
        (fun y => rankTest ε g y = true)
    _ ≤ uniformProb (fun x => f x ≤ uniformMean f - ε * (rowCount d n : ℝ) / 8) := by
      apply uniformProb_mono
      intro x hx
      have hr : ((testMatrix g (boolWord x)).rank : ℝ) ≤
          (1/2-ε/2) * (rowCount d n : ℝ) := by
        simpa only [rankTest, decide_eq_true_eq] using hx
      dsimp [f]
      nlinarith
    _ ≤ Real.exp (-2*(ε*(rowCount d n : ℝ)/8)^2/(rowCount d n : ℝ)) := hb
    _ = _ := by
      congr 1
      field_simp
      ring

/-- Familywise uniform-rank acceptance with the mission's stronger `1/32` exponent.
Its only rate/erasure dependency is the canonical registered Lemma 2.4. -/
theorem eventual_rankTest_uniform_acceptance_family (ε : ℝ)
    (hε : 0 < ε ∧ ε < 1/2) (g : ∀ n, Geometry (dimension ε) n) :
    ∀ᶠ n : ℕ in atTop,
      uniformProb (fun y : Word (rowCount (dimension ε) n) => rankTest ε (g n) y = true) ≤
        Real.exp (-(ε^2/32) * (rowCount (dimension ε) n : ℝ)) := by
  rcases auxiliary_rate ε hε g with ⟨hρ, _, hr, he⟩
  have hrE : ∀ᶠ n : ℕ in atTop,
      limitingRate (dimension ε)-ε/32 ≤
        (finrank (g n).F (auxiliaryCode (g n)) : ℝ) / rowCount (dimension ε) n := by
    apply (hr.eventually (lt_mem_nhds (show
      limitingRate (dimension ε)-ε/32 < limitingRate (dimension ε) by linarith))).mono
    intro n hn
    exact hn.le
  have heE : ∀ᶠ n : ℕ in atTop,
      erasureExpectation (auxiliaryCode (g n)) (1/2) / rowCount (dimension ε) n ≤ ε/32 := by
    apply (he.eventually (gt_mem_nhds (show (0 : ℝ) < ε/32 by linarith))).mono
    intro n hn
    exact hn.le
  filter_upwards [hrE, heE] with n hnR hnE
  apply rankTest_uniformProb_le_of_mean ε hε.1.le (g n)
  have hm : (0 : ℝ) < rowCount (dimension ε) n := by
    exact_mod_cast pow_pos (fieldSize_pos (dimension ε) n) (dimension ε)
  have hrM := (le_div_iff₀ hm).mp hnR
  have heM := (div_le_iff₀ hm).mp hnE
  have hρM := mul_le_mul_of_nonneg_right hρ hm.le
  have hmean := testMatrix_rank_mean_lower (g n)
  nlinarith

/-- Choosing a bad geometry at each size turns familywise eventual bounds into
one bound uniform over all public geometries. -/
theorem eventual_rankTest_uniform_acceptance (ε : ℝ)
    (hε : 0 < ε ∧ ε < 1/2) :
    ∀ᶠ n : ℕ in atTop, ∀ g : Geometry (dimension ε) n,
      uniformProb (fun y : Word (rowCount (dimension ε) n) => rankTest ε g y = true) ≤
        Real.exp (-(ε^2/32) * (rowCount (dimension ε) n : ℝ)) := by
  classical
  let P := fun n (g : Geometry (dimension ε) n) =>
    uniformProb (fun y : Word (rowCount (dimension ε) n) => rankTest ε g y = true) ≤
      Real.exp (-(ε^2/32) * (rowCount (dimension ε) n : ℝ))
  let g : ∀ n, Geometry (dimension ε) n := fun n =>
    if h : ∃ g, ¬P n g then Classical.choose h else standardGeometry (dimension ε) n
  have hg := eventual_rankTest_uniform_acceptance_family ε hε g
  filter_upwards [hg] with n hn
  intro g₀
  by_contra hbad
  have hex : ∃ g, ¬P n g := ⟨g₀, hbad⟩
  have hgBad : ¬P n (g n) := by
    dsimp only [g]
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  exact hgBad hn

/-- Every corruption whose weight lies below the exact test threshold is accepted. -/
theorem rankTest_accepts_weight_threshold (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2)
    (n : ℕ) (g : Geometry (dimension ε) n)
    (s : Forms g.F (dimension ε) (arity ε))
    (h : Hashes g.F (arity ε) (buckets ε n)) (x : Word n)
    (e : Word (rowCount (dimension ε) n))
    (he : (weight e : ℝ) ≤ (1/2-ε/2) * (rowCount (dimension ε) n : ℝ)) :
    rankTest ε g ((combined g s h).mulVec x + e) = true := by
  have hr := testMatrix_combined_corruption_rank_le_weight g s h x e
    (dimension_ge_four ε hε) (show 0 < buckets ε n from pow_pos (by decide) _)
  apply decide_eq_true
  exact (show ((testMatrix g ((combined g s h).mulVec x+e)).rank : ℝ) ≤ (weight e : ℝ) by
    exact_mod_cast hr).trans he

/-- The exact deterministic arbitrary-error clause of Proposition 2.5. -/
theorem rankTest_accepts_arbitrary_errors (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2)
    (n : ℕ) (g : Geometry (dimension ε) n)
    (s : Forms g.F (dimension ε) (arity ε))
    (h : Hashes g.F (arity ε) (buckets ε n)) (x : Word n)
    (e : Word (rowCount (dimension ε) n))
    (he : (weight e : ℝ) ≤ (1/2-ε) * (rowCount (dimension ε) n : ℝ)) :
    rankTest ε g ((combined g s h).mulVec x + e) = true := by
  apply rankTest_accepts_weight_threshold ε hε n g s h x e
  have hm : (0 : ℝ) ≤ rowCount (dimension ε) n := Nat.cast_nonneg _
  nlinarith

open MeasureTheory

/-- Hoeffding's scalar Bernoulli bound, isolated from the detector. -/
theorem bernoulli_two_point_mgf_le (p s : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (1-p)*Real.exp (-s*p) + p*Real.exp (s*(1-p)) ≤ Real.exp (s^2/8) := by
  let q : unitInterval := ⟨p, hp, hp'⟩
  let μ := ProbabilityTheory.bernoulliMeasure true false q
  let X : Bool → ℝ := fun b => if b then 1-p else -p
  have hm : AEMeasurable X μ := (measurable_of_countable X).aemeasurable
  have hb : ∀ᵐ b ∂μ, X b ∈ Set.Icc (-p) (1-p) := by
    apply Filter.Eventually.of_forall
    intro b
    cases b <;> dsimp [X] <;> constructor <;> linarith
  have hc : ∫ b, X b ∂μ = 0 := by
    rw [ProbabilityTheory.integral_bernoulliMeasure]
    dsimp [X, q]
    ring
  have h := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hc).mgf_le s
  have hw : (1-p)-(-p) = 1 := by ring
  rw [hw] at h
  norm_num at h
  convert h using 1
  · simp [ProbabilityTheory.mgf, μ, ProbabilityTheory.integral_bernoulliMeasure,
      X, q, smul_eq_mul, mul_neg, add_comm]
  · congr 1
    ring


/-- Exact support encoding for every binary word. -/
noncomputable def wordSupportEquiv (m : ℕ) : Word m ≃ Finset (Fin m) where
  toFun e := Finset.univ.filter (fun i => e i ≠ 0)
  invFun S i := if i ∈ S then 1 else 0
  left_inv e := by
    funext i
    simpa [boolBitEquiv] using boolBitEquiv.apply_symm_apply (e i)
  right_inv S := by
    ext i
    by_cases hi : i ∈ S <;> simp [hi]

@[simp] theorem wordSupportEquiv_card (m : ℕ) (e : Word m) :
    (wordSupportEquiv m e).card = weight e := by
  unfold wordSupportEquiv weight
  congr 1
  ext i
  simp

/-- The exact binary Bernoulli weights sum to one. -/
theorem sum_bernoulliWord (m : ℕ) (p : ℝ) :
    ∑ e : Word m, bernoulliWord m p e = 1 := by
  have hs := Fintype.sum_equiv (wordSupportEquiv m)
    (bernoulliWord m p)
    (fun E : Finset (Fin m) => p^E.card*(1-p)^(m-E.card))
    (by intro e; simp only [bernoulliWord, wordSupportEquiv_card])
  rw [hs]
  simpa using Fintype.sum_pow_mul_eq_add_pow (Fin m) p (1-p)

theorem bernoulliWord_nonneg (m : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (e : Word m) : 0 ≤ bernoulliWord m p e :=
  mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp') _)

/-- Exact centered generating function for finite Bernoulli subsets. -/
theorem bernoulli_subsets_mgf (m : ℕ) (p s : ℝ) :
    (∑ E : Finset (Fin m), p^E.card*(1-p)^(m-E.card) *
      Real.exp (s*((E.card : ℝ)-p*m))) =
      (p*Real.exp (s*(1-p)) + (1-p)*Real.exp (-s*p))^m := by
  have ht (E : Finset (Fin m)) :
      p^E.card*(1-p)^(m-E.card)*Real.exp (s*((E.card : ℝ)-p*m)) =
        (p*Real.exp (s*(1-p)))^E.card *
          ((1-p)*Real.exp (-s*p))^(m-E.card) := by
    have hcard : E.card ≤ m := by simpa using Finset.card_le_univ E
    have he : Real.exp (s*((E.card : ℝ)-p*m)) =
        (Real.exp (s*(1-p)))^E.card * (Real.exp (-s*p))^(m-E.card) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      rw [Nat.cast_sub hcard]
      ring
    rw [he, mul_pow, mul_pow]
    ring
  simp_rw [ht]
  simpa using Fintype.sum_pow_mul_eq_add_pow (Fin m)
    (p*Real.exp (s*(1-p))) ((1-p)*Real.exp (-s*p))

/-- Sharp centered MGF bound for exact binary Bernoulli weights. -/
theorem bernoulli_weight_mgf_le (m : ℕ) (p s : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (∑ e : Word m, bernoulliWord m p e *
      Real.exp (s*((weight e : ℝ)-p*m))) ≤ Real.exp ((m : ℝ)*s^2/8) := by
  have hs := Fintype.sum_equiv (wordSupportEquiv m)
    (fun e : Word m => bernoulliWord m p e * Real.exp (s*((weight e : ℝ)-p*m)))
    (fun E : Finset (Fin m) => p^E.card*(1-p)^(m-E.card)*Real.exp (s*((E.card : ℝ)-p*m)))
    (by intro e; simp only [bernoulliWord, wordSupportEquiv_card])
  rw [hs, bernoulli_subsets_mgf]
  calc
    _ ≤ (Real.exp (s^2/8))^m := by
      have hscalar := bernoulli_two_point_mgf_le p s hp hp'
      have hbase : 0 ≤ p*Real.exp (s*(1-p))+(1-p)*Real.exp (-s*p) := by positivity
      exact pow_le_pow_left₀ hbase (by simpa only [add_comm] using hscalar) m
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Finite Bernoulli Hoeffding upper tail, proved from the exact generating function. -/
theorem bernoulli_weight_upper_tail (m : ℕ) (hm : 0 < m) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    (∑ e : Word m, bernoulliWord m p e *
      (if p*m+t ≤ (weight e : ℝ) then (1 : ℝ) else 0)) ≤
        Real.exp (-2*t^2/(m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let s := 4*t/(m : ℝ)
  have hs : 0 ≤ s := by positivity
  let tail := ∑ e : Word m, bernoulliWord m p e *
    (if p*m+t ≤ (weight e : ℝ) then (1 : ℝ) else 0)
  have hmark : Real.exp (s*t)*tail ≤
      ∑ e : Word m, bernoulliWord m p e*Real.exp (s*((weight e : ℝ)-p*m)) := by
    dsimp only [tail]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    have hw := bernoulliWord_nonneg m p hp hp' e
    by_cases he : p*m+t ≤ (weight e : ℝ)
    · simp only [if_pos he, mul_one]
      rw [mul_comm (Real.exp (s*t))]
      apply mul_le_mul_of_nonneg_left _ hw
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hs (show 0 ≤ (weight e : ℝ)-p*m-t by linarith)]
    · simp only [if_neg he, mul_zero]
      exact mul_nonneg hw (Real.exp_nonneg _)
  calc
    _ = Real.exp (-s*t)*(Real.exp (s*t)*tail) := by
      change tail = _
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-s*t)*
        (∑ e : Word m, bernoulliWord m p e*Real.exp (s*((weight e : ℝ)-p*m))) :=
      mul_le_mul_of_nonneg_left hmark (Real.exp_nonneg _)
    _ ≤ Real.exp (-s*t)*Real.exp ((m : ℝ)*s^2/8) :=
      mul_le_mul_of_nonneg_left (bernoulli_weight_mgf_le m p s hp hp') (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp [s]
      field_simp
      ring

/-- The exact biased Bernoulli acceptance clause, with exponent `ε²*m/2`. -/
theorem rankTest_bernoulli_acceptance (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2)
    (n : ℕ) (g : Geometry (dimension ε) n)
    (s : Forms g.F (dimension ε) (arity ε))
    (h : Hashes g.F (arity ε) (buckets ε n)) (x : Word n) :
    (∑ e : Word (rowCount (dimension ε) n),
      bernoulliWord (rowCount (dimension ε) n) (1/2-ε) e *
        (if rankTest ε g ((combined g s h).mulVec x+e) then (1 : ℝ) else 0)) ≥
      1-Real.exp (-(ε^2/2)*(rowCount (dimension ε) n : ℝ)) := by
  let m := rowCount (dimension ε) n
  let p := (1/2 : ℝ)-ε
  let t := ε*(m : ℝ)/2
  let acc := fun e : Word m => rankTest ε g ((combined g s h).mulVec x+e)
  have hm : 0 < m := pow_pos (fieldSize_pos (dimension ε) n) (dimension ε)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : 0 ≤ p := by dsimp [p]; linarith [hε.2]
  have hp' : p ≤ 1 := by dsimp [p]; linarith [hε.1]
  have ht : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (mul_nonneg hε.1.le hmR.le) (by norm_num)
  have htail := bernoulli_weight_upper_tail m hm p hp hp' t ht
  have hthresh : p*(m : ℝ)+t = (1/2-ε/2)*(m : ℝ) := by dsimp [p,t]; ring
  rw [hthresh] at htail
  have hexp : Real.exp (-2*t^2/(m : ℝ)) = Real.exp (-(ε^2/2)*(m : ℝ)) := by
    congr 1
    dsimp [t]
    field_simp
  rw [hexp] at htail
  have hrej : 1-(∑ e : Word m, bernoulliWord m p e * (if acc e then (1 : ℝ) else 0)) ≤
      ∑ e : Word m, bernoulliWord m p e *
        (if (1/2-ε/2)*(m : ℝ) ≤ (weight e : ℝ) then (1 : ℝ) else 0) := by
    conv_lhs =>
      lhs
      rw [← sum_bernoulliWord m p]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro e _
    have hw := bernoulliWord_nonneg m p hp hp' e
    by_cases ha : acc e = true
    · simp only [ha, if_true, mul_one, sub_self]
      exact mul_nonneg hw (by split_ifs <;> norm_num)
    · have he : (1/2-ε/2)*(m : ℝ) ≤ (weight e : ℝ) := by
        by_contra hweight
        have he' : (weight e : ℝ) ≤ (1/2-ε/2)*(m : ℝ) :=
          (lt_of_not_ge hweight).le
        exact ha (rankTest_accepts_weight_threshold ε hε n g s h x e he')
      rw [if_neg ha, if_pos he]
      simp
  change (∑ e : Word m, bernoulliWord m p e * (if acc e then (1 : ℝ) else 0)) ≥ _
  linarith

/-- Proposition 2.5 assembled from exact finite concentration and the canonical
registered auxiliary-rate theorem. -/
theorem rankTest_distinguishing (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) :
    ∀ᶠ n : ℕ in atTop, ∀ g : Geometry (dimension ε) n,
      uniformProb (fun y : Word (rowCount (dimension ε) n) => rankTest ε g y = true) ≤
        Real.exp (-(ε^2/32)*(rowCount (dimension ε) n : ℝ)) ∧
      ∀ (s : Forms g.F (dimension ε) (arity ε))
        (h : Hashes g.F (arity ε) (buckets ε n)) (x : Word n),
        (∀ e : Word (rowCount (dimension ε) n),
          (weight e : ℝ) ≤ (1/2-ε)*(rowCount (dimension ε) n : ℝ) →
            rankTest ε g ((combined g s h).mulVec x+e) = true) ∧
        (∑ e : Word (rowCount (dimension ε) n),
          bernoulliWord (rowCount (dimension ε) n) (1/2-ε) e *
            (if rankTest ε g ((combined g s h).mulVec x+e) then (1 : ℝ) else 0)) ≥
          1-Real.exp (-(ε^2/2)*(rowCount (dimension ε) n : ℝ)) := by
  filter_upwards [eventual_rankTest_uniform_acceptance ε hε] with n hn
  intro g
  refine ⟨hn g, ?_⟩
  intro s h x
  exact ⟨fun e he => rankTest_accepts_arbitrary_errors ε hε n g s h x e he,
    rankTest_bernoulli_acceptance ε hε n g s h x⟩

end ExpandingCodes.PolynomialStretch

end FlattenModule137

/-! Inlined whole module: ExpandingCodes.Construction.UniformAcceptance -/
section FlattenModule138


set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch

theorem eventual_uniform_rank_acceptance (ε θ : ℝ)
    (hε : 0 < ε ∧ ε < 1 / 2) (hθ : ε / 2 < θ ∧ θ < ε)
    (g : ∀ n, Geometry (dimension θ) n) :
    ∀ᶠ n : ℕ in atTop,
      uniformProb (fun y : Word (rowCount (dimension θ) n) =>
        rankTest θ (g n) y = true) ≤
          Real.exp (-(ε ^ 2 / 128) * rowCount (dimension θ) n) := by
  have hθrange : 0 < θ ∧ θ < 1/2 :=
    ⟨(half_pos hε.1).trans hθ.1, hθ.2.trans hε.2⟩
  have hsq : ε^2 ≤ 4*θ^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 2*θ-ε by linarith [hθ.1])
      (show 0 ≤ 2*θ+ε by linarith [hθrange.1, hε.1])]
  filter_upwards [rankTest_distinguishing θ hθrange] with n hn
  apply ((hn (g n)).1).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (by nlinarith) (Nat.cast_nonneg _)

end ExpandingCodes.PolynomialStretch

end FlattenModule138

/-! Inlined whole module: ExpandingCodes.Algebra.CodewordAnnihilation -/
section FlattenModule140



set_option autoImplicit false
open scoped Classical

namespace ExpandingCodes.PolynomialStretch

open Filter
/-- Lemma 2.2, with the standing sufficiently-large-n convention of §2. -/
theorem codeword_annihilation (ε : ℝ) (hε : 0 < ε ∧ ε < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ (g : Geometry (dimension ε) n)
      (s : Forms g.F (dimension ε) (arity ε))
      (h : Hashes g.F (arity ε) (buckets ε n)) (x : Word n),
      testMatrix g ((combined g s h).mulVec x) = 0 ∧
      ∀ e : Word (rowCount (dimension ε) n),
        (testMatrix g ((combined g s h).mulVec x + e)).rank ≤ weight e := by
  apply Filter.Eventually.of_forall
  intro n g s h x
  have hd : 4 ≤ dimension ε := dimension_ge_four ε hε
  have hb : 0 < buckets ε n := by
    unfold buckets
    exact pow_pos (by decide) _
  exact ⟨testMatrix_combined_mulVec_eq_zero g s h x hd hb,
    fun e => testMatrix_combined_corruption_rank_le_weight g s h x e hd hb⟩

end ExpandingCodes.PolynomialStretch

end FlattenModule140

/-! Inlined whole module: ExpandingCodes.Construction.Adversarial -/
section FlattenModule141



set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch

theorem adversarial_rankTest_acceptance (ε θ : ℝ)
    (hθ : 0 < θ ∧ θ < 1 / 2) (hθε : θ ≤ 2 * ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (g : Geometry (dimension θ) n)
      (G : Generator (rowCount (dimension θ) n) n), sampleLaw θ n g G ≠ 0 →
      ∀ (x : Word n) (e : Word (rowCount (dimension θ) n)),
        (weight e : ℝ) ≤ (1 / 2 - ε) * rowCount (dimension θ) n →
          rankTest θ g (G.mulVec x + e) = true := by
  filter_upwards [codeword_annihilation θ hθ] with n hn
  intro g G hG x e he
  obtain ⟨s, h, rfl⟩ := (sampleLaw_ne_zero_iff θ n g G).mp hG
  have hr : ((testMatrix g ((combined g s h).mulVec x + e)).rank : ℝ) ≤ weight e := by
    exact_mod_cast (hn g s h x).2 e
  have hm : (0 : ℝ) ≤ rowCount (dimension θ) n := Nat.cast_nonneg _
  have ht : (1 / 2 - ε) * (rowCount (dimension θ) n : ℝ) ≤
      (1 / 2 - θ / 2) * rowCount (dimension θ) n := by
    exact mul_le_mul_of_nonneg_right (by linarith) hm
  simp only [rankTest, decide_eq_true_eq]
  exact hr.trans (he.trans ht)

end ExpandingCodes.PolynomialStretch

end FlattenModule141

/-! Inlined whole module: ExpandingCodes.Construction.LogGrowth -/
section FlattenModule142


set_option autoImplicit false
open Filter Topology

namespace ExpandingCodes.PolynomialStretch

theorem rowCount_log_limit (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => Real.log (rowCount d n) / Real.log n -
      2 * (d : ℝ) ^ 2) atTop (𝓝 0) := by
  have hz : Tendsto (fun n : ℕ => (d : ℝ) * Real.log 2 / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hlo : (n : ℝ) ^ (2 * d ^ 2) ≤ rowCount d n := by
      exact_mod_cast rowCount_lower d n
    have hl := Real.log_le_log (pow_pos hnpos _) hlo
    rw [Real.log_pow] at hl
    have ha : ((2 * d ^ 2 : ℕ) : ℝ) = 2 * (d : ℝ) ^ 2 := by push_cast; rfl
    rw [ha] at hl
    have := (le_div_iff₀ hlog).2 hl
    linarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hmpos : (0 : ℝ) < rowCount d n := by
      exact_mod_cast (pow_pos (fieldSize_pos d n) d)
    have hup : (rowCount d n : ℝ) ≤ 2 ^ d * (n : ℝ) ^ (2 * d ^ 2) := by
      exact_mod_cast (rowCount_upper d n hd hn).le
    have hu := Real.log_le_log hmpos hup
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hu
    have ha : ((2 * d ^ 2 : ℕ) : ℝ) = 2 * (d : ℝ) ^ 2 := by push_cast; rfl
    rw [ha] at hu
    have hdiv := div_le_div_of_nonneg_right hu hlog.le
    have he : ((d : ℝ) * Real.log 2 + 2 * (d : ℝ) ^ 2 * Real.log n) / Real.log n =
        (d : ℝ) * Real.log 2 / Real.log n + 2 * (d : ℝ) ^ 2 := by
      rw [add_div, mul_div_cancel_right₀ _ hlog.ne']
    rw [he] at hdiv
    linarith

end ExpandingCodes.PolynomialStretch

end FlattenModule142

/-! Inlined whole module: ExpandingCodes.Construction.Construction -/
section FlattenModule143




set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch

theorem construction :
    ∃ Cd Ck : ℝ, 0 < Cd ∧ 0 < Ck ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        ∃ θ : ℚ, ε / 2 < (θ : ℝ) ∧ (θ : ℝ) < ε ∧
          (dimension (θ : ℝ) : ℝ) ≤ Cd * ε⁻¹ ^ 2 ∧
          (arity (θ : ℝ) : ℝ) ≤ Ck * ε⁻¹ ^ 6 ∧
          ∃ g : ∀ n, Geometry (dimension (θ : ℝ)) n,
            EfficientFamily ε (arity (θ : ℝ)) (rowCount (dimension (θ : ℝ)))
              (fun n => sampleLaw (θ : ℝ) n (g n)) (fun n => rankTest (θ : ℝ) (g n)) ∧
            Tendsto (fun n => Real.log (rowCount (dimension (θ : ℝ)) n) / Real.log n -
              2 * (dimension (θ : ℝ) : ℝ) ^ 2) atTop (nhds 0) := by
  refine ⟨8192, 2147483648, by norm_num, by norm_num, ?_⟩
  intro ε hεpos hεhalf
  have hε := And.intro hεpos hεhalf
  obtain ⟨θ, hlo, hhi, hd, hk⟩ := rational_parameter_bounds ε hε
  have hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1 / 2 :=
    ⟨(half_pos hεpos).trans hlo, hhi.trans hεhalf⟩
  obtain ⟨g, hs, ht⟩ := rational_geometry_programs θ hθ
  refine ⟨θ, hlo, hhi, hd, hk, g, ?_, ?_⟩
  · obtain ⟨sampler, A, a, Ns, hA, hNs, hs⟩ := hs
    obtain ⟨tester, B, b, Nt, hB, hNt, ht⟩ := ht
    have hmath : ∀ᶠ n : ℕ in atTop,
        (n < rowCount (dimension (θ : ℝ)) n ∧
          rowCount (dimension (θ : ℝ)) n < n ^ arity (θ : ℝ)) ∧
        (∀ G : Generator (rowCount (dimension (θ : ℝ)) n) n,
          sampleLaw (θ : ℝ) n (g n) G ≠ 0 → RowWeight G (arity (θ : ℝ))) ∧
        (1 - (n : ℝ) ^ (-1 / ε) ≤ eventProb (sampleLaw (θ : ℝ) n (g n))
          (fun G => Expanding G (1 - ε) (arity (θ : ℝ)) ((n : ℝ) ^ (1 - ε)))) ∧
        (∀ G : Generator (rowCount (dimension (θ : ℝ)) n) n,
          sampleLaw (θ : ℝ) n (g n) G ≠ 0 →
          ∀ (x : Word n) (e : Word (rowCount (dimension (θ : ℝ)) n)),
            (weight e : ℝ) ≤ (1 / 2 - ε) * rowCount (dimension (θ : ℝ)) n →
              rankTest (θ : ℝ) (g n) (G.mulVec x + e) = true) ∧
        (uniformProb (fun y : Word (rowCount (dimension (θ : ℝ)) n) =>
          rankTest (θ : ℝ) (g n) y = true) ≤
            Real.exp (-(ε ^ 2 / 128) * rowCount (dimension (θ : ℝ)) n)) := by
      filter_upwards [eventually_rowCount_bounds (θ : ℝ) hθ,
        eventual_sampleLaw_rowWeight (θ : ℝ) hθ,
        eventual_sampler_expansion ε (θ : ℝ) hε ⟨hlo, hhi⟩ g,
        adversarial_rankTest_acceptance ε (θ : ℝ) hθ (by linarith),
        eventual_uniform_rank_acceptance ε (θ : ℝ) hε ⟨hlo, hhi⟩ g] with n hn hw hx ha hu
      exact ⟨hn, hw (g n), hx, ha (g n), hu⟩
    obtain ⟨Nm, hm⟩ := eventually_atTop.1 hmath
    let N := max 2 (max Ns (max Nt Nm))
    refine ⟨sampler, tester, A, a, B, b, N, hA, hB, le_max_left _ _, ?_⟩
    intro n hn
    have hNs' : Ns ≤ n := (le_max_left Ns _).trans ((le_max_right 2 _).trans hn)
    have hNt' : Nt ≤ n := (le_max_left Nt Nm).trans
      ((le_max_right Ns _).trans ((le_max_right 2 _).trans hn))
    have hNm' : Nm ≤ n := (le_max_right Nt Nm).trans
      ((le_max_right Ns _).trans ((le_max_right 2 _).trans hn))
    obtain ⟨hgrowth, hw, hx, ha, hu⟩ := hm n hNm'
    exact ⟨hgrowth.1, hgrowth.2, (hs n hNs').1, (hs n hNs').2,
      ht n hNt', hw, hx, ha, hu⟩
  · exact rowCount_log_limit (dimension (θ : ℝ))
      (lt_of_lt_of_le (by decide : 0 < 4) (dimension_ge_four (θ : ℝ) hθ))

end ExpandingCodes.PolynomialStretch

end FlattenModule143

/-! Inlined whole module: Solutions.Sol_ExpandingCodes_PolynomialStretch_expanding_codes -/
section FlattenModule145



set_option autoImplicit false
open scoped Classical
open ExpandingCodes.PolynomialStretch

/-! The precise construction supplies the actual sampler and tester machines,
expansion and decoding estimates, and the uniform constant. This final packaging
step selects its family and retains the headline polynomial-stretch bound. -/

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ (k : ℕ) (m : ℕ → ℕ) (P : ∀ n, PMF (Generator (m n) n))
        (D : ∀ n, Word (m n) → Bool),
        (k : ℝ) ≤ C * ε⁻¹ ^ 6 ∧ EfficientFamily ε k m P D := by
  obtain ⟨Cd, Ck, _hCd, hCk, hconstruction⟩ := construction
  refine ⟨Ck, hCk, ?_⟩
  intro ε hε hhalf
  obtain ⟨θ, _hθlower, _hθupper, _hd, hk, g, hefficient, _hgrowth⟩ :=
    hconstruction ε hε hhalf
  exact ⟨arity (θ : ℝ), rowCount (dimension (θ : ℝ)),
    (fun n => sampleLaw (θ : ℝ) n (g n)),
    (fun n => rankTest (θ : ℝ) (g n)), hk, hefficient⟩

end FlattenModule145
