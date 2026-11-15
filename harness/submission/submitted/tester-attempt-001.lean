import Definitions.Def_ExpandingCodes_PolynomialStretch_BinaryRuntime
import Mathlib

set_option autoImplicit false


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







theorem indexEquiv_inverse_value (ell : ℕ) (c : Coefficients ell) :
    ((indexEquiv ell).symm c).val = ∑ j : Fin ell, (c j).val * 2 ^ j.val := rfl
















































































































































































theorem selectedIndex_le (ell : ℕ) (h : 0 < ell) (i : Fin (2 ^ ell))
    (hi : FactorFree ell i) : selectedIndex ell h ≤ i := by
  exact Finset.min'_le _ _ (by simpa using hi)













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






























































































































theorem multiply_remainder (ell : ℕ) (h : 0 < ell) (m : Fin (2 ^ ell))
    (x y : Coefficients ell) :
    polynomial (multiply ell h m x y) = (polynomial x * polynomial y) %ₘ candidate ell m := by
  obtain ⟨s, hs⟩ := multiply_certificate ell h m x y
  have he := (divMatches_iff ell h m x y _ s).mp hs
  have hrem : (polynomial (multiply ell h m x y)).degree < (candidate ell m).degree := by
    simpa only [degree_eq_natDegree (candidate_monic ell m).ne_zero, candidate_natDegree] using
      degree_polynomial_lt (multiply ell h m x y)
  exact ((div_modByMonic_unique (polynomial s) (polynomial (multiply ell h m x y))
    (candidate_monic ell m) ⟨he.symm, hrem⟩).2).symm































































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

/-! Inlined whole module: ExpandingCodes.Computation.TapeProgram -/
section FlattenModule5


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB


























namespace TapeProgram
variable {R B L : ℕ}



















































 theorem cost_le_two (P : TapeProgram R B L) (c : TapeCfg R B L) : P.cost c ≤ 2 := by
  unfold cost
  cases P.code c.pc <;> simp

 theorem time_le (P : TapeProgram R B L) (inp : Inputs) (t : ℕ) :
    P.time inp t ≤ 2*t := by
  induction t with
  | zero => simp [time]
  | succ t ih =>
    have hc := P.cost_le_two (P.run inp t)
    simp only [time]
    omega

 theorem run_succ (P : TapeProgram R B L) (inp : Inputs) (t : ℕ) :
    P.run inp (t+1) = P.step inp (P.run inp t) :=
  Function.iterate_succ_apply' _ _ _

 theorem step_halted (P : TapeProgram R B L) (inp : Inputs) (c : TapeCfg R B L)
    (h : P.halted c) : P.step inp c = c := by
  change P.code c.pc = .halt at h
  simp [step, h]


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

 theorem unary_inc (n : ℕ) : Function.update (unary n) (n+1) .one = unary (n+1) := by
  funext k
  by_cases hk : k = n+1
  · subst k; simp
  · simp only [Function.update_of_ne hk]
    have hle : k ≤ n ↔ k ≤ n+1 := by omega
    simp only [unary, hle]

 theorem unary_dec (n : ℕ) : Function.update (unary (n+1)) (n+1) .blank = unary n := by
  funext k
  by_cases hk : k = n+1
  · subst k; simp
  · simp only [Function.update_of_ne hk]
    have hle : k ≤ n+1 ↔ k ≤ n := by omega
    simp only [unary, hle]

 




/-- First increment microstep preserves the cell under the old head and moves right.
The second writes `one` and stays. These are two legal NKtLB tape actions. -/
 theorem unary_inc_two_steps {l : List Sym} {n : ℕ} (hr : TapeRep l (unary n)) :
    TapeRep
      (Machine.writeAt (Machine.writeAt l n (l.getD n .blank)) (n+1) .one)
      (unary (n+1)) ∧
    Machine.moveHead .stay (Machine.moveHead .right n) = n+1 := by
  constructor
  · rw [hr n]
    simpa only [unary_inc] using (hr.write_same n).write (n+1) .one
  · rfl

/-- Nonzero decrement erases the last `one` and moves left in a single step. -/
 theorem unary_dec_one_step {l : List Sym} {n : ℕ} (hr : TapeRep l (unary (n+1))) :
    TapeRep (Machine.writeAt l (n+1) .blank) (unary n) ∧
    Machine.moveHead .left (n+1) = n := by
  constructor
  · simpa only [unary_dec] using hr.write (n+1) .blank
  · simp [Machine.moveHead]







/-- Extensional equality to a finite bit word leaves only irrelevant trailing blanks. -/
 theorem TapeRep.bits_shape {l : List Sym} {bs : List Bool}
    (hr : TapeRep l (fun k => (bitsSym bs).getD k .blank)) :
    ∃ n, l = bitsSym bs ++ List.replicate n .blank := by
  induction bs generalizing l with
  | nil =>
    refine ⟨l.length, ?_⟩
    simp only [bitsSym, List.map_nil, List.nil_append]
    apply List.ext_getElem
    · simp
    · intro k hk hk'
      have h := hr k
      change l.getD k .blank = .blank at h
      rw [List.getD_eq_getElem l .blank hk] at h
      simpa using h
  | cons b bs ih =>
    cases l with
    | nil =>
      have h := hr 0
      cases b <;> simp [bitsSym, Sym.ofBool] at h
    | cons a l =>
      have ha : a = Sym.ofBool b := by simpa [bitsSym] using hr 0
      have ht : TapeRep l (fun k => (bitsSym bs).getD k .blank) := by
        intro k
        simpa [bitsSym] using hr (k+1)
      obtain ⟨n, hn⟩ := ih ht
      exact ⟨n, by simp [bitsSym, ha, hn]⟩

 theorem dropWhile_bits (bs : List Bool) :
    (bitsSym bs).dropWhile (fun a => decide (a = Sym.blank)) = bitsSym bs := by
  cases bs with
  | nil => rfl
  | cons b bs => cases b <;> simp [bitsSym, Sym.ofBool]

 theorem TapeRep.output {l : List Sym} {bs : List Bool}
    (hr : TapeRep l (fun k => (bitsSym bs).getD k .blank)) :
    (l.reverse.dropWhile (fun a => decide (a = Sym.blank))).reverse = bitsSym bs := by
  obtain ⟨n, rfl⟩ := hr.bits_shape
  rw [List.reverse_append, List.reverse_replicate,
    List.dropWhile_append_of_pos (by simp)]
  have hrev : (bitsSym bs).reverse = bitsSym bs.reverse := by simp [bitsSym]
  rw [hrev, dropWhile_bits]
  simp [bitsSym]




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







 theorem workIdx_ne_bufferIdx (r : Fin R) (b : Fin B) : workIdx B r ≠ bufferIdx R b := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [workIdx, bufferIdx] at hv
  omega

 theorem bufferIdx_ne_workIdx (b : Fin B) (r : Fin R) : bufferIdx R b ≠ workIdx B r :=
  Ne.symm (workIdx_ne_bufferIdx r b)

 theorem bufferIdx_ne_outIdx (b : Fin B) : bufferIdx R b ≠ outIdx R B := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [bufferIdx, outIdx] at hv
  omega

 theorem outIdx_ne_bufferIdx (b : Fin B) : outIdx R B ≠ bufferIdx R b :=
  Ne.symm (bufferIdx_ne_outIdx (R := R) b)

@[simp] theorem bufferIdx_eq_iff (b c : Fin B) : bufferIdx R b = bufferIdx R c ↔ b = c := by
  simp [bufferIdx, Fin.ext_iff]




























































 




 










 theorem compile_start_ne_query (P : TapeProgram R B L) :
    (compile P).start ≠ (compile P).query := by
  simp [compile, startControl, queryControl]

 


































 theorem target_eq_halt (P : TapeProgram R B L) (j : Fin L) :
    target P j = haltControl ↔ P.code j = .halt := by
  unfold target
  cases P.code j <;> simp [haltControl, normal]

 theorem Represents.halt {P : TapeProgram R B L} {c : TapeCfg R B L}
    {m : Machine.Cfg (compile P)} (h : Represents P c m) (hc : P.halted c) :
    m.state = (compile P).halt := by
  rw [h.state, (target_eq_halt P c.pc).mpr hc]









 theorem initial_represents (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs) :
    Represents P P.init ((compile P).run O inp 1) := by
  have hs : (compile P).start ≠ (compile P).halt := by
    simp [compile, startControl, haltControl]
  have hq := compile_start_ne_query P
  have he : ((compile P).run O inp 1) =
      { state := controlEquiv L (target P P.entry)
        roHead := fun _ => 0
        rwTape := fun k => if k.val < R then [.bot] else [.blank]
        rwHead := fun _ => 0 } := by
    simp [Machine.run, Machine.init, Machine.step, hs, hq, compile, transition,
      startControl, haltControl, queryControl, roIdle, Machine.moveHead, Machine.writeAt]
    constructor <;> funext k <;> split_ifs <;> rfl
  rw [he]
  constructor
  · rfl
  · rfl
  · intro r; rfl
  · intro r k
    have hlt : r.val < R := r.isLt
    simp [workIdx, TapeProgram.init, unary, hlt]
    by_cases hk : k = 0 <;> simp [hk]
  · rfl
  · intro k
    simp [outIdx, TapeProgram.init, bitsSym, List.getD_eq_getElem?_getD]

  · intro b; rfl
  · intro b k
    have hnot : ¬ R + b.val < R := by omega
    simp [bufferIdx, TapeProgram.init, hnot, List.getD_eq_getElem?_getD]

/-- Ordinary target transitions expose only canonical head moves and `writeAt`. -/
 theorem step_normal (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (j : Fin L) (m : Machine.Cfg (compile P))
    (hm : m.state = controlEquiv L (normal j)) :
    (compile P).step O inp m =
      let a := transition P (normal j)
        (fun i => Machine.readRO (inp.get i) (m.roHead i))
        (fun k => (m.rwTape k).getD (m.rwHead k) .blank)
      { state := controlEquiv L a.1
        roHead := fun i => Machine.moveHead (a.2.1 i) (m.roHead i)
        rwTape := fun k => Machine.writeAt (m.rwTape k) (m.rwHead k) (a.2.2 k).1
        rwHead := fun k => Machine.moveHead (a.2.2 k).2 (m.rwHead k) } := by
  have hh : m.state ≠ (compile P).halt := by
    rw [hm]; simp [compile, normal, haltControl]
  have hq : m.state ≠ (compile P).query := by
    rw [hm]; simp [compile, normal, queryControl]
  simp only [Machine.step, if_neg hh, if_neg hq]
  simp only [compile, hm, Equiv.symm_apply_apply]

 theorem local_halt (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P))
    (hc : P.halted c) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  rw [P.step_halted inp c hc]
  change P.code c.pc = .halt at hc
  simpa [TapeProgram.cost, hc] using hr

 theorem local_jump (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P)) (j : Fin L)
    (hc : P.code c.pc = .jump j) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  simp only [TapeProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, TapeProgram.step]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro r
    simpa [idle, Machine.moveHead] using hr.workHead r
  · intro r k
    simp only [idle, getD_writeAt]
    rw [hr.workTape r k, hr.workTape r (m.rwHead (workIdx B r))]
    split_ifs with hk
    · exact congrArg (unary (c.reg r)) hk.symm
    · rfl
  · simpa [idle, Machine.moveHead] using hr.outHead
  · intro k
    simp only [idle, getD_writeAt]
    rw [hr.outTape k, hr.outTape (m.rwHead (outIdx R B))]
    split_ifs with hk
    · exact congrArg (fun z => (bitsSym c.output).getD z .blank) hk.symm
    · rfl
  · intro b
    simpa [idle, Machine.moveHead] using hr.bufferHead b
  · intro b
    simpa [idle, Machine.moveHead] using tape_write_scanned (hr.bufferTape b) (m.rwHead (bufferIdx R b))


 theorem local_read (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P)) (r : Fin 4)
    (next : Sym → Fin L) (hc : P.code c.pc = .read r next) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  simp only [TapeProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, TapeProgram.step]
  constructor
  · simp [hr.roHead]
  · funext i
    by_cases hi : i = r <;> simp [hi, roIdle, Machine.moveHead, hr.roHead]
  · intro i
    simpa [idle, Machine.moveHead] using hr.workHead i
  · intro i k
    simp only [idle, getD_writeAt]
    rw [hr.workTape i k, hr.workTape i (m.rwHead (workIdx B i))]
    split_ifs with hk
    · exact congrArg (unary (c.reg i)) hk.symm
    · rfl
  · simpa [idle, Machine.moveHead] using hr.outHead
  · intro k
    simp only [idle, getD_writeAt]
    rw [hr.outTape k, hr.outTape (m.rwHead (outIdx R B))]
    split_ifs with hk
    · exact congrArg (fun z => (bitsSym c.output).getD z .blank) hk.symm
    · rfl
  · intro b
    simpa [idle, Machine.moveHead] using hr.bufferHead b
  · intro b
    simpa [idle, Machine.moveHead] using tape_write_scanned (hr.bufferTape b) (m.rwHead (bufferIdx R b))


 theorem workIdx_ne_outIdx (r : Fin R) : workIdx B r ≠ outIdx R B := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [workIdx, outIdx] at hv
  omega

 theorem outIdx_ne_workIdx (r : Fin R) : outIdx R B ≠ workIdx B r :=
  Ne.symm (workIdx_ne_outIdx (B := B) r)

 theorem local_emit (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P)) (b : Bool) (j : Fin L)
    (hc : P.code c.pc = .emit b j) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  simp only [TapeProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, TapeProgram.step]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro r
    simpa [Function.update_of_ne (workIdx_ne_outIdx (B := B) r), idle, Machine.moveHead]
      using hr.workHead r
  · intro r k
    simp only [Function.update_of_ne (workIdx_ne_outIdx (B := B) r), idle, getD_writeAt]
    rw [hr.workTape r k, hr.workTape r (m.rwHead (workIdx B r))]
    split_ifs with hk
    · exact congrArg (unary (c.reg r)) hk.symm
    · rfl
  · simp [Function.update_self, Machine.moveHead, hr.outHead]
  · intro k
    simp only [Function.update_self, getD_writeAt, hr.outHead]
    rw [hr.outTape k]
    simp only [bitsSym, List.map_append, List.map_cons, List.map_nil]
    rw [getD_append_singleton]
    simp [List.length_map]
  · intro b
    simpa [Function.update_of_ne (bufferIdx_ne_outIdx (R := R) b), idle, Machine.moveHead] using hr.bufferHead b
  · intro b
    simpa [Function.update_of_ne (bufferIdx_ne_outIdx (R := R) b), idle, Machine.moveHead] using tape_write_scanned (hr.bufferTape b) (m.rwHead (bufferIdx R b))


@[simp] theorem workIdx_eq_iff (r s : Fin R) : workIdx B r = workIdx B s ↔ r = s := by
  simp [workIdx, Fin.ext_iff]

 theorem local_dec_zero (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P)) (r : Fin R) (z p : Fin L)
    (hc : P.code c.pc = .dec r z p) (hr : Represents P c m) (hz : c.reg r = 0) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  have hscan : (m.rwTape (workIdx B r)).getD (m.rwHead (workIdx B r)) .blank = .bot := by
    rw [hr.workHead r, hr.workTape r, hz]
    rfl
  simp only [TapeProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, TapeProgram.step, hscan, hz, ite_true, eq_self_iff_true]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro i
    simpa [idle, Machine.moveHead] using hr.workHead i
  · intro i k
    simp only [idle, getD_writeAt]
    rw [hr.workTape i k, hr.workTape i (m.rwHead (workIdx B i))]
    split_ifs with hk
    · exact congrArg (unary (c.reg i)) hk.symm
    · rfl
  · simpa [idle, Machine.moveHead] using hr.outHead
  · intro k
    simp only [idle, getD_writeAt]
    rw [hr.outTape k, hr.outTape (m.rwHead (outIdx R B))]
    split_ifs with hk
    · exact congrArg (fun z => (bitsSym c.output).getD z .blank) hk.symm
    · rfl
  · intro b
    simpa [idle, Machine.moveHead] using hr.bufferHead b
  · intro b
    simpa [idle, Machine.moveHead] using tape_write_scanned (hr.bufferTape b) (m.rwHead (bufferIdx R b))


 theorem local_dec_positive (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P)) (r : Fin R) (z p : Fin L) (n : ℕ)
    (hc : P.code c.pc = .dec r z p) (hr : Represents P c m) (hn : c.reg r = n+1) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  have hscan : (m.rwTape (workIdx B r)).getD (m.rwHead (workIdx B r)) .blank = .one := by
    rw [hr.workHead r, hr.workTape r, hn]
    simp
  simp only [TapeProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, TapeProgram.step, hscan, hn,
    reduceCtorEq, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro i
    by_cases hi : i = r
    · subst i
      simp [Function.update_self, Machine.moveHead, hr.workHead, hn]
    · have hi' : workIdx B i ≠ workIdx B r := by simpa using hi
      simpa [Function.update_of_ne hi', Function.update_of_ne hi, idle, Machine.moveHead]
        using hr.workHead i
  · intro i
    by_cases hi : i = r
    · subst i
      have ht : TapeRep (m.rwTape (workIdx B r)) (unary (n+1)) := by
        simpa [hn] using hr.workTape r
      simpa [Function.update_self, hr.workHead, hn] using (unary_dec_one_step ht).1
    · have hi' : workIdx B i ≠ workIdx B r := by simpa using hi
      intro k
      simp only [Function.update_of_ne hi', Function.update_of_ne hi, idle, getD_writeAt]
      rw [hr.workTape i k, hr.workTape i (m.rwHead (workIdx B i))]
      split_ifs with hk
      · exact congrArg (unary (c.reg i)) hk.symm
      · rfl
  · simpa [Function.update_of_ne (outIdx_ne_workIdx (B := B) r), idle, Machine.moveHead] using hr.outHead
  · intro k
    simp only [Function.update_of_ne (outIdx_ne_workIdx (B := B) r), idle, getD_writeAt]
    rw [hr.outTape k, hr.outTape (m.rwHead (outIdx R B))]
    split_ifs with hk
    · exact congrArg (fun z => (bitsSym c.output).getD z .blank) hk.symm
    · rfl
  · intro b
    simpa [Function.update_of_ne (bufferIdx_ne_workIdx b r), idle, Machine.moveHead] using hr.bufferHead b
  · intro b
    simpa [Function.update_of_ne (bufferIdx_ne_workIdx b r), idle, Machine.moveHead] using tape_write_scanned (hr.bufferTape b) (m.rwHead (bufferIdx R b))


 theorem step_finish (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (j : Fin L) (m : Machine.Cfg (compile P))
    (hm : m.state = controlEquiv L (finish j)) :
    (compile P).step O inp m =
      let a := transition P (finish j)
        (fun i => Machine.readRO (inp.get i) (m.roHead i))
        (fun k => (m.rwTape k).getD (m.rwHead k) .blank)
      { state := controlEquiv L a.1
        roHead := fun i => Machine.moveHead (a.2.1 i) (m.roHead i)
        rwTape := fun k => Machine.writeAt (m.rwTape k) (m.rwHead k) (a.2.2 k).1
        rwHead := fun k => Machine.moveHead (a.2.2 k).2 (m.rwHead k) } := by
  have hh : m.state ≠ (compile P).halt := by
    rw [hm]; simp [compile, finish, haltControl]
  have hq : m.state ≠ (compile P).query := by
    rw [hm]; simp [compile, finish, queryControl]
  simp only [Machine.step, if_neg hh, if_neg hq]
  simp only [compile, hm, Equiv.symm_apply_apply]

 theorem local_inc (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P)) (r : Fin R) (j : Fin L)
    (hc : P.code c.pc = .inc r j) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  have hfinish : ((compile P).step O inp m).state = controlEquiv L (finish c.pc) := by
    rw [step_normal P O inp c.pc m hm]
    simp only [normal, transition, hc]
  simp only [TapeProgram.cost, hc]
  change Represents P (P.step inp c) ((compile P).step O inp ((compile P).step O inp m))
  rw [step_finish P O inp c.pc _ hfinish, step_normal P O inp c.pc m hm]
  simp only [normal, finish, transition, hc, TapeProgram.step]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro i
    by_cases hi : i = r
    · subst i
      simp [Function.update_self, Machine.moveHead, hr.workHead]
    · have hi' : workIdx B i ≠ workIdx B r := by simpa using hi
      simpa [Function.update_of_ne hi', Function.update_of_ne hi, idle, Machine.moveHead]
        using hr.workHead i
  · intro i
    by_cases hi : i = r
    · subst i
      simpa [Function.update_self, idle, Machine.moveHead, hr.workHead]
        using (unary_inc_two_steps (hr.workTape r)).1
    · have hi' : workIdx B i ≠ workIdx B r := by simpa using hi
      simpa [Function.update_of_ne hi', Function.update_of_ne hi, idle, Machine.moveHead]
        using tape_write_scanned (tape_write_scanned (hr.workTape i) (m.rwHead (workIdx B i)))
          (m.rwHead (workIdx B i))
  · simpa [Function.update_of_ne (outIdx_ne_workIdx (B := B) r), idle, Machine.moveHead] using hr.outHead
  · simpa [Function.update_of_ne (outIdx_ne_workIdx (B := B) r), idle, Machine.moveHead]
      using tape_write_scanned (tape_write_scanned hr.outTape (m.rwHead (outIdx R B)))
        (m.rwHead (outIdx R B))
  · intro b
    simpa [Function.update_of_ne (bufferIdx_ne_workIdx b r), idle, Machine.moveHead] using hr.bufferHead b
  · intro b
    simpa [Function.update_of_ne (bufferIdx_ne_workIdx b r), idle, Machine.moveHead] using tape_write_scanned (tape_write_scanned (hr.bufferTape b) (m.rwHead (bufferIdx R b))) (m.rwHead (bufferIdx R b))


/-- One buffer instruction is exactly one legal cell operation, even when the
source and target use different trailing-blank storage for that buffer. -/
 theorem local_buffer (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (c : TapeCfg R B L) (m : Machine.Cfg (compile P)) (b : Fin B)
    (action : Sym → Sym × Move × Fin L)
    (hc : P.code c.pc = .buffer b action) (hr : Represents P c m) :
    Represents P (P.step inp c) (((compile P).step O inp)^[P.cost c] m) := by
  have hm : m.state = controlEquiv L (normal c.pc) := by
    simpa [target, hc] using hr.state
  have hscan : (m.rwTape (bufferIdx R b)).getD (m.rwHead (bufferIdx R b)) .blank =
      (c.bufferTape b).getD (c.bufferHead b) .blank := by
    rw [hr.bufferHead b, hr.bufferTape b]
  simp only [TapeProgram.cost, hc, Function.iterate_one]
  rw [step_normal P O inp c.pc m hm]
  simp only [normal, transition, hc, TapeProgram.step]
  rw [hscan]
  constructor
  · rfl
  · simpa [roIdle, Machine.moveHead] using hr.roHead
  · intro r
    simpa [Function.update_of_ne (workIdx_ne_bufferIdx r b), idle, Machine.moveHead]
      using hr.workHead r
  · intro r
    simpa [Function.update_of_ne (workIdx_ne_bufferIdx r b), idle]
      using tape_write_scanned (hr.workTape r) (m.rwHead (workIdx B r))
  · simpa [Function.update_of_ne (outIdx_ne_bufferIdx (R := R) b), idle, Machine.moveHead]
      using hr.outHead
  · simpa [Function.update_of_ne (outIdx_ne_bufferIdx (R := R) b), idle]
      using tape_write_scanned hr.outTape (m.rwHead (outIdx R B))
  · intro i
    by_cases hi : i = b
    · subst i
      simp only [Function.update_self]
      rw [hr.bufferHead b]
    · have hi' : bufferIdx R i ≠ bufferIdx R b := by simpa using hi
      simpa [Function.update_of_ne hi', Function.update_of_ne hi, idle, Machine.moveHead]
        using hr.bufferHead i
  · intro i
    by_cases hi : i = b
    · subst i
      intro k
      simp only [Function.update_self, getD_writeAt]
      rw [hr.bufferHead b, hr.bufferTape b k]
    · have hi' : bufferIdx R i ≠ bufferIdx R b := by simpa using hi
      simpa [Function.update_of_ne hi', Function.update_of_ne hi, idle]
        using tape_write_scanned (hr.bufferTape i) (m.rwHead (bufferIdx R i))

 theorem localSimulation (P : TapeProgram R B L) : LocalSimulation P := by
  intro O inp c m hr
  cases hc : P.code c.pc with
  | halt => exact local_halt P O inp c m hc hr
  | jump j => exact local_jump P O inp c m j hc hr
  | inc r j => exact local_inc P O inp c m r j hc hr
  | dec r z p =>
    cases hn : c.reg r with
    | zero => exact local_dec_zero P O inp c m r z p hc hr hn
    | succ n => exact local_dec_positive P O inp c m r z p n hc hr hn
  | emit b j => exact local_emit P O inp c m b j hc hr
  | read r next => exact local_read P O inp c m r next hc hr
  | buffer b action => exact local_buffer P O inp c m b action hc hr

/-- Once the finite local instruction obligations are supplied, every source
execution is simulated at its exact accumulated microstep time. -/
 theorem run_represents (P : TapeProgram R B L) (hs : LocalSimulation P)
    (O : Set (List Bool)) (inp : Inputs) (t : ℕ) :
    Represents P (P.run inp t) ((compile P).run O inp (1 + P.time inp t)) := by
  induction t with
  | zero => simpa [TapeProgram.run, TapeProgram.time] using initial_represents P O inp
  | succ t ih =>
    have h := hs O inp (P.run inp t) _ ih
    rw [TapeProgram.run_succ]
    simpa only [TapeProgram.time, ← Nat.add_assoc, Machine.run_add] using h

/-- Halting/output correctness and the actual target time bound follow from the
finite local simulation obligation, rather than from a polynomial-time oracle. -/
 theorem haltsWith_of_localSimulation (P : TapeProgram R B L) (hs : LocalSimulation P)
    (O : Set (List Bool)) (inp : Inputs) (t : ℕ) (hh : P.halted (P.run inp t)) :
    (compile P).HaltsWith O inp (1+2*t) (bitsSym (P.run inp t).output) := by
  have hr := run_represents P hs O inp t
  apply Machine.HaltsWith.mono (t := 1 + P.time inp t) ?_ (by
    have := P.time_le inp t
    omega)
  constructor
  · exact hr.halt hh
  · exact hr.outTape.output

/-- Every finite tape program is implemented with constant overhead by a
fixed, explicitly constructed canonical NKtLB machine. -/
 theorem compile_halts (P : TapeProgram R B L) (O : Set (List Bool)) (inp : Inputs)
    (t : ℕ) (hh : P.halted (P.run inp t)) :
    (compile P).HaltsWith O inp (1+2*t) (bitsSym (P.run inp t).output) :=
  haltsWith_of_localSimulation P (localSimulation P) O inp t hh

 theorem compile_computes (P : TapeProgram R B L) (u : List Bool) (t : ℕ)
    (hh : P.halted (P.run ⟨u, [], [], []⟩ t)) :
    (compile P).Computes (1+2*t) u (P.run ⟨u, [], [], []⟩ t).output :=
  compile_halts P ∅ ⟨u, [], [], []⟩ t hh





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

theorem max (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun n => max (f n) (g n)) :=
  (hf.add hg).of_le (fun n _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))








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

theorem rawConvolution_eq_modulusConvolution (ell : ℕ) (m : Fin (2^ell))
    (s : Fin (2^(2*ell))) (k : ℕ) :
    rawConvolution (2^ell+m.val) s.val k =
      BinaryField.modulusConvolution ell m (indexEquiv (2*ell) s) k := by
  simp only [rawConvolution, BinaryField.modulusConvolution, candidateCoefficient_bit, bufferCoefficient_bit]

theorem coefficientMatches_iff (ell : ℕ) (m a b rem : Fin (2^ell))
    (s : Fin (2^(2*ell))) (k : ℕ) :
    CoefficientMatches a.val b.val rem.val (2^ell+m.val) s.val k ↔
      BinaryField.convolution (indexEquiv ell a) (indexEquiv ell b) k =
        BinaryField.bufferCoefficient (indexEquiv ell rem) k +
          BinaryField.modulusConvolution ell m (indexEquiv (2*ell) s) k := by
  simp only [CoefficientMatches, rawConvolution_eq_convolution, rawConvolution_eq_modulusConvolution,
    bufferCoefficient_bit]




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

theorem coefficientMatches_all_iff (ell : ℕ) (m a b rem : Fin (2^ell))
    (s : Fin (2^(2*ell))) :
    (∀ j < 3*ell+1, CoefficientMatches a.val b.val rem.val (2^ell+m.val) s.val j) ↔
      BinaryField.DivMatches ell m (indexEquiv ell a) (indexEquiv ell b)
        (indexEquiv ell rem) (indexEquiv (2*ell) s) := by
  constructor
  · intro h j
    exact (coefficientMatches_iff ell m a b rem s j.val).mp (h j.val j.isLt)
  · intro h j hj
    exact (coefficientMatches_iff ell m a b rem s j).mpr (h ⟨j,hj⟩)








































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

/-- Every accepted bounded remainder is the exact existing field multiplication
index. Polynomial division appears only in this semantic uniqueness proof. -/
theorem accepted_remainder_unique (ell : ℕ) (h : 0 < ell) (m a b rem : Fin (2^ell))
    (s : Fin (2^(2*ell)))
    (hmatch : BinaryField.DivMatches ell m (indexEquiv ell a) (indexEquiv ell b)
      (indexEquiv ell rem) (indexEquiv (2*ell) s)) :
    rem = BinaryField.multiplyIndex ell h m (indexEquiv ell a) (indexEquiv ell b) := by
  have he := (BinaryField.divMatches_iff ell h m _ _ _ _).mp hmatch
  have hdeg : (polynomial (indexEquiv ell rem)).degree < (candidate ell m).degree := by
    simpa only [Polynomial.degree_eq_natDegree (candidate_monic ell m).ne_zero,
      candidate_natDegree] using degree_polynomial_lt (indexEquiv ell rem)
  have hrem := ((Polynomial.div_modByMonic_unique (polynomial (indexEquiv (2*ell) s))
    (polynomial (indexEquiv ell rem)) (candidate_monic ell m) ⟨he.symm,hdeg⟩).2).symm
  have hmul := BinaryField.multiply_remainder ell h m (indexEquiv ell a) (indexEquiv ell b)
  apply (indexEquiv ell).injective
  funext i
  have hp := hrem.trans hmul.symm
  have hc := congrArg (fun p : Polynomial (ZMod 2) => p.coeff i.val) hp
  simpa only [BinaryField.multiply, coefficient_polynomial] using hc










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









theorem certificateLayout_injective (r : Fin 27 → Fin R) (hr : Function.Injective r) :
    Function.Injective (certificateLayout r) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin 27 => z.val) (hr h)

theorem commitLayout_injective (r : Fin 27 → Fin R) (hr : Function.Injective r) :
    Function.Injective (commitLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [commitLayout]

theorem reg_set27 (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i j : Fin 27) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j; simp
  · simp [TapeStore.setReg, h, hr.ne h]

theorem certificate_preserves (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) (hi : i < 5 ∨ i = 19 ∨ 20 ≤ i) :
    (certificateResult (certificateLayout r) d).reg (r i) = d.reg (r i) := by
  rcases hi with hi | rfl | hi
  · let j : Fin 18 := ⟨i.val, by change i.val < 5 at hi; omega⟩
    have h := certificateResult_input (certificateLayout r) (certificateLayout_injective r hr)
      d j (by change i.val < 5; exact hi)
    simpa [certificateLayout, j] using h
  · exact certificateResult_runtimeBound (certificateLayout r) (certificateLayout_injective r hr) d
  · apply certificateResult_outside
    intro j
    apply hr.ne
    intro h
    have hv := congrArg (fun z : Fin 27 => z.val) h
    change i.val = j.val at hv
    change 20 ≤ i.val at hi
    have := j.isLt
    omega











theorem innerBodyStore_fresh (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) (hi : i < 4 ∨ i = 19 ∨ 23 ≤ i) :
    (innerBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold innerBodyStore
  simp only [reg_set27 r hr, show i ≠ (4:Fin 27) from by rcases hi with h|h|h <;> omega, ite_false]
  rw [commitStore_fresh _ _ _
    (hr.ne (show i ≠ (20:Fin 27) from by rcases hi with h|h|h <;> omega))
    (hr.ne (show i ≠ (21:Fin 27) from by rcases hi with h|h|h <;> omega))
    (hr.ne (show i ≠ (22:Fin 27) from by rcases hi with h|h|h <;> omega))
    (hr.ne (show i ≠ (6:Fin 27) from by rcases hi with h|h|h <;> omega))]
  apply certificate_preserves r hr d i
  rcases hi with h|h|h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by omega))

theorem innerBodyStore_quotient (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (innerBodyStore r d).reg (r 4) = d.reg (r 4)+1 := by
  unfold innerBodyStore
  simp only [TapeStore.setReg, Function.update_self]
  rw [commitStore_fresh _ _ _
    (hr.ne (show (4:Fin 27) ≠ 20 from by decide)) (hr.ne (show (4:Fin 27) ≠ 21 from by decide))
    (hr.ne (show (4:Fin 27) ≠ 22 from by decide)) (hr.ne (show (4:Fin 27) ≠ 6 from by decide)),
    certificate_preserves r hr d 4 (Or.inl (by decide))]

theorem innerBodyStore_tapeData (r : Fin 27 → Fin R) (d : TapeStore R B) :
    tapeData (innerBodyStore r d) = tapeData d := by
  rw [innerBodyStore, tapeData_setReg, commitStore_tapeData, certificateResult_tapeData]

theorem innerBodyStore_bound (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hq : d.reg (r 4)+1 ≤ M) : ∀ j, (innerBodyStore r d).reg j ≤ M := by
  apply setReg_bound _ _ _ M
    (commitStore_bound _ (commitLayout_injective r hr) M hM _
      (certificateResult_bound _ (certificateLayout_injective r hr) M hM d hd))
  have he := innerBodyStore_quotient r hr d
  have he' : (commitStore (commitLayout r) (certificateResult (certificateLayout r) d)).reg (r 4)+1 =
      d.reg (r 4)+1 := by simpa only [innerBodyStore, TapeStore.setReg, Function.update_self] using he
  rw [he']; exact hq

theorem innerBody_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 2400*(M+1)^4 ∧
      (innerBody r).Stops inp (d.toCfg (innerBody (B := B) r).entry) t e ∧
      e.store = innerBodyStore r d := by
  obtain ⟨t₁, c₁, ht₁, h₁, hs₁⟩ := certificate_stops_exact (certificateLayout r)
    (certificateLayout_injective r hr) inp M hM d hd
  have hb₁ : ∀ j, c₁.store.reg j ≤ M := by
    rw [hs₁]; exact certificateResult_bound _ (certificateLayout_injective r hr) M hM d hd
  obtain ⟨t₂, c₂, ht₂, h₂, hs₂⟩ := commit_stops (commitLayout r)
    (commitLayout_injective r hr) inp M c₁.store hb₁
  have h₃ := TapeMacros.increment_stops (r 4) inp c₂.store
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_, _, ?_, hall, ?_⟩
  · have hpow := Nat.le_self_pow (by decide : (4:ℕ) ≠ 0) (M+1)
    omega
  · change c₂.store.setReg (r 4) _ = _
    rw [hs₂, hs₁]
    rfl






theorem innerLoop_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hn : d.reg (r 26) = n) (hd : ∀ j, d.reg j ≤ M) (hq : d.reg (r 4)+n ≤ M) :
    ∃ t, t ≤ n*(2400*(M+1)^4+2)+1 ∧
      (innerLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 338)) t
        ((innerResult r n d).toCfg (TapeProgram.loopExit 338)) ∧
      (∀ j, (innerResult r n d).reg j ≤ M) := by
  let Inv : ℕ → TapeStore R B → Prop := fun n c => (∀ j, c.reg j ≤ M) ∧ c.reg (r 4)+n ≤ M
  have hc (c : TapeStore R B) : (innerBodyStore r c).reg (r 26) = c.reg (r 26) :=
    innerBodyStore_fresh r hr c 26 (Or.inr (Or.inr (by decide)))
  have hb : ∀ n c, c.reg (r 26) = n+1 → Inv (n+1) c →
      ∃ t e, t ≤ 2400*(M+1)^4 ∧
        (innerBody r).Stops inp ((c.setReg (r 26) n).toCfg (innerBody (B := B) r).entry) t e ∧
        e.store = innerBodyStore r (c.setReg (r 26) n) ∧ Inv n e.store := by
    intro n c hcn hi
    have hcb := setReg_bound c (r 26) n M hi.1 (by have := hi.1 (r 26); omega)
    have hcq : (c.setReg (r 26) n).reg (r 4)+1 ≤ M := by
      simp [reg_set27 r hr]
      exact (by have := hi.2; omega)
    obtain ⟨t, e, ht, he, hs⟩ := innerBody_stops r hr inp M hM _ hcb
    refine ⟨t, e, ht, he, hs, ?_⟩
    rw [hs]
    refine ⟨innerBodyStore_bound r hr M hM _ hcb hcq, ?_⟩
    rw [innerBodyStore_quotient r hr]
    simp only [reg_set27 r hr, show (4:Fin 27) ≠ 26 from by decide, ite_false]
    have := hi.2
    omega
  obtain ⟨t, ht, he, hi⟩ := loop_stops (innerBody r) (r 26) (innerBodyStore r) inp
    (2400*(M+1)^4) Inv hc hb n d hn ⟨hd,hq⟩
  exact ⟨t, ht, he, hi.1⟩

theorem innerResult_frame (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) (i : Fin 27) (hi : i < 4 ∨ i = 19 ∨ 23 ≤ i)
    (hne : i ≠ 26) : (innerResult r n d).reg (r i) = d.reg (r i) :=
  loopResult_frame (r 26) (innerBodyStore r) (r i) (hr.ne hne)
    (fun c => innerBodyStore_fresh r hr c i hi) n d






theorem innerResult_tapeData (r : Fin 27 → Fin R) (n : ℕ) (d : TapeStore R B) :
    tapeData (innerResult r n d) = tapeData d :=
  loopResult_tapeData (r 26) (innerBodyStore r) (innerBodyStore_tapeData r) n d

theorem innerResult_bound (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hq : d.reg (r 4)+n ≤ M) : ∀ j, (innerResult r n d).reg j ≤ M := by
  induction n generalizing d with
  | zero => exact hd
  | succ n ih =>
    change ∀ j, (innerResult r n (innerBodyStore r (d.setReg (r 26) n))).reg j ≤ M
    have hb := setReg_bound d (r 26) n M hd (by omega)
    apply ih _ (innerBodyStore_bound r hr M hM _ hb (by simp [reg_set27 r hr]; omega))
    rw [innerBodyStore_quotient r hr]
    simp only [reg_set27 r hr, show (4:Fin 27) ≠ 26 from by decide, ite_false]
    omega







theorem innerPrepare_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (innerPrepare r).Stops inp (d.toCfg (innerPrepare (B := B) r).entry)
      (d.reg (r 4)+d.reg (r 26)+d.reg (r 21)+5*d.reg (r 24)+9) e ∧
      e.store = innerPrepareStore r d := by
  have hclear := TapeMacros.clear_stops (r 4) inp (d.reg (r 4)) d rfl
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops (r 24) (r 26) (r 21)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp (d.setReg (r 4) 0)
  have hall := hclear.seq hc
  refine ⟨c.mapPC (TapeProgram.rightLabel 2), ?_, hcs⟩
  convert hall using 1 <;> first | rfl | (simp [reg_set27 r hr]; omega)

theorem innerPrepareStore_reg (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) :
    (innerPrepareStore r d).reg (r i) =
      if i = 21 then 0 else if i = 26 then d.reg (r 24) else if i = 4 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [innerPrepareStore, reg_set27 r hr]

theorem innerPrepareStore_bound (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (innerPrepareStore r d).reg j ≤ M := by
  unfold innerPrepareStore
  apply setReg_bound _ _ 0 M _ (by omega)
  apply setReg_bound _ _ _ M
  · exact setReg_bound d _ 0 M hd (by omega)
  · simpa [reg_set27 r hr] using hd (r 24)







theorem outerBodyStore_remainder (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (outerBodyStore r d).reg (r 2) = d.reg (r 2)+1 := by
  unfold outerBodyStore
  simp only [TapeStore.setReg, Function.update_self]
  rw [innerResult_frame r hr _ _ 2 (Or.inl (by decide)) (by decide), innerPrepareStore_reg r hr]
  simp

theorem outerBodyStore_fresh (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) (hi : i < 2 ∨ i = 3 ∨ i = 19 ∨ 23 ≤ i)
    (hne : i ≠ 26) : (outerBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold outerBodyStore
  simp only [reg_set27 r hr, show i ≠ (2:Fin 27) from by rcases hi with h|h|h|h <;> omega, ite_false]
  rw [innerResult_frame r hr _ _ i (by
    rcases hi with h|h|h|h
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)) hne, innerPrepareStore_reg r hr]
  have h21 : i ≠ (21:Fin 27) := by rcases hi with h|h|h|h <;> omega
  have h4 : i ≠ (4:Fin 27) := by rcases hi with h|h|h|h <;> omega
  simp [h21, hne, h4]

theorem outerBodyStore_tapeData (r : Fin 27 → Fin R) (d : TapeStore R B) :
    tapeData (outerBodyStore r d) = tapeData d := by
  rw [outerBodyStore, tapeData_setReg, innerResult_tapeData]
  rfl

theorem outerBodyStore_bound (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (hrem : d.reg (r 2)+1 ≤ M) : ∀ j, (outerBodyStore r d).reg j ≤ M := by
  have hb := innerResult_bound r hr M hM (d.reg (r 24)) (innerPrepareStore r d)
    (innerPrepareStore_bound r hr M d hd) (by simpa [innerPrepareStore_reg r hr] using hd (r 24))
  apply setReg_bound _ _ _ M hb
  have he := outerBodyStore_remainder r hr d
  have he' : (innerResult r (d.reg (r 24)) (innerPrepareStore r d)).reg (r 2)+1 = d.reg (r 2)+1 := by
    simpa only [outerBodyStore, TapeStore.setReg, Function.update_self] using he
  rw [he']; exact hrem

theorem outerBody_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 2500*(M+1)^5 ∧
      (outerBody r).Stops inp (d.toCfg (outerBody (B := B) r).entry) t e ∧
      e.store = outerBodyStore r d := by
  obtain ⟨c₁, h₁, hs₁⟩ := innerPrepare_stops r hr inp d
  have hb₁ : ∀ j, c₁.store.reg j ≤ M := by rw [hs₁]; exact innerPrepareStore_bound r hr M d hd
  have hn : c₁.reg (r 26) = d.reg (r 24) := by
    change c₁.store.reg (r 26) = _
    rw [hs₁, innerPrepareStore_reg r hr]; simp
  have hq : c₁.reg (r 4) = 0 := by
    change c₁.store.reg (r 4) = _
    rw [hs₁, innerPrepareStore_reg r hr]; simp
  obtain ⟨t, ht, h₂, _⟩ := innerLoop_stops r hr inp M hM (d.reg (r 24)) c₁.store hn hb₁
    (by change c₁.reg (r 4)+d.reg (r 24) ≤ M; rw [hq]; simpa using hd (r 24))
  have h₃ := TapeMacros.increment_stops (r 2) inp (innerResult r (d.reg (r 24)) c₁.store)
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_, _, ?_, hall, ?_⟩
  · have hp : d.reg (r 4)+d.reg (r 26)+d.reg (r 21)+5*d.reg (r 24)+9 ≤ 8*M+9 := by
      have := hd (r 4); have := hd (r 26); have := hd (r 21); have := hd (r 24); omega
    have hpow := Nat.le_self_pow (by decide : (5:ℕ) ≠ 0) (M+1)
    have hM5 : M ≤ (M+1)^5 := (by omega : M ≤ M+1).trans hpow
    have h15 : 1 ≤ (M+1)^5 := by omega
    have hmul : 2400*M*(M+1)^4 ≤ 2400*(M+1)^5 := by
      calc
        2400*M*(M+1)^4 ≤ 2400*(M+1)*(M+1)^4 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2400 (by omega : M ≤ M+1))
        _ = 2400*(M+1)^5 := by ring
    have ht' := Nat.mul_le_mul_right (2400*(M+1)^4+2) (hd (r 24))
    have heq : M*(2400*(M+1)^4+2) = 2400*M*(M+1)^4+2*M := by ring
    rw [heq] at ht'
    omega
  · change (innerResult r (d.reg (r 24)) c₁.store).setReg (r 2) _ = _
    rw [hs₁]
    rfl






theorem outerLoop_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hn : d.reg (r 25) = n) (hd : ∀ j, d.reg j ≤ M) (hrem : d.reg (r 2)+n ≤ M) :
    ∃ t, t ≤ n*(2500*(M+1)^5+2)+1 ∧
      (outerLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 355)) t
        ((outerResult r n d).toCfg (TapeProgram.loopExit 355)) ∧
      (∀ j, (outerResult r n d).reg j ≤ M) := by
  let Inv : ℕ → TapeStore R B → Prop := fun n c => (∀ j, c.reg j ≤ M) ∧ c.reg (r 2)+n ≤ M
  have hc (c : TapeStore R B) : (outerBodyStore r c).reg (r 25) = c.reg (r 25) :=
    outerBodyStore_fresh r hr c 25 (Or.inr (Or.inr (Or.inr (by decide)))) (by decide)
  have hb : ∀ n c, c.reg (r 25) = n+1 → Inv (n+1) c →
      ∃ t e, t ≤ 2500*(M+1)^5 ∧
        (outerBody r).Stops inp ((c.setReg (r 25) n).toCfg (outerBody (B := B) r).entry) t e ∧
        e.store = outerBodyStore r (c.setReg (r 25) n) ∧ Inv n e.store := by
    intro n c hcn hi
    have hcb := setReg_bound c (r 25) n M hi.1 (by have := hi.1 (r 25); omega)
    have hcr : (c.setReg (r 25) n).reg (r 2)+1 ≤ M := by simp [reg_set27 r hr]; have := hi.2; omega
    obtain ⟨t, e, ht, he, hs⟩ := outerBody_stops r hr inp M hM _ hcb
    refine ⟨t, e, ht, he, hs, ?_⟩
    rw [hs]
    refine ⟨outerBodyStore_bound r hr M hM _ hcb hcr, ?_⟩
    rw [outerBodyStore_remainder r hr]
    simp only [reg_set27 r hr, show (2:Fin 27) ≠ 25 from by decide, ite_false]
    have := hi.2
    omega
  obtain ⟨t, ht, he, hi⟩ := loop_stops (outerBody r) (r 25) (outerBodyStore r) inp
    (2500*(M+1)^5) Inv hc hb n d hn ⟨hd,hrem⟩
  exact ⟨t, ht, he, hi.1⟩

theorem outerResult_frame (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (n : ℕ) (d : TapeStore R B) (i : Fin 27) (hi : i < 2 ∨ i = 3 ∨ i = 19 ∨ 23 ≤ i)
    (h25 : i ≠ 25) (h26 : i ≠ 26) : (outerResult r n d).reg (r i) = d.reg (r i) :=
  loopResult_frame (r 25) (outerBodyStore r) (r i) (hr.ne h25)
    (fun c => outerBodyStore_fresh r hr c i hi h26) n d






theorem outerResult_tapeData (r : Fin 27 → Fin R) (n : ℕ) (d : TapeStore R B) :
    tapeData (outerResult r n d) = tapeData d :=
  loopResult_tapeData (r 25) (outerBodyStore r) (outerBodyStore_tapeData r) n d








theorem multiplyPrepare_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (d : TapeStore R B) :
    ∃ e, (multiplyPrepare r).Stops inp (d.toCfg (multiplyPrepare (B := B) r).entry)
      (d.reg (r 20)+d.reg (r 22)+d.reg (r 2)+d.reg (r 25)+d.reg (r 21)+5*d.reg (r 23)+13) e ∧
      e.store = multiplyPrepareStore r d := by
  have h₁ := TapeMacros.clear_stops (r 20) inp (d.reg (r 20)) d rfl
  have h₂ := TapeMacros.clear_stops (r 22) inp (d.reg (r 22)) (d.setReg (r 20) 0)
    (by simp [reg_set27 r hr])
  have h₃ := TapeMacros.clear_stops (r 2) inp (d.reg (r 2)) ((d.setReg (r 20) 0).setReg (r 22) 0)
    (by simp [reg_set27 r hr])
  obtain ⟨c, hc, hcs⟩ := TapeMacros.copy_stops (r 23) (r 25) (r 21)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) inp
    (((d.setReg (r 20) 0).setReg (r 22) 0).setReg (r 2) 0)
  have hall := ((h₁.seq h₂).seq h₃).seq hc
  refine ⟨c.mapPC (TapeProgram.rightLabel 6), ?_, hcs⟩
  convert hall using 1 <;> first | rfl | (simp [reg_set27 r hr]; omega)

theorem multiplyPrepareStore_reg (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) :
    (multiplyPrepareStore r d).reg (r i) =
      if i = 21 then 0 else if i = 25 then d.reg (r 23)
      else if i = 20 ∨ i = 22 ∨ i = 2 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [multiplyPrepareStore, reg_set27 r hr]

theorem multiplyPrepareStore_bound (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∀ j, (multiplyPrepareStore r d).reg j ≤ M := by
  unfold multiplyPrepareStore
  apply setReg_bound _ _ 0 M _ (by omega)
  apply setReg_bound _ _ _ M
  · exact setReg_bound _ _ 0 M (setReg_bound _ _ 0 M (setReg_bound d _ 0 M hd (by omega)) (by omega)) (by omega)
  · simpa [reg_set27 r hr] using hd (r 23)









theorem multiply_stops_exact (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ 10000*(M+1)^6 ∧
      (multiply r).Stops inp (d.toCfg (multiply (B := B) r).entry) t e ∧
      e.store = multiplyResult r d ∧ (∀ j, e.reg j ≤ M) := by
  obtain ⟨c, hc, hcs⟩ := multiplyPrepare_stops r hr inp d
  have hcb : ∀ j, c.store.reg j ≤ M := by rw [hcs]; exact multiplyPrepareStore_bound r hr M d hd
  have hcn : c.reg (r 25) = d.reg (r 23) := by
    change c.store.reg (r 25) = _
    rw [hcs, multiplyPrepareStore_reg r hr]; simp
  have hcr : c.reg (r 2) = 0 := by
    change c.store.reg (r 2) = _
    rw [hcs, multiplyPrepareStore_reg r hr]; simp
  obtain ⟨t, ht, he, heb⟩ := outerLoop_stops r hr inp M hM (d.reg (r 23)) c.store hcn hcb
    (by change c.reg (r 2)+d.reg (r 23) ≤ M; rw [hcr]; simpa using hd (r 23))
  have hall := hc.seq he
  refine ⟨_, _, ?_, hall, ?_, heb⟩
  · have hp : d.reg (r 20)+d.reg (r 22)+d.reg (r 2)+d.reg (r 25)+d.reg (r 21)+5*d.reg (r 23)+13 ≤ 10*M+13 := by
      have := hd (r 20); have := hd (r 22); have := hd (r 2); have := hd (r 25)
      have := hd (r 21); have := hd (r 23); omega
    have hpow := Nat.le_self_pow (by decide : (6:ℕ) ≠ 0) (M+1)
    have hM6 : M ≤ (M+1)^6 := (by omega : M ≤ M+1).trans hpow
    have h16 : 1 ≤ (M+1)^6 := by omega
    have hmul : 2500*M*(M+1)^5 ≤ 2500*(M+1)^6 := by
      calc
        2500*M*(M+1)^5 ≤ 2500*(M+1)*(M+1)^5 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2500 (by omega : M ≤ M+1))
        _ = 2500*(M+1)^6 := by ring
    have ht' := Nat.mul_le_mul_right (2500*(M+1)^5+2) (hd (r 23))
    have heq : M*(2500*(M+1)^5+2) = 2500*M*(M+1)^5+2*M := by ring
    rw [heq] at ht'
    change d.reg (r 20)+d.reg (r 22)+d.reg (r 2)+d.reg (r 25)+d.reg (r 21)+5*d.reg (r 23)+13+1+t ≤ _
    omega
  · change outerResult r (d.reg (r 23)) c.store = _
    rw [hcs]
    rfl

theorem multiplyResult_tapeData (r : Fin 27 → Fin R) (d : TapeStore R B) :
    tapeData (multiplyResult r d) = tapeData d := by
  rw [multiplyResult, outerResult_tapeData]
  rfl









theorem accept_iff (env : Fin 4 → ℕ) (rem quotient : ℕ) :
    accept env rem quotient = true ↔
      ∀ j < env 3, CoefficientMatches (env 0) (env 1) rem (env 2) quotient j := by
  simp only [accept, decide_eq_true_eq]
  constructor
  · intro h j hj
    exact h ⟨j,hj⟩
  · intro h j
    exact h j.val j.isLt

theorem environment_setReg (r : Fin 27 → Fin R) (d : TapeStore R B) (j : Fin R) (n : ℕ)
    (h₀ : r 0 ≠ j) (h₁ : r 1 ≠ j) (h₃ : r 3 ≠ j) (h₁₉ : r 19 ≠ j) :
    environment r (d.setReg j n) = environment r d := by
  funext i
  fin_cases i <;> simp [environment, TapeStore.setReg, h₀, h₁, h₃, h₁₉]

theorem answer_setReg (r : Fin 27 → Fin R) (d : TapeStore R B) (j : Fin R) (n : ℕ)
    (h₂₀ : r 20 ≠ j) (h₂₂ : r 22 ≠ j) : answer r (d.setReg j n) = answer r d := by
  simp [answer, TapeStore.setReg, h₂₀, h₂₂]

theorem innerBodyStore_environment (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    environment r (innerBodyStore r d) = environment r d := by
  funext i
  fin_cases i
  · exact innerBodyStore_fresh r hr d 0 (Or.inl (by decide))
  · exact innerBodyStore_fresh r hr d 1 (Or.inl (by decide))
  · exact innerBodyStore_fresh r hr d 3 (Or.inl (by decide))
  · exact innerBodyStore_fresh r hr d 19 (Or.inr (Or.inl rfl))

theorem innerBodyStore_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    answer r (innerBodyStore r d) =
      if accept (environment r d) (d.reg (r 2)) (d.reg (r 4)) then some (d.reg (r 2)) else answer r d := by
  let c := certificateResult (certificateLayout r) d
  have hbit : c.reg (r 6) ≤ 1 := certificateResult_flag_le _ (certificateLayout_injective r hr) d
  have hc : c.reg (r 6) = 1 ↔ accept (environment r d) (d.reg (r 2)) (d.reg (r 4)) = true := by
    rw [accept_iff]
    exact certificateResult_correct _ (certificateLayout_injective r hr) d
  have h20 : c.reg (r 20) = d.reg (r 20) := certificate_preserves r hr d 20 (Or.inr (Or.inr (by decide)))
  have h22 : c.reg (r 22) = d.reg (r 22) := certificate_preserves r hr d 22 (Or.inr (Or.inr (by decide)))
  have h2 : c.reg (r 2) = d.reg (r 2) := certificate_preserves r hr d 2 (Or.inl (by decide))
  change answer r ((commitStore (commitLayout r) c).setReg (r 4) _) = _
  rw [answer_setReg r _ _ _ (hr.ne (by decide)) (hr.ne (by decide))]
  by_cases hf : c.reg (r 6) = 0
  · have hac : accept (environment r d) (d.reg (r 2)) (d.reg (r 4)) ≠ true := by
      intro h
      have := hc.mpr h
      omega
    simp [answer, commitStore, commitLayout, hf, hac, h20, h22]
  · have hf1 : c.reg (r 6) = 1 := by omega
    have hac := hc.mp hf1
    simp [answer, commitStore, commitBodyStore, commitLayout, hf, hac, reg_set27 r hr, h2]










theorem innerResult_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (n : ℕ) (d : TapeStore R B) :
    answer r (innerResult r n d) =
      scanRow (accept (environment r d)) (d.reg (r 2)) n (d.reg (r 4)) (answer r d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    let c := d.setReg (r 26) n
    have henv : environment r c = environment r d :=
      environment_setReg r d _ n (hr.ne (by decide)) (hr.ne (by decide))
        (hr.ne (by decide)) (hr.ne (by decide))
    have h2 : c.reg (r 2) = d.reg (r 2) := by simp [c, reg_set27 r hr]
    have h4 : c.reg (r 4) = d.reg (r 4) := by simp [c, reg_set27 r hr]
    have ha : answer r c = answer r d := answer_setReg r d _ n (hr.ne (by decide)) (hr.ne (by decide))
    change answer r (innerResult r n (innerBodyStore r c)) = _
    rw [ih, innerBodyStore_environment r hr c, henv,
      innerBodyStore_fresh r hr c 2 (Or.inl (by decide)), h2, innerBodyStore_quotient r hr c,
      h4, innerBodyStore_answer r hr c, henv, h2, h4, ha]
    rfl

theorem outerBodyStore_environment (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    environment r (outerBodyStore r d) = environment r d := by
  funext i
  fin_cases i
  · exact outerBodyStore_fresh r hr d 0 (Or.inl (by decide)) (by decide)
  · exact outerBodyStore_fresh r hr d 1 (Or.inl (by decide)) (by decide)
  · exact outerBodyStore_fresh r hr d 3 (Or.inr (Or.inl rfl)) (by decide)
  · exact outerBodyStore_fresh r hr d 19 (Or.inr (Or.inr (Or.inl rfl))) (by decide)

theorem outerBodyStore_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    answer r (outerBodyStore r d) =
      scanRow (accept (environment r d)) (d.reg (r 2)) (d.reg (r 24)) 0 (answer r d) := by
  have henv : environment r (innerPrepareStore r d) = environment r d := by
    funext i
    fin_cases i <;> simp [environment, innerPrepareStore_reg r hr]
  have ha : answer r (innerPrepareStore r d) = answer r d := by
    simp [answer, innerPrepareStore_reg r hr]
  unfold outerBodyStore
  rw [answer_setReg r _ _ _ (hr.ne (by decide)) (hr.ne (by decide)), innerResult_answer r hr,
    henv, ha, innerPrepareStore_reg r hr, innerPrepareStore_reg r hr]
  simp

theorem outerResult_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (n : ℕ) (d : TapeStore R B) :
    answer r (outerResult r n d) =
      scanRect (accept (environment r d)) (d.reg (r 24)) n (d.reg (r 2)) (answer r d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    let c := d.setReg (r 25) n
    have henv : environment r c = environment r d :=
      environment_setReg r d _ n (hr.ne (by decide)) (hr.ne (by decide))
        (hr.ne (by decide)) (hr.ne (by decide))
    have h2 : c.reg (r 2) = d.reg (r 2) := by simp [c, reg_set27 r hr]
    have h24 : c.reg (r 24) = d.reg (r 24) := by simp [c, reg_set27 r hr]
    have ha : answer r c = answer r d := answer_setReg r d _ n (hr.ne (by decide)) (hr.ne (by decide))
    change answer r (outerResult r n (outerBodyStore r c)) = _
    rw [ih, outerBodyStore_environment r hr c, henv,
      outerBodyStore_fresh r hr c 24 (Or.inr (Or.inr (Or.inr (by decide)))) (by decide), h24,
      outerBodyStore_remainder r hr c, h2, outerBodyStore_answer r hr c, henv, h2, h24, ha]
    rfl

theorem multiplyResult_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    answer r (multiplyResult r d) =
      scanRect (accept (environment r d)) (d.reg (r 24)) (d.reg (r 23)) 0 none := by
  have henv : environment r (multiplyPrepareStore r d) = environment r d := by
    funext i
    fin_cases i <;> simp [environment, multiplyPrepareStore_reg r hr]
  rw [multiplyResult, outerResult_answer r hr, henv, multiplyPrepareStore_reg r hr, multiplyPrepareStore_reg r hr]
  simp [answer, multiplyPrepareStore_reg r hr]



theorem scanRow_same (test : ℕ → ℕ → Bool) (rem n s : ℕ) :
    scanRow test rem n s (some rem) = some rem := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [scanRow]
    split <;> exact ih _

theorem scanRow_hit (test : ℕ → ℕ → Bool) (rem n s : ℕ) (state : Option ℕ)
    (hit : ∃ i < n, test rem (s+i) = true) : scanRow test rem n s state = some rem := by
  induction n generalizing s state with
  | zero => rcases hit with ⟨i,hi,_⟩; omega
  | succ n ih =>
    rcases hit with ⟨i,hi,hp⟩
    by_cases hz : i = 0
    · subst i
      have hc : test rem s = true := by simpa using hp
      rw [scanRow, if_pos hc]
      exact scanRow_same test rem n (s+1)
    · rw [scanRow]
      apply ih
      refine ⟨i-1, by omega, ?_⟩
      have he : s+1+(i-1) = s+i := by omega
      rw [he]; exact hp

theorem scanRow_nonempty (test : ℕ → ℕ → Bool) (rem n s : ℕ) (state : Option ℕ)
    (hs : state ≠ none) : scanRow test rem n s state ≠ none := by
  induction n generalizing s state with
  | zero => exact hs
  | succ n ih =>
    rw [scanRow]
    apply ih
    split <;> simp_all

theorem scanRow_correct (test : ℕ → ℕ → Bool) (rem n s target : ℕ) (state : Option ℕ)
    (hs : Correct target state) (hg : ∀ i < n, test rem (s+i) = true → rem = target) :
    Correct target (scanRow test rem n s state) := by
  induction n generalizing s state with
  | zero => exact hs
  | succ n ih =>
    rw [scanRow]
    apply ih
    · split
      · have he : rem = target := hg 0 (by omega) (by simpa using ‹test rem s = true›)
        simpa [Correct] using he
      · exact hs
    · intro i hi ht
      apply hg (i+1) (by omega)
      have he : s+(i+1) = s+1+i := by omega
      rw [he]; exact ht

theorem scanRect_nonempty (test : ℕ → ℕ → Bool) (Q n r : ℕ) (state : Option ℕ)
    (hs : state ≠ none) : scanRect test Q n r state ≠ none := by
  induction n generalizing r state with
  | zero => exact hs
  | succ n ih =>
    rw [scanRect]
    exact ih _ _ (scanRow_nonempty test r Q 0 state hs)

theorem scanRect_hit (test : ℕ → ℕ → Bool) (Q n r : ℕ) (state : Option ℕ)
    (hit : ∃ i < n, ∃ s < Q, test (r+i) s = true) : scanRect test Q n r state ≠ none := by
  induction n generalizing r state with
  | zero => rcases hit with ⟨i,hi,_⟩; omega
  | succ n ih =>
    rcases hit with ⟨i,hi,s,hs,hp⟩
    rw [scanRect]
    by_cases hz : i = 0
    · subst i
      have hrow := scanRow_hit test r Q 0 state ⟨s,hs,by simpa using hp⟩
      apply scanRect_nonempty
      rw [hrow]
      simp
    · apply ih
      refine ⟨i-1,by omega,s,hs,?_⟩
      have he : r+1+(i-1) = r+i := by omega
      rw [he]; exact hp

theorem scanRect_correct (test : ℕ → ℕ → Bool) (Q n r target : ℕ) (state : Option ℕ)
    (hs : Correct target state)
    (hg : ∀ i < n, ∀ s < Q, test (r+i) s = true → r+i = target) :
    Correct target (scanRect test Q n r state) := by
  induction n generalizing r state with
  | zero => exact hs
  | succ n ih =>
    rw [scanRect]
    apply ih
    · apply scanRow_correct test r Q 0 target state hs
      intro s hs hp
      have h := hg 0 (by omega) s hs (by simpa using hp)
      simpa using h
    · intro i hi s hs hp
      have he : r+(i+1) = r+1+i := by omega
      have h := hg (i+1) (by omega) s hs (by simpa only [he] using hp)
      simpa only [he] using h

theorem scanRect_complete (test : ℕ → ℕ → Bool) (Q n target : ℕ)
    (hg : ∀ i < n, ∀ s < Q, test i s = true → i = target)
    (hit : ∃ i < n, ∃ s < Q, test i s = true) :
    scanRect test Q n 0 none = some target := by
  have hc := scanRect_correct test Q n 0 target none (by simp [Correct])
    (by simpa using hg)
  have hn := scanRect_hit test Q n 0 none (by simpa using hit)
  cases he : scanRect test Q n 0 none with
  | none => exact False.elim (hn he)
  | some v =>
    have hv : v = target := hc v he
    simpa only [hv] using he

/-- Semantic correctness of the actual374-label bounded source multiplication
search, for the exact BinaryField quotient/remainder index operations. -/
theorem multiplyResult_index (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (ell : ℕ) (h : 0 < ell) (m a b : Fin (2^ell)) (d : TapeStore R B)
    (ha : d.reg (r 0) = a.val) (hb : d.reg (r 1) = b.val)
    (hm : d.reg (r 3) = 2^ell+m.val) (hN : d.reg (r 19) = 3*ell+1)
    (hq : d.reg (r 23) = 2^ell) (hQ : d.reg (r 24) = 2^(2*ell)) :
    (multiplyResult r d).reg (r 20) =
      (BinaryField.multiplyIndex ell h m (indexEquiv ell a) (indexEquiv ell b)).val := by
  let test := accept (environment r d)
  let target := (BinaryField.multiplyIndex ell h m (indexEquiv ell a) (indexEquiv ell b)).val
  have htest (i : Fin (2^ell)) (s : Fin (2^(2*ell))) : test i.val s.val = true ↔
      BinaryField.DivMatches ell m (indexEquiv ell a) (indexEquiv ell b)
        (indexEquiv ell i) (indexEquiv (2*ell) s) := by
    rw [accept_iff]
    change (∀ j < d.reg (r 19), CoefficientMatches (d.reg (r 0)) (d.reg (r 1)) i.val
      (d.reg (r 3)) s.val j) ↔ _
    rw [ha,hb,hm,hN]
    exact coefficientMatches_all_iff ell m a b i s
  have hg : ∀ i < 2^ell, ∀ s < 2^(2*ell), test i s = true → i = target := by
    intro i hi s hs hp
    have hu := accepted_remainder_unique ell h m a b ⟨i,hi⟩ ⟨s,hs⟩ ((htest ⟨i,hi⟩ ⟨s,hs⟩).mp hp)
    exact congrArg Fin.val hu
  have hit : ∃ i < 2^ell, ∃ s < 2^(2*ell), test i s = true := by
    obtain ⟨i,s,hs⟩ := BinaryField.exists_divMatches ell h m (indexEquiv ell a) (indexEquiv ell b)
    exact ⟨i.val,i.isLt,s.val,s.isLt,(htest i s).mpr hs⟩
  have hanswer : answer r (multiplyResult r d) = some target := by
    rw [multiplyResult_answer r hr d,hq,hQ]
    exact scanRect_complete test _ _ target hg hit
  unfold answer at hanswer
  split at hanswer
  · contradiction
  · exact Option.some.inj hanswer

theorem multiplyResult_input (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) (hi : i < 2 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24) :
    (multiplyResult r d).reg (r i) = d.reg (r i) := by
  rw [multiplyResult, outerResult_frame r hr _ _ i (by
    rcases hi with h|h|h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega))))
    (by rcases hi with h|h|h|h|h <;> omega) (by rcases hi with h|h|h|h|h <;> omega),
    multiplyPrepareStore_reg r hr]
  have h21 : i ≠ (21:Fin 27) := by rcases hi with h|h|h|h|h <;> omega
  have h25 : i ≠ (25:Fin 27) := by rcases hi with h|h|h|h|h <;> omega
  have h20 : i ≠ (20:Fin 27) := by rcases hi with h|h|h|h|h <;> omega
  have h22 : i ≠ (22:Fin 27) := by rcases hi with h|h|h|h|h <;> omega
  have h2 : i ≠ (2:Fin 27) := by rcases hi with h|h|h|h|h <;> omega
  simp [h21,h25,h20,h22,h2]

theorem innerBodyStore_outside (r : Fin 27 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 27, j ≠ r i) :
    (innerBodyStore r d).reg j = d.reg j := by
  unfold innerBodyStore
  simp only [TapeStore.setReg, Function.update_of_ne (hne 4)]
  rw [commitStore_fresh _ _ _ (hne 20) (hne 21) (hne 22) (hne 6)]
  apply certificateResult_outside
  intro i
  exact hne ⟨i.val,by have := i.isLt; omega⟩

theorem innerResult_outside (r : Fin 27 → Fin R) (n : ℕ) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 27, j ≠ r i) :
    (innerResult r n d).reg j = d.reg j :=
  loopResult_frame (r 26) (innerBodyStore r) j (hne 26)
    (fun c => innerBodyStore_outside r c j hne) n d

theorem outerBodyStore_outside (r : Fin 27 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 27, j ≠ r i) :
    (outerBodyStore r d).reg j = d.reg j := by
  unfold outerBodyStore
  simp only [TapeStore.setReg, Function.update_of_ne (hne 2)]
  rw [innerResult_outside r _ _ j hne]
  simp [innerPrepareStore, TapeStore.setReg, hne 4,hne 21,hne 26]

theorem outerResult_outside (r : Fin 27 → Fin R) (n : ℕ) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 27, j ≠ r i) :
    (outerResult r n d).reg j = d.reg j :=
  loopResult_frame (r 25) (outerBodyStore r) j (hne 25)
    (fun c => outerBodyStore_outside r c j hne) n d

theorem multiplyResult_outside (r : Fin 27 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 27, j ≠ r i) :
    (multiplyResult r d).reg j = d.reg j := by
  rw [multiplyResult, outerResult_outside r _ _ j hne]
  simp [multiplyPrepareStore, TapeStore.setReg, hne 2,hne 20,hne 21,hne 22,hne 25]

/-- Complete physical-source multiplication contract. Inputs, all caller
registers outside the static layout, read-only heads/output and buffers are
preserved. The executable result is exactly BinaryField.multiplyIndex. -/
theorem multiply_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (h : 0 < ell) (m a b : Fin (2^ell))
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j, d.reg j ≤ M)
    (ha : d.reg (r 0) = a.val) (hb : d.reg (r 1) = b.val)
    (hm : d.reg (r 3) = 2^ell+m.val) (hN : d.reg (r 19) = 3*ell+1)
    (hq : d.reg (r 23) = 2^ell) (hQ : d.reg (r 24) = 2^(2*ell)) :
    ∃ t e, t ≤ 10000*(M+1)^6 ∧
      (multiply r).Stops inp (d.toCfg (multiply (B := B) r).entry) t e ∧
      e.store = multiplyResult r d ∧
      e.reg (r 20) = (BinaryField.multiplyIndex ell h m (indexEquiv ell a) (indexEquiv ell b)).val ∧
      (∀ i, i < 2 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j, (∀ i, j ≠ r i) → e.reg j = d.reg j) ∧
      (∀ j, e.reg j ≤ M) ∧ tapeData e.store = tapeData d := by
  obtain ⟨t,e,ht,he,hstore,hbound⟩ := multiply_stops_exact r hr inp M hM d hd
  refine ⟨t,e,ht,he,hstore,?_,?_,?_,hbound,?_⟩
  · change e.store.reg (r 20) = _
    rw [hstore]
    exact multiplyResult_index r hr ell h m a b d ha hb hm hN hq hQ
  · intro i hi
    change e.store.reg (r i) = _
    rw [hstore]; exact multiplyResult_input r hr d i hi
  · intro j hj
    change e.store.reg j = _
    rw [hstore]; exact multiplyResult_outside r d j hj
  · rw [hstore]; exact multiplyResult_tapeData r d



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










theorem additionBodyStore_fresh (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) (hi : i < 5 ∨ i = 19 ∨ 23 ≤ i) (h2 : i ≠ 2) :
    (additionBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold additionBodyStore
  simp only [reg_set27 r hr,if_neg h2]
  rw [commitStore_fresh _ _ _
    (hr.ne (show i ≠ (20:Fin 27) from by rcases hi with h|h|h <;> omega))
    (hr.ne (show i ≠ (21:Fin 27) from by rcases hi with h|h|h <;> omega))
    (hr.ne (show i ≠ (22:Fin 27) from by rcases hi with h|h|h <;> omega))
    (hr.ne (show i ≠ (6:Fin 27) from by rcases hi with h|h|h <;> omega))]
  apply certificate_preserves r hr d i
  rcases hi with h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by omega))

theorem additionBodyStore_index (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) : (additionBodyStore r d).reg (r 2) = d.reg (r 2)+1 := by
  unfold additionBodyStore
  simp only [TapeStore.setReg,Function.update_self]
  rw [commitStore_fresh _ _ _
    (hr.ne (show (2:Fin 27) ≠ 20 from by decide)) (hr.ne (show (2:Fin 27) ≠ 21 from by decide))
    (hr.ne (show (2:Fin 27) ≠ 22 from by decide)) (hr.ne (show (2:Fin 27) ≠ 6 from by decide)),
    certificate_preserves r hr d 2 (Or.inl (by decide))]

theorem additionBodyStore_bound (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 2)+1 ≤ M) :
    ∀ j,(additionBodyStore r d).reg j ≤ M := by
  apply setReg_bound _ _ _ M (commitStore_bound _ (commitLayout_injective r hr) M hM _
    (certificateResult_bound _ (certificateLayout_injective r hr) M hM d hd))
  have he := additionBodyStore_index r hr d
  have he' : (commitStore (commitLayout r) (certificateResult (certificateLayout r) d)).reg (r 2)+1 = d.reg (r 2)+1 := by
    simpa only [additionBodyStore,TapeStore.setReg,Function.update_self] using he
  rw [he'];exact hc

theorem additionBody_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∃ t e,t ≤ 2400*(M+1)^4 ∧
      (additionBody r).Stops inp (d.toCfg (additionBody (B:=B) r).entry) t e ∧ e.store = additionBodyStore r d := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁⟩ := certificate_stops_exact (certificateLayout r) (certificateLayout_injective r hr) inp M hM d hd
  have hb₁ : ∀ j,c₁.store.reg j ≤ M := by rw [hs₁];exact certificateResult_bound _ (certificateLayout_injective r hr) M hM d hd
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂⟩ := commit_stops (commitLayout r) (commitLayout_injective r hr) inp M c₁.store hb₁
  have h₃ := TapeMacros.increment_stops (r 2) inp c₂.store
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_,_,?_,hall,?_⟩
  · have hpow := Nat.le_self_pow (by decide : (4:ℕ) ≠ 0) (M+1)
    omega
  · change c₂.store.setReg (r 2) _ = _
    rw [hs₂,hs₁];rfl




theorem additionLoop_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B)
    (hn : d.reg (r 25) = n) (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 2)+n ≤ M) :
    ∃ t,t ≤ n*(2400*(M+1)^4+2)+1 ∧
      (additionLoop r).Stops inp (d.toCfg (TapeProgram.loopHeader 338)) t
        ((additionFold r n d).toCfg (TapeProgram.loopExit 338)) ∧ (∀ j,(additionFold r n d).reg j ≤ M) := by
  let Inv : ℕ → TapeStore R B → Prop := fun n c => (∀ j,c.reg j ≤ M) ∧ c.reg (r 2)+n ≤ M
  have hf (c : TapeStore R B) : (additionBodyStore r c).reg (r 25) = c.reg (r 25) :=
    additionBodyStore_fresh r hr c 25 (Or.inr (Or.inr (by decide))) (by decide)
  have hb : ∀ n c,c.reg (r 25) = n+1 → Inv (n+1) c → ∃ t e,t ≤ 2400*(M+1)^4 ∧
      (additionBody r).Stops inp ((c.setReg (r 25) n).toCfg (additionBody (B:=B) r).entry) t e ∧
      e.store = additionBodyStore r (c.setReg (r 25) n) ∧ Inv n e.store := by
    intro n c hcn hi
    have hcb := setReg_bound c (r 25) n M hi.1 (by have := hi.1 (r 25);omega)
    have hci : (c.setReg (r 25) n).reg (r 2)+1 ≤ M := by simp [reg_set27 r hr];have := hi.2;omega
    obtain ⟨t,e,ht,he,hs⟩ := additionBody_stops r hr inp M hM _ hcb
    refine ⟨t,e,ht,he,hs,?_⟩
    rw [hs]
    refine ⟨additionBodyStore_bound r hr M hM _ hcb hci,?_⟩
    rw [additionBodyStore_index r hr]
    simp only [reg_set27 r hr,show (2:Fin 27) ≠ 25 from by decide,ite_false]
    have := hi.2;omega
  obtain ⟨t,ht,he,hi⟩ := loop_stops (additionBody r) (r 25) (additionBodyStore r) inp (2400*(M+1)^4) Inv hf hb n d hn ⟨hd,hc⟩
  exact ⟨t,ht,he,hi.1⟩






theorem additionPrepare_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∃ t e,t ≤ 12*M+21 ∧
      (additionPrepare r).Stops inp (d.toCfg (additionPrepare (B:=B) r).entry) t e ∧ e.store = additionPrepareStore r d := by
  obtain ⟨c₁,h₁,hs₁⟩ := multiplyPrepare_stops r hr inp d
  have hb₁ : ∀ j,c₁.store.reg j ≤ M := by rw [hs₁];exact multiplyPrepareStore_bound r hr M d hd
  obtain ⟨c₂,h₂,hs₂⟩ := setOne_stops (r 1) inp c₁.store
  have hb₂ : ∀ j,c₂.store.reg j ≤ M := by rw [hs₂];exact setReg_bound _ _ 1 M hb₁ hM
  obtain ⟨c₃,h₃,hs₃⟩ := setOne_stops (r 4) inp c₂.store
  have hall := (h₁.seq h₂).seq h₃
  refine ⟨_,_,?_,hall,?_⟩
  · have := hd (r 20);have := hd (r 22);have := hd (r 2);have := hd (r 25)
    have := hd (r 21);have := hd (r 23);have := hb₁ (r 1);have := hb₂ (r 4);omega
  · change c₃.store = _
    rw [hs₃,hs₂,hs₁];rfl

theorem additionPrepareStore_reg (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) : (additionPrepareStore r d).reg (r i) =
      if i = 1 ∨ i = 4 then 1 else if i = 21 then 0 else if i = 25 then d.reg (r 23)
      else if i = 20 ∨ i = 22 ∨ i = 2 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [additionPrepareStore,reg_set27 r hr,multiplyPrepareStore_reg r hr]

theorem additionPrepareStore_bound (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∀ j,(additionPrepareStore r d).reg j ≤ M :=
  setReg_bound _ _ 1 M (setReg_bound _ _ 1 M (multiplyPrepareStore_bound r hr M d hd) hM) hM





theorem addition_stops_exact (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∃ t e,t ≤ 3000*(M+1)^5 ∧
      (addition r).Stops inp (d.toCfg (addition (B:=B) r).entry) t e ∧
      e.store = additionResult r d ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨t₁,c,ht₁,hc,hcs⟩ := additionPrepare_stops r hr inp M hM d hd
  have hcb : ∀ j,c.store.reg j ≤ M := by rw [hcs];exact additionPrepareStore_bound r hr M hM d hd
  have hcn : c.reg (r 25) = d.reg (r 23) := by change c.store.reg (r 25) = _;rw [hcs,additionPrepareStore_reg r hr];simp
  have hcc : c.reg (r 2) = 0 := by change c.store.reg (r 2) = _;rw [hcs,additionPrepareStore_reg r hr];simp
  obtain ⟨t₂,ht₂,h₂,hb₂⟩ := additionLoop_stops r hr inp M hM (d.reg (r 23)) c.store hcn hcb
    (by change c.reg (r 2)+d.reg (r 23) ≤ M;rw [hcc];simpa using hd (r 23))
  have hall := hc.seq h₂
  refine ⟨_,_,?_,hall,?_,hb₂⟩
  · have hpow := Nat.le_self_pow (by decide : (5:ℕ) ≠ 0) (M+1)
    have hM5 : M ≤ (M+1)^5 := (by omega : M ≤ M+1).trans hpow
    have h15 : 1 ≤ (M+1)^5 := by omega
    have hm : 2400*M*(M+1)^4 ≤ 2400*(M+1)^5 := by
      calc
        2400*M*(M+1)^4 ≤ 2400*(M+1)*(M+1)^4 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega : M ≤ M+1))
        _ = 2400*(M+1)^5 := by ring
    have ht' := Nat.mul_le_mul_right (2400*(M+1)^4+2) (hd (r 23))
    have heq : M*(2400*(M+1)^4+2) = 2400*M*(M+1)^4+2*M := by ring
    rw [heq] at ht'
    omega
  · change additionFold r (d.reg (r 23)) c.store = _
    rw [hcs];rfl

theorem rawConvolution_one (a k : ℕ) : rawConvolution a 1 k = bitEquiv (Nat.testBit a k) := by
  unfold rawConvolution
  rw [Finset.sum_eq_single k]
  · rw [Nat.sub_self, Nat.testBit_one_zero]
    simp [bitEquiv_true]
  · intro j hj hne
    have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
    have hsub : k-j ≠ 0 := by omega
    have hb : Nat.testBit 1 (k-j) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact hsub (Nat.testBit_one_eq_true_iff_self_eq_zero.mp ht)
    rw [hb,bitEquiv_false,mul_zero]
  · simp

theorem add_matches_iff (ell : ℕ) (a b rem : Fin (2^ell)) :
    (∀ j < 3*ell+1, CoefficientMatches a.val 1 rem.val b.val 1 j) ↔
      rem = BinaryField.addIndex ell a b := by
  constructor
  · intro hmatch
    apply (indexEquiv ell).injective
    funext j
    have hj := hmatch j.val (by have := j.isLt; omega)
    unfold CoefficientMatches at hj
    rw [rawConvolution_one,rawConvolution_one] at hj
    change indexEquiv ell rem j = indexEquiv ell ((indexEquiv ell).symm
      (BinaryField.add (indexEquiv ell a) (indexEquiv ell b))) j
    rw [Equiv.apply_symm_apply]
    change indexEquiv ell rem j = indexEquiv ell a j+indexEquiv ell b j
    rw [indexEquiv_bit,indexEquiv_bit,indexEquiv_bit]
    calc
      bitEquiv (Nat.testBit rem.val j.val) =
          (bitEquiv (Nat.testBit rem.val j.val)+bitEquiv (Nat.testBit b.val j.val))+
            bitEquiv (Nat.testBit b.val j.val) := (CharTwo.add_cancel_right _ _).symm
      _ = bitEquiv (Nat.testBit a.val j.val)+bitEquiv (Nat.testBit b.val j.val) := by rw [← hj]
  · intro heq
    subst rem
    intro j hj
    unfold CoefficientMatches
    rw [rawConvolution_one,rawConvolution_one]
    have he : bitEquiv (Nat.testBit (BinaryField.addIndex ell a b).val j) =
        bitEquiv (Nat.testBit a.val j)+bitEquiv (Nat.testBit b.val j) := by
      rw [← bufferCoefficient_bit,← bufferCoefficient_bit,← bufferCoefficient_bit]
      unfold BinaryField.addIndex
      rw [Equiv.apply_symm_apply]
      unfold BinaryField.bufferCoefficient
      split_ifs <;> rfl
    rw [he]
    have hc : bitEquiv (Nat.testBit b.val j)+bitEquiv (Nat.testBit b.val j) = 0 := by
      exact CharTwo.add_self_eq_zero _
    rw [add_assoc,hc,add_zero]
theorem additionBodyStore_environment (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    environment r (additionBodyStore r d) = environment r d := by
  funext i
  fin_cases i
  · exact additionBodyStore_fresh r hr d 0 (Or.inl (by decide)) (by decide)
  · exact additionBodyStore_fresh r hr d 1 (Or.inl (by decide)) (by decide)
  · exact additionBodyStore_fresh r hr d 3 (Or.inl (by decide)) (by decide)
  · exact additionBodyStore_fresh r hr d 19 (Or.inr (Or.inl rfl)) (by decide)

theorem additionBodyStore_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    answer r (additionBodyStore r d) =
      if accept (environment r d) (d.reg (r 2)) (d.reg (r 4)) then some (d.reg (r 2)) else answer r d := by
  have h := innerBodyStore_answer r hr d
  unfold innerBodyStore at h
  rw [answer_setReg r _ _ _ (hr.ne (by decide)) (hr.ne (by decide))] at h
  unfold additionBodyStore
  rw [answer_setReg r _ _ _ (hr.ne (by decide)) (hr.ne (by decide))]
  exact h

theorem additionFold_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (n : ℕ) (d : TapeStore R B) :
    answer r (additionFold r n d) =
      scanRect (fun c _ => accept (environment r d) c (d.reg (r 4))) 1 n (d.reg (r 2)) (answer r d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    let c := d.setReg (r 25) n
    have henv : environment r c = environment r d := environment_setReg r d _ n
      (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide))
    have h2 : c.reg (r 2) = d.reg (r 2) := by simp [c,reg_set27 r hr]
    have h4 : c.reg (r 4) = d.reg (r 4) := by simp [c,reg_set27 r hr]
    have ha : answer r c = answer r d := answer_setReg r d _ n (hr.ne (by decide)) (hr.ne (by decide))
    change answer r (additionFold r n (additionBodyStore r c)) = _
    rw [ih,additionBodyStore_environment r hr c,henv,
      additionBodyStore_fresh r hr c 4 (Or.inl (by decide)) (by decide),h4,
      additionBodyStore_index r hr c,h2,additionBodyStore_answer r hr c,henv,h2,h4,ha]
    rfl

theorem additionResult_answer (r : Fin 27 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    answer r (additionResult r d) =
      scanRect (fun c _ => accept (environment r (additionPrepareStore r d)) c 1) 1 (d.reg (r 23)) 0 none := by
  rw [additionResult,additionFold_answer r hr]
  simp [additionPrepareStore_reg r hr,answer]

theorem additionResult_index (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (ell : ℕ) (a b : Fin (2^ell)) (d : TapeStore R B)
    (ha : d.reg (r 0) = a.val) (hb : d.reg (r 3) = b.val)
    (hN : d.reg (r 19) = 3*ell+1) (hq : d.reg (r 23) = 2^ell) :
    (additionResult r d).reg (r 20) = (BinaryField.addIndex ell a b).val := by
  let p := additionPrepareStore r d
  let test := fun c (_ : ℕ) => accept (environment r p) c 1
  let target := (BinaryField.addIndex ell a b).val
  have htest (i : Fin (2^ell)) : test i.val 0 = true ↔ i = BinaryField.addIndex ell a b := by
    rw [accept_iff]
    change (∀ j < p.reg (r 19),CoefficientMatches (p.reg (r 0)) (p.reg (r 1)) i.val (p.reg (r 3)) 1 j) ↔ _
    simpa [p,additionPrepareStore_reg r hr,ha,hb,hN] using add_matches_iff ell a b i
  have hg : ∀ i < 2^ell,∀ s < 1,test i s = true → i = target := by
    intro i hi s hs hp
    have he : (⟨i,hi⟩ : Fin (2^ell)) = BinaryField.addIndex ell a b := (htest ⟨i,hi⟩).mp hp
    exact congrArg Fin.val he
  have hit : ∃ i < 2^ell,∃ s < 1,test i s = true := by
    exact ⟨(BinaryField.addIndex ell a b).val,(BinaryField.addIndex ell a b).isLt,0,by omega,
      (htest (BinaryField.addIndex ell a b)).mpr rfl⟩
  have hanswer : answer r (additionResult r d) = some target := by
    rw [additionResult_answer r hr d,hq]
    exact scanRect_complete test _ _ target hg hit
  unfold answer at hanswer
  split at hanswer
  · contradiction
  · exact Option.some.inj hanswer

theorem additionBodyStore_tapeData (r : Fin 27 → Fin R) (d : TapeStore R B) :
    tapeData (additionBodyStore r d) = tapeData d := by
  rw [additionBodyStore,tapeData_setReg,commitStore_tapeData,certificateResult_tapeData]

theorem additionResult_tapeData (r : Fin 27 → Fin R) (d : TapeStore R B) :
    tapeData (additionResult r d) = tapeData d := by
  rw [additionResult,additionFold,
    loopResult_tapeData (r 25) (additionBodyStore r) (additionBodyStore_tapeData r)]
  rfl

theorem additionResult_input (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (d : TapeStore R B) (i : Fin 27) (hi : i = 0 ∨ i = 3 ∨ i = 19 ∨ 23 ≤ i)
    (h25 : i ≠ 25) : (additionResult r d).reg (r i) = d.reg (r i) := by
  rw [additionResult,additionFold,loopResult_frame (r 25) (additionBodyStore r) (r i) (hr.ne h25)
    (fun c => additionBodyStore_fresh r hr c i (by
      rcases hi with h|h|h|h
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)) (by rcases hi with h|h|h|h <;> omega)),
    additionPrepareStore_reg r hr]
  have h1 : i ≠ (1:Fin 27) := by rcases hi with h|h|h|h <;> omega
  have h4 : i ≠ (4:Fin 27) := by rcases hi with h|h|h|h <;> omega
  have h21 : i ≠ (21:Fin 27) := by rcases hi with h|h|h|h <;> omega
  have h20 : i ≠ (20:Fin 27) := by rcases hi with h|h|h|h <;> omega
  have h22 : i ≠ (22:Fin 27) := by rcases hi with h|h|h|h <;> omega
  have h2 : i ≠ (2:Fin 27) := by rcases hi with h|h|h|h <;> omega
  simp [h1,h4,h21,h25,h20,h22,h2]

theorem additionBodyStore_outside (r : Fin 27 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 27,j ≠ r i) : (additionBodyStore r d).reg j = d.reg j := by
  unfold additionBodyStore
  simp only [TapeStore.setReg,Function.update_of_ne (hne 2)]
  rw [commitStore_fresh _ _ _ (hne 20) (hne 21) (hne 22) (hne 6)]
  apply certificateResult_outside
  intro i
  exact hne ⟨i.val,by have := i.isLt;omega⟩

theorem additionResult_outside (r : Fin 27 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 27,j ≠ r i) : (additionResult r d).reg j = d.reg j := by
  rw [additionResult,additionFold,loopResult_frame (r 25) (additionBodyStore r) j (hne 25)
    (fun c => additionBodyStore_outside r c j hne)]
  simp only [additionPrepareStore,TapeStore.setReg,Function.update_of_ne (hne 1),Function.update_of_ne (hne 4)]
  unfold multiplyPrepareStore
  simp [TapeStore.setReg,hne 2,hne 20,hne 21,hne 22,hne 25]

theorem addition_stops (r : Fin 27 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (a b : Fin (2^ell)) (M : ℕ) (hM : 1 ≤ M)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (ha : d.reg (r 0) = a.val) (hb : d.reg (r 3) = b.val)
    (hN : d.reg (r 19) = 3*ell+1) (hq : d.reg (r 23) = 2^ell) :
    ∃ t e,t ≤ 3000*(M+1)^5 ∧
      (addition r).Stops inp (d.toCfg (addition (B:=B) r).entry) t e ∧ e.store = additionResult r d ∧
      e.reg (r 20) = (BinaryField.addIndex ell a b).val ∧
      (∀ i,i = 0 ∨ i = 3 ∨ i = 19 ∨ 23 ≤ i → i ≠ 25 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ tapeData e.store = tapeData d := by
  obtain ⟨t,e,ht,he,hs,hbound⟩ := addition_stops_exact r hr inp M hM d hd
  refine ⟨t,e,ht,he,hs,?_,?_,?_,hbound,?_⟩
  · change e.store.reg (r 20) = _
    rw [hs];exact additionResult_index r hr ell a b d ha hb hN hq
  · intro i hi h25
    change e.store.reg (r i) = _
    rw [hs];exact additionResult_input r hr d i hi h25
  · intro j hj
    change e.store.reg j = _
    rw [hs];exact additionResult_outside r d j hj
  · rw [hs];exact additionResult_tapeData r d











theorem oneTest_stops (x flag : Fin R) (hxf : x ≠ flag) (inp : Inputs) (d : TapeStore R B) :
    ∃ t,t ≤ 3 ∧ (oneTest x flag).Stops inp (d.toCfg 0) t ((oneTestStore x flag d).toCfg 3) := by
  by_cases hx : d.reg x = 0
  · refine ⟨1,by omega,⟨?_,?_⟩⟩
    · apply TapeProgram.Exec.one
      · simp [TapeProgram.halted,oneTest]
      · simp [TapeProgram.step,oneTest,oneTestStore,hx]
    · simp [TapeProgram.halted,oneTest]
  · let c := d.setReg x (d.reg x-1)
    have hhead : (oneTest x flag).step inp (d.toCfg 0) = c.toCfg 1 := by
      simp [TapeProgram.step,oneTest,hx,c,TapeStore.setReg]
    by_cases h1 : d.reg x = 1
    · have hc0 : c.reg x = 0 := by simp [c,h1,TapeStore.setReg]
      refine ⟨3,by omega,⟨?_,?_⟩⟩
      · apply TapeProgram.Exec.step (by simp [TapeProgram.halted,oneTest]) hhead
        apply TapeProgram.Exec.step (d:=c.toCfg 2) (by simp [TapeProgram.halted,oneTest])
        · simp [TapeProgram.step,oneTest,hc0]
        · apply TapeProgram.Exec.one
          · simp [TapeProgram.halted,oneTest]
          · simp [TapeProgram.step,oneTest,oneTestStore,hx,h1,c,TapeStore.setReg,Ne.symm hxf]
      · simp [TapeProgram.halted,oneTest]
    · have hcpos : c.reg x ≠ 0 := by simp [c,TapeStore.setReg];omega
      have hnpos : d.reg x-1 ≠ 0 := by omega
      refine ⟨2,by omega,⟨?_,?_⟩⟩
      · apply TapeProgram.Exec.step (by simp [TapeProgram.halted,oneTest]) hhead
        apply TapeProgram.Exec.one
        · simp [TapeProgram.halted,oneTest]
        · simp [TapeProgram.step,oneTest,oneTestStore,hx,h1,c,hcpos,hnpos,TapeStore.setReg,
            Function.update_idem,Nat.sub_sub]
      · simp [TapeProgram.halted,oneTest]




theorem isOne_stops (x flag : Fin R) (hxf : x ≠ flag) (inp : Inputs) (d : TapeStore R B) :
    ∃ t e,t ≤ d.reg flag+5 ∧ (isOne x flag).Stops inp (d.toCfg (isOne (B:=B) x flag).entry) t e ∧
      e.store = isOneStore x flag d := by
  have hclear := TapeMacros.clear_stops flag inp (d.reg flag) d rfl
  obtain ⟨t,ht,hstop⟩ := oneTest_stops x flag hxf inp (d.setReg flag 0)
  have hall := hclear.seq hstop
  exact ⟨_,_,by omega,hall,rfl⟩

theorem isOneStore_flag (x flag : Fin R) (hxf : x ≠ flag) (d : TapeStore R B) :
    (isOneStore x flag d).reg flag = if d.reg x = 1 then 1 else 0 := by
  unfold isOneStore oneTestStore
  simp only [TapeStore.setReg,Function.update_self,Function.update_of_ne hxf]
  split <;> simp_all [Function.update,Ne.symm hxf]
  split <;> simp_all [Function.update,Ne.symm hxf]

theorem isOneStore_fresh (x flag j : Fin R) (d : TapeStore R B) (hjx : j ≠ x) (hjf : j ≠ flag) :
    (isOneStore x flag d).reg j = d.reg j := by
  unfold isOneStore oneTestStore
  split <;> simp_all [TapeStore.setReg]
  split <;> simp_all [TapeStore.setReg]

theorem isOneStore_tapeData (x flag : Fin R) (d : TapeStore R B) :
    tapeData (isOneStore x flag d) = tapeData d := by
  unfold isOneStore oneTestStore
  split <;> try rfl
  split <;> rfl

theorem isOneStore_bound (x flag : Fin R) (hxf : x ≠ flag) (M : ℕ) (hM : 1 ≤ M)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) : ∀ j,(isOneStore x flag d).reg j ≤ M := by
  unfold isOneStore oneTestStore
  have hb := setReg_bound d flag 0 M hd (by omega)
  split
  · exact hb
  · split
    · apply setReg_bound _ _ _ M (setReg_bound _ _ 0 M hb (by omega))
      simp [TapeStore.setReg];omega
    · apply setReg_bound _ _ _ M hb
      have := hb x
      omega

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





theorem inverseMultiplyLayout_injective (r : Fin 31 → Fin R) (hr : Function.Injective r) :
    Function.Injective (inverseMultiplyLayout r) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin 31 => z.val) (hr h)

theorem inverseCommitLayout_injective (r : Fin 31 → Fin R) (hr : Function.Injective r) :
    Function.Injective (inverseCommitLayout r) := by
  intro i j h
  have h' := hr h
  fin_cases i <;> fin_cases j <;> simp_all [inverseCommitLayout]

theorem reg_set31 (r : Fin 31 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i j : Fin 31) (n : ℕ) :
    (d.setReg (r i) n).reg (r j) = if j = i then n else d.reg (r j) := by
  by_cases h : j = i
  · subst j;simp
  · simp [TapeStore.setReg,h,hr.ne h]

theorem inverseMultiply_preserves (r : Fin 31 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 31) (hi : i < 2 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24 ∨ 27 ≤ i) :
    (multiplyResult (inverseMultiplyLayout r) d).reg (r i) = d.reg (r i) := by
  by_cases hlt : i.val < 27
  · let j : Fin 27 := ⟨i.val,hlt⟩
    have h := multiplyResult_input (inverseMultiplyLayout r) (inverseMultiplyLayout_injective r hr) d j (by
      rcases hi with hi|hi|hi|hi|hi|hi
      · left
        change i.val < 2
        change i.val < 2 at hi
        exact hi
      · subst i;exact Or.inr (Or.inl rfl)
      · subst i;exact Or.inr (Or.inr (Or.inl rfl))
      · subst i;exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · subst i;exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · change 27 ≤ i.val at hi;omega)
    simpa [inverseMultiplyLayout,j] using h
  · apply multiplyResult_outside
    intro j
    apply hr.ne
    intro h
    have hv := congrArg (fun z : Fin 31 => z.val) h
    change i.val = j.val at hv
    have := j.isLt;omega










theorem inverseBodyStore_fresh (r : Fin 31 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 31) (hi : i = 0 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24 ∨ i = 30) :
    (inverseBodyStore r d).reg (r i) = d.reg (r i) := by
  unfold inverseBodyStore
  simp only [reg_set31 r hr,show i ≠ (1:Fin 31) from by rcases hi with h|h|h|h|h|h <;> omega,ite_false]
  rw [commitStore_fresh _ _ _
    (hr.ne (show i ≠ (27:Fin 31) from by rcases hi with h|h|h|h|h|h <;> omega))
    (hr.ne (show i ≠ (28:Fin 31) from by rcases hi with h|h|h|h|h|h <;> omega))
    (hr.ne (show i ≠ (29:Fin 31) from by rcases hi with h|h|h|h|h|h <;> omega))
    (hr.ne (show i ≠ (6:Fin 31) from by rcases hi with h|h|h|h|h|h <;> omega)),
    isOneStore_fresh _ _ _ _
      (hr.ne (show i ≠ (20:Fin 31) from by rcases hi with h|h|h|h|h|h <;> omega))
      (hr.ne (show i ≠ (6:Fin 31) from by rcases hi with h|h|h|h|h|h <;> omega))]
  apply inverseMultiply_preserves r hr d i
  rcases hi with h|h|h|h|h|h <;> simp_all

theorem inverseBodyStore_index (r : Fin 31 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) :
    (inverseBodyStore r d).reg (r 1) = d.reg (r 1)+1 := by
  unfold inverseBodyStore
  simp only [TapeStore.setReg,Function.update_self]
  rw [commitStore_fresh _ _ _
    (hr.ne (show (1:Fin 31) ≠ 27 from by decide)) (hr.ne (show (1:Fin 31) ≠ 28 from by decide))
    (hr.ne (show (1:Fin 31) ≠ 29 from by decide)) (hr.ne (show (1:Fin 31) ≠ 6 from by decide)),
    isOneStore_fresh _ _ _ _ (hr.ne (by decide)) (hr.ne (by decide)),
    inverseMultiply_preserves r hr d 1 (Or.inl (by decide))]

theorem inverseBodyStore_bound (r : Fin 31 → Fin R) (hr : Function.Injective r) (M : ℕ) (hM : 1 ≤ M)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 1)+1 ≤ M) :
    ∀ j,(inverseBodyStore r d).reg j ≤ M := by
  have hb₁ : ∀ j,(multiplyResult (inverseMultiplyLayout r) d).reg j ≤ M := by
    obtain ⟨_,_,_,_,hs,hb⟩ := multiply_stops_exact (inverseMultiplyLayout r) (inverseMultiplyLayout_injective r hr) ⟨[],[],[],[]⟩ M hM d hd
    simpa only [← hs,TapeCfg.store] using hb
  have hb₂ := isOneStore_bound (r 20) (r 6) (hr.ne (by decide)) M hM _ hb₁
  have hb₃ := commitStore_bound (inverseCommitLayout r) (inverseCommitLayout_injective r hr) M hM _ hb₂
  apply setReg_bound _ _ _ M hb₃
  have he := inverseBodyStore_index r hr d
  have he' : (commitStore (inverseCommitLayout r) (isOneStore (r 20) (r 6)
    (multiplyResult (inverseMultiplyLayout r) d))).reg (r 1)+1 = d.reg (r 1)+1 := by
    simpa only [inverseBodyStore,TapeStore.setReg,Function.update_self] using he
  rw [he'];exact hc

theorem inverseBody_stops (r : Fin 31 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∃ t e,t ≤ 11000*(M+1)^6 ∧ (inverseBody r).Stops inp (d.toCfg (inverseBody (B:=B) r).entry) t e ∧
      e.store = inverseBodyStore r d := by
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := multiply_stops_exact (inverseMultiplyLayout r) (inverseMultiplyLayout_injective r hr) inp M hM d hd
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂⟩ := isOne_stops (r 20) (r 6) (hr.ne (by decide)) inp c₁.store
  have hb₂ : ∀ j,c₂.store.reg j ≤ M := by rw [hs₂];exact isOneStore_bound _ _ (hr.ne (by decide)) M hM _ hb₁
  obtain ⟨t₃,c₃,ht₃,h₃,hs₃⟩ := commit_stops (inverseCommitLayout r) (inverseCommitLayout_injective r hr) inp M c₂.store hb₂
  have h₄ := TapeMacros.increment_stops (r 1) inp c₃.store
  have hall := ((h₁.seq h₂).seq h₃).seq h₄
  refine ⟨_,_,?_,hall,?_⟩
  · have ht₂' : t₂ ≤ M+5 := ht₂.trans (Nat.add_le_add_right (hb₁ (r 6)) 5)
    have hpow := Nat.le_self_pow (by decide : (6:ℕ) ≠ 0) (M+1)
    omega
  · change c₃.store.setReg (r 1) _ = _
    rw [hs₃,hs₂,hs₁];rfl




theorem inverseLoop_stops (r : Fin 31 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (d : TapeStore R B) (hn : d.reg (r 30) = n)
    (hd : ∀ j,d.reg j ≤ M) (hc : d.reg (r 1)+n ≤ M) :
    ∃ t,t ≤ n*(11000*(M+1)^6+2)+1 ∧ (inverseLoop r).Stops inp
      (d.toCfg (TapeProgram.loopHeader 399)) t ((inverseFold r n d).toCfg (TapeProgram.loopExit 399)) ∧
      (∀ j,(inverseFold r n d).reg j ≤ M) := by
  exact singleLoop_stops (inverseBody r) (r 30) (r 1) (hr.ne (by decide)) (inverseBodyStore r) inp M _
    (fun c => inverseBodyStore_fresh r hr c 30 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
    (inverseBodyStore_index r hr) (inverseBodyStore_bound r hr M hM) (inverseBody_stops r hr inp M hM) n d hn hd hc








theorem inversePrepare_stops (r : Fin 31 → Fin R) (hr : Function.Injective r) (inp : Inputs) (d : TapeStore R B) :
    ∃ e,(inversePrepare r).Stops inp (d.toCfg (inversePrepare (B:=B) r).entry)
      (d.reg (r 27)+d.reg (r 29)+d.reg (r 1)+d.reg (r 30)+d.reg (r 28)+5*d.reg (r 23)+13) e ∧
      e.store = inversePrepareStore r d := by
  have h₁ := TapeMacros.clear_stops (r 27) inp (d.reg (r 27)) d rfl
  have h₂ := TapeMacros.clear_stops (r 29) inp (d.reg (r 29)) (d.setReg (r 27) 0) (by simp [reg_set31 r hr])
  have h₃ := TapeMacros.clear_stops (r 1) inp (d.reg (r 1)) ((d.setReg (r 27) 0).setReg (r 29) 0) (by simp [reg_set31 r hr])
  obtain ⟨c,hc,hcs⟩ := TapeMacros.copy_stops (r 23) (r 30) (r 28) (hr.ne (by decide)) (hr.ne (by decide))
    (hr.ne (by decide)) inp (((d.setReg (r 27) 0).setReg (r 29) 0).setReg (r 1) 0)
  have hall := ((h₁.seq h₂).seq h₃).seq hc
  refine ⟨c.mapPC (TapeProgram.rightLabel 6),?_,hcs⟩
  convert hall using 1 <;> first | rfl | (simp [reg_set31 r hr];omega)

theorem inversePrepareStore_reg (r : Fin 31 → Fin R) (hr : Function.Injective r) (d : TapeStore R B) (i : Fin 31) :
    (inversePrepareStore r d).reg (r i) = if i = 28 then 0 else if i = 30 then d.reg (r 23)
      else if i = 27 ∨ i = 29 ∨ i = 1 then 0 else d.reg (r i) := by
  fin_cases i <;> simp [inversePrepareStore,reg_set31 r hr]

theorem inversePrepareStore_bound (r : Fin 31 → Fin R) (hr : Function.Injective r) (M : ℕ)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) : ∀ j,(inversePrepareStore r d).reg j ≤ M := by
  unfold inversePrepareStore
  apply setReg_bound _ _ 0 M _ (by omega)
  apply setReg_bound _ _ _ M
  · exact setReg_bound _ _ 0 M (setReg_bound _ _ 0 M (setReg_bound d _ 0 M hd (by omega)) (by omega)) (by omega)
  · simpa [reg_set31 r hr] using hd (r 23)






theorem inverse_stops_exact (r : Fin 31 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) :
    ∃ t e,t ≤ 20000*(M+1)^7 ∧ (inverse r).Stops inp (d.toCfg (inverse (B:=B) r).entry) t e ∧
      e.store = inverseResult r d ∧ (∀ j,e.reg j ≤ M) := by
  obtain ⟨c,hc,hcs⟩ := inversePrepare_stops r hr inp d
  have hcb : ∀ j,c.store.reg j ≤ M := by rw [hcs];exact inversePrepareStore_bound r hr M d hd
  have hcn : c.reg (r 30) = d.reg (r 23) := by change c.store.reg (r 30) = _;rw [hcs,inversePrepareStore_reg r hr];simp
  have hcc : c.reg (r 1) = 0 := by change c.store.reg (r 1) = _;rw [hcs,inversePrepareStore_reg r hr];simp
  obtain ⟨t,ht,he,hbound⟩ := inverseLoop_stops r hr inp M hM (d.reg (r 23)) c.store hcn hcb
    (by change c.reg (r 1)+d.reg (r 23) ≤ M;rw [hcc];simpa using hd (r 23))
  have hall := hc.seq he
  refine ⟨_,_,?_,hall,?_,hbound⟩
  · have hp : d.reg (r 27)+d.reg (r 29)+d.reg (r 1)+d.reg (r 30)+d.reg (r 28)+5*d.reg (r 23)+13 ≤ 10*M+13 := by
      have := hd (r 27);have := hd (r 29);have := hd (r 1);have := hd (r 30);have := hd (r 28);have := hd (r 23);omega
    have hpow := Nat.le_self_pow (by decide : (7:ℕ) ≠ 0) (M+1)
    have hM7 : M ≤ (M+1)^7 := (by omega : M ≤ M+1).trans hpow
    have h17 : 1 ≤ (M+1)^7 := by omega
    have hm : 11000*M*(M+1)^6 ≤ 11000*(M+1)^7 := by
      calc
        11000*M*(M+1)^6 ≤ 11000*(M+1)*(M+1)^6 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega : M ≤ M+1))
        _ = 11000*(M+1)^7 := by ring
    have ht' := Nat.mul_le_mul_right (11000*(M+1)^6+2) (hd (r 23))
    have heq : M*(11000*(M+1)^6+2) = 11000*M*(M+1)^6+2*M := by ring
    rw [heq] at ht'
    change d.reg (r 27)+d.reg (r 29)+d.reg (r 1)+d.reg (r 30)+d.reg (r 28)+5*d.reg (r 23)+13+1+t ≤ _
    omega
  · change inverseFold r (d.reg (r 23)) c.store = _
    rw [hcs];rfl

theorem indexEquiv_one (ell : ℕ) (h : 0 < ell) :
    indexEquiv ell ⟨1,Nat.one_lt_two_pow (by omega)⟩ = BinaryField.one ell := by
  funext j
  rw [indexEquiv_bit]
  have hb : Nat.testBit 1 j.val = decide (0 = j.val) := by simpa using (Nat.testBit_two_pow (n:=0) (m:=j.val))
  rw [hb]
  simp [BinaryField.one,bitEquiv,eq_comm]

theorem multiplyIndex_one_iff (ell : ℕ) (h : 0 < ell) (a b : Fin (2^ell)) :
    (BinaryField.multiplyIndex ell h (selectedIndex ell h) (indexEquiv ell a) (indexEquiv ell b)).val = 1 ↔
      BinaryField.multiply ell h (selectedIndex ell h) (indexEquiv ell a) (indexEquiv ell b) = BinaryField.one ell := by
  constructor
  · intro hv
    have he : BinaryField.multiplyIndex ell h (selectedIndex ell h) (indexEquiv ell a) (indexEquiv ell b) =
        ⟨1,Nat.one_lt_two_pow (by omega)⟩ := Fin.ext hv
    rw [BinaryField.multiply,he,indexEquiv_one ell h]
  · intro he
    have hv := (indexEquiv ell).injective (he.trans (indexEquiv_one ell h).symm)
    exact congrArg Fin.val hv

theorem inverse_candidate_unique (ell : ℕ) (h : 0 < ell) (a b : Fin (2^ell))
    (hb : (BinaryField.multiplyIndex ell h (selectedIndex ell h) (indexEquiv ell a) (indexEquiv ell b)).val = 1) :
    b = BinaryField.inverseIndex ell h a := by
  have he := (multiplyIndex_one_iff ell h a b).mp hb
  have hd := congrArg (BinaryField.decode ell h) he
  rw [BinaryField.decode_multiply,BinaryField.decode_one] at hd
  apply (BinaryField.elements ell h).injective
  rw [BinaryField.elements_inverseIndex]
  change BinaryField.decode ell h (indexEquiv ell b) = (BinaryField.decode ell h (indexEquiv ell a))⁻¹
  exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hd)











theorem inverseAnswer_setReg (r : Fin 31 → Fin R) (d : TapeStore R B) (j : Fin R) (n : ℕ)
    (h27 : r 27 ≠ j) (h29 : r 29 ≠ j) : inverseAnswer r (d.setReg j n) = inverseAnswer r d := by
  simp [inverseAnswer,TapeStore.setReg,h27,h29]

theorem inverseSetup_setReg (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (d : TapeStore R B) (n : ℕ) (hs : InverseSetup r ell h a d) :
    InverseSetup r ell h a (d.setReg (r 30) n) := by simpa [InverseSetup,reg_set31 r hr] using hs

theorem inverseBodyStore_setup (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (d : TapeStore R B) (hs : InverseSetup r ell h a d) :
    InverseSetup r ell h a (inverseBodyStore r d) := by
  rcases hs with ⟨h0,h3,h19,h23,h24⟩
  exact ⟨(inverseBodyStore_fresh r hr d 0 (Or.inl rfl)).trans h0,
    (inverseBodyStore_fresh r hr d 3 (Or.inr (Or.inl rfl))).trans h3,
    (inverseBodyStore_fresh r hr d 19 (Or.inr (Or.inr (Or.inl rfl)))).trans h19,
    (inverseBodyStore_fresh r hr d 23 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans h23,
    (inverseBodyStore_fresh r hr d 24 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).trans h24⟩

theorem inverseBodyStore_answer (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (d : TapeStore R B) (hs : InverseSetup r ell h a d) (hc : d.reg (r 1) < 2^ell) :
    inverseAnswer r (inverseBodyStore r d) =
      if inverseTest ell h a (d.reg (r 1)) then some (d.reg (r 1)) else inverseAnswer r d := by
  let c₁ := multiplyResult (inverseMultiplyLayout r) d
  let c₂ := isOneStore (r 20) (r 6) c₁
  rcases hs with ⟨ha,hm,hN,hq,hQ⟩
  have hp : c₁.reg (r 20) = (BinaryField.multiplyIndex ell h (selectedIndex ell h)
      (indexEquiv ell a) (indexEquiv ell ⟨d.reg (r 1),hc⟩)).val :=
    multiplyResult_index (inverseMultiplyLayout r) (inverseMultiplyLayout_injective r hr) ell h
      (selectedIndex ell h) a ⟨d.reg (r 1),hc⟩ d ha rfl hm hN hq hQ
  have hf : c₂.reg (r 6) = if c₁.reg (r 20) = 1 then 1 else 0 :=
    isOneStore_flag _ _ (hr.ne (by decide)) c₁
  have hcan : c₂.reg (r 1) = d.reg (r 1) := by
    rw [isOneStore_fresh _ _ _ _ (hr.ne (by decide)) (hr.ne (by decide))]
    exact inverseMultiply_preserves r hr d 1 (Or.inl (by decide))
  have h27 : c₂.reg (r 27) = d.reg (r 27) := by
    rw [isOneStore_fresh _ _ _ _ (hr.ne (by decide)) (hr.ne (by decide))]
    exact inverseMultiply_preserves r hr d 27 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))
  have h29 : c₂.reg (r 29) = d.reg (r 29) := by
    rw [isOneStore_fresh _ _ _ _ (hr.ne (by decide)) (hr.ne (by decide))]
    exact inverseMultiply_preserves r hr d 29 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))
  change inverseAnswer r ((commitStore (inverseCommitLayout r) c₂).setReg (r 1) _) = _
  rw [inverseAnswer_setReg r _ _ _ (hr.ne (by decide)) (hr.ne (by decide))]
  by_cases ht : c₁.reg (r 20) = 1
  · have hf1 : c₂.reg (r 6) = 1 := by simp [hf,ht]
    have hac : inverseTest ell h a (d.reg (r 1)) = true := by simp [inverseTest,hc,← hp,ht]
    simp [inverseAnswer,commitStore,commitBodyStore,inverseCommitLayout,reg_set31 r hr,hf1,hcan,hac]
  · have hf0 : c₂.reg (r 6) = 0 := by simp [hf,ht]
    have hac : inverseTest ell h a (d.reg (r 1)) = false := by simp [inverseTest,hc,← hp,ht]
    simp [inverseAnswer,commitStore,inverseCommitLayout,hf0,hac,h27,h29]

theorem inverseFold_answer (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (n : ℕ) (d : TapeStore R B) (hs : InverseSetup r ell h a d)
    (hc : d.reg (r 1)+n ≤ 2^ell) :
    inverseAnswer r (inverseFold r n d) =
      scanRect (fun c _ => inverseTest ell h a c) 1 n (d.reg (r 1)) (inverseAnswer r d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    let c := d.setReg (r 30) n
    have hsetup := inverseSetup_setReg r hr ell h a d n hs
    have hc1 : c.reg (r 1) = d.reg (r 1) := by simp [c,reg_set31 r hr]
    have hcan : c.reg (r 1) < 2^ell := by omega
    have ha : inverseAnswer r c = inverseAnswer r d := inverseAnswer_setReg r d _ n (hr.ne (by decide)) (hr.ne (by decide))
    change inverseAnswer r (inverseFold r n (inverseBodyStore r c)) = _
    rw [ih (inverseBodyStore r c) (inverseBodyStore_setup r hr ell h a c hsetup)
      (by rw [inverseBodyStore_index r hr c,hc1];omega),inverseBodyStore_index r hr c,hc1,
      inverseBodyStore_answer r hr ell h a c hsetup hcan,hc1,ha]
    rfl

theorem inverseResult_answer (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (d : TapeStore R B) (hs : InverseSetup r ell h a d) :
    inverseAnswer r (inverseResult r d) = scanRect (fun c _ => inverseTest ell h a c) 1 (2^ell) 0 none := by
  have hp : InverseSetup r ell h a (inversePrepareStore r d) := by
    simpa [InverseSetup,inversePrepareStore_reg r hr] using hs
  rw [inverseResult,hs.2.2.2.1,inverseFold_answer r hr ell h a _ _ hp
    (by simp [inversePrepareStore_reg r hr])]
  simp [inversePrepareStore_reg r hr,inverseAnswer]

theorem indexEquiv_zero (ell : ℕ) : indexEquiv ell ⟨0,Nat.two_pow_pos ell⟩ = BinaryField.zero ell := by
  funext j
  rw [indexEquiv_bit]
  simp [BinaryField.zero,bitEquiv]

theorem inverseResult_index_nonzero (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (d : TapeStore R B) (hs : InverseSetup r ell h a d) (ha0 : a.val ≠ 0) :
    (inverseResult r d).reg (r 27) = (BinaryField.inverseIndex ell h a).val := by
  let test := fun c (_ : ℕ) => inverseTest ell h a c
  let target := (BinaryField.inverseIndex ell h a).val
  have hg : ∀ i < 2^ell,∀ s < 1,test i s = true → i = target := by
    intro i hi s hs ht
    have hp : (BinaryField.multiplyIndex ell h (selectedIndex ell h) (indexEquiv ell a) (indexEquiv ell ⟨i,hi⟩)).val = 1 := by
      simpa [test,inverseTest,hi] using ht
    exact congrArg Fin.val (inverse_candidate_unique ell h a ⟨i,hi⟩ hp)
  have hx : indexEquiv ell a ≠ BinaryField.zero ell := by
    intro hz
    have he := (indexEquiv ell).injective (hz.trans (indexEquiv_zero ell).symm)
    exact ha0 (congrArg Fin.val he)
  obtain ⟨i,hi⟩ := BinaryField.exists_inverseIndex ell h (indexEquiv ell a) hx
  have hp := (multiplyIndex_one_iff ell h a i).mpr hi
  have hit : ∃ i < 2^ell,∃ s < 1,test i s = true :=
    ⟨i.val,i.isLt,0,by omega,by simp [test,inverseTest,i.isLt,hp]⟩
  have han : inverseAnswer r (inverseResult r d) = some target := by
    rw [inverseResult_answer r hr ell h a d hs]
    exact scanRect_complete test _ _ target hg hit
  unfold inverseAnswer at han
  split at han
  · contradiction
  · exact Option.some.inj han

theorem inverseBodyStore_tapeData (r : Fin 31 → Fin R) (d : TapeStore R B) :
    tapeData (inverseBodyStore r d) = tapeData d := by
  rw [inverseBodyStore,tapeData_setReg,commitStore_tapeData,isOneStore_tapeData,multiplyResult_tapeData]

theorem inverseResult_tapeData (r : Fin 31 → Fin R) (d : TapeStore R B) :
    tapeData (inverseResult r d) = tapeData d := by
  rw [inverseResult,inverseFold,loopResult_tapeData (r 30) (inverseBodyStore r) (inverseBodyStore_tapeData r)]
  rfl

theorem inverseResult_input (r : Fin 31 → Fin R) (hr : Function.Injective r) (d : TapeStore R B)
    (i : Fin 31) (hi : i = 0 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24) :
    (inverseResult r d).reg (r i) = d.reg (r i) := by
  rw [inverseResult,inverseFold,loopResult_frame (r 30) (inverseBodyStore r) (r i)
    (hr.ne (show i ≠ (30:Fin 31) from by rcases hi with h|h|h|h|h <;> omega))
    (fun c => inverseBodyStore_fresh r hr c i (by rcases hi with h|h|h|h|h <;> simp_all)),
    inversePrepareStore_reg r hr]
  have h28 : i ≠ (28:Fin 31) := by rcases hi with h|h|h|h|h <;> omega
  have h30 : i ≠ (30:Fin 31) := by rcases hi with h|h|h|h|h <;> omega
  have h27 : i ≠ (27:Fin 31) := by rcases hi with h|h|h|h|h <;> omega
  have h29 : i ≠ (29:Fin 31) := by rcases hi with h|h|h|h|h <;> omega
  have h1 : i ≠ (1:Fin 31) := by rcases hi with h|h|h|h|h <;> omega
  simp [h28,h30,h27,h29,h1]

theorem inverseBodyStore_outside (r : Fin 31 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 31,j ≠ r i) : (inverseBodyStore r d).reg j = d.reg j := by
  unfold inverseBodyStore
  simp only [TapeStore.setReg,Function.update_of_ne (hne 1)]
  rw [commitStore_fresh _ _ _ (hne 27) (hne 28) (hne 29) (hne 6),
    isOneStore_fresh _ _ _ _ (hne 20) (hne 6)]
  apply multiplyResult_outside
  intro i
  exact hne ⟨i.val,by have := i.isLt;omega⟩

theorem inverseResult_outside (r : Fin 31 → Fin R) (d : TapeStore R B)
    (j : Fin R) (hne : ∀ i : Fin 31,j ≠ r i) : (inverseResult r d).reg j = d.reg j := by
  rw [inverseResult,inverseFold,loopResult_frame (r 30) (inverseBodyStore r) j (hne 30)
    (fun c => inverseBodyStore_outside r c j hne)]
  simp [inversePrepareStore,TapeStore.setReg,hne 1,hne 27,hne 28,hne 29,hne 30]






















theorem inverseIndex_zero (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell)) (ha0 : a.val = 0) :
    (BinaryField.inverseIndex ell h a).val = 0 := by
  have ha : a = ⟨0,Nat.two_pow_pos ell⟩ := Fin.ext ha0
  rw [ha,BinaryField.inverseIndex,indexEquiv_zero]
  unfold BinaryField.inverse
  rw [dif_pos rfl,← indexEquiv_zero ell,Equiv.symm_apply_apply]

theorem inverseTest_zero (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell)) (ha0 : a.val = 0) (b : ℕ) :
    inverseTest ell h a b = false := by
  unfold inverseTest
  split
  · rename_i hb
    apply decide_eq_false
    intro hp
    have he := (multiplyIndex_one_iff ell h a ⟨b,hb⟩).mp hp
    have hd := congrArg (BinaryField.decode ell h) he
    rw [BinaryField.decode_multiply,BinaryField.decode_one] at hd
    have ha : a = ⟨0,Nat.two_pow_pos ell⟩ := Fin.ext ha0
    rw [ha,indexEquiv_zero,BinaryField.decode_zero,zero_mul] at hd
    exact zero_ne_one hd
  · rfl

theorem inverseBodyStore_output_zero (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (d : TapeStore R B) (hs : InverseSetup r ell h a d) (hc : d.reg (r 1) < 2^ell)
    (ha0 : a.val = 0) : (inverseBodyStore r d).reg (r 27) = d.reg (r 27) := by
  let c₁ := multiplyResult (inverseMultiplyLayout r) d
  let c₂ := isOneStore (r 20) (r 6) c₁
  rcases hs with ⟨ha,hm,hN,hq,hQ⟩
  have hp : c₁.reg (r 20) = (BinaryField.multiplyIndex ell h (selectedIndex ell h)
      (indexEquiv ell a) (indexEquiv ell ⟨d.reg (r 1),hc⟩)).val :=
    multiplyResult_index (inverseMultiplyLayout r) (inverseMultiplyLayout_injective r hr) ell h
      (selectedIndex ell h) a ⟨d.reg (r 1),hc⟩ d ha rfl hm hN hq hQ
  have hn : c₁.reg (r 20) ≠ 1 := by
    intro hh
    have ht : inverseTest ell h a (d.reg (r 1)) = true := by simp [inverseTest,hc,← hp,hh]
    rw [inverseTest_zero ell h a ha0] at ht
    contradiction
  have hf : c₂.reg (r 6) = 0 := by rw [isOneStore_flag _ _ (hr.ne (by decide))];simp [hn]
  change ((commitStore (inverseCommitLayout r) c₂).setReg (r 1) _).reg (r 27) = _
  simp only [reg_set31 r hr,show (27:Fin 31) ≠ 1 from by decide,ite_false]
  simp only [commitStore,show inverseCommitLayout r 4 = r 6 from rfl,hf,if_pos rfl,ite_true]
  rw [isOneStore_fresh _ _ _ _ (hr.ne (by decide)) (hr.ne (by decide))]
  exact inverseMultiply_preserves r hr d 27 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))

theorem inverseFold_output_zero (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (n : ℕ) (d : TapeStore R B) (hs : InverseSetup r ell h a d)
    (hc : d.reg (r 1)+n ≤ 2^ell) (ha0 : a.val = 0) :
    (inverseFold r n d).reg (r 27) = d.reg (r 27) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    let c := d.setReg (r 30) n
    have hsetup := inverseSetup_setReg r hr ell h a d n hs
    have hc1 : c.reg (r 1) = d.reg (r 1) := by simp [c,reg_set31 r hr]
    change (inverseFold r n (inverseBodyStore r c)).reg (r 27) = _
    rw [ih (inverseBodyStore r c) (inverseBodyStore_setup r hr ell h a c hsetup)
      (by rw [inverseBodyStore_index r hr c,hc1];omega),
      inverseBodyStore_output_zero r hr ell h a c hsetup (by omega) ha0]
    simp [c,reg_set31 r hr]

theorem inverseResult_index (r : Fin 31 → Fin R) (hr : Function.Injective r) (ell : ℕ) (h : 0 < ell)
    (a : Fin (2^ell)) (d : TapeStore R B) (hs : InverseSetup r ell h a d) :
    (inverseResult r d).reg (r 27) = (BinaryField.inverseIndex ell h a).val := by
  by_cases ha0 : a.val = 0
  · have hp : InverseSetup r ell h a (inversePrepareStore r d) := by
      simpa [InverseSetup,inversePrepareStore_reg r hr] using hs
    rw [inverseIndex_zero ell h a ha0,inverseResult,hs.2.2.2.1,
      inverseFold_output_zero r hr ell h a _ _ hp (by simp [inversePrepareStore_reg r hr]) ha0,
      inversePrepareStore_reg r hr]
    simp
  · exact inverseResult_index_nonzero r hr ell h a d hs ha0

/-- Total physical-source inverse, including the canonical zero-to-zero case. -/
theorem inverse_stops (r : Fin 31 → Fin R) (hr : Function.Injective r) (inp : Inputs)
    (ell : ℕ) (h : 0 < ell) (a : Fin (2^ell)) (M : ℕ) (hM : 1 ≤ M)
    (d : TapeStore R B) (hd : ∀ j,d.reg j ≤ M) (hs : InverseSetup r ell h a d) :
    ∃ t e,t ≤ 20000*(M+1)^7 ∧ (inverse r).Stops inp (d.toCfg (inverse (B:=B) r).entry) t e ∧
      e.store = inverseResult r d ∧ e.reg (r 27) = (BinaryField.inverseIndex ell h a).val ∧
      (∀ i,i = 0 ∨ i = 3 ∨ i = 19 ∨ i = 23 ∨ i = 24 → e.reg (r i) = d.reg (r i)) ∧
      (∀ j,(∀ i,j ≠ r i) → e.reg j = d.reg j) ∧ (∀ j,e.reg j ≤ M) ∧ tapeData e.store = tapeData d := by
  obtain ⟨t,e,ht,he,hes,hbound⟩ := inverse_stops_exact r hr inp M hM d hd
  refine ⟨t,e,ht,he,hes,?_,?_,?_,hbound,?_⟩
  · change e.store.reg (r 27) = _
    rw [hes];exact inverseResult_index r hr ell h a d hs
  · intro i hi
    change e.store.reg (r i) = _
    rw [hes];exact inverseResult_input r hr d i hi
  · intro j hj
    change e.store.reg j = _
    rw [hes];exact inverseResult_outside r d j hj
  · rw [hes];exact inverseResult_tapeData r d

















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



















































































































































































































































theorem scaleStore_bound_exact (src dst tmp : Fin R) (c M : ℕ) (s : TapeStore R B)
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


















theorem fullTestTable_rank {d n : ℕ} (g : Geometry d n) [DecidableEq g.F]
    (y : Word (rowCount d n)) :
    (Computation.Gaussian.run (fullTestTable g y)).1 = (testMatrix g y).rank := by
  rw [Computation.Gaussian.run_correct]
  unfold fullTestTable
  rw [Computation.Gaussian.toMatrix_ofMatrix, Matrix.rank_submatrix, fullTestMatrix_rank]











/-- Cross multiplication replaces the real-valued rank threshold by a natural
integer comparison. Only the fixed rational parameter supplies constants. -/
theorem rational_rank_threshold_iff (η : ℚ) (hη : 0 ≤ η) (r m : ℕ) :
    (r : ℝ) ≤ (η : ℝ) * m ↔ r * η.den ≤ η.num.toNat * m := by
  have hn : 0 ≤ η.num := Rat.num_nonneg.mpr hη
  have hden : (0 : ℝ) < η.den := by exact_mod_cast η.den_pos
  have hnum : (η.num.toNat : ℝ) = η.num := by exact_mod_cast Int.toNat_of_nonneg hn
  rw [Rat.cast_def, ← hnum, div_mul_eq_mul_div, le_div_iff₀ hden]
  norm_cast









theorem rationalRankTest_eq (θ : ℚ) (hθ : θ ≤ 1) {d n : ℕ}
    (g : Geometry d n) [DecidableEq g.F] (y : Word (rowCount d n)) :
    rationalRankTest θ g y = rankTest (θ : ℝ) g y := by
  classical
  let η : ℚ := 1/2 - θ/2
  have hη : 0 ≤ η := by dsimp [η]; linarith
  have hcast : (η : ℝ) = 1/2 - (θ : ℝ)/2 := by
    norm_num [η, Rat.cast_sub, Rat.cast_div]
  apply Bool.eq_iff_iff.mpr
  simp only [rationalRankTest, rankTest, decide_eq_true_eq, fullTestTable_rank]
  exact (rational_rank_threshold_iff η hη _ _).symm.trans (by rw [hcast])





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
























theorem binaryRankTest_eq (θ : ℚ) (hθ : θ ≤ 1) (d n : ℕ)
    (y : Word (rowCount d n)) :
    binaryRankTest θ d n y = rankTest (θ : ℝ) (binaryGeometry d n) y := by
  classical
  rw [← rationalRankTest_eq θ hθ]
  simp only [binaryRankTest, rationalRankTest, binaryTestTable_rank, fullTestTable_rank]





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






























































theorem zeroIndex_value (ell : ℕ) : (BinaryField.zeroIndex ell).val=0 := by
  rw [BinaryField.zeroIndex,BinaryPolynomial.indexEquiv_inverse_value]
  simp [BinaryField.zero]























































































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

/-! Inlined whole module: ExpandingCodes.Computation.TesterPowers -/
section FlattenModule62


set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterPowers
open NKtLB SamplerEvaluation SamplerProgram
open ExpandingCodes.PolynomialStretch BinaryPolynomial
open FieldPrograms UnaryArithmetic
variable {R B : ℕ}




theorem scalar_injective (r : Fin 33 → Fin R) (hr : Function.Injective r) :
    Function.Injective (scalar r) := by
  intro i j hij
  have hh := congrArg (Fin.val : Fin 33 → ℕ) (hr hij)
  exact Fin.ext hh

theorem count_outside (r : Fin 33 → Fin R) (hr : Function.Injective r) :
    ∀ i : Fin 32,r 32≠scalar r i := by
  intro i heq
  have hh := congrArg Fin.val (hr heq)
  have hi := i.isLt
  simp only [scalar,Fin.val_mk] at hh
  omega






theorem powerLoop_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
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







theorem power_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
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










theorem factor_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
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


















theorem productValue_eq (ell : ℕ) (h : 0<ell) (values : Fin R → Fin (2^ell))
    (exponents : Fin R → ℕ) (ps : List (Fin R × Fin R)) :
    productValue ell h values exponents ps=(EncodedTester.product (BinaryField.indexOperations ell h)
      (ps.map fun p => EncodedTester.power (BinaryField.indexOperations ell h) (values p.2) (exponents p.1))).1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [productValue,List.map_cons,EncodedTester.product,ih]

theorem productCore_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
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







theorem product_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
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











theorem sumCore_stops (dst tmp : Fin R) (hdt : dst≠tmp) (ps : List (Fin R))
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





theorem sumDigits_stops (dst tmp : Fin R) (hdt : dst≠tmp) (ps : List (Fin R))
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





theorem comparison_injective (r : Fin 33 → Fin R) (hr : Function.Injective r)
    (c : Fin 4 → Fin R) (hc : Function.Injective c) (hcr : ∀ i j,c i≠r j) :
    Function.Injective (comparison r c) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [comparison,hr.eq_iff,hc.eq_iff,hcr,Ne.symm]









/-- Exact frame of the preserving comparison, convenient for composing a field
workspace without unfolding the scalar comparison's internal source. -/
theorem lessThanStore_frame (r : Fin 6 → Fin R) (s : TapeStore R B) (j : Fin R)
    (hj : j≠r 2 ∧ j≠r 3 ∧ j≠r 4 ∧ j≠r 5) :
    (ParameterPrograms.lessThanStore r s).reg j=s.reg j := by
  simp [ParameterPrograms.lessThanStore,ParameterPrograms.lessCore,ParameterPrograms.lessPrepare,
    ParameterPrograms.ltLoopStore,TapeStore.setReg,hj]












theorem evaluate_stops (r : Fin 33 → Fin R) (hr : Function.Injective r)
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


theorem value_canonical {d : ℕ} (ell : ℕ) (h : 0<ell) (degree : ℕ)
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
theorem evaluate_canonical_stops {d : ℕ} (r : Fin 33 → Fin R) (hr : Function.Injective r)
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






/-- Frozen integer-floor cutoff agrees with its nonnegative unary formula
for the construction parameter range. -/
theorem auxiliaryDegree_nat (q d : ℕ) (hd : 4 ≤ d) (hq : 2 ≤ q) :
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


















theorem degree_stops (r : Fin 5 → Fin R) (hr : Function.Injective r) (d : ℕ)
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




theorem bit_le_one (inp : Inputs) (p : ℕ) : bit inp p ≤ 1 := by unfold bit; split <;> omega










theorem readBit_stops (a : Fin R) (inp : Inputs) (s : TapeStore R B) :
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













theorem blockStore_reg (r : Fin 4 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (s : TapeStore R B) :
    (blockStore r b inp s).reg=(((s.setReg (r 1) 0).setReg (r 2) 0).setReg (r 3) 0).reg := by
  rw [blockStore,TapeArrays.writeBlockStore_reg]
  funext j
  simp only [blockPrepare,readBitStore,TapeStore.setReg]
  by_cases h₁ : j=r 1 <;> by_cases h₂ : j=r 2 <;> by_cases h₃ : j=r 3 <;>
    simp_all [Function.update,hr.eq_iff]




theorem blockStore_written (r : Fin 4 → Fin R) (hr : Function.Injective r)
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

theorem block_stops (r : Fin 4 → Fin R) (hr : Function.Injective r)
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




theorem loadLayout_injective (r : Fin 5 → Fin R) (hr : Function.Injective r) :
    Function.Injective (loadLayout r) := by
  intro i j hij
  have hh := congrArg (Fin.val : Fin 5 → ℕ) (hr hij)
  exact Fin.ext hh







theorem load_counter (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (s : TapeStore R B) :
    (blockStore (loadLayout r) b inp s).reg (r 4)=s.reg (r 4) := by
  rw [blockStore_reg _ (loadLayout_injective r hr)]
  simp [loadLayout,reg_layout r hr]














theorem load_stops (r : Fin 5 → Fin R) (hr : Function.Injective r)
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




theorem loadStore_register_frame (r : Fin 5 → Fin R) (hr : Function.Injective r)
    (b : Fin B) (inp : Inputs) (n : ℕ) (s : TapeStore R B)
    (j : Fin R) (hj : j≠r 1 ∧ j≠r 2 ∧ j≠r 3 ∧ j≠r 4) :
    (loadStore r b inp n s).reg j=s.reg j := by
  apply SourceFieldArithmetic.loopResult_frame _ _ j hj.2.2.2
  intro d
  rw [blockStore_reg _ (loadLayout_injective r hr)]
  simp [loadLayout,TapeStore.setReg,hj]






theorem loadStore_output (r : Fin 5 → Fin R) (b : Fin B) (inp : Inputs)
    (n : ℕ) (s : TapeStore R B) : (loadStore r b inp n s).output=s.output := by
  unfold loadStore
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [SourceFieldArithmetic.loopResult,ih]
    simp [blockStore,TapeArrays.writeBlockStore_output,blockPrepare,readBitStore,TapeStore.setReg]











theorem loadStore_bufferHead_frame (r : Fin 5 → Fin R) (b c : Fin B) (hcb : c≠b) (inp : Inputs)
    (n : ℕ) (s : TapeStore R B) : (loadStore r b inp n s).bufferHead c=s.bufferHead c := by
  unfold loadStore
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [SourceFieldArithmetic.loopResult,ih]
    simp [blockStore,TapeArrays.writeBlockStore,TapeArrays.fillStore_head,blockPrepare,readBitStore,TapeStore.setReg,hcb]

theorem loadStore_bufferSymbol_frame (r : Fin 5 → Fin R) (b c : Fin B) (hcb : c≠b) (inp : Inputs)
    (n : ℕ) (s : TapeStore R B) (k : ℕ) :
    ((loadStore r b inp n s).bufferTape c).getD k .blank=(s.bufferTape c).getD k .blank := by
  unfold loadStore
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [SourceFieldArithmetic.loopResult,ih]
    simp only [blockStore,TapeArrays.writeBlockStore,TapeArrays.fillStore_symbol,hcb,false_and,if_false,blockPrepare,readBitStore,TapeStore.setReg]

/-- Exact current-cell symbols after an arbitrary prefix, including sizeInput. -/
theorem input_symbols (inp : Inputs) (pre : List Bool) {N : ℕ} (y : Fin N → Bool)
    (hi : inp.input=pre++List.ofFn y) (j : Fin N) :
    Machine.readRO inp.input (pre.length+j.val)=if y j then .one else .zero := by
  unfold Machine.readRO
  rw [hi,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,List.getElem?_ofFn]
  simp only [j.isLt,dite_true]
  cases y j <;> rfl

theorem word_symbols (inp : Inputs) (n N : ℕ) (y : ExpandingCodes.PolynomialStretch.Word N)
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














































































































/-- Source assembly and exact storage/time correctness of `program` are separate:
no correctness axiom, theorem hole or runtime field/array instruction is present
in this concrete finite source table. -/
theorem scalar_injective (d : ℕ) : Function.Injective (scalar d) := by
  intro i j hij
  exact Fin.ext (congrArg (Fin.val : Registers d → ℕ) hij)



@[simp] theorem low_eq_iff (d : ℕ) (i j : Fin 80) : low d i=low d j ↔ i=j := by
  constructor
  · intro hij
    exact Fin.ext (congrArg (Fin.val : Registers d → ℕ) hij)
  · exact congrArg (low d)

theorem low_outside_scalar (d : ℕ) (i : Fin 80) (hi : 33 ≤ i.val) :
    ∀ j,low d i≠scalar d j := by
  intro j hij
  have hh := congrArg (Fin.val : Registers d → ℕ) hij
  have hj := j.isLt
  simp only [low,scalar,Fin.val_mk] at hh
  omega

theorem digit_ne_low (d : ℕ) (group : Fin 6) (i : Fin d) (j : Fin 80) :
    digit d group i≠low d j := by
  intro hij
  have hh := congrArg (Fin.val : Registers d → ℕ) hij
  have hj := j.isLt
  simp only [digit,low,Fin.val_mk] at hh
  omega

theorem digit_outside_scalar (d : ℕ) (group : Fin 6) (i : Fin d) :
    ∀ j,digit d group i≠scalar d j :=
  fun j => digit_ne_low d group i ⟨j.val,by omega⟩

theorem caller_injective (d : ℕ) : Function.Injective (evaluationCaller d) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [evaluationCaller]

theorem caller_outside_scalar (d : ℕ) : ∀ i j,evaluationCaller d i≠scalar d j := by
  intro i j hij
  have hh := congrArg (Fin.val : Registers d → ℕ) hij
  have hj := j.isLt
  fin_cases i <;> simp [evaluationCaller,scalar,low] at hh <;> omega

theorem digit_outside_caller (d : ℕ) (group : Fin 6) (i : Fin d) :
    ∀ j,digit d group i≠evaluationCaller d j := by
  intro j
  fin_cases j <;> exact digit_ne_low d group i _

/-- The eager Gram leaf performs two actual canonical monomials, saves the first
value, and uses the checked source field multiply/add to accumulate their product.
All point/exponent counters and every caller register above69 are preserved. -/
theorem maskedTerm_stops (d ell : ℕ) (h : 0<ell)
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

/-! Inlined whole module: ExpandingCodes.Computation.TapeRename -/
section FlattenModule78


set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace TapeInstr
variable {R B S C L : ℕ}













theorem renameStorage_eq_halt (ρ : Fin R → Fin S) (σ : Fin B → Fin C) (i : TapeInstr R B L) :
    i.renameStorage ρ σ = .halt ↔ i = .halt := by cases i <;> simp [renameStorage]
end TapeInstr

namespace TapeCfg
variable {R B S C L : ℕ}



end TapeCfg

namespace TapeStore
variable {R B S C L : ℕ}







end TapeStore

namespace TapeProgram
variable {R B S C L : ℕ}




theorem halted_renameStorage (ρ : Fin R → Fin S) (σ : Fin B → Fin C)
    (P : TapeProgram R B L) (c : TapeCfg S C L) :
    (P.renameStorage ρ σ).halted c ↔ P.halted (c.projectStorage ρ σ) := by
  exact TapeInstr.renameStorage_eq_halt ρ σ (P.code c.pc)

theorem step_projectStorage (ρ : Fin R → Fin S) (σ : Fin B → Fin C)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (P : TapeProgram R B L) (inp : Inputs) (c : TapeCfg S C L) :
    ((P.renameStorage ρ σ).step inp c).projectStorage ρ σ =
      P.step inp (c.projectStorage ρ σ) := by
  have hr (i : Fin R) (v : ℕ) := Function.update_comp_eq_of_injective c.reg hρ i v
  have ht (b : Fin B) (v : List Sym) := Function.update_comp_eq_of_injective c.bufferTape hσ b v
  have hh (b : Fin B) (v : ℕ) := Function.update_comp_eq_of_injective c.bufferHead hσ b v
  cases hc : P.code c.pc <;>
    simp only [step,renameStorage,TapeCfg.projectStorage,TapeInstr.renameStorage,hc]
  all_goals try rfl
  all_goals try (simp only [hr,ht,hh]; rfl)
  split <;> simp_all only [hr,ht,hh,Function.comp_apply,ite_true,ite_false]

/-- Every active small-program trace lifts to the larger fixed storage frame
with exactly the same number of source steps. -/
theorem Exec.liftStorage {P : TapeProgram R B L} {inp : Inputs}
    {c d : TapeCfg R B L} {t : ℕ} (h : P.Exec inp c t d)
    (ρ : Fin R → Fin S) (σ : Fin B → Fin C)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (big : TapeCfg S C L) (hc : big.projectStorage ρ σ = c) :
    ∃ final, (P.renameStorage ρ σ).Exec inp big t final ∧ final.projectStorage ρ σ = d := by
  induction h generalizing big with
  | refl c => exact ⟨big,Exec.refl _,hc⟩
  | @step c d e t active next tail ih =>
    have hd : ((P.renameStorage ρ σ).step inp big).projectStorage ρ σ = d := by
      rw [step_projectStorage ρ σ hρ hσ,hc,next]
    obtain ⟨final,hfinal,hproj⟩ := ih ((P.renameStorage ρ σ).step inp big) hd
    refine ⟨final,Exec.step ?_ rfl hfinal,hproj⟩
    intro hh
    have hp := (halted_renameStorage ρ σ P big).mp hh
    exact active (by simpa only [hc] using hp)

theorem Stops.liftStorage {P : TapeProgram R B L} {inp : Inputs}
    {c d : TapeCfg R B L} {t : ℕ} (h : P.Stops inp c t d)
    (ρ : Fin R → Fin S) (σ : Fin B → Fin C)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (big : TapeCfg S C L) (hc : big.projectStorage ρ σ = c) :
    ∃ final, (P.renameStorage ρ σ).Stops inp big t final ∧
      final.projectStorage ρ σ = d ∧ final.output = d.output := by
  obtain ⟨final,he,hproj⟩ := h.exec.liftStorage ρ σ hρ hσ big hc
  refine ⟨final,⟨he,?_⟩,hproj,congrArg TapeCfg.output hproj⟩
  apply (halted_renameStorage ρ σ P final).mpr
  simpa only [hproj] using h.halted





























































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

theorem digit_injective (d : ℕ) {g h : Fin 6} {i j : Fin d}
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

theorem tuple_used (d : ℕ) (g : Fin 3) (j : Registers d) :
    j∈SamplerOdometer.used (tuple d g) ↔
      ∃ i : Fin d,j=digit d ⟨2*g.val,by omega⟩ i ∨ j=digit d ⟨2*g.val+1,by omega⟩ i := by
  rw [SamplerOdometer.used_mem_iff]
  simp only [tuple,List.mem_ofFn]
  constructor
  · rintro ⟨p,⟨i,rfl⟩,hi⟩
    exact ⟨i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨_,⟨i,rfl⟩,hi⟩

theorem low_not_tuple (d : ℕ) (g : Fin 3) (j : Fin 80) :
    low d j∉SamplerOdometer.used (tuple d g) := by
  rw [tuple_used]
  rintro ⟨i,he|he⟩ <;> exact digit_ne_low d _ i j he.symm

theorem tuple_nodup (d : ℕ) (g : Fin 3) :
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

theorem tuple_unique (d : ℕ) (g : Fin 3) :
    (low d 23::low d 2::SamplerOdometer.used (tuple d g)).Nodup := by
  simp only [List.nodup_cons,List.mem_cons,not_or]
  exact ⟨⟨by simp,low_not_tuple d g 23⟩,low_not_tuple d g 2,tuple_nodup d g⟩





theorem numbered_digits (d : ℕ) (g : Fin 3) (q k : ℕ) (hq : 1<q)
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

theorem numbered_next (d : ℕ) (g : Fin 3) (q k : ℕ) (hq : 1<q)
    (s : TapeStore (80+6*d) 3) (hn : Numbered d g q k s) :
    Numbered d g q (k+1) (SamplerOdometer.nextStore (low d 23) (low d 2) (tuple d g) s) := by
  have hu := tuple_unique d g
  refine ⟨?_,SamplerOdometer.program_valid _ _ _ hu s hn.2.1,?_⟩
  · rw [SamplerOdometer.nextStore_fresh _ _ _ _ _ (by simp) (low_not_tuple d g 23)]
    exact hn.1
  · have hh := SamplerOdometer.program_number _ _ _ hu s hn.2.1 (by rw [hn.1]; exact hq)
    rw [hn.1,hn.2.2] at hh
    simpa [tuple,SamplerOdometer.readings,Nat.mod_add_mod] using hh

theorem numbered_initialize (d : ℕ) (g : Fin 3) (q : ℕ) (hq : 1<q)
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

theorem Numbered.frame {d : ℕ} {g : Fin 3} {q k : ℕ}
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

theorem tuple_other (d : ℕ) (g h : Fin 3) (hgh : g≠h) (j : Registers d)
    (hj : j∈SamplerOdometer.used (tuple d g)) : j∉SamplerOdometer.used (tuple d h) := by
  rw [tuple_used] at hj ⊢
  obtain ⟨i,rfl|rfl⟩ := hj
  all_goals rintro ⟨k,hk|hk⟩
  all_goals have hh := congrArg Fin.val (digit_injective d hk).1
  all_goals apply hgh; apply Fin.ext; simp only [Fin.val_mk] at hh; omega

theorem numbered_next_other (d : ℕ) (g h : Fin 3) (hgh : g≠h) (q k : ℕ)
    (s : TapeStore (80+6*d) 3) (hn : Numbered d g q k s) :
    Numbered d g q k (SamplerOdometer.nextStore (low d 23) (low d 2) (tuple d h) s) := by
  apply hn.frame
  · exact SamplerOdometer.nextStore_fresh _ _ _ _ _ (by simp) (low_not_tuple d h 23)
  · intro j hj
    apply SamplerOdometer.nextStore_fresh
    · obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj
      all_goals exact digit_ne_low d _ i 2
    · exact tuple_other d g h hgh j hj

theorem inputLookup_injective (d : ℕ) : Function.Injective (inputLookup d) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [inputLookup]

theorem inputLookup_outside (d : ℕ) (j : Fin 80)
    (hj : j≠0 ∧ j≠1 ∧ j≠2 ∧ j≠4 ∧ j≠5 ∧ j≠23 ∧ j≠73 ∧ j≠78) :
    ∀ i,low d j ≠ inputLookup d i := by
  intro i
  fin_cases i <;> simp_all [inputLookup]

theorem tapeData_payload {R B : ℕ} {s e : TapeStore R B}
    (h : FieldConvolution.tapeData e=FieldConvolution.tapeData s) : TapeStore.SamePayload e s := by
  have hr := congrArg Prod.fst h
  have ho := congrArg (fun x => x.2.1) h
  have ht := congrArg (fun x => x.2.2.1) h
  exact ⟨hr,ho,fun c k => congrArg (fun t => (t c).getD k .blank) ht⟩

theorem tapeData_head {R B : ℕ} {s e : TapeStore R B}
    (h : FieldConvolution.tapeData e=FieldConvolution.tapeData s) : e.bufferHead=s.bufferHead :=
  congrArg (fun x => x.2.2.2) h























theorem pointBody_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
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









@[simp] theorem pointPrefix_zero (d ell : ℕ) (h : 0<ell) (D : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) :
    pointPrefix d ell h D y a b 0=BinaryField.zeroIndex ell := rfl

theorem pointPrefix_step (d ell : ℕ) (h : 0<ell) (D : ℕ)
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

@[simp] theorem pointPrefix_full (d ell : ℕ) (h : 0<ell) (D : ℕ)
    (y : Fin ((2^ell)^d) → Bool) (a b : Fin ((2^ell)^d)) :
    pointPrefix d ell h D y a b ((2^ell)^d)=
      (EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1 := by
  unfold pointPrefix EncodedTester.entry
  rw [List.take_of_length_le (by simp)]

theorem Core.setReg {d ell : ℕ} {h : 0<ell} {D M : ℕ}
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

theorem Numbered.setReg {d : ℕ} {g : Fin 3} {q k : ℕ}
    {s : TapeStore (80+6*d) 3} (hn : Numbered d g q k s)
    (i : Fin 80) (hi : i≠23) (v : ℕ) : Numbered d g q k (s.setReg (low d i) v) := by
  apply hn.frame
  · simp [TapeStore.setReg,((low_eq_iff d 23 i).not.mpr (Ne.symm hi))]
  · intro j hj
    obtain ⟨k,rfl|rfl⟩ := (tuple_used d g j).mp hj
    all_goals simp [TapeStore.setReg,Function.update_of_ne (digit_ne_low d _ k i)]

/-- The semantic loop rule consumes the actual checked body's preserved countdown. -/
theorem loop_stops {R B L : ℕ} (P : TapeProgram R B L) (r : Fin R)
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















theorem pointLoop_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
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



theorem Core.frame {d ell : ℕ} {h : 0<ell} {D M : ℕ}
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

theorem initialize_payload {R B : ℕ} (q tmp : Fin R) (ps : List (SamplerOdometer.Digit R))
    (s : TapeStore R B) :
    FieldConvolution.tapeData (SamplerOdometer.initializeStore q tmp ps s)=FieldConvolution.tapeData s := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    rw [SamplerOdometer.initializeStore,ih]
    rfl

theorem initialize_other (d : ℕ) (g h : Fin 3) (hgh : g≠h) (q k : ℕ)
    (s : TapeStore (80+6*d) 3) (hn : Numbered d g q k s) :
    Numbered d g q k (SamplerOdometer.initializeStore (low d 23) (low d 2) (tuple d h) s) := by
  apply hn.frame
  · exact SamplerOdometer.initializeStore_fresh _ _ _ _ _ (by simp) (low_not_tuple d h 23)
  · intro j hj
    apply SamplerOdometer.initializeStore_fresh
    · obtain ⟨i,rfl|rfl⟩ := (tuple_used d g j).mp hj
      all_goals exact digit_ne_low d _ i 2
    · exact tuple_other d g h hgh j hj








theorem pairPrepare_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ)
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



theorem Core.frame_input {d ell : ℕ} {h : 0<ell} {D M : ℕ}
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

















theorem pairFinishAfter_stops {L : ℕ} (d ell : ℕ) (h : 0<ell) (D M : ℕ)
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















theorem pairBody_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
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






theorem GramEffect.prefix {d q flat v : ℕ} {s e : TapeStore (80+6*d) 3}
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

theorem GramEffect.bottomMarked {d q flat v : ℕ} {s e : TapeStore (80+6*d) 3}
    (he : GramEffect d s e q flat v) (hm : TapeArrays.BottomMarked s 0) : TapeArrays.BottomMarked e 0 := by
  constructor
  · rw [he.symbol]
    have hh : ¬1+flat*q ≤ 0 := by omega
    simp only [hh,false_and,and_false,if_false]
    exact hm.1
  · intro k hk
    rw [he.symbol]
    split_ifs <;> first | decide | exact hm.2 k hk




theorem gramValue_pair (d ell : ℕ) (h : 0<ell) (D : ℕ) (y : Fin ((2^ell)^d) → Bool)
    (a b : Fin ((2^ell)^d)) :
    gramValue d ell h D y (a.val*(2^ell)^d+b.val)=
      (EncodedTester.entry (BinaryField.indexOperations ell h) D y a b).1.val := by
  have hval : (finProdFinEquiv (a,b)).val=a.val*(2^ell)^d+b.val := by simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  have hk : a.val*(2^ell)^d+b.val<(2^ell)^d*(2^ell)^d := hval ▸ (finProdFinEquiv (a,b)).isLt
  have he : (⟨a.val*(2^ell)^d+b.val,hk⟩ : Fin ((2^ell)^d*(2^ell)^d))=finProdFinEquiv (a,b) := Fin.ext hval.symm
  simp [gramValue,GaussianProgram.flatEntry,dif_pos hk,he,EncodedTester.table,Gaussian.toMatrix,Gaussian.ofMatrix]














theorem BuildState.frame {d ell : ℕ} {h : 0<ell} {D M flat : ℕ}
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

theorem BuildState.after_pair {d ell : ℕ} {h : 0<ell} {D M flat : ℕ}
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







theorem rowPrepare_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ)
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














theorem rowLoop_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
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







theorem rowFinishAfter_stops {L : ℕ} (d ell : ℕ) (h : 0<ell) (D M flat : ℕ)
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



theorem rowBody_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
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








theorem programPrepare_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ)
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









theorem programLoop_stops (d ell : ℕ) (h : 0<ell) (D M : ℕ) (hM : 1 ≤ M)
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

theorem BuildState.table {d ell : ℕ} {h : 0<ell} {D M : ℕ}
    {y : Fin ((2^ell)^d) → Bool} {origin s : TapeStore (80+6*d) 3}
    (hs : BuildState d ell h D M y origin ((2^ell)^d*(2^ell)^d) s) :
    TapeArrays.ThermometerTable s 0 (2^ell)
      (fun k : Fin ((2^ell)^d*(2^ell)^d) => GaussianProgram.flatEntry
        (EncodedTester.table (BinaryField.indexOperations ell h) D y) k.val) := by
  intro k
  exact hs.entries k.val k.isLt




theorem programTime_polynomial (d : ℕ) {M m : ℕ → ℕ}
    (hM : PolynomialBound M) (hm : PolynomialBound m) :
    PolynomialBound (fun x => programTime d (M x) (m x)) := by
  have hp := hM.add (PolynomialBound.const 1)
  have heval : PolynomialBound (fun x => TesterEvaluation.timeBound d (M x)) := by
    exact (((((PolynomialBound.const (d+1)).mul
        (((PolynomialBound.const 8).mul hM).add (PolynomialBound.const 10))).add
      ((PolynomialBound.const 64).mul hp)).add
        (((PolynomialBound.const (d+1)).mul ((PolynomialBound.const 27020).mul (hp.pow 7))).max hp)).add
          (PolynomialBound.const 4))
  have hu := (PolynomialBound.const d).mul (((PolynomialBound.const 8).mul hM).add (PolynomialBound.const 20))
  have hpoint : PolynomialBound (fun x => pointTime d (M x)) := by
    exact (((((PolynomialBound.const 64).mul (hp.pow 2)).add
      (((((PolynomialBound.const 2).mul heval).add ((PolynomialBound.const 13300).mul (hp.pow 6))).add
        ((PolynomialBound.const 28).mul hM)).add (PolynomialBound.const 32))).add hu).add (PolynomialBound.const 6))
  have hpair : PolynomialBound (fun x => pairTime d (M x) (m x)) := by
    exact (((((((hu.add ((PolynomialBound.const 9).mul hM)).add (PolynomialBound.const 12)).add (PolynomialBound.const 1)).add
      ((hm.mul (hpoint.add (PolynomialBound.const 2))).add (PolynomialBound.const 1))).add hu).add
        ((PolynomialBound.const 10).mul hM)).add (PolynomialBound.const 17))
  have hrow : PolynomialBound (fun x => rowTime d (M x) (m x)) := by
    exact ((((((hu.add ((PolynomialBound.const 8).mul hM)).add (PolynomialBound.const 10)).add (PolynomialBound.const 1)).add
      ((hm.mul (hpair.add (PolynomialBound.const 2))).add (PolynomialBound.const 1))).add hu).add (PolynomialBound.const 3))
  exact ((((hu.add ((PolynomialBound.const 9).mul hM)).add (PolynomialBound.const 12)).add (PolynomialBound.const 1)).add
    ((hm.mul (hrow.add (PolynomialBound.const 2))).add (PolynomialBound.const 1)))

theorem programTime_mono_m (d M : ℕ) : Monotone (programTime d M) := by
  intro m n hmn
  unfold programTime rowTime pairTime
  gcongr










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

/-! Inlined whole module: ExpandingCodes.Computation.TesterEnvelope -/
section FlattenModule82


set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation

theorem setupCounterBound_mono (d : ℕ) : Monotone (ParameterPrograms.setupCounterBound d) := by
  intro a b hab
  unfold ParameterPrograms.setupCounterBound ParameterPrograms.floorCounterBound
    ParameterPrograms.setupBound₃ ParameterPrograms.setupBound₂ ParameterPrograms.setupBound₁
    ParameterPrograms.powerCounterBound ParameterPrograms.ceilingCounterBound
  gcongr



















theorem testerEnvelope_covers (d n : ℕ) (hd : 0 < d) :
    TesterEnvelopeCovers d n (testerEnvelope d (rowCount d n+n)) := by
  let x := rowCount d n+n
  have hm : rowCount d n ≤ x+1 := by omega
  have hn : n ≤ x := by omega
  have hqrow : fieldSize d n ≤ rowCount d n := Nat.le_self_pow hd.ne' _
  have hq : fieldSize d n ≤ x+1 := hqrow.trans hm
  have he : fieldExponent d n ≤ x+1 :=
    (Nat.lt_two_pow_self : fieldExponent d n < 2^fieldExponent d n).le.trans hq
  have hcube : x+1 ≤ (x+1)^3 := Nat.le_self_pow (by decide) _
  have hc : (x+1)^3 ≤ (d+1)*(x+1)^3 := Nat.le_mul_of_pos_left _ (by omega)
  have hprod : rowCount d n*rowCount d n*fieldSize d n ≤ (x+1)^3 := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul hm hm) hq
    nlinarith only [h]
  have hword : rowCount d n*fieldSize d n ≤ (x+1)^3 := by
    have h := Nat.mul_le_mul hm hq
    have hx : 1 ≤ x+1 := by omega
    nlinarith
  have hsq : (fieldSize d n)^2 ≤ (x+1)^3 := by
    have h := Nat.mul_le_mul hq hq
    have hx : 1 ≤ x+1 := by omega
    nlinarith
  have hsum : d*(fieldSize d n-1) ≤ (d+1)*(x+1)^3 :=
    Nat.mul_le_mul (Nat.le_succ d) ((Nat.sub_le _ _).trans (hq.trans hcube))
  have hcut : (d-3)*(fieldSize d n-1) ≤ d*(fieldSize d n-1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hsetup := setupCounterBound_mono d (show n+1 ≤ x+1 by omega)
  constructor <;> change _ ≤ testerEnvelope d x <;> unfold testerEnvelope <;> omega

theorem testerEnvelope_polynomial (d : ℕ) : PolynomialBound (testerEnvelope d) := by
  have hsetup := ((ParameterPrograms.setup_bounds_polynomial d).2.comp
    (ParameterPrograms.PolynomialMajorant.id.add (ParameterPrograms.PolynomialMajorant.const 1))).toPolynomialBound
  exact (((((PolynomialBound.const 2).add hsetup).add
    ((PolynomialBound.const (d+1)).mul ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 3))).add
      ((PolynomialBound.const 3).mul (PolynomialBound.identity.add (PolynomialBound.const 1)))).add
        (PolynomialBound.const 1))



end ExpandingCodes.PolynomialStretch

end FlattenModule82

/-! Inlined whole module: ExpandingCodes.Computation.TesterPrefix -/
section FlattenModule83



set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterPrefix
open NKtLB TesterGram FieldPrograms
open ExpandingCodes.PolynomialStretch




theorem parameter_injective (d : ℕ) : Function.Injective (parameterLayout d) := by
  intro i j h; apply Fin.ext
  exact congrArg (fun x : Registers d => x.val) h
theorem field_injective (d : ℕ) : Function.Injective (fieldSetupLayout d) := by
  intro i j h; apply Fin.ext
  exact congrArg (fun x : Registers d => x.val) h


























theorem setup_initial_stops (d n M : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n)
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









theorem markers_stops (d : ℕ) (inp : Inputs) (s : TapeStore (80+6*d) 3) :
    (markers d).Stops inp (s.toCfg (markers d).entry) 5
      ((markedStore d s).toCfg (TapeProgram.rightLabel 4 (1 : Fin 2))) := by
  have h₀ := TapeMacros.cell_stops (0 : Fin 3) (fun _ => (Sym.bot,Move.right)) inp s
  have h₁ := TapeMacros.cell_stops (1 : Fin 3) (fun _ => (Sym.bot,Move.right)) inp
    (TapeArrays.painted s 0 .bot)
  have h₂ := TapeMacros.cell_stops (2 : Fin 3) (fun _ => (Sym.bot,Move.right)) inp
    (TapeArrays.painted (TapeArrays.painted s 0 .bot) 1 .bot)
  exact (h₀.seq h₁).seq h₂

theorem markedStore_tapes (d : ℕ) (s : TapeStore (80+6*d) 3)
    (ht : s.bufferTape=fun _ => []) (hh : s.bufferHead=fun _ => 0) :
    (markedStore d s).bufferTape=(fun _ => [.bot]) ∧
    (markedStore d s).bufferHead=(fun _ => 1) := by
  constructor <;> funext b <;> fin_cases b <;>
    simp [markedStore,TapeArrays.painted,TapeMacros.cellStore,ht,hh,Machine.writeAt,Machine.moveHead]

theorem markedStore_bottom (d : ℕ) (s : TapeStore (80+6*d) 3)
    (ht : s.bufferTape=fun _ => []) (hh : s.bufferHead=fun _ => 0) (b : Fin 3) :
    TapeArrays.BottomMarked (markedStore d s) b := by
  rw [TapeArrays.BottomMarked,(markedStore_tapes d s ht hh).1]
  constructor
  · rfl
  · intro k hk
    cases k with
    | zero => omega
    | succ k => simp

















theorem input_stops (d n M : ℕ) (inp : Inputs) (y : Word (rowCount d n))
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





theorem degree_injective (d : ℕ) : Function.Injective (degreeLayout d) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [degreeLayout,low]

theorem degree_width (d : ℕ) (s : TapeStore (80+6*d) 3) :
    (TesterEvaluation.degreeStore (degreeLayout d) d s).reg (low d 23)=s.reg (low d 23) := by
  simp [TesterEvaluation.degreeStore,TesterEvaluation.degreeScaled,TesterEvaluation.degreePrepare,
    FieldPrograms.halfStore,SamplerEvaluation.scaleStore,degreeLayout,TapeStore.setReg,low]

theorem degree_stops (d n M : ℕ) (hd : 4 ≤ d) (inp : Inputs)
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

theorem setupTimeBound_mono (d : ℕ) : Monotone (ParameterPrograms.setupTimeBound d) := by
  intro a b hab
  unfold ParameterPrograms.setupTimeBound ParameterPrograms.powerTimeBound
    ParameterPrograms.ceilingTimeBound ParameterPrograms.divisionTimeBound ParameterPrograms.floorTimeBound
    ParameterPrograms.setupBound₃ ParameterPrograms.setupBound₂ ParameterPrograms.setupBound₁
    ParameterPrograms.powerCounterBound ParameterPrograms.ceilingCounterBound
  gcongr






theorem time_le_clock (d n M : ℕ) : time d n M ≤ clock d (rowCount d n+n) M := by
  have hs := setupTimeBound_mono d (show n+1 ≤ rowCount d n+n+1 by omega)
  have hm := Nat.mul_le_mul_right (20*(M+1)+2) (show rowCount d n ≤ rowCount d n+n by omega)
  unfold time setupTime inputTime clock
  omega

theorem clock_polynomial (d : ℕ) : PolynomialBound (fun x => clock d x (testerEnvelope d x)) := by
  have hi := PolynomialBound.identity
  have hM := testerEnvelope_polynomial d
  have hM1 := hM.add (PolynomialBound.const 1)
  have hsetup := ((ParameterPrograms.setup_bounds_polynomial d).1.comp
    (ParameterPrograms.PolynomialMajorant.id.add (ParameterPrograms.PolynomialMajorant.const 1))).toPolynomialBound
  have hfirst := (((PolynomialBound.const 2).mul hi).add (PolynomialBound.const 4)).add hsetup
  have hsecond := (((PolynomialBound.const 28).mul hM).add (PolynomialBound.const 42)).add
    ((PolynomialBound.const 40000).mul (hM1.pow 7))
  have hthird := (hi.mul (((PolynomialBound.const 20).mul hM1).add (PolynomialBound.const 2))).add
    ((PolynomialBound.const (d+1)).mul ((PolynomialBound.const 30).mul hM1))
  exact (hfirst.add hsecond).add hthird



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

/-! Inlined whole module: ExpandingCodes.Computation.TesterProgram -/
section FlattenModule90



set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterProgram

open NKtLB

variable {R B : ℕ}















theorem compareTime_le (a b : ℕ) : compareTime a b ≤ 2*a+3 := by
  induction a generalizing b with
  | zero => simp [compareTime]
  | succ a ih =>
    cases b with
    | zero => simp [compareTime]
    | succ b => have h := ih b; simp only [compareTime]; omega




/-- Exact source trace and a frame contract. Only the two consumed counters
and output can change. No buffer access or read-only input occurs. -/
theorem compareLE_stops (a b : Fin R) (hab : a ≠ b) (inp : Inputs)
    (x y : ℕ) (d : TapeStore R B) (ha : d.reg a = x) (hb : d.reg b = y) :
    ∃ e : TapeStore R B, (compareLE a b).Stops inp (d.toCfg 0) (compareTime x y) (e.toCfg 5) ∧
      e.output = d.output ++ [decide (x ≤ y)] ∧
      e.roHead = d.roHead ∧ e.bufferTape = d.bufferTape ∧ e.bufferHead = d.bufferHead ∧
      (∀ r, r ≠ a → r ≠ b → e.reg r = d.reg r) ∧
      (∀ r, e.reg r ≤ d.reg r) := by
  induction x generalizing y d with
  | zero =>
    refine ⟨emitStore d true, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
    · constructor
      · apply TapeProgram.Exec.step (d := d.toCfg 3) (by simp [TapeProgram.halted, compareLE])
          (by simp [TapeProgram.step, compareLE, TapeStore.toCfg, ha])
        apply TapeProgram.Exec.one (by simp [TapeProgram.halted, compareLE])
        simp [TapeProgram.step, compareLE, TapeStore.toCfg, emitStore]
      · simp [TapeProgram.halted, compareLE]
    · simp [emitStore]
    · intro r _ _; rfl
    · intro r; exact le_rfl
  | succ x ih =>
    let d₁ := d.setReg a x
    have hs₁ : (compareLE a b).step inp (d.toCfg 0) = d₁.toCfg 1 := by
      simp [TapeProgram.step, compareLE, TapeStore.toCfg, d₁, TapeStore.setReg, ha]
    cases y with
    | zero =>
      refine ⟨emitStore d₁ false, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · constructor
        · apply TapeProgram.Exec.step (by simp [TapeProgram.halted, compareLE]) hs₁
          apply TapeProgram.Exec.step (d := d₁.toCfg 4) (by simp [TapeProgram.halted, compareLE])
            (by simp [TapeProgram.step, compareLE, TapeStore.toCfg, d₁, TapeStore.setReg,
              Ne.symm hab, hb])
          apply TapeProgram.Exec.one (by simp [TapeProgram.halted, compareLE])
          simp [TapeProgram.step, compareLE, TapeStore.toCfg, emitStore]
        · simp [TapeProgram.halted, compareLE]
      · simp [emitStore, d₁, TapeStore.setReg]
      · intro r hra _
        simp [emitStore, d₁, TapeStore.setReg, hra]
      · intro r
        by_cases hr : r = a
        · subst r; simp [emitStore, d₁, TapeStore.setReg, ha]
        · simp [emitStore, d₁, TapeStore.setReg, hr]
    | succ y =>
      let d₂ := d₁.setReg b y
      have h₂a : d₂.reg a = x := by simp [d₂, d₁, TapeStore.setReg, hab]
      have h₂b : d₂.reg b = y := by simp [d₂, TapeStore.setReg]
      obtain ⟨e, he, heo, her, het, heh, hef, heb⟩ := ih y d₂ h₂a h₂b
      refine ⟨e, ?_, ?_, her, het, heh, ?_, ?_⟩
      · constructor
        · apply TapeProgram.Exec.step (by simp [TapeProgram.halted, compareLE]) hs₁
          apply TapeProgram.Exec.step (d := d₂.toCfg 0) (by simp [TapeProgram.halted, compareLE])
            (by simp [TapeProgram.step, compareLE, TapeStore.toCfg, d₂, d₁,
              TapeStore.setReg, Ne.symm hab, hb])
          exact he.exec
        · exact he.halted
      · simpa [d₂, d₁, TapeStore.setReg] using heo
      · intro r hra hrb
        rw [hef r hra hrb]
        simp [d₂, d₁, TapeStore.setReg, hra, hrb]
      · intro r
        apply (heb r).trans
        by_cases hra : r = a
        · subst r; simp [d₂, d₁, TapeStore.setReg, hab, ha]
        · by_cases hrb : r = b
          · subst r; simp [d₂, d₁, TapeStore.setReg, hb]
          · simp [d₂, d₁, TapeStore.setReg, hra, hrb]

























theorem rankThreshold_stops {B : ℕ} (inp : Inputs) (d : TapeStore 8 B) (M : ℕ)
    (hM : ∀ r, d.reg r ≤ M) :
    ∃ t e, t ≤ 100*(M+1)^2 ∧
      (rankThreshold (B := B)).Stops inp (d.toCfg (rankThreshold (B := B)).entry) t e ∧
      e.output = d.output ++ [decide (d.reg 0*d.reg 2 ≤ d.reg 3*d.reg 1)] ∧
      e.roHead = d.roHead ∧ e.bufferTape = d.bufferTape ∧ e.bufferHead = d.bufferHead ∧
      (∀ r : Fin 8, r.val < 4 → e.reg r = d.reg r) := by
  obtain ⟨t₁, c, ht₁, hc, hcs⟩ := UnaryArithmetic.multiply_stops_polynomial
    (B := B) (0 : Fin 8) 2 4 6 7 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      inp d M (hM 0) (hM 2) (hM 4) (hM 6) (hM 7)
  have hcm (r : Fin 8) (hr : r ≠ 4) : c.store.reg r ≤ M := by
    rw [hcs]
    simp only [UnaryArithmetic.multiplyStore, TapeStore.setReg]
    by_cases h6 : r = 6
    · subst r; simp
    · by_cases h7 : r = 7
      · subst r; simp
      · simpa [Function.update, hr, h6, h7] using hM r
  obtain ⟨t₂, f, ht₂, hf, hfs⟩ := UnaryArithmetic.multiply_stops_polynomial
    (B := B) (1 : Fin 8) 3 5 6 7 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      inp c.store M (hcm 1 (by decide)) (hcm 3 (by decide))
        (hcm 5 (by decide)) (hcm 6 (by decide)) (hcm 7 (by decide))
  have hleft : f.store.reg 4 = d.reg 0*d.reg 2 := by
    rw [hfs, hcs]
    simp [UnaryArithmetic.multiplyStore, TapeStore.setReg]
  have hright : f.store.reg 5 = d.reg 1*d.reg 3 := by
    rw [hfs, hcs]
    simp [UnaryArithmetic.multiplyStore, TapeStore.setReg]
  obtain ⟨s, hs, hso, hsr, hst, hsh, hsf, _⟩ := compareLE_stops
    (B := B) (4 : Fin 8) 5 (by decide) inp (f.store.reg 4) (f.store.reg 5)
      f.store rfl rfl
  have hall := (hc.seq hf).seq hs
  refine ⟨_, _, ?_, hall, ?_, ?_, ?_, ?_, ?_⟩
  · have ht := compareTime_le (f.store.reg 4) (f.store.reg 5)
    rw [hleft] at ht
    rw [hleft]
    have hp := Nat.mul_le_mul (hM 0) (hM 2)
    nlinarith
  · change s.output = _
    rw [hso, hleft, hright]
    rw [hfs, hcs]
    simp [UnaryArithmetic.multiplyStore, TapeStore.setReg, Nat.mul_comm]
  · change s.roHead = _
    rw [hsr, hfs, hcs]
    rfl
  · change s.bufferTape = _
    rw [hst, hfs, hcs]
    rfl
  · change s.bufferHead = _
    rw [hsh, hfs, hcs]
    rfl
  · intro r hr
    change s.reg r = _
    rw [hsf r (by intro he; subst r; simp at hr) (by intro he; subst r; simp at hr), hfs, hcs]
    have h4 : r ≠ 4 := by intro he; subst r; simp at hr
    have h5 : r ≠ 5 := by intro he; subst r; simp at hr
    have h6 : r ≠ 6 := by intro he; subst r; simp at hr
    have h7 : r ≠ 7 := by intro he; subst r; simp at hr
    simp [UnaryArithmetic.multiplyStore, TapeStore.setReg, h4, h5, h6, h7]

































end ExpandingCodes.Computation.TesterProgram

end FlattenModule90

/-! Inlined whole module: ExpandingCodes.Computation.TesterSuffix -/
section FlattenModule91





set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterSuffix
open NKtLB ParameterPrograms
variable {R B : ℕ}



















theorem program_stops (θ : ℚ) (r : Fin 8 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (d : TapeStore R B) (M : ℕ) (hd : ∀ j, d.reg j ≤ M) :
    ∃ t e, t ≤ timeBound θ M ∧
      (program θ r).Stops inp (d.toCfg (program (B := B) θ r).entry) t e ∧
      e.output = d.output ++ [decide (d.reg (r 0)*(eta θ).den ≤ (eta θ).num.toNat*d.reg (r 1))] := by
  obtain ⟨c,hc,hcs⟩ := loadConstant_stops (r 2) (eta θ).den inp d
  obtain ⟨f,hf,hfs⟩ := loadConstant_stops (r 3) (eta θ).num.toNat inp c.store
  have hpost : f.store = constantsStore θ r d := by rw [hfs,hcs]; rfl
  have h3 : c.store.reg (r 3) = d.reg (r 3) := by
    rw [hcs]
    simp [TapeStore.setReg,hr.ne (by decide : (3 : Fin 8) ≠ 2)]
  have hbound : ∀ j, f.store.reg j ≤ envelope θ M := by
    rw [hpost]
    apply FieldPrograms.setReg_bound
    · apply FieldPrograms.setReg_bound
      · intro j
        exact (hd j).trans (le_max_left _ _)
      · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  let small := f.store.projectStorage r (id : Fin B → Fin B)
  have hb : ∀ i, small.reg i ≤ envelope θ M := fun i => hbound (r i)
  obtain ⟨u,e,hu,he,heo,_⟩ := TesterProgram.rankThreshold_stops inp small (envelope θ M) hb
  obtain ⟨z,hz,hproj,hzo⟩ := he.liftStorage r (id : Fin B → Fin B) hr Function.injective_id
    (f.store.toCfg (TesterProgram.rankThreshold (B := B)).entry) rfl
  have hbit : decide (small.reg 0*small.reg 2 ≤ small.reg 3*small.reg 1) =
      decide (d.reg (r 0)*(eta θ).den ≤ (eta θ).num.toNat*d.reg (r 1)) := by
    have hreg : f.reg = (constantsStore θ r d).reg := congrArg TapeStore.reg hpost
    simp [small,TapeStore.projectStorage,hreg,constantsStore,TapeStore.setReg,hr.eq_iff]
  have houtput : small.output = d.output := by rw [show small.output = f.store.output from rfl,hpost]; rfl
  have hall := (hc.seq hf).seq hz
  refine ⟨(d.reg (r 2)+2*(eta θ).den+2)+1+
    (c.store.reg (r 3)+2*(eta θ).num.toNat+2)+1+u,
    z.mapPC (TapeProgram.rightLabel (loadLabels (eta θ).den+loadLabels (eta θ).num.toNat)),?_,?_,?_⟩
  · rw [h3]
    have := hd (r 2)
    have := hd (r 3)
    unfold timeBound
    omega
  · convert hall using 1 <;> rfl
  · change z.output = _
    rw [hzo,heo,houtput,hbit]

theorem timeBound_polynomial (θ : ℚ) : PolynomialBound (timeBound θ) := by
  have he : PolynomialBound (envelope θ) := PolynomialBound.identity.max
    ((PolynomialBound.const (eta θ).den).max (PolynomialBound.const (eta θ).num.toNat))
  have hleft := (((PolynomialBound.const 2).mul PolynomialBound.identity).add
    (PolynomialBound.const (2*(eta θ).den))).add (PolynomialBound.const (2*(eta θ).num.toNat))
  exact (hleft.add (PolynomialBound.const 6)).add
    ((PolynomialBound.const 100).mul ((he.add (PolynomialBound.const 1)).pow 2))

theorem program_canonical (θ : ℚ) (hθ : θ ≤ 1) (r : Fin 8 → Fin R)
    (hr : Function.Injective r) (d n : ℕ)
    (y : PolynomialStretch.Word (PolynomialStretch.rowCount d n))
    (inp : Inputs) (s : TapeStore R B) (M : ℕ) (hM : ∀ j, s.reg j ≤ M)
    (hrank : s.reg (r 0) = (EncodedGaussian.run
      (PolynomialStretch.BinaryField.indexOperations
        (PolynomialStretch.fieldExponent d n) (PolynomialStretch.fieldExponent_pos d n))
      (PolynomialStretch.binaryTestTable d n y)).1)
    (hm : s.reg (r 1) = PolynomialStretch.rowCount d n) :
    ∃ t e, t ≤ timeBound θ M ∧
      (program θ r).Stops inp (s.toCfg (program (B := B) θ r).entry) t e ∧
      e.output = s.output ++ [PolynomialStretch.rankTest (θ : ℝ)
        (PolynomialStretch.binaryGeometry d n) y] := by
  obtain ⟨t,e,ht,he,heo⟩ := program_stops θ r hr inp s M hM
  have hb : decide (s.reg (r 0)*(eta θ).den ≤ (eta θ).num.toNat*s.reg (r 1)) =
      PolynomialStretch.rankTest (θ : ℝ) (PolynomialStretch.binaryGeometry d n) y := by
    calc
      _ = PolynomialStretch.binaryRankTest θ d n y := by
        simp only [hrank,hm,eta,PolynomialStretch.binaryRankTest]
      _ = _ := PolynomialStretch.binaryRankTest_eq θ hθ d n y
  exact ⟨t,e,ht,he,by simpa only [hb] using heo⟩




end ExpandingCodes.Computation.TesterSuffix

end FlattenModule91

/-! Inlined whole module: ExpandingCodes.Computation.TesterBackend -/
section FlattenModule92




set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterBackend
open NKtLB GaussianProgram
open ExpandingCodes.PolynomialStretch


theorem suffixLayout_injective : Function.Injective suffixLayout := by decide









theorem program_stops (θ : ℚ) (hθ : θ ≤ 1) (degree n M : ℕ) (inp : Inputs)
    (d : Store) (y : Word (rowCount degree n))
    (hc : GaussianDriver.Common (fieldExponent degree n) (fieldExponent_pos degree n)
      (rowCount degree n) M d)
    (B : Gaussian.Table (Fin (fieldSize degree n)) (rowCount degree n) (rowCount degree n))
    (ha : MatrixStored d 0 (binaryTestTable degree n y)) (hb : MatrixStored d 1 B) :
    ∃ t e, t ≤ timeBound θ M ∧ (program θ).Stops inp (d.toCfg (program θ).entry) t e ∧
      e.output = d.output ++ [rankTest (θ : ℝ) (binaryGeometry degree n) y] := by
  obtain ⟨t,c,ht,hc,hcommon,hrank,_,_,hout⟩ := GaussianDriver.rankProgram_stops_canonical
    degree n M inp d y hc B ha hb
  have hr : c.store.reg (suffixLayout 0) = (EncodedGaussian.run
      (BinaryField.indexOperations (fieldExponent degree n) (fieldExponent_pos degree n))
      (binaryTestTable degree n y)).1 :=
    hrank.trans (binaryTestTable_rank degree n y).symm
  have hm : c.store.reg (suffixLayout 1) = rowCount degree n := hcommon.rows
  obtain ⟨s,e,hs,he,heo⟩ := TesterSuffix.program_canonical θ hθ suffixLayout suffixLayout_injective
    degree n y inp c.store M hcommon.state.bounded hr hm
  refine ⟨t+1+s,e.mapPC (TapeProgram.rightLabel 4260),?_,?_,?_⟩
  · unfold timeBound
    omega
  · convert hc.seq he using 1 <;> rfl
  · change e.output = _
    have ho : c.store.output = d.output := hout
    rw [heo,ho]

theorem timeBound_polynomial (θ : ℚ) : PolynomialBound (timeBound θ) :=
  ((((PolynomialBound.const 100000).mul
    ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 9)).add
      (PolynomialBound.const 1)).add (TesterSuffix.timeBound_polynomial θ))



end ExpandingCodes.Computation.TesterBackend

end FlattenModule92

/-! Inlined whole module: ExpandingCodes.Computation.ZeroTables -/
section FlattenModule93


set_option autoImplicit false

namespace ExpandingCodes.Computation.ZeroTables
open NKtLB TapeArrays
variable {R B K : ℕ}








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




end ExpandingCodes.Computation.ZeroTables

end FlattenModule93

/-! Inlined whole module: ExpandingCodes.Computation.TesterBackendPrep -/
section FlattenModule94





set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterBackendPrep
open NKtLB UnaryArithmetic FieldPrograms TapeArrays GaussianProgram
open ExpandingCodes.PolynomialStretch



















theorem copies_stops (ps : List Pair) (hp : Valid ps) (inp : Inputs)
    (d : BigStore) (M : ℕ) (hd : ∀ r,d.reg r ≤ M) :
    ∃ t e, t ≤ ps.length*(7*M+8) ∧
      (copies ps).Stops inp (d.toCfg (copies ps).entry) t e ∧
      e.store = copyResult ps d ∧ ∀ r,e.reg r ≤ M := by
  induction ps generalizing d with
  | nil => exact ⟨0,d.toCfg ⟨0,by decide⟩,by simp,TapeProgram.skip_stops inp d,rfl,hd⟩
  | cons p ps ih =>
    have hv := hp p (by simp)
    obtain ⟨t,c,ht,hc,hcs,hcb⟩ := SamplerEvaluation.copy_stops_bound
      p.1 p.2 79 hv.1 hv.2.1 hv.2.2 inp M d hd
    obtain ⟨s,e,hs,he,hes,heb⟩ := ih (by
      intro p hp'; exact hp p (by simp [hp'])) c.store hcb
    refine ⟨t+1+s,e.mapPC (TapeProgram.rightLabel 11),?_,?_,?_,heb⟩
    · rw [List.length_cons,Nat.succ_mul]
      omega
    · exact hc.seq he
    · change e.store = _
      rw [hes,hcs]
      rfl

theorem copyResult_data (ps : List Pair) (d : BigStore) :
    FieldConvolution.tapeData (copyResult ps d) = FieldConvolution.tapeData d := by
  induction ps generalizing d with
  | nil => rfl
  | cons p ps ih => simpa [copyResult] using ih ((d.setReg p.2 (d.reg p.1)).setReg 79 0)


theorem metadataPairs_valid : Valid metadataPairs := by
  intro p hp
  simp [metadataPairs] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by decide,by decide,by decide⟩
















theorem beforeZero_reg (d : BigStore) :
    (beforeZero d).reg = (registerResult d).reg := by
  simp only [beforeZero,metadataPairs,copyResult,multiplyStore,registerResult,TapeStore.setReg]
  funext r
  by_cases h79 : r = 79
  · subst r; simp
  · simp [Function.update,h79]


theorem beforeZero_data (d : BigStore) :
    FieldConvolution.tapeData (beforeZero d) = FieldConvolution.tapeData d := by
  simp only [beforeZero,multiplyStore,FieldConvolution.tapeData_setReg,copyResult_data]

theorem program_stops (inp : Inputs) (d : BigStore) (M : ℕ)
    (hd : ∀ r,d.reg r ≤ M) (hq : 0 < d.reg 23)
    (hn : d.reg 70*d.reg 70*d.reg 23 ≤ M) :
    ∃ t e, t ≤ 150*(M+1)^2 ∧ program.Stops inp (d.toCfg program.entry) t e ∧
      e.store = result d ∧ ∀ r,e.reg r ≤ M := by
  have hsq : d.reg 70*d.reg 70 ≤ M := by
    exact (Nat.le_mul_of_pos_right _ hq).trans hn
  obtain ⟨t₁,c₁,ht₁,h₁,hs₁,hb₁⟩ := copies_stops metadataPairs metadataPairs_valid inp d M hd
  obtain ⟨t₂,c₂,ht₂,h₂,hs₂⟩ := multiply_stops_polynomial 70 70 51 52 53
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) inp c₁.store M
    (hb₁ _) (hb₁ _) (hb₁ _) (hb₁ _) (hb₁ _)
  have h70 : c₁.reg 70 = d.reg 70 := by
    change c₁.store.reg 70 = _
    rw [hs₁]
    simp [metadataPairs,copyResult,TapeStore.setReg]
  have hb₂ : ∀ r,c₂.reg r ≤ M := by
    change ∀ r,c₂.store.reg r ≤ M
    rw [hs₂]
    apply setReg_bound
    · apply setReg_bound
      · apply setReg_bound _ _ _ M hb₁
        simpa only [h70] using hsq
      · omega
    · omega
  obtain ⟨t₃,c₃,ht₃,h₃,hs₃⟩ := multiply_stops_polynomial 51 0 54 55 56
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) inp c₂.store M
    (hb₂ _) (hb₂ _) (hb₂ _) (hb₂ _) (hb₂ _)
  have hpre : c₃.store = beforeZero d := by rw [hs₃,hs₂,hs₁]; rfl
  have hpreBound : ∀ r,(beforeZero d).reg r ≤ M := by
    rw [beforeZero_reg]
    unfold registerResult
    repeat apply setReg_bound
    all_goals first | exact hd | exact hd _ | exact hsq | exact hn | omega
  have h54 : c₃.reg 54 = d.reg 70*d.reg 70*d.reg 23 := by
    change c₃.store.reg 54 = _
    rw [hpre,beforeZero_reg]
    simp [registerResult,TapeStore.setReg]
  have h₄ := ZeroTables.program_stops 54 1 (d.reg 70*d.reg 70*d.reg 23) inp c₃.store h54
  have hall := ((h₁.seq h₂).seq h₃).seq h₄
  refine ⟨t₁+1+t₂+1+t₃+1+(2*(d.reg 70*d.reg 70*d.reg 23)+1),_,?_,hall,?_,?_⟩
  · have hh : metadataPairs.length = 6 := rfl
    rw [hh] at ht₁
    nlinarith
  · change ZeroTables.result 54 1 _ c₃.store = result d
    rw [hpre]
    rfl
  · change ∀ r,(ZeroTables.result 54 1 _ c₃.store).reg r ≤ M
    rw [hpre]
    exact ZeroTables.result_bound _ _ _ _ _ hpreBound


end ExpandingCodes.Computation.TesterBackendPrep

end FlattenModule94

/-! Inlined whole module: ExpandingCodes.Computation.TesterBackendComplete -/
section FlattenModule95


set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterBackendComplete
open NKtLB GaussianProgram TapeArrays
open ExpandingCodes.PolynomialStretch
open TesterBackendPrep



theorem registers_injective : Function.Injective registers := by
  intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 80 => x.val) h
theorem buffers_injective : Function.Injective buffers := by
  intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 3 => x.val) h

















theorem result_metadata (d : BigStore) :
    (result d).reg 0 = d.reg 23 ∧ (result d).reg 36 = d.reg 24 ∧
    (result d).reg 37 = d.reg 19 ∧ (result d).reg 38 = d.reg 3 ∧
    (result d).reg 40 = d.reg 70 ∧ (result d).reg 49 = d.reg 70 ∧
    (result d).reg 51 = d.reg 70*d.reg 70 := by
  have hr : (result d).reg = Function.update (registerResult d).reg 54 0 := by
    rw [result,ZeroTables.result_reg,beforeZero_reg]
  rw [hr]
  simp [registerResult,TapeStore.setReg]

theorem beforeZero_tape (d : BigStore) : (beforeZero d).bufferTape = d.bufferTape :=
  congrArg (fun v => v.2.2.1) (beforeZero_data d)

theorem beforeZero_head (d : BigStore) : (beforeZero d).bufferHead = d.bufferHead :=
  congrArg (fun v => v.2.2.2) (beforeZero_data d)

theorem result_common (ell : ℕ) (h : 0 < ell) (m M : ℕ) (d : BigStore)
    (hr : Ready ell h m M d) (hb : ∀ r,(result d).reg r ≤ M) :
    GaussianDriver.Common ell h m M (project (result d)) := by
  obtain ⟨hq,hq2,hN,hp,hm,hm',hc⟩ := result_metadata d
  have hH : (beforeZero d).bufferHead 1 = 1 := by rw [beforeZero_head]; exact hr.spareHead
  have hheads := ZeroTables.result_head 54 1 (d.reg 70*d.reg 70*d.reg 23) (beforeZero d) hH
  have hbound : d.reg 70*d.reg 70*d.reg 23 ≤ M := by rw [hr.rows,hr.q]; exact hr.cells
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,hr.large⟩
  · change (result d).reg 0 = _ ∧ (result d).reg 36 = _ ∧
      (result d).reg 37 = _ ∧ (result d).reg 38 = _
    exact ⟨hq.trans hr.q,hq2.trans hr.qSquared,hN.trans hr.coefficientCount,hp.trans hr.monic⟩
  · intro r; exact hb (registers r)
  · change (result d).bufferHead 0 ≤ _
    rw [result,hheads]
    simpa only [Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1),beforeZero_head] using hr.gramHead
  · change (result d).bufferHead 1 ≤ _
    rw [result,hheads]
    simp only [Function.update_self]
    nlinarith
  · change BottomMarked (result d) (0 : Fin 3)
    have hz (j : ℕ) : ((result d).bufferTape 0).getD j .blank =
        (d.bufferTape 0).getD j .blank := by
      rw [result,ZeroTables.result_other_symbol _ _ _ _ _ (by decide),beforeZero_tape]
    exact ⟨(hz 0).trans hr.gramMarked.1,fun j hj => by rw [hz]; exact hr.gramMarked.2 j hj⟩
  · change BottomMarked (result d) (1 : Fin 3)
    apply ZeroTables.result_bottomMarked 54 1 _ (beforeZero d) hH
    simpa only [BottomMarked,beforeZero_tape] using hr.spareMarked
  · exact hm.trans hr.rows
  · exact hm'.trans hr.rows
  · change (result d).reg 51 = m*m
    simpa only [hr.rows] using hc

theorem result_gram {q m n : ℕ} (d : BigStore)
    (A : Gaussian.Table (Fin q) m n)
    (ha : ThermometerTable d 0 q (fun i : Fin (m*n) => flatEntry A i.val)) :
    MatrixStored (project (result d)) 0 A := by
  change ThermometerTable (result d) (0 : Fin 3) q _
  apply ZeroTables.result_other_table 54 1 _ (beforeZero d) 0 (by decide) q _
  simpa only [ThermometerTable,ThermometerAt,beforeZero_tape] using ha




theorem zeroTable_flat (ell m k : ℕ) : flatEntry (zeroTable ell m) k = 0 := by
  simp [flatEntry,zeroTable,Gaussian.toMatrix,Gaussian.ofMatrix]

theorem result_spare (ell : ℕ) (h : 0 < ell) (m M : ℕ) (d : BigStore)
    (hr : Ready ell h m M d) :
    MatrixStored (project (result d)) 1 (zeroTable ell m) := by
  have hH : (beforeZero d).bufferHead 1 = 1 := by rw [beforeZero_head]; exact hr.spareHead
  have ht := ZeroTables.result_table (K := m*m) 54 1 (2^ell) (beforeZero d) hH
  change ThermometerTable (result d) (1 : Fin 3) (2^ell) _
  simp only [zeroTable_flat]
  simpa only [result,hr.rows,hr.q] using ht








theorem program_stops (θ : ℚ) (hθ : θ ≤ 1) (degree n M : ℕ) (inp : Inputs)
    (d : BigStore) (y : Word (rowCount degree n))
    (hr : Ready (fieldExponent degree n) (fieldExponent_pos degree n) (rowCount degree n) M d)
    (ha : ThermometerTable d 0 (fieldSize degree n)
      (fun i : Fin (rowCount degree n*rowCount degree n) => flatEntry (binaryTestTable degree n y) i.val)) :
    ∃ t e, t ≤ timeBound θ M ∧ (program θ).Stops inp (d.toCfg (program θ).entry) t e ∧
      e.output = d.output ++ [rankTest (θ : ℝ) (binaryGeometry degree n) y] := by
  have hq : 0 < d.reg 23 := by rw [hr.q]; exact pow_pos (by decide) _
  have hn : d.reg 70*d.reg 70*d.reg 23 ≤ M := by rw [hr.rows,hr.q]; exact hr.cells
  obtain ⟨t,c,ht,hc,hcs,hcb⟩ := TesterBackendPrep.program_stops inp d M hr.bounded hq hn
  have hbc : ∀ r,(result d).reg r ≤ M := by
    have he : c.reg = (result d).reg := congrArg TapeStore.reg hcs
    simpa only [he] using hcb
  have hcommon := result_common _ _ _ _ d hr hbc
  have hGram := result_gram d (binaryTestTable degree n y) ha
  have hSpare := result_spare _ _ _ _ d hr
  obtain ⟨s,e,hs,he,heo⟩ := TesterBackend.program_stops θ hθ degree n M inp
    (project (result d)) y hcommon (zeroTable (fieldExponent degree n) (rowCount degree n)) hGram hSpare
  obtain ⟨f,hf,_,hfo⟩ := he.liftStorage registers buffers registers_injective buffers_injective
    (c.store.toCfg (TesterBackend.program θ).entry) (by rw [hcs]; rfl)
  refine ⟨t+1+s,f.mapPC (TapeProgram.rightLabel 118),by unfold timeBound; omega,?_,?_⟩
  · convert hc.seq hf using 1 <;> rfl
  · change f.output = _
    rw [hfo,heo]
    change (result d).output ++ _ = _
    have ho : (result d).output = d.output :=
      (ZeroTables.result_payload 54 1 _ (beforeZero d)).2.trans
        (congrArg (fun v => v.2.1) (beforeZero_data d))
    rw [ho]

theorem timeBound_polynomial (θ : ℚ) : PolynomialBound (timeBound θ) :=
  ((((PolynomialBound.const 150).mul
    ((PolynomialBound.identity.add (PolynomialBound.const 1)).pow 2)).add
      (PolynomialBound.const 1)).add (TesterBackend.timeBound_polynomial θ))



end ExpandingCodes.Computation.TesterBackendComplete

end FlattenModule95

/-! Inlined whole module: ExpandingCodes.Computation.TesterAssembly -/
section FlattenModule96



set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterAssembly
open NKtLB GaussianProgram TapeArrays
open ExpandingCodes.PolynomialStretch




theorem low_injective (degree : ℕ) : Function.Injective (TesterGram.low degree) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin (80+6*degree) => x.val) h







theorem backend_stops (θ : ℚ) (hθ : θ ≤ 1) (degree n M : ℕ) (inp : Inputs)
    (d : TapeStore (80+6*degree) 3) (y : Word (rowCount degree n))
    (hr : TesterBackendComplete.Ready (fieldExponent degree n) (fieldExponent_pos degree n)
      (rowCount degree n) M (view degree d))
    (ha : ThermometerTable d 0 (fieldSize degree n)
      (fun i : Fin (rowCount degree n*rowCount degree n) => flatEntry (binaryTestTable degree n y) i.val)) :
    ∃ t e, t ≤ TesterBackendComplete.timeBound θ M ∧
      (backend θ degree).Stops inp (d.toCfg (backend θ degree).entry) t e ∧
      e.output = d.output ++ [rankTest (θ : ℝ) (binaryGeometry degree n) y] := by
  obtain ⟨t,c,ht,hc,hco⟩ := TesterBackendComplete.program_stops θ hθ degree n M inp
    (view degree d) y hr ha
  obtain ⟨e,he,_,heo⟩ := hc.liftStorage (TesterGram.low degree) id (low_injective degree)
    Function.injective_id (d.toCfg (backend θ degree).entry) rfl
  exact ⟨t,e,ht,he,heo.trans hco⟩

/-- Compose an actual Gram-prefix trace with the complete actual backend.
The prefix premise contains its executed trace and physical final matrix. -/
theorem program_stops_of_construct (θ : ℚ) (hθ : θ ≤ 1) (degree n M : ℕ)
    (inp : Inputs) (d : TapeStore (80+6*degree) 3) (y : Word (rowCount degree n))
    (t : ℕ) (c : TapeCfg (80+6*degree) 3 _)
    (hc : (TesterGram.construct degree).Stops inp (d.toCfg (TesterGram.construct degree).entry) t c)
    (hr : TesterBackendComplete.Ready (fieldExponent degree n) (fieldExponent_pos degree n)
      (rowCount degree n) M (view degree c.store))
    (ha : ThermometerTable c.store 0 (fieldSize degree n)
      (fun i : Fin (rowCount degree n*rowCount degree n) => flatEntry (binaryTestTable degree n y) i.val))
    (ho : c.output = []) :
    ∃ s e, s ≤ t+1+TesterBackendComplete.timeBound θ M ∧
      (program θ degree).Stops inp (d.toCfg (program θ degree).entry) s e ∧
      e.output = [rankTest (θ : ℝ) (binaryGeometry degree n) y] := by
  obtain ⟨s,e,hs,he,heo⟩ := backend_stops θ hθ degree n M inp c.store y hr ha
  refine ⟨t+1+s,e.mapPC (TapeProgram.rightLabel _),by omega,?_,?_⟩
  · exact hc.seq he
  · change e.output = _
    simpa only [ho,List.nil_append] using heo



end ExpandingCodes.Computation.TesterAssembly

end FlattenModule96

/-! Inlined whole module: ExpandingCodes.Computation.SourceBridge -/
section FlattenModule97





set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch






























open ExpandingCodes.Computation

/-- Convert an actual finite source program's uniform source-step bound to the
canonical finite transition-table tester clause, with explicit constant overhead. -/
theorem testerImplementation_of_tape {R B L : ℕ}
    (θ : ℚ) (g : ∀ n, Geometry (dimension (θ : ℝ)) n)
    (P : TapeProgram R B L) (C b N : ℕ) (hN : 2 ≤ N)
    (h : ∀ n ≥ N, ∀ y : Word (rowCount (dimension (θ : ℝ)) n),
      ∃ t ≤ C * (rowCount (dimension (θ : ℝ)) n + n + 1) ^ b,
        P.halted (P.run ⟨sizeInput n ++ wordBits y, [], [], []⟩ t) ∧
          (P.run ⟨sizeInput n ++ wordBits y, [], [], []⟩ t).output =
            [rankTest (θ : ℝ) (g n) y]) : TesterImplementation θ g := by
  refine ⟨TapeCompiler.compile P, 2*C+1, b, N, by omega, hN, ?_⟩
  intro n hn y
  obtain ⟨t, ht, hh, hout⟩ := h n hn y
  have hp : 1 ≤ (rowCount (dimension (θ : ℝ)) n + n + 1) ^ b :=
    one_le_pow₀ (by omega)
  have htime : 1+2*t ≤ (2*C+1) * (rowCount (dimension (θ : ℝ)) n + n + 1) ^ b := by
    nlinarith
  have hm := (TapeCompiler.compile_computes P (sizeInput n ++ wordBits y) t hh).mono htime
  simpa only [hout] using hm







































end ExpandingCodes.PolynomialStretch

end FlattenModule97

/-! Inlined whole module: ExpandingCodes.Computation.TesterSource -/
section FlattenModule98




set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation

/-- Assemble the actual source runtime theorem, a polynomial envelope in
m+n, and the proved source compiler into the exact canonical tester clause. -/
theorem binary_tester_of_source {R B L : ℕ} (θ : ℚ)
    (P : TapeProgram R B L) (time : ℕ → ℕ) (N : ℕ)
    (htime : PolynomialBound time)
    (hsource : ∀ n ≥ N, ∀ y : Word (rowCount (dimension (θ : ℝ)) n),
      ∃ t ≤ time (rowCount (dimension (θ : ℝ)) n+n),
        P.halted (P.run ⟨sizeInput n ++ wordBits y, [], [], []⟩ t) ∧
          (P.run ⟨sizeInput n ++ wordBits y, [], [], []⟩ t).output =
            [rankTest (θ : ℝ) (binaryGeometry (dimension (θ : ℝ)) n) y]) :
    TesterImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) := by
  obtain ⟨C,a,hbound⟩ := htime
  apply testerImplementation_of_tape θ (fun n => binaryGeometry (dimension (θ : ℝ)) n)
    P C a (max N 2) (le_max_right _ _)
  intro n hn y
  obtain ⟨t,ht,hh,hout⟩ := hsource n ((le_max_left N 2).trans hn) y
  have hn2 : 2 ≤ n := (le_max_right N 2).trans hn
  have hx : 2 ≤ rowCount (dimension (θ : ℝ)) n+n := by omega
  exact ⟨t,ht.trans (hbound _ hx),hh,hout⟩


end ExpandingCodes.PolynomialStretch

end FlattenModule98

/-! Inlined whole module: ExpandingCodes.Computation.TesterImplementation -/
section FlattenModule99





set_option autoImplicit false

namespace ExpandingCodes.Computation.TesterImplementation
open NKtLB TesterGram
open ExpandingCodes.PolynomialStretch






theorem clock_polynomial (θ : ℚ) (d : ℕ) : PolynomialBound (clock θ d) := by
  have hf := TesterFrontend.clock_polynomial d
  have hg := programTime_polynomial d (testerEnvelope_polynomial d) PolynomialBound.identity
  have hb := (TesterBackendComplete.timeBound_polynomial θ).comp (testerEnvelope_polynomial d)
  exact ((((hf.add (PolynomialBound.const 1)).add hg).add (PolynomialBound.const 1)).add hb)

theorem source_stops (θ : ℚ) (hθ : θ ≤ 1) (d n : ℕ) (hd : 4 ≤ d) (hn : 2 ≤ n)
    (y : Word (rowCount d n)) :
    ∃ t e,t ≤ clock θ d (rowCount d n+n) ∧
      (TesterAssembly.program θ d).Stops ⟨sizeInput n++wordBits y,[],[],[]⟩
        ((TesterPrefix.initialStore d).toCfg (TesterAssembly.program θ d).entry) t e ∧
      e.output=[rankTest (θ : ℝ) (binaryGeometry d n) y] := by
  let M := testerEnvelope d (rowCount d n+n)
  let inp : Inputs := ⟨sizeInput n++wordBits y,[],[],[]⟩
  have hc : TesterEnvelopeCovers d n M := testerEnvelope_covers d n (by omega)
  obtain ⟨t₁,c₁,ht₁,h₁,hcore,hout,hh0,hh1,hmarks⟩ :=
    TesterFrontend.program_stops d n M hd hn inp y rfl hc
  have hq0 : 0 < fieldSize d n := fieldSize_pos d n
  have hprod : rowCount d n*rowCount d n*fieldSize d n ≤ M := by have := hc.gram;omega
  have hmatrix : rowCount d n*rowCount d n ≤ M :=
    (Nat.le_mul_of_pos_right _ hq0).trans hprod
  obtain ⟨t₂,c₂,ht₂,h₂,hbuild⟩ := TesterGram.program_stops d (fieldExponent d n)
    (fieldExponent_pos d n) (auxiliaryDegree (fieldSize d n) d) M (by have := hc.two;omega)
    (fun z => decide (y z≠0)) inp c₁.store hcore hh0 (hmarks 0) (hmarks 1)
    hc.digitSum hc.word hmatrix
  have hconstruct : (TesterGram.construct d).Stops inp
      ((TesterPrefix.initialStore d).toCfg (TesterGram.construct d).entry)
      (t₁+1+t₂) (c₂.mapPC (TapeProgram.rightLabel _)) := h₁.seq h₂
  have hlarge : 1 < rowCount d n := by
    have hqrow : fieldSize d n ≤ rowCount d n := Nat.le_self_pow (by omega) _
    have := fieldSize_ge_two d n
    omega
  have hready : TesterBackendComplete.Ready (fieldExponent d n) (fieldExponent_pos d n)
      (rowCount d n) M (TesterAssembly.view d c₂.store) := by
    refine ⟨?_,?_,?_,?_,?_,?_,hlarge,hprod,?_,?_,hbuild.marked,hbuild.spareMarked⟩
    · intro r
      exact hbuild.core.bounded (low d r)
    · exact hbuild.core.environment.cardinal
    · exact hbuild.core.environment.square
    · exact hbuild.core.environment.length
    · exact hbuild.core.environment.modulus
    · exact hbuild.core.size
    · change c₂.bufferHead 0 ≤ (M+1)^2
      have hh : c₂.bufferHead 0 ≤ M := hbuild.head.trans_le hc.gram
      nlinarith
    · exact hbuild.spareHead.trans hh1
  have htable : TapeArrays.ThermometerTable c₂.store 0 (fieldSize d n)
      (fun k : Fin (rowCount d n*rowCount d n) => GaussianProgram.flatEntry (binaryTestTable d n y) k.val) :=
    hbuild.table
  have houtput : c₂.output=[] := hbuild.output.trans hout
  obtain ⟨t,e,ht,he,heo⟩ := TesterAssembly.program_stops_of_construct θ hθ d n M inp
    (TesterPrefix.initialStore d) y (t₁+1+t₂) (c₂.mapPC (TapeProgram.rightLabel _)) hconstruct
    hready htable houtput
  refine ⟨t,e,?_,he,heo⟩
  change t₂ ≤ programTime d M (rowCount d n) at ht₂
  have hf := TesterFrontend.time_le_clock d n M
  have hg := programTime_mono_m d M (show rowCount d n ≤ rowCount d n+n by omega)
  unfold clock
  dsimp only [M] at *
  omega

end ExpandingCodes.Computation.TesterImplementation

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation

theorem binary_tester_implementation_source (θ : ℚ)
    (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2) :
    TesterImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) := by
  let d := dimension (θ : ℝ)
  have hd : 4 ≤ d := dimension_ge_four _ hθ
  have hθ1 : θ ≤ 1 := by exact_mod_cast (show (θ : ℝ) ≤ 1 by linarith [hθ.2])
  apply binary_tester_of_source θ (TesterAssembly.program θ d) (TesterImplementation.clock θ d) 2
    (TesterImplementation.clock_polynomial θ d)
  intro n hn y
  obtain ⟨t,e,ht,he,heo⟩ := TesterImplementation.source_stops θ hθ1 d n hd hn y
  have hr := he.exec.iterate
  change (TesterAssembly.program θ d).run ⟨sizeInput n++wordBits y,[],[],[]⟩ t=e at hr
  exact ⟨t,ht,by rw [hr];exact he.halted,by rw [hr];exact heo⟩


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

open ExpandingCodes.PolynomialStretch in
theorem solution (θ : ℚ)
    (hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1/2) :
    TesterImplementation θ (fun n => binaryGeometry (dimension (θ : ℝ)) n) := by
  exact ExpandingCodes.PolynomialStretch.binary_tester_implementation_source θ hθ
