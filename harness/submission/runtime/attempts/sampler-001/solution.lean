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








theorem flatFour_val {a b c d : ℕ} (i : Fin a) (j : Fin b) (u : Fin c) (v : Fin d) :
    (flatFour a b c d (((i,j),u),v)).val =
      v.val + d * (u.val + c * (j.val + b*i.val)) := by
  simp [flatFour, finProdFinEquiv]

































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


section FlattenModule54





set_option autoImplicit false

namespace ExpandingCodes.Computation.Gaussian

variable {F : Type*} [Field F] [DecidableEq F]







































































































































































































end ExpandingCodes.Computation.Gaussian

end FlattenModule54


section FlattenModule55







set_option autoImplicit false

namespace ExpandingCodes.Computation.Gaussian

open Matrix Module LinearMap
open scoped Matrix

variable {F : Type*} [Field F]










































































































































end ExpandingCodes.Computation.Gaussian

end FlattenModule55

/-! Inlined whole module: ExpandingCodes.Computation.EncodedGaussian -/
section FlattenModule56




set_option autoImplicit false

namespace ExpandingCodes.Computation.EncodedGaussian

open Gaussian





























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


section FlattenModule57



set_option autoImplicit false

open scoped BigOperators

namespace ExpandingCodes.PolynomialStretch















































































































































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


section FlattenModule77






set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterGram
open NKtLB























































































































































































































































































































































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


section FlattenModule79




set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianProgram

open NKtLB TapeArrays







































































































section SearchLoop

variable {R B L : ℕ}

































































































































end SearchLoop




























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end ExpandingCodes.Computation.GaussianProgram

end FlattenModule79


section FlattenModule80




set_option autoImplicit false
namespace ExpandingCodes.Computation.TesterGram
open NKtLB
open ExpandingCodes.PolynomialStretch

















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































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


section FlattenModule85


set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianGrid

open NKtLB GaussianProgram



































































































































































































































































































































































































































































































































































































































































































































































































































































































end ExpandingCodes.Computation.GaussianGrid

end FlattenModule85


section FlattenModule86



set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianPivot
open NKtLB GaussianProgram
open ExpandingCodes.PolynomialStretch
























































































































































































































































































































































end ExpandingCodes.Computation.GaussianPivot

end FlattenModule86


section FlattenModule87



set_option autoImplicit false

namespace ExpandingCodes.Computation.PaddedGaussian
open GaussianProgram EncodedGaussian
open ExpandingCodes.PolynomialStretch

variable {q m n : ℕ}












































































































variable {F : Type*} [Field F] [DecidableEq F]
variable {O : Operations (Fin q)} {decode : Fin q → F}










































































end ExpandingCodes.Computation.PaddedGaussian

end FlattenModule87


section FlattenModule88




set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianDriver

open NKtLB GaussianProgram GaussianGrid

section Branch
variable {R B L K : ℕ}







































































end Branch



























































































































































































































































































































































































































































































































































































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

theorem sizeStageTime_polynomial (d : ℕ) : PolynomialBound (sizeStageTime d) := by
  have hp : ParameterPrograms.PolynomialMajorant (fun n => 2*n+4+setupTimeBound d (n+1)) :=
    (((ParameterPrograms.PolynomialMajorant.const 2).mul ParameterPrograms.PolynomialMajorant.id).add
      (ParameterPrograms.PolynomialMajorant.const 4)).add
      ((setup_bounds_polynomial d).1.comp
        (ParameterPrograms.PolynomialMajorant.id.add (ParameterPrograms.PolynomialMajorant.const 1)))
  exact hp.toPolynomialBound

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
