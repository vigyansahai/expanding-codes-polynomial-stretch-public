import Definitions.Def_NKtLB_Machine

set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

/-- Tape equality ignores the finite list's trailing blank storage. -/
def TapeRep (l : List Sym) (f : ℕ → Sym) : Prop :=
  ∀ k, l.getD k Sym.blank = f k

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

/-- A counter occupies one tape, with a bottom marker at zero and its head at its value. -/
def unary (n k : ℕ) : Sym :=
  if k = 0 then .bot else if k ≤ n then .one else .blank

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

 theorem unary_init : TapeRep (Machine.writeAt [] 0 .bot) (unary 0) := by
  intro k
  rw [getD_writeAt]
  by_cases hk : k = 0 <;> simp [unary, hk]

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

/-- The finite transition table can test zero solely from the scanned symbol. -/
 theorem unary_zero_test {l : List Sym} {n : ℕ} (hr : TapeRep l (unary n)) :
    l.getD n .blank = .bot ↔ n = 0 := by
  rw [hr]
  cases n <;> simp

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

#print axioms getD_writeAt
#print axioms unary_inc_two_steps
#print axioms unary_dec_one_step
end ExpandingCodes.Computation
