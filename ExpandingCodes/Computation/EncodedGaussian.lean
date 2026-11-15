import ExpandingCodes.Computation.GaussianCorrectness
import ExpandingCodes.Computation.BinaryField
import Mathlib.Algebra.CharP.Two

set_option autoImplicit false

namespace ExpandingCodes.Computation.EncodedGaussian

open Gaussian

/-- Executable operations on finite field codes. No field structure or
noncomputable quotient operation is used by the encoded algorithm. -/
structure Operations (α : Type*) where
  zero : α
  one : α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  inv : α → α

structure Interpretation {α F : Type*} [Field F]
    (O : Operations α) (decode : α → F) : Prop where
  injective : Function.Injective decode
  zero : decode O.zero = 0
  one : decode O.one = 1
  add : ∀ a b, decode (O.add a b) = decode a + decode b
  sub : ∀ a b, decode (O.sub a b) = decode a - decode b
  mul : ∀ a b, decode (O.mul a b) = decode a * decode b
  inv : ∀ a, decode (O.inv a) = (decode a)⁻¹

def mapTable {α β : Type*} (f : α → β) {m n : ℕ} (A : Table α m n) : Table β m n :=
  ofMatrix fun i j => f (toMatrix A i j)

@[simp] theorem toMatrix_mapTable {α β : Type*} (f : α → β) {m n : ℕ}
    (A : Table α m n) (i : Fin m) (j : Fin n) :
    toMatrix (mapTable f A) i j = f (toMatrix A i j) := by
  simp [mapTable, toMatrix, ofMatrix]

variable {α : Type*} [DecidableEq α]

def scan (O : Operations α) {m n : ℕ} (A : Table α m n) :
    List (Fin m × Fin n) → Option (Fin m × Fin n) × ℕ
  | [] => (none, 0)
  | p :: ps =>
      if toMatrix A p.1 p.2 != O.zero then (some p, 1)
      else let r := scan O A ps; (r.1, r.2+1)

def schur (O : Operations α) {m n : ℕ} (A : Table α (m+1) (n+1))
    (p : Fin (m+1) × Fin (n+1)) : Table α m n :=
  let B := toMatrix A
  let aInv := O.inv (B p.1 p.2)
  ofMatrix fun i j =>
    O.sub (B (p.1.succAbove i) (p.2.succAbove j))
      (O.mul (O.mul (B (p.1.succAbove i) p.2) aInv)
        (B p.1 (p.2.succAbove j)))

/-- Actual finite-code elimination. The recursive argument loses one row and
column after each successful pivot, and the resulting arrays are eager. -/
def run (O : Operations α) : {m n : ℕ} → Table α m n → ℕ × Work
  | 0, _, _ => (0, {})
  | _+1, 0, _ => (0, {})
  | m+1, n+1, A =>
      let s := scan O A (cells (m+1) (n+1))
      match s.1 with
      | none => (0, zeroWork s.2 ((m+1)*(n+1)))
      | some p =>
          let r := run O (schur O A p)
          (r.1+1, (pivotWork m n s.2).add r.2)

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

theorem run_work_le (h : Interpretation O decode) {m n : ℕ} (A : Table α m n) :
    (run O A).2.total ≤ 12*m*n*min m n := by
  rw [run_decode h]
  exact Gaussian.run_work_le _

end ExpandingCodes.Computation.EncodedGaussian

namespace ExpandingCodes.PolynomialStretch.BinaryField

open Computation.EncodedGaussian BinaryPolynomial

def zeroIndex (ell : ℕ) : Fin (2 ^ ell) := (indexEquiv ell).symm (zero ell)

def oneIndex (ell : ℕ) : Fin (2 ^ ell) := (indexEquiv ell).symm (one ell)

def indexOperations (ell : ℕ) (h : 0 < ell) : Operations (Fin (2 ^ ell)) where
  zero := zeroIndex ell
  one := oneIndex ell
  add := addIndex ell
  sub := addIndex ell
  mul i j := multiplyIndex ell h (selectedIndex ell h) (indexEquiv ell i) (indexEquiv ell j)
  inv := inverseIndex ell h

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

#print axioms indexOperations_interpretation
#print axioms Computation.EncodedGaussian.run_correct
#print axioms Computation.EncodedGaussian.run_work_le

end ExpandingCodes.PolynomialStretch.BinaryField
