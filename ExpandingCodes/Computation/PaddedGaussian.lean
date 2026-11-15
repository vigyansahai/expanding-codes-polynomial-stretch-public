import ExpandingCodes.Computation.GaussianProgram
import ExpandingCodes.Computation.EncodedTester

set_option autoImplicit false

namespace ExpandingCodes.Computation.PaddedGaussian
open GaussianProgram EncodedGaussian
open ExpandingCodes.PolynomialStretch

variable {q m n : ℕ}

theorem scan_nonzero_lt (A : Gaussian.Table (Fin q) m n)
    (h : (scanResult (flatEntry A) 0 (m*n)).2 ≠ 0) :
    (scanResult (flatEntry A) 0 (m*n)).1 < m*n := by
  rcases scanResult_spec (flatEntry A) 0 (m*n) with hs | hs
  · exact (h hs.1).elim
  · simpa using hs.2.1

/-- The exact first-nonzero flat scan used by the physical Gaussian source.
The dependent bound constructs a finite coordinate, not a pivot choice oracle. -/
def pivot (A : Gaussian.Table (Fin q) m n) : Option (Fin m × Fin n) :=
  let s := scanResult (flatEntry A) 0 (m*n)
  if h : s.2 = 0 then none else
    some (finProdFinEquiv.symm ⟨s.1,scan_nonzero_lt A h⟩)

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

/-- Fixed-dimension eager elimination. Each iteration uses the same physical
array dimensions; the fuel bounds only the number of actual pivot attempts. -/
def run (O : Operations (Fin q)) : ℕ → Gaussian.Table (Fin q) m n → ℕ
  | 0,_ => 0
  | fuel+1,A => match pivot A with
    | none => 0
    | some p => run O fuel (paddedSchur O A p)+1

structure State (q m n : ℕ) where
  table : Gaussian.Table (Fin q) m n
  rank : ℕ
  done : Bool

/-- Logical state of one physical driver round. A no-pivot matrix is retained
with a done bit; all later rounds are exact fixed points. -/
def step (O : Operations (Fin q)) (s : State q m n) : State q m n :=
  if s.done then s else match pivot s.table with
    | none => {s with done := true}
    | some p => ⟨paddedSchur O s.table p,s.rank+1,false⟩

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

theorem iterate_rows_correct (h : Interpretation O decode) (hz : O.zero.val = 0)
    (A : Gaussian.Table (Fin q) m n) :
    ((step O)^[m] (⟨A,0,false⟩ : State q m n)).rank =
      (Gaussian.toMatrix (mapTable decode A)).rank := by
  rw [iterate_rank]
  simpa using run_rows_correct h hz A

theorem binary_iterate_rank (d n : ℕ) (y : Word (rowCount d n)) :
    ((step (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n)))^[rowCount d n]
      (⟨binaryTestTable d n y,0,false⟩ : State (fieldSize d n) (rowCount d n) (rowCount d n))).rank =
        (testMatrix (binaryGeometry d n) y).rank := by
  erw [iterate_rank]
  simpa using binaryTest_rank d n y

#print axioms pivot_some_iff
#print axioms run_correct
#print axioms binaryTest_rank
#print axioms binary_iterate_rank
end ExpandingCodes.Computation.PaddedGaussian
