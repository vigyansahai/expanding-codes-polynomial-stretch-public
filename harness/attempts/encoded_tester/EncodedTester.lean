import ExpandingCodes.Computation.EncodedGaussian
import ExpandingCodes.Algebra.FullEvaluation
import ExpandingCodes.Construction.BinaryGeometry

set_option autoImplicit false

open scoped BigOperators

namespace ExpandingCodes.Computation.EncodedTester

open EncodedGaussian Gaussian

variable {α : Type*}

/-- The second component counts actual calls to encoded field operations. -/
def power (O : Operations α) (x : α) : ℕ → α × ℕ
  | 0 => (O.one, 0)
  | k+1 => let r := power O x k; (O.mul r.1 x, r.2+1)

def product (O : Operations α) : List (α × ℕ) → α × ℕ
  | [] => (O.one, 0)
  | a :: as => let r := product O as; (O.mul a.1 r.1, a.2+r.2+1)

def sum (O : Operations α) : List (α × ℕ) → α × ℕ
  | [] => (O.zero, 0)
  | a :: as => let r := sum O as; (O.add a.1 r.1, a.2+r.2+1)

@[simp] theorem power_cost (O : Operations α) (x : α) (k : ℕ) :
    (power O x k).2 = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [power, ih]

theorem product_cost_le (O : Operations α) (xs : List (α × ℕ)) (B : ℕ)
    (h : ∀ x ∈ xs, x.2 ≤ B) : (product O xs).2 ≤ xs.length*(B+1) := by
  induction xs with
  | nil => simp [product]
  | cons a as ih =>
    have ha := h a (by simp)
    have hi := ih (fun x hx => h x (by simp [hx]))
    simp only [product, List.length_cons]
    nlinarith

theorem sum_cost_le (O : Operations α) (xs : List (α × ℕ)) (B : ℕ)
    (h : ∀ x ∈ xs, x.2 ≤ B) : (sum O xs).2 ≤ xs.length*(B+1) := by
  induction xs with
  | nil => simp [sum]
  | cons a as ih =>
    have ha := h a (by simp)
    have hi := ih (fun x hx => h x (by simp [hx]))
    simp only [sum, List.length_cons]
    nlinarith

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

/-- Explicit base-q digit extraction; the fixed source program must refine
this bounded enumeration using runtime quotient/remainder loops. -/
def digits (q d : ℕ) : Fin (q^d) ≃ (Fin d → Fin q) := finFunctionFinEquiv.symm

def evaluation {q d : ℕ} (O : Operations (Fin q)) (R : ℕ)
    (a z : Fin (q^d)) : Fin q × ℕ :=
  if (∑ i, (digits q d a i).val) ≤ R then
    product O (List.ofFn fun i : Fin d =>
      power O (digits q d z i) (digits q d a i).val)
  else (O.zero, 0)

theorem evaluation_cost_le {q d : ℕ} (O : Operations (Fin q)) (R : ℕ)
    (a z : Fin (q^d)) : (evaluation O R a z).2 ≤ d*(q+1) := by
  unfold evaluation
  split
  · have h := product_cost_le O
      (List.ofFn fun i : Fin d => power O (digits q d z i) (digits q d a i).val) q (by
        intro x hx
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        simpa using (Nat.le_of_lt (digits q d a i).isLt))
    simpa using h
  · simp

theorem evaluation_decode {q d : ℕ} {O : Operations (Fin q)} {f : Fin q → F}
    (h : Interpretation O f) (R : ℕ) (a z : Fin (q^d)) :
    f (evaluation O R a z).1 =
      if (∑ i, (digits q d a i).val) ≤ R then
        ∏ i, (f (digits q d z i)) ^ (digits q d a i).val else 0 := by
  unfold evaluation
  split
  · simp [product_decode h, List.map_ofFn, power_decode h, List.prod_ofFn]
  · exact h.zero

/-- Recompute two bounded monomials per point. Reusing an evaluation table is
unnecessary for polynomial time and would complicate physical storage. -/
def term {q d : ℕ} (O : Operations (Fin q)) (R : ℕ)
    (y : Fin (q^d) → Bool) (a b z : Fin (q^d)) : Fin q × ℕ :=
  if y z then
    let x := evaluation O R a z
    let w := evaluation O R b z
    (O.mul x.1 w.1, x.2+w.2+1)
  else (O.zero, 0)

def entry {q d : ℕ} (O : Operations (Fin q)) (R : ℕ)
    (y : Fin (q^d) → Bool) (a b : Fin (q^d)) : Fin q × ℕ :=
  sum O (List.ofFn fun z : Fin (q^d) => term O R y a b z)

def table {q d : ℕ} (O : Operations (Fin q)) (R : ℕ)
    (y : Fin (q^d) → Bool) : Table (Fin q) (q^d) (q^d) :=
  ofMatrix fun a b => (entry O R y a b).1

def constructionCost {q d : ℕ} (O : Operations (Fin q)) (R : ℕ)
    (y : Fin (q^d) → Bool) : ℕ := ∑ a, ∑ b, (entry O R y a b).2

theorem term_cost_le {q d : ℕ} (O : Operations (Fin q)) (R : ℕ)
    (y : Fin (q^d) → Bool) (a b z : Fin (q^d)) :
    (term O R y a b z).2 ≤ 2*d*(q+1)+1 := by
  unfold term
  split
  · have ha := evaluation_cost_le O R a z
    have hb := evaluation_cost_le O R b z
    dsimp only
    nlinarith
  · simp

theorem entry_cost_le {q d : ℕ} (O : Operations (Fin q)) (R : ℕ)
    (y : Fin (q^d) → Bool) (a b : Fin (q^d)) :
    (entry O R y a b).2 ≤ q^d*(2*d*(q+1)+2) := by
  unfold entry
  have h := sum_cost_le O (List.ofFn fun z : Fin (q^d) => term O R y a b z)
    (2*d*(q+1)+1) (by
      intro x hx
      obtain ⟨z, rfl⟩ := List.mem_ofFn.mp hx
      exact term_cost_le O R y a b z)
  simpa [Nat.add_assoc] using h

theorem constructionCost_le {q d : ℕ} (O : Operations (Fin q)) (R : ℕ)
    (y : Fin (q^d) → Bool) :
    constructionCost O R y ≤ (q^d)^3*(2*d*(q+1)+2) := by
  have h : constructionCost O R y ≤
      ∑ _a : Fin (q^d), ∑ _b : Fin (q^d), q^d*(2*d*(q+1)+2) := by
    apply Finset.sum_le_sum
    intro a _
    exact Finset.sum_le_sum (fun b _ => entry_cost_le O R y a b)
  simpa [constructionCost, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

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

/-- Explicit rectangular exponent enumeration, followed only by proof casts
of individual digits. It enumerates every canonical bounded exponent tuple. -/
def encodedExponentOrder {d n : ℕ} (g : Geometry d n) :
    Fin (rowCount d n) ≃ (Fin d → Fin (Fintype.card g.F)) :=
  (digits (fieldSize d n) d).trans
    (Equiv.piCongrRight fun _ => finCongr (geometry_card g).symm)

@[simp] theorem encodedExponentOrder_val {d n : ℕ} (g : Geometry d n)
    (a : Fin (rowCount d n)) (i : Fin d) :
    (encodedExponentOrder g a i).val = (digits (fieldSize d n) d a i).val := rfl

def binaryTestTable (d n : ℕ) (y : Word (rowCount d n)) :
    Gaussian.Table (Fin (fieldSize d n)) (rowCount d n) (rowCount d n) :=
  table (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n))
    (auxiliaryDegree (fieldSize d n) d) (fun z => decide (y z ≠ 0))

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

theorem binaryTestTable_elimination_work (d n : ℕ) (y : Word (rowCount d n)) :
    (EncodedGaussian.run
      (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n))
      (binaryTestTable d n y)).2.total ≤ 12*(rowCount d n)^3 := by
  classical
  simpa [pow_succ, Nat.mul_assoc] using EncodedGaussian.run_work_le
    (BinaryField.indexOperations_interpretation (fieldExponent d n) (fieldExponent_pos d n))
    (binaryTestTable d n y)

theorem binaryTestTable_construction_work (d n : ℕ) (y : Word (rowCount d n)) :
    constructionCost
      (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n))
      (auxiliaryDegree (fieldSize d n) d) (fun z => decide (y z ≠ 0)) ≤
      (rowCount d n)^3*(2*d*(fieldSize d n+1)+2) := constructionCost_le _ _ _

/-- Executable finite-code tester. Physical TapeProgram refinement, parsing,
and a source-step bound are separate obligations. -/
def binaryRankTest (θ : ℚ) (d n : ℕ) (y : Word (rowCount d n)) : Bool :=
  let η : ℚ := 1/2-θ/2
  decide ((EncodedGaussian.run
    (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n))
    (binaryTestTable d n y)).1*η.den ≤ η.num.toNat*rowCount d n)

theorem binaryRankTest_eq (θ : ℚ) (hθ : θ ≤ 1) (d n : ℕ)
    (y : Word (rowCount d n)) :
    binaryRankTest θ d n y = rankTest (θ : ℝ) (binaryGeometry d n) y := by
  classical
  rw [← rationalRankTest_eq θ hθ]
  simp only [binaryRankTest, rationalRankTest, binaryTestTable_rank, fullTestTable_rank]

#print axioms binaryTestTable_rank
#print axioms binaryRankTest_eq
#print axioms binaryTestTable_construction_work

end ExpandingCodes.PolynomialStretch
