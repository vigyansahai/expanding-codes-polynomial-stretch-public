import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic

set_option autoImplicit false

namespace ExpandingCodes.Computation.Gaussian

variable {F : Type*} [Field F] [DecidableEq F]

/-- Eager, explicitly indexed storage. No whole table is packed into a natural. -/
abbrev Table (F : Type*) (m n : ℕ) := Vector (Vector F n) m

def toMatrix {m n : ℕ} (A : Table F m n) : Matrix (Fin m) (Fin n) F :=
  fun i j => A[i.val][j.val]

def ofMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) : Table F m n :=
  Vector.ofFn fun i => Vector.ofFn fun j => A i j

omit [Field F] [DecidableEq F] in
@[simp] theorem toMatrix_ofMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    toMatrix (ofMatrix A) = A := by
  ext i j
  simp [toMatrix, ofMatrix]

/-- Deterministic row-major list of cells, of length exactly m*n. -/
def cells (m n : ℕ) : List (Fin m × Fin n) :=
  (List.finRange m).flatMap fun i => (List.finRange n).map fun j => (i,j)

@[simp] theorem length_cells (m n : ℕ) : (cells m n).length = m*n := by
  simp [cells, List.length_flatMap, List.length_finRange]

@[simp] theorem mem_cells {m n : ℕ} (p : Fin m × Fin n) : p ∈ cells m n := by
  simp [cells]

/-- Bounded search, inspecting at most m*n entries. -/
def pivot {m n : ℕ} (A : Table F m n) : Option (Fin m × Fin n) :=
  (cells m n).find? fun p => toMatrix A p.1 p.2 != 0

theorem pivot_some {m n : ℕ} {A : Table F m n} {p : Fin m × Fin n}
    (h : pivot A = some p) : toMatrix A p.1 p.2 ≠ 0 := by
  have := List.find?_some h
  simpa using this

theorem pivot_none {m n : ℕ} {A : Table F m n}
    (h : pivot A = none) : toMatrix A = 0 := by
  ext i j
  have hh := List.find?_eq_none.mp h (i,j) (mem_cells (i,j))
  simpa using hh

/-- Swap a chosen row and column to the origin, then eliminate both. This
eagerly writes exactly m*n entries, using one inverse and three field
operations per entry. The inverse is shared outside the materialization. -/
def schur {m n : ℕ} (A : Table F (m+1) (n+1))
    (p : Fin (m+1) × Fin (n+1)) : Table F m n :=
  let B := toMatrix A
  let aInv := (B p.1 p.2)⁻¹
  ofMatrix fun i j =>
    B (p.1.succAbove i) (p.2.succAbove j) -
      B (p.1.succAbove i) p.2 * aInv * B p.1 (p.2.succAbove j)

/-- Actual deterministic elimination, recursing on a strictly smaller table.
The result is the number of successful nonzero pivots. -/
def rank : {m n : ℕ} → Table F m n → ℕ
  | 0, _, _ => 0
  | _+1, 0, _ => 0
  | _m+1, _n+1, A =>
      match pivot A with
      | none => 0
      | some p => rank (schur A p) + 1

theorem rank_le_min {m n : ℕ} (A : Table F m n) : rank A ≤ min m n := by
  induction m generalizing n with
  | zero => simp [rank]
  | succ m ih =>
    cases n with
    | zero => simp [rank]
    | succ n =>
      have he : min (m+1) (n+1) = min m n + 1 := by omega
      simp only [rank, he]
      split
      · omega
      · exact Nat.succ_le_succ (ih _)

/-- The same finite search, returning the exact number of field comparisons.
The pair is computed in one traversal. -/
def scan {m n : ℕ} (A : Table F m n) :
    List (Fin m × Fin n) → Option (Fin m × Fin n) × ℕ
  | [] => (none, 0)
  | p :: ps =>
      if toMatrix A p.1 p.2 != 0 then (some p, 1)
      else let r := scan A ps; (r.1, r.2+1)

theorem scan_result {m n : ℕ} (A : Table F m n) (ps : List (Fin m × Fin n)) :
    (scan A ps).1 = ps.find? (fun p => toMatrix A p.1 p.2 != 0) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      cases hb : (toMatrix A p.1 p.2 != 0) <;> simp [scan, List.find?, hb, ih]

theorem scan_cost_le {m n : ℕ} (A : Table F m n) (ps : List (Fin m × Fin n)) :
    (scan A ps).2 ≤ ps.length := by
  induction ps with
  | nil => simp [scan]
  | cons p ps ih =>
      simp only [scan, List.length_cons]
      split <;> simp only <;> omega

/-- Abstract resource counters. Field arithmetic consists of one inverse per
pivot and two multiplications and one subtraction per new Schur entry.
Array reads/writes count field entries, not physical bit cells. `enumerated`
also charges every cell of the row-major index list, including unused suffixes.
Refinement to encoded arithmetic, bit buffers, and counter moves is required. -/
structure Work where
  comparisons : ℕ := 0
  inverses : ℕ := 0
  arithmetic : ℕ := 0
  reads : ℕ := 0
  writes : ℕ := 0
  enumerated : ℕ := 0
  deriving Repr, DecidableEq

def Work.total (w : Work) : ℕ :=
  w.comparisons+w.inverses+w.arithmetic+w.reads+w.writes+w.enumerated

def Work.add (a b : Work) : Work :=
  ⟨a.comparisons+b.comparisons, a.inverses+b.inverses,
    a.arithmetic+b.arithmetic, a.reads+b.reads,
    a.writes+b.writes, a.enumerated+b.enumerated⟩

@[simp] theorem Work.total_add (a b : Work) :
    (a.add b).total = a.total + b.total := by
  simp [Work.total, Work.add]; omega

def zeroWork (s cells : ℕ) : Work := ⟨s, 0, 0, s, 0, cells⟩

def pivotWork (m n s : ℕ) : Work :=
  ⟨s, 1, 3*m*n, s+3*m*n+1, m*n, (m+1)*(n+1)⟩

/-- Resource-instrumented executable elimination. Its search result, reduced
table, rank, and resource record are all explicit deterministic data. -/
def run : {m n : ℕ} → Table F m n → ℕ × Work
  | 0, _, _ => (0, {})
  | _+1, 0, _ => (0, {})
  | m+1, n+1, A =>
      let s := scan A (cells (m+1) (n+1))
      match s.1 with
      | none => (0, zeroWork s.2 ((m+1)*(n+1)))
      | some p =>
          let r := run (schur A p)
          (r.1+1, (pivotWork m n s.2).add r.2)

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

theorem run_work_le {m n : ℕ} (A : Table F m n) :
    (run A).2.total ≤ 12*m*n*min m n := by
  induction m generalizing n with
  | zero => simp [run, Work.total]
  | succ m ih =>
    cases n with
    | zero => simp [run, Work.total]
    | succ n =>
      have hs : (scan A (cells (m+1) (n+1))).2 ≤ (m+1)*(n+1) := by
        simpa using scan_cost_le A (cells (m+1) (n+1))
      have he : min (m+1) (n+1) = min m n + 1 := by omega
      have hpos : 1 ≤ (m+1)*(n+1) := by nlinarith
      simp only [run]
      split
      · simp only [zeroWork, Work.total]
        rw [he]
        nlinarith [Nat.zero_le (min m n)]
      next p _ =>
        have hi := ih (schur A p)
        dsimp only [Work.total] at hi
        have hm : 12*m*n*min m n ≤ 12*(m+1)*(n+1)*min m n :=
          Nat.mul_le_mul_right _ (by nlinarith)
        rw [Work.total_add]
        simp only [pivotWork, Work.total]
        rw [he]
        nlinarith

theorem run_field_operations_le {m n : ℕ} (A : Table F m n) :
    (run A).2.inverses + (run A).2.arithmetic ≤ 12*m*n*min m n := by
  have h := run_work_le A
  unfold Work.total at h
  omega

theorem run_array_operations_le {m n : ℕ} (A : Table F m n) :
    (run A).2.reads + (run A).2.writes + (run A).2.enumerated ≤
      12*m*n*min m n := by
  have h := run_work_le A
  unfold Work.total at h
  omega

#print axioms run_work_le

end ExpandingCodes.Computation.Gaussian
