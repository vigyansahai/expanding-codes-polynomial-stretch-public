import ExpandingCodes.Computation.EncodedSampler
import ExpandingCodes.Computation.SamplerOdometer

set_option autoImplicit false

namespace ExpandingCodes.Computation.SamplerRows
open ExpandingCodes.PolynomialStretch EncodedTester

variable {q d k b n : ℕ}

def row (O : EncodedGaussian.Operations (Fin q))
    (s : Fin (2*k*q*d) → Fin q) (h : Fin (k*q*q*q) → Fin b)
    (z : Fin (q^d)) : List Bool :=
  List.ofFn fun j : Fin n => decide (∃ i : Fin k,
    j.val = i.val*b+(EncodedSampler.neighbor O s h i (digits q d z)).val)

def rowsBefore (O : EncodedGaussian.Operations (Fin q))
    (s : Fin (2*k*q*d) → Fin q) (h : Fin (k*q*q*q) → Fin b)
    (r : ℕ) (hr : r ≤ q^d) : List Bool :=
  (List.ofFn fun i : Fin r => row (n := n) O s h ⟨i.val,lt_of_lt_of_le i.isLt hr⟩).flatten

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

@[simp] theorem prefix_zero (O : EncodedGaussian.Operations (Fin q))
    (s : Fin (2*k*q*d) → Fin q) (h : Fin (k*q*q*q) → Fin b)
    (hr : 0 ≤ q^d) : rowsBefore (n := n) O s h 0 hr = [] := by
  simp [rowsBefore]

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

#print axioms readings_eq_digits
end ExpandingCodes.Computation.SamplerRows
