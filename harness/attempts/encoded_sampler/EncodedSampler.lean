import ExpandingCodes.Computation.SamplerTables
import ExpandingCodes.Computation.EncodedTester
import Definitions.Def_ExpandingCodes_PolynomialStretch_OperationalFamily

set_option autoImplicit false
open scoped BigOperators

namespace ExpandingCodes.Computation.EncodedSampler

open EncodedGaussian EncodedTester
open ExpandingCodes.PolynomialStretch

variable {q d k b : ℕ}

def fixed (O : Operations (Fin q)) (a : Fin q) (z : Fin d → Fin q) : Fin q × ℕ :=
  sum O (List.ofFn fun j : Fin d =>
    let p := power O a j.val
    (O.mul p.1 (z j), p.2+1))

def linear (O : Operations (Fin q)) (s z : Fin d → Fin q) : Fin q × ℕ :=
  sum O (List.ofFn fun j : Fin d => (O.mul (s j) (z j), 1))

def address (O : Operations (Fin q)) (s : Fin (2*k*q*d) → Fin q)
    (i : Fin k) (z : Fin d → Fin q) : (Fin q × Fin q × Fin q) × ℕ :=
  let a := fixed O (if h : i.val < q then ⟨i.val,h⟩ else O.zero) z
  let u := linear O (fun j => s (SamplerTables.flatFour 2 k q d (((0,i),a.1),j))) z
  let v := linear O (fun j => s (SamplerTables.flatFour 2 k q d (((1,i),a.1),j))) z
  ((a.1,u.1,v.1),a.2+u.2+v.2)

def neighbor (O : Operations (Fin q)) (s : Fin (2*k*q*d) → Fin q)
    (h : Fin (k*q*q*q) → Fin b) (i : Fin k) (z : Fin d → Fin q) : Fin b :=
  let a := (address O s i z).1
  h (SamplerTables.flatFour k q q q (((i,a.1),a.2.1),a.2.2))

/-- Executable finite-index generator. Only finite-index arithmetic and field
code operations occur; quotient-field values enter only its semantic proof. -/
def matrix (n : ℕ) (O : Operations (Fin q)) (s : Fin (2*k*q*d) → Fin q)
    (h : Fin (k*q*q*q) → Fin b) : Generator (q^d) n :=
  fun z j => if ∃ i : Fin k,
    j.val = i.val*b+(neighbor O s h i (digits q d z)).val then 1 else 0

theorem fixed_cost_le (O : Operations (Fin q)) (a : Fin q) (z : Fin d → Fin q) :
    (fixed O a z).2 ≤ d*(d+2) := by
  have hh := sum_cost_le O (List.ofFn fun j : Fin d =>
    (O.mul (power O a j.val).1 (z j), (power O a j.val).2+1)) (d+1) (by
      intro x hx
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
      simp only [power_cost]
      omega)
  simpa [fixed] using hh

theorem linear_cost_le (O : Operations (Fin q)) (s z : Fin d → Fin q) :
    (linear O s z).2 ≤ 2*d := by
  have hh := sum_cost_le O (List.ofFn fun j : Fin d => (O.mul (s j) (z j), 1)) 1 (by
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    exact le_rfl)
  simpa [linear, Nat.mul_comm] using hh

theorem address_cost_le (O : Operations (Fin q)) (s : Fin (2*k*q*d) → Fin q)
    (i : Fin k) (z : Fin d → Fin q) : (address O s i z).2 ≤ d*(d+6) := by
  have ha := fixed_cost_le O (if h : i.val < q then ⟨i.val,h⟩ else O.zero) z
  have hu := linear_cost_le O
    (fun j => s (SamplerTables.flatFour 2 k q d (((0,i),
      (fixed O (if h : i.val < q then ⟨i.val,h⟩ else O.zero) z).1),j))) z
  have hv := linear_cost_le O
    (fun j => s (SamplerTables.flatFour 2 k q d (((1,i),
      (fixed O (if h : i.val < q then ⟨i.val,h⟩ else O.zero) z).1),j))) z
  change (fixed O _ z).2 + (linear O _ z).2 + (linear O _ z).2 ≤ _
  nlinarith

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

/-- The finite-index matrix from exactly the physical random-reader values.
This is a data function, not a source-runtime claim. -/
def binarySamplerFromInput (d n k beta : ℕ) (inp : NKtLB.Inputs) :
    Generator (rowCount d n) n :=
  EncodedSampler.matrix n
    (BinaryField.indexOperations (fieldExponent d n) (fieldExponent_pos d n))
    (RandomTables.sampledValues inp (SamplerTables.formEntries d n k) (fieldExponent d n) 0)
    (RandomTables.sampledValues inp (SamplerTables.hashEntries d n k) beta
      (SamplerTables.formEntries d n k * fieldExponent d n))

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

#print axioms encodedSampler_address
#print axioms encodedSampler_matrix
end ExpandingCodes.PolynomialStretch
