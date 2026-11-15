import Mathlib
import Definitions.Def_CodingTheory

namespace TillichZemor.HGP

open Matrix
open scoped Kronecker

/-- The binary code of a Tanner graph with parity-check matrix `H` (rows = check nodes,
columns = variable nodes): the kernel of `H` (§2, p. 4). -/
def code {C V : Type*} [Fintype V] (H : Matrix C V (ZMod 2)) :
    Submodule (ZMod 2) (V → ZMod 2) :=
  LinearMap.ker H.mulVecLin

/-- Minimum distance of a binary linear code: the least Hamming weight of a nonzero codeword,
with the convention of p. 15 that it is `∞ = ⊤` for the zero code. -/
noncomputable def minDist {ι : Type*} [Fintype ι] (D : Submodule (ZMod 2) (ι → ZMod 2)) : ℕ∞ :=
  ⨅ x ∈ D, ⨅ (_ : x ≠ 0), (hammingNorm x : ℕ∞)

/-- `d_X` of eq. (1), p. 4, for the CSS pair `(A, B) = (𝒞_X, 𝒞_Z)`: the least Hamming weight of a
vector of `A ∖ B^⊥` (`⊤` if there is none). `d_Z` is `cssDist B A`. -/
noncomputable def cssDist {ι : Type*} [Fintype ι] (A B : Submodule (ZMod 2) (ι → ZMod 2)) : ℕ∞ :=
  ⨅ x ∈ A, ⨅ (_ : x ∉ CodingTheory.dualCode (ZMod 2) ι B), (hammingNorm x : ℕ∞)

/-- `k_Q` of eq. (2), p. 4: `dim (A / B^⊥)`, the quotient of `A` by `B^⊥ ∩ A`. -/
noncomputable def cssDim {ι : Type*} [Fintype ι] (A B : Submodule (ZMod 2) (ι → ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) (A ⧸ (CodingTheory.dualCode (ZMod 2) ι B).comap A.subtype)

section Product

variable {V₁ C₁ V₂ C₂ : Type*} [Fintype V₁] [Fintype C₁] [Fintype V₂] [Fintype C₂]
  [DecidableEq V₁] [DecidableEq C₁] [DecidableEq V₂] [DecidableEq C₂]

/-- The parity-check matrix `H_X = (H₁ ⊗ I_{n₂} | I_{r₁} ⊗ H₂ᵀ)` of `𝒞_X(𝒢₁ × 𝒢₂)`
(Definition 3, pp. 7–8; matrix form p. 18). Rows: checks `C₁ × V₂`; columns (qubits):
`(V₁ × V₂) ⊕ (C₁ × C₂)`. -/
def hx (H₁ : Matrix C₁ V₁ (ZMod 2)) (H₂ : Matrix C₂ V₂ (ZMod 2)) :
    Matrix (C₁ × V₂) ((V₁ × V₂) ⊕ (C₁ × C₂)) (ZMod 2) :=
  Matrix.fromCols (H₁ ⊗ₖ (1 : Matrix V₂ V₂ (ZMod 2))) ((1 : Matrix C₁ C₁ (ZMod 2)) ⊗ₖ H₂ᵀ)

/-- The parity-check matrix `H_Z = (I_{n₁} ⊗ H₂ | H₁ᵀ ⊗ I_{r₂})` of `𝒞_Z(𝒢₁ × 𝒢₂)`
(Definition 3, pp. 7–8; matrix form p. 18). Rows: checks `V₁ × C₂`. -/
def hz (H₁ : Matrix C₁ V₁ (ZMod 2)) (H₂ : Matrix C₂ V₂ (ZMod 2)) :
    Matrix (V₁ × C₂) ((V₁ × V₂) ⊕ (C₁ × C₂)) (ZMod 2) :=
  Matrix.fromCols ((1 : Matrix V₁ V₁ (ZMod 2)) ⊗ₖ H₂) (H₁ᵀ ⊗ₖ (1 : Matrix C₂ C₂ (ZMod 2)))

/-- The quantum minimum distance `d_Q = min(d_X, d_Z)` of `𝒬(𝒢₁ × 𝒢₂)` (eq. (1)). -/
noncomputable def quantumDist (H₁ : Matrix C₁ V₁ (ZMod 2)) (H₂ : Matrix C₂ V₂ (ZMod 2)) : ℕ∞ :=
  min (cssDist (code (hx H₁ H₂)) (code (hz H₁ H₂)))
    (cssDist (code (hz H₁ H₂)) (code (hx H₁ H₂)))

/-- The quantum dimension `k_Q = dim(𝒞_X / 𝒞_Z^⊥)` of `𝒬(𝒢₁ × 𝒢₂)` (eq. (2)). -/
noncomputable def quantumDim (H₁ : Matrix C₁ V₁ (ZMod 2)) (H₂ : Matrix C₂ V₂ (ZMod 2)) : ℕ :=
  cssDim (code (hx H₁ H₂)) (code (hz H₁ H₂))

/-- The parity-check matrix of the hypergraph product `𝒢₁ ⊗ 𝒢₂` (Definition 7, p. 12):
variable nodes `V₁ × V₂`, check nodes `(C₁ × V₂) ⊕ (V₁ × C₂)`. -/
def tensorTanner (H₁ : Matrix C₁ V₁ (ZMod 2)) (H₂ : Matrix C₂ V₂ (ZMod 2)) :
    Matrix ((C₁ × V₂) ⊕ (V₁ × C₂)) (V₁ × V₂) (ZMod 2) :=
  Matrix.fromRows (H₁ ⊗ₖ (1 : Matrix V₂ V₂ (ZMod 2))) ((1 : Matrix V₁ V₁ (ZMod 2)) ⊗ₖ H₂)

end Product

/-- The product code `𝒞₁ ⊗ 𝒞₂` (Definition 8, p. 12): the words `x : ι₁ × ι₂ → 𝔽₂`, viewed as
`ι₁ × ι₂` matrices, whose columns `i ↦ x (i, j)` all lie in `D₁` and whose rows
`j ↦ x (i, j)` all lie in `D₂`. -/
def productCode {ι₁ ι₂ : Type*} (D₁ : Submodule (ZMod 2) (ι₁ → ZMod 2))
    (D₂ : Submodule (ZMod 2) (ι₂ → ZMod 2)) : Submodule (ZMod 2) (ι₁ × ι₂ → ZMod 2) :=
  (⨅ j : ι₂, D₁.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : ι₁ => (i, j)))) ⊓
  (⨅ i : ι₁, D₂.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun j : ι₂ => (i, j))))

end TillichZemor.HGP
