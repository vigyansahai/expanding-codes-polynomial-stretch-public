import Mathlib
import Definitions.Def_CodingTheory
import Definitions.Def_TillichZemor_HGP_Setting

namespace QuantumExpander.Decoder

open TillichZemor.HGP

section Graph

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  (adj : A → B → Prop) [∀ a b, Decidable (adj a b)]

/-- `Γ(S)` for `S ⊆ A` (p. 3): the vertices of `B` adjacent to some vertex of `S`. -/
def nbhdA (S : Finset A) : Finset B :=
  Finset.univ.filter (fun β => ∃ a ∈ S, adj a β)

/-- `Γ(T)` for `T ⊆ B` (p. 3): the vertices of `A` adjacent to some vertex of `T`. -/
def nbhdB (T : Finset B) : Finset A :=
  Finset.univ.filter (fun α => ∃ b ∈ T, adj α b)

/-- `Γu(S)` for `S ⊆ A` (p. 7): the unique neighbours of `S`, i.e. the vertices of `B`
adjacent to exactly one vertex of `S`. -/
def uniqNbhdA (S : Finset A) : Finset B :=
  Finset.univ.filter (fun β => (S.filter (fun a => adj a β)).card = 1)

/-- `Γu(T)` for `T ⊆ B` (p. 7): the vertices of `A` adjacent to exactly one vertex of `T`. -/
def uniqNbhdB (T : Finset B) : Finset A :=
  Finset.univ.filter (fun α => (T.filter (fun b => adj α b)).card = 1)

/-- `Γm(S) = Γ(S) \ Γu(S)` (p. 7): the multiple neighbours of `S ⊆ A`. -/
def multNbhdA (S : Finset A) : Finset B := nbhdA adj S \ uniqNbhdA adj S

/-- `Γm(T) = Γ(T) \ Γu(T)` (p. 7): the multiple neighbours of `T ⊆ B`. -/
def multNbhdB (T : Finset B) : Finset A := nbhdB adj T \ uniqNbhdB adj T

/-- `(ΔA, ΔB)`-biregularity (p. 3): every `a ∈ A` has exactly `ΔA` neighbours and every
`b ∈ B` has exactly `ΔB` neighbours. -/
def IsBiregular (ΔA ΔB : ℕ) : Prop :=
  (∀ a : A, (Finset.univ.filter (fun β => adj a β)).card = ΔA) ∧
  (∀ b : B, (Finset.univ.filter (fun α => adj α b)).card = ΔB)

/-- `(γA, δA)`-left-expansion (p. 3): every `S ⊆ A` with `|S| ≤ γA nA` has
`|Γ(S)| ≥ (1 - δA) ΔA |S|`, where `nA = |A|`. -/
def IsLeftExpanding (ΔA : ℕ) (γA δA : ℝ) : Prop :=
  ∀ S : Finset A, (S.card : ℝ) ≤ γA * Fintype.card A →
    (1 - δA) * ΔA * S.card ≤ ((nbhdA adj S).card : ℝ)

/-- `(γB, δB)`-right-expansion (p. 3): every `T ⊆ B` with `|T| ≤ γB nB` has
`|Γ(T)| ≥ (1 - δB) ΔB |T|`, where `nB = |B|`. -/
def IsRightExpanding (ΔB : ℕ) (γB δB : ℝ) : Prop :=
  ∀ T : Finset B, (T.card : ℝ) ≤ γB * Fintype.card B →
    (1 - δB) * ΔB * T.card ≤ ((nbhdB adj T).card : ℝ)

/-- The `nB × nA` matrix `H` of the graph (p. 3): rows indexed by `B`, columns by `A`,
`H b a = 1` iff `a ∼ b`. -/
def bipMatrix : Matrix B A (ZMod 2) :=
  Matrix.of fun b a => if adj a b then 1 else 0

end Graph

/-- The qubits `A² ∪ B²` of the code `Q_G` (p. 4): `αa ↦ Sum.inl (α, a)`,
`bβ ↦ Sum.inr (b, β)`. -/
abbrev Qubit (A B : Type*) := (A × A) ⊕ (B × B)

section Code

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The `X`-syndrome `σX(e) = H_X e^T` (p. 5), where the paper's `H_X` of eq. (1) is
`TillichZemor.HGP.hz H H` (rows `αβ ∈ A × B`). -/
def sigmaX (H : Matrix B A (ZMod 2)) (e : Qubit A B → ZMod 2) : A × B → ZMod 2 :=
  (hz H H).mulVec e

/-- The `Z`-syndrome `σZ(e) = H_Z e^T` (p. 5), where the paper's `H_Z` of eq. (2) is
`TillichZemor.HGP.hx H H` (rows `ba ∈ B × A`). -/
def sigmaZ (H : Matrix B A (ZMod 2)) (e : Qubit A B → ZMod 2) : B × A → ZMod 2 :=
  (hx H H).mulVec e

/-- `C_Z^⊥` (p. 7): the sums of `Z`-generators, i.e. the dual of `C_Z = ker H_Z`
(the row space of `H_Z`). -/
def CZperp (H : Matrix B A (ZMod 2)) : Submodule (ZMod 2) (Qubit A B → ZMod 2) :=
  CodingTheory.dualCode (ZMod 2) (Qubit A B) (code (hx H H))

/-- `C_X^⊥`: the sums of `X`-generators, i.e. the dual of `C_X = ker H_X`. -/
def CXperp (H : Matrix B A (ZMod 2)) : Submodule (ZMod 2) (Qubit A B → ZMod 2) :=
  CodingTheory.dualCode (ZMod 2) (Qubit A B) (code (hz H H))

/-- The weight `w(eX, eZ)` of a quantum error (p. 6): the number of qubits on which `eX` or
`eZ` is nonzero. -/
def quantumWeight (eX eZ : Qubit A B → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun q => eX q ≠ 0 ∨ eZ q ≠ 0)).card

/-- The support `E` of an error vector `e`. -/
def errSupport (e : Qubit A B → ZMod 2) : Finset (Qubit A B) :=
  Finset.univ.filter (fun q => e q ≠ 0)

/-- The indicator vector of a set `F` of qubits. -/
def indicator (F : Finset (Qubit A B)) : Qubit A B → ZMod 2 :=
  fun q => if q ∈ F then 1 else 0

/-- The reduced weight `w_R(e)` (p. 8): the least Hamming weight of an element of the coset
`e + C_Z^⊥`. The set is nonempty (take `f = 0`), so the infimum is attained. -/
noncomputable def reducedWeight (H : Matrix B A (ZMod 2)) (e : Qubit A B → ZMod 2) : ℕ :=
  sInf {w : ℕ | ∃ f ∈ CZperp H, hammingNorm (e + f) = w}

variable (adj : A → B → Prop) [∀ a b, Decidable (adj a b)]

/-- The `Z`-generator `g_ba = {αa : α ∼ b} ∪ {bβ : β ∼ a}` of eq. (5), p. 6: the support of
row `ba` of `H_Z`. -/
def genZ (b : B) (a : A) : Finset (Qubit A B) :=
  (Finset.univ.filter (fun α => adj α b)).image (fun α => Sum.inl (α, a)) ∪
  (Finset.univ.filter (fun β => adj a β)).image (fun β => Sum.inr (b, β))

/-- The `X`-generator `g_αβ` of eq. (6), p. 6: the support of row `αβ` of `H_X`, i.e. the
qubits `αa` with `a ∼ β` and `bβ` with `α ∼ b`. -/
def genX (α : A) (β : B) : Finset (Qubit A B) :=
  (Finset.univ.filter (fun a => adj a β)).image (fun a => Sum.inl (α, a)) ∪
  (Finset.univ.filter (fun b => adj α b)).image (fun b => Sum.inr (b, β))

/-- The number of neighbours in `E` of the check `αβ` of `G_X`: the qubits `q ∈ E` with
`H_X (α, β) q = 1`. -/
def checkDegX (E : Finset (Qubit A B)) (α : A) (β : B) : ℕ :=
  (E.filter (fun q => hz (bipMatrix adj) (bipMatrix adj) (α, β) q ≠ 0)).card

/-- The six parts of Definition 6 (p. 8), given as the first coordinates
`xa x̄a χa ⊆ {α : α ∼ b}` (standing for `{αa : α ∈ xa}`, …) and the second coordinates
`xb x̄b χb ⊆ {β : β ∼ a}` (standing for `{bβ : β ∈ xb}`, …), satisfy the conditions of
Definition 6 with respect to the error pattern `E`. For `α ∈ N(b)` and `β ∈ N(a)` the check
`αβ` lies in `Γ(αa) ∩ Γ(bβ)`, so `Γ(xa) ∩ Γ(xb) = {αβ : α ∈ xa, β ∈ xb}`, etc. -/
def CriticalPartition (δA δB : ℝ) (ΔA ΔB : ℕ) (E : Finset (Qubit A B)) (b : B) (a : A)
    (xa xa' χa : Finset A) (xb xb' χb : Finset B) : Prop :=
  -- `xa ∪ x̄a ∪ χa` is a partition of `g_ba ∩ A²` (empty parts allowed)
  Disjoint xa xa' ∧ Disjoint xa χa ∧ Disjoint xa' χa ∧
  xa ∪ xa' ∪ χa = Finset.univ.filter (fun α => adj α b) ∧
  -- `xb ∪ x̄b ∪ χb` is a partition of `g_ba ∩ B²`
  Disjoint xb xb' ∧ Disjoint xb χb ∧ Disjoint xb' χb ∧
  xb ∪ xb' ∪ χb = Finset.univ.filter (fun β => adj a β) ∧
  -- `xa ∪ xb ⊂ E`, `x̄a ∩ E = ∅`, `x̄b ∩ E = ∅`
  (∀ α ∈ xa, Sum.inl (α, a) ∈ E) ∧ (∀ β ∈ xb, Sum.inr (b, β) ∈ E) ∧
  (∀ α ∈ xa', Sum.inl (α, a) ∉ E) ∧ (∀ β ∈ xb', Sum.inr (b, β) ∉ E) ∧
  -- every vertex of `Γ(xa) ∩ Γ(xb)` has exactly two neighbours in `E`
  (∀ α ∈ xa, ∀ β ∈ xb, checkDegX adj E α β = 2) ∧
  -- every vertex of `Γ(x̄a) ∩ Γ(x̄b)` has no neighbour in `E`
  (∀ α ∈ xa', ∀ β ∈ xb', checkDegX adj E α β = 0) ∧
  -- every vertex of `Γ(xa) ∩ Γ(x̄b)` and of `Γ(x̄a) ∩ Γ(xb)` has exactly one neighbour in `E`
  (∀ α ∈ xa, ∀ β ∈ xb', checkDegX adj E α β = 1) ∧
  (∀ α ∈ xa', ∀ β ∈ xb, checkDegX adj E α β = 1) ∧
  -- `xa ∪ xb ≠ ∅`, `|χa| ≤ 2 δB ΔB`, `|χb| ≤ 2 δA ΔA`
  (xa.Nonempty ∨ xb.Nonempty) ∧
  (χa.card : ℝ) ≤ 2 * δB * ΔB ∧ (χb.card : ℝ) ≤ 2 * δA * ΔA

/-- Definition 6 (p. 8): the generator `g_ba` is critical with respect to `E` if it admits a
partition as in `CriticalPartition`. -/
def IsCritical (δA δB : ℝ) (ΔA ΔB : ℕ) (E : Finset (Qubit A B)) (b : B) (a : A) : Prop :=
  ∃ (xa xa' χa : Finset A) (xb xb' χb : Finset B),
    CriticalPartition adj δA δB ΔA ΔB E b a xa xa' χa xb xb' χb

/-- The qubit set `{αa : α ∈ sa} ∪ {bβ : β ∈ sb}` inside `g_ba` described by first coordinates
`sa ⊆ A` and second coordinates `sb ⊆ B`. -/
def genPart (b : B) (a : A) (sa : Finset A) (sb : Finset B) : Finset (Qubit A B) :=
  sa.image (fun α => Sum.inl (α, a)) ∪ sb.image (fun β => Sum.inr (b, β))

end Code

section Algorithm

/-! The decoding algorithm of §3 (pp. 6–7), generic in the syndrome matrix `S` and the
generator matrix `Gm` on the same qubits. The `X` decoder is `S = H_X = hz H H`,
`Gm = H_Z = hx H H` (it flips patterns inside the `Z`-generators `g_ba`); the `Z` decoder is
`S = hx H H`, `Gm = hz H H`. -/

variable {Q R C : Type*} [Fintype Q] [Fintype R] [Fintype C] [DecidableEq Q] [DecidableEq C]

/-- The ratio `(|s| - |s + S e|) / |e|` of §3, in `ℚ`. -/
def ratio (S : Matrix C Q (ZMod 2)) (s : C → ZMod 2) (e : Q → ZMod 2) : ℚ :=
  ((hammingNorm s : ℚ) - hammingNorm (s + S.mulVec e)) / hammingNorm e

/-- The first two conditions of a decoding iteration (p. 6): the support of `e1` is included
in the support of some generator (row of `Gm`), and `s1 = s + S e1` has `|s1| < |s|`. -/
def Candidate (S : Matrix C Q (ZMod 2)) (Gm : Matrix R Q (ZMod 2)) (s : C → ZMod 2)
    (e1 : Q → ZMod 2) : Prop :=
  (∃ r : R, ∀ q, e1 q ≠ 0 → Gm r q ≠ 0) ∧ hammingNorm (s + S.mulVec e1) < hammingNorm s

/-- A decoding iteration (p. 6): `e1` is a candidate and its ratio `(|s| - |s1|)/|e1|` is
maximal among all candidates, over all generators at once. -/
def Step (S : Matrix C Q (ZMod 2)) (Gm : Matrix R Q (ZMod 2)) (s : C → ZMod 2)
    (e1 : Q → ZMod 2) : Prop :=
  Candidate S Gm s e1 ∧ ∀ e', Candidate S Gm s e' → ratio S s e' ≤ ratio S s e1

/-- `Reach S Gm s eO`: after some number of iterations of the algorithm on input syndrome `s`,
the accumulated flip is `eO = e1 + ⋯ + ei`; the current syndrome is `s + S eO`
(p. 6, `s_i = s + σ(e1 + ⋯ + ei)`). Every tie-breaking among maximal `e1` is covered. -/
inductive Reach (S : Matrix C Q (ZMod 2)) (Gm : Matrix R Q (ZMod 2)) (s : C → ZMod 2) :
    (Q → ZMod 2) → Prop
  | zero : Reach S Gm s 0
  | step {eO e1 : Q → ZMod 2} :
      Reach S Gm s eO → Step S Gm (s + S.mulVec eO) e1 → Reach S Gm s (eO + e1)

/-- The algorithm, run on the syndrome `S e` of the error `e`, never outputs a decoding failure
and always decodes `e` correctly (p. 7): at every reachable state, if the current syndrome is
nonzero a further iteration exists, and if it is zero the output `eO` satisfies
`eO + e ∈ (ker Gm)^⊥`, the row space of `Gm`. -/
def DecodesCorrectly (S : Matrix C Q (ZMod 2)) (Gm : Matrix R Q (ZMod 2)) (e : Q → ZMod 2) :
    Prop :=
  ∀ eO, Reach S Gm (S.mulVec e) eO →
    (S.mulVec e + S.mulVec eO ≠ 0 → ∃ e1, Step S Gm (S.mulVec e + S.mulVec eO) e1) ∧
    (S.mulVec e + S.mulVec eO = 0 → eO + e ∈ CodingTheory.dualCode (ZMod 2) Q (code Gm))

end Algorithm

end QuantumExpander.Decoder
