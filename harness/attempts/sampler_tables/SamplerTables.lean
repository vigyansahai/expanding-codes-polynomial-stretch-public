import ExpandingCodes.Computation.RandomTables
import ExpandingCodes.Construction.ExpansionTransfer

set_option autoImplicit false
set_option linter.style.haveILetI false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch
namespace SamplerTables

/-- Row-major four-dimensional layout. The last coordinate changes fastest. -/
def flatFour (a b c d : ℕ) :
    (((Fin a × Fin b) × Fin c) × Fin d) ≃ Fin (a*b*c*d) :=
  (Equiv.prodCongr (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin c)))
    (Equiv.refl (Fin d))).trans
    ((Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin d))).trans finProdFinEquiv)

theorem flatFour_val {a b c d : ℕ} (i : Fin a) (j : Fin b) (u : Fin c) (v : Fin d) :
    (flatFour a b c d (((i,j),u),v)).val =
      v.val + d * (u.val + c * (j.val + b*i.val)) := by
  simp [flatFour, finProdFinEquiv]

def quadTableEquiv (a b c d : ℕ) (X : Type*) :
    (Fin (a*b*c*d) → X) ≃ (Fin a → Fin b → Fin c → Fin d → X) where
  toFun t i j u v := t (flatFour a b c d (((i,j),u),v))
  invFun f z :=
    let p := (flatFour a b c d).symm z
    f p.1.1.1 p.1.1.2 p.1.2 p.2
  left_inv t := by
    funext z
    change t (flatFour a b c d ((flatFour a b c d).symm z)) = t z
    rw [Equiv.apply_symm_apply]
  right_inv f := by
    funext i j u v
    change f ((flatFour a b c d).symm (flatFour a b c d (((i,j),u),v))).1.1.1
      ((flatFour a b c d).symm (flatFour a b c d (((i,j),u),v))).1.1.2
      ((flatFour a b c d).symm (flatFour a b c d (((i,j),u),v))).1.2
      ((flatFour a b c d).symm (flatFour a b c d (((i,j),u),v))).2 = _
    rw [Equiv.symm_apply_apply]

def formEntries (d n k : ℕ) : ℕ := 2*k*fieldSize d n*d
def hashEntries (d n k : ℕ) : ℕ := k*fieldSize d n*fieldSize d n*fieldSize d n
def entropy (d n k beta : ℕ) : ℕ :=
  formEntries d n k * fieldExponent d n + hashEntries d n k * beta

/-- Explicit coefficient-table decoding; both field arguments and values use the
geometry's given enumeration, rather than any fresh choice of enumeration. -/
noncomputable def formsEquiv {d n : ℕ} (g : Geometry d n) (k : ℕ) :
    (Fin (formEntries d n k) → Fin (fieldSize d n)) ≃ Forms g.F d k :=
  (quadTableEquiv 2 k (fieldSize d n) d (Fin (fieldSize d n))).trans
    (Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ =>
      Equiv.arrowCongr g.elements
        (Equiv.arrowCongr (Equiv.refl (Fin d)) g.elements))

theorem formsEquiv_apply {d n : ℕ} (g : Geometry d n) (k : ℕ)
    (t : Fin (formEntries d n k) → Fin (fieldSize d n))
    (r : Fin 2) (i : Fin k) (a : g.F) (j : Fin d) :
    formsEquiv g k t r i a j =
      g.elements (t (flatFour 2 k (fieldSize d n) d (((r,i),g.elements.symm a),j))) := rfl

/-- Flat hash-table decoding, with index order (layer,a,u,v). -/
noncomputable def hashesEquiv {d n : ℕ} (g : Geometry d n) (k b : ℕ) :
    (Fin (hashEntries d n k) → Fin b) ≃ Hashes g.F k b :=
  (quadTableEquiv k (fieldSize d n) (fieldSize d n) (fieldSize d n) (Fin b)).trans
    (Equiv.piCongrRight fun _ =>
      ((Equiv.piCongrRight fun _ =>
        (Equiv.curry (Fin (fieldSize d n)) (Fin (fieldSize d n)) (Fin b)).symm).trans
      ((Equiv.curry (Fin (fieldSize d n))
        (Fin (fieldSize d n) × Fin (fieldSize d n)) (Fin b)).symm.trans
        (Equiv.arrowCongr
          (Equiv.prodCongr g.elements (Equiv.prodCongr g.elements g.elements))
          (Equiv.refl (Fin b))))))

theorem hashesEquiv_apply {d n : ℕ} (g : Geometry d n) (k b : ℕ)
    (t : Fin (hashEntries d n k) → Fin b) (i : Fin k) (a u v : g.F) :
    hashesEquiv g k b t i (a,u,v) =
      t (flatFour k (fieldSize d n) (fieldSize d n) (fieldSize d n)
        (((i,g.elements.symm a),g.elements.symm u),g.elements.symm v)) := rfl

def splitBits (a b : ℕ) :
    (Fin (a+b) → Bool) ≃ ((Fin a → Bool) × (Fin b → Bool)) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) Bool)

theorem splitBits_list (a b : ℕ) (ω : Fin (a+b) → Bool) :
    List.ofFn ω = List.ofFn (splitBits a b ω).1 ++ List.ofFn (splitBits a b ω).2 := by
  change List.ofFn ω =
    List.ofFn (fun i : Fin a => ω (Fin.castLE (Nat.le_add_right a b) i)) ++
      List.ofFn (fun i : Fin b => ω (Fin.natAdd a i))
  exact List.ofFn_add

def indexCoinsEquiv (K ell H beta extra : ℕ) :
    (Fin (K*ell+H*beta+extra) → Bool) ≃
      (((Fin K → Fin (2^ell)) × (Fin H → Fin (2^beta))) × (Fin extra → Bool)) :=
  (splitBits (K*ell+H*beta) extra).trans
    (Equiv.prodCongr
      ((splitBits (K*ell) (H*beta)).trans
        (Equiv.prodCongr (Computation.RandomTables.tableIndexEquiv K ell)
          (Computation.RandomTables.tableIndexEquiv H beta)))
      (Equiv.refl (Fin extra → Bool)))

noncomputable def coinsEquiv {d n : ℕ} (g : Geometry d n) (k beta extra : ℕ) :
    (Fin (entropy d n k beta + extra) → Bool) ≃
      ((Forms g.F d k × Hashes g.F k (2^beta)) × (Fin extra → Bool)) :=
  (indexCoinsEquiv (formEntries d n k) (fieldExponent d n)
    (hashEntries d n k) beta extra).trans
      (Equiv.prodCongr (Equiv.prodCongr (formsEquiv g k) (hashesEquiv g k (2^beta)))
        (Equiv.refl (Fin extra → Bool)))

noncomputable def decodeCoins {d n : ℕ} (g : Geometry d n) (k beta extra : ℕ)
    (ω : Fin (entropy d n k beta+extra) → Bool) :
    Forms g.F d k × Hashes g.F k (2^beta) := (coinsEquiv g k beta extra ω).1

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


/-- Full matrix determined by the two independent decoded tables. -/
noncomputable def generator {d n : ℕ} (g : Geometry d n) (k beta extra : ℕ)
    (ω : Fin (entropy d n k beta+extra) → Bool) : Generator (rowCount d n) n :=
  combined g (decodeCoins g k beta extra ω).1 (decodeCoins g k beta extra ω).2

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

/-- Transport a sufficiently long actual random tape to the entropy plus padding
layout. This cast changes no bit positions. -/
def padEquiv (E T : ℕ) (h : E ≤ T) :
    (Fin T → Bool) ≃ (Fin (E+(T-E)) → Bool) :=
  Equiv.arrowCongr (finCongr (Nat.add_sub_of_le h).symm) (Equiv.refl Bool)

theorem padEquiv_list (E T : ℕ) (h : E ≤ T) (ω : Fin T → Bool) :
    List.ofFn (padEquiv E T h ω) = List.ofFn ω := by
  have hh := List.ofFn_congr (Nat.add_sub_of_le h) (padEquiv E T h ω)
  have hf : (fun i : Fin T => padEquiv E T h ω (Fin.cast (Nat.add_sub_of_le h).symm i)) = ω := by
    funext i
    apply congrArg ω
    apply Fin.ext
    rfl
  exact hh.trans (congrArg List.ofFn hf)

noncomputable def fromTape (θ : ℝ) (n T : ℕ) (g : Geometry (dimension θ) n)
    (h : entropy (dimension θ) n (arity θ) (Nat.log 2 (n/arity θ)) ≤ T)
    (ω : Fin T → Bool) : Generator (rowCount (dimension θ) n) n :=
  generator g (arity θ) (Nat.log 2 (n/arity θ))
    (T-entropy (dimension θ) n (arity θ) (Nat.log 2 (n/arity θ)))
    (padEquiv _ T h ω)

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

#print axioms flatFour_val
#print axioms formsEquiv_apply
#print axioms hashesEquiv_apply
#print axioms uniform_decodeCoins
#print axioms decodeCoins_physical
#print axioms generator_law
#print axioms fromTape_law

end SamplerTables
end ExpandingCodes.PolynomialStretch
