import Definitions.Def_ExpandingCodes_PolynomialStretch_ErasureModel

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

noncomputable def coordinateLinearEquiv {F I J : Type*} [Field F] (e : J ≃ I) :
    (I → F) ≃ₗ[F] (J → F) where
  toFun c := c ∘ e
  invFun c := c ∘ e.symm
  left_inv c := by funext i; simp
  right_inv c := by funext j; simp
  map_add' c c' := rfl
  map_smul' a c := rfl

noncomputable def codeReindex {F I J : Type*} [Field F] (e : J ≃ I)
    (C : Submodule F (I → F)) : Submodule F (J → F) :=
  C.map (coordinateLinearEquiv (F := F) e).toLinearMap

@[simp] theorem mem_codeReindex {F I J : Type*} [Field F] (e : J ≃ I)
    (C : Submodule F (I → F)) (c : J → F) :
    c ∈ codeReindex e C ↔ (fun i => c (e.symm i)) ∈ C := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa [coordinateLinearEquiv] using hv
  · intro hc
    refine ⟨(fun i => c (e.symm i)), hc, ?_⟩
    funext j
    simp [coordinateLinearEquiv]

@[simp] theorem finrank_codeReindex {F I J : Type*} [Field F] (e : J ≃ I)
    (C : Submodule F (I → F)) :
    Module.finrank F (codeReindex e C) = Module.finrank F C :=
  (coordinateLinearEquiv (F := F) e).finrank_map_eq C

theorem ambiguity_codeReindex {F I J : Type*} [Field F] [Fintype I] [Fintype J]
    (e : J ≃ I) (C : Submodule F (I → F)) (E : Finset J) :
    ambiguity (codeReindex e C) E = codeReindex e (ambiguity C (E.map e.toEmbedding)) := by
  ext c
  simp only [ambiguity, Submodule.mem_mk, mem_codeReindex]
  constructor
  · rintro ⟨hc, hz⟩
    refine ⟨hc, fun i hi => hz _ ?_⟩
    simpa using hi
  · rintro ⟨hc, hz⟩
    refine ⟨hc, fun j hj => ?_⟩
    simpa using hz (e j) (by simpa using hj)

theorem erasureExpectation_codeReindex {F I J : Type*} [Field F] [Fintype I] [Fintype J]
    (e : J ≃ I) (C : Submodule F (I → F)) (p : ℝ) :
    erasureExpectation (codeReindex e C) p = erasureExpectation C p := by
  unfold erasureExpectation
  have hdim (E : Finset J) :
      Module.finrank F (ambiguity (codeReindex e C) E) =
        Module.finrank F (ambiguity C (E.map e.toEmbedding)) := by
    calc
      _ = Module.finrank F (codeReindex e (ambiguity C (E.map e.toEmbedding))) :=
        congrArg (fun S : Submodule F (J → F) => Module.finrank F S)
          (ambiguity_codeReindex e C E)
      _ = _ := finrank_codeReindex e _
  simp_rw [hdim]
  apply Fintype.sum_equiv e.finsetCongr
  intro E
  simp only [Equiv.finsetCongr_apply, Finset.card_map, Fintype.card_congr e]
  congr 2

/-- All coordinate permutations preserving a code in both directions. -/
noncomputable def codePreservingSubgroup {F I : Type*} [Field F]
    (C : Submodule F (I → F)) : Subgroup (Equiv.Perm I) where
  carrier := {σ | ∀ c, c ∈ C ↔ (fun i => c (σ i)) ∈ C}
  one_mem' := by intro c; rfl
  mul_mem' := by
    intro σ τ hσ hτ c
    exact (hσ c).trans (hτ (fun i => c (σ i)))
  inv_mem' := by
    intro σ hσ c
    have h := hσ (fun i => c (σ⁻¹ i))
    simpa using h.symm

/-- Transport an honest doubly transitive code symmetry action to numbered coordinates. -/
theorem codeReindex_doublyTransitive {F I : Type*} [Field F] {M : ℕ}
    (e : Fin M ≃ I) (C : Submodule F (I → F))
    (hpair : ∀ a b a' b' : I, a ≠ b → a' ≠ b' →
      ∃ σ ∈ codePreservingSubgroup C, σ a = a' ∧ σ b = b') :
    DoublyTransitiveCode M (codeReindex e C) := by
  refine ⟨codePreservingSubgroup (codeReindex e C), ?_, ?_⟩
  · intro σ hσ c hc
    exact (hσ c).mp hc
  · intro a b a' b' hab hab'
    obtain ⟨σ, hσ, ha, hb⟩ := hpair (e a) (e b) (e a') (e b')
      (e.injective.ne hab) (e.injective.ne hab')
    let τ : Equiv.Perm (Fin M) := (e.trans σ).trans e.symm
    refine ⟨τ, ?_, ?_, ?_⟩
    · intro c
      simp only [mem_codeReindex]
      have h := hσ (fun i => c (e.symm i))
      simpa only [τ, Equiv.trans_apply, Equiv.apply_symm_apply] using h
    · apply e.injective
      simpa [τ] using ha
    · apply e.injective
      simpa [τ] using hb

end ExpandingCodes.PolynomialStretch
