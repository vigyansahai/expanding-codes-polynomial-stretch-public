import ExpandingCodes.Construction.AffineGeometry

set_option autoImplicit false
open scoped Classical BigOperators

namespace ExpandingCodes.PolynomialStretch

/-- Layers whose fixed level at `z` belongs to a prescribed set of level pairs. -/
noncomputable def activeLayers {d n k : ℕ} (g : Geometry d n)
    (A : Finset (Fin k × g.F)) (z : Fin d → g.F) : Finset (Fin k) :=
  Finset.univ.filter (fun i => (i, fixedForm g i z) ∈ A)

/-- The deterministic candidate set `W_A` of paper Lemma 2.6. -/
noncomputable def activePointSet {d n k : ℕ} (g : Geometry d n)
    (A : Finset (Fin k × g.F)) : Finset (Fin d → g.F) :=
  Finset.univ.filter (fun z => d ≤ (activeLayers g A z).card)

@[simp] theorem mem_activeLayers {d n k : ℕ} (g : Geometry d n)
    (A : Finset (Fin k × g.F)) (z : Fin d → g.F) (i : Fin k) :
    i ∈ activeLayers g A z ↔ (i, fixedForm g i z) ∈ A := by
  simp [activeLayers]

@[simp] theorem mem_activePointSet {d n k : ℕ} (g : Geometry d n)
    (A : Finset (Fin k × g.F)) (z : Fin d → g.F) :
    z ∈ activePointSet g A ↔ d ≤ (activeLayers g A z).card := by
  simp [activePointSet]

/-- Every candidate point admits `d` distinct active layers. -/
theorem exists_active_layers {d n k : ℕ} (g : Geometry d n)
    (A : Finset (Fin k × g.F)) {z : Fin d → g.F}
    (hz : z ∈ activePointSet g A) :
    ∃ layers : Fin d ↪ Fin k, ∀ j, (layers j, fixedForm g (layers j) z) ∈ A := by
  classical
  have hc : Fintype.card (Fin d) ≤ (activeLayers g A z).card := by
    simpa using (mem_activePointSet g A z).mp hz
  obtain ⟨layers, hlayers⟩ := Function.Embedding.exists_of_card_le_finset hc
  refine ⟨layers, fun j => (mem_activeLayers g A z (layers j)).mp ?_⟩
  exact hlayers ⟨j, rfl⟩

/-- Choosing `d` active level pairs determines a point, so `|W_A| ≤ |A|^d`.
This statement depends only on the fixed forms, before sampling any random forms. -/
theorem activePointSet_card_le {d n k : ℕ} (g : Geometry d n)
    (hk : k ≤ fieldSize d n) (A : Finset (Fin k × g.F)) :
    (activePointSet g A).card ≤ A.card ^ d := by
  classical
  have hchoose : ∀ z : activePointSet g A,
      ∃ layers : Fin d ↪ Fin k,
        ∀ j, (layers j, fixedForm g (layers j) z.val) ∈ A :=
    fun z => exists_active_layers g A z.property
  choose layers hlayers using hchoose
  let encode : activePointSet g A → (Fin d → A) := fun z j =>
    ⟨(layers z j, fixedForm g (layers z j) z.val), hlayers z j⟩
  have hinj : Function.Injective encode := by
    intro z z' heq
    apply Subtype.ext
    apply eq_of_fixedForm_eq g hk (layers z)
    intro j
    have hj := congrFun heq j
    have hi : layers z j = layers z' j :=
      congrArg (fun p : A => p.val.1) hj
    have hv : fixedForm g (layers z j) z.val = fixedForm g (layers z' j) z'.val :=
      congrArg (fun p : A => p.val.2) hj
    simpa only [← hi] using hv
  have hc := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] using hc

end ExpandingCodes.PolynomialStretch
