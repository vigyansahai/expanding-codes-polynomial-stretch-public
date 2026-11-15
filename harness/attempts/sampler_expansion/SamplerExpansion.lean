import ExpandingCodes.Construction.ExpansionTransfer

set_option autoImplicit false
open scoped Classical BigOperators Topology
open Filter

namespace ExpandingCodes.PolynomialStretch

theorem eventProb_sampleLaw (θ : ℝ) (n : ℕ) (g : Geometry (dimension θ) n)
    (E : Generator (rowCount (dimension θ) n) n → Prop) :
    eventProb (sampleLaw θ n g) E =
      uniformProb (fun p : Forms g.F (dimension θ) (arity θ) ×
        Hashes g.F (arity θ) (buckets θ n) => E (combined g p.1 p.2)) := by
  unfold sampleLaw
  rw [eventProb_map]
  rfl

theorem eventual_sampler_expansion (ε θ : ℝ)
    (hε : 0 < ε ∧ ε < 1/2) (hθ : ε/2 < θ ∧ θ < ε)
    (g : ∀ n, Geometry (dimension θ) n) :
    ∀ᶠ n : ℕ in atTop,
      1 - (n : ℝ) ^ (-1/ε) ≤ eventProb (sampleLaw θ n (g n))
        (fun G => Expanding G (1-ε) (arity θ) ((n : ℝ) ^ (1-ε))) := by
  have hθrange : 0 < θ ∧ θ < 1/2 :=
    ⟨(half_pos hε.1).trans hθ.1, hθ.2.trans hε.2⟩
  obtain ⟨δ, hδpos, hδlim, hδgood⟩ := hash_expansion_envelope θ hθrange g
  let pbad : ℕ → ℝ := fun n => uniformProb
    (fun s : Forms (g n).F (dimension θ) (arity θ) => ¬ PreliminaryGood θ n (g n) s)
  have hlim : Tendsto (fun n => (pbad n + δ n) * (n : ℝ) ^ (1/θ)) atTop (𝓝 0) := by
    simpa only [pbad, add_mul, zero_add] using
      (preliminary_expansion_limit θ hθrange g).add hδlim
  have hsmall := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hδgood, hsmall, eventually_ge_atTop 1] with n hn hnorm hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpow : (0 : ℝ) < (n : ℝ) ^ (1/θ) := by positivity
  have hinv : ε⁻¹ ≤ θ⁻¹ := (inv_le_inv₀ hε.1 hθrange.1).2 hθ.2.le
  have hexp : 0 ≤ -1/ε + 1/θ := by
    simp only [div_eq_mul_inv, neg_one_mul, one_mul]
    linarith
  have hbad : pbad n + δ n ≤ (n : ℝ) ^ (-1/ε) := by
    apply (mul_le_mul_iff_left₀ hpow).mp
    calc
      (pbad n + δ n) * (n : ℝ) ^ (1/θ) ≤ 1 := hnorm.le
      _ ≤ (n : ℝ) ^ (-1/ε) * (n : ℝ) ^ (1/θ) := by
        rw [← Real.rpow_add hnp]
        exact Real.one_le_rpow hnR hexp
  let Ω := Forms (g n).F (dimension θ) (arity θ) ×
    Hashes (g n).F (arity θ) (buckets θ n)
  let Good : Forms (g n).F (dimension θ) (arity θ) → Prop := PreliminaryGood θ n (g n)
  let E : Ω → Prop := fun p => Expanding (combined (g n) p.1 p.2)
    (1-θ) (arity θ) ((n : ℝ) ^ (1-θ))
  have hf : uniformProb (fun p : Ω => ¬ E p) ≤ pbad n + δ n := by
    exact uniformProb_conditional_bad_le Good (fun p => ¬ E p) (δ n) (hδpos n) hn
  have hc := uniformProb_compl E
  have hs : 1 - (pbad n + δ n) ≤ uniformProb E := by linarith
  rw [eventProb_sampleLaw]
  apply (show 1 - (n : ℝ) ^ (-1/ε) ≤ uniformProb E by linarith).trans
  apply uniformProb_mono
  intro p hp
  exact Expanding.mono hp (by linarith [hθ.2])
    (Real.rpow_le_rpow_of_exponent_le hnR (by linarith [hθ.2]))

end ExpandingCodes.PolynomialStretch
