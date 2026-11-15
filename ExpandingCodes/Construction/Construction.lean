import ExpandingCodes.Construction.Obligations
import ExpandingCodes.Construction.Adversarial
import ExpandingCodes.Construction.LogGrowth

set_option autoImplicit false
open scoped Classical
open Filter

namespace ExpandingCodes.PolynomialStretch

theorem construction :
    ∃ Cd Ck : ℝ, 0 < Cd ∧ 0 < Ck ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        ∃ θ : ℚ, ε / 2 < (θ : ℝ) ∧ (θ : ℝ) < ε ∧
          (dimension (θ : ℝ) : ℝ) ≤ Cd * ε⁻¹ ^ 2 ∧
          (arity (θ : ℝ) : ℝ) ≤ Ck * ε⁻¹ ^ 6 ∧
          ∃ g : ∀ n, Geometry (dimension (θ : ℝ)) n,
            EfficientFamily ε (arity (θ : ℝ)) (rowCount (dimension (θ : ℝ)))
              (fun n => sampleLaw (θ : ℝ) n (g n)) (fun n => rankTest (θ : ℝ) (g n)) ∧
            Tendsto (fun n => Real.log (rowCount (dimension (θ : ℝ)) n) / Real.log n -
              2 * (dimension (θ : ℝ) : ℝ) ^ 2) atTop (nhds 0) := by
  refine ⟨8192, 2147483648, by norm_num, by norm_num, ?_⟩
  intro ε hεpos hεhalf
  have hε := And.intro hεpos hεhalf
  obtain ⟨θ, hlo, hhi, hd, hk⟩ := rational_parameter_bounds ε hε
  have hθ : 0 < (θ : ℝ) ∧ (θ : ℝ) < 1 / 2 :=
    ⟨(half_pos hεpos).trans hlo, hhi.trans hεhalf⟩
  obtain ⟨g, hs, ht⟩ := rational_geometry_programs θ hθ
  refine ⟨θ, hlo, hhi, hd, hk, g, ?_, ?_⟩
  · obtain ⟨sampler, A, a, Ns, hA, hNs, hs⟩ := hs
    obtain ⟨tester, B, b, Nt, hB, hNt, ht⟩ := ht
    have hmath : ∀ᶠ n : ℕ in atTop,
        (n < rowCount (dimension (θ : ℝ)) n ∧
          rowCount (dimension (θ : ℝ)) n < n ^ arity (θ : ℝ)) ∧
        (∀ G : Generator (rowCount (dimension (θ : ℝ)) n) n,
          sampleLaw (θ : ℝ) n (g n) G ≠ 0 → RowWeight G (arity (θ : ℝ))) ∧
        (1 - (n : ℝ) ^ (-1 / ε) ≤ eventProb (sampleLaw (θ : ℝ) n (g n))
          (fun G => Expanding G (1 - ε) (arity (θ : ℝ)) ((n : ℝ) ^ (1 - ε)))) ∧
        (∀ G : Generator (rowCount (dimension (θ : ℝ)) n) n,
          sampleLaw (θ : ℝ) n (g n) G ≠ 0 →
          ∀ (x : Word n) (e : Word (rowCount (dimension (θ : ℝ)) n)),
            (weight e : ℝ) ≤ (1 / 2 - ε) * rowCount (dimension (θ : ℝ)) n →
              rankTest (θ : ℝ) (g n) (G.mulVec x + e) = true) ∧
        (uniformProb (fun y : Word (rowCount (dimension (θ : ℝ)) n) =>
          rankTest (θ : ℝ) (g n) y = true) ≤
            Real.exp (-(ε ^ 2 / 128) * rowCount (dimension (θ : ℝ)) n)) := by
      filter_upwards [eventually_rowCount_bounds (θ : ℝ) hθ,
        eventual_sampleLaw_rowWeight (θ : ℝ) hθ,
        eventual_sampler_expansion ε (θ : ℝ) hε ⟨hlo, hhi⟩ g,
        adversarial_rankTest_acceptance ε (θ : ℝ) hθ (by linarith),
        eventual_uniform_rank_acceptance ε (θ : ℝ) hε ⟨hlo, hhi⟩ g] with n hn hw hx ha hu
      exact ⟨hn, hw (g n), hx, ha (g n), hu⟩
    obtain ⟨Nm, hm⟩ := eventually_atTop.1 hmath
    let N := max 2 (max Ns (max Nt Nm))
    refine ⟨sampler, tester, A, a, B, b, N, hA, hB, le_max_left _ _, ?_⟩
    intro n hn
    have hNs' : Ns ≤ n := (le_max_left Ns _).trans ((le_max_right 2 _).trans hn)
    have hNt' : Nt ≤ n := (le_max_left Nt Nm).trans
      ((le_max_right Ns _).trans ((le_max_right 2 _).trans hn))
    have hNm' : Nm ≤ n := (le_max_right Nt Nm).trans
      ((le_max_right Ns _).trans ((le_max_right 2 _).trans hn))
    obtain ⟨hgrowth, hw, hx, ha, hu⟩ := hm n hNm'
    exact ⟨hgrowth.1, hgrowth.2, (hs n hNs').1, (hs n hNs').2,
      ht n hNt', hw, hx, ha, hu⟩
  · exact rowCount_log_limit (dimension (θ : ℝ))
      (lt_of_lt_of_le (by decide : 0 < 4) (dimension_ge_four (θ : ℝ) hθ))

end ExpandingCodes.PolynomialStretch
