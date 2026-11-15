import Definitions.Def_ExpandingCodes_PolynomialStretch_PolynomialTest

set_option autoImplicit false

namespace ExpandingCodes.PolynomialStretch

/-- The exact platform integer-floor choice satisfies the strict orthogonality bound. -/
theorem auxiliaryDegree_strict_degree_bound (q d : ℕ) (hd : 4 ≤ d) (hq : 2 ≤ q) :
    2 * auxiliaryDegree q d + 3 * (q - 1) < d * (q - 1) := by
  have hd' : (4 : ℤ) ≤ d := by exact_mod_cast hd
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hnum : 0 ≤ ((d : ℤ) - 3) * ((q : ℤ) - 1) - 1 := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (d : ℤ) - 4 by omega)
      (show (0 : ℤ) ≤ (q : ℤ) - 2 by omega)]
  have hdiv : 0 ≤ (((d : ℤ) - 3) * ((q : ℤ) - 1) - 1) / 2 :=
    Int.ediv_nonneg hnum (by norm_num)
  have hcast : ((auxiliaryDegree q d : ℕ) : ℤ) =
      (((d : ℤ) - 3) * ((q : ℤ) - 1) - 1) / 2 := by
    exact Int.toNat_of_nonneg hdiv
  have hfloor : 2 * ((((d : ℤ) - 3) * ((q : ℤ) - 1) - 1) / 2) ≤
      ((d : ℤ) - 3) * ((q : ℤ) - 1) - 1 := by omega
  have hqcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  have hfinal : (2 : ℤ) * (auxiliaryDegree q d : ℤ) + 3 * ((q - 1 : ℕ) : ℤ) <
      (d : ℤ) * ((q - 1 : ℕ) : ℤ) := by
    rw [hcast, hqcast]
    nlinarith
  exact_mod_cast hfinal

end ExpandingCodes.PolynomialStretch
