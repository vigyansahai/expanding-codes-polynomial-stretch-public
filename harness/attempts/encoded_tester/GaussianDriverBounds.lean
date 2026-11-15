import ExpandingCodes.Computation.GaussianDriver

set_option autoImplicit false

namespace ExpandingCodes.Computation.GaussianDriver
open NKtLB GaussianProgram GaussianGrid EncodedGaussian
open ExpandingCodes.PolynomialStretch

theorem sourceBudget_le (m M : ℕ) (hm : m ≤ M) :
    10*M+13+m*(roundBudget m M+2)+2 ≤ 100000*(M+1)^9 := by
  let X := M+1
  have hx : 1 ≤ X := by omega
  have hmX : m ≤ X := by omega
  have hMX : M ≤ X := by omega
  have hp (a b : ℕ) (hab : a ≤ b) : X^a ≤ X^b := Nat.pow_le_pow_right hx hab
  have h1 (a : ℕ) : 1 ≤ X^a := one_le_pow₀ hx
  have hs : (X^2+1)^2 ≤ 4*X^4 := by
    calc
      (X^2+1)^2 ≤ (2*X^2)^2 := Nat.pow_le_pow_left (by have := h1 2;omega) 2
      _ = 4*X^4 := by ring
  have hc : cellBudget M ≤ 25000*X^6 := by
    change 100*X+460*(X^2+1)^2+20000*X^6+3000*X^5+7 ≤ _
    have h16 := hp 1 6 (by decide)
    have h46 := hp 4 6 (by decide)
    have h56 := hp 5 6 (by decide)
    have h06 := h1 6
    simp only [pow_one] at h16
    omega
  have ht : tickBudget M ≤ 26000*X^6 := by
    unfold tickBudget
    have h16 := hp 1 6 (by decide)
    have h06 := h1 6
    simp only [pow_one] at h16
    omega
  have hr : rowBudget m M ≤ 27000*X^7 := by
    calc
      rowBudget m M ≤ X*(26000*X^6+2)+20*X := by
        unfold rowBudget
        exact Nat.add_le_add (Nat.mul_le_mul hmX (by omega)) (by rfl)
      _ = 26000*X^7+22*X := by ring
      _ ≤ 27000*X^7 := by
        have hh := hp 1 7 (by decide)
        simp only [pow_one] at hh
        omega
  have hg : gridBudget m M ≤ 28000*X^8 := by
    calc
      gridBudget m M ≤ 20*X+X*(27000*X^7+2)+2 := by
        unfold gridBudget
        exact Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul hmX (by omega)) _) (by rfl)
      _ = 27000*X^8+22*X+2 := by ring
      _ ≤ 28000*X^8 := by
        have hh := hp 1 8 (by decide)
        have h08 := h1 8
        simp only [pow_one] at hh
        omega
  have hsuccess : successBudget m M ≤ 50000*X^8 := by
    change 21000*X^7+gridBudget m M+10 ≤ _
    have h78 := hp 7 8 (by decide)
    have h08 := h1 8
    omega
  have hscan : scanBudget m M ≤ 500*X^6 := by
    calc
      scanBudget m M ≤ X^2*(400*X^4+5)+1 := by
        unfold scanBudget
        apply Nat.add_le_add_right
        apply Nat.mul_le_mul
        · simpa only [pow_two] using Nat.mul_le_mul hmX hmX
        · change 100*(X^2+1)^2+5 ≤ _
          omega
      _ = 400*X^6+5*X^2+1 := by ring
      _ ≤ 500*X^6 := by
        have hh := hp 2 6 (by decide)
        have h06 := h1 6
        omega
  have hround : roundBudget m M ≤ 51000*X^8 := by
    unfold roundBudget
    have h18 := hp 1 8 (by decide)
    have h68 := hp 6 8 (by decide)
    have h08 := h1 8
    simp only [pow_one] at h18
    omega
  calc
    10*M+13+m*(roundBudget m M+2)+2 ≤ 10*X+13+X*(51000*X^8+2)+2 := by
      exact Nat.add_le_add (Nat.add_le_add (by omega) (Nat.mul_le_mul hmX (by omega))) (by rfl)
    _ = 51000*X^9+12*X+15 := by ring
    _ ≤ 100000*X^9 := by
      have hh := hp 1 9 (by decide)
      have h09 := h1 9
      simp only [pow_one] at hh
      omega

theorem rankProgram_stops_rank (ell : ℕ) (h : 0 < ell) (m M : ℕ) (inp : Inputs) (d : Store)
    (hc : Common ell h m M d) (A B : Gaussian.Table (Fin (2^ell)) m m)
    (ha : MatrixStored d 0 A) (hb : MatrixStored d 1 B) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 4260),t ≤ 100000*(M+1)^9 ∧
      rankProgram.Stops inp (d.toCfg rankProgram.entry) t e ∧ Common ell h m M e.store ∧
      e.reg 48 = (Gaussian.toMatrix (mapTable (BinaryField.elements ell h) A)).rank ∧
      e.reg 62 = 0 ∧ e.roHead = d.roHead ∧ e.output = d.output := by
  obtain ⟨t,e,ht,he,heo,hr,h62,hro,hout⟩ := rankProgram_stops ell h m M inp d hc A B ha hb
  have hm : m ≤ M := by rw [← hc.rows];exact hc.state.bounded 49
  refine ⟨t,e,ht.trans (sourceBudget_le m M hm),he,heo,?_,h62,hro,hout⟩
  exact hr.trans (PaddedGaussian.iterate_rows_correct
    (BinaryField.indexOperations_interpretation ell h) (binary_zeroIndex_val ell) A)

theorem rankProgram_stops_canonical (degree n M : ℕ) (inp : Inputs) (d : Store)
    (y : Word (rowCount degree n))
    (hc : Common (fieldExponent degree n) (fieldExponent_pos degree n) (rowCount degree n) M d)
    (B : Gaussian.Table (Fin (fieldSize degree n)) (rowCount degree n) (rowCount degree n))
    (ha : MatrixStored d 0 (binaryTestTable degree n y)) (hb : MatrixStored d 1 B) :
    ∃ (t : ℕ) (e : TapeCfg 64 2 4260),t ≤ 100000*(M+1)^9 ∧
      rankProgram.Stops inp (d.toCfg rankProgram.entry) t e ∧
      Common (fieldExponent degree n) (fieldExponent_pos degree n) (rowCount degree n) M e.store ∧
      e.reg 48 = (testMatrix (binaryGeometry degree n) y).rank ∧
      e.reg 62 = 0 ∧ e.roHead = d.roHead ∧ e.output = d.output := by
  obtain ⟨t,e,ht,he,heo,hr,h62,hro,hout⟩ := rankProgram_stops
    (fieldExponent degree n) (fieldExponent_pos degree n) (rowCount degree n) M inp d hc
      (binaryTestTable degree n y) B ha hb
  have hm : rowCount degree n ≤ M := by rw [← hc.rows];exact hc.state.bounded 49
  exact ⟨t,e,ht.trans (sourceBudget_le _ _ hm),he,heo,
    hr.trans (PaddedGaussian.binary_iterate_rank degree n y),h62,hro,hout⟩

#print axioms sourceBudget_le
#print axioms rankProgram_stops_rank
#print axioms rankProgram_stops_canonical

end ExpandingCodes.Computation.GaussianDriver
