import ExpandingCodes.Computation.SourceFieldArithmetic
set_option autoImplicit false
namespace ExpandingCodes.Computation.SourceFieldArithmetic
open NKtLB FieldPrograms FieldConvolution FieldCertificates
open ExpandingCodes.PolynomialStretch BinaryPolynomial

theorem rawConvolution_one (a k : ℕ) : rawConvolution a 1 k = bitEquiv (Nat.testBit a k) := by
  unfold rawConvolution
  rw [Finset.sum_eq_single k]
  · rw [Nat.sub_self, Nat.testBit_one_zero]
    simp [bitEquiv_true]
  · intro j hj hne
    have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
    have hsub : k-j ≠ 0 := by omega
    have hb : Nat.testBit 1 (k-j) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact hsub (Nat.testBit_one_eq_true_iff_self_eq_zero.mp ht)
    rw [hb,bitEquiv_false,mul_zero]
  · simp

theorem add_matches_iff (ell : ℕ) (a b rem : Fin (2^ell)) :
    (∀ j < 3*ell+1, CoefficientMatches a.val 1 rem.val b.val 1 j) ↔
      rem = BinaryField.addIndex ell a b := by
  constructor
  · intro hmatch
    apply (indexEquiv ell).injective
    funext j
    have hj := hmatch j.val (by have := j.isLt; omega)
    unfold CoefficientMatches at hj
    rw [rawConvolution_one,rawConvolution_one] at hj
    change indexEquiv ell rem j = indexEquiv ell ((indexEquiv ell).symm
      (BinaryField.add (indexEquiv ell a) (indexEquiv ell b))) j
    rw [Equiv.apply_symm_apply]
    change indexEquiv ell rem j = indexEquiv ell a j+indexEquiv ell b j
    rw [indexEquiv_bit,indexEquiv_bit,indexEquiv_bit]
    calc
      bitEquiv (Nat.testBit rem.val j.val) =
          (bitEquiv (Nat.testBit rem.val j.val)+bitEquiv (Nat.testBit b.val j.val))+
            bitEquiv (Nat.testBit b.val j.val) := (CharTwo.add_cancel_right _ _).symm
      _ = bitEquiv (Nat.testBit a.val j.val)+bitEquiv (Nat.testBit b.val j.val) := by rw [← hj]
  · intro heq
    subst rem
    intro j hj
    unfold CoefficientMatches
    rw [rawConvolution_one,rawConvolution_one]
    have he : bitEquiv (Nat.testBit (BinaryField.addIndex ell a b).val j) =
        bitEquiv (Nat.testBit a.val j)+bitEquiv (Nat.testBit b.val j) := by
      rw [← bufferCoefficient_bit,← bufferCoefficient_bit,← bufferCoefficient_bit]
      unfold BinaryField.addIndex
      rw [Equiv.apply_symm_apply]
      unfold BinaryField.bufferCoefficient
      split_ifs <;> rfl
    rw [he]
    have hc : bitEquiv (Nat.testBit b.val j)+bitEquiv (Nat.testBit b.val j) = 0 := by
      exact CharTwo.add_self_eq_zero _
    rw [add_assoc,hc,add_zero]
end ExpandingCodes.Computation.SourceFieldArithmetic
