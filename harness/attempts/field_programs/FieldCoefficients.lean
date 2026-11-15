import ExpandingCodes.Computation.BinaryPolynomial
import ExpandingCodes.Computation.FieldPrograms

set_option autoImplicit false

namespace ExpandingCodes.Computation.FieldPrograms
open NKtLB
open ExpandingCodes.PolynomialStretch.BinaryPolynomial

/-- The existing finite-field coefficient enumeration is exactly ordinary
binary digits, including its least-significant-first convention. -/
theorem indexEquiv_value (ell : ℕ) (a : Fin (2^ell)) (j : Fin ell) :
    (indexEquiv ell a j).val = a.val/2^j.val%2 := rfl

theorem indexEquiv_bit (ell : ℕ) (a : Fin (2^ell)) (j : Fin ell) :
    indexEquiv ell a j = bitEquiv (Nat.testBit a.val j.val) := by
  apply ZMod.val_injective 2
  rw [indexEquiv_value]
  change a.val/2^j.val%2 = (if Nat.testBit a.val j.val then (1 : ZMod 2) else 0).val
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases hb : a.val/2^j.val%2 = 1
  · simp [hb]
    rfl
  · have hz : a.val/2^j.val%2 = 0 := by omega
    simp [hb, hz]

/-- The monic modulus candidate has the ordinary binary index `2^ell+a`.
The equality covers every coefficient position, including the monic bit and
all the zero padding needed by the bounded convolution certificates. -/
theorem candidateCoefficient_bit (ell : ℕ) (a : Fin (2^ell)) (j : ℕ) :
    candidateCoefficient ell a j = bitEquiv (Nat.testBit (2^ell+a.val) j) := by
  by_cases he : j = ell
  · subst j
    rw [candidateCoefficient, if_pos rfl, Nat.testBit_two_pow_add_eq,
      Nat.testBit_lt_two_pow a.isLt]
    rfl
  · by_cases hj : j < ell
    · rw [candidateCoefficient, if_neg he, dif_pos hj, Nat.testBit_two_pow_add_gt hj]
      exact indexEquiv_bit ell a ⟨j, hj⟩
    · have hl : ell+1 ≤ j := by omega
      have hx : 2^ell+a.val < 2^j := by
        have hp : 2^ell+a.val < 2^(ell+1) := by
          rw [pow_succ]
          have := a.isLt
          omega
        exact hp.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hl)
      rw [candidateCoefficient, if_neg he, dif_neg hj, Nat.testBit_lt_two_pow hx]
      rfl

/-- Actual source coefficient extraction, linked to the exact index encoding
used by BinaryPolynomial and BinaryField. The field size is a runtime bound;
the finite source program still has forty-five labels. -/
theorem coefficient_stops {R B : ℕ} (r : Fin 7 → Fin R) (hr : Function.Injective r)
    (inp : Inputs) (ell : ℕ) (a : Fin (2^ell)) (j : Fin ell)
    (M : ℕ) (hM : 1 ≤ M) (d : TapeStore R B)
    (hd : ∀ s, d.reg s ≤ M) (ha : d.reg (r 0) = a.val) (hj : d.reg (r 1) = j.val) :
    ∃ t e, t ≤ 64*(M+1)^2 ∧
      (testBit r).Stops inp (d.toCfg (testBit (B := B) r).entry) t e ∧
      (e.reg (r 4) : ZMod 2) = indexEquiv ell a j ∧
      e.reg (r 0) = a.val ∧ e.reg (r 1) = j.val := by
  obtain ⟨t, e, ht, he, hstore⟩ := testBit_stops r hr inp M hM d hd
  refine ⟨t, e, ht, he, ?_, ?_, ?_⟩
  · change (e.store.reg (r 4) : ZMod 2) = _
    rw [hstore, testBitStore_bit r hr, ha, hj, indexEquiv_bit]
    cases hbit : Nat.testBit a.val j.val <;> rfl
  · change e.store.reg (r 0) = _
    rw [hstore, testBitStore_preserves r hr d 0 (Or.inl rfl), ha]
  · change e.store.reg (r 1) = _
    rw [hstore, testBitStore_preserves r hr d 1 (Or.inr rfl), hj]

#print axioms indexEquiv_bit
#print axioms candidateCoefficient_bit
#print axioms coefficient_stops
end ExpandingCodes.Computation.FieldPrograms
