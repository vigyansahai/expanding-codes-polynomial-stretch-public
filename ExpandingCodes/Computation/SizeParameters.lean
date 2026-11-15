import Definitions.Def_ExpandingCodes_PolynomialStretch_Parameters

set_option autoImplicit false
namespace ExpandingCodes.Computation
namespace SizeParameters

/-- Scalar specification of the actual compare/double loop. This is not a
machine instruction: the source implementation must use unary comparison and
addition to realize one step. -/
def ceilStep (p : ℕ) (x : ℕ × ℕ) : ℕ × ℕ :=
  if x.1<p then (2*x.1,x.2+1) else x

def ceilIter (p : ℕ) : ℕ → (ℕ × ℕ) → (ℕ × ℕ)
  | 0, x => x
  | t+1, x => ceilIter p t (ceilStep p x)

/-- A p-step budget is sufficient: every active doubling increases q by at
least one. The separate q<2p invariant bounds all unary arithmetic values. -/
theorem ceilIter_invariant (p t q ell : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hb : q<2*p) (he : q=2^ell)
    (hbudget : p ≤ q+t) (hell : ell+t ≤ p) :
    p ≤ (ceilIter p t (q,ell)).1 ∧ (ceilIter p t (q,ell)).1<2*p ∧
      (ceilIter p t (q,ell)).1=2^(ceilIter p t (q,ell)).2 ∧
      (ceilIter p t (q,ell)).2 ≤ p := by
  induction t generalizing q ell with
  | zero => simpa [ceilIter] using And.intro hbudget ⟨hb,he,hell⟩
  | succ t ih =>
    by_cases hlt : q<p
    · have he' : 2*q=2^(ell+1) := by rw [pow_succ, ← he]; omega
      have ht := ih (2*q) (ell+1) (by omega) (by omega) he' (by omega) (by omega)
      simpa [ceilIter, ceilStep, hlt] using ht
    · have ht := ih q ell hq hb he (by omega) (by omega)
      simpa [ceilIter, ceilStep, hlt] using ht

theorem power_clog_unique (p ell : ℕ) (hp : p ≤ 2^ell) (hb : 2^ell<2*p) :
    ell=Nat.clog 2 p := by
  have hle : Nat.clog 2 p ≤ ell := (Nat.clog_le_iff_le_pow (by decide)).mpr hp
  apply Nat.le_antisymm _ hle
  by_contra hn
  have ht : Nat.clog 2 p+1 ≤ ell := by omega
  have hpw := Nat.pow_le_pow_right (show 0<2 by decide) ht
  have hpc := Nat.le_pow_clog (by decide : 1<2) p
  rw [pow_succ] at hpw
  omega

theorem ceilIter_exact (p : ℕ) (hp : 1 ≤ p) :
    ceilIter p p (1,0) = (2^Nat.clog 2 p,Nat.clog 2 p) := by
  have h := ceilIter_invariant p p 1 0 hp (by omega) (by omega) rfl (by omega) (by omega)
  have he := power_clog_unique p (ceilIter p p (1,0)).2
    (by simpa only [← h.2.2.1] using h.1) (by simpa only [← h.2.2.1] using h.2.1)
  apply Prod.ext
  · simpa [he] using h.2.2.1
  · exact he

theorem ceilIter_fieldExponent (d n : ℕ) (hp : 2 ≤ n^(2*d)) :
    (ceilIter (n^(2*d)) (n^(2*d)) (1,0)).2 =
      ExpandingCodes.PolynomialStretch.fieldExponent d n := by
  rw [ceilIter_exact _ (by omega)]
  have hc : 1 ≤ Nat.clog 2 (n^(2*d)) := Nat.clog_pos (by decide) (by omega)
  simp [ExpandingCodes.PolynomialStretch.fieldExponent, max_eq_right hc]

/-- Scalar specification of doubling while twice the current power still fits. -/
def floorStep (u : ℕ) (x : ℕ × ℕ) : ℕ × ℕ :=
  if 2*x.1≤u then (2*x.1,x.2+1) else x

def floorIter (u : ℕ) : ℕ → (ℕ × ℕ) → (ℕ × ℕ)
  | 0, x => x
  | t+1, x => floorIter u t (floorStep u x)

theorem floorIter_invariant (u t b beta : ℕ)
    (hu : 1 ≤ u) (hb : 1 ≤ b) (hbu : b≤u) (he : b=2^beta)
    (hbudget : u<2*b ∨ u≤b+t) (hbeta : beta+t≤u) :
    (floorIter u t (b,beta)).1≤u ∧ u<2*(floorIter u t (b,beta)).1 ∧
      (floorIter u t (b,beta)).1=2^(floorIter u t (b,beta)).2 ∧
      (floorIter u t (b,beta)).2≤u := by
  induction t generalizing b beta with
  | zero =>
    simp only [floorIter, Prod.fst, Prod.snd, Nat.add_zero] at *
    exact ⟨hbu, by omega, he, hbeta⟩
  | succ t ih =>
    by_cases hle : 2*b≤u
    · have he' : 2*b=2^(beta+1) := by rw [pow_succ, ← he]; omega
      have ht := ih (2*b) (beta+1) (by omega) hle he' (Or.inr (by omega)) (by omega)
      simpa [floorIter, floorStep, hle] using ht
    · have ht := ih b beta hb hbu he (Or.inl (by omega)) (by omega)
      simpa [floorIter, floorStep, hle] using ht

theorem power_log_unique (u beta : ℕ) (hb : 2^beta≤u) (hu : u<2*(2^beta)) :
    beta=Nat.log 2 u := by
  symm
  exact Nat.log_eq_of_pow_le_of_lt_pow hb (by simpa [pow_succ, Nat.mul_comm] using hu)

theorem floorIter_exact (u : ℕ) (hu : 1 ≤ u) :
    floorIter u u (1,0) = (2^Nat.log 2 u,Nat.log 2 u) := by
  have h := floorIter_invariant u u 1 0 hu (by omega) hu rfl (Or.inr (by omega)) (by omega)
  have he := power_log_unique u (floorIter u u (1,0)).2
    (by simpa only [← h.2.2.1] using h.1) (by simpa only [← h.2.2.1] using h.2.1)
  apply Prod.ext
  · simpa [he] using h.2.2.1
  · exact he

#print axioms ceilIter_invariant
#print axioms ceilIter_exact
#print axioms ceilIter_fieldExponent
#print axioms floorIter_invariant
#print axioms floorIter_exact
end SizeParameters
end ExpandingCodes.Computation
