import ExpandingCodes.Construction.Growth
import ExpandingCodes.Computation.SamplerTables

set_option autoImplicit false

namespace ExpandingCodes.Computation

/-- A uniform numerical envelope. This predicate bounds a specified function;
it says nothing about an algorithm unless a source execution theorem supplies
that function as its actual step count or counter bound. -/
def PolynomialBound (f : ℕ → ℕ) : Prop :=
  ∃ C a : ℕ, ∀ n ≥ 2, f n ≤ C*(n+1)^a

namespace PolynomialBound
variable {f g : ℕ → ℕ}

theorem const (c : ℕ) : PolynomialBound (fun _ => c) :=
  ⟨c,0,by intro n _; simp⟩

theorem identity : PolynomialBound (fun n => n) :=
  ⟨1,1,by intro n _; simp⟩

theorem of_le (hf : PolynomialBound f) (h : ∀ n ≥ 2, g n ≤ f n) : PolynomialBound g := by
  obtain ⟨C,a,hf⟩ := hf
  exact ⟨C,a,fun n hn => (h n hn).trans (hf n hn)⟩

theorem add (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun n => f n+g n) := by
  obtain ⟨C,a,hf⟩ := hf
  obtain ⟨D,b,hg⟩ := hg
  refine ⟨C+D,max a b,?_⟩
  intro n hn
  have hp : 1 ≤ n+1 := by omega
  have ha := (hf n hn).trans
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_right hp (le_max_left a b)))
  have hb := (hg n hn).trans
    (Nat.mul_le_mul_left D (Nat.pow_le_pow_right hp (le_max_right a b)))
  calc
    f n+g n ≤ C*(n+1)^max a b+D*(n+1)^max a b := Nat.add_le_add ha hb
    _ = _ := by ring

theorem mul (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun n => f n*g n) := by
  obtain ⟨C,a,hf⟩ := hf
  obtain ⟨D,b,hg⟩ := hg
  refine ⟨C*D,a+b,?_⟩
  intro n hn
  simpa [pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    Nat.mul_le_mul (hf n hn) (hg n hn)

theorem pow (hf : PolynomialBound f) (r : ℕ) : PolynomialBound (fun n => (f n)^r) := by
  obtain ⟨C,a,hf⟩ := hf
  refine ⟨C^r,a*r,?_⟩
  intro n hn
  simpa [mul_pow, pow_mul] using Nat.pow_le_pow_left (hf n hn) r

theorem max (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun n => max (f n) (g n)) :=
  (hf.add hg).of_le (fun n _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))

theorem natLog (base : ℕ) (hf : PolynomialBound f) :
    PolynomialBound (fun n => Nat.log base (f n)) :=
  hf.of_le (fun n _ => Nat.log_le_self base (f n))

theorem div (hf : PolynomialBound f) (k : ℕ) : PolynomialBound (fun n => f n/k) :=
  hf.of_le (fun n _ => Nat.div_le_self (f n) k)

end PolynomialBound
end ExpandingCodes.Computation

namespace ExpandingCodes.PolynomialStretch
open ExpandingCodes.Computation

theorem fieldSize_polynomial (d : ℕ) (hd : 0 < d) :
    PolynomialBound (fieldSize d) := by
  refine ⟨2,2*d,?_⟩
  intro n hn
  exact (fieldSize_upper d n hd hn).le.trans
    (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.le_succ n) _))

theorem fieldExponent_polynomial (d : ℕ) (hd : 0 < d) :
    PolynomialBound (fieldExponent d) := by
  apply (fieldSize_polynomial d hd).of_le
  intro n _
  exact (Nat.lt_two_pow_self : fieldExponent d n < 2 ^ fieldExponent d n).le

theorem rowCount_polynomial (d : ℕ) (hd : 0 < d) :
    PolynomialBound (rowCount d) := (fieldSize_polynomial d hd).pow d

theorem samplerEntropy_polynomial (d k : ℕ) (hd : 0 < d) :
    PolynomialBound (fun n => SamplerTables.entropy d n k (Nat.log 2 (n/k))) := by
  have hq := fieldSize_polynomial d hd
  have he := fieldExponent_polynomial d hd
  have hbeta := (PolynomialBound.identity.div k).natLog 2
  exact (((((PolynomialBound.const 2).mul (PolynomialBound.const k)).mul hq).mul
    (PolynomialBound.const d)).mul he).add
    (((((PolynomialBound.const k).mul hq).mul hq).mul hq).mul hbeta)

/-- A single polynomial can cover both the actual proved time bound and the
required entropy. Raising its coefficient to 2*C+1 leaves compiler overhead. -/
theorem common_polynomial_envelope {f g : ℕ → ℕ}
    (hf : PolynomialBound f) (hg : PolynomialBound g) :
    ∃ C a : ℕ, ∀ n ≥ 2, f n ≤ C*(n+1)^a ∧ g n ≤ (2*C+1)*(n+1)^a := by
  obtain ⟨C,a,h⟩ := hf.add hg
  refine ⟨C,a,?_⟩
  intro n hn
  have hh := h n hn
  constructor
  · exact (Nat.le_add_right (f n) (g n)).trans hh
  · exact ((Nat.le_add_left (g n) (f n)).trans hh).trans
      (Nat.mul_le_mul_right _ (by omega))

#print axioms samplerEntropy_polynomial
#print axioms common_polynomial_envelope
end ExpandingCodes.PolynomialStretch
