import ExpandingCodes.Computation.ParameterPrograms

set_option autoImplicit false
namespace ExpandingCodes.Computation
namespace ParameterPrograms

/-- A scalar polynomial majorant. This is only a closure lemma for the explicit
source-step bounds proved by the actual finite programs. -/
def PolynomialMajorant (f : ℕ → ℕ) : Prop := ∃ C a, ∀ n, f n≤C*(n+1)^a

namespace PolynomialMajorant

theorem const (C : ℕ) : PolynomialMajorant (fun _ => C) := ⟨C,0,by simp⟩
theorem id : PolynomialMajorant (fun n => n) := ⟨1,1,by intro n; simp⟩

theorem mono {f g : ℕ → ℕ} (hg : PolynomialMajorant g) (hfg : ∀ n, f n≤g n) :
    PolynomialMajorant f := by
  obtain ⟨C,a,h⟩ := hg
  exact ⟨C,a,fun n => (hfg n).trans (h n)⟩

theorem add {f g : ℕ → ℕ} (hf : PolynomialMajorant f) (hg : PolynomialMajorant g) :
    PolynomialMajorant (fun n => f n+g n) := by
  obtain ⟨C,a,hf⟩ := hf
  obtain ⟨D,b,hg⟩ := hg
  refine ⟨C+D,a+b,?_⟩
  intro n
  have hpa : (n+1)^a≤(n+1)^(a+b) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpb : (n+1)^b≤(n+1)^(a+b) := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    f n+g n≤C*(n+1)^a+D*(n+1)^b := Nat.add_le_add (hf n) (hg n)
    _≤C*(n+1)^(a+b)+D*(n+1)^(a+b) :=
      Nat.add_le_add (Nat.mul_le_mul_left C hpa) (Nat.mul_le_mul_left D hpb)
    _=(C+D)*(n+1)^(a+b) := by ring

theorem mul {f g : ℕ → ℕ} (hf : PolynomialMajorant f) (hg : PolynomialMajorant g) :
    PolynomialMajorant (fun n => f n*g n) := by
  obtain ⟨C,a,hf⟩ := hf
  obtain ⟨D,b,hg⟩ := hg
  refine ⟨C*D,a+b,?_⟩
  intro n
  calc
    f n*g n≤(C*(n+1)^a)*(D*(n+1)^b) := Nat.mul_le_mul (hf n) (hg n)
    _=(C*D)*(n+1)^(a+b) := by rw [pow_add]; ring

theorem pow {f : ℕ → ℕ} (hf : PolynomialMajorant f) (e : ℕ) :
    PolynomialMajorant (fun n => (f n)^e) := by
  obtain ⟨C,a,hf⟩ := hf
  refine ⟨C^e,a*e,?_⟩
  intro n
  calc
    (f n)^e≤(C*(n+1)^a)^e := Nat.pow_le_pow_left (hf n) e
    _=C^e*(n+1)^(a*e) := by rw [mul_pow,pow_mul]

theorem comp {f g : ℕ → ℕ} (hf : PolynomialMajorant f) (hg : PolynomialMajorant g) :
    PolynomialMajorant (fun n => f (g n)) := by
  obtain ⟨C,a,hf⟩ := hf
  obtain ⟨D,b,hg⟩ := (hg.add (const 1)).pow a
  refine ⟨C*D,b,?_⟩
  intro n
  calc
    f (g n)≤C*(g n+1)^a := hf _
    _≤C*(D*(n+1)^b) := Nat.mul_le_mul_left C (hg n)
    _=(C*D)*(n+1)^b := by ring

end PolynomialMajorant

def powerCounterBound (e M : ℕ) : ℕ := (e+1)*(M+1)^(e+1)
def powerTimeBound (e M : ℕ) : ℕ := 512*(e+1)^3*(M+1)^(2*(e+1))
def ceilingCounterBound (M : ℕ) : ℕ := 2*M+2
def ceilingTimeBound (M : ℕ) : ℕ := 512*(M+1)^2
def divisionTimeBound (M : ℕ) : ℕ := 16*(M+1)
def floorCounterBound (M : ℕ) : ℕ := 2*M+4
def floorTimeBound (M : ℕ) : ℕ := 4096*(M+1)^2

theorem powerCounterBound_polynomial (e : ℕ) : PolynomialMajorant (powerCounterBound e) :=
  ⟨e+1,e+1,fun _ => Nat.le_refl _⟩
theorem powerTimeBound_polynomial (e : ℕ) : PolynomialMajorant (powerTimeBound e) :=
  ⟨512*(e+1)^3,2*(e+1),fun _ => Nat.le_refl _⟩
theorem ceilingCounterBound_polynomial : PolynomialMajorant ceilingCounterBound :=
  ⟨2,1,by intro n; simp [ceilingCounterBound]; omega⟩
theorem ceilingTimeBound_polynomial : PolynomialMajorant ceilingTimeBound :=
  ⟨512,2,fun _ => Nat.le_refl _⟩
theorem divisionTimeBound_polynomial : PolynomialMajorant divisionTimeBound :=
  ⟨16,1,by intro n; simp [divisionTimeBound]⟩
theorem floorCounterBound_polynomial : PolynomialMajorant floorCounterBound :=
  ⟨4,1,by intro n; simp [floorCounterBound]; omega⟩
theorem floorTimeBound_polynomial : PolynomialMajorant floorTimeBound :=
  ⟨4096,2,fun _ => Nat.le_refl _⟩

def setupBound₁ (d M : ℕ) : ℕ := powerCounterBound (2*d) M
def setupBound₂ (d M : ℕ) : ℕ := ceilingCounterBound (setupBound₁ d M)
def setupBound₃ (d M : ℕ) : ℕ := powerCounterBound d (setupBound₂ d M)
def setupCounterBound (d M : ℕ) : ℕ := floorCounterBound (setupBound₃ d M)
def setupTimeBound (d M : ℕ) : ℕ :=
  powerTimeBound (2*d) M+1+ceilingTimeBound (setupBound₁ d M)+1+
    powerTimeBound d (setupBound₂ d M)+1+divisionTimeBound (setupBound₃ d M)+1+
    floorTimeBound (setupBound₃ d M)

theorem setup_bounds_polynomial (d : ℕ) :
    PolynomialMajorant (setupTimeBound d) ∧ PolynomialMajorant (setupCounterBound d) := by
  have h₁ := powerCounterBound_polynomial (2*d)
  have h₂ := ceilingCounterBound_polynomial.comp h₁
  have h₃ := (powerCounterBound_polynomial d).comp h₂
  constructor
  · exact ((((((((powerTimeBound_polynomial (2*d)).add (PolynomialMajorant.const 1)).add
      (ceilingTimeBound_polynomial.comp h₁)).add (PolynomialMajorant.const 1)).add
      ((powerTimeBound_polynomial d).comp h₂)).add (PolynomialMajorant.const 1)).add
      (divisionTimeBound_polynomial.comp h₃)).add (PolynomialMajorant.const 1)).add
      (floorTimeBound_polynomial.comp h₃)
  · exact floorCounterBound_polynomial.comp h₃

#print axioms setup_bounds_polynomial
end ParameterPrograms
end ExpandingCodes.Computation
