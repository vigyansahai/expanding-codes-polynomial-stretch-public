import ExpandingCodes.Computation.ParameterSetup

set_option autoImplicit false
namespace ExpandingCodes.Computation
open NKtLB
namespace ParameterPrograms
variable {R B L : ℕ}

/-- Every source instruction changes any one unary register by at most one.
This rules out hidden aggregate counters at every intermediate source state. -/
theorem source_step_reg_le (P : TapeProgram R B L) (inp : Inputs)
    (c : TapeCfg R B L) (j : Fin R) : (P.step inp c).reg j≤c.reg j+1 := by
  cases h : P.code c.pc <;> simp only [TapeProgram.step,h]
  all_goals try omega
  case inc r k =>
    by_cases hj : j=r
    · subst j; simp
    · simpa [Function.update_of_ne hj] using Nat.le_succ (c.reg j)
  case dec r z p =>
    split
    · exact Nat.le_succ _
    · by_cases hj : j=r
      · subst j; simp; omega
      · simpa [Function.update_of_ne hj] using Nat.le_succ (c.reg j)

theorem source_exec_reg_le {P : TapeProgram R B L} {inp : Inputs}
    {c e : TapeCfg R B L} {t : ℕ} (h : P.Exec inp c t e) (j : Fin R) :
    e.reg j≤c.reg j+t := by
  induction h with
  | refl c => omega
  | @step c z e t active next tail ih =>
    have hs := source_step_reg_le P inp c j
    rw [next] at hs
    omega

theorem setup_trace_counter_bound (r : Fin 14 → Fin R) (d k : ℕ)
    (inp : Inputs) (M t : ℕ) (σ : TapeStore R B) (hσ : ∀ j, σ.reg j≤M)
    (ht : t≤ setupTimeBound d M) (c : TapeCfg R B (setupLabels d k))
    (h : (setup r d k).Exec inp (σ.toCfg (setup (B := B) r d k).entry) t c) :
    ∀ j, c.reg j≤M+setupTimeBound d M := by
  intro j
  have hreg := source_exec_reg_le h j
  have := hσ j
  simp only [TapeStore.toCfg] at hreg
  omega

/-- The same polynomial envelope covers every intermediate unary register,
not only the final counters exposed by setup_stops. -/
theorem setup_running_counters_polynomial (r : Fin 14 → Fin R) (d k : ℕ) :
    ∃ C a, ∀ (inp : Inputs) (M t : ℕ) (σ : TapeStore R B),
      (∀ j, σ.reg j≤M) → t≤ setupTimeBound d M →
      ∀ c, (setup r d k).Exec inp (σ.toCfg (setup (B := B) r d k).entry) t c →
      ∀ j, c.reg j≤C*(M+1)^a := by
  obtain ⟨C,a,hpoly⟩ := PolynomialMajorant.id.add (setup_bounds_polynomial d).1
  exact ⟨C,a,fun inp M t σ hσ ht c h j =>
    (setup_trace_counter_bound r d k inp M t σ hσ ht c h j).trans (hpoly M)⟩

/-- The actual NKtLB compilation of unary setup inherits the checked finite
source execution with its proved constant1+2t overhead. -/
theorem setupInput_compiled (r : Fin 14 → Fin R) (hr : Function.Injective r)
    (d k : ℕ) (hk : 0<k) :
    ∃ C a, ∀ (n : ℕ) (hn : 2≤n) (hnk : k≤n) (inp : Inputs) (tail : List Bool),
      inp.input=List.replicate n true ++ false :: tail →
      ∃ (t : ℕ) (z : TapeCfg R B (5+setupLabels d k)), t≤C*(n+1)^a ∧
        (TapeCompiler.compile (setupInput (B := B) r d k)).HaltsWith (Set.univ) inp t (bitsSym z.output) ∧
        z.store=setupStore r d k (SizeReader.sizeStore (r 0) n (setupInput (B := B) r d k).init.store) := by
  obtain ⟨C,a,hsetup⟩ := setupInput_unary (B := B) r hr d k hk
  refine ⟨2*C+1,a,?_⟩
  intro n hn hnk inp tail hi
  obtain ⟨t,z,ht,hstop,hstore,hframe⟩ := hsetup n hn hnk inp tail
    (setupInput (B := B) r d k).init.store (by intro j; rfl) rfl hi
  have hp : 1≤(n+1)^a := Nat.one_le_pow _ _ (by omega)
  refine ⟨1+2*t,z,?_,hstop.compile Set.univ,hstore⟩
  nlinarith

#print axioms source_exec_reg_le
#print axioms setup_running_counters_polynomial
#print axioms setupInput_compiled
end ParameterPrograms
end ExpandingCodes.Computation
