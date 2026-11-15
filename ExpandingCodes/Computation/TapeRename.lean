import ExpandingCodes.Computation.TapeLoops

set_option autoImplicit false

namespace ExpandingCodes.Computation
open NKtLB

namespace TapeInstr
variable {R B S C L : ℕ}

/-- Injecting storage names changes no control flow and executes no extra
instruction. Both register and buffer counts remain fixed program parameters. -/
def renameStorage (ρ : Fin R → Fin S) (σ : Fin B → Fin C) :
    TapeInstr R B L → TapeInstr S C L
  | .halt => .halt
  | .jump j => .jump j
  | .inc r j => .inc (ρ r) j
  | .dec r z p => .dec (ρ r) z p
  | .emit b j => .emit b j
  | .read r f => .read r f
  | .buffer b f => .buffer (σ b) f

theorem renameStorage_eq_halt (ρ : Fin R → Fin S) (σ : Fin B → Fin C) (i : TapeInstr R B L) :
    i.renameStorage ρ σ = .halt ↔ i = .halt := by cases i <;> simp [renameStorage]
end TapeInstr

namespace TapeCfg
variable {R B S C L : ℕ}

def projectStorage (ρ : Fin R → Fin S) (σ : Fin B → Fin C) (c : TapeCfg S C L) : TapeCfg R B L :=
  ⟨c.pc,c.reg ∘ ρ,c.roHead,c.output,c.bufferTape ∘ σ,c.bufferHead ∘ σ⟩
end TapeCfg

namespace TapeStore
variable {R B S C L : ℕ}

def projectStorage (ρ : Fin R → Fin S) (σ : Fin B → Fin C) (d : TapeStore S C) : TapeStore R B :=
  ⟨d.reg ∘ ρ,d.roHead,d.output,d.bufferTape ∘ σ,d.bufferHead ∘ σ⟩

theorem projectStorage_toCfg (ρ : Fin R → Fin S) (σ : Fin B → Fin C)
    (d : TapeStore S C) (j : Fin L) :
    (d.toCfg j).projectStorage ρ σ = (d.projectStorage ρ σ).toCfg j := rfl
end TapeStore

namespace TapeProgram
variable {R B S C L : ℕ}

def renameStorage (ρ : Fin R → Fin S) (σ : Fin B → Fin C) (P : TapeProgram R B L) :
    TapeProgram S C L := ⟨P.entry,fun j => (P.code j).renameStorage ρ σ⟩

theorem halted_renameStorage (ρ : Fin R → Fin S) (σ : Fin B → Fin C)
    (P : TapeProgram R B L) (c : TapeCfg S C L) :
    (P.renameStorage ρ σ).halted c ↔ P.halted (c.projectStorage ρ σ) := by
  exact TapeInstr.renameStorage_eq_halt ρ σ (P.code c.pc)

theorem step_projectStorage (ρ : Fin R → Fin S) (σ : Fin B → Fin C)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (P : TapeProgram R B L) (inp : Inputs) (c : TapeCfg S C L) :
    ((P.renameStorage ρ σ).step inp c).projectStorage ρ σ =
      P.step inp (c.projectStorage ρ σ) := by
  have hr (i : Fin R) (v : ℕ) := Function.update_comp_eq_of_injective c.reg hρ i v
  have ht (b : Fin B) (v : List Sym) := Function.update_comp_eq_of_injective c.bufferTape hσ b v
  have hh (b : Fin B) (v : ℕ) := Function.update_comp_eq_of_injective c.bufferHead hσ b v
  cases hc : P.code c.pc <;>
    simp only [step,renameStorage,TapeCfg.projectStorage,TapeInstr.renameStorage,hc]
  all_goals try rfl
  all_goals try (simp only [hr,ht,hh]; rfl)
  split <;> simp_all only [hr,ht,hh,Function.comp_apply,ite_true,ite_false]

/-- Every active small-program trace lifts to the larger fixed storage frame
with exactly the same number of source steps. -/
theorem Exec.liftStorage {P : TapeProgram R B L} {inp : Inputs}
    {c d : TapeCfg R B L} {t : ℕ} (h : P.Exec inp c t d)
    (ρ : Fin R → Fin S) (σ : Fin B → Fin C)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (big : TapeCfg S C L) (hc : big.projectStorage ρ σ = c) :
    ∃ final, (P.renameStorage ρ σ).Exec inp big t final ∧ final.projectStorage ρ σ = d := by
  induction h generalizing big with
  | refl c => exact ⟨big,Exec.refl _,hc⟩
  | @step c d e t active next tail ih =>
    have hd : ((P.renameStorage ρ σ).step inp big).projectStorage ρ σ = d := by
      rw [step_projectStorage ρ σ hρ hσ,hc,next]
    obtain ⟨final,hfinal,hproj⟩ := ih ((P.renameStorage ρ σ).step inp big) hd
    refine ⟨final,Exec.step ?_ rfl hfinal,hproj⟩
    intro hh
    have hp := (halted_renameStorage ρ σ P big).mp hh
    exact active (by simpa only [hc] using hp)

theorem Stops.liftStorage {P : TapeProgram R B L} {inp : Inputs}
    {c d : TapeCfg R B L} {t : ℕ} (h : P.Stops inp c t d)
    (ρ : Fin R → Fin S) (σ : Fin B → Fin C)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (big : TapeCfg S C L) (hc : big.projectStorage ρ σ = c) :
    ∃ final, (P.renameStorage ρ σ).Stops inp big t final ∧
      final.projectStorage ρ σ = d ∧ final.output = d.output := by
  obtain ⟨final,he,hproj⟩ := h.exec.liftStorage ρ σ hρ hσ big hc
  refine ⟨final,⟨he,?_⟩,hproj,congrArg TapeCfg.output hproj⟩
  apply (halted_renameStorage ρ σ P final).mpr
  simpa only [hproj] using h.halted

theorem renameStorage_fresh (ρ : Fin R → Fin S) (σ : Fin B → Fin C)
    (P : TapeProgram R B L) (r : Fin S) (hr : ∀ i, r ≠ ρ i) :
    (P.renameStorage ρ σ).Fresh r := by
  intro j
  cases hc : P.code j <;> simp only [renameStorage,TapeInstr.renameStorage,hc,preservesRegister]
  all_goals first | trivial | exact Ne.symm (hr _)

theorem Exec.renameStorage_outside {P : TapeProgram R B L} {inp : Inputs}
    (ρ : Fin R → Fin S) (σ : Fin B → Fin C)
    {c d : TapeCfg S C L} {t : ℕ} (h : (P.renameStorage ρ σ).Exec inp c t d)
    (r : Fin S) (hr : ∀ i, r ≠ ρ i) : d.reg r = c.reg r :=
  h.reg_of_fresh (renameStorage_fresh ρ σ P r hr)

theorem Stops.liftStorage_bounded {P : TapeProgram R B L} {inp : Inputs}
    {c d : TapeCfg R B L} {t : ℕ} (h : P.Stops inp c t d)
    (ρ : Fin R → Fin S) (σ : Fin B → Fin C)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (big : TapeCfg S C L) (hc : big.projectStorage ρ σ = c)
    (M : ℕ) (hbig : ∀ r, big.reg r ≤ M) (hsmall : ∀ r, d.reg r ≤ M) :
    ∃ final, (P.renameStorage ρ σ).Stops inp big t final ∧
      final.projectStorage ρ σ = d ∧ final.output = d.output ∧ ∀ r, final.reg r ≤ M := by
  classical
  obtain ⟨final,he,hproj,hout⟩ := h.liftStorage ρ σ hρ hσ big hc
  refine ⟨final,he,hproj,hout,?_⟩
  intro r
  by_cases hr : ∃ i, ρ i = r
  · obtain ⟨i,hi⟩ := hr
    have hv : final.reg (ρ i) = d.reg i := congrArg (fun c : TapeCfg R B L => c.reg i) hproj
    rw [← hi,hv]
    exact hsmall i
  · have hn : ∀ i, r ≠ ρ i := by
      intro i hi
      exact hr ⟨i,hi.symm⟩
    exact (he.exec.renameStorage_outside ρ σ r hn).le.trans (hbig r)

theorem step_renameStorage_buffer_outside (ρ : Fin R → Fin S) (σ : Fin B → Fin C)
    (P : TapeProgram R B L) (inp : Inputs) (c : TapeCfg S C L)
    (b : Fin C) (hb : ∀ i, b ≠ σ i) :
    ((P.renameStorage ρ σ).step inp c).bufferTape b = c.bufferTape b ∧
      ((P.renameStorage ρ σ).step inp c).bufferHead b = c.bufferHead b := by
  cases hc : P.code c.pc <;> simp [step,renameStorage,TapeInstr.renameStorage,hc,hb]
  split <;> exact ⟨rfl,rfl⟩

theorem Exec.renameStorage_buffer_outside {P : TapeProgram R B L} {inp : Inputs}
    (ρ : Fin R → Fin S) (σ : Fin B → Fin C)
    {c d : TapeCfg S C L} {t : ℕ} (h : (P.renameStorage ρ σ).Exec inp c t d)
    (b : Fin C) (hb : ∀ i, b ≠ σ i) :
    d.bufferTape b = c.bufferTape b ∧ d.bufferHead b = c.bufferHead b := by
  induction h with
  | refl c => exact ⟨rfl,rfl⟩
  | @step c d e t active next tail ih =>
    have hs := step_renameStorage_buffer_outside ρ σ P inp c b hb
    rw [next] at hs
    exact ⟨ih.1.trans hs.1,ih.2.trans hs.2⟩

#print axioms step_projectStorage
#print axioms Stops.liftStorage
#print axioms Exec.renameStorage_outside
#print axioms Stops.liftStorage_bounded
#print axioms Exec.renameStorage_buffer_outside
end TapeProgram
end ExpandingCodes.Computation
