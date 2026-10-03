module

public import Mathlib.Probability.Martingale.OptionalStopping

@[expose] public section




set_option autoImplicit false
open MeasureTheory Filter
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {Ω ι : Type*} [Preorder ι] {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ι m0} {f : ι → Ω → ℝ}

/-- **The absolute value of a martingale is a submartingale.**  Mathlib has `Submartingale.pos`,
`Submartingale.add` and `Martingale.neg` but no `Submartingale.abs`; this is the missing
composition, through `|x| = x⁺ + (-x)⁺`. -/
theorem Martingale.abs_submartingale (hf : Martingale f ℱ μ) :
    Submartingale (fun i ω => |f i ω|) ℱ μ := by
  have hpos : Submartingale (f⁺) ℱ μ := hf.submartingale.pos
  have hneg : Submartingale ((-f)⁺) ℱ μ := hf.neg.submartingale.pos
  have heq : (fun i ω => |f i ω|) = f⁺ + (-f)⁺ := by
    funext i ω
    simp only [Pi.add_apply, Pi.neg_apply, posPart_def, Pi.sup_apply, Pi.zero_apply]
    rcases le_total (0 : ℝ) (f i ω) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h, add_zero]
    · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h, zero_add]
  rw [heq]
  exact hpos.add hneg

/-! ## Restriction of a submartingale to a monotone (frozen) time grid -/

/-- A filtration pulled back along a monotone time map. -/
def comapFiltration {ι' : Type*} [Preorder ι'] (ℱ : Filtration ι m0) (σ : ι' → ι)
    (hσ : Monotone σ) : Filtration ι' m0 where
  seq := fun k => ℱ (σ k)
  mono' := fun _ _ hij => ℱ.mono (hσ hij)
  le' := fun k => ℱ.le (σ k)

@[simp] theorem comapFiltration_apply {ι' : Type*} [Preorder ι'] (ℱ : Filtration ι m0)
    (σ : ι' → ι) (hσ : Monotone σ) (k : ι') : comapFiltration ℱ σ hσ k = ℱ (σ k) := rfl

/-- **A submartingale restricted to a monotone family of times is a submartingale.**  With
`σ k = grid (min k N)` this is the "freeze after the last grid point" construction that turns the
continuous-time martingale into a genuine `Filtration ℕ`-submartingale, which is what
`MeasureTheory.maximal_ineq` requires. -/
theorem Submartingale.comp_monotone {ι' : Type*} [Preorder ι'] {g : ι → Ω → ℝ}
    (hf : Submartingale g ℱ μ) (σ : ι' → ι) (hσ : Monotone σ) :
    Submartingale (fun k => g (σ k)) (comapFiltration ℱ σ hσ) μ :=
  ⟨fun k => hf.1 (σ k), fun i j hij => hf.2.1 (σ i) (σ j) (hσ hij), fun k => hf.2.2 (σ k)⟩

/-- The frozen dyadic index map: monotone, and eventually constant at `N`. -/
theorem monotone_min_const (N : ℕ) : Monotone fun k : ℕ => min k N :=
  fun _ _ hij => min_le_min hij le_rfl

/-- **The input `maximal_ineq` needs, assembled.**  The absolute value of a martingale, restricted
to a monotone frozen grid, is a nonnegative `Filtration ℕ`-submartingale. -/
theorem Martingale.abs_grid_submartingale (hf : Martingale f ℱ μ)
    (σ : ℕ → ι) (hσ : Monotone σ) :
    Submartingale (fun k ω => |f (σ k) ω|) (comapFiltration ℱ σ hσ) μ ∧
      (0 : ℕ → Ω → ℝ) ≤ fun k ω => |f (σ k) ω| :=
  ⟨Submartingale.comp_monotone (Martingale.abs_submartingale hf) σ hσ, fun _ _ => abs_nonneg _⟩

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
