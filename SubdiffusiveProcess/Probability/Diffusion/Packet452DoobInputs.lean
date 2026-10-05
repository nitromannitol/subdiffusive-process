module

public import Mathlib.Probability.Martingale.OptionalStopping

@[expose] public section

/-!
# Absolute submartingales and discrete filtrations for `maximal_ineq`

The two ingredients are the absolute-value submartingale and
discretization to `Filtration ℕ`.

* `Martingale.abs_submartingale` — **Mathlib has no `Submartingale.abs`.**  It has
  `Submartingale.pos`, `Submartingale.add` and `Martingale.neg`; This is the missing composition,
  through `|x| = x⁺ + (-x)⁺`.
* `comapFiltration`, `Submartingale.comp_monotone` — a submartingale restricted along **any**
  monotone time map is a submartingale for the pulled-back filtration.  With
  `σ k = grid (min k N)` this is exactly the "freeze after the last grid point"
  construction, which is what turns the `NNReal`-indexed Dynkin martingale into a genuine
  `Filtration ℕ`-submartingale.  Stated for an arbitrary monotone map rather than for the dyadic
  grid, because nothing in the argument uses the grid's shape; `monotone_min_const` is the freezing
  map itself.
* `Martingale.abs_grid_submartingale` — the two composed, delivering exactly the hypotheses
  `MeasureTheory.maximal_ineq` asks for: a nonnegative `Filtration ℕ`-submartingale.

## What remains in the Doob unit

The strong `L²` inequality itself, with constant `4`.  Mathlib's `maximal_ineq` is the **weak**
(Chebyshev) form, so the derivation of the strong `Lᵖ` bound is: layer cake (`MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul` with
`g t = 2t`, giving `∫ S² = ∫₀^∞ 2ε·μ{S ≥ ε}dε`), then `maximal_ineq` on the inner measure, then
Tonelli to reach `2∫ f_n·S`, then Hölder (`ENNReal.lintegral_mul_le_Lp_mul_Lq` at `p = q = 2`), then
cancel one `‖S‖₂` -- which needs `‖S‖₂ < ∞`, obtained by truncating `S` to `S ⊓ M` (the weak
inequality survives the truncation, since `{S ⊓ M ≥ ε} ⊆ {S ≥ ε}`) and passing `M → ∞` by monotone
convergence.  Then the grid bound goes to the continuous supremum by monotone convergence along the
nested dyadic grids, with no loss in the constant.
-/

set_option autoImplicit false
open MeasureTheory Filter
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {Ω ι : Type*} [Preorder ι] {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ι m0} {f : ι → Ω → ℝ}

/-- **The absolute value of a martingale is a submartingale.**  Mathlib has `Submartingale.pos`,
`Submartingale.add` and `Martingale.neg` but no `Submartingale.abs`; This is the missing
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
`σ k = grid (min k N)` This is the "freeze after the last grid point" construction that turns the
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
