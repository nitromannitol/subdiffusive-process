module

public import Mathlib

@[expose] public section

/-!
# Almost-everywhere order constraints pass to `L²` limits
-/
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.E7

/-- A one-sided pointwise bound holding almost everywhere for each term of an `L²`-convergent
sequence holds for the limit. -/
theorem ae_le_of_tendsto_Lp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {gn : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ} (h : Tendsto gn atTop (𝓝 g)) {B : α → ℝ}
    (hB : AEStronglyMeasurable B μ) (hle : ∀ n, gn n ≤ᵐ[μ] B) : g ≤ᵐ[μ] B := by
  have hmeas : AEStronglyMeasurable (fun x => max (g x - B x) 0) μ :=
    ((Lp.stronglyMeasurable g).aestronglyMeasurable.sub hB).sup aestronglyMeasurable_const
  have hdom : ∀ n, eLpNorm (fun x => max (g x - B x) 0) 2 μ ≤ eLpNorm (⇑(g - gn n)) 2 μ := by
    intro n
    refine eLpNorm_mono_ae hmeas ?_
    filter_upwards [hle n, Lp.coeFn_sub g (gn n)] with x hx hsub
    rw [hsub, Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (abs_nonneg _)
    exact le_trans (by linarith) (le_abs_self _)
  have hlim : Tendsto (fun n => eLpNorm (⇑(g - gn n)) 2 μ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ‖g - gn n‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 h)
      exact this.congr fun n => by rw [norm_sub_rev]
    have h2 := (ENNReal.tendsto_ofReal h1)
    simp only [ENNReal.ofReal_zero] at h2
    refine h2.congr fun n => ?_
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  have hzero : eLpNorm (fun x => max (g x - B x) 0) 2 μ = 0 :=
    le_antisymm (ge_of_tendsto' hlim hdom) bot_le
  have := (eLpNorm_eq_zero_iff (by norm_num)).1 hzero
  filter_upwards [this] with x hx
  have : max (g x - B x) 0 = 0 := hx
  have h2 := le_max_left (g x - B x) 0
  linarith

end SubdiffusiveProcess.E7
