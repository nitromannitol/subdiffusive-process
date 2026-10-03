module

public import SubdiffusiveProcess.Meyers.Defs

@[expose] public section

/-! Dimension `0`: `Vec 0` is a point, all gradients vanish, and the estimate is trivial. -/

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Meyers

theorem e2_dim_zero (p epsilon : ℝ) : E2Body 0 p epsilon 1 := by
  intro x0 l hl a a0 ha0 haM hnear F Kf hFM hKf hFb u heq
  have hG : (fun x => Real.sqrt (∑ i : Fin 0, (u.grad x i) ^ 2)) = fun _ => 0 := by
    funext x
    simp
  have h0 : ∀ (q : ℝ≥0∞) (μ : Measure (Vec 0)), eLpNorm (fun _ : Vec 0 => (0 : ℝ)) q μ = 0 :=
    fun q μ => eLpNorm_zero
  rw [hG]
  refine ⟨by simp, ?_⟩
  rw [h0, h0]
  simp only [ENNReal.toReal_zero, zero_div, mul_zero, zero_add, one_mul]
  positivity

end SubdiffusiveProcess.Meyers
