import SubdiffusiveProcess.Paper.lem_affine_events
open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- A uniform inverse-reference cap absorbs the source below one base mesh,
chosen before every cell. This uses the already proved small-power estimate. -/
theorem density_source_absorption {Cells : Type*}
    (d : ℕ) (eta K fsup c : ℝ) (heta : eta < 2) (hK : 0 ≤ K) (hc : 0 < c)
    (side ref : Cells → ℝ) (hside : ∀ b, 0 < side b) (Good : Cells → Prop)
    (hcap : ∀ b, Good b → (ref b)⁻¹ ≤ K * (side b) ^ (-eta)) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ b, side b ≤ r0 → Good b →
      (ref b)⁻¹ * (side b) ^ ((d : ℝ) + 2) * fsup ^ 2 ≤ c * (side b) ^ d := by
  obtain ⟨r0, hr0, hsmall⟩ := aux_lem_affine_events_mesh_exists
    (K * fsup ^ 2) (2 * eta - 2) c (mul_nonneg hK (sq_nonneg fsup)) (by linarith) hc
  refine ⟨r0, hr0, fun b hb hg => ?_⟩
  have h := hsmall (side b) (hside b) hb
  rw [show (1 : ℝ) - (2 * eta - 2) / 2 = 2 - eta by ring] at h
  calc
    (ref b)⁻¹ * (side b) ^ ((d : ℝ) + 2) * fsup ^ 2 ≤
        (K * (side b) ^ (-eta)) * (side b) ^ ((d : ℝ) + 2) * fsup ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcap b hg) (Real.rpow_nonneg (hside b).le _))
        (sq_nonneg fsup)
    _ = (K * fsup ^ 2 * (side b) ^ (2 - eta)) * (side b) ^ d := by
      rw [← Real.rpow_natCast (side b) d]
      have heq : (side b) ^ (-eta) * (side b) ^ ((d : ℝ) + 2) =
          (side b) ^ (2 - eta) * (side b) ^ (d : ℝ) := by
        rw [← Real.rpow_add (hside b), ← Real.rpow_add (hside b)]
        congr 1
        ring
      calc _ = (K * fsup ^ 2) * ((side b) ^ (-eta) * (side b) ^ ((d : ℝ) + 2)) := by ring
        _ = _ := by rw [heq]; ring
    _ ≤ c * (side b) ^ d := mul_le_mul_of_nonneg_right h (pow_nonneg (hside b).le d)

end Paper
