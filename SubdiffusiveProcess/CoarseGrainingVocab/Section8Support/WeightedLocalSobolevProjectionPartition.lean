import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevProjectionStep
set_option autoImplicit false
open Homogenization MeasureTheory
open scoped ENNReal BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support

theorem weightedProjection_indicator_at {d : ℕ} (Q : TriadicCube d) (j : ℕ) (a : TriadicCube d → ℝ≥0∞) {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q j) {x : Vec d} (hx : x ∈ cubeSet R) : (∑ S ∈ descendantsAtDepth Q j, if x ∈ cubeSet S then a S else 0) = a R := by
  rw [Finset.sum_eq_single_of_mem R hR]
  · simp [hx]
  · intro S hS hSR
    have hdis := pairwiseDisjoint_descendantsAtDepth Q j hR hS (fun h => hSR h.symm)
    have hxS : x ∉ cubeSet S := fun h => hdis.le_bot ⟨hx, h⟩
    simp [hxS]

theorem weightedProjection_indicator_outside {d : ℕ} (Q : TriadicCube d) (j : ℕ) (a : TriadicCube d → ℝ≥0∞) {x : Vec d} (hx : x ∉ cubeSet Q) : (∑ R ∈ descendantsAtDepth Q j, if x ∈ cubeSet R then a R else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro R hR
  have hxR : x ∉ cubeSet R := fun h =>
    hx (cubeSet_subset_of_mem_descendantsAtDepth hR h)
  simp [hxR]

theorem weightedProjection_step_integrand_easy {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : TriadicCube d → ℝ) (p : ℝ) (hp : 0 < p) (x : Vec d) : ‖weightedProjectionStep Q j c x‖ₑ ^ p = ∑ R ∈ descendantsAtDepth Q j, if x ∈ cubeSet R then ‖c R‖ₑ ^ p else 0 := by
  by_cases hx : x ∈ cubeSet Q
  · obtain ⟨R, hR, hxR⟩ :=
      exists_mem_descendantsAtDepth_of_mem_cubeSet (Q := Q) (n := j) hx
    rw [weightedProjection_step_at Q j c hR hxR]
    rw [weightedProjection_indicator_at Q j (fun R => ‖c R‖ₑ ^ p) hR hxR]
  · rw [weightedProjection_step_outside Q j c hx]
    rw [weightedProjection_indicator_outside Q j (fun R => ‖c R‖ₑ ^ p) hx]
    simp [ENNReal.zero_rpow_of_pos hp]

theorem weightedProjection_step_eLpNorm {d : ℕ} (ν : Measure (Vec d)) (Q : TriadicCube d) (j : ℕ) (c : TriadicCube d → ℝ) (p : ℝ) (hp : 0 < p) : eLpNorm (weightedProjectionStep Q j c) (ENNReal.ofReal p) ν = (∑ R ∈ descendantsAtDepth Q j, ‖c R‖ₑ ^ p * ν (cubeSet R)) ^ (1 / p) := by
  refine weightedProjection_step_lp_formula ν Q j c p hp ?_
  refine weightedProjection_step_lintegral ν Q j c p hp ?_
  intro x
  simpa only [Set.indicator] using weightedProjection_step_integrand_easy Q j c p hp x

theorem weightedProjection_step_norm_le {d : ℕ} (ν μ : Measure (Vec d)) (Q : TriadicCube d) (j : ℕ) (c : TriadicCube d → ℝ) (p : ℝ) (hp : 2 ≤ p) (N W : ℝ≥0∞) (hN0 : N ≠ 0) (hNt : N ≠ ∞) (hμ : ∀ R ∈ descendantsAtDepth Q j, μ (cubeSet R) = N⁻¹) (hν : ∀ R ∈ descendantsAtDepth Q j, ν (cubeSet R) ≤ W / N) : eLpNorm (weightedProjectionStep Q j c) (ENNReal.ofReal p) ν ≤ ((W / N) ^ (1 / p) * N ^ (1 / 2 : ℝ)) * eLpNorm (weightedProjectionStep Q j c) 2 μ := by
  have hp0 : 0 < p := by linarith
  let D := descendantsAtDepth Q j
  let S : ℝ≥0∞ := ∑ R ∈ D, ‖c R‖ₑ ^ (2 : ℝ)
  have hμnorm : eLpNorm (weightedProjectionStep Q j c) 2 μ = (S / N) ^ (1 / 2 : ℝ) := by
    have h := weightedProjection_step_eLpNorm μ Q j c (2 : ℝ) (by norm_num)
    norm_num only [ENNReal.ofReal_ofNat] at h
    rw [h]
    congr 1
    calc
      (∑ R ∈ descendantsAtDepth Q j, ‖c R‖ₑ ^ (2 : ℝ) * μ (cubeSet R)) =
          ∑ R ∈ D, ‖c R‖ₑ ^ (2 : ℝ) * N⁻¹ := by
            apply Finset.sum_congr rfl
            intro R hR
            rw [hμ R hR]
      _ = S / N := weightedProjection_normalized_sum D (fun R => ‖c R‖ₑ ^ (2 : ℝ)) N
  have hroot : (∑ R ∈ D, ‖c R‖ₑ ^ p) ^ (1 / p) ≤ S ^ (1 / 2 : ℝ) :=
    weightedProjection_root_l2 D (fun R => ‖c R‖ₑ) p hp
      (weightedProjection_sum_rpow D (fun R => ‖c R‖ₑ ^ (2 : ℝ)) (p / 2) (by linarith))
  rw [weightedProjection_step_eLpNorm ν Q j c p hp0]
  calc
    (∑ R ∈ descendantsAtDepth Q j, ‖c R‖ₑ ^ p * ν (cubeSet R)) ^ (1 / p) ≤
        (W / N) ^ (1 / p) * (∑ R ∈ D, ‖c R‖ₑ ^ p) ^ (1 / p) :=
      weightedProjection_weighted_root D (fun R => ‖c R‖ₑ ^ p)
        (fun R => ν (cubeSet R)) (W / N) p hp0 hν
    _ ≤ (W / N) ^ (1 / p) * S ^ (1 / 2 : ℝ) := mul_le_mul_right hroot _
    _ = ((W / N) ^ (1 / p) * N ^ (1 / 2 : ℝ)) *
        eLpNorm (weightedProjectionStep Q j c) 2 μ := by
      rw [weightedProjection_sum_square_normalize N S hN0 hNt, hμnorm]
      ac_rfl

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
