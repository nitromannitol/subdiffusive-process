import SubdiffusiveProcess.Paper.in_deterministic
import SubdiffusiveProcess.Analysis.PotentialSumLipschitz

/-! A cutoff potential has the Lipschitz bound supplied by its rescaled shell gradients.
The infrared field is either its actual limit or identically zero; neither case is assumed to have the other characterization. -/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators Topology
noncomputable section
namespace Paper

/-- The zero-infrared cutoff uses a finite shell sum and needs no infrared convergence. -/
theorem aux_lfgc_potential_lipschitz_zero {d : ℕ}
    (omega : BilateralField d) (N : ℕ) (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (G : ℝ) (x y : SpatialCoordinates d)
    (hgrad : ∀ Z ∈ segment ℝ (((3 : ℝ) ^ N) • x) (((3 : ℝ) ^ N) • y), ∀ J : ℕ,
      ∑ i ∈ Finset.range J, Homogenization.euclideanNorm (shellGradient (eta i) Z) ≤ G) :
    |cutoffPotential 0 omega N y - cutoffPotential 0 omega N x| ≤
      (d : ℝ) * G * ((3 : ℝ) ^ N * ‖y - x‖) := by
  have hunscale (v : SpatialCoordinates d) :
      ((3 : ℝ) ^ (-(N : ℤ))) • (((3 : ℝ) ^ N) • v) = v := by
    rw [smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity), one_smul]
  have hlay : ∑ i ∈ Finset.range (N + 1),
      (eta i (((3 : ℝ) ^ N) • y) - eta i (((3 : ℝ) ^ N) • x)) =
        ∑ j ∈ Finset.range (N + 1), (omega (-(j : ℤ)) y - omega (-(j : ℤ)) x) := by
    have h := aux_in_deterministic_good_scale_transfer_uv_ir_sum
      (fun i : ℤ => omega i y - omega i x) N 0
    simp only [add_zero, Finset.range_zero, Finset.sum_empty] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    rw [hEta, hEta, hunscale, hunscale]
  have h := potentialSample_sum_increment_le eta (N + 1)
    (((3 : ℝ) ^ N) • x) (((3 : ℝ) ^ N) • y) G (fun Z hZ => hgrad Z hZ (N + 1))
  rw [hlay, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (3 : ℝ) ^ N)] at h
  simpa only [cutoffPotential, Pi.zero_apply, ContinuousMap.zero_apply, zero_add,
    Finset.sum_sub_distrib, Int.ofNat_eq_natCast, mul_assoc] using h

/-- Both permitted infrared variants obey the same local Lipschitz estimate. -/
theorem lfgc_potential_lipschitz {d : ℕ}
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∨ H = 0)
    (G : ℝ) (x y : SpatialCoordinates d)
    (hgrad : ∀ Z ∈ segment ℝ (((3 : ℝ) ^ N) • x) (((3 : ℝ) ^ N) • y), ∀ J : ℕ,
      ∑ i ∈ Finset.range J, Homogenization.euclideanNorm (shellGradient (eta i) Z) ≤ G) :
    |cutoffPotential H omega N y - cutoffPotential H omega N x| ≤
      (d : ℝ) * G * ((3 : ℝ) ^ N * ‖y - x‖) := by
  rcases hIR with hIR | rfl
  · exact aux_in_deterministic_onestep_potential_lip H omega N eta hEta hIR G x y hgrad
  · exact aux_lfgc_potential_lipschitz_zero omega N eta hEta G x y hgrad

end Paper
