import SubdiffusiveProcess.Frozen.Assumptions.GMCModel
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-- A deterministic finite cover bounds every native potential field by translated unit
regularity observables. The cover is chosen before the field and the model. -/
theorem exists_gmc_root_lipschitz_cover {d : ℕ} (R : ℝ) :
  ∃ S : Finset (Homogenization.Vec d), S.Nonempty ∧
    ∀ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      LipschitzOnWith
        (∑ z ∈ S, (⟨SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
           (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g),
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0))
        (fun x => g x) (Metric.closedBall (0 : Homogenization.Vec d) R) := by
  classical
  obtain ⟨S₀, hS₀⟩ := (isCompact_closedBall (0 : Homogenization.Vec d) R).elim_finite_subcover
    (fun z : Homogenization.Vec d => Metric.ball z (1 / 2 : ℝ))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.2 ⟨x, Metric.mem_ball_self (by norm_num)⟩)
  let S : Finset (Homogenization.Vec d) := insert 0 S₀
  have hSne : S.Nonempty := by
    exact ⟨0, Finset.mem_insert_self 0 S₀⟩
  have hS : Metric.closedBall (0 : Homogenization.Vec d) R ⊆
      ⋃ z ∈ S, Metric.ball z (1 / 2 : ℝ) := by
    intro x hx
    obtain ⟨z, hzS₀, hzx⟩ : ∃ z, ∃ (_ : z ∈ S₀),
        x ∈ Metric.ball z (1 / 2 : ℝ) := by
      simpa only [mem_iUnion] using hS₀ hx
    exact mem_iUnion.2 ⟨z, mem_iUnion.2 ⟨Finset.mem_insert_of_mem hzS₀, hzx⟩⟩
  refine ⟨S, hSne, ?_⟩
  intro g
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x hx
    exact (g.hasFDerivAt x).differentiableAt
  · intro x hx
    obtain ⟨z, hzS, hzx⟩ : ∃ z, ∃ (_ : z ∈ S),
        x ∈ Metric.ball z (1 / 2 : ℝ) := by
      simpa only [mem_iUnion] using hS hx
    have hxm : x - z ∈ Metric.ball (0 : Homogenization.Vec d) (1 / 2 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzx
    have hcube : x - z ∈ Homogenization.openCubeSet
        (Homogenization.originCube d 0) := by
      rw [← Homogenization.ball_cubeCenter_eq_openCubeSet]
      have hcenter : Homogenization.cubeCenter
          (Homogenization.originCube d 0) = (0 : Homogenization.Vec d) := by
        ext i
        simp [Homogenization.cubeCenter, Homogenization.originCube]
      have hradius : Homogenization.cubeRadius
          (Homogenization.originCube d 0) = (1 / 2 : ℝ) := by
        unfold Homogenization.cubeRadius
        rw [Homogenization.cubeScaleFactor_eq_one_of_scale_eq_zero]
        · norm_num
        · rfl
      rw [hcenter, hradius]
      exact hxm
    have hderiv :
        fderiv ℝ ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g :
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
          Homogenization.Vec d → ℝ) (x - z) =
          fderiv ℝ (fun y => g y) x := by
      simpa [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply, sub_add_cancel] using
        (fderiv_comp_add_right (𝕜 := ℝ) (f := (fun y => g y))
          z (x := x - z))
    have hlocal :
        ‖fderiv ℝ (fun y => g y) x‖₊ ≤
          (⟨SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g),
            SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0) := by
      rw [← hderiv]
      rw [(SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g).hasFDerivAt
        (x - z) |>.fderiv]
      rw [← NNReal.coe_le_coe]
      exact SubdiffusiveProcess.Frozen.Assumptions.PotentialField.norm_deriv_le_g2Observable
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g) hcube
    exact hlocal.trans
      (Finset.single_le_sum
        (fun y _ => zero_le
          (⟨SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate y g),
            SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0))
        hzS)
  · exact convex_closedBall (0 : Homogenization.Vec d) R

end SubdiffusiveProcess
