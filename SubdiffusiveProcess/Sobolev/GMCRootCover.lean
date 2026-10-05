module

public import SubdiffusiveProcess.Model.GMCModel
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-- A deterministic finite cover bounds every native potential field by translated unit
regularity observables. The cover is chosen before the field and the model. -/
theorem exists_gmc_root_lipschitz_cover {d : ℕ} (R : ℝ) :
  ∃ S : Finset (Homogenization.Vec d), S.Nonempty ∧
    ∀ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
      LipschitzOnWith
        (∑ z ∈ S, (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
           (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g),
          _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0))
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
        fderiv ℝ ((_root_.SubdiffusiveProcess.Model.PotentialField.translate z g :
          _root_.SubdiffusiveProcess.Model.PotentialField d) :
          Homogenization.Vec d → ℝ) (x - z) =
          fderiv ℝ (fun y => g y) x := by
      rw [show ((_root_.SubdiffusiveProcess.Model.PotentialField.translate z g :
        _root_.SubdiffusiveProcess.Model.PotentialField d) : Homogenization.Vec d → ℝ) =
        (fun y => g (y + z)) from
          funext (_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply z g)]
      simpa only [sub_add_cancel] using
        (fderiv_comp_add_right (𝕜 := ℝ) (f := (fun y => g y))
          z (x := x - z))
    have hlocal :
        ‖fderiv ℝ (fun y => g y) x‖₊ ≤
          (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
            (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g),
            _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0) := by
      apply NNReal.coe_le_coe.mp
      change ‖fderiv ℝ (fun y => g y) x‖ ≤
        _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)
      rw [← hderiv]
      rw [(_root_.SubdiffusiveProcess.Model.PotentialField.translate z g).hasFDerivAt
        (x - z) |>.fderiv]
      exact _root_.SubdiffusiveProcess.Model.PotentialField.norm_deriv_le_g2Observable
        (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) hcube
    exact hlocal.trans
      (Finset.single_le_sum
        (fun y _ => bot_le (a :=
          (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
            (_root_.SubdiffusiveProcess.Model.PotentialField.translate y g),
            _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0)))
        hzS)
  · exact convex_closedBall (0 : Homogenization.Vec d) R

end SubdiffusiveProcess
