import SubdiffusiveProcess.Section10.PrelimitExitClock
import SubdiffusiveProcess.Section10.PhysicalLocalTransportResolvent
import SubdiffusiveProcess.Section10.ExitMomentPassage
import SubdiffusiveProcess.Section10.ExitScaling
import MarkovProcess.Trajectory.Equivariance

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.Section10.PhysicalLocalTransport SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PrelimitExitPaths

/-- Translating a path does not change its centered cube exit. -/
theorem centered_exit_eq_of_increments {d : ℕ} (v w : DiffusionPath d) (r : ℝ)
    (h : ∀ t, v t - v 0 = w t - w 0) :
    ContinuousPath.exitTime (Metric.ball (v 0) r) v =
      ContinuousPath.exitTime (Metric.ball (w 0) r) w := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro t
  change ContinuousPath.exitTime (Metric.ball (v 0) r) v ≤ (t : ℝ≥0∞) ↔
    ContinuousPath.exitTime (Metric.ball (w 0) r) w ≤ (t : ℝ≥0∞)
  rw [ContinuousPath.exitTime_le_iff_mem_hitsSetBy _ Metric.isOpen_ball t v,
    ContinuousPath.exitTime_le_iff_mem_hitsSetBy _ Metric.isOpen_ball t w]
  simp only [ContinuousPath.hitsSetBy, Set.mem_setOf_eq, Set.mem_compl_iff,
    Metric.mem_ball, dist_eq_norm, h]

/-- Centered exits of the literal affine map use the raw clock, at every path,
including infinite exits. No starting-point assumption is needed here. -/
theorem centered_exit_affine {d : ℕ} (m : ℕ) (z : Vec d) (c : ℝ≥0)
    (hc : 0 < c) (r : ℝ) (w : DiffusionPath d) :
    ContinuousPath.exitTime
      (Metric.ball ((ContinuousPath.rescale (physicalCoordinates m z).symm c w) 0) r)
      (ContinuousPath.rescale (physicalCoordinates m z).symm c w) =
      (c : ℝ≥0∞)⁻¹ * ContinuousPath.exitTime (Metric.ball (w 0) (r * (3 : ℝ)^m)) w := by
  let a : ℝ := ((3 : ℝ)^m)⁻¹
  have ha : 0 < a := inv_pos.mpr (pow_pos (by norm_num) _)
  have he := centered_exit_eq_of_increments
    (ContinuousPath.rescale (physicalCoordinates m z).symm c w)
    (Paper.aux_lim_nonbrownian_scalePath a c w) r (by
      intro t
      simp only [ContinuousPath.rescale_apply, physicalCoordinates_symm_apply,
        Paper.aux_lim_nonbrownian_scalePath, ContinuousMap.coe_mk, mul_zero]
      module)
  have hz : Paper.aux_lim_nonbrownian_scalePath a c w 0 = 0 := by
    simp [Paper.aux_lim_nonbrownian_scalePath]
  rw [he, hz, Paper.aux_lim_nonbrownian_scalePath_exit a ha c hc]
  simp only [a, div_inv_eq_mul]

/-- Literal prelimit path law map; its start is the deterministic x_N. -/
def prelimitPath {d : ℕ} (M : GMCModel d) (N : ℕ) : DiffusionPath d → DiffusionPath d :=
  ContinuousPath.rescale (physicalCoordinates N (0 : Vec d)).symm (rawClock M N N)

/-- Exact centered exit conversion for L=N,m=N-k,z=3^N*x_N. -/
theorem smallExit_prelimit {d : ℕ} (M : GMCModel d) {N k : ℕ} (hk : k ≤ N)
    (x : Vec d) (w : DiffusionPath d) :
    EndpointPaths.smallExit k (prelimitPath M N w) =
      ((rawClock M N (N-k) / rawClock M N N : ℝ≥0) : ℝ≥0∞) *
        EndpointPaths.smallExit 0
          (ContinuousPath.rescale (physicalCoordinates (N-k) ((3 : ℝ)^N • x)).symm
            (rawClock M N (N-k)) w) := by
  have hrad : ((3 : ℝ)^(-(k : ℤ))/2) * (3 : ℝ)^N = (1/2) * (3 : ℝ)^(N-k) := by
    rw [zpow_neg, zpow_natCast, pow_sub₀ (3 : ℝ) (by norm_num) hk]
    ring
  simp only [EndpointPaths.smallExit, prelimitPath,
    centered_exit_affine _ _ _ (rawClock_pos M _ _), Nat.cast_zero, neg_zero, zpow_zero,
    one_div, hrad]
  simp only [ENNReal.coe_div (rawClock_pos M N N).ne', ENNReal.div_eq_inv_mul, mul_assoc]
  rw [← mul_assoc (rawClock M N (N-k) : ℝ≥0∞) (rawClock M N (N-k) : ℝ≥0∞)⁻¹]
  rw [ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr (rawClock_pos M N (N-k)).ne')
    ENNReal.coe_ne_top, one_mul]

end SubdiffusiveProcess.Section10.PrelimitExitPaths
