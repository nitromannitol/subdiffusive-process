module

public import SubdiffusiveProcess.Section10.ExitCarrier
public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry

@[expose] public section

/-! Deterministic endpoint helpers for `lim:cor-paths`. No physical exit estimate
or source root is assumed. The supremum norm defines the cube; displacement
uses the Euclidean norm. -/
open Filter MeasureTheory Topology Set MarkovProcess SubdiffusiveProcess
open Homogenization
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.EndpointPaths

/-- Exit from the centred cube of side length `3^(-k)`. -/
def smallExit {d : ℕ} (k : ℕ) (w : DiffusionPath d) : ℝ≥0∞ :=
  ContinuousPath.exitTime (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w

/-- Literal Euclidean maximum over the compact initial time interval. -/
def maximum {d : ℕ} (t : ℝ≥0) (w : DiffusionPath d) : ℝ :=
  ⨆ s : Set.Icc (0 : ℝ≥0) t, euclideanNorm (w s - w 0)

lemma displacement_continuous {d : ℕ} (w : DiffusionPath d) :
    Continuous (fun s : ℝ≥0 => euclideanNorm (w s - w 0)) := by
  simp only [euclideanNorm, vecNormSq, vecDot]
  fun_prop

lemma maximum_bddAbove {d : ℕ} (w : DiffusionPath d) (t : ℝ≥0) :
    BddAbove (Set.range (fun s : Set.Icc (0 : ℝ≥0) t =>
      euclideanNorm (w s - w 0))) := by
  exact (isCompact_range ((displacement_continuous w).comp
    (continuous_subtype_val : Continuous (Subtype.val : Set.Icc (0 : ℝ≥0) t → ℝ≥0)))).bddAbove

lemma displacement_le_maximum {d : ℕ} (w : DiffusionPath d) (t s : ℝ≥0)
    (hs : s ≤ t) : euclideanNorm (w s - w 0) ≤ maximum t w := by
  exact le_ciSup (maximum_bddAbove w t) ⟨s, zero_le, hs⟩

lemma maximum_nonneg {d : ℕ} (w : DiffusionPath d) (t : ℝ≥0) :
    0 ≤ maximum t w :=
  (euclideanNorm_nonneg _).trans (displacement_le_maximum w t 0 zero_le)

lemma maximum_mono {d : ℕ} (w : DiffusionPath d) : Monotone (fun t => maximum t w) := by
  intro t u htu
  letI : Nonempty (Set.Icc (0 : ℝ≥0) t) := ⟨⟨0, le_rfl, zero_le⟩⟩
  apply ciSup_le
  intro s
  exact displacement_le_maximum w u s (s.property.2.trans htu)

lemma radius_le_maximum_of_smallExit_le {d : ℕ} (w : DiffusionPath d)
    (k : ℕ) (t : ℝ≥0) (h : smallExit k w ≤ (t : ℝ≥0∞)) :
    (3 : ℝ) ^ (-(k : ℤ)) / 2 ≤ maximum t w := by
  obtain ⟨s, hs⟩ := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy _
    Metric.isOpen_ball t w).mp h
  have hnorm : (3 : ℝ) ^ (-(k : ℤ)) / 2 ≤ ‖w s - w 0‖ := by
    simpa only [ContinuousPath.hitsSetBy, Set.mem_setOf_eq, Set.mem_compl_iff,
      Metric.mem_ball, dist_eq_norm, not_lt] using hs
  exact hnorm.trans ((norm_le_euclideanNorm _).trans
    (displacement_le_maximum w t s s.property))

/-- The exact polynomial/geometric endpoint in the paper. -/
def endpoint (eta epsilon : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) ^ (1 + epsilon) * (3 : ℝ) ^ (-((2 + eta) * k))

lemma endpoint_pos (eta epsilon : ℝ) {k : ℕ} (hk : 0 < k) :
    0 < endpoint eta epsilon k := by
  exact mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast hk) _)
    (Real.rpow_pos_of_pos (by norm_num) _)

lemma endpoint_exp (eta epsilon : ℝ) (k : ℕ) :
    endpoint eta epsilon k = (k : ℝ) ^ (1 + epsilon) *
      Real.exp (-((2 + eta) * Real.log 3) * k) := by
  rw [endpoint, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  congr 2
  ring

lemma endpoint_tendsto_zero (eta epsilon : ℝ) (heta : 0 < eta) :
    Tendsto (endpoint eta epsilon) atTop (𝓝 0) := by
  simpa only [Function.comp_def, ← endpoint_exp] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 + epsilon)
      ((2 + eta) * Real.log 3) (mul_pos (by linarith) (Real.log_pos (by norm_num)))).comp
      tendsto_natCast_atTop_atTop

lemma endpoint_eventually_le_exp (eta epsilon : ℝ) (heta : 0 < eta) :
    ∀ᶠ k : ℕ in atTop, endpoint eta epsilon k ≤
      Real.exp (-((2 + eta) * Real.log 3 / 2) * k) := by
  have hc : 0 < (2 + eta) * Real.log 3 / 2 :=
    div_pos (mul_pos (by linarith) (Real.log_pos (by norm_num))) (by norm_num)
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 + epsilon)
    ((2 + eta) * Real.log 3 / 2) hc).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h] with k hk
  rw [endpoint_exp]
  have heq : -((2 + eta) * Real.log 3) * (k : ℝ) =
      -((2 + eta) * Real.log 3 / 2) * k +
      -((2 + eta) * Real.log 3 / 2) * k := by ring
  rw [heq, Real.exp_add, ← mul_assoc]
  exact mul_le_of_le_one_left (Real.exp_pos _).le hk.le

end SubdiffusiveProcess.Section10.EndpointPaths
