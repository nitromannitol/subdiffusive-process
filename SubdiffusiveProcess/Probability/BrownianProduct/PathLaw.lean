module

public import SubdiffusiveProcess.Probability.BrownianProduct.Kernel
public import MarkovProcess.Examples.BrownianMotion

@[expose] public section

/-!
# Brownian motion with Laplacian normalization in finite dimensions

Take independent copies of the constructed real Brownian path kernel and run
each coordinate at twice the elapsed time. The resulting kernel is a genuine
probability law on continuous paths in `Fin d → ℝ`, including `d = 0`.
Its Gaussian variance is `2t`, matching the heat series for `Δ`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal Topology

noncomputable section
namespace SubdiffusiveProcess.Probability.BrownianProduct

/-- Assemble scalar paths into a vector path, with clock speed two. -/
def assemblePaths {d : ℕ} (ω : Fin d → ContinuousPath ℝ) : ContinuousPath (Fin d → ℝ) where
  toFun t i := ω i (2 * t)
  continuous_toFun := continuous_pi fun i =>
    (ω i).continuous.comp (continuous_const.mul continuous_id)

/-- Assembly is continuous for the compact-open topologies. -/
theorem continuous_assemblePaths (d : ℕ) :
    Continuous (@assemblePaths d) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_pi fun i =>
    ContinuousEval.continuous_eval.comp
      (((continuous_apply i).comp continuous_fst).prodMk (continuous_const.mul continuous_snd))

/-- Independent scalar Brownian trajectories, measurably parametrized by their starting vector. -/
def coordinateLaws (d : ℕ) : Kernel (Fin d → ℝ) (Fin d → ContinuousPath ℝ) :=
  piKernel fun i => brownianMotion.comap (fun x => x i) (measurable_pi_apply i)

instance isMarkovKernel_coordinateLaws (d : ℕ) : IsMarkovKernel (coordinateLaws d) := by
  unfold coordinateLaws
  infer_instance

/-- The scalar coordinate laws are a product measure. -/
theorem coordinateLaws_apply {d : ℕ} (x : Fin d → ℝ) :
    coordinateLaws d x = Measure.pi (fun i => brownianMotion (x i)) := rfl

/-- Finite-dimensional Brownian path kernel, with covariance `2t` times the identity. -/
def brownianPath (d : ℕ) : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)) :=
  (coordinateLaws d).map assemblePaths

/-- The vector path law is the pushforward of independent scalar paths. -/
theorem brownianPath_apply {d : ℕ} (x : Fin d → ℝ) :
    brownianPath d x = (Measure.pi (fun i => brownianMotion (x i))).map assemblePaths := by
  exact Kernel.map_apply _ (continuous_assemblePaths d).measurable x

instance isMarkovKernel_brownianPath (d : ℕ) : IsMarkovKernel (brownianPath d) := by
  exact Kernel.IsMarkovKernel.map _ (continuous_assemblePaths d).measurable

/-- Every vector marginal is the product Gaussian with mean `x` and variance `2t`. -/
theorem brownianPath_map_eval {d : ℕ} (t : ℝ≥0) (x : Fin d → ℝ) :
    (brownianPath d x).map (fun ω => ω t) =
      Measure.pi (fun i => gaussianReal (x i) (2 * t)) := by
  have hm : Measurable (fun ω : ContinuousPath (Fin d → ℝ) => ω t) :=
    ContinuousPath.measurable_coordinateProcess t
  rw [brownianPath_apply, Measure.map_map hm (continuous_assemblePaths d).measurable]
  change (Measure.pi (fun i => brownianMotion (x i))).map
    (fun ω i => ω i (2 * t)) = _
  calc
    _ = Measure.pi (fun i => (brownianMotion (x i)).map (fun ω => ω (2 * t))) :=
      Measure.pi_map_pi (fun _ =>
        (ContinuousPath.measurable_coordinateProcess (2 * t)).aemeasurable)
    _ = _ := by simp only [brownianMotion_map_eval]

/-- Each vector increment is a centered product Gaussian of variance twice the elapsed time. -/
theorem brownianPath_map_increment {d : ℕ} (x : Fin d → ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (brownianPath d x).map (fun ω => ω t - ω s) =
      Measure.pi (fun _ : Fin d => gaussianReal 0 (2 * (t - s))) := by
  have hm : Measurable (fun ω : ContinuousPath (Fin d → ℝ) => ω t - ω s) :=
    (ContinuousPath.measurable_coordinateProcess t).sub
      (ContinuousPath.measurable_coordinateProcess s)
  rw [brownianPath_apply, Measure.map_map hm (continuous_assemblePaths d).measurable]
  change (Measure.pi (fun i => brownianMotion (x i))).map
    (fun ω i => ω i (2 * t) - ω i (2 * s)) = _
  calc
    _ = Measure.pi (fun i => (brownianMotion (x i)).map
        (fun ω => ω (2 * t) - ω (2 * s))) :=
      Measure.pi_map_pi (fun _ =>
        ((ContinuousPath.measurable_coordinateProcess (2 * t)).sub
          (ContinuousPath.measurable_coordinateProcess (2 * s))).aemeasurable)
    _ = _ := by
      simp only [brownianMotion_map_increment _ _ _
        (mul_le_mul_of_nonneg_left hst (by norm_num : (0 : ℝ≥0) ≤ 2)), mul_tsub]

/-- The joint laws of all successive coordinate increments are product Gaussians.
The outer product ranges over spatial coordinates and the inner product over time intervals. -/
theorem brownianPath_map_coordinateIncrements {d n : ℕ} (x : Fin d → ℝ)
    (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) :
    (brownianPath d x).map (fun ω (i : Fin d) (j : Fin n) =>
      ω (t j.succ) i - ω (t j.castSucc) i) =
        Measure.pi (fun _ : Fin d => Measure.pi (fun j : Fin n =>
          gaussianReal 0 (2 * (t j.succ - t j.castSucc)))) := by
  have hm : Measurable (fun (ω : ContinuousPath (Fin d → ℝ)) (i : Fin d) (j : Fin n) =>
      ω (t j.succ) i - ω (t j.castSucc) i) :=
    Measurable.of_eval fun i => Measurable.of_eval fun j =>
      ((measurable_pi_apply i).comp (ContinuousPath.measurable_coordinateProcess _)).sub
        ((measurable_pi_apply i).comp (ContinuousPath.measurable_coordinateProcess _))
  rw [brownianPath_apply, Measure.map_map hm (continuous_assemblePaths d).measurable]
  change (Measure.pi (fun i => brownianMotion (x i))).map
    (fun ω i (j : Fin n) => ω i (2 * t j.succ) - ω i (2 * t j.castSucc)) = _
  have h2t : Monotone (fun j => 2 * t j) := fun _ _ h =>
    mul_le_mul_of_nonneg_left (ht h) (by norm_num)
  calc
    _ = Measure.pi (fun i => (brownianMotion (x i)).map
        (fun ω (j : Fin n) => ω (2 * t j.succ) - ω (2 * t j.castSucc))) :=
      Measure.pi_map_pi (fun _ =>
        (Measurable.of_eval fun _ =>
          (ContinuousPath.measurable_coordinateProcess _).sub
            (ContinuousPath.measurable_coordinateProcess _)).aemeasurable)
    _ = _ := by simp only [brownianMotion_map_increments h2t, mul_tsub]












end SubdiffusiveProcess.Probability.BrownianProduct
