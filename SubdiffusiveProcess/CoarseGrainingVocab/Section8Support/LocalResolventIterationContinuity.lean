module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationKernelIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
@[expose] public section

/-!
# Right continuity of killed-kernel pairings

Before exit a bounded continuous test follows the live path continuously. From exit onward it is
zero, so the killed test is right-continuous. Dominated convergence first through each path law and
then through a finite measure gives right continuity of the killed-kernel scalar pairing.
-/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossing
open scoped ENNReal NNReal Topology BoundedContinuousFunction
set_option autoImplicit false
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
/-- The live-position projection is continuous strictly before the lifetime. -/
theorem continuousAt_position_of_lt_lifetime {d : ℕ} (w : Path d) (t : NNReal) (ht : (t : ENNReal) < w.lifetime) : ContinuousAt (fun s => position s w) t := by
  have hp : Continuous (fun z : Cemetery (Vec d) => z.elim id (fun _ => 0)) :=
    continuous_sumElim.mpr ⟨continuous_id, continuous_const⟩
  exact hp.continuousAt.comp (coordinate_continuous_at w t ht)

/-- A survival threshold which has already been reached remains reached at later times. -/
theorem not_ofReal_lt_of_le (a r : ℝ) (τ : ENNReal) (ha : ¬ ENNReal.ofReal a < τ) (har : a ≤ r) : ¬ ENNReal.ofReal r < τ := by
  intro h
  exact ha (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal har) h)

/-- A conditional function is continuous before an open threshold. -/
theorem continuousAt_ite_of_lt_threshold (v : ℝ → ℝ) (a : ℝ) (τ : ENNReal) (hv : ContinuousAt v a) (ha : ENNReal.ofReal a < τ) : ContinuousAt (fun r => if ENNReal.ofReal r < τ then v r else 0) a := by
  apply hv.congr
  filter_upwards [(isOpen_lt ENNReal.continuous_ofReal continuous_const).mem_nhds ha] with r hr
  exact (if_pos hr).symm

/-- After reaching the threshold the conditional function is constantly zero to the right. -/
theorem continuousWithinAt_ite_of_le_threshold (v : ℝ → ℝ) (a : ℝ) (τ : ENNReal) (ha : ¬ ENNReal.ofReal a < τ) : ContinuousWithinAt (fun r => if ENNReal.ofReal r < τ then v r else 0) (Ici a) a := by
  apply (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ => (0:ℝ)) (Ici a) a).congr_of_mem
    (fun r hr => ?_) (by simp : a ∈ Ici a)
  exact if_neg (not_lt.mpr ((not_lt.mp ha).trans (ENNReal.ofReal_le_ofReal hr)))

/-- The nonnegative-real and extended-nonnegative-real truncations of real time agree. -/
theorem coe_real_toNNReal_eq_ofReal (t : ℝ) : ((Real.toNNReal t : NNReal) : ENNReal) = ENNReal.ofReal t := by
  rfl

/-- The killed path test at a fixed time is measurable. -/
theorem measurable_killedPathTest_function {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) (g : Vec d → ℝ) (hg : Measurable g) (t : ℝ) : Measurable (fun w : Path d => if ENNReal.ofReal t < LifetimePath.exitTime U w then g (position (Real.toNNReal t) w) else 0) := by
  have htime : Measurable (fun w : Path d => (LifetimePath.exitTime U w : ENNReal)) := by
    simpa using! (LifetimePath.isStoppingTime_exitTime U hU).measurable'
  exact Measurable.ite
    (measurableSet_lt measurable_const htime)
    (hg.comp (position_fixed_measurable (Real.toNNReal t))) measurable_const

/-- The bounded continuous norm controls every killed path test. -/
theorem norm_killedPathTest_function_le {d : ℕ} (U : Set (Vec d)) (g : Vec d →ᵇ ℝ) (t : ℝ) (w : Path d) : ‖if ENNReal.ofReal t < LifetimePath.exitTime U w then g (position (Real.toNNReal t) w) else 0‖ ≤ ‖g‖ := by
  by_cases h : ENNReal.ofReal t < LifetimePath.exitTime U w
  · rw [if_pos h]
    exact g.norm_coe_le_norm _
  · rw [if_neg h, norm_zero]
    exact norm_nonneg _

/-- Dominated convergence preserves right continuity under a finite measure. -/
theorem continuousWithinAt_integral_of_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (F : ℝ → α → ℝ) (hF : ∀ t, Measurable (F t)) (C : ℝ) (hb : ∀ t x, ‖F t x‖ ≤ C) (a : ℝ) (hc : ∀ x, ContinuousWithinAt (fun t => F t x) (Ici a) a) : ContinuousWithinAt (fun t => ∫ x, F t x ∂μ) (Ici a) a := by
  exact tendsto_integral_filter_of_dominated_convergence (fun _ : α => C)
    (Eventually.of_forall fun t => (hF t).aestronglyMeasurable)
    (Eventually.of_forall fun t => Eventually.of_forall (hb t))
    (integrable_const C) (Eventually.of_forall hc)

/-- Integration against a probability measure preserves a pointwise norm bound. -/
theorem norm_integral_le_of_probability_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) : ‖∫ x, f x ∂μ‖ ≤ C := by
  simpa using (norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hb))

/-- Integrating a measurable real function against a kernel is measurable in the starting point. -/
theorem measurable_kernelIntegral_function {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (κ : Kernel α β) (g : β → ℝ) (hg : Measurable g) : Measurable (fun x => ∫ y, g y ∂κ x) := by
  exact hg.stronglyMeasurable.integral_kernel.measurable

/-- Test a path at the given real time while it survives inside the set, and return zero after
exit. -/
def killedPathTest {d : ℕ} (U : Set (Vec d)) (g : Vec d → ℝ) (t : ℝ) (w : Path d) : ℝ :=
  if ENNReal.ofReal t < LifetimePath.exitTime U w then
    g (position (Real.toNNReal t) w) else 0

/-- The killed path test is right-continuous at every real time. -/
theorem continuousWithinAt_killedPathTest {d : ℕ} (U : Set (Vec d))
    (w : Path d) (g : Vec d → ℝ) (hg : Continuous g) (t : ℝ) :
    ContinuousWithinAt (fun r => killedPathTest U g r w) (Ici t) t := by
  by_cases ht : ENNReal.ofReal t < LifetimePath.exitTime U w
  · have hl : ((Real.toNNReal t : NNReal) : ENNReal) < w.lifetime := by
      rw [coe_real_toNNReal_eq_ofReal]
      exact ht.trans_le (LifetimePath.exitTime_le_lifetime U w)
    have hp : ContinuousAt (fun r => position (Real.toNNReal r) w) t :=
      (continuousAt_position_of_lt_lifetime w (Real.toNNReal t) hl).comp continuous_real_toNNReal.continuousAt
    exact (continuousAt_ite_of_lt_threshold _ t _ (hg.continuousAt.comp hp) ht).continuousWithinAt
  · exact continuousWithinAt_ite_of_le_threshold _ t _ ht

/-- The killed-kernel integral is the integral of the killed path test. -/
theorem killedKernel_integral_eq_pathTest {d : ℕ} (law : Kernel (Vec d) (Path d))
    (U : Set (Vec d)) (hU : IsOpen U) (g : Vec d → ℝ) (hg : Measurable g)
    (t : ℝ) (x : Vec d) :
    kernelIntegral (killedKernel law U hU (Real.toNNReal t)) g x =
      ∫ w, killedPathTest U g t w ∂law x := by
  rw [killedKernel_integral law U hU (Real.toNNReal t) g hg x]
  have htime : Measurable (fun w : Path d => (LifetimePath.exitTime U w : ENNReal)) := by
    simpa using! (LifetimePath.isStoppingTime_exitTime U hU).measurable'
  have hS : MeasurableSet {w : Path d | ((Real.toNNReal t : NNReal) : ENNReal) <
      LifetimePath.exitTime U w} :=
    measurableSet_lt measurable_const htime
  rw [← integral_indicator hS]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    simp only [Set.indicator, Set.mem_setOf_eq, coe_real_toNNReal_eq_ofReal, killedPathTest]

/-- The killed-kernel integral is bounded by the norm of its bounded continuous test. -/
theorem norm_killedKernel_integral_le {d : ℕ} (law : Kernel (Vec d) (Path d))
    [IsMarkovKernel law] (U : Set (Vec d)) (hU : IsOpen U) (g : Vec d →ᵇ ℝ)
    (t : ℝ) (x : Vec d) :
    ‖kernelIntegral (killedKernel law U hU (Real.toNNReal t)) g x‖ ≤ ‖g‖ := by
  rw [killedKernel_integral_eq_pathTest law U hU g g.continuous.measurable t x]
  exact norm_integral_le_of_probability_bound (law x) _ ‖g‖ (fun w => norm_killedPathTest_function_le U g t w)

/-- Every killed-kernel row tested against a bounded continuous function is right-continuous in
time. -/
theorem continuousWithinAt_killedKernel_integral {d : ℕ}
    (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) (g : Vec d →ᵇ ℝ) (x : Vec d) (t : ℝ) :
    ContinuousWithinAt
      (fun r => kernelIntegral (killedKernel law U hU (Real.toNNReal r)) g x) (Ici t) t := by
  have hc := continuousWithinAt_integral_of_bound (law x) (fun r w => killedPathTest U g r w)
    (fun r => measurable_killedPathTest_function U hU g g.continuous.measurable r)
    ‖g‖ (fun r w => norm_killedPathTest_function_le U g r w) t
    (fun w => continuousWithinAt_killedPathTest U w g g.continuous t)
  exact hc.congr
    (fun r _ => killedKernel_integral_eq_pathTest law U hU g g.continuous.measurable r x)
    (killedKernel_integral_eq_pathTest law U hU g g.continuous.measurable t x)

/-- Pairing a killed-kernel row with bounded continuous data under a finite measure is right-
continuous in time. -/
theorem continuousWithinAt_killedKernel_pairing {d : ℕ}
    (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    (f g : Vec d →ᵇ ℝ) (t : ℝ) :
    ContinuousWithinAt
      (fun r => ∫ x, f x * kernelIntegral (killedKernel law U hU (Real.toNNReal r)) g x ∂μ)
      (Ici t) t := by
  let F : ℝ → Vec d → ℝ := fun r x =>
    f x * kernelIntegral (killedKernel law U hU (Real.toNNReal r)) g x
  have hFm : ∀ r, Measurable (F r) := fun r => f.continuous.measurable.mul
    (measurable_kernelIntegral_function (killedKernel law U hU (Real.toNNReal r)) g g.continuous.measurable)
  have hFb : ∀ r x, ‖F r x‖ ≤ ‖f‖ * ‖g‖ := by
    intro r x
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul (f.norm_coe_le_norm x) (norm_killedKernel_integral_le law U hU g r x)
      (norm_nonneg _) (norm_nonneg _)
  exact continuousWithinAt_integral_of_bound μ F hFm (‖f‖ * ‖g‖) hFb t (fun x =>
    continuousWithinAt_const.mul (continuousWithinAt_killedKernel_integral law U hU g x t))

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
