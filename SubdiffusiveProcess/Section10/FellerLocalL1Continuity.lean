import SubdiffusiveProcess.Section10.BoundedC0Approximation
import SubdiffusiveProcess.Section10.TorsionExitBassInterfaces
import MarkovProcess.Feller.FiniteTimeKernelContinuity
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! Local L¹ approximation of the original transition kernels promotes
their C₀ Feller property to continuity on bounded measurable observables.
The approximation is uniform over compact starting sets and retains every
starting point. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open scoped ENNReal NNReal ZeroAtInfty

namespace SubdiffusiveProcess.Section10

/-- Bounded measurable functions are integrable for every finite measure. -/
theorem integrable_of_measurable_abs_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) {F : ℝ} (hbound : ∀ x, |f x| ≤ F) : Integrable f μ :=
  (integrable_const F).mono' hf.aestronglyMeasurable
    (Eventually.of_forall hbound)

/-- Sub-Markov integration preserves a pointwise absolute bound. -/
theorem abs_kernelIntegral_le_bound {d : ℕ}
    (κ : Kernel (Vec d) (Vec d)) (hκ : IsSubMarkovKernel κ)
    {f : Vec d → ℝ} {F : ℝ} (hF : 0 ≤ F)
    (hbound : ∀ y, |f y| ≤ F) (x : Vec d) :
    |kernelIntegral κ f x| ≤ F := by
  letI : IsFiniteKernel κ := hκ.isFiniteKernel
  rw [← Real.norm_eq_abs]
  calc
    ‖kernelIntegral κ f x‖ ≤ ∫ _y, F ∂κ x :=
      norm_integral_le_of_norm_le (integrable_const F) (Eventually.of_forall hbound)
    _ ≤ F := by
      rw [integral_const, smul_eq_mul]
      apply mul_le_of_le_one_left hF
      rw [measureReal_def, ← ENNReal.toReal_one]
      exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
        (hκ.measure_le_one x univ)

/-- At positive time, bounded measurable kernel integrals admit continuous
approximations uniformly over each compact starting set. -/
theorem exists_continuous_kernelIntegral_approx {d : ℕ}
    (P : SubMarkovKernelSemigroup (Vec d)) (hFeller : P.IsFellerKernelSemigroup)
    (μ : Measure (Vec d)) (happrox : LocalL1ApproximationBound P μ)
    (S : Set (Vec d)) (hS : IsCompact S)
    (t : NNReal) (ht : 0 < t) {f : Vec d → ℝ} (hf : Measurable f)
    {F : ℝ} (hF : 0 ≤ F) (hbound : ∀ x, |f x| ≤ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : Vec d → ℝ, Continuous u ∧
      ∀ x ∈ S, |kernelIntegral (P t) f x - u x| ≤ ε := by
  have hF1 : 0 < F + 1 := by linarith
  obtain ⟨s, hs, hst, W, _hW, _hWb, hWfin, A, hA, hlocal⟩ :=
    happrox S hS (ε / (4 * (F + 1))) t (by positivity) (by exact_mod_cast ht)
  have hst' : s ≤ t := le_of_lt (by exact_mod_cast hst)
  let r : NNReal := t - s
  let g : Vec d → ℝ := kernelIntegral (P r) f
  have hg : Measurable g := hf.stronglyMeasurable.integral_kernel.measurable
  have hgbound : ∀ x, |g x| ≤ F :=
    abs_kernelIntegral_le_bound (P r) (P.isSubMarkovKernel r) hF hbound
  letI : IsFiniteMeasure (μ.restrict W) := isFiniteMeasure_restrict.mpr hWfin
  obtain ⟨k, hkbound, hkerr⟩ :=
    exists_bounded_c0_integral_sub_le (μ.restrict W) hg hF hgbound
      (ε := ε / (2 * (A + 1))) (by positivity)
  let u : Vec d → ℝ := kernelIntegral (P s) k
  refine ⟨u, (hFeller.mapsC0 s k).1, ?_⟩
  intro x hx
  letI : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  letI : IsFiniteKernel (P s) := (P.isSubMarkovKernel s).isFiniteKernel
  letI : IsFiniteKernel (P r) := (P.isSubMarkovKernel r).isFiniteKernel
  have hsplit : kernelIntegral (P t) f x = ∫ y, g y ∂P s x := by
    have htr : t = s + r := (add_tsub_cancel_of_le hst').symm
    rw [htr, P.add]
    exact Kernel.integral_comp
      (integrable_of_measurable_abs_le _ hf hbound)
  have hdiffbound : ∀ y, |g y - k y| ≤ 2 * F := fun y =>
    (abs_sub (g y) (k y)).trans (by linarith [hgbound y, hkbound y])
  have hdiff : Measurable (fun y => g y - k y) := hg.sub k.continuous.measurable
  have hest := hlocal (fun y => g y - k y) hdiff (2 * F) (by positivity)
    hdiffbound x hx
  have hA1 : 0 < A + 1 := by linarith
  have hAterm : A * (ε / (2 * (A + 1))) ≤ ε / 2 := by
    calc
      _ ≤ (A + 1) * (ε / (2 * (A + 1))) := by gcongr; linarith
      _ = ε / 2 := by field_simp [ne_of_gt hA1]
  have hFterm : ε / (4 * (F + 1)) * (2 * F) ≤ ε / 2 := by
    calc
      _ ≤ ε / (4 * (F + 1)) * (2 * (F + 1)) := by gcongr; linarith
      _ = ε / 2 := by field_simp [ne_of_gt hF1]; ring
  calc
    |kernelIntegral (P t) f x - u x| = |∫ y, (g y - k y) ∂P s x| := by
      rw [hsplit]
      congr 1
      exact (integral_sub (integrable_of_measurable_abs_le _ hg hgbound)
        (integrable_of_measurable_abs_le _ k.continuous.measurable hkbound)).symm
    _ ≤ ∫ y, |g y - k y| ∂P s x := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => g y - k y)
    _ ≤ A * (∫ y in W, |g y - k y| ∂μ) + ε / (4 * (F + 1)) * (2 * F) := hest
    _ ≤ ε / 2 + ε / 2 :=
      add_le_add ((mul_le_mul_of_nonneg_left hkerr hA).trans hAterm) hFterm
    _ = ε := add_halves ε

/-- The local L¹ certificate promotes Feller continuity to bounded
measurable tests at every positive time and every starting point. -/
theorem continuous_kernelIntegral_of_localL1 {d : ℕ}
    (P : SubMarkovKernelSemigroup (Vec d)) (hFeller : P.IsFellerKernelSemigroup)
    (μ : Measure (Vec d)) (happrox : LocalL1ApproximationBound P μ)
    (t : NNReal) (ht : 0 < t) {f : Vec d → ℝ} (hf : Measurable f)
    {F : ℝ} (hF : 0 ≤ F) (hbound : ∀ x, |f x| ≤ F) :
    Continuous (kernelIntegral (P t) f) := by
  apply continuous_of_locally_uniform_approx_of_continuousAt
  intro x V hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.mp hV
  obtain ⟨u, hu, herr⟩ := exists_continuous_kernelIntegral_approx
    P hFeller μ happrox (Metric.closedBall x 1) (isCompact_closedBall x 1)
    t ht hf hF hbound (ε := ε / 2) (by positivity)
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x (by norm_num),
    u, hu.continuousAt, ?_⟩
  intro y hy
  apply hεV
  rw [Real.dist_eq]
  exact (herr y hy).trans_lt (by linarith)

end SubdiffusiveProcess.Section10
