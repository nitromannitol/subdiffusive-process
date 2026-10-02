import SubdiffusiveProcess.Model.BrownianDiffusion
import SubdiffusiveProcess.Model.KilledBrownian
import SubdiffusiveProcess.Model.BrownianResolventSubinvariant




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Model.HeatSemigroupVec SubdiffusiveProcess.Model.LifetimeProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The independent-coordinate Gaussian semigroup with variance `2t`. -/
def laplacianSemigroup (d : ℕ) : SubMarkovKernelSemigroup (Vec d) where
  kernel t := heatSemigroupVec d (2 * t)
  measurable_kernel := (heatSemigroupVec d).measurable_kernel.comp
    (show Measurable (fun p : NNReal × Vec d => (2 * p.1, p.2)) from by fun_prop)
  kernel_zero := by rw [mul_zero]; exact (heatSemigroupVec d).kernel_zero
  kernel_add s t := by rw [mul_add]; exact (heatSemigroupVec d).kernel_add (2 * s) (2 * t)
  isSubMarkovKernel t := (heatSemigroupVec d).isSubMarkovKernel (2 * t)

/-- The transition law has coordinate variance `2t`, fixing the factor of two. -/
theorem laplacianSemigroup_apply (t : NNReal) (x : Vec d) :
    laplacianSemigroup d t x = gaussianVec d x (2 * t) :=
  heatSemigroupVec_apply (2 * t) x

/-- The rescaled Gaussian semigroup is conservative. -/
theorem isConservative_laplacianSemigroup : (laplacianSemigroup d).IsConservative :=
  fun t x => isConservative_heatSemigroupVec (2 * t) x

/-- A deterministic linear change of clock preserves the Feller properties. -/
theorem isFeller_laplacianSemigroup : (laplacianSemigroup d).IsFellerKernelSemigroup := by
  refine ⟨fun t f => mapsC0_heatSemigroupVec (2 * t) f, ?_⟩
  intro f
  exact (hasContinuousC0Orbits_heatSemigroupVec f).comp (continuous_const.mul continuous_id)

/-- The fourth moment bound has the expected factor `2²`. -/
theorem hasKolmogorovMoments_laplacianSemigroup :
    (laplacianSemigroup d).HasKolmogorovMoments 4 2 (4 * vecFourthMoment d) := by
  refine ⟨by norm_num, by norm_num, fun t x => ?_⟩
  have h := (hasKolmogorovMoments_heatSemigroupVec (d := d)).2.2 (2 * t) x
  change (∫⁻ z, edist z x ^ (4 : ℝ) ∂heatSemigroupVec d (2 * t) x) ≤ _
  convert h using 1
  push_cast
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  ring

/-- The rescaled process meets MarkovProcess's path continuity criterion. -/
theorem kolmogorovRegular_laplacianSemigroup :
    (laplacianSemigroup d).KolmogorovRegular isConservative_laplacianSemigroup :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _ _
    hasKolmogorovMoments_laplacianSemigroup

/-- The continuous Brownian path kernel at the variance-`2t` clock. -/
def laplacianContinuousLaw (d : ℕ) : Kernel (Vec d) (ContinuousPath (Vec d)) :=
  SubMarkovKernelSemigroup.IsConservative.continuousProcess (laplacianSemigroup d)
    isConservative_laplacianSemigroup



def laplacianLaw (d : ℕ) : Kernel (Vec d) (Path d) :=
  lifetimeProcess (laplacianSemigroup d) isConservative_laplacianSemigroup

/-- The full-Laplacian Brownian law satisfies the exact GMC stopping-time predicate. -/
theorem strongMarkov_laplacianLaw : StrongMarkov (laplacianLaw d) :=
  strongMarkov_lifetimeProcess _ _ isFeller_laplacianSemigroup
    kolmogorovRegular_laplacianSemigroup

instance isMarkovKernel_laplacianLaw : IsMarkovKernel (laplacianLaw d) :=
  ⟨fun x => ⟨strongMarkov_laplacianLaw.1 x⟩⟩

/-- The Brownian lifetime is almost surely infinite at every starting point. -/
theorem ae_lifetime_laplacianLaw (x : Vec d) :
    ∀ᵐ w ∂laplacianLaw d x, w.lifetime = ∞ := by
  rw [laplacianLaw, lifetimeProcess_apply]
  exact (ae_map_iff LifetimePath.measurable_ofContinuousPath.aemeasurable
    (measurableSet_eq_fun LifetimePath.measurable_lifetime measurable_const)).2
      (Filter.Eventually.of_forall LifetimePath.lifetime_ofContinuousPath)

/-- Evaluation of the continuous law has the required finite-dimensional Gaussian carrier. -/
theorem laplacianContinuousLaw_map_eval (t : NNReal) :
    (laplacianContinuousLaw d).map (fun w => w t) = laplacianSemigroup d t :=
  isFeller_laplacianSemigroup.continuousProcess_map_eval_nnreal
    (laplacianSemigroup d) isConservative_laplacianSemigroup
    kolmogorovRegular_laplacianSemigroup t

/-- Lebesgue measure is invariant under the rescaled Gaussian semigroup. -/
theorem isSubInvariant_laplacianSemigroup :
    (laplacianSemigroup d).IsSubInvariant (volume : Measure (Vec d)) :=
  fun t => isSubInvariant_volume_heatSemigroupVec d (2 * t)

/-- The killed Brownian transition kernels are subinvariant without an elliptic PDE premise. -/
theorem killedKernel_laplacianLaw_subinvariant (U : Set (Vec d)) (hU : IsOpen U)
    (t : NNReal) :
    killedKernel (laplacianLaw d) U hU t ∘ₘ (volume.restrict U) ≤ volume.restrict U := by
  rw [laplacianLaw, killedKernel_lifetimeProcess]
  exact killedKernel_subinvariant (laplacianSemigroup d) isConservative_laplacianSemigroup
    isFeller_laplacianSemigroup kolmogorovRegular_laplacianSemigroup volume
    isSubInvariant_laplacianSemigroup U hU t

/-- The normalized killed resolvent kernel is subinvariant on a bounded domain. -/
theorem resolventKernel_laplacianLaw_subinvariant (U : Set (Vec d)) (hU : IsOpen U)
    (s : ℝ) (hs : 0 < s) :
    resolventKernel (laplacianLaw d) U hU s hs ∘ₘ (volume.restrict U) ≤ volume.restrict U :=
  SubdiffusiveProcess.Model.resolventKernel_subinvariant_of_killed _ U hU s hs _
    (killedKernel_laplacianLaw_subinvariant U hU)

/-- The normalized killed Brownian resolvent is an actual bounded `L²` operator. -/
def laplacianResolventLp (U : Set (Vec d)) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (s : ℝ) (hs : 0 < s) :
    Lp ℝ 2 (volume.restrict U) →L[ℝ] Lp ℝ 2 (volume.restrict U) :=
  letI := SubdiffusiveProcess.Model.isFiniteMeasure_volume_restrict hUb
  kernelLpFinite (volume.restrict U) (resolventKernel (laplacianLaw d) U hU s hs)
    (resolventKernel_subMarkov _ U hU s hs)
    (resolventKernel_laplacianLaw_subinvariant U hU s hs) 2

/-- The constructed resolvent operator is a contraction. -/
theorem norm_laplacianResolventLp_le (U : Set (Vec d)) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (s : ℝ) (hs : 0 < s) :
    ‖laplacianResolventLp U hU hUb s hs‖ ≤ 1 :=
  letI := SubdiffusiveProcess.Model.isFiniteMeasure_volume_restrict hUb
  norm_kernelLpFinite_le _ _ _ _ 2

/-- Its representative is the literal normalized path resolvent in `LocalDiffusion`. -/
theorem laplacianResolventLp_coeFn (U : Set (Vec d)) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (s : ℝ) (hs : 0 < s)
    (f : Lp ℝ 2 (volume.restrict U)) :
    laplacianResolventLp U hU hUb s hs f =ᵐ[volume.restrict U]
      killedResolvent (laplacianLaw d) U s f := by
  letI := SubdiffusiveProcess.Model.isFiniteMeasure_volume_restrict hUb
  refine (coeFn_kernelLpFinite _ _ _ _ 2 f).trans ?_
  exact resolventKernel_integral_ae _ U hU s hs _
    (resolventKernel_laplacianLaw_subinvariant U hU s hs) _
    ((Lp.memLp f).integrable (by norm_num))

end SubdiffusiveProcess.Probability.Diffusion
