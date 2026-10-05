module

public import SubdiffusiveProcess.Probability.Diffusion.Brownian
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularityKilled

@[expose] public section

/-!
# Killed Brownian densities without the elliptic identification

The Gaussian product density gives absolute continuity at every starting point.
Killing preserves this by domination and support in the domain. The kernel
Radon--Nikodym derivative then gives a jointly measurable spatial density for
each positive time. Joint continuity in time and space remains an additional
analytic obligation; it is not inferred from a measurable representative.

This proves the density-existence portion of the part-kernel assertion in
`s.fixed.coefficient` directly from the Brownian law.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularityKilled
open SubdiffusiveProcess.Model.HeatSemigroupVec SubdiffusiveProcess.Model.LifetimeProcess
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The finite-coordinate Gaussian has the product of the scalar Gaussian densities. -/
theorem gaussianVec_eq_withDensity (x : Vec d) {v : NNReal} (hv : v ≠ 0) :
    gaussianVec d x v = (volume : Measure (Vec d)).withDensity
      (fun y => ∏ i, gaussianPDF (x i) v (y i)) := by
  apply Measure.pi_eq
  intro A hA
  rw [withDensity_apply _ (MeasurableSet.univ_pi hA)]
  change (∫⁻ y, ∏ i, gaussianPDF (x i) v (y i)
    ∂(Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict (univ.pi A)) = _
  rw [Measure.restrict_pi_pi, lintegral_fin_prod_eq_prod
    (fun i => (volume : Measure ℝ).restrict (A i))
    (fun i z => gaussianPDF (x i) v z) (fun i => measurable_gaussianPDF (x i) v)]
  exact Finset.prod_congr rfl fun i _ => (gaussianReal_apply (x i) hv (A i)).symm

/-- A nondegenerate Gaussian in the exact `Fin d → ℝ` carrier is absolutely continuous. -/
theorem gaussianVec_absolutelyContinuous (x : Vec d) {v : NNReal} (hv : v ≠ 0) :
    gaussianVec d x v ≪ (volume : Measure (Vec d)) := by
  rw [gaussianVec_eq_withDensity x hv]
  exact withDensity_absolutelyContinuous _ _

/-- Killed Brownian transition laws are absolutely continuous at every starting point. -/
theorem killedKernel_laplacianLaw_absolutelyContinuous (U : Set (Vec d)) (hU : IsOpen U)
    {t : NNReal} (ht : 0 < t) (x : Vec d) :
    killedKernel (laplacianLaw d) U hU t x ≪ (volume : Measure (Vec d)) := by
  rw [laplacianLaw, killedKernel_lifetimeProcess]
  have hdom := killedKernel_le_transition (laplacianSemigroup d)
    isConservative_laplacianSemigroup isFeller_laplacianSemigroup
    kolmogorovRegular_laplacianSemigroup U hU t x
  have hac : laplacianSemigroup d t x ≪ (volume : Measure (Vec d)) := by
    rw [laplacianSemigroup_apply]
    exact gaussianVec_absolutelyContinuous x (ne_of_gt (mul_pos (by norm_num) ht))
  exact (Measure.absolutelyContinuous_of_le hdom).trans hac

/-- Killing gives the precise null-set condition relative to restricted Lebesgue measure. -/
theorem killedLawAbsolutelyContinuousOn_laplacianLaw (U : Set (Vec d)) (hU : IsOpen U) :
    KilledLawAbsolutelyContinuousOn (laplacianLaw d) (fun _ => 1) U := by
  intro t ht x _ B hB hnull
  rw [← killedKernel_apply_law (laplacianLaw d) hU t x B hB,
    killedKernel_inter (laplacianLaw d) U hU]
  apply killedKernel_laplacianLaw_absolutelyContinuous U hU (Real.toNNReal_pos.mpr ht) x
  simpa only [weightedMeasure, ENNReal.ofReal_one, withDensity_const, one_smul] using hnull

/-- Kernel Radon--Nikodym differentiation only needs a finite reference measure and
pointwise absolute continuity, independently of any diffusion equation. -/
theorem exists_isKilledDensity_of_absolutelyContinuous
    {rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpen U)
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    (hac : KilledLawAbsolutelyContinuousOn law rho U) :
    ∃ p : ℝ → Vec d → Vec d → ℝ, IsKilledDensity law rho U p := by
  let η : Kernel (Vec d) (Vec d) := Kernel.const (Vec d) ((weightedMeasure rho).restrict U)
  refine ⟨fun t x y =>
    (((killedKernel law U hU (Real.toNNReal t)).rnDeriv η) x y).toReal, ?_, ?_, ?_⟩
  · intro t _
    exact (Kernel.measurable_rnDeriv _ η).ennreal_toReal
  · intro t _ x _ y _
    exact ENNReal.toReal_nonneg
  · intro t ht x hx B hB
    have : IsFiniteKernel (killedKernel law U hU (Real.toNNReal t)) :=
      (killedKernel_subMarkov law U hU (Real.toNNReal t)).isFiniteKernel
    have hac' := absolutelyContinuous_killedKernel hac hU ht hx
    have hη : η x = (weightedMeasure rho).restrict U := rfl
    rw [← killedKernel_apply_law law hU t x B hB,
      ← Kernel.setLIntegral_rnDeriv (hη ▸ hac') hB, hη, ← Measure.restrict_restrict hB]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae
      (Kernel.rnDeriv_ne_top (killedKernel law U hU (Real.toNNReal t)) η (a := x))] with y hy
    exact (ENNReal.ofReal_toReal hy).symm

/-- The full-Laplacian Brownian law has killed densities on every bounded open domain.
No weak elliptic solution or continuity premise is used. -/
theorem exists_isKilledDensity_laplacianLaw (U : Set (Vec d)) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) :
    ∃ p : ℝ → Vec d → Vec d → ℝ, IsKilledDensity (laplacianLaw d) (fun _ => 1) U p := by
  have : IsFiniteMeasure ((weightedMeasure (fun _ : Vec d => 1)).restrict U) := by
    simpa only [weightedMeasure, ENNReal.ofReal_one, withDensity_const, one_smul] using
      SubdiffusiveProcess.Model.isFiniteMeasure_volume_restrict hUb
  exact exists_isKilledDensity_of_absolutelyContinuous hU
    (killedLawAbsolutelyContinuousOn_laplacianLaw U hU)

end SubdiffusiveProcess.Probability.Diffusion
