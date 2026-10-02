import Mathlib
import SubdiffusiveProcess.Nash.TimeSplit
import SubdiffusiveProcess.Nash.KernelExtension
import SubdiffusiveProcess.Nash.DimensionConstant
import MarkovProcess.Semigroup.Generator
import MarkovProcess.Kernel.OperatorSemigroup

open MeasureTheory MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal NNReal RealInnerProductSpace
universe u


noncomputable section
namespace SubdiffusiveProcess.Nash

theorem symmetric_subMarkov_sobolev_ultracontractive
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ Cd : ℝ, 0 < Cd ∧
      ∀ (X : Type u) [MeasurableSpace X] (mu : Measure X) [SigmaFinite mu]
        (P : SubMarkovKernelSemigroup X)
        (S : StronglyContinuousContractionSemigroup (Lp ℝ 2 mu)),
        P.IsSubInvariant mu →
        (∀ (t : ℝ≥0) (f g : Lp ℝ 2 mu), ⟪S t f, g⟫ = ⟪f, S t g⟫) →
        (∀ (t : ℝ≥0) (f : Lp ℝ 2 mu),
          ((S t f : Lp ℝ 2 mu) : X → ℝ) =ᵐ[mu] kernelIntegral (P t) f) →
        ∀ K : ℝ, 0 < K →
        (∀ f : S.generatorDomain,
          eLpNorm ((f : Lp ℝ 2 mu) : X → ℝ)
              (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1))) mu ^ (2 : ℕ) ≤
            ENNReal.ofReal K * ENNReal.ofReal
              (-⟪S.generator f, (f : Lp ℝ 2 mu)⟫)) →
        ∀ t : ℝ≥0, 0 < t →
        ∀ f : X → ℝ, Integrable f mu →
          eLpNorm (kernelIntegral (P t) f) ∞ mu ≤
            ENNReal.ofReal Cd *
              (ENNReal.ofReal K / (t : ℝ≥0∞)) ^ d * eLpNorm f 1 mu := by
  refine ⟨(d : ℝ) ^ d, by positivity, ?_⟩
  intro X _ mu _ P S hsub hsym hcompat K hK hsob t ht f hf
  have hA : 0 ≤ ((d : ℝ) * K / (t : ℝ)) ^ d := by positivity
  have hbound : ∀ g : X → ℝ, MemLp g 2 mu → Integrable g mu →
      eLpNorm (kernelIntegral (P t) g) ∞ mu ≤
        ENNReal.ofReal (((d : ℝ) * K / (t : ℝ)) ^ d) * eLpNorm g 1 mu := by
    intro g hg2 hg1
    let v : Lp ℝ 2 mu := hg2.toLp g
    have hvEq : (v : X → ℝ) =ᵐ[mu] g := MemLp.coeFn_toLp hg2
    have hvI : Integrable (v : X → ℝ) mu := hg1.congr hvEq.symm
    have hrep : (S t v : X → ℝ) =ᵐ[mu] kernelIntegral (P t) g :=
      (hcompat t v).trans (kernelIntegral_congr_ae (hsub t) hvEq)
    have h := semigroup_L1_top_bound mu P S hsub hcompat hsym d hd K hK hsob t ht v hvI
    rwa [eLpNorm_congr_ae hrep, eLpNorm_congr_ae hvEq] at h
  have h := kernel_bound_of_L1_L2 mu (P t) (P.isSubMarkovKernel t) (hsub t)
    (((d : ℝ) * K / (t : ℝ)) ^ d) hA hbound f hf
  rwa [dimension_constant d K hK.le t ht] at h

end SubdiffusiveProcess.Nash
