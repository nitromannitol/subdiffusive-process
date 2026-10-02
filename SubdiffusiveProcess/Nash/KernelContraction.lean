import MarkovProcess.Semigroup.Generator
import MarkovProcess.Kernel.OperatorSemigroup
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.Nash

/-- Compatibility with a subinvariant sub-Markov kernel gives L1 contraction. -/
theorem semigroup_eLpNorm_one_le {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (P : SubMarkovKernelSemigroup X)
    (S : StronglyContinuousContractionSemigroup (Lp ℝ 2 mu))
    (hsub : P.IsSubInvariant mu)
    (hcompat : ∀ (t : ℝ≥0) (f : Lp ℝ 2 mu), (S t f : X → ℝ) =ᵐ[mu] kernelIntegral (P t) f)
    (t : ℝ≥0) (f : Lp ℝ 2 mu) (hf : Integrable (f : X → ℝ) mu) :
    eLpNorm (S t f : X → ℝ) 1 mu ≤ eLpNorm (f : X → ℝ) 1 mu := by
  rw [eLpNorm_congr_ae (hcompat t f)]
  exact eLpNorm_kernelIntegral_le (P.isSubMarkovKernel t) (hsub t) (by norm_num : (1 : ℝ≥0) ≤ 1)
    (memLp_one_iff_integrable.mpr hf)

/-- The orbit stays integrable at exponent one. -/
theorem semigroup_integrable {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (P : SubMarkovKernelSemigroup X)
    (S : StronglyContinuousContractionSemigroup (Lp ℝ 2 mu))
    (hsub : P.IsSubInvariant mu)
    (hcompat : ∀ (t : ℝ≥0) (f : Lp ℝ 2 mu), (S t f : X → ℝ) =ᵐ[mu] kernelIntegral (P t) f)
    (t : ℝ≥0) (f : Lp ℝ 2 mu) (hf : Integrable (f : X → ℝ) mu) :
    Integrable (S t f : X → ℝ) mu := by
  apply memLp_one_iff_integrable.mp
  exact ⟨Lp.aestronglyMeasurable _, (semigroup_eLpNorm_one_le mu P S hsub hcompat t f hf).trans_lt
    (memLp_one_iff_integrable.mpr hf).2⟩

end SubdiffusiveProcess.Nash
