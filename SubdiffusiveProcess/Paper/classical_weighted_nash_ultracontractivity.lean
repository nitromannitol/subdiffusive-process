import Mathlib
import SubdiffusiveProcess.Nash.Ultracontractivity
import MarkovProcess.Semigroup.Generator
import MarkovProcess.Kernel.OperatorSemigroup

open MeasureTheory MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal NNReal RealInnerProductSpace
universe u


namespace Paper

theorem classical_weighted_nash_ultracontractivity
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
  exact SubdiffusiveProcess.Nash.symmetric_subMarkov_sobolev_ultracontractive d hd

end Paper
