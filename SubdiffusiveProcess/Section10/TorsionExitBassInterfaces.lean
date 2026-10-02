import SubdiffusiveProcess.Section10.TorsionExitC2MartingaleProblem
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularityKilled
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderRegularity

/-! Disjoint completing interfaces for the reversible weighted route. These
are internal propositions without witnesses, not new cited leaves or source
root assumptions. The actual same-speed Feller family supplies their data. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledResolventLp
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- Uniform small-time exit control for the actual continuous-path law.
The event includes exit exactly at the deterministic horizon. -/
def UniformEarlyExit {d : ℕ}
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) : Prop :=
  ∀ U : Set (Vec d), IsOpen U → ∀ S : Set (Vec d), IsCompact S → S ⊆ U →
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ t : NNReal, (t : ℝ) < delta → ∀ x ∈ S,
        K x {w | ContinuousPath.exitTime U w ≤ (t : ENNReal)} ≤ ENNReal.ofReal eps

/-- A local L¹ approximation estimate for the original whole-space kernels.
The error can be made arbitrarily small at an arbitrarily short positive time;
the L¹ constant may depend on that time. This retains all starting points. -/
def LocalL1ApproximationBound {d : ℕ}
    (P : SubMarkovKernelSemigroup (Vec d)) (mu : Measure (Vec d)) : Prop :=
  ∀ S : Set (Vec d), IsCompact S → ∀ eps delta : ℝ,
    0 < eps → 0 < delta → ∃ s : NNReal, 0 < s ∧ (s : ℝ) < delta ∧
      ∃ W : Set (Vec d), IsOpen W ∧ Bornology.IsBounded W ∧ mu W ≠ ∞ ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ g : Vec d → ℝ, Measurable g →
        ∀ F : ℝ, 0 ≤ F → (∀ y, |g y| ≤ F) → ∀ x ∈ S,
          (∫ y, |g y| ∂P s x) ≤ A * (∫ y in W, |g y| ∂mu) + eps * F



def FellerKilledStartContinuitySupplier : Prop :=
  ∀ (d : ℕ) (a : Vec d → ℝ) (_hapos : ∀ x, 0 < a x) (_ha : Continuous a)
    (P : SubMarkovKernelSemigroup (Vec d)) (_hP : P.IsConservative)
    (_hF : P.IsFellerKernelSemigroup)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) (_hK : IsMarkovKernel K)
    (_hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (_happrox : LocalL1ApproximationBound P (weightedMeasure a))
    (_hearly : UniformEarlyExit K),
    ∀ U : Set (Vec d), ∀ hU : IsOpen U, ∀ t : ℝ, 0 < t →
      ∀ B : Set (Vec d), MeasurableSet B →
        ContinuousOn (fun x => (killedKernel (K.map LifetimePath.ofContinuousPath)
          U hU (Real.toNNReal t) x B).toReal) U



def ReversibleKilledSmoothingSupplier : Prop :=
  ∀ (d : ℕ) (_hd : 2 ≤ d) (a : Vec d → ℝ) (_hapos : ∀ x, 0 < a x)
    (_ha : Continuous a) (law : Kernel (Vec d) (Path d))
    [hK : IsMarkovKernel law] (hD : LocalDiffusion a a law)
    (U : Set (Vec d)) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    [hfinite : IsFiniteMeasure ((weightedMeasure a).restrict U)],
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp ℝ 2 ((weightedMeasure a).restrict U),
      ∀ᵐ x ∂((weightedMeasure a).restrict U),
        |(((killedResolventLp hD hU hUb 1 (by norm_num)) ^ N) f) x| ≤ C * ‖f‖



def ReversibleFellerLocalL1ApproximationSupplier : Prop :=
  ∀ (d : ℕ) (_hd : 2 ≤ d) (a : Vec d → ℝ) (_hapos : ∀ x, 0 < a x)
    (_ha : Continuous a) (P : SubMarkovKernelSemigroup (Vec d))
    (_hP : P.IsConservative) (_hF : P.IsFellerKernelSemigroup)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) (_hK : IsMarkovKernel K)
    (_hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (_hD : LocalDiffusion a a (K.map LifetimePath.ofContinuousPath))
    (_hearly : UniformEarlyExit K),
    LocalL1ApproximationBound P (weightedMeasure a)

end SubdiffusiveProcess.Section10
