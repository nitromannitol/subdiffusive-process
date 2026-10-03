module

public import SubdiffusiveProcess.Sobolev.LocalEnergy
public import SubdiffusiveProcess.Sobolev.PotentialPerturbation
public import Mathlib.Tactic

@[expose] public section




open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess
namespace Lane3

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The localized weighted form is monotone in the localizing set. -/
theorem weightedL2Form_localize_mono (a : Lp ℝ ∞ μ) {s t : Set α}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t)
    (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (u : Lp ℝ 2 μ) :
    weightedL2Form a (localizeL2 hs u) (localizeL2 hs u) ≤
      weightedL2Form a (localizeL2 ht u) (localizeL2 ht u) := by
  rw [weightedL2Form_apply, weightedL2Form_apply]
  apply integral_mono_ae (integrable_weighted_inner a _ _) (integrable_weighted_inner a _ _)
  filter_upwards [ha, localizeL2_coeFn hs u, localizeL2_coeFn ht u] with x hx hes het
  rw [hes, het]
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem (hst hxs)]
  · simp only [Set.indicator_of_notMem hxs, inner_zero_left, mul_zero]
    by_cases hxt : x ∈ t
    · rw [Set.indicator_of_mem hxt]
      exact mul_nonneg hx real_inner_self_nonneg
    · simp only [Set.indicator_of_notMem hxt, inner_zero_left, mul_zero]
      exact le_refl 0

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Local energy is monotone in the measurable set. -/
theorem localGradientEnergy_mono (a : PositiveCoefficient Ω)
    {s t : Set (SpatialCoordinates d)} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) (g : HilbertGradient Ω) :
    localGradientEnergy a hs g ≤ localGradientEnergy a ht g := by
  simp only [localGradientEnergy]
  exact Finset.sum_le_sum fun i _ =>
    weightedL2Form_localize_mono a.val hs ht hst (positiveCoefficient_ae_nonneg a) (g i)

/-- On the whole space the local energy is the total coefficient energy. -/
theorem localGradientEnergy_univ (a : PositiveCoefficient Ω) (g : HilbertGradient Ω) :
    localGradientEnergy a MeasurableSet.univ g = weightedGradientForm a.val g g := by
  simp only [localGradientEnergy, weightedGradientForm, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.bilinearComp_apply, PiLp.proj_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [weightedL2Form_apply, weightedL2Form_apply]
  apply integral_congr_ae
  filter_upwards [localizeL2_coeFn (MeasurableSet.univ (α := SpatialCoordinates d)) (g i)]
    with x hx
  rw [hx]
  simp only [Set.indicator_univ]

end Lane3
end SubdiffusiveProcess
