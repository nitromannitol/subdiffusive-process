import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section
namespace Paper



theorem aux_lem_15_masked_response
    (Ω α X : Type*) [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (ξ ξ' : ι → Ω → α)
    (hξ : ∀ i, Measurable (ξ i)) (hξ' : ∀ i, Measurable (ξ' i))
    (hind : iIndepFun ξ μ) (hind' : iIndepFun ξ' μ)
    (B : ι → Set X) (masks : ι → X → ℝ)
    (hmask : ∀ i x, 0 ≤ masks i x ∧ masks i x ≤ 1)
    (hsupp : ∀ i x, x ∉ B i → masks i x = 0)
    (hsep : Pairwise (fun i j => Disjoint (B i) (B j)))
    (F : (ι → α) → ℝ) (hF : Measurable F)
    (μcoord μcoord' : Measure (ι → α)) (hlaw : μcoord = μcoord')
    (Y Y' Yhat Yhat' : Ω → ℝ)
    (hYhat : ∀ omega, Yhat omega = F (fun i => ξ i omega))
    (hYhat' : ∀ omega, Yhat' omega = F (fun i => ξ' i omega)) :
    (∫ v, F v ∂μcoord) = ∫ v, F v ∂μcoord' ∧
      (Y - Y') =ᵐ[μ]
        (fun omega =>
          (Y omega - Yhat omega) +
            (Yhat omega - ∫ v, F v ∂μcoord) -
            (Yhat' omega - ∫ v, F v ∂μcoord') +
            (Yhat' omega - Y' omega)) := by
  constructor
  · rw [hlaw]
  · filter_upwards with omega
    simp only [Pi.sub_apply]
    rw [hlaw]
    ring


end Paper
