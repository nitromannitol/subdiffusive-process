module

public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.CutoffPotential
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal BigOperators

namespace Paper
noncomputable section



def conditional_response_setup
    (d : ℕ) (Q : TopologicalSpace.Opens (SpatialCoordinates d))
    (K : Set (SpatialCoordinates d)) [CompactSpace K] (H : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Pa nu : Measure (BilateralField d))
    [IsProbabilityMeasure Pa] [IsProbabilityMeasure nu]
    (R : Response Q) (kappa : ℕ → ℝ)
    (restrictQ : C(K, ℝ) → Potential Q)
    (V : BilateralField d → C(K, ℝ))
    (t : ℕ → BilateralField d → C(K, ℝ))
    (Sigma : Set (BilateralField d))
    (RN : ℕ → (BilateralField d × BilateralField d) → ℝ)
    (FN : ℕ → C(K, ℝ) → ℝ≥0∞) : Prop :=
  (closure (Q : Set (SpatialCoordinates d)) ⊆ K ∧ ∀ N, 0 < kappa N) ∧
  ((∀ v : C(K, ℝ), ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      ∀ hx : x ∈ K, restrictQ v x = v ⟨x, hx⟩) ∧
    ∀ v : C(K, ℝ), ‖restrictQ v‖ ≤ ‖v‖) ∧
  (∀ a, V a =
    (∑ j ∈ Finset.Icc (-(H : ℤ)) (-1),
      ((a (-j)).restrict K - ContinuousMap.const K (a (-j) 0))) +
    ∑ j ∈ Finset.range (H + 1), (a (-(j : ℤ))).restrict K) ∧
  (Sigma = {y | Summable (fun i : ℕ =>
    (y ((H : ℤ) + 1 + (i : ℤ))).restrict K -
      ContinuousMap.const K (y ((H : ℤ) + 1 + (i : ℤ)) 0))}) ∧
  (MeasurableSet Sigma ∧ nu Sigma = 1) ∧
  (∀ N, H ≤ N → ∀ y ∈ Sigma, t N y =
    (∑' i : ℕ, ((y ((H : ℤ) + 1 + (i : ℤ))).restrict K -
      ContinuousMap.const K (y ((H : ℤ) + 1 + (i : ℤ)) 0))) +
    (∑ j ∈ Finset.Icc (H + 1) N, (y (-(j : ℤ))).restrict K) -
      ContinuousMap.const K (Real.log (kappa N))) ∧
  (∀ N, H ≤ N → ∀ a y, y ∈ Sigma →
    RN N (a, y) = R.eval (restrictQ (V a + t N y))) ∧
  (∀ N, H ≤ N → ∀ v, FN N v =
    ∫⁻ y in Sigma, ENNReal.ofReal (R.eval (restrictQ (v + t N y))) ∂nu)

end
end Paper
