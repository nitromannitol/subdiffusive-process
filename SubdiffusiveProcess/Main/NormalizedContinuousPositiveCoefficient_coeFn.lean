import SubdiffusiveProcess.Main.ContinuousPositiveLog
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient
import SubdiffusiveProcess.Sobolev.GridFoldConvolution

open MeasureTheory Set TopologicalSpace
open scoped NNReal
noncomputable section

namespace SubdiffusiveProcess

theorem normalizedContinuousPositiveCoefficient_coeFn
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (K : Compacts (SpatialCoordinates d))
    [hΩ : Fact (((Ω : Set (SpatialCoordinates d)) ⊆ K))]
    (a : C(K, ℝ)) (ha : ∀ x, 0 < a x) (a₀ : ℝ) (ha₀ : 0 < a₀) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), ∀ hx : x ∈ Ω,
      (normalizedContinuousPositiveCoefficient (Ω := Ω) K a ha a₀ ha₀).val x =
        a ⟨x, hΩ.out hx⟩ / a₀ := by
  filter_upwards [
    expPotentialCoefficient_coeFn (compactPotentialToLp (Ω := Ω) K
      (continuousPositiveLog a ha - ContinuousMap.const K (Real.log a₀))),
    compactPotentialToLp_on_domain (Ω := Ω) K
      (continuousPositiveLog a ha - ContinuousMap.const K (Real.log a₀))] with x hexp hroot
  intro hx
  unfold normalizedContinuousPositiveCoefficient
  rw [hexp, hroot hx]
  change Real.exp (Real.log (a ⟨x, hΩ.out hx⟩) - Real.log a₀) = _
  rw [Real.exp_sub, Real.exp_log (ha _), Real.exp_log ha₀]

end SubdiffusiveProcess
