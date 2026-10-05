module

public import SubdiffusiveProcess.Main.ContinuousPositiveLog
public import SubdiffusiveProcess.Sobolev.GridFoldConvolution

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped NNReal
noncomputable section

namespace SubdiffusiveProcess

def normalizedContinuousPositiveCoefficient
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (K : Compacts (SpatialCoordinates d))
    [Fact (((Ω : Set (SpatialCoordinates d)) ⊆ K))]
    (a : C(K, ℝ)) (ha : ∀ x, 0 < a x) (a₀ : ℝ) (_ha₀ : 0 < a₀) :
    PositiveCoefficient Ω :=
  expPotentialCoefficient (compactPotentialToLp (Ω := Ω) K
    (continuousPositiveLog a ha - ContinuousMap.const K (Real.log a₀)))

end SubdiffusiveProcess
