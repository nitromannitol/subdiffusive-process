import SubdiffusiveProcess.Sobolev.ConditionalResponses

/-! # Measurable finite-layer potential and response maps

Continuous fields carry the compact-open topology. Restriction to a compact
root, finite sums, and subtraction of the value at the origin are continuous.
An arbitrary deterministic additive constant accommodates normalization.
The infinite anchored infrared sum and its measurable local convergence are
separate obligations; this file does not replace that series by a finite one.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- The literal finite anchored-coarse and unanchored-fine potential on a compact root. -/
def finiteLayerPotential (K : Compacts (SpatialCoordinates d)) (coarse fine : Finset ℤ)
    (ω : ℤ → C(SpatialCoordinates d, ℝ)) : C(K, ℝ) :=
  (∑ j ∈ coarse, ((ω j).restrict (K : Set (SpatialCoordinates d)) - ContinuousMap.const K (ω j 0))) +
    ∑ j ∈ fine, (ω j).restrict (K : Set (SpatialCoordinates d))

/-- Evaluation is exactly the finite sum prescribed by the layer model. -/
theorem finiteLayerPotential_apply (K : Compacts (SpatialCoordinates d)) (coarse fine : Finset ℤ)
    (ω : ℤ → C(SpatialCoordinates d, ℝ)) (x : K) :
    finiteLayerPotential K coarse fine ω x =
      (∑ j ∈ coarse, (ω j x - ω j 0)) + ∑ j ∈ fine, ω j x := by
  simp [finiteLayerPotential, ContinuousMap.restrict]

/-- The finite-layer map is continuous for the local uniform field topology. -/
theorem continuous_finiteLayerPotential (K : Compacts (SpatialCoordinates d)) (coarse fine : Finset ℤ) :
    Continuous (finiteLayerPotential K coarse fine) := by
  apply Continuous.add
  · apply continuous_finset_sum
    intro j hj
    exact ((ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).comp (continuous_apply j)).sub
      (ContinuousMap.continuous_const'.comp ((continuous_eval_const (0 : SpatialCoordinates d)).comp
        (continuous_apply j)))
  · apply continuous_finset_sum
    intro j hj
    exact (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).comp (continuous_apply j)

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Actual inverse responses of finitely many continuous layer restrictions are measurable. -/
theorem measurable_inverseResponse_finiteLayers (S : ResponseSpace Ω)
    (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)] (coarse fine : Finset ℤ) (c : ℝ) (L : S.space →L[ℝ] ℝ) :
    Measurable (fun ω : ℤ → C(SpatialCoordinates d, ℝ) =>
      inverseResponse S (expPotentialCoefficient
        (compactPotentialToLp K (finiteLayerPotential K coarse fine ω + ContinuousMap.const K c))) L) :=
  ((continuous_inverseResponse_compact S K L).comp
    ((continuous_finiteLayerPotential K coarse fine).add continuous_const)).measurable

/-- Actual boundary minima of finitely many continuous layers are measurable as well. -/
theorem measurable_dirichletResponse_finiteLayers (S : ResponseSpace Ω)
    (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)] (coarse fine : Finset ℤ) (c : ℝ) (b : weakSobolevGraph Ω) :
    Measurable (fun ω : ℤ → C(SpatialCoordinates d, ℝ) =>
      dirichletResponse S (expPotentialCoefficient
        (compactPotentialToLp K (finiteLayerPotential K coarse fine ω + ContinuousMap.const K c))) b) :=
  ((continuous_dirichletResponse_compact S K b).comp
    ((continuous_finiteLayerPotential K coarse fine).add continuous_const)).measurable

end SubdiffusiveProcess
