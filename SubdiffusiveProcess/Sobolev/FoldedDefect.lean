import SubdiffusiveProcess.Sobolev.FoldedPotential
import SubdiffusiveProcess.Sobolev.ReflectionDefect
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Geometry.TriadicAdaptive

/-! # Actual retained-cell responses of the folded root coefficient

Both coefficient families are restrictions of their single compact-root
potentials. The fold selects a literal original-grid image and a signed
slope. Ordinary Poincare on these finite-cutoff cubes is the only analytic
input here; coefficient and response covariance are proved.
-/
open MeasureTheory Set TopologicalSpace
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d m : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
variable
    (hD : ∀ k : OddGridIndex d m, ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (oddGridCell z r hr m k),
        ‖(u : SobolevData (oddGridCell z r hr m k)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (oddGridCell z r hr m k)) u‖)
    (hN : ∀ k : OddGridIndex d m, ∃ K : ℝ≥0,
      ∀ u : meanZeroSobolevGraph (oddGridCell z r hr m k),
        ‖(u : SobolevData (oddGridCell z r hr m k)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (oddGridCell z r hr m k)) u‖)

/-- A folded cell defect equals the original-grid defect at the explicitly reflected slope. -/
theorem affineDiagonalDefect_fold_cell (I P : Finset (Fin d))
    (k : OddGridIndex d m) (hk : k ∉ oddGridUnresolved m I)
    (g : C(closedCube z r hr, ℝ)) (p : Fin d → ℝ) :
    affineDiagonalDefect (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
      (hD k) (hN k)
      (positiveCoefficientRestrict (oddGridCell_subset z hr m k)
        (expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
          (closedCube z r hr) (g.comp (coordinateFoldOnCube z hr I P))))) p =
    affineDiagonalDefect (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
      (hD (oddGridReflect (oddGridFoldReflections I P k) k))
      (hN (oddGridReflect (oddGridFoldReflections I P k) k))
      (positiveCoefficientRestrict
        (oddGridCell_subset z hr m (oddGridReflect (oddGridFoldReflections I P k) k))
        (expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
          (closedCube z r hr) g)))
      (coordinateReflectionDerivative (oddGridFoldReflections I P k) p) := by
  rw [positiveCoefficientRestrict_compactPotential,
    positiveCoefficientRestrict_compactPotential]
  let J := oddGridFoldReflections I P k
  have h := affineDiagonalDefect_reflection
    (U := oddGridCell z r hr m k) (Ω := oddGridCell z r hr m (oddGridReflect J k))
    z J (coordinateReflection_preimage_oddGridCell z hr J k)
    (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
    (hD (oddGridReflect J k)) (hN (oddGridReflect J k))
    (expPotentialCoefficient (compactPotentialLp (Ω := oddGridCell z r hr m
      (oddGridReflect J k)) (closedCube z r hr) g)) (coordinateReflectionDerivative J p)
  rw [coordinateReflectionDerivative_involutive] at h
  rw [reflectionCoefficient_compactPotential_fold_cell z hr I P k hk g] at h
  exact h

/-- An original-grid unit-slope bound applies to every actual newly retained fold cell. -/
theorem affineDiagonalDefect_retained_fold_le (J : ℕ)
    (hD : ∀ k : OddGridIndex d (triadicHalf (J + 1)), ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf (J + 1)) k),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf (J + 1)) k)).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph (oddGridCell z r hr (triadicHalf (J + 1)) k)) u‖)
    (hN : ∀ k : OddGridIndex d (triadicHalf (J + 1)), ∃ K : ℝ≥0,
      ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf (J + 1)) k),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf (J + 1)) k)).1‖ ≤
        K * ‖subspaceGradient
          (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf (J + 1)) k)) u‖)
    (I P : Finset (Fin d)) (g : C(closedCube z r hr, ℝ)) {M : ℝ}
    (hM : ∀ k (p : Fin d → ℝ), (∑ i : Fin d, (p i)^2) = 1 →
      affineDiagonalDefect (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
        (hD k) (hN k)
        (positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf (J + 1)) k)
          (expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
            (closedCube z r hr) g))) p ≤ M)
    {k : OddGridIndex d (triadicHalf (J + 1))} (hk : k ∈ triadicRetainedLabels J I)
    {p : Fin d → ℝ} (hp : (∑ i : Fin d, (p i)^2) = 1) :
    affineDiagonalDefect (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
      (hD k) (hN k)
      (positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf (J + 1)) k)
        (expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
          (closedCube z r hr) (g.comp (coordinateFoldOnCube z hr I P))))) p ≤ M := by
  rw [affineDiagonalDefect_fold_cell z hr hD hN I P k (Finset.mem_filter.mp hk).2.2]
  apply hM
  rw [coordinateReflectionDerivative_sum_sq]
  exact hp

end SubdiffusiveProcess
