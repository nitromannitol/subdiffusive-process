module

public import SubdiffusiveProcess.Sobolev.PartitionDefect
public import SubdiffusiveProcess.Sobolev.RestrictedTriadicResponse
public import SubdiffusiveProcess.Geometry.TriadicFinitePartition

@[expose] public section

/-! # The finite adaptive response inequality on actual cubes

Only primal and inverse-Neumann subadditivity are supplied as named
finite-cutoff inputs. The actual adaptive geometry supplies the positive
volumes, exact weight sum, coefficient restrictions and separation into
retained generations and the final unresolved response.
-/
open MeasureTheory Set TopologicalSpace
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
variable
  (hD0 : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
    ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
    K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
  (hN0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (centeredCube z r hr),
    ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
    K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) u‖)
  (hD : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
    ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
      ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
      K * ‖subspaceGradient (killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)
  (hN : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
    ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
      ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
      K * ‖subspaceGradient (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)

include hD in
/-- Killed Poincare is inherited from the actual grid cell selected by the adaptive label. -/
theorem triadicAdaptiveCell_killedPoincare (J : ℕ) (t : TriadicAdaptiveIndex d J) :
    ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (triadicAdaptiveCell z r hr J t),
      ‖(u : SobolevData (triadicAdaptiveCell z r hr J t)).1‖ ≤
      K * ‖subspaceGradient (killedSobolevGraph (triadicAdaptiveCell z r hr J t)) u‖ := by
  rcases t with ⟨j, k⟩ | k
  · exact hD (j.val + 1) k
  · exact hD J k

include hN in
/-- Mean-zero Poincare is transported through the actual adaptive label, retaining finite volume. -/
theorem triadicAdaptiveCell_meanZeroPoincare (J : ℕ) (t : TriadicAdaptiveIndex d J) :
    ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (triadicAdaptiveCell z r hr J t),
      ‖(u : SobolevData (triadicAdaptiveCell z r hr J t)).1‖ ≤
      K * ‖subspaceGradient (meanZeroSobolevGraph (triadicAdaptiveCell z r hr J t)) u‖ := by
  rcases t with ⟨j, k⟩ | k
  · exact hN (j.val + 1) k
  · exact hN J k

/-- The adaptive partition bounds the root defect by its retained generations and actual residual. -/
theorem affineDiagonalDefect_triadicPartition {I : Finset (Fin d)} (hI : I.Nonempty)
    (J : ℕ) (a : PositiveCoefficient (centeredCube z r hr)) (p : Fin d → ℝ)
    (hDir : affineDirichletResponse (centeredCube_isBounded z hr) hD0 a p ≤
      ∑ t ∈ triadicAdaptiveLabels I J,
        affineDirichletResponse (triadicAdaptiveCell_isBounded z hr J t)
          (triadicAdaptiveCell_killedPoincare z hr hD J t)
          (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root z hr J t) a) p)
    (hNeu : affineInverseNeumannResponse hN0 a p ≤
      ∑ t ∈ triadicAdaptiveLabels I J,
        affineInverseNeumannResponse (triadicAdaptiveCell_meanZeroPoincare z hr hN J t)
          (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root z hr J t) a) p) :
    affineDiagonalDefect (centeredCube_isBounded z hr) (centeredCube_volume_pos z hr)
      hD0 hN0 a p ≤
      (∑ j : Fin J, ∑ k ∈ triadicRetainedLabels j.val I,
        (volume.real (oddGridCell z r hr (triadicHalf (j.val + 1)) k :
          Set (SpatialCoordinates d)) / volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) *
        affineDiagonalDefect (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
          (hD (j.val + 1) k) (hN (j.val + 1) k)
          (positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf (j.val + 1)) k) a) p) +
      triadicResponseResidual z hr hD hN
        (fun n k => positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf n) k) a)
        I (fun _ _ => p) J := by
  have h := affineDiagonalDefect_le_partition (triadicAdaptiveCell z r hr J)
    (triadicAdaptiveLabels I J) (triadicAdaptiveCell_subset_root z hr J)
    (centeredCube_isBounded z hr) (centeredCube_volume_pos z hr)
    (triadicAdaptiveCell_volume_pos z hr J) (triadicAdaptiveCells_sum_volume z hr hI J)
    hD0 hN0 (triadicAdaptiveCell_killedPoincare z hr hD J)
    (triadicAdaptiveCell_meanZeroPoincare z hr hN J) a p hDir hNeu
  rw [triadicAdaptive_sum] at h
  exact h

end SubdiffusiveProcess
