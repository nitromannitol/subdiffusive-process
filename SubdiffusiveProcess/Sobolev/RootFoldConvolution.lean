module

public import SubdiffusiveProcess.Sobolev.TriadicPartitionDefect
public import SubdiffusiveProcess.Sobolev.TriadicDefectSup
public import SubdiffusiveProcess.Sobolev.FoldedDefect

@[expose] public section

/-! # The centered-root fold convolution

Actual retained-cell covariance and geometric volume weights are combined
with the named finite-partition primal and inverse-Neumann inequalities.
The unresolved term tends to zero at the fixed folded root coefficient.
This is a centered-root estimate; general observation subcubes require
additional ancestor bookkeeping before the full grid-maximum statement.
-/
open MeasureTheory Set TopologicalSpace Filter
open scoped NNReal Topology
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


/-- One retained generation is bounded by its actual geometric volume fraction and original-grid supremum. -/
theorem foldedRetainedResponse_sum_le (hd : 0 < d) (I P : Finset (Fin d))
    (g : C(closedCube z r hr, ℝ)) {p : Fin d → ℝ}
    (hp : (∑ i : Fin d, (p i)^2) = 1) (J : ℕ) :
    let a := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) g)
    let af := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) (g.comp (coordinateFoldOnCube z hr I P)))
    (∑ k ∈ triadicRetainedLabels J I,
      (volume.real (oddGridCell z r hr (triadicHalf (J + 1)) k : Set (SpatialCoordinates d)) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) *
      affineDiagonalDefect (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
        (hD (J + 1) k) (hN (J + 1) k)
        (positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf (J + 1)) k) af) p) ≤
      ((d : ℝ) / (3 : ℝ)^J) * triadicDefectSup z hr hD hN a hd (J + 1) := by
  intro a af
  let B := triadicDefectSup z hr hD hN a hd (J + 1)
  calc
    _ ≤ ∑ k ∈ triadicRetainedLabels J I,
        (volume.real (oddGridCell z r hr (triadicHalf (J + 1)) k : Set (SpatialCoordinates d)) /
          volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) * B := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact affineDiagonalDefect_retained_fold_le z hr J (hD (J + 1)) (hN (J + 1)) I P g
        (fun k p hp => le_triadicDefectSup z hr hD hN a hd (J + 1) k hp) hk hp
    _ = (∑ k ∈ triadicRetainedLabels J I,
        volume.real (oddGridCell z r hr (triadicHalf (J + 1)) k : Set (SpatialCoordinates d)) /
          volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) * B := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (triadicRetainedCells_sum_weights_le hd z hr I J)
      (triadicDefectSup_nonneg z hr hD hN a hd (J + 1))

/-- The actual centered-root fold obeys the full geometric convolution, relative only to finite-partition subadditivity. -/
theorem foldedRoot_defect_le_series (hd : 0 < d) {I : Finset (Fin d)} (hI : I.Nonempty)
    (P : Finset (Fin d)) (g : C(closedCube z r hr, ℝ)) {p : Fin d → ℝ}
    (hp : (∑ i : Fin d, (p i)^2) = 1) :
    let a := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) g)
    let af := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) (g.comp (coordinateFoldOnCube z hr I P)))
    (∀ J,
      (triadicAdaptiveLabels I J : Set (TriadicAdaptiveIndex d J)).PairwiseDisjoint
        (fun t => (triadicAdaptiveCell z r hr J t : Set (SpatialCoordinates d))) →
      ((⋃ t ∈ triadicAdaptiveLabels I J,
        (triadicAdaptiveCell z r hr J t : Set (SpatialCoordinates d)))
        =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d))) →
      affineDirichletResponse (centeredCube_isBounded z hr) hD0 af p ≤
        ∑ t ∈ triadicAdaptiveLabels I J,
          affineDirichletResponse (triadicAdaptiveCell_isBounded z hr J t)
            (triadicAdaptiveCell_killedPoincare z hr hD J t)
            (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root z hr J t) af) p) →
    (∀ J,
      (triadicAdaptiveLabels I J : Set (TriadicAdaptiveIndex d J)).PairwiseDisjoint
        (fun t => (triadicAdaptiveCell z r hr J t : Set (SpatialCoordinates d))) →
      ((⋃ t ∈ triadicAdaptiveLabels I J,
        (triadicAdaptiveCell z r hr J t : Set (SpatialCoordinates d)))
        =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d))) →
      affineInverseNeumannResponse hN0 af p ≤
        ∑ t ∈ triadicAdaptiveLabels I J,
          affineInverseNeumannResponse (triadicAdaptiveCell_meanZeroPoincare z hr hN J t)
            (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root z hr J t) af) p) →
    affineDiagonalDefect (centeredCube_isBounded z hr) (centeredCube_volume_pos z hr)
      hD0 hN0 af p ≤
      ∑' j : ℕ, ((d : ℝ) / (3 : ℝ)^j) * triadicDefectSup z hr hD hN a hd (j + 1) := by
  intro a af hDir hNeu
  let b := fun j : ℕ => ((d : ℝ) / (3 : ℝ)^j) * triadicDefectSup z hr hD hN a hd (j + 1)
  let R := triadicResponseResidual z hr hD hN
    (fun n k => positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf n) k) af)
    I (fun _ _ => p)
  have hfinite : ∀ J, affineDiagonalDefect (centeredCube_isBounded z hr)
      (centeredCube_volume_pos z hr) hD0 hN0 af p ≤ (∑ j ∈ Finset.range J, b j) + R J := by
    intro J
    have hpart := affineDiagonalDefect_triadicPartition z hr hD0 hN0 hD hN hI J af p
      (hDir J (triadicAdaptiveCells_pairwiseDisjoint z hr I J)
        (triadicAdaptiveCells_union_ae_eq z hr hI J))
      (hNeu J (triadicAdaptiveCells_pairwiseDisjoint z hr I J)
        (triadicAdaptiveCells_union_ae_eq z hr hI J))
    refine hpart.trans (add_le_add ?_ (le_refl (R J)))
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_le_sum
    intro j _
    exact foldedRetainedResponse_sum_le z hr hD hN hd I P g hp j.val
  have hs : Summable b := triadicDefectSup_summable z hr hD hN a hd
  have hR : Tendsto R atTop (𝓝 0) :=
    restrictedTriadicResponseResidual_tendsto_zero z hr hd hD hN af I (fun _ _ => hp)
  have hlim := hs.hasSum.tendsto_sum_nat.add hR
  simpa only [add_zero] using ge_of_tendsto' hlim hfinite

end SubdiffusiveProcess
