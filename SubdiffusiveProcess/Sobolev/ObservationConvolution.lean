module

public import SubdiffusiveProcess.Sobolev.ObservationResponses
public import SubdiffusiveProcess.Sobolev.TriadicPartitionDefect

@[expose] public section

/-! # Fold convolution at arbitrary cut observation cubes

The actual local adaptive partition is used inside an original-grid
observation cube. Its retained responses are controlled on the global
original grid. Only M's two finite-partition response inequalities enter
as analytic subadditivity inputs.
-/
open MeasureTheory Set TopologicalSpace Filter
open scoped NNReal Topology
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
variable
  (hD : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
    ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
      ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
      K * ‖subspaceGradient (killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)
  (hN : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
    ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
      ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
      K * ‖subspaceGradient (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)

/-- The shifted actual original-grid series is summable at every fixed observation depth. -/
theorem triadicDefectSup_shift_summable
    (a : PositiveCoefficient (centeredCube z r hr)) (hd : 0 < d) (N : ℕ) :
    Summable (fun j : ℕ => ((d : ℝ) / (3 : ℝ)^j) *
      triadicDefectSup z hr hD hN a hd (N + (j + 1))) := by
  have hs := (summable_nat_add_iff N).mpr (triadicDefectSup_summable z hr hD hN a hd)
  have ht := hs.mul_left ((3 : ℝ)^N)
  convert ht using 1
  funext j
  simp only [Nat.add_comm j N, Nat.add_assoc, pow_add]
  field_simp

/-- A retained generation in any observation cube has its actual local weight and global response bound. -/
theorem foldedObservationRetained_sum_le (hd : 0 < d) (N : ℕ)
    (k : OddGridIndex d (triadicHalf N)) (I P : Finset (Fin d))
    (g : C(closedCube z r hr, ℝ)) {p : Fin d → ℝ}
    (hp : (∑ i : Fin d, (p i)^2) = 1) (J : ℕ) :
    let w := oddGridCenter z r (triadicHalf N) k
    let s := r / (2 * (triadicHalf N : ℝ) + 1)
    let hs : 0 < s := div_pos hr (by positivity)
    let D := observation_killedPoincare z hr hD N k
    let V := observation_meanZeroPoincare z hr hN N k
    let a := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) g)
    let af := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube w s hs)
      (closedCube z r hr) (g.comp (coordinateFoldOnCube z hr I P)))
    (∑ l ∈ triadicRetainedLabels J (triadicObservationPlanes N I k),
      (volume.real (oddGridCell w s hs (triadicHalf (J + 1)) l : Set (SpatialCoordinates d)) /
        volume.real (centeredCube w s hs : Set (SpatialCoordinates d))) *
      affineDiagonalDefect (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
        (D (J + 1) l) (V (J + 1) l)
        (positiveCoefficientRestrict (oddGridCell_subset w hs (triadicHalf (J + 1)) l) af) p) ≤
      ((d : ℝ) / (3 : ℝ)^J) * triadicDefectSup z hr hD hN a hd (N + (J + 1)) := by
  intro w s hs D V a af
  let B := triadicDefectSup z hr hD hN a hd (N + (J + 1))
  calc
    _ ≤ ∑ l ∈ triadicRetainedLabels J (triadicObservationPlanes N I k),
        (volume.real (oddGridCell w s hs (triadicHalf (J + 1)) l : Set (SpatialCoordinates d)) /
          volume.real (centeredCube w s hs : Set (SpatialCoordinates d))) * B := by
      apply Finset.sum_le_sum
      intro l hl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      erw [positiveCoefficientRestrict_compactPotential]
      exact affineDiagonalDefect_observation_retained_le z hr hD hN hd N J k I P g hl hp
    _ = (∑ l ∈ triadicRetainedLabels J (triadicObservationPlanes N I k),
        volume.real (oddGridCell w s hs (triadicHalf (J + 1)) l : Set (SpatialCoordinates d)) /
          volume.real (centeredCube w s hs : Set (SpatialCoordinates d))) * B := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (triadicRetainedCells_sum_weights_le hd w hs (triadicObservationPlanes N I k) J)
      (triadicDefectSup_nonneg z hr hD hN a hd (N + (J + 1)))

/-- A cut observation cube obeys the geometric convolution on the same original global grid. -/
theorem foldedObservation_defect_le_series (hd : 0 < d) (N : ℕ)
    (k : OddGridIndex d (triadicHalf N)) (I P : Finset (Fin d))
    (hk : k ∈ oddGridUnresolved (triadicHalf N) I)
    (g : C(closedCube z r hr, ℝ)) {p : Fin d → ℝ}
    (hp : (∑ i : Fin d, (p i)^2) = 1) :
    let w := oddGridCenter z r (triadicHalf N) k
    let s := r / (2 * (triadicHalf N : ℝ) + 1)
    let hs : 0 < s := div_pos hr (by positivity)
    let D := observation_killedPoincare z hr hD N k
    let V := observation_meanZeroPoincare z hr hN N k
    let I' := triadicObservationPlanes N I k
    let a := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) g)
    let af := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube w s hs)
      (closedCube z r hr) (g.comp (coordinateFoldOnCube z hr I P)))
    (∀ J,
      (triadicAdaptiveLabels I' J : Set (TriadicAdaptiveIndex d J)).PairwiseDisjoint
        (fun t => (triadicAdaptiveCell w s hs J t : Set (SpatialCoordinates d))) →
      ((⋃ t ∈ triadicAdaptiveLabels I' J,
        (triadicAdaptiveCell w s hs J t : Set (SpatialCoordinates d)))
        =ᵐ[volume] (centeredCube w s hs : Set (SpatialCoordinates d))) →
      affineDirichletResponse (centeredCube_isBounded w hs) (hD N k) af p ≤
        ∑ t ∈ triadicAdaptiveLabels I' J,
          affineDirichletResponse (triadicAdaptiveCell_isBounded w hs J t)
            (triadicAdaptiveCell_killedPoincare w hs D J t)
            (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root w hs J t) af) p) →
    (∀ J,
      (triadicAdaptiveLabels I' J : Set (TriadicAdaptiveIndex d J)).PairwiseDisjoint
        (fun t => (triadicAdaptiveCell w s hs J t : Set (SpatialCoordinates d))) →
      ((⋃ t ∈ triadicAdaptiveLabels I' J,
        (triadicAdaptiveCell w s hs J t : Set (SpatialCoordinates d)))
        =ᵐ[volume] (centeredCube w s hs : Set (SpatialCoordinates d))) →
      affineInverseNeumannResponse (hN N k) af p ≤
        ∑ t ∈ triadicAdaptiveLabels I' J,
          affineInverseNeumannResponse (triadicAdaptiveCell_meanZeroPoincare w hs V J t)
            (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root w hs J t) af) p) →
    affineDiagonalDefect (centeredCube_isBounded w hs) (centeredCube_volume_pos w hs)
      (hD N k) (hN N k) af p ≤
      ∑' j : ℕ, ((d : ℝ) / (3 : ℝ)^j) * triadicDefectSup z hr hD hN a hd (N + (j + 1)) := by
  intro w s hs D V I' a af hDir hNeu
  have hI : I'.Nonempty := (triadicObservationPlanes_nonempty_iff N I k).mpr hk
  let b := fun j : ℕ => ((d : ℝ) / (3 : ℝ)^j) * triadicDefectSup z hr hD hN a hd (N + (j + 1))
  let R := triadicResponseResidual w hs D V
    (fun n l => positiveCoefficientRestrict (oddGridCell_subset w hs (triadicHalf n) l) af)
    I' (fun _ _ => p)
  have hfinite : ∀ J, affineDiagonalDefect (centeredCube_isBounded w hs)
      (centeredCube_volume_pos w hs) (hD N k) (hN N k) af p ≤
      (∑ j ∈ Finset.range J, b j) + R J := by
    intro J
    have hpart := affineDiagonalDefect_triadicPartition w hs (hD N k) (hN N k) D V hI J af p
      (hDir J (triadicAdaptiveCells_pairwiseDisjoint w hs I' J)
        (triadicAdaptiveCells_union_ae_eq w hs hI J))
      (hNeu J (triadicAdaptiveCells_pairwiseDisjoint w hs I' J)
        (triadicAdaptiveCells_union_ae_eq w hs hI J))
    refine hpart.trans (add_le_add ?_ (le_refl (R J)))
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_le_sum
    intro j _
    exact foldedObservationRetained_sum_le z hr hD hN hd N k I P g hp j.val
  have hsum : Summable b := triadicDefectSup_shift_summable z hr hD hN a hd N
  have hR : Tendsto R atTop (𝓝 0) :=
    restrictedTriadicResponseResidual_tendsto_zero w hs hd D V af I' (fun _ _ => hp)
  have hlim := hsum.hasSum.tendsto_sum_nat.add hR
  simpa only [add_zero] using ge_of_tendsto' hlim hfinite

end SubdiffusiveProcess
