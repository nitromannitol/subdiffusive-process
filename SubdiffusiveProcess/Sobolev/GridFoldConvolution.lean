import SubdiffusiveProcess.Sobolev.ObservationConvolution

/-! # The original-grid maximum response convolution

Every observation label is handled: uncut cells use actual reflection
covariance, and cut cells use their local adaptive partition. M's two
finite-partition inequalities below refer only to actual restrictions of
one folded root coefficient. No reflection bound is a premise.
-/
open MeasureTheory Set TopologicalSpace
open scoped NNReal
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

/-- The literal original-grid defect supremum obeys the fold convolution at every observation depth. -/
theorem triadicDefectSup_fold_le_series (hd : 0 < d) (N : ℕ)
    (I P : Finset (Fin d)) (g : C(closedCube z r hr, ℝ)) :
    let a := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) g)
    let af := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) (g.comp (coordinateFoldOnCube z hr I P)))
    (∀ (k : OddGridIndex d (triadicHalf N)) (p : Fin d → ℝ),
      let w := oddGridCenter z r (triadicHalf N) k
      let s := r / (2 * (triadicHalf N : ℝ) + 1)
      let hs : 0 < s := div_pos hr (by positivity)
      let D := observation_killedPoincare z hr hD N k
      let V := observation_meanZeroPoincare z hr hN N k
      let I' := triadicObservationPlanes N I k
      let afU := positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf N) k) af
      ∀ J,
        (triadicAdaptiveLabels I' J : Set (TriadicAdaptiveIndex d J)).PairwiseDisjoint
          (fun t => (triadicAdaptiveCell w s hs J t : Set (SpatialCoordinates d))) →
        ((⋃ t ∈ triadicAdaptiveLabels I' J,
          (triadicAdaptiveCell w s hs J t : Set (SpatialCoordinates d)))
          =ᵐ[volume] (centeredCube w s hs : Set (SpatialCoordinates d))) →
        (affineDirichletResponse (centeredCube_isBounded w hs) (hD N k) afU p ≤
          ∑ t ∈ triadicAdaptiveLabels I' J,
            affineDirichletResponse (triadicAdaptiveCell_isBounded w hs J t)
              (triadicAdaptiveCell_killedPoincare w hs D J t)
              (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root w hs J t) afU) p) ∧
        (affineInverseNeumannResponse (hN N k) afU p ≤
          ∑ t ∈ triadicAdaptiveLabels I' J,
            affineInverseNeumannResponse (triadicAdaptiveCell_meanZeroPoincare w hs V J t)
              (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root w hs J t) afU) p)) →
    triadicDefectSup z hr hD hN af hd N ≤
      triadicDefectSup z hr hD hN a hd N +
        ∑' j : ℕ, ((d : ℝ) / (3 : ℝ)^j) * triadicDefectSup z hr hD hN a hd (N + (j + 1)) := by
  intro a af hSub
  apply (triadicDefectSup_isLUB z hr hD hN af hd N).2
  intro y hy
  obtain ⟨k, p, hp, rfl⟩ := hy
  by_cases hk : k ∈ oddGridUnresolved (triadicHalf N) I
  · have hcut := foldedObservation_defect_le_series z hr hD hN hd N k I P hk g hp
    have he : affineDiagonalDefect (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
        (hD N k) (hN N k)
        (positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf N) k) af) p ≤
        ∑' j : ℕ, ((d : ℝ) / (3 : ℝ)^j) * triadicDefectSup z hr hD hN a hd (N + (j + 1)) := by
      rw [positiveCoefficientRestrict_compactPotential]
      apply hcut
      · intro J hdisj hcover
        simpa only [af, positiveCoefficientRestrict_compactPotential] using
          (hSub k p J hdisj hcover).1
      · intro J hdisj hcover
        simpa only [af, positiveCoefficientRestrict_compactPotential] using
          (hSub k p J hdisj hcover).2
    exact he.trans (le_add_of_nonneg_left (triadicDefectSup_nonneg z hr hD hN a hd N))
  · rw [affineDiagonalDefect_fold_cell z hr (hD N) (hN N) I P k hk]
    have he := le_triadicDefectSup z hr hD hN a hd N
      (oddGridReflect (oddGridFoldReflections I P k) k)
      (p := coordinateReflectionDerivative (oddGridFoldReflections I P k) p)
      (by simpa only [coordinateReflectionDerivative_sum_sq] using hp)
    have hseries : 0 ≤ ∑' j : ℕ, ((d : ℝ) / (3 : ℝ)^j) *
        triadicDefectSup z hr hD hN a hd (N + (j + 1)) :=
      tsum_nonneg fun j => mul_nonneg (by positivity)
        (triadicDefectSup_nonneg z hr hD hN a hd (N + (j + 1)))
    exact he.trans (le_add_of_nonneg_right hseries)

/-- With no active plane, compact-root potential composition is exactly the original potential. -/
theorem compactPotential_comp_emptyFold (P : Finset (Fin d))
    (g : C(closedCube z r hr, ℝ)) :
    g.comp (coordinateFoldOnCube z hr ∅ P) = g := by
  ext x
  change g (coordinateFoldOnCube z hr ∅ P x) = g x
  congr 1

/-- The empty-fold case preserves the actual grid supremum without a convolution term. -/
theorem triadicDefectSup_fold_empty (hd : 0 < d) (N : ℕ) (P : Finset (Fin d))
    (g : C(closedCube z r hr, ℝ)) :
    triadicDefectSup z hr hD hN
      (expPotentialCoefficient (compactPotentialLp (closedCube z r hr)
        (g.comp (coordinateFoldOnCube z hr ∅ P)))) hd N =
      triadicDefectSup z hr hD hN
        (expPotentialCoefficient (compactPotentialLp (closedCube z r hr) g)) hd N := by
  rw [compactPotential_comp_emptyFold]

end SubdiffusiveProcess
