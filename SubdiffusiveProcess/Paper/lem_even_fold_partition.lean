module

public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMeanControlCore

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

noncomputable section
namespace Paper

/-- The finite reflected-copy partition used by the even-extension construction,
paper 847--862.  The pieces are the reflected copies of the original cube;
they cover the folded cube away from the separating coordinate faces, and the
fold agrees with the appropriate coordinate reflection on each piece.
The final null-set assertion records the separating faces explicitly.
-/
theorem lem_even_fold_partition
  (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
  (I P : Finset (Fin d)) :
  ∃ pieces : Finset (Fin d) → Set (SpatialCoordinates d),
    (∀ J : Finset (Fin d), J ⊆ I →
      pieces J = coordinateReflection (foldedCubeCenter w r I P) J ⁻¹'
        (centeredCube w r hr : Set (SpatialCoordinates d))) ∧
    (∀ J : Finset (Fin d), J ⊆ I → MeasurableSet (pieces J)) ∧
    (∀ x : SpatialCoordinates d,
      x ∈ (foldedCube w r hr I P : Set (SpatialCoordinates d)) →
      (∀ j : Fin d, j ∈ I → x j ≠ foldedCubeCenter w r I P j) →
      ∃ J : Finset (Fin d), J ⊆ I ∧ x ∈ pieces J ∧
        coordinateFold (foldedCubeCenter w r I P) I P x =
          coordinateReflection (foldedCubeCenter w r I P) J x) ∧
    volume {x : SpatialCoordinates d |
      x ∈ (foldedCube w r hr I P : Set (SpatialCoordinates d)) ∧
        ∃ j : Fin d, j ∈ I ∧ x j = foldedCubeCenter w r I P j} = 0 := by
  classical
  let z : SpatialCoordinates d := foldedCubeCenter w r I P
  refine ⟨fun J => coordinateReflection z J ⁻¹'
      (centeredCube w r hr : Set (SpatialCoordinates d)), ?_, ?_, ?_, ?_⟩
  · intro J hJ
    rfl
  · intro J hJ
    exact (centeredCube w r hr).isOpen.measurableSet.preimage
      (coordinateReflection_isometry z J).continuous.measurable
  · intro x hx hneq
    let J : Finset (Fin d) :=
      I.filter (fun j =>
        (j ∈ P ∧ z j < x j) ∨ (j ∉ P ∧ x j < z j))
    have hJI : J ⊆ I := by
      intro j hj
      exact (Finset.mem_filter.mp hj).1
    refine ⟨J, hJI, ?_, ?_⟩
    · change coordinateReflection z J x ∈
        (centeredCube w r hr : Set (SpatialCoordinates d))
      rw [centeredCube_eq_pi w hr]
      intro i hi
      have hx' := hx
      change x ∈ Set.pi Set.univ (fun j =>
        if j ∈ I then
          (if j ∈ P then Set.Ioo (w j - r / 2) (w j + 3 * r / 2)
          else Set.Ioo (w j - 3 * r / 2) (w j + r / 2))
        else Set.Ioo (w j - r / 2) (w j + r / 2)) at hx'
      have hxi := hx' i hi
      by_cases hI : i ∈ I
      · by_cases hP : i ∈ P
        · have hzi : z i = w i + r / 2 := by
            simp [z, foldedCubeCenter, hI, hP]
          have hne : x i ≠ z i := by
            simpa [z] using hneq i hI
          have hJmem : i ∈ J ↔ z i < x i := by
            simp [J, hI, hP]
          simp only [hI, hP, if_pos] at hxi
          change w i - r / 2 < x i ∧ x i < w i + 3 * r / 2 at hxi
          by_cases hside : z i < x i
          · rw [coordinateReflection, if_pos (hJmem.mpr hside)]
            change w i - r / 2 < 2 * z i - x i ∧
              2 * z i - x i < w i + r / 2
            rw [hzi]
            constructor <;> linarith [hxi.1, hxi.2, hside]
          · have hside' : x i < z i := lt_of_le_of_ne (le_of_not_gt hside) hne
            have hJnot : i ∉ J := fun h => hside (hJmem.mp h)
            rw [coordinateReflection, if_neg hJnot]
            change w i - r / 2 < x i ∧ x i < w i + r / 2
            rw [hzi] at hside'
            exact ⟨hxi.1, hside'⟩
        · have hzi : z i = w i - r / 2 := by
            simp [z, foldedCubeCenter, hI, hP]
          have hne : x i ≠ z i := by
            simpa [z] using hneq i hI
          have hJmem : i ∈ J ↔ x i < z i := by
            simp [J, hI, hP]
          simp only [hI, hP, if_pos, if_false] at hxi
          change w i - 3 * r / 2 < x i ∧ x i < w i + r / 2 at hxi
          by_cases hside : x i < z i
          · rw [coordinateReflection, if_pos (hJmem.mpr hside)]
            change w i - r / 2 < 2 * z i - x i ∧
              2 * z i - x i < w i + r / 2
            rw [hzi]
            constructor <;> linarith [hxi.1, hxi.2, hside]
          · have hside' : z i < x i := lt_of_le_of_ne (le_of_not_gt hside) hne.symm
            have hJnot : i ∉ J := fun h => hside (hJmem.mp h)
            rw [coordinateReflection, if_neg hJnot]
            change w i - r / 2 < x i ∧ x i < w i + r / 2
            rw [hzi] at hside'
            exact ⟨hside', hxi.2⟩
      · simp only [hI, if_false] at hxi
        rw [coordinateReflection, if_neg]
        · exact hxi
        · simp [J, hI]
    · funext i
      by_cases hI : i ∈ I
      · by_cases hP : i ∈ P
        · have hJmem : i ∈ J ↔ z i < x i := by
            simp [J, hI, hP]
          have hne : x i ≠ z i := by
            simpa [z] using hneq i hI
          by_cases hside : z i < x i
          · have hJ : i ∈ J := hJmem.mpr hside
            simp only [coordinateFold, coordinateReflection, hI, if_pos, hJ]
            change z i + coordinateReflectionSign P i * |x i - z i| = 2 * z i - x i
            rw [show coordinateReflectionSign P i = -1 by simp [coordinateReflectionSign, hP],
              abs_of_pos (sub_pos.mpr hside)]
            ring
          · have hJ : i ∉ J := fun h => hside (hJmem.mp h)
            have hside' : x i < z i := lt_of_le_of_ne (le_of_not_gt hside) hne
            simp only [coordinateFold, coordinateReflection, hI, if_pos, hJ]
            change z i + coordinateReflectionSign P i * |x i - z i| = x i
            rw [show coordinateReflectionSign P i = -1 by simp [coordinateReflectionSign, hP],
              abs_of_neg (sub_neg.mpr hside')]
            ring
        · have hJmem : i ∈ J ↔ x i < z i := by
            simp [J, hI, hP]
          have hne : x i ≠ z i := by
            simpa [z] using hneq i hI
          by_cases hside : x i < z i
          · have hJ : i ∈ J := hJmem.mpr hside
            simp only [coordinateFold, coordinateReflection, hI, if_pos, hJ]
            change z i + coordinateReflectionSign P i * |x i - z i| = 2 * z i - x i
            rw [show coordinateReflectionSign P i = 1 by simp [coordinateReflectionSign, hP],
              abs_of_neg (sub_neg.mpr hside)]
            ring
          · have hJ : i ∉ J := fun h => hside (hJmem.mp h)
            have hside' : z i < x i := lt_of_le_of_ne (le_of_not_gt hside) hne.symm
            simp only [coordinateFold, coordinateReflection, hI, if_pos, hJ]
            change z i + coordinateReflectionSign P i * |x i - z i| = x i
            rw [show coordinateReflectionSign P i = 1 by simp [coordinateReflectionSign, hP],
              abs_of_pos (sub_pos.mpr hside')]
            ring
      · have hJ : i ∉ J := by simp [J, hI]
        simp only [coordinateFold, coordinateReflection, hI, hJ, if_false]
  · have hplane : ∀ i : Fin d, ∀ c : ℝ,
        volume {x : SpatialCoordinates d | x i = c} = 0 := by
      intro i c
      exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.MeanControlSchauder.volume_coordHyperplane_eq_zero i c
    have hsubset : {x : SpatialCoordinates d |
        x ∈ (foldedCube w r hr I P : Set (SpatialCoordinates d)) ∧
          ∃ j : Fin d, j ∈ I ∧ x j = foldedCubeCenter w r I P j} ⊆
        ⋃ j : Fin d, {x : SpatialCoordinates d | x j = z j} := by
      intro x hx
      rcases hx.2 with ⟨j, hj, hxj⟩
      exact Set.mem_iUnion.2 ⟨j, hxj⟩
    apply measure_mono_null hsubset
    refine measure_iUnion_null (fun j => ?_)
    exact hplane j (z j)

end Paper
