import SubdiffusiveProcess.Frozen.Section6.IterationLemma
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.ScaledPoincare
import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.LiteralSupMeasurability
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.SandwichNondegeneracyAttainment

/-!
# Theta-perturbed ladder: iteration on concentric translated cubes

The ordinary Holder ladder uses truncated cubes because it must handle the
boundary of a Dirichlet problem.  The bounded-multiplier application is
interior and homogeneous.  Its natural carrier is therefore the simpler
family of concentric translated cubes.  This file specializes the proved
abstract iteration lemma to that family, including affine-minimum attainment.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem translatedCube_mono_same_center {d : ℕ} {a b : ℤ}
    (hab : a ≤ b) (z : Vec d) :
    translatedCube d a z ⊆ translatedCube d b z := by
  rintro p ⟨q, hq, rfl⟩
  exact ⟨q, cube_subset_cube_of_le hab hq, rfl⟩

/-- The proved iteration lemma on the concentric family
`U_j = z + cube_j`. -/
theorem translatedCube_iteration (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 0 < h → ∀ theta ∈ Set.Ioo (0 : ℝ) 1,
      theta ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5) →
      ∀ n m : ℤ, n < m → ∀ z : Vec d,
      ∀ u : H1Function (translatedCube d m z),
      ∀ bad : Finset ℤ, bad ⊆ Finset.Icc n m →
      ∀ epsilon defect : ℤ → ℝ,
        (∀ j ∈ Finset.Icc n m, 0 ≤ epsilon j ∧ 0 ≤ defect j) →
        (∀ j ∈ Finset.Icc n m, j ∉ bad →
          ∀ ell : Affine d,
            ell ∈ affineMinimizers (translatedCube d j z) u.toFun →
            excess (j - h) (translatedCube d (j - h) z) u.toFun ≤
              theta ^ h * excess j (translatedCube d j z) u.toFun +
                epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) →
        let A := C * (h + 1) * (bad.card + 1) +
          C * ∑ j ∈ Finset.Icc n m, epsilon j
        (3 : ℝ) ^ (-n) *
            normalizedL2On (translatedCube d n z)
              (fun x ↦ u.toFun x -
                averageOn (translatedCube d n z) u.toFun) ≤
          Real.exp A *
            ((3 : ℝ) ^ (-m) *
              normalizedL2On (translatedCube d m z)
                (fun x ↦ u.toFun x -
                  averageOn (translatedCube d m z) u.toFun) +
              ∑ j ∈ Finset.Icc n m, defect j) ∧
        ∀ R : ℝ, 0 ≤ R →
          (∀ j ∈ Finset.Icc n m, epsilon j ≤ R) →
          excess n (translatedCube d n z) u.toFun ≤
            theta ^ (-C * (h + 1) * (bad.card + 1)) * Real.exp A *
              (theta ^ (m - n) *
                  excess m (translatedCube d m z) u.toFun +
                R * (3 : ℝ) ^ (-m) *
                  normalizedL2On (translatedCube d m z)
                    (fun x ↦ u.toFun x -
                      averageOn (translatedCube d m z) u.toFun) +
                (1 + R) * ∑ j ∈ Finset.Icc n m, defect j) := by
  obtain ⟨C, hC, hiter⟩ := SubdiffusiveProcess.Frozen.Section6.iteration_lemma d
  refine ⟨C, hC, ?_⟩
  intro h hh theta htheta hthetah n m hnm z u bad hbad epsilon defect
    hnonneg hrec A
  let U : ℤ → Set (Vec d) := fun j ↦ translatedCube d j z
  have hUmb : ∀ j, MeasurableSet (U j) ∧ Bornology.IsBounded (U j) := by
    intro j
    exact ⟨(Section6CutoffRegularity.isOpen_translatedCube d j z).measurableSet,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.isBounded_translatedCube d j z⟩
  have hnest : ∀ j ≤ m, U (j - 1) ⊆ U j := by
    intro j _
    exact translatedCube_mono_same_center (by omega) z
  have hsand : ∀ j ≤ m, ∃ x y : Vec d,
      translatedCube d (j - 2) x ⊆ U j ∧ U j ⊆ translatedCube d j y := by
    intro j _
    exact ⟨z, z, translatedCube_mono_same_center (by omega) z, Set.Subset.rfl⟩
  have huTop : MemLp u.toFun 2 (volume.restrict (U m)) := u.memL2
  have huAll : ∀ j ≤ m, MemLp u.toFun 2 (volume.restrict (U j)) := by
    intro j hj
    exact u.memL2.mono_measure
      (Measure.restrict_mono (translatedCube_mono_same_center hj z) le_rfl)
  have hexists : ∀ j ≤ m,
      ∃ ell : Affine d, ell ∈ affineMinimizers (U j) u.toFun := by
    intro j hj
    have hWm : MeasurableSet (U j) :=
      (Section6CutoffRegularity.isOpen_translatedCube d j z).measurableSet
    have hcube : U j =
        axisCube (Section6BoundaryL2.cubeCorner j z) ((3 : ℝ) ^ j) :=
      Section6BoundaryL2.translatedCube_eq_axisCube d j z
    obtain ⟨c, g, hcg⟩ :=
      Section6Iteration.exists_isAffineMinimizer_of_axisCubeSandwich
        (zpow_pos (by norm_num : (0 : ℝ) < 3) j)
        (zpow_pos (by norm_num : (0 : ℝ) < 3) j) hWm
        (by rw [hcube]) (by rw [hcube]) u.toFun (huAll j hj)
    exact ⟨⟨c, g⟩, Section6Iteration.mem_affineMinimizers_iff.2 hcg⟩
  let fit : ℤ → Affine d := fun j ↦
    if hj : j ≤ m then Classical.choose (hexists j hj) else ⟨0, 0⟩
  have hfit : ∀ j ≤ m, fit j ∈ affineMinimizers (U j) u.toFun := by
    intro j hj
    simpa only [fit, dif_pos hj] using Classical.choose_spec (hexists j hj)
  exact hiter h hh theta htheta hthetah n m hnm U hUmb hnest hsand
    u.toFun huTop bad hbad epsilon defect hnonneg fit hfit
    (fun j hj hnot ↦ hrec j hj hnot (fit j)
      (hfit j (Finset.mem_Icc.1 hj).2))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
