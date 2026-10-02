import SubdiffusiveProcess.Frozen.Section6.IterationLemma
import SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.ComposeGlue

/-!
# Hölder Step 4: iteration on truncated cubes

This is the geometry adapter between the proved abstract iteration lemma and
the manuscript family `U_j = (z + cube_j) ∩ cube_m`.  Measurability,
boundedness, nesting, the cube sandwich, `L²` restriction, and attainment of
every affine minimum are all discharged here.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

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

/-- The proved iteration lemma, specialized to the actual truncated windows.
The recurrence is required for every minimizing affine map, allowing this
adapter to choose minimizers internally. -/
theorem truncatedCube_iteration (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 0 < h → ∀ theta ∈ Set.Ioo (0 : ℝ) 1,
      theta ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5) →
      ∀ domain n m : ℕ, n < m → m ≤ domain →
      ∀ z ∈ cube d domain,
      ∀ u : H1Function (openCubeSet (originCube d domain)),
      ∀ bad : Finset ℤ, bad ⊆ Finset.Icc (n : ℤ) (m : ℤ) →
      ∀ epsilon defect : ℤ → ℝ,
        (∀ j ∈ Finset.Icc (n : ℤ) (m : ℤ),
          0 ≤ epsilon j ∧ 0 ≤ defect j) →
        (∀ j ∈ Finset.Icc (n : ℤ) (m : ℤ), j ∉ bad →
          ∀ ell : Affine d,
            ell ∈ affineMinimizers (truncatedCube d domain j z) u.toFun →
            excess (j - h) (truncatedCube d domain (j - h) z) u.toFun ≤
              theta ^ h * excess j (truncatedCube d domain j z) u.toFun +
                epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) →
        let A := C * (h + 1) * (bad.card + 1) +
          C * ∑ j ∈ Finset.Icc (n : ℤ) (m : ℤ), epsilon j
        (3 : ℝ) ^ (-(n : ℤ)) *
            normalizedL2On (truncatedCube d domain n z)
              (fun x ↦ u.toFun x - averageOn (truncatedCube d domain n z) u.toFun) ≤
          Real.exp A *
            ((3 : ℝ) ^ (-(m : ℤ)) *
                normalizedL2On (truncatedCube d domain m z)
                  (fun x ↦ u.toFun x - averageOn
                    (truncatedCube d domain m z) u.toFun) +
              ∑ j ∈ Finset.Icc (n : ℤ) (m : ℤ), defect j) ∧
        ∀ R : ℝ, 0 ≤ R →
          (∀ j ∈ Finset.Icc (n : ℤ) (m : ℤ), epsilon j ≤ R) →
          excess n (truncatedCube d domain n z) u.toFun ≤
            theta ^ (-C * (h + 1) * (bad.card + 1)) * Real.exp A *
              (theta ^ ((m : ℤ) - (n : ℤ)) *
                  excess m (truncatedCube d domain m z) u.toFun +
                R * (3 : ℝ) ^ (-(m : ℤ)) *
                  normalizedL2On (truncatedCube d domain m z)
                    (fun x ↦ u.toFun x - averageOn
                      (truncatedCube d domain m z) u.toFun) +
                (1 + R) * ∑ j ∈ Finset.Icc (n : ℤ) (m : ℤ), defect j) := by
  obtain ⟨C, hC, hiter⟩ := SubdiffusiveProcess.Frozen.Section6.iteration_lemma d
  refine ⟨C, hC, ?_⟩
  intro h hh theta htheta hthetah domain n m hnm hmd z hz u bad hbad epsilon defect
    hnonneg hrec A
  let U : ℤ → Set (Vec d) := fun j ↦ truncatedCube d domain j z
  have hUmb : ∀ j, MeasurableSet (U j) ∧ Bornology.IsBounded (U j) := by
    intro j
    exact ⟨measurableSet_truncatedCube d domain j z,
      (isOpenBoundedConvexDomain_truncatedCube d domain j z).isBoundedDomain.isBounded⟩
  have hnest : ∀ j ≤ (m : ℤ), U (j - 1) ⊆ U j := by
    intro j _
    exact truncatedCube_mono d domain z (by omega)
  have hsand : ∀ j ≤ (m : ℤ), ∃ x y : Vec d,
      translatedCube d (j - 2) x ⊆ U j ∧ U j ⊆ translatedCube d j y := by
    intro j hj
    let x := wellPlacedCentre z domain (j - 1)
    refine ⟨x, z, ?_, truncatedCube_subset_translatedCube d domain j z⟩
    exact (translatedCube_mono_same_center (by omega) x).trans
      (translatedCube_wellPlacedCentre_subset_truncatedCube z hz (by omega))
  have huTop : MemLp u.toFun 2 (volume.restrict (U (m : ℤ))) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedCube_subset_cube d domain m z) le_rfl)
  have huAll : ∀ j ≤ (m : ℤ),
      MemLp u.toFun 2 (volume.restrict (U j)) := by
    intro j hj
    exact u.memL2.mono_measure
      (Measure.restrict_mono (truncatedCube_subset_cube d domain j z) le_rfl)
  have hexists : ∀ j ≤ (m : ℤ),
      ∃ ell : Affine d, ell ∈ affineMinimizers (U j) u.toFun := by
    intro j hj
    obtain ⟨c, g, hcg⟩ :=
      Section6OddClass.exists_isAffineMinimizer_truncatedWindow hz (by omega) (huAll j hj)
    exact ⟨⟨c, g⟩, Section6Iteration.mem_affineMinimizers_iff.2 hcg⟩
  let fit : ℤ → Affine d := fun j ↦
    if hj : j ≤ (m : ℤ) then Classical.choose (hexists j hj) else ⟨0, 0⟩
  have hfit : ∀ j ≤ (m : ℤ), fit j ∈ affineMinimizers (U j) u.toFun := by
    intro j hj
    simpa only [fit, dif_pos hj] using Classical.choose_spec (hexists j hj)
  exact hiter h hh theta htheta hthetah (n : ℤ) (m : ℤ) (by exact_mod_cast hnm)
    U hUmb hnest hsand u.toFun huTop bad hbad epsilon defect hnonneg fit hfit
    (fun j hj hnot ↦ hrec j hj hnot (fit j) (hfit j (Finset.mem_Icc.1 hj).2))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
