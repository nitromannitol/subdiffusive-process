module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCoverAssembly

@[expose] public section

/-!
# Projected mixed interior/boundary cover

This is the exact finite geometric assembly used in the manuscript: each
depth-two descendant of the comparison cube is read as a physical
scale-`n-4` cell, its centre is projected into the scale-`n-2` parent, and the
cell is dispatched according to whether its scale-`n-3` patch remains in the
ambient cube.

PROVENANCE: mirrors the finite projected cover in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryAssemblyEnergy.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Exact mixed `9^d` cover with the physical projected-cell interface
exposed to the two analytic branches. -/
theorem normalizedCutoffEnergy_projectedCover_le_max
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {m : ℕ} {n : ℕ} {x y : Vec d}
    (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    (hD : translatedCube d ((n : ℤ) - 2) y ⊆
      truncatedCube d (m : ℤ) ((n : ℤ) - 1) x)
    (Binterior Bboundary : ℝ)
    (hinterior : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ Binterior)
    (hboundary : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ Bboundary) :
    normalizedSetAverage (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
      max Binterior Bboundary := by
  let k : ℤ := (n : ℤ) - 2
  have hparent : translatedCube d k y ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    intro p hp
    exact (hD (by simpa only [k] using! hp)).2
  apply normalizedCutoffEnergy_translatedCube_le_max_of_depthTwo_split
    M L omega u hparent
    (fun R ↦ openCubeAtScale (y + triadicCubeShift R) ((n : ℤ) - 3) ⊆
      cube d (m : ℤ)) Binterior Bboundary
  · intro R hR hpatch
    let q : Vec d := y + triadicCubeShift R
    have htranslate : translateSet y (openCubeSet (originCube d k)) =
        translatedCube d k y := by
      rw [translatedCube, cube,
        Section6SchauderDatum.image_add_eq_translateSet]
    have hq : q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x := by
      apply translated_descendantCentre_mem_of_parent_subset hR
      rw [htranslate]
      simpa only [k] using! hD
    have hset : translateSet y (openCubeSet R) =
        truncatedCube d (m : ℤ) ((n : ℤ) - 4) q := by
      have heq := translate_descendant_openCubeSet_eq_truncatedCube hR
        (by
          rw [htranslate]
          simpa only [cube] using! hparent)
      simpa only [k, sub_sub, sub_self, sub_zero] using! heq
    rw [hset]
    exact hinterior q hq hpatch
  · intro R hR hpatch
    let q : Vec d := y + triadicCubeShift R
    have htranslate : translateSet y (openCubeSet (originCube d k)) =
        translatedCube d k y := by
      rw [translatedCube, cube,
        Section6SchauderDatum.image_add_eq_translateSet]
    have hq : q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x := by
      apply translated_descendantCentre_mem_of_parent_subset hR
      rw [htranslate]
      simpa only [k] using! hD
    have hset : translateSet y (openCubeSet R) =
        truncatedCube d (m : ℤ) ((n : ℤ) - 4) q := by
      have heq := translate_descendant_openCubeSet_eq_truncatedCube hR
        (by
          rw [htranslate]
          simpa only [cube] using! hparent)
      simpa only [k, sub_sub, sub_self, sub_zero] using! heq
    rw [hset]
    exact hboundary q hq hpatch

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
