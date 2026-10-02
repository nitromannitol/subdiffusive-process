import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoEnergyCover

/-!
# Interior Step 6 with the cell-interiority as an explicit hypothesis

`EnergyCover.exists_interiorHolderProjectedEnergy` states its interiority as
`z ∈ cube d (m-1)`.  That is **too strong for the grid neighbours** of an
interior base point: a neighbour sits up to `3^j` away from `x`, so its sup-norm
can reach `3^{m-1}(1/2 + 1/81)` and it need not lie in `cube d (m-1)` at all.

What the proof actually uses is only that the projected cover has no boundary
cell.  Carrying that directly — as `WindowMonotone.interiorGate_of_descendant`
supplies it for any descendant of an interior point — makes Step 6 applicable at
the neighbours.  The `z ∈ cube d (m-1)` version is the special case.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch01 Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **Step 6 on the interior branch, with the boundary-cell budget deleted.**
Compare `Section6Holder.exists_holderProjectedEnergy_le_sqrt_max_of_boundaryCells`:
there the conclusion carries `max Binterior Bboundary` and an unproved
`Bboundary`; here the cover has no boundary cell, so the estimate is the plain
interior budget. -/
theorem exists_interiorHolderProjectedEnergyGate (d : ℕ) [NeZero d]
    (hcell : InteriorCellEnergyInput d) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        (∀ q, q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
          openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ)) →
        omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        vectorNormalizedL2On
            (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
            (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
              u.grad p) ≤
          Real.sqrt ((81 : ℝ) ^ d *
            (K * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                  normalizedL2On U
                    (fun p ↦ u.toFun p - averageOn U u.toFun) ^ 2 +
                Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                  Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                  (fractionalSeminormOn U sOrder.1 g).toReal ^ 2))) := by
  obtain ⟨K, hK, hinteriorCell⟩ := hcell
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hmL hnm z x omega hz hx hnobc hgood u g hsol hg
  dsimp only
  let U := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  let Binterior := K *
    (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
        normalizedL2On U (fun p ↦ u.toFun p - averageOn U u.toFun) ^ 2 +
      Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
        (fractionalSeminormOn U sOrder.1 g).toReal ^ 2)
  have hmain := vectorNormalizedL2On_truncatedCube_predFour_le_sqrt_max_of_cellBounds
    M L omega (n := n)
    (Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx)
    (by omega) u Binterior Binterior
    (by
      intro q hq hpatch
      have hcell := hinteriorCell M sOrder hs L m n hmL hnm z x q omega hz hx hq
        hpatch hgood u g hsol hg
      simpa only [Binterior, U, sigma, sub_sub] using hcell)
    (by
      intro q hq hpatch
      exact absurd (hnobc q hq) hpatch)
  rw [max_self] at hmain
  simpa only [Binterior, U, sigma] using hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
