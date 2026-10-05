module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ProjectedCoverReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.InteriorWindows
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.ProjectedEnergyAssembly

@[expose] public section

/-!
# Interior Hölder Step 6: the projected energy cover, interior branch

The boundary Hölder argument's Step 6 splits the projected cover into interior and
boundary cells and stops at the boundary-cell budget.  **On the interior branch
there are no boundary cells at all**
(`InteriorWindows.openCubeAtScale_subset_cube_of_interior_descendant`), so the
cover readout runs with a one-sided budget and the `max` collapses by
`max_self`.

The cover readout itself
(`Section6Holder.vectorNormalizedL2On_truncatedCube_predFour_le_sqrt_max_of_cellBounds`)
is already datum-free and is used unchanged.  The only thing the interior argument
still needs from the harmonic-approximation argument is the *interior cell price*
without its unused datum binders; that shape is recorded here as
`InteriorCellEnergyInput_cut`, transcribed from
`Section6HarmonicApproximation.exists_interiorCellEnergy_le_manuscriptPrices`
with `(u h : H1Function …)`, `IsDirichletSolutionOn … u h g` and
`MemCubeEuclideanFullWsp … h.grad` replaced by `(u : H1Function …)` and
`IsDivFormWeakSolutionOn (aCutoff M L omega) (cube d m) u g`.  Nothing else is
changed, so the discharge from that statement is one `exact`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch01 Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

noncomputable section

variable {L : ℕ}
attribute [local instance] Classical.propDecidable

/-- The datum-free interior-cell energy price: exactly
`Section6HarmonicApproximation.exists_interiorCellEnergy_le_manuscriptPrices`
with the three unused datum binders dropped. -/
def InteriorCellEnergyInput_cut (d : ℕ) : Prop :=
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x q : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        let k : ℤ := (n : ℤ) - 2
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
            (fun y => _root_.SubdiffusiveProcess.Model.aCutoff M L omega y *
              vecNormSq (u.grad y)) ≤
          K *
            (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                normalizedL2On U
                  (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
              Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                (fractionalSeminormOn U sOrder.1 g).toReal ^ 2)

/-- **Step 6 on the interior branch, with the boundary-cell budget deleted.**
Compare `exists_holderProjectedEnergy_le_sqrt_max_of_boundaryCells_cut`:
there the conclusion carries `max Binterior Bboundary` and an explicit
`Bboundary` budget; here the cover has no boundary cell, so the estimate is the plain
interior budget. -/
theorem exists_interiorHolderProjectedEnergy_cut (d : ℕ) [NeZero d]
    (hcell : InteriorCellEnergyInput_cut d) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        z ∈ cube d ((m : ℤ) - 1) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        vectorNormalizedL2On
            (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
            (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) •
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
  intro M sOrder hs L m n hnm z x omega hzint hx hgood u g hsol hg
  dsimp only
  have hz : z ∈ cube d (m : ℤ) := mem_cube_of_mem_cube_sub_one hzint
  let U := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  let Binterior := K *
    (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
        normalizedL2On U (fun p ↦ u.toFun p - averageOn U u.toFun) ^ 2 +
      Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
        (fractionalSeminormOn U sOrder.1 g).toReal ^ 2)
  have hnobc : ∀ q, q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) := by
    intro q hq
    exact openCubeAtScale_subset_cube_of_interior_descendant (top := (n : ℤ))
      hzint hx (by omega) (by omega) hq
  have hmain := vectorNormalizedL2On_truncatedCube_predFour_le_sqrt_max_of_cellBounds
    M L omega (n := n)
    (Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx)
    (by omega) u Binterior Binterior
    (by
      intro q hq hpatch
      have hcell := hinteriorCell M sOrder hs L m n hnm z x q omega hz hx hq
        hpatch hgood u g hsol hg
      have hscale : (n : ℤ) - 2 - 2 = (n : ℤ) - 4 := by omega
      simpa only [Binterior, U, sigma, hscale] using hcell)
    (by
      intro q hq hpatch
      exact absurd (hnobc q hq) hpatch)
  rw [max_self] at hmain
  simpa only [Binterior, U, sigma] using hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
