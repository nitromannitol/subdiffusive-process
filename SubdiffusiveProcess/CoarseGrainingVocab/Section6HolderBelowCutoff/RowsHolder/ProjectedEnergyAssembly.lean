module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ProjectedCoverReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCellCollapsed
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAdaptiveCellReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffCellEnergy

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder

open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch01 Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

variable {d : ℕ} [NeZero d]
variable {L : ℕ}

/-- The mixed cover with its interior branch completely discharged.  The
remaining `hboundary` argument is exactly the uniform boundary-cell price;
it is an internal analytic composition, not a provider premise. -/
theorem exists_holderProjectedEnergy_le_sqrt_max_of_boundaryCells_cut
    (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad →
      ∀ Bboundary : ℝ,
        (∀ q,
          q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
          ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
          normalizedSetAverage
              (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
                _root_.SubdiffusiveProcess.Model.aCutoff M L omega p *
                  vecNormSq (u.grad p)) ≤ Bboundary) →
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        vectorNormalizedL2On
            (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
            (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) •
              u.grad p) ≤
          Real.sqrt ((81 : ℝ) ^ d * max
            (K * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                  normalizedL2On U
                    (fun p ↦ u.toFun p - averageOn U u.toFun) ^ 2 +
                Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                  Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                  (fractionalSeminormOn U sOrder.1 g).toReal ^ 2))
            Bboundary) := by
  obtain ⟨K, hK, hinteriorCell⟩ := SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.exists_interiorCellEnergy_le_manuscriptPrices_datumCutoff d
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hnm z x omega hz hx hgood u h g hdir hg hh
    Bboundary hboundary
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
  apply vectorNormalizedL2On_truncatedCube_predFour_le_sqrt_max_of_cellBounds
    M L omega
    (Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx)
    (by omega) u Binterior Bboundary
  · intro q hq hpatch
    have hcell := hinteriorCell M sOrder hs L m n hnm z x q omega hz hx hq
      hpatch hgood u h g hdir hg hh
    simpa only [Binterior, U, sigma, sub_sub] using! hcell
  · exact hboundary

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder
