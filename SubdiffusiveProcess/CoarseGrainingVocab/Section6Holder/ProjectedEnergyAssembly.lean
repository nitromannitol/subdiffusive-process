module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ProjectedCoverReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCellCollapsed
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAdaptiveCellReadout

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch01 Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

variable {d : ℕ} [NeZero d]



theorem exists_holderProjectedEnergy_le_sqrt_max_of_boundaryCells
    (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
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
                SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
                  vecNormSq (u.grad p)) ≤ Bboundary) →
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        vectorNormalizedL2On
            (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
            (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
              u.grad p) ≤
          Real.sqrt ((81 : ℝ) ^ d * max
            (K * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                  normalizedL2On U
                    (fun p ↦ u.toFun p - averageOn U u.toFun) ^ 2 +
                Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                  Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                  (fractionalSeminormOn U sOrder.1 g).toReal ^ 2))
            Bboundary) := by
  obtain ⟨K, hK, hinteriorCell⟩ := exists_interiorCellEnergy_le_manuscriptPrices d
  refine ⟨K, hK, ?_⟩
  intro M sOrder hs L m n hmL hnm z x omega hz hx hgood u h g hdir hg hh
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
    have hcell := hinteriorCell M sOrder hs L m n hmL hnm z x q omega hz hx hq
      hpatch hgood u h g hdir hg hh
    simpa only [Binterior, U, sigma, sub_sub] using! hcell
  · exact hboundary



theorem exists_holderProjectedEnergy_le_of_boundaryAdaptiveBudget
    (d : ℕ) [NeZero d] :
    ∃ K C B : ℝ, 0 < K ∧ 0 < C ∧ 0 < B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad →
        MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
      ∀ Bboundary : ℝ,
        (∀ q,
          q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
          ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
          ∀ (g0 : Vec d → Vec d)
            (u0 h0 : H1Function (openCubeSet (originCube d ((n : ℤ) - 2)))),
            (∀ y, g0 y = g (y + Section6ExcessDecay.wellPlacedCentre
              q (m : ℤ) ((n : ℤ) - 2))) →
            (∀ y, u0.grad y = u.grad (y + Section6ExcessDecay.wellPlacedCentre
              q (m : ℤ) ((n : ℤ) - 2))) →
            (∀ y, h0.grad y = h.grad (y + Section6ExcessDecay.wellPlacedCentre
              q (m : ℤ) ((n : ℤ) - 2))) →
            let Q := originCube d ((n : ℤ) - 2)
            let sigma := tailAverage M L (n + 2) omega
              (translatedCube d ((n : ℤ) + 2) z)
            let BE := cubeAverage Q (coefficientEnergyDensity
              (publicCoeffField Q
                (aCutoffFamily M L (translatePotentialSample
                  (Section6ExcessDecay.wellPlacedCentre
                    q (m : ℤ) ((n : ℤ) - 2)) omega))) h0.grad)
            let Ag := sigma⁻¹ *
              (1 + Section6Localization.subunitCollapseConstant d *
                Section6Localization.subunitEnvelope (sOrder.1 / 8) (n + 2) *
                Section6Localization.subunitDeviation M (n + 2)
                  (translatePotentialSample z omega)) *
              (Fintype.card (Fin d) : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q
                (sOrder.1 / 3) g0 ^ 2
            ((81 : ℝ) ^ d * (18 : ℝ) ^ d) *
                (((5 / 2 : ℝ) * BE +
                    boundaryCommonGapPowerBudget Q sOrder.1 sigma B C BE
                      (fun y ↦ u0.toFun y - h0.toFun y)
                      (fun y ↦ -(cubeFluctuationVec Q g0 y)) +
                    (5 / 2 : ℝ) * Ag) *
                  coarseCaccioppoliRadiusIterationConst 8) ≤ Bboundary) →
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        vectorNormalizedL2On
            (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
            (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
              u.grad p) ≤
          Real.sqrt ((81 : ℝ) ^ d * max
            (K * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
                  normalizedL2On U
                    (fun p ↦ u.toFun p - averageOn U u.toFun) ^ 2 +
                Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
                  Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
                  (fractionalSeminormOn U sOrder.1 g).toReal ^ 2))
            Bboundary) := by
  obtain ⟨K, hK, hcover⟩ := exists_holderProjectedEnergy_le_sqrt_max_of_boundaryCells d
  obtain ⟨C, B, hC, hB, hcell⟩ :=
    exists_projectedBoundaryCellEnergy_le_adaptiveBudget d
  refine ⟨K, C, B, hK, hC, hB, ?_⟩
  intro M sOrder hs L m n hmL hnm z x omega hz hx hgood u h g hdir hg hh hfrac
    Bboundary hprice
  apply hcover M sOrder hs L m n hmL hnm z x omega hz hx hgood u h g hdir hg hh
    Bboundary
  intro q hq hpatch
  obtain ⟨g0, u0, h0, hg0, hu0, hh0, henergy⟩ :=
    hcell M sOrder.1 hs sOrder rfl L m n hmL hnm z x q omega hx hq hgood
      u h g hdir hg hfrac
  simpa only [sub_sub] using!
    henergy.trans (hprice q hq hpatch g0 u0 h0 hg0 hu0 hh0)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
