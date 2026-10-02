import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EllipticityCap




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization hiding Vec
open Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- **Row 2's oscillation leg on a good scale.**  Deterministic constant; the
only sample-dependence is the good-event hypothesis. -/
theorem exists_interiorOscillationEnergyGoodScale (d : ℕ) [NeZero d] :
    ∃ Kosc : ℝ, 0 ≤ Kosc ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, n + 2 ≤ L →
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d, ∀ y z : Vec d,
        translateSet (y - z) (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
      ∀ u : H1Function (openCubeSet (originCube d ((n : ℤ) - 2))),
        Real.sqrt
            (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z)) *
            (cubeBesovScaleWeight (1 : ℝ) (originCube d ((n : ℤ) - 2)) *
              normalizedL2On (openCubeSet (originCube d ((n : ℤ) - 2)))
                (fun p ↦ u.toFun p -
                  volumeAverage (openCubeSet (originCube d ((n : ℤ) - 2)))
                    u.toFun)) ≤
          Kosc *
            vectorNormalizedL2On (openCubeSet (originCube d ((n : ℤ) - 2)))
              (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
                (translatePotentialSample y omega) p) • u.grad p) := by
  obtain ⟨Kell, hKell0, hcap⟩ := exists_interiorEllipticityCap d
  refine ⟨interiorOscEnergyConst d * Real.sqrt Kell,
    mul_nonneg (interiorOscEnergyConst_nonneg d) (Real.sqrt_nonneg _), ?_⟩
  intro M s hs L n hnL omega y z hcontain hgoodEvent u
  have hsigma0 : 0 ≤
      tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z) :=
    Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _
  have hmain := sqrt_mul_oscillation_le_weightedEnergy
    (originCube d ((n : ℤ) - 2)) M L (translatePotentialSample y omega)
    (sigma := tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z))
    (K := Kell) hsigma0
    (hcap M s hs L n hnL omega y z hcontain hgoodEvent) u
  simpa only [mul_assoc] using hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
