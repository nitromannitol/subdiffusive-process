import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.OscillationEnergyGoodScale
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorTransport




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization hiding Vec
open Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- Untranslating the scale-normalized oscillation. -/
theorem normalizedL2On_fluctuation_untranslate (Q : TriadicCube d) (y : Vec d)
    (v : H1Function (translateSet y (openCubeSet Q))) :
    normalizedL2On (openCubeSet Q)
        (fun p ↦ (H1Function.untranslate y v).toFun p -
          volumeAverage (openCubeSet Q) (H1Function.untranslate y v).toFun) =
      normalizedL2On (translateSet y (openCubeSet Q))
        (fun p ↦ v.toFun p -
          volumeAverage (translateSet y (openCubeSet Q)) v.toFun) := by
  have havg : volumeAverage (translateSet y (openCubeSet Q)) v.toFun =
      volumeAverage (openCubeSet Q) (H1Function.untranslate y v).toFun := by
    rw [Ch01.volumeAverage_translateSet_eq_comp_addRight]
    rfl
  rw [normalizedL2On_translateSet, havg]
  rfl

/-- Untranslating the weighted gradient energy. -/
theorem vectorNormalizedL2On_weightedGrad_untranslate
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (y : Vec d)
    (v : H1Function (translateSet y (openCubeSet Q))) :
    vectorNormalizedL2On (openCubeSet Q)
        (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
          (translatePotentialSample y omega) p) •
            (H1Function.untranslate y v).grad p) =
      vectorNormalizedL2On (translateSet y (openCubeSet Q))
        (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
          v.grad p) := by
  unfold vectorNormalizedL2On
  rw [normalizedL2On_translateSet]
  congr 1

/-- **Row 2's oscillation leg on a good scale, in the original frame.** -/
theorem exists_interiorOscillationEnergyFrame (d : ℕ) [NeZero d] :
    ∃ Kosc : ℝ, 0 ≤ Kosc ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, n + 2 ≤ L →
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d, ∀ y z : Vec d,
        translateSet (y - z) (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
      ∀ v : H1Function
          (translateSet y (openCubeSet (originCube d ((n : ℤ) - 2)))),
        Real.sqrt
            (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z)) *
            (cubeBesovScaleWeight (1 : ℝ) (originCube d ((n : ℤ) - 2)) *
              normalizedL2On
                (translateSet y (openCubeSet (originCube d ((n : ℤ) - 2))))
                (fun p ↦ v.toFun p -
                  volumeAverage
                    (translateSet y (openCubeSet (originCube d ((n : ℤ) - 2))))
                    v.toFun)) ≤
          Kosc *
            vectorNormalizedL2On
              (translateSet y (openCubeSet (originCube d ((n : ℤ) - 2))))
              (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
                v.grad p) := by
  obtain ⟨Kosc, hKosc0, hleg⟩ := exists_interiorOscillationEnergyGoodScale d
  refine ⟨Kosc, hKosc0, ?_⟩
  intro M s hs L n hnL omega y z hcontain hgoodEvent v
  have h := hleg M s hs L n hnL omega y z hcontain hgoodEvent
    (H1Function.untranslate y v)
  rwa [normalizedL2On_fluctuation_untranslate (originCube d ((n : ℤ) - 2)) y v,
    vectorNormalizedL2On_weightedGrad_untranslate M L omega
      (originCube d ((n : ℤ) - 2)) y v] at h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
