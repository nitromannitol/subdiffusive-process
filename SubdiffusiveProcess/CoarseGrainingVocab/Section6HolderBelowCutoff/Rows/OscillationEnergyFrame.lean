module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.OscillationEnergyGoodScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.OscillationEnergyGoodScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorTransport

@[expose] public section

/-!
# Row 2's `hO` leg in the original frame

`OscillationEnergyGoodScale.exists_interiorOscillationEnergyGoodScale_cut` is stated
in the *anchored* frame: the cube is `originCube d (n-2)` and the sample is
translated by the comparison centre `y`.  That is the frame in which the
harmonic-approximation argument proves its ellipticity transport, but the frozen row
lives in the original frame, on the translated window `y + cu_{n-2}`.

Untranslating is exact — Lebesgue measure is translation invariant — so nothing
is lost.  The three transports used are

* `H1Function.untranslate`, whose value and gradient are the precompositions
  (`untranslate_toFun`, `untranslate_grad`);
* `Section6HarmonicApproximation.normalizedL2On_translateSet`;
* `Section6Covariance.aCutoff_translatePotentialSample`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization hiding Vec
open Homogenization.Book

noncomputable section

variable {d : ℕ}
variable {L : ℕ}

/-- Untranslating the scale-normalized oscillation. -/
theorem normalizedL2On_fluctuation_untranslate_cut (Q : TriadicCube d) (y : Vec d)
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
theorem vectorNormalizedL2On_weightedGrad_untranslate_cut
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (y : Vec d)
    (v : H1Function (translateSet y (openCubeSet Q))) :
    vectorNormalizedL2On (openCubeSet Q)
        (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L
          (translatePotentialSample y omega) p) •
            (H1Function.untranslate y v).grad p) =
      vectorNormalizedL2On (translateSet y (openCubeSet Q))
        (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) •
          v.grad p) := by
  unfold vectorNormalizedL2On
  rw [normalizedL2On_translateSet]
  congr 1

/-- **Row 2's oscillation leg on a good scale, in the original frame.** -/
theorem exists_interiorOscillationEnergyFrame_cut (d : ℕ) [NeZero d] :
    ∃ Kosc : ℝ, 0 ≤ Kosc ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ,
      ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, ∀ y z : Vec d,
        translateSet (y - z) (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
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
              (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) •
                v.grad p) := by
  obtain ⟨Kosc, hKosc0, hleg⟩ := exists_interiorOscillationEnergyGoodScale_cut d
  refine ⟨Kosc, hKosc0, ?_⟩
  intro M s hs L n omega y z hcontain hgoodEvent v
  have h := hleg M s hs L n omega y z hcontain hgoodEvent
    (H1Function.untranslate y v)
  rwa [normalizedL2On_fluctuation_untranslate_cut (originCube d ((n : ℤ) - 2)) y v,
    vectorNormalizedL2On_weightedGrad_untranslate_cut M L omega
      (originCube d ((n : ℤ) - 2)) y v] at h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
