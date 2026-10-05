module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.EllipticityCap
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EllipticityCap

@[expose] public section

/-!
# Row 2's `hO` leg on a good scale, in the anchored frame

Composing

* `EllipticityPairing.sqrt_mul_oscillation_le_weightedEnergy` — the fractional
  Poincaré, the `q = 2` negative-Besov seam, the coarse-grained Poincaré estimate
  and the `b^{1/2} / b^{-1/2}` pairing, on an arbitrary triadic cube; and
* `EllipticityCap.exists_interiorEllipticityCap_cut` — the good-scale ellipticity
  comparison

gives `ss.good.scale.estimates` and `ss.regularity.iteration` in the anchored frame: on a good scale, the
tail average's square root times the scale-normalized oscillation of an arbitrary
`H¹` function is bounded by the weighted gradient energy, at a **dimension-only**
constant.

The frame is the translated one: the comparison cube `y + cu_{n-2}` of the
manuscript is `originCube d (n-2)` for the sample translated by `y`, which is the
frame in which the harmonic-approximation argument proves its ellipticity transport.
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

/-- **Row 2's oscillation leg on a good scale.**  Deterministic constant; the
only sample-dependence is the good-event hypothesis. -/
theorem exists_interiorOscillationEnergyGoodScale_cut (d : ℕ) [NeZero d] :
    ∃ Kosc : ℝ, 0 ≤ Kosc ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ,
      ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, ∀ y z : Vec d,
        translateSet (y - z) (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
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
              (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L
                (translatePotentialSample y omega) p) • u.grad p) := by
  obtain ⟨Kell, hKell0, hcap⟩ := exists_interiorEllipticityCap_cut d
  refine ⟨interiorOscEnergyConst d * Real.sqrt Kell,
    mul_nonneg (interiorOscEnergyConst_nonneg d) (Real.sqrt_nonneg _), ?_⟩
  intro M s hs L n omega y z hcontain hgoodEvent u
  have hsigma0 : 0 ≤
      tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z) :=
    Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _
  have hmain := sqrt_mul_oscillation_le_weightedEnergy
    (originCube d ((n : ℤ) - 2)) M L (translatePotentialSample y omega)
    (sigma := tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z))
    (K := Kell) hsigma0
    (hcap M s hs L n omega y z hcontain hgoodEvent) u
  simpa only [mul_assoc] using hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
