module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCube7a

@[expose] public section

/-!
# Clause 7a in the provider's event family

The local hull construction supplies the provider's exact layer-zero
measurability binders, without a measurability hypothesis on the raw analytic
predicate. Probability equality preserves the tail obligation. Pointwise
containment of the resulting good event preserves every analytic obligation.

The second theorem consumes the existing producers for clauses 7b, 7d, 7e,
and 7f. It changes neither the layer events nor any constants. The remaining
probability and analytic estimates of the full anchor are separate
obligations; this file does not promote that anchor.
-/

set_option autoImplicit false

open Homogenization hiding Vec
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The exact `E0` and `hE0meas` quantifier order used by
`weighted_good_cube_events_of_supportInputs`, together with the pointwise,
probability, and covariance guarantees needed by its other inputs. -/
theorem exists_layerZero_hull_family {d : ℕ} {C : ℝ} (hC : 0 < C)
    (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n C (0 : Lattice d) → ℝ)) :
    ∃ E0 : GMCModel d → ℕ → Lattice d → Set (PotentialSample d),
      (∀ M n z, MeasurableSet[restrictedCoefficientSigma (aCutoff M n)
        (nativeBox n C z)] (E0 M n z)) ∧
      (∀ M n z, coefficientLocalBadEvent M n C (bad M n) z ⊆ E0 M n z) ∧
      (∀ (M : GMCModel d) n z, M.P.toMeasure (E0 M n z) =
        M.P.toMeasure (coefficientLocalBadEvent M n C (bad M n) z)) ∧
      ∀ M n z a, E0 M n (z + a) =
        translatePotentialSequence (goodCubeCentre n a) ⁻¹' (E0 M n z) := by
  classical
  choose E0 hm hs hmu hcov using
    fun (M : GMCModel d) (n : ℕ) =>
      exists_coefficientLocalBadEvent_hull M n hC (bad M n)
  exact ⟨E0, hm, hs, hmu, hcov⟩

/-- Clauses 7a, 7b, 7d, 7e and 7f for a local analytic bad predicate, with
the same probability at every layer and all previous good-event consequences
retained pointwise. No measurability or tail premise on `bad` is required. -/
theorem exists_goodCubeEventField_local_hull {d : ℕ} [NeZero d]
    (M : GMCModel d) (n : ℕ) {C eps1 : ℝ} {Cdep : ℕ} (hC : 0 < C)
    (hdep : C + Real.sqrt (d : ℝ) ≤ (Cdep : ℝ))
    (bad : Set (nativeBox n C (0 : Lattice d) → ℝ)) :
    ∃ E : ℕ → Lattice d → Set (PotentialSample d),
      (∀ z, MeasurableSet[restrictedCoefficientSigma (aCutoff M n)
        (nativeBox n C z)] (E 0 z)) ∧
      (∀ j, 1 ≤ j → ∀ z, MeasurableSet[shellLocalSigma (n + j)
        (layerBox n j C z)] (E j z)) ∧
      IndependentEventScales M.P.toMeasure E ∧
      MultiscaleFiniteRangeIndependentEvents M.P.toMeasure (fun j => Cdep * 3 ^ j) E ∧
      TranslationInvariantEventLaw M.P.toMeasure E ∧
      (∀ j z, M.P.toMeasure (E j z) = M.P.toMeasure
        (goodCubeEventField n C eps1 (coefficientLocalBadEvent M n C bad) j z)) ∧
      ∀ z, goodCubeEvent E z ⊆
        goodCubeEvent (goodCubeEventField n C eps1 (coefficientLocalBadEvent M n C bad)) z := by
  obtain ⟨E0, hm, hs, hmu, hcov⟩ := exists_coefficientLocalBadEvent_hull M n hC bad
  obtain ⟨hl, hi, hf⟩ := goodCubeEventField_clauses M n hC.le hdep E0 hm
  refine ⟨goodCubeEventField n C eps1 E0, hm, hl, hi, hf, ?_, ?_, ?_⟩
  · exact translationInvariantEventLaw_goodCubeEventField M n hC.le E0
      (fun z => SubdiffusiveProcess.CoarseGrainingVocab.measurableSet_of_restrictedCoefficientSigma
        (fun x _ => measurable_aCutoff M n x) (hm z)) hcov
  · intro j z
    cases j with
    | zero => exact hmu z
    | succ j => rfl
  · exact goodCubeEvent_mono_layerZero n C eps1 _ E0 hs

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
