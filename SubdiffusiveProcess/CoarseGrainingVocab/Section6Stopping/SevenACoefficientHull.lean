import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedCoefficientEvent
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Action




set_option autoImplicit false

open Homogenization hiding Vec
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

/-- A coefficient-local bad set has a restricted-measurable hull with the
same outer measure. The original bad predicate may be arbitrary. -/
theorem exists_cutoff_local_measurable_hull {d : ℕ} (M : GMCModel d) (L : ℕ)
    (B : Set (Vec d)) [Nonempty B] (bad : Set (B → ℝ)) :
    ∃ E : Set (PotentialSample d),
      MeasurableSet[restrictedCoefficientSigma (aCutoff M L) B] E ∧
      restrictedCoefficientObservation (aCutoff M L) B ⁻¹' bad ⊆ E ∧
      M.P.toMeasure E = M.P.toMeasure
        (restrictedCoefficientObservation (aCutoff M L) B ⁻¹' bad) := by
  let A : Set (PotentialSample d) :=
    restrictedCoefficientObservation (aCutoff M L) B ⁻¹' bad
  let H := toMeasurable M.P.toMeasure A
  obtain ⟨E, hE, hmu, hgood⟩ :=
    restricted_exists_coefficient_bad M.P.toMeasure (aCutoff M L) B
      (continuous_aCutoff M L) (fun x _ => measurable_aCutoff M L x)
      (fun w => w ∉ A) Hᶜ (measurableSet_toMeasurable _ _).compl
      (fun w hw hAw => hw (subset_toMeasurable _ _ hAw))
      (fun w v h => by
        change (restrictedCoefficientObservation (aCutoff M L) B w ∉ bad) ↔
          (restrictedCoefficientObservation (aCutoff M L) B v ∉ bad)
        rw [h])
  have hAE : A ⊆ E := by
    intro w hw
    by_contra h
    exact hgood w h hw
  refine ⟨E, hE, hAE, le_antisymm ?_ (measure_mono hAE)⟩
  simpa only [compl_compl, H, measure_toMeasurable] using hmu

/-- Translating a restricted-measurable event translates its observation
window by exactly the same vector. -/
theorem measurableSet_preimage_translate_restricted {d : ℕ} (M : GMCModel d) (L : ℕ)
    (B : Set (Vec d)) (z : Vec d) {s : Set (PotentialSample d)}
    (hs : MeasurableSet[restrictedCoefficientSigma (aCutoff M L) B] s) :
    MeasurableSet[restrictedCoefficientSigma (aCutoff M L)
      ((fun x => x + z) '' B)] (translatePotentialSequence z ⁻¹' s) := by
  letI : MeasurableSpace (PotentialSample d) :=
    restrictedCoefficientSigma (aCutoff M L) ((fun x => x + z) '' B)
  rw [restrictedCoefficientSigma_eq_comap_observation,
    MeasurableSpace.measurableSet_comap] at hs
  obtain ⟨T, hT, rfl⟩ := hs
  apply hT.preimage
  apply measurable_pi_iff.mpr
  intro x
  simpa only [Function.comp_apply, restrictedCoefficientObservation,
    aCutoff_translatePotentialSequence] using
    (measurable_eval_restrictedCoefficientSigma (a := aCutoff M L)
      (B := (fun y => y + z) '' B) (x := x + z) ⟨x, x.property, rfl⟩)

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
