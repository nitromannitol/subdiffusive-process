import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedImageCore
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.RestrictedObservation
import SubdiffusiveProcess.Assumptions.Cutoff
/-!
# Coefficient-measurable exceptional events

Continuous coefficients on a nonempty window are determined by a countable
dense sequence of evaluations. This gives a Polish observation carrier for
`RestrictedImageCore`, and its pullback sigma-field lies in the frozen
restricted coefficient sigma-field on that same window.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open MeasureTheory Topology Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping SubdiffusiveProcess.Frozen.Assumptions
noncomputable section

def restrictedDenseObservation {d : ℕ} {X : Type*}
    (a : X → Vec d → ℝ) (B : Set (Vec d)) [Nonempty B] (w : X) : ℕ → ℝ :=
  fun n => a w (TopologicalSpace.denseSeq B n)

theorem restrictedDenseObservation_measurable {d : ℕ} {X : Type*}
    (a : X → Vec d → ℝ) (B : Set (Vec d)) [Nonempty B] :
    Measurable[restrictedCoefficientSigma a B] (restrictedDenseObservation a B) := by
  letI : MeasurableSpace X := restrictedCoefficientSigma a B
  apply measurable_pi_iff.mpr
  intro n
  exact measurable_eval_restrictedCoefficientSigma (TopologicalSpace.denseSeq B n).property

theorem restrictedDenseObservation_fibre {d : ℕ} {X : Type*}
    (a : X → Vec d → ℝ) (B : Set (Vec d)) [Nonempty B]
    (ha : ∀ w, Continuous (a w)) {w w' : X}
    (h : restrictedDenseObservation a B w = restrictedDenseObservation a B w') :
    Section6ThetaLadder.restrictedCoefficientObservation a B w =
      Section6ThetaLadder.restrictedCoefficientObservation a B w' := by
  apply (TopologicalSpace.denseRange_denseSeq B).equalizer
    ((ha w).comp continuous_subtype_val) ((ha w').comp continuous_subtype_val)
  funext n
  exact congrFun h n

theorem restricted_exists_coefficient_bad
    {d : ℕ} {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (a : X → Vec d → ℝ)
    (B : Set (Vec d)) [Nonempty B] (ha : ∀ w, Continuous (a w))
    (hmeas : ∀ x ∈ B, Measurable fun w => a w x)
    (P : X → Prop) (G : Set X) (hG : MeasurableSet G)
    (hGP : ∀ w ∈ G, P w)
    (hP : ∀ w w', Section6ThetaLadder.restrictedCoefficientObservation a B w =
      Section6ThetaLadder.restrictedCoefficientObservation a B w' → (P w ↔ P w')) :
    ∃ bad : Set X, MeasurableSet[restrictedCoefficientSigma a B] bad ∧
      mu bad ≤ mu Gᶜ ∧ ∀ w ∉ bad, P w := by
  have hf := restrictedDenseObservation_measurable a B
  have hfle : restrictedCoefficientSigma a B ≤ (inferInstance : MeasurableSpace X) :=
    restrictedCoefficientSigma_le hmeas
  have hfambient : Measurable (restrictedDenseObservation a B) :=
    hf.mono hfle le_rfl
  obtain ⟨bad, hbad, htail, hprop⟩ := restricted_exists_bad_event
    mu (restrictedDenseObservation a B) hfambient P G hG hGP
      (fun w w' h => hP w w' (restrictedDenseObservation_fibre a B ha h))
  exact ⟨bad, hf.comap_le _ hbad, htail, hprop⟩

end
end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
