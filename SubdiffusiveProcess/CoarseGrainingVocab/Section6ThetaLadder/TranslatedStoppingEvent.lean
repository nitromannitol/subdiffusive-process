module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.StoppingEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Action

@[expose] public section

/-!
# Theta-perturbed ladder: translated stopping event

The bounded-multiplier window is centered at an arbitrary physical point.
Stationarity transports the origin-centered cutoff stopping scale to that
window without changing its law.  This file records the translated event,
its ambient measurability, and the exact measure transfer.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- The fixed-depth theta stopping event viewed from the physical center
`z`. -/
def translatedThetaLadderStoppingEvent {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (C1 C2 : ℝ) (step m j0 : ℕ) (z : Vec d) : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
  {omega | thetaLadderStoppingScale M L C1 C2 step m
      (translatePotentialSample z omega) ≤ j0}

theorem translatedThetaLadderStoppingEvent_eq_preimage {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (C1 C2 : ℝ) (step m j0 : ℕ) (z : Vec d) :
    translatedThetaLadderStoppingEvent M L C1 C2 step m j0 z =
      translatePotentialSample z ⁻¹'
        thetaLadderStoppingEvent M L C1 C2 step m j0 := rfl

theorem measurableSet_translatedThetaLadderStoppingEvent {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (C1 C2 : ℝ) (step m j0 : ℕ) (z : Vec d) :
    MeasurableSet
      (translatedThetaLadderStoppingEvent M L C1 C2 step m j0 z) := by
  rw [translatedThetaLadderStoppingEvent_eq_preimage]
  exact (measurableSet_thetaLadderStoppingEvent M L C1 C2 step m j0).preimage
    (Section6Covariance.measurable_translatePotentialSample z)

/-- Translation leaves the stopping-event probability unchanged. -/
theorem measure_compl_translatedThetaLadderStoppingEvent {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (C1 C2 : ℝ) (step m j0 : ℕ) (z : Vec d) :
    M.P.toMeasure
        (translatedThetaLadderStoppingEvent M L C1 C2 step m j0 z)ᶜ =
      M.P.toMeasure
        (thetaLadderStoppingEvent M L C1 C2 step m j0)ᶜ := by
  have hset :
      (translatedThetaLadderStoppingEvent M L C1 C2 step m j0 z)ᶜ =
        translatePotentialSample z ⁻¹'
          (thetaLadderStoppingEvent M L C1 C2 step m j0)ᶜ := by
    rw [translatedThetaLadderStoppingEvent_eq_preimage]
    exact Set.preimage_compl
  rw [hset, Section6Covariance.measure_preimage_translatePotentialSample M z]

/-- Any origin-centered tail bound therefore applies verbatim to the physical
window. -/
theorem measure_compl_translatedThetaLadderStoppingEvent_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (C1 C2 : ℝ) (step m j0 : ℕ) (z : Vec d) {R : ENNReal}
    (htail : M.P.toMeasure
      (thetaLadderStoppingEvent M L C1 C2 step m j0)ᶜ ≤ R) :
    M.P.toMeasure
      (translatedThetaLadderStoppingEvent M L C1 C2 step m j0 z)ᶜ ≤ R := by
  rw [measure_compl_translatedThetaLadderStoppingEvent]
  exact htail

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
