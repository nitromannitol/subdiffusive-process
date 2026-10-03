module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.CutoffHolderScale

@[expose] public section

/-!
# Theta-perturbed cutoff Hölder ladder: stopping event

The multiplier does not enter either stopping index.  This module fixes the
manuscript exponent `3/4`, exposes the corresponding measurable event, and
records that any tail estimate for the ordinary cutoff stopping scale applies
without a union over multipliers.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The exponent at which the manuscript reruns the cutoff ladder. -/
def thetaLadderExponent : ℝ := 3 / 4

theorem thetaLadderExponent_mem :
    thetaLadderExponent ∈ Set.Ico (1 / 2 : ℝ) 1 := by
  constructor <;> norm_num [thetaLadderExponent]

/-- The measurable minimal depth used by the theta ladder.  It is literally
the ordinary cutoff stopping depth at exponent `3/4`; in particular it has
no multiplier argument. -/
def thetaLadderStoppingScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (C1 C2 : ℝ) (step m : ℕ) : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ :=
  measurableCutoffHolderStoppingScale M L thetaLadderExponent
    (holderStoppingLambda C1 thetaLadderExponent)
    (holderStoppingEpsilon C2 thetaLadderExponent) step m

theorem measurable_thetaLadderStoppingScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (C1 C2 : ℝ) (step m : ℕ) :
    Measurable (thetaLadderStoppingScale M L C1 C2 step m) :=
  measurable_measurableCutoffHolderStoppingScale _ _ _ _ _ _ _

/-- The event on which the theta rerun reaches the deterministic depth `j0`.
It is independent of `theta`. -/
def thetaLadderStoppingEvent {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (C1 C2 : ℝ) (step m j0 : ℕ) : Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :=
  {omega | thetaLadderStoppingScale M L C1 C2 step m omega ≤ j0}

theorem measurableSet_thetaLadderStoppingEvent {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (C1 C2 : ℝ) (step m j0 : ℕ) :
    MeasurableSet (thetaLadderStoppingEvent M L C1 C2 step m j0) := by
  exact (measurable_thetaLadderStoppingScale M L C1 C2 step m)
    (measurableSet_Iic : MeasurableSet (Set.Iic j0))

theorem thetaLadderStoppingEvent_compl {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (C1 C2 : ℝ) (step m j0 : ℕ) :
    (thetaLadderStoppingEvent M L C1 C2 step m j0)ᶜ =
      {omega | j0 < thetaLadderStoppingScale M L C1 C2 step m omega} := by
  ext omega
  simp [thetaLadderStoppingEvent]

/-- Any ordinary stopping-depth tail is therefore already the theta-ladder
bad-event estimate.  The statement deliberately quantifies no multiplier. -/
theorem measure_thetaLadderStoppingEvent_compl_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (C1 C2 : ℝ) (step m j0 : ℕ) {R : ENNReal}
    (htail : M.P.toMeasure
      {omega | j0 < thetaLadderStoppingScale M L C1 C2 step m omega} ≤ R) :
    M.P.toMeasure (thetaLadderStoppingEvent M L C1 C2 step m j0)ᶜ ≤ R := by
  rw [thetaLadderStoppingEvent_compl]
  exact htail

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
