module

public import SubdiffusiveProcess.Frozen.Assumptions.AAnchored
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

/-!
# Anchored coefficient API

This module proves the characterization and elementary analytic properties of
the anchored coefficient and supplies the induced probability law when the
good event's measurable-full certificate is provided.
-/

-- REUSE-CANDIDATE: Algsuperdiff/Section3/Cutoff/Carrier.lean

namespace SubdiffusiveProcess.Frozen.Assumptions

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The selected logarithmic potential satisfies the defining local-limit
property. -/
theorem anchoredLog_spec (omega : AnchoredC11Sample d) :
    IsAnchoredC11Limit omega.1 (anchoredLog omega) :=
  Classical.choose_spec omega.property.exists

/-- Any field with the defining limit property is the selected logarithmic
potential. -/
theorem eq_anchoredLog_of_isAnchoredC11Limit (omega : AnchoredC11Sample d)
    (g : PotentialField d) (hg : IsAnchoredC11Limit omega.1 g) :
    g = anchoredLog omega :=
  omega.property.unique hg (anchoredLog_spec omega)

@[simp]
theorem anchoredLog_origin (omega : AnchoredC11Sample d) :
    anchoredLog omega 0 = 0 :=
  (anchoredLog_spec omega).anchored

@[simp]
theorem aAnchored_origin (M : GMCModel d) (omega : AnchoredC11Sample d) :
    aAnchored M omega 0 = 1 := by
  rw [aAnchored, anchoredLog_origin, Real.exp_zero]

theorem continuous_aAnchored (M : GMCModel d) (omega : AnchoredC11Sample d) :
    Continuous (aAnchored M omega) :=
  Real.continuous_exp.comp (anchoredLog omega).1.1.continuous

theorem aAnchored_pos (M : GMCModel d) (omega : AnchoredC11Sample d)
    (x : Vec d) :
    0 < aAnchored M omega x :=
  Real.exp_pos _

/-- The probability law induced on the exact anchored-convergence carrier by
a measurable full-event certificate. -/
-- Adapted from Algsuperdiff/Section3/Cutoff/Carrier.lean
noncomputable def anchoredC11SampleLaw (M : GMCModel d)
    (hmeas : MeasurableSet (anchoredC11GoodSet d))
    (hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1) :
    ProbabilityMeasure (AnchoredC11Sample d) :=
  ⟨Measure.comap (Subtype.val : AnchoredC11Sample d → PotentialSample d)
      M.P.toMeasure,
    (MeasurableEmbedding.subtype_coe hmeas).isProbabilityMeasure_comap <| by
      have hgood : anchoredC11GoodSet d ∈ ae M.P.toMeasure :=
        (mem_ae_iff_prob_eq_one hmeas).2 hfull
      filter_upwards [hgood] with omega homega
      exact ⟨⟨omega, homega⟩, rfl⟩⟩

end

end SubdiffusiveProcess.Frozen.Assumptions
