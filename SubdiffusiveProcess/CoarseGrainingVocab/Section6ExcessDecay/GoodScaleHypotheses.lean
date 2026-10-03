module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.AnchorInterior
public import SubdiffusiveProcess.Providers.Section6.GoodScaleMathcalE

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Prop-valued input with the exact basename and binder strength of the
frozen harmonic block.  `HarmonicApproximationInput` is its statement body,
transcribed from the frozen v6 declaration. -/
abbrev harmonic_approximation_good_scales (d : ℕ) : Prop :=
  NeZero d → HarmonicApproximationInput d

/-- The frozen harmonic conclusion, supplied under its `NeZero d` binder,
gives the dimension-uniform hypothesis consumed by the excess-decay branches.
For `d = 0` the model class is empty because every model carries `2 ≤ d`. -/
theorem harmonicApproximationInput_of_harmonic_approximation_good_scales
    (d : ℕ)
    (h : harmonic_approximation_good_scales d) :
    HarmonicApproximationInput d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, one_pos, ?_⟩
    intro M
    exact absurd M.shellPrefix.dimension (by norm_num)
  · exact h ⟨hd.ne'⟩

/-- The second clause of the established good-scale error theorem supplies
the cap used in Step 3 of the excess-decay proof. -/
theorem mathcalECapInput_of_good_scale_mathcal_e (d : ℕ) :
    MathcalECapInput d := by
  obtain ⟨C, hC, hgood⟩ := SubdiffusiveProcess.Providers.Section6.good_scale_mathcal_e d
  refine ⟨C, hC, ?_⟩
  intro M s hs L m hmL omega epsilon hepsilon homega
  exact (hgood M s hs L m hmL omega).2 epsilon hepsilon homega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
