module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.GoodScaleSaturation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.CutoffHolderScale

@[expose] public section

/-!
# The stopping carriers coincide at or below the cutoff

`Section6Cutoff.mem_goodEvent_some_iff_none_of_scale_le_cutoff` and
`Section6Cutoff.accumulatedError_some_eq_none_of_scale_le_cutoff` say that the
two ingredients of the frozen stopping indices agree at every scale `≤ L`.
Both frozen indices at domain scale `m` only ever evaluate those ingredients at
scales `j ∈ [n, m]`, so for `m ≤ L` the two indices — and hence
`regularityMinimalScale`, the literal Hölder stopping scale and its measurable
hull — are *literally the same function of `ω`*.

This is the transport `Section6Stopping.measurableCutoffHolderStoppingScale`
versus `Section6Stopping.measurableHolderStoppingScale` that
 Addendum 35 named but did not
prove.  Its consequence is recorded in `CutoffRows.lean`: the `m ≤ L` half of
the manuscript's `L`-uniform row obligation
(`Section6HolderInterior.InteriorCutoffRowsAt`) is exactly the established
above-cutoff rows.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The accumulated-error tail sums used by the error stopping index agree at
or below the cutoff. -/
theorem accumulatedError_sum_some_eq_none_of_le_cutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (n : ℕ) (z : Vec d) (s : ℝ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    ∑ j ∈ Finset.Icc n m, accumulatedError M (some L) j z s omega =
      ∑ j ∈ Finset.Icc n m, accumulatedError M none j z s omega := by
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
  exact Section6Cutoff.accumulatedError_some_eq_none_of_scale_le_cutoff M
    (le_trans hjm hmL) z s omega

/-- The good-scale counting sums used by the good stopping index agree at or
below the cutoff. -/
theorem goodEventCount_sum_some_eq_none_of_le_cutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (n : ℕ) (z : Vec d) (epsilon s : ℝ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    ∑ j ∈ Finset.Icc n m,
        (if omega ∈ goodEvent M (some L) j z epsilon s then (1 : ℝ) else 0) =
      ∑ j ∈ Finset.Icc n m,
        (if omega ∈ goodEvent M none j z epsilon s then (1 : ℝ) else 0) := by
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
  by_cases hmem : omega ∈ goodEvent M (some L) j z epsilon s
  · have hnone : omega ∈ goodEvent M none j z epsilon s :=
      (Section6Cutoff.mem_goodEvent_some_iff_none_of_scale_le_cutoff M
        (le_trans hjm hmL) z epsilon s omega).1 hmem
    simp [hmem, hnone]
  · have hnone : omega ∉ goodEvent M none j z epsilon s := fun h =>
      hmem ((Section6Cutoff.mem_goodEvent_some_iff_none_of_scale_le_cutoff M
        (le_trans hjm hmL) z epsilon s omega).2 h)
    simp [hmem, hnone]

/-- **The error stopping index saturates at the cutoff.** -/
theorem errorStoppingIndex_some_eq_none_of_le_cutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (lambda s : ℝ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    ((errorStoppingIndex M (some L) lambda s m omega : ℤ)) =
      ((errorStoppingIndex M none lambda s m omega : ℤ)) := by
  have hpred : ∀ n : ℕ,
      (sSup {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
          r = ∑ j ∈ Finset.Icc n m, accumulatedError M (some L) j z s omega} >
        lambda * ((m : ℝ) - (n : ℝ))) =
      (sSup {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
          r = ∑ j ∈ Finset.Icc n m, accumulatedError M none j z s omega} >
        lambda * ((m : ℝ) - (n : ℝ))) := by
    intro n
    congr 2
    ext r
    constructor
    · rintro ⟨z, hz, hzm, rfl⟩
      exact ⟨z, hz, hzm,
        accumulatedError_sum_some_eq_none_of_le_cutoff M hmL n z s omega⟩
    · rintro ⟨z, hz, hzm, rfl⟩
      exact ⟨z, hz, hzm,
        (accumulatedError_sum_some_eq_none_of_le_cutoff M hmL n z s omega).symm⟩
  unfold errorStoppingIndex
  simp only [hpred]

/-- **The good-scale stopping index saturates at the cutoff.** -/
theorem goodStoppingIndex_some_eq_none_of_le_cutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (lambda epsilon s : ℝ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    ((goodStoppingIndex M (some L) lambda epsilon s m omega : ℤ)) =
      ((goodStoppingIndex M none lambda epsilon s m omega : ℤ)) := by
  have hpred : ∀ n : ℕ,
      (sInf {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
          r = ∑ j ∈ Finset.Icc n m,
            if omega ∈ goodEvent M (some L) j z epsilon s then (1 : ℝ) else 0} ≤
        (1 - lambda) * ((m : ℝ) - (n : ℝ))) =
      (sInf {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
          r = ∑ j ∈ Finset.Icc n m,
            if omega ∈ goodEvent M none j z epsilon s then (1 : ℝ) else 0} ≤
        (1 - lambda) * ((m : ℝ) - (n : ℝ))) := by
    intro n
    congr 2
    ext r
    constructor
    · rintro ⟨z, hz, hzm, rfl⟩
      exact ⟨z, hz, hzm,
        goodEventCount_sum_some_eq_none_of_le_cutoff M hmL n z epsilon s omega⟩
    · rintro ⟨z, hz, hzm, rfl⟩
      exact ⟨z, hz, hzm,
        (goodEventCount_sum_some_eq_none_of_le_cutoff M hmL n z epsilon s omega).symm⟩
  unfold goodStoppingIndex
  simp only [hpred]

/-- **The literal Hölder stopping scale saturates at the cutoff.** -/
theorem cutoffHolderStoppingScale_eq_holderStoppingScale_of_le_cutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (alpha lambda epsilon : ℝ) (step : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Section6Stopping.cutoffHolderStoppingScale M L alpha lambda epsilon step m
        omega =
      Section6Stopping.holderStoppingScale M alpha lambda epsilon step m omega := by
  unfold Section6Stopping.cutoffHolderStoppingScale
    Section6Stopping.holderStoppingScale
  congr 1
  unfold regularityMinimalScale
  rw [errorStoppingIndex_some_eq_none_of_le_cutoff M hmL lambda
      Section6Stopping.holderStoppingS omega,
    goodStoppingIndex_some_eq_none_of_le_cutoff M hmL lambda epsilon
      Section6Stopping.holderStoppingS omega]

/-- **The measurable hulls coincide at or below the cutoff.** -/
theorem measurableCutoffHolderStoppingScale_eq_of_le_cutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (alpha lambda epsilon : ℝ) (step : ℕ) :
    Section6Stopping.measurableCutoffHolderStoppingScale M L alpha lambda
        epsilon step m =
      Section6Stopping.measurableHolderStoppingScale M alpha lambda epsilon
        step m := by
  unfold Section6Stopping.measurableCutoffHolderStoppingScale
    Section6Stopping.measurableHolderStoppingScale
  congr 1
  funext omega
  exact cutoffHolderStoppingScale_eq_holderStoppingScale_of_le_cutoff M hmL
    alpha lambda epsilon step omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
