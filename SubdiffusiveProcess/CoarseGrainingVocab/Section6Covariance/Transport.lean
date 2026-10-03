module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.GoodEvent

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance

open MeasureTheory Homogenization

noncomputable section

variable {d : ℕ}

/-- A bound on the Section 6 error valid on the good event at translate `0`
holds on the good event at every translate. -/
theorem section6HomogenizationError_le_of_translate_zero
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {cutoff : Option ℕ} {s : ℝ}
    {L m : ℕ} {epsilon B : ℝ}
    (hzero : ∀ ν : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ν ∈ goodEvent M cutoff m 0 epsilon s →
        section6HomogenizationError M s L m ν 0 ≤ B)
    (z : Vec d) {ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (hω : ω ∈ goodEvent M cutoff m z epsilon s) :
    section6HomogenizationError M s L m ω z ≤ B := by
  rw [section6HomogenizationError_eq_translate_zero]
  exact hzero (translatePotentialSample z ω)
    ((mem_goodEvent_iff_translate_zero M cutoff m epsilon s z ω).mp hω)

/-- A bound on the Section 6 response valid on the good event at translate `0`
holds on the good event at every translate. -/
theorem section6Response_le_of_translate_zero
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {cutoff : Option ℕ}
    {cubeScale responseCutoff m : ℕ} {epsilon s B : ℝ} {e : Vec d}
    (hzero : ∀ ν : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ν ∈ goodEvent M cutoff m 0 epsilon s →
        section6Response M cubeScale responseCutoff ν 0 e ≤ B)
    (z : Vec d) {ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (hω : ω ∈ goodEvent M cutoff m z epsilon s) :
    section6Response M cubeScale responseCutoff ω z e ≤ B := by
  rw [section6Response_eq_translate_zero]
  exact hzero (translatePotentialSample z ω)
    ((mem_goodEvent_iff_translate_zero M cutoff m epsilon s z ω).mp hω)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
