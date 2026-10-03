module

public import SubdiffusiveProcess.Frozen.Section6.Defs.AccumulatedError

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab

open scoped BigOperators

/-- The literal first-failure error stopping index minus one. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.errorStoppingIndex {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (cutoff : Option ℕ)
    (lambda s : ℝ) (m : ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    {j : ℤ // j ∈ Set.Icc (-1 : ℤ) m} := by
  let candidates := insert m ((Finset.range m).filter fun n ↦
      sSup {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
        r = ∑ j ∈ Finset.Icc n m, accumulatedError M cutoff j z s ω} >
          lambda * ((m : ℝ) - (n : ℝ)))
  have hm : m ∈ candidates := by simp [candidates]
  let n := candidates.min' ⟨m, hm⟩
  have hn : n ≤ m := Finset.min'_le candidates m hm
  exact ⟨(n : ℤ) - 1, by constructor <;> omega⟩

