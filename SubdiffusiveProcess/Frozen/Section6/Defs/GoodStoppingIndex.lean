module

public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The literal first-failure good-scale stopping index minus one. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.goodStoppingIndex {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (cutoff : Option ℕ)
    (lambda epsilon s : ℝ) (m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    {j : ℤ // j ∈ Set.Icc (-1 : ℤ) m} := by
  let candidates := insert (m + 1) ((Finset.range (m + 1)).filter fun n ↦
      sInf {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
        r = ∑ j ∈ Finset.Icc n m,
          if ω ∈ goodEvent M cutoff j z epsilon s then 1 else 0} ≤
        (1 - lambda) * ((m : ℝ) - (n : ℝ)))
  have hm : m + 1 ∈ candidates := by simp [candidates]
  let n := candidates.min' ⟨m + 1, hm⟩
  have hn : n ≤ m + 1 := Finset.min'_le candidates (m + 1) hm
  exact ⟨(n : ℤ) - 1, by constructor <;> omega⟩

