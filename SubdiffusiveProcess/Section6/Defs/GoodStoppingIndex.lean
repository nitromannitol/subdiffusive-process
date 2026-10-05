module

public import SubdiffusiveProcess.Section6.Defs.GoodEvent

@[expose] public section

/-!
# The good-scale stopping index

`goodStoppingIndex` chooses the least failure candidate and subtracts one.
The inserted sentinel `m + 1` makes the finite candidate set nonempty, so the
result always lies in the integer interval `[-1,m]`. If there is no failure
candidate among scales `0,...,m`, the sentinel is selected and the result is
`m`. The count criterion uses a real infimum over grid centers; its intended
minimum requires the corresponding set to be nonempty and bounded below.
The stopping estimates supply the paper's positive-parameter conditions.
-/

open SubdiffusiveProcess.CoarseGrainingVocab

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The literal first-failure good-scale stopping index minus one. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.goodStoppingIndex {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (lambda epsilon s : ℝ) (m : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
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

