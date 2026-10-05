module

public import SubdiffusiveProcess.Section6.Defs.AccumulatedError

@[expose] public section

/-!
# The accumulated-error stopping index

`errorStoppingIndex` chooses the least failure candidate and subtracts one.
The inserted sentinel `m` makes the finite candidate set nonempty; the result
lies in `[-1,m]`. If no earlier failure is found it returns `m-1`, and at
`m = 0` it returns `-1`. These are the literal endpoint conventions.
The spatial error criterion uses a total real supremum; its intended meaning
uses the bounds and summability proved by the Section 6 stopping suppliers.
-/

open SubdiffusiveProcess.CoarseGrainingVocab

open scoped BigOperators

/-- The literal first-failure error stopping index minus one. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.errorStoppingIndex {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (lambda s : ℝ) (m : ℕ) (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    {j : ℤ // j ∈ Set.Icc (-1 : ℤ) m} := by
  let candidates := insert m ((Finset.range m).filter fun n ↦
      sSup {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
        r = ∑ j ∈ Finset.Icc n m, accumulatedError M cutoff j z s ω} >
          lambda * ((m : ℝ) - (n : ℝ)))
  have hm : m ∈ candidates := by simp [candidates]
  let n := candidates.min' ⟨m, hm⟩
  have hn : n ≤ m := Finset.min'_le candidates m hm
  exact ⟨(n : ℤ) - 1, by constructor <;> omega⟩

