module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GridCenters
public import SubdiffusiveProcess.Section6.Defs.ErrorStoppingIndex

@[expose] public section

/-!
# Deterministic accumulated-error stopping interface

This is the pathwise half of `l.sum.the.errors`.  It unfolds the frozen
first-failure definition and uses the finite grid-centre carrier to justify
the real supremum occurring there.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The literal spatial family in the definition of `errorStoppingIndex` is
bounded above because it is indexed by the finite grid-centre carrier. -/
theorem bddAbove_accumulatedError_grid_values {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (s : ℝ) {n m : ℕ} (hnm : n ≤ m)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    BddAbove {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
      r = ∑ j ∈ Finset.Icc n m, accumulatedError M cutoff j z s omega} := by
  let centers := gridCentersInCube d n m
  let value : {z : Vec d // z ∈ centers} → ℝ := fun z =>
    ∑ j ∈ Finset.Icc n m, accumulatedError M cutoff j z.1 s omega
  obtain ⟨B, hB⟩ := Finite.bddAbove_range value
  refine ⟨B, ?_⟩
  rintro r ⟨z, hzgrid, hzmem, rfl⟩
  have hz : z ∈ centers := by
    exact (mem_gridCentersInCube_iff hnm).2 ⟨hzgrid, hzmem⟩
  exact hB ⟨⟨z, hz⟩, rfl⟩

/-- Below the literal error stopping index, every admissible centre satisfies
the printed accumulated-error bound. -/
theorem accumulatedError_sum_le_of_le_errorStoppingIndex {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (lambda s : ℝ) (m n : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hn : (n : ℤ) ≤ errorStoppingIndex M cutoff lambda s m omega)
    (z : Vec d) (hzgrid : OnTriadicGrid n z) (hzmem : z ∈ cube d m) :
    (∑ j ∈ Finset.Icc n m, accumulatedError M cutoff j z s omega) ≤
      lambda * ((m : ℝ) - (n : ℝ)) := by
  let candidates := insert m ((Finset.range m).filter fun k ↦
      sSup {r : ℝ | ∃ y : Vec d, OnTriadicGrid k y ∧ y ∈ cube d m ∧
        r = ∑ j ∈ Finset.Icc k m, accumulatedError M cutoff j y s omega} >
          lambda * ((m : ℝ) - (k : ℝ)))
  have hm : m ∈ candidates := by simp [candidates]
  let first := candidates.min' ⟨m, hm⟩
  have hfirst_le : first ≤ m := Finset.min'_le candidates m hm
  have hindex : (errorStoppingIndex M cutoff lambda s m omega : ℤ) =
      (first : ℤ) - 1 := by
    rfl
  rw [hindex] at hn
  have hnlt : n < first := by omega
  have hnm : n ≤ m := by omega
  have hnnot : n ∉ candidates := by
    intro hnmem
    have := Finset.min'_le candidates n hnmem
    omega
  let values : Set ℝ := {r : ℝ | ∃ y : Vec d,
    OnTriadicGrid n y ∧ y ∈ cube d m ∧
      r = ∑ j ∈ Finset.Icc n m, accumulatedError M cutoff j y s omega}
  have hnotlarge : ¬sSup values > lambda * ((m : ℝ) - (n : ℝ)) := by
    intro hlarge
    apply hnnot
    simp only [candidates, Finset.mem_insert, Finset.mem_filter,
      Finset.mem_range]
    right
    refine ⟨by omega, ?_⟩
    simpa only [values] using hlarge
  have hbdd : BddAbove values := by
    simpa only [values] using
      bddAbove_accumulatedError_grid_values M cutoff s hnm omega
  have hvalue : (∑ j ∈ Finset.Icc n m,
      accumulatedError M cutoff j z s omega) ∈ values :=
    ⟨z, hzgrid, hzmem, rfl⟩
  exact (le_csSup hbdd hvalue).trans (le_of_not_gt hnotlarge)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
