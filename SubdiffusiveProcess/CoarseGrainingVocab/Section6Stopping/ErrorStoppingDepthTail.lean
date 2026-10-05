module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.HolderScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GridCenters

@[expose] public section

/-!
# Tail event for the accumulated-error stopping depth

This file isolates the deterministic first-failure and spatial-union layer of
`l.sum.the.errors`.  The only remaining input after this module is the
fixed-`s0` one-centre window estimate.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

def accumulatedErrorSpatialFailure {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (lambda s : ℝ)
    (n m : ℕ) : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
  {omega | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
    lambda * ((m : ℝ) - (n : ℝ)) <
      ∑ j ∈ Finset.Icc n m, accumulatedError M none j z s omega}

/-- Away from the deterministic depth-one sentinel, a large frozen error
depth supplies an actual failing start scale. -/
theorem errorStoppingDepth_tail_subset_iUnion {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (lambda s : ℝ)
    (q m : ℕ) (hq : 0 < q) :
    {omega | q < errorStoppingDepth M lambda s m omega} ⊆
      ⋃ n ∈ Finset.range (m - q + 1),
        accumulatedErrorSpatialFailure M lambda s n m := by
  intro omega homega
  change q < errorStoppingDepth M lambda s m omega at homega
  let candidates := insert m ((Finset.range m).filter fun n ↦
      sSup {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
        r = ∑ j ∈ Finset.Icc n m, accumulatedError M none j z s omega} >
        lambda * ((m : ℝ) - (n : ℝ)))
  have hm : m ∈ candidates := by simp [candidates]
  let first := candidates.min' ⟨m, hm⟩
  have hfirst_mem : first ∈ candidates := Finset.min'_mem candidates ⟨m, hm⟩
  have hfirst_le : first <= m := Finset.min'_le candidates m hm
  have hindex : (errorStoppingIndex M none lambda s m omega : Int) =
      (first : Int) - 1 := by
    rfl
  have hdepth : errorStoppingDepth M lambda s m omega = m + 1 - first := by
    unfold errorStoppingDepth
    rw [hindex]
    have hnonneg : 0 <= (m : Int) - ((first : Int) - 1) := by omega
    apply Nat.cast_injective (R := Int)
    rw [Int.toNat_of_nonneg hnonneg, Nat.cast_sub (by omega : first <= m + 1)]
    push_cast
    ring
  rw [hdepth] at homega
  have hfirst_lt_m : first < m := by omega
  have hfirst_range : first ∈ Finset.range (m - q + 1) := by
    rw [Finset.mem_range]
    omega
  have hfilter : first ∈ (Finset.range m).filter fun n ↦
      sSup {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
        r = ∑ j ∈ Finset.Icc n m, accumulatedError M none j z s omega} >
        lambda * ((m : ℝ) - (n : ℝ)) := by
    simp only [candidates, Finset.mem_insert] at hfirst_mem
    rcases hfirst_mem with htop | hfilter
    · omega
    · exact hfilter
  obtain ⟨_hrange, hfail⟩ := Finset.mem_filter.1 hfilter
  unfold accumulatedErrorSpatialFailure
  let values : Set ℝ := {r : ℝ | ∃ z : Vec d,
    OnTriadicGrid first z ∧ z ∈ cube d m ∧
      r = ∑ j ∈ Finset.Icc first m, accumulatedError M none j z s omega}
  have hnonempty : values.Nonempty := by
    let centers := gridCentersInCube d first m
    have hcenters : centers.Nonempty := by
      rw [← Finset.card_pos, card_gridCentersInCube (Nat.le_of_lt hfirst_lt_m)]
      positivity
    obtain ⟨z, hz⟩ := hcenters
    obtain ⟨hzgrid, hzmem⟩ :=
      (mem_gridCentersInCube_iff (Nat.le_of_lt hfirst_lt_m)).1 hz
    exact ⟨_, z, hzgrid, hzmem, rfl⟩
  have hsup : lambda * ((m : ℝ) - (first : ℝ)) < sSup values := by
    simpa only [values] using hfail
  obtain ⟨r, ⟨z, hzgrid, hzmem, hr⟩, hrlarge⟩ :=
    exists_lt_of_lt_csSup hnonempty hsup
  exact Set.mem_iUnion₂.2 ⟨first, hfirst_range,
    ⟨z, hzgrid, hzmem, by simpa only [hr] using hrlarge⟩⟩

/-- The exact finite spatial/starting-scale union preceding the analytic
fixed-`s0` window estimate. -/
theorem measure_errorStoppingDepth_tail_le_sum {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (lambda s : ℝ)
    (q m : ℕ) (hq : 0 < q) :
    M.P.toMeasure {omega | q < errorStoppingDepth M lambda s m omega} <=
      ∑ n ∈ Finset.range (m - q + 1),
        M.P.toMeasure (accumulatedErrorSpatialFailure M lambda s n m) := by
  calc
    M.P.toMeasure {omega | q < errorStoppingDepth M lambda s m omega} <=
        M.P.toMeasure (⋃ n ∈ Finset.range (m - q + 1),
          accumulatedErrorSpatialFailure M lambda s n m) :=
      measure_mono (errorStoppingDepth_tail_subset_iUnion M lambda s q m hq)
    _ <= ∑ n ∈ Finset.range (m - q + 1),
        M.P.toMeasure (accumulatedErrorSpatialFailure M lambda s n m) :=
      measure_biUnion_finset_le _ _

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
