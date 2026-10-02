import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.AccumulatedErrorWindow
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.CutoffHolderScale
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GridCenters

/-!
# Tail event for the finite-cutoff accumulated-error stopping depth

This is the finite-cutoff specialization of the deterministic first-failure
and spatial-union layer used by the Holder stopping argument.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

def cutoffAccumulatedErrorSpatialFailure {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (lambda s : ℝ)
    (n m : ℕ) : Set (Sample d) :=
  {omega | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
    lambda * ((m : ℝ) - (n : ℝ)) <
      ∑ j ∈ Finset.Icc n m, accumulatedError M (some L) j z s omega}

/-- Away from the deterministic depth-one sentinel, a large cutoff error
depth supplies an actual failing start scale. -/
theorem cutoffErrorStoppingDepth_tail_subset_iUnion {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (lambda s : ℝ)
    (q m : ℕ) (hq : 0 < q) :
    {omega | q < cutoffErrorStoppingDepth M L lambda s m omega} ⊆
      ⋃ n ∈ Finset.range (m - q + 1),
        cutoffAccumulatedErrorSpatialFailure M L lambda s n m := by
  intro omega homega
  change q < cutoffErrorStoppingDepth M L lambda s m omega at homega
  let candidates := insert m ((Finset.range m).filter fun n ↦
      sSup {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
        r = ∑ j ∈ Finset.Icc n m,
          accumulatedError M (some L) j z s omega} >
        lambda * ((m : ℝ) - (n : ℝ)))
  have hm : m ∈ candidates := by simp [candidates]
  let first := candidates.min' ⟨m, hm⟩
  have hfirst_mem : first ∈ candidates :=
    Finset.min'_mem candidates ⟨m, hm⟩
  have hfirst_le : first ≤ m := Finset.min'_le candidates m hm
  have hindex : (errorStoppingIndex M (some L) lambda s m omega : Int) =
      (first : Int) - 1 := by
    rfl
  have hdepth : cutoffErrorStoppingDepth M L lambda s m omega =
      m + 1 - first := by
    unfold cutoffErrorStoppingDepth
    rw [hindex]
    have hnonneg : 0 ≤ (m : Int) - ((first : Int) - 1) := by omega
    apply Nat.cast_injective (R := Int)
    rw [Int.toNat_of_nonneg hnonneg, Nat.cast_sub (by omega : first ≤ m + 1)]
    push_cast
    ring
  rw [hdepth] at homega
  have hfirst_lt_m : first < m := by omega
  have hfirst_range : first ∈ Finset.range (m - q + 1) := by
    rw [Finset.mem_range]
    omega
  have hfilter : first ∈ (Finset.range m).filter fun n ↦
      sSup {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
        r = ∑ j ∈ Finset.Icc n m,
          accumulatedError M (some L) j z s omega} >
        lambda * ((m : ℝ) - (n : ℝ)) := by
    simp only [candidates, Finset.mem_insert] at hfirst_mem
    rcases hfirst_mem with htop | hfilter
    · omega
    · exact hfilter
  obtain ⟨_hrange, hfail⟩ := Finset.mem_filter.1 hfilter
  unfold cutoffAccumulatedErrorSpatialFailure
  let values : Set ℝ := {r : ℝ | ∃ z : Vec d,
    OnTriadicGrid first z ∧ z ∈ cube d m ∧
      r = ∑ j ∈ Finset.Icc first m,
        accumulatedError M (some L) j z s omega}
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
finite-cutoff window estimate. -/
theorem measure_cutoffErrorStoppingDepth_tail_le_sum {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (lambda s : ℝ)
    (q m : ℕ) (hq : 0 < q) :
    M.P.toMeasure {omega | q < cutoffErrorStoppingDepth M L lambda s m omega} ≤
      ∑ n ∈ Finset.range (m - q + 1),
        M.P.toMeasure (cutoffAccumulatedErrorSpatialFailure M L lambda s n m) := by
  calc
    M.P.toMeasure {omega |
        q < cutoffErrorStoppingDepth M L lambda s m omega} ≤
        M.P.toMeasure (⋃ n ∈ Finset.range (m - q + 1),
          cutoffAccumulatedErrorSpatialFailure M L lambda s n m) :=
      measure_mono
        (cutoffErrorStoppingDepth_tail_subset_iUnion M L lambda s q m hq)
    _ ≤ ∑ n ∈ Finset.range (m - q + 1),
        M.P.toMeasure (cutoffAccumulatedErrorSpatialFailure M L lambda s n m) :=
      measure_biUnion_finset_le _ _

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
