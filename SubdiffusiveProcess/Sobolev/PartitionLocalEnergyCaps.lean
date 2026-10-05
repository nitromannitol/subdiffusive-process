module

public import SubdiffusiveProcess.Sobolev.GradientEnergyPartition

@[expose] public section

/-! Finite density partitions give local mass bounds from only the cells meeting a test set.
The interface mass vanishes before taking a limit; no limiting measure is split here. -/
open MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess

/-- A local density mass is bounded by any nonnegative caps for the partition cells it meets. -/
theorem withDensity_set_le_sum_of_partition_caps
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    {I : Type*} [Fintype I] (Q : Set X) (cell : I → Set X)
    (hle : ∀ i, cell i ⊆ Q) (hcell : ∀ i, MeasurableSet (cell i))
    (hdisj : Pairwise (Function.onFun Disjoint cell))
    (hcover : (⋃ i, cell i) =ᵐ[mu] Q) (f : X → ENNReal)
    (O : Set X) (hO : MeasurableSet O) (cap : I → ℝ) (hcap : ∀ i, 0 ≤ cap i)
    (hbound : ∀ i, (cell i ∩ O).Nonempty →
      (mu.restrict Q).withDensity f (cell i) ≤ ENNReal.ofReal (cap i)) :
    (mu.restrict Q).withDensity f O ≤ ENNReal.ofReal (∑ i, cap i) := by
  classical
  have heq := withDensity_eq_sum_restrict_of_partition mu Q cell hle hcell hdisj hcover f
  rw [heq, Measure.sum_apply _ hO, tsum_fintype,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hcap i)]
  apply Finset.sum_le_sum
  intro i hi
  rw [Measure.restrict_apply hO]
  by_cases h : (cell i ∩ O).Nonempty
  · exact (measure_mono Set.inter_subset_right).trans (hbound i h)
  · rw [Set.inter_comm, Set.not_nonempty_iff_eq_empty.mp h, measure_empty]
    exact bot_le

end SubdiffusiveProcess
