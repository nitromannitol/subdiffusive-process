module

public import SubdiffusiveProcess.Sobolev.GradientEnergyMeasureIntegral

@[expose] public section

/-! Exact splitting of coefficient-gradient measures over finite partitions.
The partition covers the parent only almost everywhere; the density therefore
places no mass on omitted interfaces.
-/
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

/-- A density measure splits exactly over an almost-everywhere finite partition. -/
theorem withDensity_eq_sum_restrict_of_partition
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    {I : Type*} [Fintype I] (Q : Set X) (cell : I → Set X)
    (hle : ∀ i, cell i ⊆ Q) (hcell : ∀ i, MeasurableSet (cell i))
    (hdisj : Pairwise (Function.onFun Disjoint cell))
    (hcover : (⋃ i, cell i) =ᵐ[mu] Q) (f : X → ENNReal) :
    (mu.restrict Q).withDensity f =
      Measure.sum (fun i => ((mu.restrict Q).withDensity f).restrict (cell i)) := by
  calc
    (mu.restrict Q).withDensity f = (mu.restrict (⋃ i, cell i)).withDensity f := by
      rw [Measure.restrict_congr_set hcover]
    _ = Measure.sum (fun i => (mu.restrict (cell i)).withDensity f) := by
      rw [Measure.restrict_iUnion hdisj hcell, withDensity_sum]
    _ = Measure.sum (fun i => ((mu.restrict Q).withDensity f).restrict (cell i)) := by
      apply congrArg Measure.sum
      funext i
      rw [restrict_withDensity (hcell i), Measure.restrict_restrict_of_subset (hle i)]

/-- Nonnegative cell bounds control the total mass of a density measure on a finite partition. -/
theorem withDensity_mass_le_sum_of_partition
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    {I : Type*} [Fintype I] (Q : Set X) (cell : I → Set X)
    (hle : ∀ i, cell i ⊆ Q) (hcell : ∀ i, MeasurableSet (cell i))
    (hdisj : Pairwise (Function.onFun Disjoint cell))
    (hcover : (⋃ i, cell i) =ᵐ[mu] Q) (f : X → ENNReal)
    (E : I → ℝ) (hE : ∀ i, 0 ≤ E i)
    (hbound : ∀ i, (mu.restrict Q).withDensity f (cell i) ≤ ENNReal.ofReal (E i)) :
    (mu.restrict Q).withDensity f Set.univ ≤ ENNReal.ofReal (∑ i, E i) := by
  have heq := withDensity_eq_sum_restrict_of_partition mu Q cell hle hcell hdisj hcover f
  rw [heq, Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  simp only [Measure.restrict_apply_univ]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hE i)]
  exact Finset.sum_le_sum (fun i _ => hbound i)

end SubdiffusiveProcess
