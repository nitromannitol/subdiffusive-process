module

public import SubdiffusiveProcess.Geometry.TriadicAdaptive

@[expose] public section

/-!
# The finite adaptive partition and its volume weights

Retained regions at different generations are disjoint. Together with
the final unresolved region they cover the root up to Lebesgue null sets.
Their weights are actual cube volumes; the fraction retained at generation
`J+1` is bounded by `d/3^J`.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- Unresolved regions shrink at every pair of ordered depths. -/
theorem triadicUnresolvedRegion_antitone (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (I : Finset (Fin d)) : Antitone (triadicUnresolvedRegion z r hr I) :=
  antitone_nat_of_succ_le (triadicUnresolvedRegion_succ_subset z hr I)

/-- A retained generation is disjoint from all later unresolved regions. -/
theorem triadicRetainedRegion_disjoint_unresolved (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (I : Finset (Fin d)) {j J : ℕ} (hj : j < J) :
    Disjoint (triadicRetainedRegion z r hr I j) (triadicUnresolvedRegion z r hr I J) :=
  (triadicRetainedRegion_disjoint_next z hr I j).mono_right
    (triadicUnresolvedRegion_antitone z hr I (Nat.succ_le_of_lt hj))

/-- Actual retained regions from distinct generations are disjoint. -/
theorem triadicRetainedRegion_pairwiseDisjoint (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (I : Finset (Fin d)) :
    Pairwise (fun j J => Disjoint (triadicRetainedRegion z r hr I j)
      (triadicRetainedRegion z r hr I J)) := by
  intro j J h
  rcases lt_or_gt_of_ne h with hj | hJ
  · exact (triadicRetainedRegion_disjoint_unresolved z hr I hj).mono_right
      (triadicRetainedRegion_subset_previous z hr I J)
  · exact ((triadicRetainedRegion_disjoint_unresolved z hr I hJ).mono_right
      (triadicRetainedRegion_subset_previous z hr I j)).symm

/-- Before any refinement, a nonempty active-plane set leaves the root unresolved. -/
theorem triadicUnresolvedRegion_zero (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) {I : Finset (Fin d)} (hI : I.Nonempty) :
    triadicUnresolvedRegion z r hr I 0 = (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  apply Subset.antisymm (triadicUnresolvedRegion_subset_root z hr I 0)
  intro x hx
  let k : OddGridIndex d (triadicHalf 0) := fun _ => ⟨0, by norm_num [triadicHalf]⟩
  have hk : k ∈ oddGridUnresolved (triadicHalf 0) I := by
    obtain ⟨i, hi⟩ := hI
    simp only [oddGridUnresolved, Finset.mem_biUnion, oddGridPlaneCells,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, hi, rfl⟩
  have hc : oddGridCell z r hr (triadicHalf 0) k = centeredCube z r hr := by
    have hz : oddGridCenter z r (triadicHalf 0) k = z := by
      funext i
      simp only [oddGridCenter, k, triadicHalf, pow_zero, Nat.reduceDiv,
        Nat.cast_zero, sub_self, zero_mul, add_zero]
    unfold oddGridCell
    rw [hz]
    congr 1
    norm_num [triadicHalf]
  exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, hc.symm ▸ hx⟩⟩

/-- Retained generations through `J`, together with the unresolved depth-`J` cells, cover the root. -/
theorem triadicAdaptive_partition_ae_eq (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) {I : Finset (Fin d)} (hI : I.Nonempty) (J : ℕ) :
    ((⋃ j ∈ Finset.range J, triadicRetainedRegion z r hr I j) ∪
      triadicUnresolvedRegion z r hr I J : Set (SpatialCoordinates d))
      =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  induction J with
  | zero =>
      simpa only [Finset.range_zero, Finset.notMem_empty, iUnion_of_empty,
        iUnion_empty, empty_union, triadicUnresolvedRegion_zero z hr hI]
        using (Filter.EventuallyEqSet.rfl : (centeredCube z r hr : Set (SpatialCoordinates d))
          =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d)))
  | succ J ih =>
      rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm (triadicRetainedRegion z r hr I J),
        union_assoc]
      exact ((Filter.EventuallyEqSet.rfl).union (triadicAdaptive_step_ae_eq z hr I J)).trans ih

/-- Actual unresolved regions are measurable. -/
theorem measurableSet_triadicUnresolvedRegion (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (I : Finset (Fin d)) (J : ℕ) :
    MeasurableSet (triadicUnresolvedRegion z r hr I J) :=
  MeasurableSet.iUnion (fun k => MeasurableSet.iUnion (fun _ =>
    (oddGridCell z r hr (triadicHalf J) k).isOpen.measurableSet))

/-- Actual retained regions are measurable. -/
theorem measurableSet_triadicRetainedRegion (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (I : Finset (Fin d)) (J : ℕ) :
    MeasurableSet (triadicRetainedRegion z r hr I J) :=
  MeasurableSet.iUnion (fun k => MeasurableSet.iUnion (fun _ =>
    (oddGridCell z r hr (triadicHalf (J + 1)) k).isOpen.measurableSet))

/-- The fraction first retained at generation `J+1` has the required geometric bound. -/
theorem triadicRetainedRegion_volume_fraction_le (hd : 0 < d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (I : Finset (Fin d)) (J : ℕ) :
    volume.real (triadicRetainedRegion z r hr I J) /
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) ≤ (d : ℝ) / (3 : ℝ)^J := by
  have hf : volume (triadicUnresolvedRegion z r hr I J) ≠ ∞ :=
    measure_ne_top_of_subset (triadicUnresolvedRegion_subset_root z hr I J)
      (by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top)
  apply (div_le_div_of_nonneg_right
    (measureReal_mono (triadicRetainedRegion_subset_previous z hr I J) hf)
    (centeredCube_volume_pos z hr).le).trans
  exact triadicUnresolved_volume_fraction_le hd z hr I J

/-- Retained volume plus the new unresolved volume equals the previous unresolved volume. -/
theorem triadicAdaptive_volume_step (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (I : Finset (Fin d)) (J : ℕ) :
    volume.real (triadicRetainedRegion z r hr I J) +
      volume.real (triadicUnresolvedRegion z r hr I (J + 1)) =
        volume.real (triadicUnresolvedRegion z r hr I J) := by
  have hf : volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ ∞ := by
    rw [centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  rw [← measureReal_union (triadicRetainedRegion_disjoint_next z hr I J)
    (measurableSet_triadicUnresolvedRegion z hr I (J + 1))
    (measure_ne_top_of_subset
      ((triadicRetainedRegion_subset_previous z hr I J).trans
        (triadicUnresolvedRegion_subset_root z hr I J)) hf)
    (measure_ne_top_of_subset (triadicUnresolvedRegion_subset_root z hr I (J + 1)) hf)]
  exact measureReal_congr (triadicAdaptive_step_ae_eq z hr I J)

/-- The finite adaptive partition's actual volume weights sum to one. -/
theorem triadicAdaptive_volume_weights_sum (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) {I : Finset (Fin d)} (hI : I.Nonempty) (J : ℕ) :
    (∑ j ∈ Finset.range J, volume.real (triadicRetainedRegion z r hr I j)) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) +
      volume.real (triadicUnresolvedRegion z r hr I J) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) = 1 := by
  have he : (∑ j ∈ Finset.range J, volume.real (triadicRetainedRegion z r hr I j)) +
      volume.real (triadicUnresolvedRegion z r hr I J) =
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    induction J with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_add,
        triadicUnresolvedRegion_zero z hr hI]
    | succ J ih =>
      rw [Finset.sum_range_succ, add_assoc, triadicAdaptive_volume_step, ih]
  rw [← add_div, he, div_self (ne_of_gt (centeredCube_volume_pos z hr))]

end SubdiffusiveProcess
