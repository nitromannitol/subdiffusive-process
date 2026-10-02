import SubdiffusiveProcess.Geometry.TriadicObservationPlanes
import SubdiffusiveProcess.Geometry.TriadicAdaptive

/-! # The unresolved remainder relative to an observation cube

The family is filtered on the original global grid by its actual ancestor.
Its exact local-grid image permits the existing midplane count to be used
with the observation volume, rather than the outer-root volume.
-/
open MeasureTheory Set TopologicalSpace Filter
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- Original-grid unresolved descendants of one actual observation label. -/
def triadicObservationUnresolvedLabels (N J : ℕ) (I : Finset (Fin d))
    (k : OddGridIndex d (triadicHalf N)) : Finset (OddGridIndex d (triadicHalf (N + J))) :=
  (oddGridUnresolved (triadicHalf (N + J)) I).filter (fun q => triadicAncestor N J q = k)

/-- The filtered global family is exactly the image of its local unresolved labels. -/
theorem triadicObservationUnresolvedLabels_eq_image (N J : ℕ) (I : Finset (Fin d))
    (k : OddGridIndex d (triadicHalf N)) :
    triadicObservationUnresolvedLabels N J I k =
      (oddGridUnresolved (triadicHalf J) (triadicObservationPlanes N I k)).image
        (triadicDescendant N J k) := by
  ext q
  simp only [triadicObservationUnresolvedLabels, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hq, hk⟩
    have he : triadicDescendant N J k (triadicDescendantLabel N J q) = q := by
      simpa only [hk] using triadicDescendant_ancestor_label N J q
    refine ⟨triadicDescendantLabel N J q, ?_, he⟩
    apply (triadicDescendant_mem_unresolved_iff N J I k _).mp
    simpa only [he] using hq
  · rintro ⟨l, hl, rfl⟩
    exact ⟨(triadicDescendant_mem_unresolved_iff N J I k l).mpr hl,
      triadicAncestor_descendant N J k l⟩

/-- The actual original-grid unresolved region inside one observation cube. -/
def triadicObservationUnresolvedRegion (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (N J : ℕ) (I : Finset (Fin d)) (k : OddGridIndex d (triadicHalf N)) :
    Set (SpatialCoordinates d) :=
  ⋃ q ∈ triadicObservationUnresolvedLabels N J I k,
    (oddGridCell z r hr (triadicHalf (N + J)) q : Set (SpatialCoordinates d))

/-- The filtered global region equals the literal local unresolved region of the observation cube. -/
theorem triadicObservationUnresolvedRegion_eq (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (N J : ℕ) (I : Finset (Fin d))
    (k : OddGridIndex d (triadicHalf N)) :
    triadicObservationUnresolvedRegion z r hr N J I k =
      triadicUnresolvedRegion (oddGridCenter z r (triadicHalf N) k)
        (r / (2 * (triadicHalf N : ℝ) + 1)) (div_pos hr (by positivity))
        (triadicObservationPlanes N I k) J := by
  unfold triadicObservationUnresolvedRegion triadicUnresolvedRegion
  rw [triadicObservationUnresolvedLabels_eq_image]
  ext x
  simp only [mem_iUnion, Finset.mem_image]
  constructor
  · rintro ⟨q, ⟨l, hl, rfl⟩, hx⟩
    exact ⟨l, hl, by simpa only [triadicDescendant_cell] using hx⟩
  · rintro ⟨l, hl, hx⟩
    exact ⟨triadicDescendant N J k l, ⟨l, hl, rfl⟩,
      by simpa only [triadicDescendant_cell] using hx⟩

/-- The actual unresolved fraction is bounded relative to its observation cube. -/
theorem triadicObservationUnresolved_volume_fraction_le (hd : 0 < d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (N J : ℕ)
    (I : Finset (Fin d)) (k : OddGridIndex d (triadicHalf N)) :
    volume.real (triadicObservationUnresolvedRegion z r hr N J I k) /
      volume.real (oddGridCell z r hr (triadicHalf N) k : Set (SpatialCoordinates d)) ≤
        (d : ℝ) / (3 : ℝ) ^ J := by
  rw [triadicObservationUnresolvedRegion_eq]
  exact triadicUnresolved_volume_fraction_le hd _ (div_pos hr (by positivity)) _ J

/-- At a fixed observation cube the actual relative unresolved volume tends to zero. -/
theorem triadicObservationUnresolved_volume_fraction_tendsto_zero (hd : 0 < d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (N : ℕ)
    (I : Finset (Fin d)) (k : OddGridIndex d (triadicHalf N)) :
    Tendsto (fun J : ℕ => volume.real (triadicObservationUnresolvedRegion z r hr N J I k) /
      volume.real (oddGridCell z r hr (triadicHalf N) k : Set (SpatialCoordinates d)))
      atTop (𝓝 0) := by
  simp_rw [triadicObservationUnresolvedRegion_eq]
  exact triadicUnresolved_volume_fraction_tendsto_zero hd _ (div_pos hr (by positivity)) _

end SubdiffusiveProcess
