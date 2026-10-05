module

public import SubdiffusiveProcess.Paper.inputs_classical_piecewise_ascoli
public import SubdiffusiveProcess.Paper.prop_regularity_mesh_core
public import SubdiffusiveProcess.Geometry.ClosedOddGridCover

@[expose] public section




set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Cellwise bounded Holder norms on one finite odd grid yield uniform subsequential compactness on the parent cube. -/
theorem prop_conc_mesh_compactness
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (J : ℕ)
    (f : ℕ → SpatialCoordinates d → ℝ)
    (hcont : ∀ n, ContinuousOn (f n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (alpha : ℝ) (ha : 0 < alpha)
    (B : OddGridIndex d (triadicHalf J) → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hholder : ∀ i n, IsHolderOn alpha
      (closure (oddGridCell z r hr (triadicHalf J) i : Set (SpatialCoordinates d))) (f n))
    (hnorm : ∀ i n, cAlphaNorm alpha
      (closure (oddGridCell z r hr (triadicHalf J) i : Set (SpatialCoordinates d))) (f n) ≤ B i) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧
      ∃ g : C(closure (centeredCube z r hr : Set (SpatialCoordinates d)), ℝ),
        TendstoUniformly (fun n x => f (seq n) x.val) (fun x => g x) atTop := by
  let X := closure (centeredCube z r hr : Set (SpatialCoordinates d))
  have compactParent : CompactSpace X :=
    isCompact_iff_compactSpace.mp (lane2_isCompact_closure_centeredCube z hr)
  let A : OddGridIndex d (triadicHalf J) → Set X := fun i =>
    {x | x.val ∈ closure (oddGridCell z r hr (triadicHalf J) i : Set (SpatialCoordinates d))}
  have hclosed : ∀ i, IsClosed (A i) := fun _ =>
    isClosed_closure.preimage continuous_subtype_val
  have hcover : ∀ x : X, ∃ i, x ∈ A i := by
    intro x
    have hx := x.property
    change x.val ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) at hx
    rw [← oddGridCell_closure_iUnion_eq_closure_centeredCube z hr (triadicHalf J)] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨i, hi⟩
  have hlocal : ∀ i, ∃ C : ℝ, 0 ≤ C ∧
      (∀ n (x : X), x ∈ A i → |f n x.val| ≤ C) ∧
      (∀ n (x : X), x ∈ A i → ∀ y : X, y ∈ A i →
        |f n x.val - f n y.val| ≤ C * dist x y ^ alpha) := by
    intro i
    let C := max (B i) (B i * (Real.sqrt (d : ℝ)) ^ alpha)
    refine ⟨C, (hB i).trans (le_max_left _ _), ?_, ?_⟩
    · intro n x hx
      have hc := (hcont n).mono (lane2_closure_oddGridCell_subset z hr (triadicHalf J) i)
      have hb : BddAbove {v : ℝ | ∃ y ∈
          closure (oddGridCell z r hr (triadicHalf J) i : Set (SpatialCoordinates d)),
          v = |f n y|} := by
        obtain ⟨D, hD⟩ := (lane2_isCompact_closure_centeredCube _
          (div_pos hr (by positivity))).exists_bound_of_continuousOn hc
        refine ⟨D, ?_⟩
        rintro v ⟨y, hy, rfl⟩
        simpa only [Real.norm_eq_abs] using hD y hy
      exact (le_csSup hb ⟨x.val, hx, rfl⟩).trans
        ((aux_prop_regularity_mesh_core_sup_le_cAlphaNorm.trans (hnorm i n)).trans (le_max_left _ _))
    · intro n x hx y hy
      have h := aux_prop_regularity_mesh_core_holder_dist_bound hd ha.le (hholder i n)
        (hB i) (hnorm i n) x.val hx y.val hy
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg dist_nonneg _))
  obtain ⟨seq, hseq, g, hg, hlim⟩ := inputs_classical_piecewise_ascoli A hclosed hcover
    (fun n x => f n x.val) (fun n => continuousOn_iff_continuous_domRestrict.mp (hcont n)) alpha ha hlocal
  exact ⟨seq, hseq, ⟨g, hg⟩, hlim⟩

end
end SubdiffusiveProcess.Paper
