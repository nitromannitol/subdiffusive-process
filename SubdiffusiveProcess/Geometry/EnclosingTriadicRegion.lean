module

public import SubdiffusiveProcess.Geometry.RationalTriadicCatalogue
public import SubdiffusiveProcess.Lane4.Bridge

@[expose] public section

open Set SubdiffusiveProcess
noncomputable section
namespace SubdiffusiveProcess.Geometry

/-- A cube with arbitrary centre fits in a calibration root and a bounded
region containing every unit neighbourhood of its closure. -/
theorem exists_enclosing_triadic_region {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ (Q : Homogenization.TriadicCube d) (Region : Set (SpatialCoordinates d)),
      Bornology.IsBounded Region ∧
      closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        closure (Homogenization.openCubeSet Q) ∧
      closure (Homogenization.openCubeSet Q) ⊆ Region ∧
      ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), Metric.ball x 1 ⊆ Region := by
  obtain ⟨m, hm⟩ := exists_triadic_root_for_prefix (fun _ => z) (fun _ => r) (fun _ => hr) 0
  let Q := Homogenization.originCube d (m : ℤ)
  have hzero : (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m)
      (pow_pos zero_lt_three m) : Set (SpatialCoordinates d)) = Homogenization.openCubeSet Q := by
    simpa only [Int.cast_natCast, zpow_natCast] using
      Lane4.centeredCube_zero_eq_openCubeSet_originCube (d := d) (m : ℤ)
        (zpow_pos zero_lt_three _)
  have hsub : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Q) := by
    have h := hm 0 le_rfl
    rw [hzero] at h
    exact h.trans subset_closure
  refine ⟨Q, Metric.cthickening 1 (closure (Homogenization.openCubeSet Q)),
    (Homogenization.isBounded_openCubeSet Q).closure.cthickening, hsub,
    Metric.self_subset_cthickening _, ?_⟩
  intro x hx y hy
  exact Metric.mem_cthickening_of_dist_le y x 1 _ (hsub hx) hy.le

/-- A catalogue side is either at most one or a positive integral power of three. -/
theorem rationalTriadicSide_small_or_large (d i : ℕ) :
    rationalTriadicSide d i ≤ 1 ∨ ∃ k : ℕ, 0 < k ∧ rationalTriadicSide d i = (3 : ℝ) ^ k := by
  let k := (rationalTriadicEnumeration d i).2
  by_cases hk : k ≤ 0
  · exact Or.inl (zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 3) hk)
  · have hkpos : 0 < k := lt_of_not_ge hk
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hkpos.le
    refine Or.inr ⟨n, by omega, ?_⟩
    change (3 : ℝ) ^ k = _
    rw [hn, zpow_natCast]

end SubdiffusiveProcess.Geometry
