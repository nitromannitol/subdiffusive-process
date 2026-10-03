module

public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.Geometry.RationalTriadicCatalogue
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Instances.Rat

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess
open scoped Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- A closed mesh cell has diameter at most its side. -/
theorem aux_in_represented_cutoff_geometry_cell_dist
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (J : ℕ) (idx : OddGridIndex d (triadicHalf J))
    {x y : SpatialCoordinates d}
    (hx : x ∈ closure (oddGridCell z R hR (triadicHalf J) idx : Set (SpatialCoordinates d)))
    (hy : y ∈ closure (oddGridCell z R hR (triadicHalf J) idx : Set (SpatialCoordinates d))) :
    dist x y ≤ R / (3 : ℝ) ^ J := by
  have hx' := Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hx)
  have hy' := Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hy)
  have ht := dist_triangle x (oddGridCenter z R (triadicHalf J) idx) y
  rw [dist_comm (oddGridCenter z R (triadicHalf J) idx) y] at ht
  have hh : 2 * (triadicHalf J : ℝ) + 1 = (3 : ℝ) ^ J := by
    exact_mod_cast two_mul_triadicHalf_add_one J
  change dist x (oddGridCenter z R (triadicHalf J) idx) ≤
    R / (2 * (triadicHalf J : ℝ) + 1) / 2 at hx'
  change dist y (oddGridCenter z R (triadicHalf J) idx) ≤
    R / (2 * (triadicHalf J : ℝ) + 1) / 2 at hy'
  rw [hh] at hx' hy'
  linarith

/-- Fine enough meshes confine every plateau transition cell to O minus K. -/
theorem aux_in_represented_cutoff_geometry_transition
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (K O W : Set (SpatialCoordinates d))
    (hK : IsCompact K) (hO : IsOpen O) (hW : IsOpen W) (hKW : K ⊆ W)
    (theta : SpatialCoordinates d → ℝ) (hcomp : HasCompactSupport theta)
    (hsupp : tsupport theta ⊆ O) (hone : ∀ x ∈ W, theta x = 1) :
    ∃ J : ℕ, ∀ idx : OddGridIndex d (triadicHalf J),
      (closure (oddGridCell z R hR (triadicHalf J) idx : Set (SpatialCoordinates d)) ∩
        {x | 0 < theta x ∧ theta x < 1}).Nonempty →
      closure (oddGridCell z R hR (triadicHalf J) idx : Set (SpatialCoordinates d)) ⊆ O \ K := by
  obtain ⟨eps1, heps1, ht1⟩ := hcomp.exists_thickening_subset_open hO hsupp
  obtain ⟨eps2, heps2, ht2⟩ := hK.exists_thickening_subset_open hW hKW
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (R / min eps1 eps2)
    (by norm_num : (1 : ℝ) < 3)
  have hsmall : R / (3 : ℝ) ^ J < min eps1 eps2 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ J)).mpr
    have hm : 0 < min eps1 eps2 := lt_min heps1 heps2
    have h := (div_lt_iff₀ hm).mp hJ
    nlinarith
  refine ⟨J, fun idx ⟨x, hx, htx⟩ y hy => ⟨?_, ?_⟩⟩
  · apply ht1
    apply Metric.mem_thickening_iff.mpr
    refine ⟨x, subset_tsupport _ (ne_of_gt htx.1), ?_⟩
    exact (aux_in_represented_cutoff_geometry_cell_dist z R hR J idx hy hx).trans_lt
      (hsmall.trans_le (min_le_left _ _))
  · intro hyK
    have hxW : x ∈ W := ht2 (Metric.mem_thickening_iff.mpr
      ⟨y, hyK, (aux_in_represented_cutoff_geometry_cell_dist z R hR J idx hx hy).trans_lt
        (hsmall.trans_le (min_le_right _ _))⟩)
    have h := hone x hxW
    linarith [htx.2]

/-- Rational-centred triadic cubes form a neighbourhood basis with closure control. -/
theorem aux_in_represented_cutoff_geometry_basis
    {d : ℕ} (x : SpatialCoordinates d) (O : Set (SpatialCoordinates d))
    (hO : IsOpen O) (hx : x ∈ O) :
    ∃ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      (∀ i : Fin d, ∃ q : ℚ, z i = (q : ℝ)) ∧ (∃ m : ℤ, r = (3 : ℝ) ^ m) ∧
      x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ O := by
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hO x hx
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (1 / eps) (by norm_num : (1 : ℝ) < 3)
  let r : ℝ := (3 : ℝ) ^ (-(J : ℤ))
  have hr : 0 < r := zpow_pos (by norm_num) _
  have hre : r < eps := by
    dsimp [r]
    rw [zpow_neg, zpow_natCast]
    rw [← one_div]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ J)).mpr
    have h := (div_lt_iff₀ heps).mp hJ
    nlinarith
  have hrat : ∀ i : Fin d, ∃ q : ℚ, dist (x i) (q : ℝ) < r / 4 := by
    intro i
    exact Rat.denseRange_cast.exists_dist_lt (x i) (by positivity)
  choose q hq using hrat
  let z : SpatialCoordinates d := fun i => (q i : ℝ)
  have hdist : dist x z < r / 4 := (dist_pi_lt_iff (by positivity)).mpr hq
  refine ⟨z, r, hr, fun i => ⟨q i, rfl⟩, ⟨-(J : ℤ), rfl⟩, ?_, ?_⟩
  · exact Metric.mem_ball.mpr (by linarith)
  · intro y hy
    apply hball
    have hyz := Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hy)
    have ht := dist_triangle y z x
    rw [dist_comm z x] at ht
    exact Metric.mem_ball.mpr (by linarith)

/-- A compact set has a finite catalogue cover whose closed cubes stay in the given open set. -/
theorem aux_in_represented_cutoff_geometry_finite_cover
    {d : ℕ} {J : Type} [DecidableEq J]
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (root : J)
    (hcomplete : ∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (∀ i : Fin d, ∃ q : ℚ, z' i = (q : ℝ)) → (∃ m : ℤ, r' = (3 : ℝ) ^ m) →
      (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)) →
      ∃ j : J, z j = z' ∧ r j = r')
    (K O : Set (SpatialCoordinates d)) (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O)
    (hOR : O ⊆ (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d))) :
    ∃ s : Finset J,
      K ⊆ ⋃ j ∈ s, (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ∧
      (⋃ j ∈ s, closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) ⊆ O := by
  classical
  let Good := {j : J // closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ⊆ O}
  have hcover : K ⊆ ⋃ j : Good,
      (centeredCube (z j.val) (r j.val) (hr j.val) : Set (SpatialCoordinates d)) := by
    intro x hx
    obtain ⟨zc, rc, hrc, hzrat, hrtri, hxc, hcl⟩ :=
      aux_in_represented_cutoff_geometry_basis x O hO (hKO hx)
    obtain ⟨j, hjz, hjr⟩ := hcomplete zc rc hrc hzrat hrtri
      (subset_closure.trans (hcl.trans hOR))
    have heq : (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) =
        (centeredCube zc rc hrc : Set (SpatialCoordinates d)) := by
      simp only [centeredCube, hjz, hjr]
    have hjgood : closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ⊆ O := by
      rwa [heq]
    exact mem_iUnion.mpr ⟨⟨j, hjgood⟩, by simpa only [heq] using hxc⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun j : Good => (centeredCube (z j.val) (r j.val) (hr j.val) : Set (SpatialCoordinates d)))
    (fun j => (centeredCube (z j.val) (r j.val) (hr j.val)).isOpen) hcover
  refine ⟨s.image Subtype.val, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion₂.mpr ⟨j.val, Finset.mem_image.mpr ⟨j, hj, rfl⟩, hxj⟩
  · intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
    obtain ⟨jc, _, rfl⟩ := Finset.mem_image.mp hj
    exact jc.property hxj

/-- Catalogue plateaus and finite meshes supply the geometry for an arbitrary compact/open cutoff. -/
theorem in_represented_cutoff_geometry
    {d : ℕ} {J : Type} [DecidableEq J]
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (root j0 : J) (T : Type) (theta : T → SpatialCoordinates d → ℝ)
    (hroot : (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
    (hcomplete : ∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (∀ i : Fin d, ∃ q : ℚ, z' i = (q : ℝ)) → (∃ m : ℤ, r' = (3 : ℝ) ^ m) →
      (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)) →
      ∃ j : J, z j = z' ∧ r j = r')
    (hplateau : ∀ s o : Finset J,
      (⋃ k ∈ s, closure (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ⊆
        (⋃ k ∈ o, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) →
      closure (⋃ k ∈ o, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ⊆
        (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d)) →
      ∃ b : T, ∃ W : Set (SpatialCoordinates d), IsOpen W ∧
        (⋃ k ∈ s, closure (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ⊆ W ∧
        W ⊆ (⋃ k ∈ o, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ∧
        (∀ x, 0 ≤ theta b x ∧ theta b x ≤ 1) ∧ (∀ x ∈ W, theta b x = 1) ∧
        tsupport (theta b) ⊆ (⋃ k ∈ o,
          (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))))
    (K O : Set (SpatialCoordinates d)) (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hOQ : closure O ⊆ (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d))) :
    ∃ (b : T) (W : Set (SpatialCoordinates d)) (Jmesh : ℕ),
      IsOpen W ∧ K ⊆ W ∧ W ⊆ O ∧
      (∀ x, 0 ≤ theta b x ∧ theta b x ≤ 1) ∧ (∀ x ∈ W, theta b x = 1) ∧
      tsupport (theta b) ⊆ O ∧
      ∀ idx : OddGridIndex d (triadicHalf Jmesh),
        (closure (oddGridCell (z j0) (r j0) (hr j0) (triadicHalf Jmesh) idx :
            Set (SpatialCoordinates d)) ∩ {x | 0 < theta b x ∧ theta b x < 1}).Nonempty →
        closure (oddGridCell (z j0) (r j0) (hr j0) (triadicHalf Jmesh) idx :
            Set (SpatialCoordinates d)) ⊆ O \ K := by
  classical
  have hOR := subset_closure.trans (hOQ.trans hroot)
  obtain ⟨s, hsK, hsO⟩ := aux_in_represented_cutoff_geometry_finite_cover
    z r hr root hcomplete K O hK hO hKO hOR
  let K' := ⋃ j ∈ s, closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))
  have hK' : IsCompact K' := s.isCompact_biUnion fun j _ =>
    (centeredCube_isBounded (z j) (hr j)).isCompact_closure
  have hKK' : K ⊆ K' := hsK.trans (iUnion₂_mono fun j _ => subset_closure)
  obtain ⟨o, hoK, hoO⟩ := aux_in_represented_cutoff_geometry_finite_cover
    z r hr root hcomplete K' O hK' hO hsO hOR
  have hoO' : (⋃ j ∈ o, (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) ⊆ O :=
    (iUnion₂_mono fun j _ => subset_closure).trans hoO
  have hclO : closure (⋃ j ∈ o,
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) ⊆ O := by
    have hc : IsClosed (⋃ j ∈ o,
        closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) :=
      isClosed_biUnion_finset (fun _ _ => isClosed_closure)
    have hs : (⋃ j ∈ o, (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) ⊆
        (⋃ j ∈ o, closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) :=
      iUnion₂_mono fun j _ => subset_closure
    exact (closure_minimal hs hc).trans hoO
  obtain ⟨b, W, hW, hKW, hWO, hrange, hone, hsupp⟩ :=
    hplateau s o hoK (hclO.trans (subset_closure.trans hOQ))
  have hcompact : HasCompactSupport (theta b) :=
    ((centeredCube_isBounded (z j0) (hr j0)).isCompact_closure).of_isClosed_subset
      (isClosed_tsupport _) (hsupp.trans (hoO'.trans (subset_closure.trans (hOQ.trans subset_closure))))
  obtain ⟨Jmesh, hmesh⟩ := aux_in_represented_cutoff_geometry_transition
    (z j0) (r j0) (hr j0) K O W hK hO hW (hKK'.trans hKW)
    (theta b) hcompact (hsupp.trans hoO') hone
  exact ⟨b, W, Jmesh, hW, hKK'.trans hKW, hWO.trans hoO', hrange, hone,
    hsupp.trans hoO', hmesh⟩

end Paper

