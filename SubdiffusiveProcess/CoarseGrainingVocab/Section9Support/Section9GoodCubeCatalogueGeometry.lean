import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubePhysicalMass
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryScales
/-!
# Physical geometry of a finite depth catalogue

Reference cubes of side `3^-k` become exact integer-scale physical cubes under
native dilation. Containment, the common volume floor, and the conversion to
natural scales above a fixed maximum depth are retained explicitly.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open Set MeasureTheory SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
attribute [local instance] Classical.propDecidable

/-- The physical catalogue cube is the exact affine image of its reference cube. -/
theorem goodCube_catalogue_cube_eq_affine
    {d : ℕ} (n k : ℕ) (x : Vec d) :
    (((3 : ℝ) ^ n • x, (3 : ℝ) ^ ((n : ℤ) - k)) : Cube d) =
      affineCubeTransport 0 ((3 : ℝ) ^ n) (x, (3 : ℝ) ^ (-(k : ℤ))) := by
  simp only [affineCubeTransport, zero_add, (goodCube_native_depth_scales n k k le_rfl).1]

/-- Reference-frame points translate into the physical catalogue cube. -/
theorem goodCube_catalogue_pullback_mem_physical
    {d : ℕ} (n k : ℕ) (x u : Vec d)
    (hu : u ∈ openCubeSet (originCube d ((n : ℤ) - k))) :
    u + (3 : ℝ) ^ n • x ∈
      cubeSet ((3 : ℝ) ^ n • x, (3 : ℝ) ^ ((n : ℤ) - k)) := by
  rw [← translatedCube_eq_cubeSet]
  exact ⟨u, hu, add_comm _ _⟩

/-- A reference cube contained in the unit cube stays inside the native parent. -/
theorem goodCube_catalogue_cube_subset_parent
    {d : ℕ} (n k : ℕ) (x : Vec d)
    (hinside : cubeSet (x, (3 : ℝ) ^ (-(k : ℤ))) ⊆ cubeSet ((0 : Vec d), (1 : ℝ))) :
    cubeSet ((3 : ℝ) ^ n • x, (3 : ℝ) ^ ((n : ℤ) - k)) ⊆
      cubeSet ((0 : Vec d), (3 : ℝ) ^ n) := by
  have hs : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hunit : affineCubeTransport (0 : Vec d) ((3 : ℝ) ^ n) ((0 : Vec d), (1 : ℝ)) =
      ((0 : Vec d), (3 : ℝ) ^ n) := by simp [affineCubeTransport]
  rw [goodCube_catalogue_cube_eq_affine, ← hunit,
    cubeSet_affineCubeTransport _ hs, cubeSet_affineCubeTransport _ hs]
  exact Set.image_mono hinside

/-- Bounded reference depths give the actual physical volume floor at every native scale. -/
theorem goodCube_catalogue_volume_floor
    {d : ℕ} (n J k l : ℕ) (x y : Vec d) (hk : k ≤ J) (hl : l ≤ J) :
    ENNReal.ofReal (((3 : ℝ) ^ (-(J : ℤ))) ^ d) *
      volume (cubeSet ((3 : ℝ) ^ n • y, (3 : ℝ) ^ ((n : ℤ) - l))) ≤
        volume (cubeSet ((3 : ℝ) ^ n • x, (3 : ℝ) ^ ((n : ℤ) - k))) := by
  have h3 : (1 : ℝ) < 3 := by norm_num
  have hs : (0 : ℝ) < (3 : ℝ) ^ n := pow_pos (by norm_num : (0 : ℝ) < 3) n
  have hell : (0 : ℝ) < (3 : ℝ) ^ (-(J : ℤ)) := zpow_pos (by norm_num) _
  have hQ : (3 : ℝ) ^ (-(J : ℤ)) ≤ (3 : ℝ) ^ (-(k : ℤ)) :=
    (zpow_le_zpow_iff_right₀ h3).2 (by omega)
  have hR0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(l : ℤ)) := zpow_nonneg (by norm_num) _
  have hR1 : (3 : ℝ) ^ (-(l : ℤ)) ≤ 1 := (zpow_le_one_iff_right₀ h3).2 (by omega)
  have hQ' : affineCubeTransport (0 : Vec d) ((3 : ℝ) ^ n) (x, (3 : ℝ) ^ (-(k : ℤ)))
      = ((3 : ℝ) ^ n • x, (3 : ℝ) ^ ((n : ℤ) - k)) := by
    simp only [affineCubeTransport, zero_add, (goodCube_native_depth_scales n k J hk).1]
  have hR' : affineCubeTransport (0 : Vec d) ((3 : ℝ) ^ n) (y, (3 : ℝ) ^ (-(l : ℤ)))
      = ((3 : ℝ) ^ n • y, (3 : ℝ) ^ ((n : ℤ) - l)) := by
    simp only [affineCubeTransport, zero_add, (goodCube_native_depth_scales n l J hl).1]
  have hvol := goodCube_affine_volume_floor
    (Q := (x, (3 : ℝ) ^ (-(k : ℤ)))) (R := (y, (3 : ℝ) ^ (-(l : ℤ)))) (0 : Vec d)
    hs hell hQ hR0 hR1
  rw [hR', hQ'] at hvol
  exact hvol

/-- Above the catalogue depth, all native scales are nonnegative and the
finite image has the required cardinality and depth bounds. -/
theorem goodCube_catalogue_positive_indices
    {d : ℕ} (n J N : ℕ) (hn : J ≤ n) (G : Finset (ℕ × Vec d))
    (hcard : G.card ≤ N) (hdepth : ∀ q ∈ G, q.1 ≤ J) :
    let F := G.image (fun q => (n - q.1, (3 : ℝ) ^ n • q.2))
    F.card ≤ N ∧ (∀ q ∈ F, q.1 ≤ n ∧ n - q.1 ≤ J) ∧
      ∀ q ∈ G, (n : ℤ) - q.1 = ((n - q.1 : ℕ) : ℤ) ∧
        (3 : ℝ) ^ ((n : ℤ) - q.1) = (3 : ℝ) ^ (n - q.1) := by
  refine ⟨Finset.card_image_le.trans hcard, ?_, ?_⟩
  · intro q hq
    rcases Finset.mem_image.1 hq with ⟨p, hp, rfl⟩
    have hpJ : p.1 ≤ J := hdepth p hp
    refine ⟨Nat.sub_le n p.1, ?_⟩
    show n - (n - p.1) ≤ J
    omega
  · intro q hq
    have hqn : q.1 ≤ n := (hdepth q hq).trans hn
    have h1 : ((n : ℤ) - q.1) = ((n - q.1 : ℕ) : ℤ) := (Int.ofNat_sub hqn).symm
    refine ⟨h1, ?_⟩
    rw [h1]
    exact zpow_natCast _ _

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
