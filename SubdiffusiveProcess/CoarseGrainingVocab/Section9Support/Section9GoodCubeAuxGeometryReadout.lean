import Homogenization.Sobolev.Foundations.Cutoff.Cube
import Homogenization.Geometry.Translation
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryComplete
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryPairs
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryTransport




set_option autoImplicit false
open Set MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Compact inclusion is equivalent before and after any positive affine cube transport. -/
theorem goodCube_compactlyInside_affine_iff {d : ℕ} (Q R : Cube d)
    (y : Vec d) {s : ℝ} (hs : 0 < s) :
    CompactlyInside (affineCubeTransport y s Q) (affineCubeTransport y s R) ↔
      CompactlyInside Q R := by
  unfold CompactlyInside
  rw [cubeSet_affineCubeTransport y hs Q, cubeSet_affineCubeTransport y hs R,
    closure_image_affinePhi y hs.ne' (cubeSet Q),
    Set.image_subset_image_iff (affinePhi_injective y hs.ne')]

/-- The open concentric interior lies in the translated closed theta profile domain at every integer native scale. -/
theorem goodCube_centered_interior_subset_translated_profile {d : ℕ}
    (z : Vec d) (m : ℤ) {theta : ℝ} (_htheta : 0 < theta) :
    centeredAxisCube z (theta * (3 : ℝ) ^ m) ⊆
      Homogenization.translateSet z
        (Homogenization.scaledClosedCubeSet (Homogenization.originCube d m) theta) := by
  intro x hx
  rw [Homogenization.mem_translateSet_iff_sub_mem]
  intro i
  simp only [Pi.sub_apply]
  have hs : Homogenization.cubeScaleFactor (Homogenization.originCube d m) = (3 : ℝ) ^ m := rfl
  have hc : Homogenization.cubeCenter (Homogenization.originCube d m) i = 0 := by
    simp [Homogenization.cubeCenter, Homogenization.originCube]
  have hr : Homogenization.cubeRadius (Homogenization.originCube d m) = (3 : ℝ) ^ m / 2 := by
    unfold Homogenization.cubeRadius
    rw [hs]
    ring
  have h := mem_centeredAxisCube.mp hx i
  simp only [hc, hr, sub_zero]
  have hring : theta * ((3 : ℝ) ^ m / 2) = theta * (3 : ℝ) ^ m / 2 := by
    ring
  rw [hring]
  exact le_of_lt h

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
