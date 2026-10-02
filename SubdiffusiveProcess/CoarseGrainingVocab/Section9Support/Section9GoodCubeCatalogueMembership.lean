import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryScales
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReducedResidual
/-! The physical catalogue contains every original cube, the parent, and a subcube of its middle quarter, at every integer native scale. -/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
theorem goodCube_native_catalogue_memberships
    {d : ℕ} (Qfam0 : Set (Cube d))
    (hunit : ((0 : Vec d), (1 : ℝ)) ∈ Qfam0)
    (depth : Qfam0 → ℕ)
    (hdepth : ∀ Q : Qfam0, Q.val.2 = (3 : ℝ)^(-(depth Q : ℤ)))
    (G : Finset (ℕ × Vec d))
    (hGorig : ∀ Q : Qfam0, (depth Q, Q.val.1) ∈ G)
    (hGquarter : (2, (0 : Vec d)) ∈ G) (n : ℕ) (z : Lattice d) :
    let Gn := G.image (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ)^n • q.2))
    (∀ Q ∈ goodCubeReferenceFamily Qfam0 n z,
      ∃ q ∈ Gn, ((q.2, (3 : ℝ)^q.1) : Cube d) = Q) ∧
      (∃ q ∈ Gn, ((q.2, (3 : ℝ)^q.1) : Cube d) =
        (goodCubeCentre n z, (3 : ℝ)^n)) ∧
      ∃ q ∈ Gn, cubeSet (q.2, (3 : ℝ)^q.1) ⊆
        middleQuarter (goodCubeCentre n z, (3 : ℝ)^n) := by
  classical
  dsimp only
  have hfamily : ∀ Q ∈ goodCubeReferenceFamily Qfam0 n z,
      ∃ q ∈ G.image (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ)^n • q.2)),
        ((q.2, (3 : ℝ)^q.1) : Cube d) = Q := by
    intro Q hQ
    obtain ⟨R, hR, rfl⟩ := hQ
    refine ⟨((n : ℤ) - depth ⟨R, hR⟩, goodCubeCentre n z + (3 : ℝ)^n • R.1),
      Finset.mem_image.mpr ⟨(depth ⟨R, hR⟩, R.1), hGorig ⟨R, hR⟩, rfl⟩, ?_⟩
    apply Prod.ext
    · rfl
    · change (3 : ℝ)^((n : ℤ) - depth ⟨R, hR⟩) = (3 : ℝ)^n * R.2
      rw [hdepth ⟨R, hR⟩]
      exact (goodCube_native_depth_scales n (depth ⟨R, hR⟩) (depth ⟨R, hR⟩) le_rfl).1.symm
  refine ⟨hfamily, hfamily _ (parent_mem_transported_family
    (by simpa only [pow_zero] using hunit) n z), ?_⟩
  refine ⟨((n : ℤ) - (2 : ℕ), goodCubeCentre n z + (3 : ℝ)^n • (0 : Vec d)),
    Finset.mem_image.mpr ⟨(2, (0 : Vec d)), hGquarter, rfl⟩, ?_⟩
  simp only [smul_zero, add_zero]
  change centeredAxisCube (goodCubeCentre n z) ((3 : ℝ)^((n : ℤ) - (2 : ℕ))) ⊆
    centeredAxisCube (goodCubeCentre n z) ((3 : ℝ)^n / 4)
  apply centeredAxisCube_mono
  rw [← (goodCube_native_depth_scales n 2 2 (le_refl 2)).1]
  calc
    (3 : ℝ)^n * (3 : ℝ)^(-(2 : ℤ)) ≤ (3 : ℝ)^n * (1 / 4) :=
      mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
    _ = (3 : ℝ)^n / 4 := by ring
end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
