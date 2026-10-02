import SubdiffusiveProcess.Main.CubeSmoothFractionalL2Tests
import SubdiffusiveProcess.Geometry.UpstreamCube
import Mathlib.Geometry.Manifold.PartitionOfUnity

open MeasureTheory Set TopologicalSpace
open scoped ENNReal ContDiff Manifold

namespace SubdiffusiveProcess

/-- Smoothness on a neighborhood of the closed cube gives the same fractional test
classes as global smoothness, by a smooth cutoff equal to one on the cube. -/
theorem mem_cubeSmoothFractionalL2Tests_iff_global_representative
    {d : ℕ} (hd : 2 ≤ d) (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (s : Set.Ioo (0 : ℝ) 1)
    (u : CubeFractionalL2 (k := d) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s) :
    u ∈ cubeSmoothFractionalL2Tests hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s ↔
      ∃ f : SpatialCoordinates d → Fin d → ℝ,
        ContDiff ℝ ∞ f ∧
        ∀ i : Fin d, (u.val i : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube (Homogenization.cubeCenter Q)
            (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d))]
          (fun x => f x i) := by
  let z : SpatialCoordinates d := Homogenization.cubeCenter Q
  let r : ℝ := Homogenization.cubeScaleFactor Q
  let K : Set (SpatialCoordinates d) := closure (centeredCube z r hr : Set (SpatialCoordinates d))
  constructor
  · intro hu
    change ∃ (O : Opens (SpatialCoordinates d)) (f : SpatialCoordinates d → Fin d → ℝ),
      closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ O ∧
        ContDiffOn ℝ ∞ f (O : Set (SpatialCoordinates d)) ∧
          ∀ i : Fin d, (u.val i : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
            (fun x => f x i) at hu
    obtain ⟨O, g, hK_O, hg, hu⟩ := hu
    obtain ⟨L, hL_compact, hL_closed, hK_intL, hL_O⟩ :=
      exists_compact_closed_between
        ((centeredCube_isBounded z hr).isCompact_closure)
        O.isOpen hK_O
    obtain ⟨χ, hχ_one, hχ_zero, hχ_range⟩ :=
      exists_smooth_one_nhds_of_subset_interior (𝓘(ℝ, SpatialCoordinates d))
        (isClosed_closure : IsClosed K) hK_intL
    let f : SpatialCoordinates d → Fin d → ℝ := fun x i => χ x * g x i
    have hχ_contDiff : ContDiff ℝ ∞ χ := χ.contMDiff.contDiff
    have hf_O : ContDiffOn ℝ ∞ f (O : Set (SpatialCoordinates d)) := by
      rw [contDiffOn_pi]
      intro i
      exact (hχ_contDiff.contDiffOn.mul ((contDiffOn_pi.mp hg) i))
    have hf_Lc : ContDiffOn ℝ ∞ f (L : Set (SpatialCoordinates d))ᶜ := by
      have hzero : ContDiffOn ℝ ∞ (fun _ : SpatialCoordinates d => (0 : Fin d → ℝ))
          (L : Set (SpatialCoordinates d))ᶜ := contDiffOn_const
      refine (contDiffOn_congr (f₁ := f)
        (f := fun _ : SpatialCoordinates d => (0 : Fin d → ℝ)) ?_).mpr hzero
      intro x hx
      funext i
      dsimp [f]
      rw [hχ_zero x hx]
      simp only [zero_mul]
    have hOLc : (O : Set (SpatialCoordinates d)) ∪ (L : Set (SpatialCoordinates d))ᶜ = Set.univ := by
      ext x
      by_cases hx : x ∈ (O : Set (SpatialCoordinates d))
      · simp only [mem_union, hx, true_or, mem_univ]
      · simp only [mem_union, hx, false_or, mem_compl_iff]
        constructor
        · intro
          trivial
        · intro _ hxL
          exact hx (hL_O hxL)
    refine ⟨f, contDiff_of_contDiffOn_union_of_isOpen hf_O hf_Lc hOLc O.isOpen hL_closed.isOpen_compl, ?_⟩
    intro i
    filter_upwards [hu i,
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hx_cube
    have hxK : x ∈ K := subset_closure hx_cube
    have hχx : χ x = 1 := hχ_one.self_of_nhdsSet x hxK
    dsimp [f]
    rw [hχx, one_mul]
    exact hx
  · rintro ⟨f, hf, hu⟩
    change ∃ (O : Opens (SpatialCoordinates d)) (g : SpatialCoordinates d → Fin d → ℝ),
      closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ O ∧
        ContDiffOn ℝ ∞ g (O : Set (SpatialCoordinates d)) ∧
          ∀ i : Fin d, (u.val i : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
            (fun x => g x i)
    refine ⟨(⊤ : Opens (SpatialCoordinates d)), f, ?_, hf.contDiffOn, hu⟩
    exact subset_univ _

end SubdiffusiveProcess
