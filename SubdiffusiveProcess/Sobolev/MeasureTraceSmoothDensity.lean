module

public import SubdiffusiveProcess.Sobolev.ScalarFractionalSmoothDensity
public import SubdiffusiveProcess.Geometry.UpstreamCube
public import SubdiffusiveProcess.Main.HalfFractionalOrder

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal ContDiff
noncomputable section

namespace SubdiffusiveProcess

theorem contDiff_memLp_of_finiteMeasure_supported_closure {d : ℕ}
    (Q : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Q)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure (Homogenization.openCubeSet Q))ᶜ = 0)
    (g : SpatialCoordinates d → ℝ) (hg : ContDiff ℝ ∞ g) :
    MemLp g 2 ν := by
  have hK : IsCompact (closure (Homogenization.openCubeSet Q)) := by
    rw [← centeredCube_eq_openCubeSet Q hr]
    exact (centeredCube_isBounded (Homogenization.cubeCenter Q) hr).isCompact_closure
  have hcont : Continuous g := hg.continuous
  obtain ⟨C, hC⟩ := bddAbove_def.mp (hK.bddAbove_image hcont.norm.continuousOn)
  apply MemLp.of_bound hcont.aestronglyMeasurable C
  rw [ae_iff]
  apply measure_mono_null ?_ hsupp
  intro x hx
  by_contra hxK
  have hxK' : x ∈ closure (Homogenization.openCubeSet Q) := by
    simpa only [mem_compl_iff, not_not] using hxK
  exact hx (hC _ ⟨x, hxK', rfl⟩)

theorem measureTrace_hdense_of_finiteMeasure_supported {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Q)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure (Homogenization.openCubeSet Q))ᶜ = 0)
    (u : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder) :
    ∃ (a : ℕ → CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder)
      (f : ℕ → SpatialCoordinates d → ℝ)
      (w : ℕ → CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder),
      (∀ n, ContDiff ℝ ∞ (f n)) ∧
      (∀ n, MemLp (f n) 2 ν) ∧
      (∀ n, (a n).val 0 =ᵐ[volume.restrict
          (centeredCube (Homogenization.cubeCenter Q)
            (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d))] f n) ∧
      (∀ n, (w n).val 0 = u.val 0 - (a n).val 0) ∧
      Filter.Tendsto
        (fun n => cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (w n))
        Filter.atTop (nhds 0) := by
  classical
  let H (n : ℕ) :=
    exists_scalarCubeFractionalL2_globalSmooth_sub_norm_lt hd Q hr
      halfFractionalOrder u (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  let a := fun n : ℕ => (H n).choose
  let f := fun n : ℕ => (H n).choose_spec.1.choose
  let w := fun n : ℕ => (H n).choose_spec.2.choose
  refine ⟨a, f, w, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (H n).choose_spec.1.choose_spec.1
  · intro n
    exact contDiff_memLp_of_finiteMeasure_supported_closure Q hr ν hsupp
      (f n) ((H n).choose_spec.1.choose_spec.1)
  · intro n
    exact (H n).choose_spec.1.choose_spec.2
  · intro n
    exact (H n).choose_spec.2.choose_spec.1
  · have hnonneg : ∀ n, 0 ≤ cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (w n) := by
      intro n
      unfold cubeFractionalL2Norm
      exact add_nonneg ENNReal.toReal_nonneg
        (mul_nonneg
          (Real.rpow_nonneg hr.le _)
          (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    have hle : ∀ n, cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (w n) ≤
        1 / ((n : ℝ) + 1) := by
      intro n
      exact (H n).choose_spec.2.choose_spec.2.le
    have hlim : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds 0) := by
      simpa only [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact squeeze_zero hnonneg hle hlim

end SubdiffusiveProcess
