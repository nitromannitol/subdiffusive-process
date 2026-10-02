import SubdiffusiveProcess.Sobolev.CubeUniformError
import SubdiffusiveProcess.DirichletForm.ThresholdCore

/-! Turn uniform convergence of continuous representatives on a closed cube into L2 convergence.
This module constructs the actual L2 limit and makes no energy or form-domain assertion. -/

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology
namespace SubdiffusiveProcess
noncomputable section

/-- A continuous function on the closed cube has a representative in cube L2. -/
theorem exists_cubeL2_of_continuous_closedCube
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (g : C(closure (centeredCube z r hr : Set (SpatialCoordinates d)), ℝ)) :
    ∃ (v : DomainL2 (centeredCube z r hr)) (vc : SpatialCoordinates d → ℝ),
      ContinuousOn vc (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      ((v : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc) ∧
      ∀ x (hx : x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d))), vc x = g ⟨x, hx⟩ := by
  classical
  haveI finiteCube := LimitFormCore.isFiniteMeasure_cube z r hr
  let vc : SpatialCoordinates d → ℝ := fun x =>
    if hx : x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) then g ⟨x, hx⟩ else 0
  have heq (x) (hx : x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d))) :
      vc x = g ⟨x, hx⟩ := dif_pos hx
  have hc : ContinuousOn vc (closure (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    rw [continuousOn_iff_continuous_restrict]
    convert g.continuous using 1
    funext x
    exact heq x.val x.property
  obtain ⟨B, hB⟩ := (lane2_isCompact_closure_centeredCube z hr).exists_bound_of_continuousOn hc
  have hm : MemLp vc 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    MemLp.of_bound ((hc.mono subset_closure).aestronglyMeasurable
      (centeredCube z r hr).isOpen.measurableSet) B
      ((ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet).mono
        fun x hx => hB x (subset_closure hx))
  exact ⟨hm.toLp vc, vc, hc, hm.coeFn_toLp, heq⟩

/-- Uniform convergence on the closed cube implies convergence of the represented L2 classes. -/
theorem cube_tendsto_of_uniformly_on
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (f : ℕ → SpatialCoordinates d → ℝ) (u : ℕ → DomainL2 (centeredCube z r hr))
    (hu : ∀ n, (u n : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f n)
    (vc : SpatialCoordinates d → ℝ) (v : DomainL2 (centeredCube z r hr))
    (hv : (v : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc)
    (hlim : TendstoUniformly
      (fun n (x : closure (centeredCube z r hr : Set (SpatialCoordinates d))) => f n x.val)
      (fun x => vc x.val) atTop) : Tendsto u atTop (𝓝 v) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  let L := Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hden : 0 < L + 1 := by linarith only [hL]
  let eta := eps / (L + 1)
  have heta : 0 < eta := div_pos heps hden
  have hevent := Metric.tendstoUniformly_iff.mp hlim eta heta
  filter_upwards [hevent] with n hn
  have hb : ‖u n - v‖ ≤ L * eta := cube_norm_sub_le_of_uniform_error z hr (f n) vc eta heta.le
    (fun x hx => by simpa only [Real.dist_eq, abs_sub_comm] using (hn ⟨x, subset_closure hx⟩).le)
    (u n) v (hu n) hv
  rw [dist_eq_norm]
  refine hb.trans_lt ?_
  change L * (eps / (L + 1)) < eps
  rw [← mul_div_assoc, div_lt_iff₀ hden]
  nlinarith only [heps]

end
end SubdiffusiveProcess
