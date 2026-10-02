import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn

/-! Continuous representatives and ellipticity of fixed cutoff coefficients.
The bounds depend on the cutoff and sample; no bound uniform in cutoffs is claimed. -/

open MeasureTheory Set TopologicalSpace
open scoped NNReal

namespace SubdiffusiveProcess.Lane4
noncomputable section

/-- The Sobolev cutoff coefficient has its literal continuous positive field representative. -/
theorem cutoffPositiveCoefficient_representative
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    Continuous (cutoffCoefficient M H omega N) ∧
      (∀ x, 0 < cutoffCoefficient M H omega N x) ∧
      (∃ Lam : ℝ, ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        cutoffCoefficient M H omega N x ≤ Lam) ∧
      (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        (Lane4.cutoffPositiveCoefficient M H omega N z hr).val x =
          cutoffCoefficient M H omega N x) := by
  refine ⟨Lane4.cutoffCoefficient_continuous M H omega N,
    Lane4.cutoffCoefficient_pos M H omega N, ?_, ?_⟩
  · have hne : (closedCube z r hr : Set (SpatialCoordinates d)).Nonempty :=
      ⟨z, Metric.mem_closedBall_self (by positivity)⟩
    have hcompact : IsCompact (closedCube z r hr : Set (SpatialCoordinates d)) :=
      isCompact_closedBall z (r / 2)
    obtain ⟨x0, -, hx0⟩ := hcompact.exists_isMaxOn hne
      (Lane4.cutoffCoefficient_continuous M H omega N).continuousOn
    exact ⟨cutoffCoefficient M H omega N x0, isMaxOn_iff.mp hx0⟩
  · haveI cubeInsideClosed : Fact (((centeredCube z r hr : Set (SpatialCoordinates d))) ⊆
        (closedCube z r hr : Set (SpatialCoordinates d))) :=
      ⟨centeredCube_subset_closedCube z hr⟩
    have hval := normalizedContinuousPositiveCoefficient_coeFn
      (Ω := centeredCube z r hr) (closedCube z r hr)
      (Lane4.cutoffCoefficientCM M H omega N z hr)
      (Lane4.cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
    unfold Lane4.cutoffPositiveCoefficient
    filter_upwards [hval, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
      with x hx hxΩ
    rw [hx hxΩ, div_one]
    rfl


/-- Every fixed cutoff is uniformly elliptic on a closed cube. -/
theorem cutoffCoefficient_closedCube_bounds
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        lam ≤ cutoffCoefficient M H omega N x ∧ cutoffCoefficient M H omega N x ≤ Lam := by
  have hne : (closedCube z r hr : Set (SpatialCoordinates d)).Nonempty :=
    ⟨z, Metric.mem_closedBall_self (by positivity)⟩
  have hcompact : IsCompact (closedCube z r hr : Set (SpatialCoordinates d)) :=
    isCompact_closedBall z (r / 2)
  obtain ⟨xmin, -, hxmin⟩ := hcompact.exists_isMinOn hne
    (Lane4.cutoffCoefficient_continuous M H omega N).continuousOn
  obtain ⟨xmax, -, hxmax⟩ := hcompact.exists_isMaxOn hne
    (Lane4.cutoffCoefficient_continuous M H omega N).continuousOn
  exact ⟨cutoffCoefficient M H omega N xmin, cutoffCoefficient M H omega N xmax,
    Lane4.cutoffCoefficient_pos M H omega N xmin,
    fun x hx => ⟨isMinOn_iff.mp hxmin x hx, isMaxOn_iff.mp hxmax x hx⟩⟩

end
end SubdiffusiveProcess.Lane4
