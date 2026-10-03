module

public import SubdiffusiveProcess.Lane2.MeshError
public import SubdiffusiveProcess.Sobolev.ResponseSpace

@[expose] public section

/-! Transfer a pointwise approximation on a finite cube to its actual L2 classes.
This bound is independent of the coefficient and makes no energy claim. -/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace SubdiffusiveProcess

/-- A uniform error between representatives gives the corresponding cube L2 error. -/
theorem cube_norm_sub_le_of_uniform_error
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (f g : SpatialCoordinates d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hfg : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), |f x - g x| ≤ B)
    (u v : DomainL2 (centeredCube z r hr))
    (hu : (u : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (hv : (v : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g) :
    ‖u - v‖ ≤ Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) * B := by
  have hae : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      ‖((u - v : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) x‖ ≤ B := by
    filter_upwards [Lp.coeFn_sub u v, hu, hv,
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x he hf hg hx
    rw [he]
    simpa only [Pi.sub_apply, hf, hg, Real.norm_eq_abs] using hfg x hx
  have hle := Lp.norm_le_of_ae_bound (μ := volume.restrict
    (centeredCube z r hr : Set (SpatialCoordinates d))) (p := 2) hB hae
  have hmass : measureUnivNNReal (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) =
      (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))).toNNReal := by
    simp only [measureUnivNNReal, measureReal_def, Measure.restrict_apply_univ,
      ENNReal.toReal]
    exact Real.toNNReal_coe.symm
  have hvol : 0 ≤ volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    ENNReal.toReal_nonneg
  rw [hmass, Real.coe_toNNReal _ hvol] at hle
  have hexp : ((2 : ℝ≥0∞).toReal)⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [hexp, ← Real.sqrt_eq_rpow] at hle
  exact hle

end SubdiffusiveProcess
