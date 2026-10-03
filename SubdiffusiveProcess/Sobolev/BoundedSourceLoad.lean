module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.Sobolev.GradientRange
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Tactic

@[expose] public section

/-! A bounded measurable source on an open cube gives an `L²` volume load, membership in
every `Lᵖ` of the cube, and the normalized local `Lᵖ` bound by its supremum.
This module asserts no PDE estimate. -/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ}

/-- A measurable source bounded on an open cube lies in every `Lᵖ` of that cube. -/
theorem boundedSource_memLp (zP : SpatialCoordinates d) {R : ℝ} (hR : 0 < R)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hF : Measurable F)
    (hbound : ∀ x ∈ (centeredCube zP R hR : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (p : ℝ≥0∞) :
    MemLp F p (volume.restrict (centeredCube zP R hR : Set (SpatialCoordinates d))) := by
  haveI instFin : IsFiniteMeasure
      (volume.restrict (centeredCube zP R hR : Set (SpatialCoordinates d))) :=
    isFiniteMeasure_restrict.2 (by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top)
  exact MemLp.of_bound hF.aestronglyMeasurable Kf
    (ae_restrict_of_forall_mem (centeredCube zP R hR).isOpen.measurableSet
      (fun x hx => by simpa only [Real.norm_eq_abs] using hbound x hx))

/-- The `L²` class of a bounded source realizes the integral load against every datum. -/
theorem boundedSource_load (zP : SpatialCoordinates d) {R : ℝ} (hR : 0 < R)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hF : Measurable F)
    (hbound : ∀ x ∈ (centeredCube zP R hR : Set (SpatialCoordinates d)), |F x| ≤ Kf) :
    ∃ fL2 : DomainL2 (centeredCube zP R hR),
      ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube zP R hR : Set (SpatialCoordinates d))] F) ∧
      ∀ ψ : SobolevData (centeredCube zP R hR),
        sobolevVolumeLoad fL2 ψ =
          ∫ x in (centeredCube zP R hR : Set (SpatialCoordinates d)), F x * ψ.1 x := by
  have hmem := boundedSource_memLp zP hR F Kf hF hbound 2
  refine ⟨hmem.toLp F, hmem.coeFn_toLp, fun ψ => ?_⟩
  rw [sobolevVolumeLoad_apply]
  apply integral_congr_ae
  filter_upwards [hmem.coeFn_toLp] with x hx
  rw [hx]

/-- The normalized local `Lᵖ` norm of a bounded source on a sup-norm ball is at most its bound. -/
theorem boundedSource_eLpNorm_ball_le (z : SpatialCoordinates d) {ρ : ℝ} (hρ : 0 < ρ)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hbound : ∀ x ∈ Metric.ball z (ρ / 2), |F x| ≤ Kf) (p : ℝ) (hp : 0 < p) :
    (SubdiffusiveProcess.RawLp.eLpNorm F (ENNReal.ofReal p) (volume.restrict (Metric.ball z (ρ / 2)))).toReal /
      (ρ ^ d) ^ (1 / p) ≤ Kf := by
  have hae : ∀ᵐ x ∂volume.restrict (Metric.ball z (ρ / 2)), ‖F x‖ ≤ Kf :=
    ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet
      (fun x hx => by simpa only [Real.norm_eq_abs] using hbound x hx)
  have hconst := eLpNorm_le_of_ae_bound (p := ENNReal.ofReal p)
    (μ := volume.restrict (Metric.ball z (ρ / 2)))
    (f := fun _ : SpatialCoordinates d => Kf) (C := Kf) aestronglyMeasurable_const
    (Filter.Eventually.of_forall fun _ => by simp only [Real.norm_of_nonneg hKf, le_refl])
  have hmono : SubdiffusiveProcess.RawLp.eLpNorm F (ENNReal.ofReal p)
      (volume.restrict (Metric.ball z (ρ / 2))) ≤
      SubdiffusiveProcess.RawLp.eLpNorm (fun _ : SpatialCoordinates d => Kf) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z (ρ / 2))) :=
    SubdiffusiveProcess.RawLp.eLpNorm_mono_ae (hae.mono fun _ hx => by
      simpa only [Real.norm_of_nonneg hKf] using hx)
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded aestronglyMeasurable_const] at hmono
  have hle := hmono.trans hconst
  have hvol : (volume.restrict (Metric.ball z (ρ / 2))) Set.univ = ENNReal.ofReal (ρ ^ d) := by
    rw [Measure.restrict_apply_univ]
    exact centeredCube_volume z hρ
  rw [hvol, ENNReal.toReal_ofReal hp.le] at hle
  have hpow : 0 < (ρ ^ d) ^ (1 / p) := Real.rpow_pos_of_pos (pow_pos hρ d) _
  have hfin : ENNReal.ofReal (ρ ^ d) ^ p⁻¹ * ENNReal.ofReal Kf ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 hp.le) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (pow_nonneg hρ.le d),
    ENNReal.toReal_ofReal hKf] at hreal
  rw [div_le_iff₀ hpow, one_div, mul_comm]
  exact hreal

end SubdiffusiveProcess
