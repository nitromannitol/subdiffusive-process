module

public import SubdiffusiveProcess.Main.WeightedChaosCutoff
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped CompactlySupported ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

theorem weightedChaosCutoff_centeredCube_toReal_eq_integral
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ((weightedChaosCutoff M H N omega)
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        Real.exp (H omega x) * fineDensity M N omega x := by
  let Q : Set (SpatialCoordinates d) := centeredCube z r hr
  let f : SpatialCoordinates d → ℝ≥0∞ :=
    ENNReal.ofReal ∘ (fun x => Real.exp (H omega x) * fineDensity M N omega x)
  have hf : Measurable f := by
    dsimp [f]
    apply Measurable.ennreal_ofReal
    unfold fineDensity finePotential
    fun_prop
  have htop : ∀ᵐ x ∂(volume.restrict Q), f x < ∞ := by
    filter_upwards with x
    exact ENNReal.coe_lt_top
  have hset := setIntegral_withDensity_eq_setIntegral_toReal_smul
    (μ := volume) hf htop (fun _ : SpatialCoordinates d => (1 : ℝ))
      (show MeasurableSet Q by
        dsimp [Q]
        exact (centeredCube z r hr).isOpen.measurableSet)
  change ((volume.withDensity f) Q).toReal = _
  have hconst : (∫ x in Q, (1 : ℝ) ∂volume.withDensity f) =
      ((volume.withDensity f) Q).toReal := by
    rw [setIntegral_const, Measure.real, smul_eq_mul, mul_one]
  rw [← hconst, hset]
  apply integral_congr_ae
  filter_upwards with x
  dsimp [f]
  rw [ENNReal.toReal_ofReal]
  · simp
  · unfold fineDensity
    exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le



end SubdiffusiveProcess
