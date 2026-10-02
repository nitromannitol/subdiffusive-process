import SubdiffusiveProcess.KilledFeller.ShortTimeMeanBound
import Mathlib.MeasureTheory.Integral.Prod

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal BoundedContinuousFunction

noncomputable section
namespace SubdiffusiveProcess.KilledFeller

/-- The killed Laplace integrand is absolutely integrable jointly in path and positive time. -/
theorem integrable_killedLaplace_product {d : ℕ}
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (g : SpatialCoordinates d →ᵇ ℝ) (lam : ℝ) (hlam : 0 < lam)
    (mu : Measure (DiffusionPath d)) [IsFiniteMeasure mu] :
    Integrable (fun p : DiffusionPath d × ℝ =>
      Real.exp (-lam * p.2) * killedTest U g p.1 p.2)
      (mu.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmeas : Measurable (fun p : DiffusionPath d × ℝ =>
      Real.exp (-lam * p.2) * killedTest U g p.1 p.2) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
      (measurable_killedTest U hU g)
  have hmajor := ((exp_neg_integrableOn_Ioi 0 hlam).mul_const ‖g‖).comp_snd mu
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (abs_killedTest_le U g p.1 p.2) (Real.exp_pos _).le

/-- Fubini identifies the actual killed double Laplace integral with integrated marginals. -/
theorem killedResolventScalar_eq_laplace_integral {d : ℕ}
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (g : SpatialCoordinates d →ᵇ ℝ) (lam : ℝ) (hlam : 0 < lam)
    (mu : Measure (DiffusionPath d)) [IsFiniteMeasure mu] :
    killedResolventScalar U g lam mu =
      ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * (∫ w, killedTest U g w t ∂mu) := by
  rw [killedResolventScalar,
    integral_integral_swap (integrable_killedLaplace_product U hU g lam hlam mu)]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => integral_const_mul _ _

end SubdiffusiveProcess.KilledFeller
