import SubdiffusiveProcess.Probability.Diffusion.Packet452DoobL2
import SubdiffusiveProcess.Probability.Diffusion.Packet452GridLimit
import SubdiffusiveProcess.Probability.Diffusion.LaplacianGenerator
import SubdiffusiveProcess.Probability.Diffusion.HuntIdentity
import MarkovProcess.Trajectory.DynkinMartingale




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology

open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-- **Doob's `L²` maximal inequality for the Brownian Dynkin martingale**, continuous time,
under each `P_x`, constant `4`. -/
theorem lintegral_iSup_sq_dynkinProcess_le
    (f : (isFeller_laplacianSemigroup (d := d)).c0Semigroup.generatorDomain)
    (x : Vec d) (T : ℝ≥0) :
    (∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
        ENNReal.ofReal ((isFeller_laplacianSemigroup.dynkinProcess f t ω) ^ 2))
        ∂(laplacianContinuousLaw d x))
      ≤ 4 * ∫⁻ ω, ENNReal.ofReal ((isFeller_laplacianSemigroup.dynkinProcess f T ω) ^ 2)
          ∂(laplacianContinuousLaw d x) := by
  classical
  have hmart : Martingale (isFeller_laplacianSemigroup.dynkinProcess f)
      (ContinuousPath.canonicalFiltration (alpha := Vec d)) (laplacianContinuousLaw d x) :=
    isFeller_laplacianSemigroup.martingale_dynkinProcess isConservative_laplacianSemigroup
      kolmogorovRegular_laplacianSemigroup f x
  have hcont : ∀ ω : ContinuousPath (Vec d), Continuous fun t : ℝ≥0 =>
      ENNReal.ofReal ((isFeller_laplacianSemigroup.dynkinProcess f t ω) ^ 2) :=
    fun ω => ENNReal.continuous_ofReal.comp
      ((isFeller_laplacianSemigroup.continuous_dynkinProcess f ω).pow 2)
  have hslice : ∀ t : ℝ≥0, Measurable fun ω : ContinuousPath (Vec d) =>
      ENNReal.ofReal ((isFeller_laplacianSemigroup.dynkinProcess f t ω) ^ 2) := fun t =>
    (((isFeller_laplacianSemigroup.stronglyMeasurable_dynkinProcess f t).measurable).pow_const
      2).ennreal_ofReal
  have hmeas : ∀ n : ℕ, Measurable fun ω : ContinuousPath (Vec d) =>
      dyadicGridSup (fun t : ℝ≥0 =>
        ENNReal.ofReal ((isFeller_laplacianSemigroup.dynkinProcess f t ω) ^ 2)) T n := by
    intro n
    exact Finset.measurable_range_sup'' (f := fun k ω =>
      ENNReal.ofReal ((isFeller_laplacianSemigroup.dynkinProcess f (dyadicTime T n k) ω) ^ 2))
      (fun k _ => hslice (dyadicTime T n k))
  refine le_trans (lintegral_iSup_le_dyadicGridSup hcont hmeas) (iSup_le fun n => ?_)
  have hgrid := lintegral_sq_sup_abs_le hmart (dyadicTime T n) (monotone_dyadicTime T n) (2 ^ n)
  simp only [dyadicTime_last] at hgrid
  refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hgrid
  exact (ofReal_sq_sup' Finset.nonempty_range_add_one
    (fun k => isFeller_laplacianSemigroup.dynkinProcess f (dyadicTime T n k) ω)).symm

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
