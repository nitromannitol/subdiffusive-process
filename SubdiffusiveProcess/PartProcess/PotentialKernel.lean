import SubdiffusiveProcess.PartProcess.Data
import SubdiffusiveProcess.Processes.E7.Occupation
import MarkovProcess.Killed.GluingPotential

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7
variable {d : ℕ}

/-- The finite state-space kernel obtained by integrating the path law over Laplace time. -/
def freeKernel (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
    [IsMarkovKernel K] (α : ℝ) (hα : 0 < α) : Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  letI : IsFiniteMeasure (laplaceWeight α) := isFiniteMeasure_laplaceWeight hα
  ((Kernel.const (Fin d → ℝ) (laplaceWeight α)) ×ₖ K).map
    (fun p : ℝ × ContinuousPath (Fin d → ℝ) => p.2 (Real.toNNReal p.1))

theorem isFiniteKernel_freeKernel
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) [IsMarkovKernel K]
    (α : ℝ) (hα : 0 < α) : IsFiniteKernel (freeKernel K α hα) := by
  letI : IsFiniteMeasure (laplaceWeight α) := isFiniteMeasure_laplaceWeight hα
  unfold freeKernel
  infer_instance

theorem lintegral_freeKernel_ennreal
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) [IsMarkovKernel K]
    (α : ℝ) (hα : 0 < α) (f : (Fin d → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (x : Fin d → ℝ) :
    (∫⁻ y, f y ∂freeKernel K α hα x) =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-α * t)) *
        ∫⁻ w, f (w (Real.toNNReal t)) ∂K x := by
  letI : IsFiniteMeasure (laplaceWeight α) := isFiniteMeasure_laplaceWeight hα
  have hfm : Measurable fun p : ℝ × ContinuousPath (Fin d → ℝ) => f (p.2 (Real.toNNReal p.1)) :=
    hf.comp aux_n8_measurable_eval
  rw [freeKernel, Kernel.map_apply _ aux_n8_measurable_eval,
    lintegral_map hf aux_n8_measurable_eval, Kernel.lintegral_prod _ _ _ hfm]
  change (∫⁻ t, ∫⁻ w, f (w (Real.toNNReal t)) ∂K x ∂laplaceWeight α) = _
  rw [lintegral_laplaceWeight α hfm.lintegral_prod_right']

theorem lintegral_freeKernel
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) [IsMarkovKernel K]
    (α : ℝ) (hα : 0 < α) (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (x : Fin d → ℝ) :
    (∫⁻ y, ENNReal.ofReal (f y) ∂freeKernel K α hα x) = potentialOcc K 0 α f x := by
  letI : IsFiniteMeasure (laplaceWeight α) := isFiniteMeasure_laplaceWeight hα
  have hfm : Measurable fun p : ℝ × ContinuousPath (Fin d → ℝ) =>
      ENNReal.ofReal (f (p.2 (Real.toNNReal p.1))) :=
    (hf.comp aux_n8_measurable_eval).ennreal_ofReal
  rw [freeKernel, Kernel.map_apply _ aux_n8_measurable_eval,
    lintegral_map (hf.ennreal_ofReal) aux_n8_measurable_eval,
    Kernel.lintegral_prod _ _ _ hfm]
  change (∫⁻ t, ∫⁻ w, ENNReal.ofReal (f (w (Real.toNNReal t))) ∂K x ∂laplaceWeight α) = _
  rw [lintegral_laplaceWeight α hfm.lintegral_prod_right']
  simp [potentialOcc, SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional_apply]

theorem integral_freeKernel
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) [IsMarkovKernel K]
    (α : ℝ) (hα : 0 < α) (g : (Fin d → ℝ) → ℝ) (hg : Measurable g)
    (B : ℝ) (hB : ∀ y, |g y| ≤ B) (x : Fin d → ℝ) :
    (∫ y, g y ∂freeKernel K α hα x) =
      ∫ t in Ioi 0, Real.exp (-α * t) * ∫ w, g (w (Real.toNNReal t)) ∂K x := by
  letI : IsFiniteMeasure (laplaceWeight α) := isFiniteMeasure_laplaceWeight hα
  have hi : Integrable (fun p : ℝ × ContinuousPath (Fin d → ℝ) =>
      g (p.2 (Real.toNNReal p.1))) ((laplaceWeight α).prod (K x)) :=
    (integrable_const B).mono' (hg.comp aux_n8_measurable_eval).aestronglyMeasurable
      (Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hB _)
  rw [freeKernel, Kernel.map_apply _ aux_n8_measurable_eval,
    integral_map aux_n8_measurable_eval.aemeasurable hg.aestronglyMeasurable,
    Kernel.prod_apply, Kernel.const_apply, integral_prod _ hi]
  rw [laplaceWeight, integral_withDensity_eq_integral_toReal_smul
    (measurable_laplaceDensity α) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext t
  simp [ENNReal.toReal_ofReal (Real.exp_pos _).le]

end SubdiffusiveProcess.PartProcess
