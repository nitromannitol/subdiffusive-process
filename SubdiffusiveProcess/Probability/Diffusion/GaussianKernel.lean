module

public import SubdiffusiveProcess.Probability.Diffusion.BrownianDensity

@[expose] public section

/-!
# The continuous free Gaussian kernel at the full-Laplacian clock

The density is the product of the scalar Gaussian densities with variance
`2t`. Its joint continuity is proved on positive times. This supplies the
free term in Hunt's formula; no regularity of an exit correction is inferred
from the regularity of this free term.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.Model.HeatSemigroupVec SubdiffusiveProcess.Model.LifetimeProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularityKilled
open scoped ENNReal NNReal BigOperators Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The free density for generator `Δ`, with each coordinate having variance `2t`. -/
def laplacianDensity (t : ℝ) (x y : Vec d) : ℝ :=
  ∏ i, gaussianPDFReal (x i) (2 * Real.toNNReal t) (y i)

theorem laplacianDensity_nonneg (t : ℝ) (x y : Vec d) :
    0 ≤ laplacianDensity t x y :=
  Finset.prod_nonneg fun _ _ => gaussianPDFReal_nonneg _ _ _

theorem laplacianDensity_pos {t : ℝ} (ht : 0 < t) (x y : Vec d) :
    0 < laplacianDensity t x y :=
  Finset.prod_pos fun i _ => gaussianPDFReal_pos _ _ _
    (ne_of_gt (mul_pos (by norm_num) (Real.toNNReal_pos.mpr ht)))

/-- Joint measurability includes the harmless totalization at nonpositive times. -/
theorem measurable_laplacianDensity :
    Measurable (fun z : ℝ × Vec d × Vec d => laplacianDensity z.1 z.2.1 z.2.2) := by
  unfold laplacianDensity gaussianPDFReal
  fun_prop

/-- Spatial measurability at a fixed time. -/
theorem measurable_uncurry_laplacianDensity (t : ℝ) :
    Measurable (Function.uncurry (laplacianDensity (d := d) t)) := by
  unfold Function.uncurry laplacianDensity gaussianPDFReal
  fun_prop

/-- The free Gaussian is jointly continuous at all positive times. -/
theorem continuousOn_laplacianDensity :
    ContinuousOn (fun z : ℝ × Vec d × Vec d => laplacianDensity z.1 z.2.1 z.2.2)
      (Ioi 0 ×ˢ univ ×ˢ univ) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  unfold laplacianDensity
  apply tendsto_finset_prod
  intro i _
  change ContinuousAt (fun z : ℝ × Vec d × Vec d =>
    gaussianPDFReal (z.2.1 i) (2 * Real.toNNReal z.1) (z.2.2 i)) z
  have hv : (0 : ℝ) < (2 * Real.toNNReal z.1 : NNReal) := by
    exact_mod_cast mul_pos (by norm_num : (0 : NNReal) < 2) (Real.toNNReal_pos.mpr hz.1)
  unfold gaussianPDFReal
  fun_prop (disch := positivity)

/-- The Gaussian transition measure has the displayed density, at every start. -/
theorem laplacianSemigroup_eq_withDensity {t : ℝ} (ht : 0 < t) (x : Vec d) :
    laplacianSemigroup d (Real.toNNReal t) x =
      volume.withDensity (fun y => ENNReal.ofReal (laplacianDensity t x y)) := by
  rw [laplacianSemigroup_apply, gaussianVec_eq_withDensity x
    (ne_of_gt (mul_pos (by norm_num) (Real.toNNReal_pos.mpr ht)))]
  congr 1
  funext y
  exact (ENNReal.ofReal_prod_of_nonneg
    (fun i _ => gaussianPDFReal_nonneg (x i) (2 * Real.toNNReal t) (y i))).symm

/-- Killing on the whole state space leaves the Brownian transition measure unchanged. -/
theorem killedKernel_laplacianLaw_univ (t : NNReal) (x : Vec d) :
    killedKernel (laplacianLaw d) univ isOpen_univ t x = laplacianSemigroup d t x := by
  rw [laplacianLaw, killedKernel_lifetimeProcess]
  apply Measure.ext
  intro B hB
  rw [SubMarkovKernelSemigroup.IsConservative.killedKernel_apply _ _ _ _ t x hB]
  have hevent : ContinuousPath.killedEvent (univ : Set (Vec d)) t B =
      (fun w : ContinuousPath (Vec d) => w t) ⁻¹' B := by
    ext w
    rw [ContinuousPath.mem_killedEvent_iff]
    rw [(ContinuousPath.exitTime_eq_top_iff univ w).mpr (fun _ => mem_univ _)]
    simp only [ENNReal.coe_lt_top, true_and, mem_preimage]
  rw [hevent]
  change (laplacianContinuousLaw d x) ((fun w : ContinuousPath (Vec d) => w t) ⁻¹' B) = _
  rw [← Kernel.map_apply' (laplacianContinuousLaw d)
    (show Measurable (fun w : ContinuousPath (Vec d) => w t) from
      ContinuousPath.measurable_coordinateProcess t) x hB, laplacianContinuousLaw_map_eval]

/-- The free Gaussian is the continuous whole-space killed density. This does
not assert the bounded-domain density target of P-435. -/
theorem isKilledDensity_laplacianDensity_univ :
    IsKilledDensity (laplacianLaw d) (fun _ => 1) univ laplacianDensity := by
  refine ⟨fun t _ => measurable_uncurry_laplacianDensity t,
    fun t _ x _ y _ => laplacianDensity_nonneg t x y, ?_⟩
  intro t ht x _ B hB
  rw [← killedKernel_apply_law _ isOpen_univ t x B hB,
      killedKernel_laplacianLaw_univ, laplacianSemigroup_eq_withDensity ht,
      withDensity_apply _ hB]
  simp only [inter_univ, ENNReal.ofReal_one, withDensity_const, one_smul]

end SubdiffusiveProcess.Probability.Diffusion
