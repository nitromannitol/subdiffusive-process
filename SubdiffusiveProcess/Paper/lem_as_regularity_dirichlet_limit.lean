import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_stability
import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_exists
import SubdiffusiveProcess.Paper.lem_as_regularity_trunc_coeff
import SubdiffusiveProcess.Analysis.CenteredL2Continuity
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.SeminormLimits

/-! Limit passage for the Dirichlet oscillation display along a uniformly convergent family of
coefficients, and the coefficient convergence for the truncated infrared fields. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut
open Homogenization hiding Vec
open scoped Topology ENNReal
noncomputable section
namespace Paper

variable {d : ℕ}

/-- The centered normalized `L²` oscillation on a subwindow is continuous along `L²(Q)`
convergence. -/
theorem aux_lem_as_regularity_dirichlet_limit_osc_tendsto {Q : Homogenization.TriadicCube d}
    {V : Set (Vec d)} (hVm : MeasurableSet V) (hVpos : 0 < (volume V).toReal)
    (hVfin : volume V ≠ ⊤) (hVQ : V ⊆ openCubeSet Q)
    {u : H1Function (openCubeSet Q)} {v : ℕ → H1Function (openCubeSet Q)}
    (hconv : Tendsto (fun k => ∫ x in openCubeSet Q, ((v k).toFun x - u.toFun x) ^ 2 ∂volume)
      atTop (𝓝 0)) :
    Tendsto (fun k => normalizedL2On V (fun x => (v k).toFun x - averageOn V (v k).toFun))
      atTop (𝓝 (normalizedL2On V (fun x => u.toFun x - averageOn V u.toFun))) := by
  haveI : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr hVfin
  have hrestrict : volume.restrict V ≤ volume.restrict (openCubeSet Q) :=
    Measure.restrict_mono hVQ le_rfl
  have hfV : ∀ k, MemLp (v k).toFun 2 (volume.restrict V) := fun k =>
    ((v k).memL2).mono_measure hrestrict
  have hflimV : MemLp u.toFun 2 (volume.restrict V) := u.memL2.mono_measure hrestrict
  have hsqW : ∀ k, IntegrableOn (fun x => ((v k).toFun x - u.toFun x) ^ 2) (openCubeSet Q) :=
    fun k => (((v k).memL2).sub u.memL2).integrable_sq
  have hconvV := tendsto_setIntegral_zero_of_subset hVQ hVm (fun k x => sq_nonneg _) hsqW hconv
  have hraw := tendsto_normalizedL2On_of_tendsto_integral_sq hconvV
  have hcent := tendsto_centeredNormalizedL2On_sub_of_tendsto_sub hVm hVpos hVfin hfV hflimV hraw
  exact tendsto_normalizedL2On_of_tendsto_sub (fun k => (hfV k).sub (memLp_const _))
    (hflimV.sub (memLp_const _)) hcent

/-- A display between two centered windows passes to the limit along `L²` convergence. -/
theorem lem_as_regularity_dirichlet_limit {Q : Homogenization.TriadicCube d}
    {V W : Set (Vec d)} (hVm : MeasurableSet V) (hVpos : 0 < (volume V).toReal)
    (hVfin : volume V ≠ ⊤) (hVQ : V ⊆ openCubeSet Q)
    (hWm : MeasurableSet W) (hWpos : 0 < (volume W).toReal)
    (hWfin : volume W ≠ ⊤) (hWQ : W ⊆ openCubeSet Q)
    {u : H1Function (openCubeSet Q)} {v : ℕ → H1Function (openCubeSet Q)}
    (hconv : Tendsto (fun k => ∫ x in openCubeSet Q, ((v k).toFun x - u.toFun x) ^ 2 ∂volume)
      atTop (𝓝 0))
    {c1 c2 C : ℝ} {r : ℕ → ℝ} {r0 : ℝ} (hr : Tendsto r atTop (𝓝 r0))
    (hle : ∀ k, c1 * normalizedL2On V (fun x => (v k).toFun x - averageOn V (v k).toFun) ≤
      C * (c2 * normalizedL2On W (fun x => (v k).toFun x - averageOn W (v k).toFun) + r k)) :
    c1 * normalizedL2On V (fun x => u.toFun x - averageOn V u.toFun) ≤
      C * (c2 * normalizedL2On W (fun x => u.toFun x - averageOn W u.toFun) + r0) := by
  have h1 := aux_lem_as_regularity_dirichlet_limit_osc_tendsto hVm hVpos hVfin hVQ hconv
  have h2 := aux_lem_as_regularity_dirichlet_limit_osc_tendsto hWm hWpos hWfin hWQ hconv
  exact le_of_tendsto_of_tendsto (h1.const_mul c1) (((h2.const_mul c2).add hr).const_mul C)
    (Eventually.of_forall hle)

end Paper
