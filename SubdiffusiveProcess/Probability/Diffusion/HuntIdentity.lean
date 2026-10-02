import SubdiffusiveProcess.Probability.Diffusion.ExitRestart

/-!
# The Hunt identity for the constructed Brownian law

Parameterized strong Markov restart gives the fixed-horizon endpoint formula.
Tonelli then identifies the exit correction. Finiteness of its total mass
justifies the real Bochner integral for almost every terminal point, which is
exactly what the set-integral density identity needs.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

instance isMarkovKernel_laplacianContinuousLaw : IsMarkovKernel (laplacianContinuousLaw d) := by
  unfold laplacianContinuousLaw
  infer_instance

/-- An endpoint in the open domain cannot occur exactly at its finite exit
time, for paths started in the domain. -/
theorem postExitMass_eq_measure_exitTime_lt {U : Set (Vec d)} (hU : IsOpen U)
    {t : ℝ} {x : Vec d} (hx : x ∈ U) (B : Set (Vec d)) :
    postExitMass U t x B = laplacianContinuousLaw d x
      {w | ContinuousPath.exitTime U w < ENNReal.ofReal t ∧
        w (Real.toNNReal t) ∈ B ∩ U} := by
  unfold postExitMass
  apply measure_congr
  filter_upwards [SubMarkovKernelSemigroup.IsConservative.ae_eval_zero_eq
    isConservative_laplacianSemigroup kolmogorovRegular_laplacianSemigroup x] with w hw
  apply propext
  change (ContinuousPath.exitTime U w ≤ ENNReal.ofReal t ∧
      w (Real.toNNReal t) ∈ B ∩ U) ↔ _
  constructor
  · intro h
    refine ⟨lt_of_le_of_ne h.1 ?_, h.2⟩
    intro heq
    have heq' : ContinuousPath.exitTime U w = ENNReal.ofReal t := heq
    have hfront := ContinuousPath.coordinate_exitTime_mem_frontier U hU w
      (hw ▸ hx) (heq' ▸ ENNReal.ofReal_ne_top)
    rw [heq'] at hfront
    change w (Real.toNNReal t) ∈ frontier U at hfront
    exact ((hU.frontier_eq ▸ hfront).2) h.2.2
  · exact fun h => ⟨h.1.le, h.2⟩

/-- Joint measurability of the nonnegative exit integrand in endpoint and path. -/
theorem measurable_ofReal_huntIntegrand_pair (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ) :
    Measurable (fun z : Vec d × ContinuousPath (Vec d) =>
      ENNReal.ofReal (huntIntegrand U t z.1 z.2)) :=
  ((measurable_huntIntegrand U hU).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).ennreal_ofReal

/-- Tonelli and fixed-horizon restart identify the nonnegative correction
mass for each starting point of every open domain. -/
theorem lintegral_lintegral_huntIntegrand_eq_postExitMass
    {U : Set (Vec d)} (hU : IsOpen U) {t : ℝ} (ht : 0 < t)
    {x : Vec d} (hx : x ∈ U) (B : Set (Vec d)) (hB : MeasurableSet B) :
    (∫⁻ y in B ∩ U, ∫⁻ w, ENNReal.ofReal (huntIntegrand U t y w)
      ∂laplacianContinuousLaw d x) = postExitMass U t x B := by
  let S := {w : ContinuousPath (Vec d) | ContinuousPath.exitTime U w < ENNReal.ofReal t}
  have hS : MeasurableSet S :=
    measurableSet_lt (ContinuousPath.measurable_exitTime U hU) measurable_const
  rw [lintegral_lintegral_swap (measurable_ofReal_huntIntegrand_pair U hU t).aemeasurable]
  calc
    _ = ∫⁻ w, S.indicator (fun w =>
        laplacianSemigroup d (Real.toNNReal (t - (ContinuousPath.exitTime U w).toReal))
          (w (ContinuousPath.exitTime U w).toNNReal) (B ∩ U)) w
        ∂laplacianContinuousLaw d x := by
      apply lintegral_congr
      intro w
      by_cases hw : w ∈ S
      · rw [indicator_of_mem hw]
        have hfin : ContinuousPath.exitTime U w ≠ ∞ := ne_top_of_lt hw
        have hlt : (ContinuousPath.exitTime U w).toReal < t := by
          simpa only [ENNReal.toReal_ofReal ht.le] using
            (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).2 hw
        have hw' : w ∈ {w | ContinuousPath.exitTime U w < ENNReal.ofReal t} := hw
        simp_rw [huntIntegrand, indicator_of_mem hw']
        rw [← withDensity_apply _ (hB.inter hU.measurableSet),
          ← laplacianSemigroup_eq_withDensity (sub_pos.mpr hlt)]
      · rw [indicator_of_notMem hw]
        have hw' : w ∉ {w | ContinuousPath.exitTime U w < ENNReal.ofReal t} := hw
        simp only [huntIntegrand, indicator_of_notMem hw', ENNReal.ofReal_zero,
          lintegral_zero]
    _ = _ := by
      rw [lintegral_indicator hS,
        ← measure_exitTime_lt_eval_eq_setLIntegral_semigroup U hU ht x
          (B ∩ U) (hB.inter hU.measurableSet),
        postExitMass_eq_measure_exitTime_lt hU hx]

/-- The actual exit integrand is integrable in the path variable for almost
every terminal point in the domain. This follows from finite post-exit mass. -/
theorem ae_integrable_huntIntegrand {U : Set (Vec d)} (hU : IsOpen U)
    {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U) :
    ∀ᵐ y ∂volume.restrict U, Integrable (huntIntegrand U t y) (laplacianContinuousLaw d x) := by
  have hm := measurable_ofReal_huntIntegrand_pair U hU t
  have hfin : (∫⁻ y in U, ∫⁻ w, ENNReal.ofReal (huntIntegrand U t y w)
      ∂laplacianContinuousLaw d x) ≠ ∞ := by
    have heq := lintegral_lintegral_huntIntegrand_eq_postExitMass hU ht hx univ MeasurableSet.univ
    rw [univ_inter] at heq
    rw [heq]
    exact measure_ne_top _ _
  filter_upwards [ae_lt_top hm.lintegral_prod_right' hfin] with y hy
  apply (lintegral_ofReal_ne_top_iff_integrable ?_
    (Eventually.of_forall (huntIntegrand_nonneg U t y))).1 hy.ne
  have harg : Measurable (fun w : ContinuousPath (Vec d) => ((t, y), w)) :=
    measurable_const.prodMk measurable_id
  exact ((measurable_huntIntegrand U hU).comp harg).aestronglyMeasurable

/-- The real exit correction equals its nonnegative path integral almost
everywhere in the terminal point. -/
theorem ofReal_huntCorrection_eq_lintegral_ae {U : Set (Vec d)} (hU : IsOpen U)
    {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U) :
    (fun y => ENNReal.ofReal (huntCorrection U t x y)) =ᵐ[volume.restrict U]
      fun y => ∫⁻ w, ENNReal.ofReal (huntIntegrand U t y w) ∂laplacianContinuousLaw d x := by
  filter_upwards [ae_integrable_huntIntegrand hU ht hx] with y hy
  exact ofReal_integral_eq_lintegral_ofReal hy
    (Eventually.of_forall (huntIntegrand_nonneg U t y))

/-- The complete fixed-horizon Hunt identity, unconditionally for the actual
variance-`2t` Brownian law, on every bounded open set and for every interior start. -/
theorem brownian_hunt_identity (d : ℕ) : BrownianHuntIdentity d := by
  intro U hU _hUb t ht x hx B hB
  rw [← lintegral_lintegral_huntIntegrand_eq_postExitMass hU ht hx B hB]
  apply lintegral_congr_ae
  symm
  simpa only [Measure.restrict_restrict hB] using
    ae_restrict_of_ae (s := B) (ofReal_huntCorrection_eq_lintegral_ae hU ht hx)

end SubdiffusiveProcess.Probability.Diffusion
