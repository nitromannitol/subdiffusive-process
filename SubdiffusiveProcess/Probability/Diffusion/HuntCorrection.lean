module

public import SubdiffusiveProcess.Probability.Diffusion.GaussianKernel
public import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput

@[expose] public section

/-!
# The explicit exit correction and the remaining Hunt inputs

The correction is an integral over the constructed Brownian law, using the
actual exit time and exit location. Its measurability and the splitting of
free transition mass into survival and post-exit mass are unconditional.

`BrownianHuntIdentity` is the still missing fixed-horizon strong-Markov
calculation with the random remaining time. `BrownianHuntContinuity` is the
still missing interior regularity of that correction. Neither follows just
by invoking dominated convergence for the free Gaussian: the starting law
also varies with the starting point.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.Model.LifetimeProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularityKilled
open scoped ENNReal NNReal BigOperators Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The pathwise term in Hunt's formula, zero unless exit is strictly before `t`. -/
def huntIntegrand (U : Set (Vec d)) (t : ℝ) (y : Vec d)
    (w : ContinuousPath (Vec d)) : ℝ :=
  {w : ContinuousPath (Vec d) | ContinuousPath.exitTime U w < ENNReal.ofReal t}.indicator
    (fun w => laplacianDensity (t - (ContinuousPath.exitTime U w).toReal)
      (w (ContinuousPath.exitTime U w).toNNReal) y) w

/-- The literal Brownian exit correction; proving its analytic properties is
part of T1b, not a consequence of defining this integral. -/
def huntCorrection (U : Set (Vec d)) (t : ℝ) (x y : Vec d) : ℝ :=
  ∫ w, huntIntegrand U t y w ∂laplacianContinuousLaw d x

theorem huntIntegrand_nonneg (U : Set (Vec d)) (t : ℝ) (y : Vec d)
    (w : ContinuousPath (Vec d)) : 0 ≤ huntIntegrand U t y w :=
  Set.indicator_nonneg (fun _ _ => laplacianDensity_nonneg _ _ _) w

theorem huntCorrection_nonneg (U : Set (Vec d)) (t : ℝ) (x y : Vec d) :
    0 ≤ huntCorrection U t x y :=
  integral_nonneg (huntIntegrand_nonneg U t y)

/-- The pathwise correction is measurable jointly in its parameters and path. -/
theorem measurable_huntIntegrand (U : Set (Vec d)) (hU : IsOpen U) :
    Measurable (fun z : (ℝ × Vec d) × ContinuousPath (Vec d) =>
      huntIntegrand U z.1.1 z.1.2 z.2) := by
  have hτ := ContinuousPath.measurable_exitTime U hU
  have he := ContinuousPath.measurable_eval_untopD_stoppingTime
    (ContinuousPath.exitTime U) (ContinuousPath.isStoppingTime_exitTime U hU)
  have he' : Measurable (fun w : ContinuousPath (Vec d) =>
      w (ContinuousPath.exitTime U w).toNNReal) := he
  have harg : Measurable (fun z : (ℝ × Vec d) × ContinuousPath (Vec d) =>
      (z.1.1 - (ContinuousPath.exitTime U z.2).toReal,
        z.2 (ContinuousPath.exitTime U z.2).toNNReal, z.1.2)) :=
    ((measurable_fst.comp measurable_fst).sub (hτ.ennreal_toReal.comp measurable_snd)).prodMk
      ((he'.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst))
  have hset : MeasurableSet {z : (ℝ × Vec d) × ContinuousPath (Vec d) |
      ContinuousPath.exitTime U z.2 < ENNReal.ofReal z.1.1} :=
    measurableSet_lt (hτ.comp measurable_snd)
      ((measurable_fst.comp measurable_fst).ennreal_ofReal)
  exact ((measurable_laplacianDensity (d := d)).comp harg).indicator hset

/-- Integration against the actual parameterized Brownian law preserves measurability. -/
theorem measurable_huntCorrection (U : Set (Vec d)) (hU : IsOpen U) :
    Measurable (fun z : ℝ × Vec d × Vec d => huntCorrection U z.1 z.2.1 z.2.2) := by
  letI : IsMarkovKernel (laplacianContinuousLaw d) := by
    unfold laplacianContinuousLaw
    infer_instance
  let κ : Kernel (ℝ × Vec d × Vec d) (ContinuousPath (Vec d)) :=
    (laplacianContinuousLaw d).comap
      (fun z : ℝ × Vec d × Vec d => z.2.1) (measurable_fst.comp measurable_snd)
  letI : IsMarkovKernel κ := by dsimp [κ]; infer_instance
  have harg : Measurable (fun z : (ℝ × Vec d × Vec d) × ContinuousPath (Vec d) =>
      ((z.1.1, z.1.2.2), z.2)) := by fun_prop
  have hf := ((measurable_huntIntegrand U hU).comp harg).stronglyMeasurable
  exact (hf.integral_kernel_prod_right' (κ := κ)).measurable

/-- Spatial measurability of the exit correction at a fixed time. -/
theorem measurable_uncurry_huntCorrection (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ) :
    Measurable (Function.uncurry (huntCorrection U t)) := by
  change Measurable (fun z : Vec d × Vec d => huntCorrection U t z.1 z.2)
  exact (measurable_huntCorrection U hU).comp
    (show Measurable (fun z : Vec d × Vec d => (t, z)) from
      measurable_const.prodMk measurable_id)

/-- Post-exit endpoint mass in the domain. The event includes `τ = t`; for an
interior start, such paths are outside the open domain at time `t`. -/
def postExitMass (U : Set (Vec d)) (t : ℝ) (x : Vec d) (B : Set (Vec d)) : ENNReal :=
  laplacianContinuousLaw d x {w |
    ContinuousPath.exitTime U w ≤ (Real.toNNReal t : ENNReal) ∧
      w (Real.toNNReal t) ∈ B ∩ U}

/-- Free transition mass splits into survival and post-exit mass. This step
uses only pathwise killing and the already proved Gaussian marginals. -/
theorem laplacianSemigroup_eq_killed_add_postExit (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ) (x : Vec d) (B : Set (Vec d)) (hB : MeasurableSet B) :
    laplacianSemigroup d (Real.toNNReal t) x (B ∩ U) =
      killedKernel (laplacianLaw d) U hU (Real.toNNReal t) x B + postExitMass U t x B := by
  let tt := Real.toNNReal t
  let E := (fun w : ContinuousPath (Vec d) => w tt) ⁻¹' (B ∩ U)
  let S := {w : ContinuousPath (Vec d) | (tt : ENNReal) < ContinuousPath.exitTime U w}
  have hS : MeasurableSet S :=
    measurableSet_lt measurable_const (ContinuousPath.measurable_exitTime U hU)
  have hES : E ∩ S = ContinuousPath.killedEvent U tt B := by
    ext w
    simp only [E, S, mem_inter_iff, mem_preimage, mem_setOf_eq,
      ContinuousPath.mem_killedEvent_iff]
    constructor
    · exact fun h => ⟨h.2, h.1.1⟩
    · exact fun h => ⟨⟨h.2, ContinuousPath.mem_of_lt_exitTime U w tt h.1⟩, h.1⟩
  have hdiff : E \ S = {w : ContinuousPath (Vec d) |
      ContinuousPath.exitTime U w ≤ (tt : ENNReal) ∧ w tt ∈ B ∩ U} := by
    ext w
    simp only [E, S, mem_diff, mem_preimage, mem_setOf_eq, not_lt, and_comm]
  have hsplit := measure_inter_add_diff (μ := laplacianContinuousLaw d x) E hS
  rw [hES, hdiff] at hsplit
  rw [laplacianLaw, killedKernel_lifetimeProcess,
    SubMarkovKernelSemigroup.IsConservative.killedKernel_apply _ _ U hU tt x hB]
  rw [← laplacianContinuousLaw_map_eval tt,
    Kernel.map_apply' (laplacianContinuousLaw d)
      (show Measurable (fun w : ContinuousPath (Vec d) => w tt) from
        ContinuousPath.measurable_coordinateProcess tt) x (hB.inter hU.measurableSet)]
  exact hsplit.symm

/-- Missing fixed-horizon Hunt identity for the actual exit correction. Its
proof must justify the random remaining-time restart and the integrals. -/
def BrownianHuntIdentity (d : ℕ) : Prop :=
  ∀ U : Set (Vec d), IsOpen U → Bornology.IsBounded U →
    ∀ t : ℝ, 0 < t → ∀ x ∈ U, ∀ B : Set (Vec d), MeasurableSet B →
      postExitMass U t x B =
        ∫⁻ y in B ∩ U, ENNReal.ofReal (huntCorrection U t x y)

/-- Missing interior continuity, including continuity in the starting point. -/
def BrownianHuntContinuity (d : ℕ) : Prop :=
  ∀ U : Set (Vec d), IsOpen U → Bornology.IsBounded U →
    ContinuousOn (fun z : ℝ × Vec d × Vec d => huntCorrection U z.1 z.2.1 z.2.2)
      (Ioi 0 ×ˢ U ×ˢ U)

end SubdiffusiveProcess.Probability.Diffusion
