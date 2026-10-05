module

public import SubdiffusiveProcess.Probability.Diffusion.StoppedParameter
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import SubdiffusiveProcess.Probability.Diffusion.HuntCorrection
public import MarkovProcess.Trajectory.HarmonicRepresentation

@[expose] public section

/-!
# Fixed-horizon restart at the actual Brownian exit time

The remaining horizon is a stopped-measurable parameter. The strong Markov
identity therefore applies to its jointly measurable evaluation of the future
path, including on arbitrary open domains.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- Brownian restart before a fixed horizon allows an arbitrary measurable
observable of the exit time and the future path. -/
theorem setLIntegral_exitTime_shift_lt (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ) (x : Vec d) (F : ℝ × ContinuousPath (Vec d) → ENNReal)
    (hF : Measurable F) :
    (∫⁻ w in {w | ContinuousPath.exitTime U w < ENNReal.ofReal t},
      F ((ContinuousPath.exitTime U w).toReal,
        ContinuousPath.shift (ContinuousPath.exitTime U w).toNNReal w)
        ∂laplacianContinuousLaw d x) =
      ∫⁻ w in {w | ContinuousPath.exitTime U w < ENNReal.ofReal t},
        ∫⁻ η, F ((ContinuousPath.exitTime U w).toReal, η)
          ∂laplacianContinuousLaw d (w (ContinuousPath.exitTime U w).toNNReal)
        ∂laplacianContinuousLaw d x := by
  let : IsMarkovKernel (laplacianContinuousLaw d) := by
    unfold laplacianContinuousLaw
    infer_instance
  let τ := ContinuousPath.exitTime U
  let S := {w : ContinuousPath (Vec d) | τ w < ENNReal.ofReal t}
  have hτ := ContinuousPath.isStoppingTime_exitTime U hU
  have hS : MeasurableSet[hτ.measurableSpace] S := by
    simpa only [S, τ, ENNReal.ofReal] using! hτ.measurableSet_lt' (Real.toNNReal t)
  let κ : Kernel (ContinuousPath (Vec d)) (ContinuousPath (Vec d)) :=
    (laplacianContinuousLaw d).comap (fun w => w (τ w).toNNReal)
    (ContinuousPath.measurable_eval_untopD_stoppingTime τ hτ)
  let : IsMarkovKernel κ := by
    simpa only [κ, ENNReal.toNNReal] using!
      Kernel.IsMarkovKernel.comap (laplacianContinuousLaw d)
        (ContinuousPath.measurable_eval_untopD_stoppingTime τ hτ)
  have hJoint : ∀ A : Set (ContinuousPath (Vec d)), MeasurableSet[hτ.measurableSpace] A →
      ((laplacianContinuousLaw d x).restrict (A ∩ S)).map
        (fun w => ContinuousPath.shift (τ w).toNNReal w) =
          κ ∘ₘ (laplacianContinuousLaw d x).restrict (A ∩ S) := by
    intro A hA
    have h := isFeller_laplacianSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top
      (laplacianSemigroup d) isConservative_laplacianSemigroup
      kolmogorovRegular_laplacianSemigroup x τ hτ (A ∩ S) (hA.inter hS)
    have heq : (A ∩ S) ∩ {w | τ w < ∞} = A ∩ S := by
      apply inter_eq_left.mpr
      exact fun w hw => lt_trans hw.2 ENNReal.ofReal_lt_top
    have h' : Measure.map (fun w => ContinuousPath.shift (τ w).toNNReal w)
        ((laplacianContinuousLaw d x).restrict ((A ∩ S) ∩ {w | τ w < ∞})) =
        κ ∘ₘ (laplacianContinuousLaw d x).restrict ((A ∩ S) ∩ {w | τ w < ∞}) := by
      simpa only [κ, laplacianContinuousLaw, ENNReal.toNNReal] using! h
    rw [heq] at h'
    exact h'

  exact setLIntegral_stoppedParameter_eq (laplacianContinuousLaw d x) κ
    (fun w => ContinuousPath.shift (τ w).toNNReal w)
    (ContinuousPath.measurable_shift_untopD_stoppingTime τ hτ)
    hτ.measurableSpace_le S hJoint (fun w => (τ w).toReal)
    hτ.measurable.ennreal_toReal F hF

/-- The exit time, followed by the remaining horizon, is the original horizon. -/
theorem exitTime_add_remaining {U : Set (Vec d)} {t : ℝ} (ht : 0 < t)
    {w : ContinuousPath (Vec d)} (hw : ContinuousPath.exitTime U w < ENNReal.ofReal t) :
    (ContinuousPath.exitTime U w).toNNReal +
      Real.toNNReal (t - (ContinuousPath.exitTime U w).toReal) = Real.toNNReal t := by
  have hfin : ContinuousPath.exitTime U w ≠ ∞ := ne_top_of_lt hw
  have hlt : (ContinuousPath.exitTime U w).toReal < t := by
    simpa only [ENNReal.toReal_ofReal ht.le] using
      (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).2 hw
  apply NNReal.eq
  simp only [NNReal.coe_add, Real.coe_toNNReal _ (sub_pos.mpr hlt).le,
    Real.coe_toNNReal _ ht.le]
  change (ContinuousPath.exitTime U w).toReal +
    (t - (ContinuousPath.exitTime U w).toReal) = t
  ring

/-- The strict post-exit endpoint law is the free semigroup restarted at the
actual exit location with the actual random remaining time. -/
theorem measure_exitTime_lt_eval_eq_setLIntegral_semigroup
    (U : Set (Vec d)) (hU : IsOpen U) {t : ℝ} (ht : 0 < t) (x : Vec d)
    (B : Set (Vec d)) (hB : MeasurableSet B) :
    laplacianContinuousLaw d x {w | ContinuousPath.exitTime U w < ENNReal.ofReal t ∧
      w (Real.toNNReal t) ∈ B} =
      ∫⁻ w in {w | ContinuousPath.exitTime U w < ENNReal.ofReal t},
        laplacianSemigroup d (Real.toNNReal (t - (ContinuousPath.exitTime U w).toReal))
          (w (ContinuousPath.exitTime U w).toNNReal) B ∂laplacianContinuousLaw d x := by
  let S := {w : ContinuousPath (Vec d) | ContinuousPath.exitTime U w < ENNReal.ofReal t}
  let F : ℝ × ContinuousPath (Vec d) → ENNReal :=
    fun z => B.indicator (fun _ => 1) (z.2 (Real.toNNReal (t - z.1)))
  have heval : Measurable (fun z : ℝ × ContinuousPath (Vec d) =>
      z.2 (Real.toNNReal (t - z.1))) := by
    exact (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_const.sub measurable_fst).real_toNNReal.prodMk measurable_snd)
  have hF : Measurable F := (measurable_const.indicator hB).comp heval
  have h := setLIntegral_exitTime_shift_lt U hU t x F hF
  have hleft : (∫⁻ w in S, F ((ContinuousPath.exitTime U w).toReal,
      ContinuousPath.shift (ContinuousPath.exitTime U w).toNNReal w)
        ∂laplacianContinuousLaw d x) =
      laplacianContinuousLaw d x {w | ContinuousPath.exitTime U w < ENNReal.ofReal t ∧
        w (Real.toNNReal t) ∈ B} := by
    have hmeas : Measurable (fun w : ContinuousPath (Vec d) => w (Real.toNNReal t)) :=
      ContinuousPath.measurable_coordinateProcess (Real.toNNReal t)
    calc
      _ = ∫⁻ w in S, ((fun w : ContinuousPath (Vec d) => w (Real.toNNReal t)) ⁻¹' B).indicator (fun _ => (1 : ENNReal)) w
          ∂laplacianContinuousLaw d x := by
        apply setLIntegral_congr_fun
        · exact measurableSet_lt (ContinuousPath.measurable_exitTime U hU) measurable_const
        · intro w hw
          dsimp only [F]
          rw [ContinuousPath.shift_apply, exitTime_add_remaining ht hw]
          rfl
      _ = _ := by
        rw [lintegral_indicator (hmeas hB), lintegral_one, Measure.restrict_apply_univ,
          Measure.restrict_apply (hmeas hB)]
        congr 1
        ext w
        simp only [S, mem_inter_iff, mem_preimage, mem_ofPred_eq, and_comm]
  rw [hleft] at h
  refine h.trans (setLIntegral_congr_fun ?_ fun w _ => ?_)
  · exact measurableSet_lt (ContinuousPath.measurable_exitTime U hU) measurable_const
  · dsimp only [F]
    have heval' : Measurable (fun η : ContinuousPath (Vec d) =>
        η (Real.toNNReal (t - (ContinuousPath.exitTime U w).toReal))) :=
      ContinuousPath.measurable_coordinateProcess _
    rw [← lintegral_map (measurable_const.indicator hB)
      heval']
    rw [← Kernel.map_apply _ heval',
      laplacianContinuousLaw_map_eval, lintegral_indicator hB, lintegral_one,
      Measure.restrict_apply_univ]

end SubdiffusiveProcess.Probability.Diffusion
