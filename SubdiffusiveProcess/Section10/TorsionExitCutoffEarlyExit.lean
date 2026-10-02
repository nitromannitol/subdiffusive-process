import SubdiffusiveProcess.Section10.TorsionExitBassInterfaces
import SubdiffusiveProcess.Section10.TorsionExitDynkinStopping
import MarkovProcess.Trajectory.ExpectedExitTime
import Homogenization.Sobolev.Foundations.Cutoff.OpenSet

/-! Compact smooth cutoffs and bounded optional stopping control early exit
under the ORIGINAL supplied Feller law. There is no path-law tightness,
Kolmogorov, Brownian, heat-kernel or SDE hypothesis. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open MarkovProcess.SubMarkovKernelSemigroup
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal ZeroAtInfty CompactlySupported
namespace SubdiffusiveProcess.Section10

/-- A native compact C-infinity cutoff, between zero and one, equals one on
any compact subset of any open set. The open set need not be bounded. -/
theorem exists_compact_smooth_cutoff {d : ℕ} {U S : Set (Vec d)}
    (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ w : C_c(Vec d, ℝ), ContDiff ℝ (⊤ : ℕ∞) (w : Vec d → ℝ) ∧
      (∀ y, 0 ≤ w y ∧ w y ≤ 1) ∧ Set.EqOn w 1 S ∧ tsupport w ⊆ U := by
  obtain ⟨r, _, hSr⟩ := hS.isBounded.subset_ball_lt 0 (0 : Vec d)
  let V := U ∩ Metric.ball (0 : Vec d) r
  have hSV : S ⊆ V := fun x hx => ⟨hSU hx, hSr hx⟩
  obtain ⟨w, hw, hb, hOne, hsupp⟩ :=
    exists_contDiff_one_on_compact_tsupport_subset hS hSV
      (hU.inter Metric.isOpen_ball)
  have hcomp : HasCompactSupport w :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport w) (Metric.isBounded_ball.subset
      (fun x hx => (hsupp hx).2))
  exact ⟨⟨⟨w, hw.continuous⟩, hcomp⟩, hw, hb, hOne, fun x hx => (hsupp hx).1⟩

/-- Exit by time t forces the stopped cutoff value to vanish, including exit
exactly at t. Infinite exit cannot belong to the event. -/
theorem cutoff_exitTimeTrunc_eq_zero {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (w : C_c(Vec d, ℝ)) (hsupp : tsupport w ⊆ U)
    (path : ContinuousPath (Vec d)) (hzero : path 0 ∈ U) (t : NNReal)
    (hexit : ContinuousPath.exitTime U path ≤ (t : ENNReal)) :
    w (path (ContinuousPath.exitTimeTrunc U t path)) = 0 := by
  have hfin : ContinuousPath.exitTime U path ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hexit
  have hT : ContinuousPath.exitTimeTrunc U t path =
      (ContinuousPath.exitTime U path).toNNReal := by
    have hcoe : (ContinuousPath.exitTimeTrunc U t path : ENNReal) =
        ContinuousPath.exitTime U path := by
      rw [ContinuousPath.coe_exitTimeTrunc_ennreal,
        min_eq_left hexit]
    simpa only [ENNReal.toNNReal_coe] using congrArg ENNReal.toNNReal hcoe
  rw [hT]
  have hnot := (ContinuousPath.coordinate_exitTime_mem_frontier U hU path hzero hfin).2
  apply image_eq_zero_of_notMem_tsupport
  exact fun hx => hnot (hU.interior_eq.symm ▸ hsupp hx)

/-- A generator cutoff gives the literal uniform short-time probability bound
at all starts where the cutoff is one. -/
theorem earlyExit_le_of_generator_cutoff {d : ℕ}
    (P : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)
    (hF : P.IsFellerKernelSemigroup) (K : Kernel (Vec d) (ContinuousPath (Vec d)))
    [IsMarkovKernel K] (hfdd : ∀ I : Finset NNReal,
      K.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (hzero : ∀ x, ∀ᵐ path ∂K x, path (0 : NNReal) = x)
    (f : hF.c0Semigroup.generatorDomain) {U : Set (Vec d)} (hU : IsOpen U)
    (hb : ∀ y, 0 ≤ (f : C₀(Vec d, ℝ)) y ∧ (f : C₀(Vec d, ℝ)) y ≤ 1)
    (hsupp : tsupport (f : Vec d → ℝ) ⊆ U) {x : Vec d} (hx : x ∈ U)
    (hfx : (f : C₀(Vec d, ℝ)) x = 1) (t : NNReal) :
    K x {path | ContinuousPath.exitTime U path ≤ (t : ENNReal)} ≤
      ENNReal.ofReal ((t : ℝ) * ‖hF.c0Semigroup.generator f‖) := by
  let T := ContinuousPath.exitTimeTrunc U t
  have hT := ContinuousPath.isStoppingTime_exitTimeTrunc U hU t
  have hTt := ContinuousPath.exitTimeTrunc_le U t
  have hpos : Integrable (fun path : ContinuousPath (Vec d) ↦
      (f : C₀(Vec d, ℝ)) (path (T path))) (K x) :=
    Integrable.of_bound
      (((f : C₀(Vec d, ℝ)).continuous.measurable.comp
        (ContinuousPath.measurable_eval_stoppingTime_borel T hT)).aestronglyMeasurable)
      1 (Eventually.of_forall fun path => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hb _).1] using (hb _).2)
  let E := {path : ContinuousPath (Vec d) | ContinuousPath.exitTime U path ≤ (t : ENNReal)}
  have hE : MeasurableSet E := by
    convert (ContinuousPath.measurableSet_lt_exitTime U hU t).compl using 1
    ext path
    simp only [mem_setOf_eq, mem_compl_iff, not_lt, E]
  have hlo := integral_eval_stoppingTime_ge_realization P hP hF K hfdd f T hT hTt x
  rw [hfx] at hlo
  have hcmp : E.indicator (fun _ => (1 : ℝ)) ≤ᵐ[K x]
      fun path => 1 - (f : C₀(Vec d, ℝ)) (path (T path)) := by
    filter_upwards [hzero x] with path hp
    by_cases he : path ∈ E
    · rw [indicator_of_mem he]
      have hfin : ContinuousPath.exitTime U path ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.coe_ne_top he
      have hTe : T path = (ContinuousPath.exitTime U path).toNNReal := by
        have hcoe : (ContinuousPath.exitTimeTrunc U t path : ENNReal) =
            ContinuousPath.exitTime U path := by
          rw [ContinuousPath.coe_exitTimeTrunc_ennreal,
            min_eq_left he]
        simpa only [ENNReal.toNNReal_coe] using congrArg ENNReal.toNNReal hcoe
      have hnot := (ContinuousPath.coordinate_exitTime_mem_frontier U hU path
        (hp ▸ hx) hfin).2
      have hfzero : (f : C₀(Vec d, ℝ)) (path (T path)) = 0 := by
        rw [hTe]
        exact image_eq_zero_of_notMem_tsupport (fun h => hnot (hU.interior_eq.symm ▸ hsupp h))
      simp only [hfzero, sub_zero, le_refl]
    · rw [indicator_of_notMem he]
      exact sub_nonneg.mpr (hb _).2
  have hm := integral_mono_ae ((integrable_const (1 : ℝ)).indicator hE)
    ((integrable_const (1 : ℝ)).sub hpos) hcmp
  change (∫ path, E.indicator (fun _ => (1 : ℝ)) path ∂K x) ≤
    ∫ path, 1 - (f : C₀(Vec d, ℝ)) (path (T path)) ∂K x at hm
  rw [integral_indicator_const (1 : ℝ) hE, smul_eq_mul, mul_one,
    integral_sub (integrable_const (1 : ℝ)) hpos, integral_const,
    probReal_univ, one_smul] at hm
  change (K x E).toReal ≤ 1 -
    ∫ path, (f : C₀(Vec d, ℝ)) (path (T path)) ∂K x at hm
  have hreal : (K x E).toReal ≤ (t : ℝ) * ‖hF.c0Semigroup.generator f‖ := by
    linarith only [hm, hlo]
  rw [← ENNReal.ofReal_toReal (measure_ne_top (K x) E)]
  exact ENNReal.ofReal_le_ofReal hreal

end SubdiffusiveProcess.Section10
