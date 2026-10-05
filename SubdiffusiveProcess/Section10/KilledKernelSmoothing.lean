module

public import SubdiffusiveProcess.Section10.FellerLocalL1Continuity
public import SubdiffusiveProcess.Section10.TorsionExitDynkinExpectation
public import SubdiffusiveProcess.Section10.PhysicalAttachmentRestart
public import SubdiffusiveProcess.Probability.Diffusion.AnalyticBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationKernelIntegral

@[expose] public section

/-! Deterministic-time smoothing of the actual killed transition law.
Restart gives the killed semigroup identity. Removing its short initial
survival restriction costs at most the probability of exit at or before
that short time; equality at exit and infinite exits retain their literal
strict-survival meanings. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Section10

/-- The existing lifetime killed kernel integrates precisely on surviving
paths of the original continuous-path law. -/
theorem killedKernel_integral_ofContinuousPath {d : ℕ}
    (K : Kernel (Vec d) (ContinuousPath (Vec d)))
    (U : Set (Vec d)) (hU : IsOpen U) (s : NNReal)
    {f : Vec d → ℝ} (hf : Measurable f) (x : Vec d) :
    (∫ y, f y ∂killedKernel (K.map LifetimePath.ofContinuousPath) U hU s x) =
      ∫ w in {w | (s : ENNReal) < ContinuousPath.exitTime U w}, f (w s) ∂K x := by
  have hS : MeasurableSet {w : Path d | (s : ENNReal) < LifetimePath.exitTime U w} :=
    (LifetimePath.canonicalFiltration.le' s) _
      ((LifetimePath.isStoppingTime_exitTime U hU).measurableSet_gt s)
  have hCS := ContinuousPath.measurableSet_lt_exitTime U hU s
  rw [← show kernelIntegral (killedKernel (K.map LifetimePath.ofContinuousPath) U hU s) f x =
      (∫ y, f y ∂killedKernel (K.map LifetimePath.ofContinuousPath) U hU s x) from rfl,
    killedKernel_integral (K.map LifetimePath.ofContinuousPath) U hU s f hf x,
    ← integral_indicator hS,
    Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath]
  refine (integral_map LifetimePath.measurable_ofContinuousPath.aemeasurable
    ((hf.comp (position_fixed_measurable s)).indicator hS).aestronglyMeasurable).trans ?_
  rw [← integral_indicator hCS]
  apply integral_congr_ae
  filter_upwards [] with w
  by_cases hw : (s : ENNReal) < ContinuousPath.exitTime U w
  · simp only [Function.comp_def, LifetimePath.exitTime_ofContinuousPath, hw, mem_ofPred_eq,
      Set.indicator_of_mem, position, LifetimePath.coordinate_ofContinuousPath,
      Sum.elim_inl, id_eq]
  · simp only [Function.comp_def, Set.indicator_apply, mem_ofPred_eq,
      LifetimePath.exitTime_ofContinuousPath, ite_eq_right hw]

/-- The killed semigroup law, read as a bounded real mass integral. -/
theorem killedKernel_mass_add {d : ℕ}
    (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (hSM : StrongMarkov law) (U : Set (Vec d)) (hU : IsOpen U)
    (s r : NNReal) (x : Vec d) (B : Set (Vec d)) (hB : MeasurableSet B) :
    (killedKernel law U hU (s + r) x B).toReal =
      ∫ y, (killedKernel law U hU r y B).toReal ∂killedKernel law U hU s x := by
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup.semigroup
    law hSM U hU s r, Kernel.comp_apply' _ _ _ hB]
  apply (integral_toReal ((killedKernel law U hU r).measurable_coe hB).aemeasurable _).symm
  filter_upwards [] with y
  exact (killedKernel_subMarkov law U hU r).measure_le_one y B |>.trans_lt (by simp)

/-- A bounded observable's full expectation and killed expectation differ
by at most its bound times the probability of early exit, including ties. -/
theorem abs_free_sub_killed_integral_le_exit {d : ℕ}
    (P : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset NNReal,
      K.map (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P I)
    (U : Set (Vec d)) (hU : IsOpen U) (s : NNReal)
    {f : Vec d → ℝ} (hf : Measurable f) (hbound : ∀ y, |f y| ≤ 1) (x : Vec d) :
    |kernelIntegral (P s) f x -
      ∫ y, f y ∂killedKernel (K.map LifetimePath.ofContinuousPath) U hU s x| ≤
        (K x {w | ContinuousPath.exitTime U w ≤ (s : ENNReal)}).toReal := by
  have hev : Measurable (fun w : ContinuousPath (Vec d) => w s) :=
    ContinuousPath.measurable_coordinateProcess s
  have hfull : kernelIntegral (P s) f x = ∫ w, f (w s) ∂K x := by
    have hm := realization_map_eval P hP K hfdd s
    rw [kernelIntegral, ← hm, Kernel.map_apply _ hev,
      integral_map hev.aemeasurable hf.aestronglyMeasurable]
  have hsurv := ContinuousPath.measurableSet_lt_exitTime U hU s
  have hint : Integrable (fun w : ContinuousPath (Vec d) => f (w s)) (K x) :=
    integrable_of_measurable_abs_le _ (hf.comp hev) (fun w => hbound (w s))
  have hcomp : {w : ContinuousPath (Vec d) | (s : ENNReal) < ContinuousPath.exitTime U w}ᶜ =
      {w | ContinuousPath.exitTime U w ≤ (s : ENNReal)} := by
    ext w
    simp only [Set.mem_compl_iff, mem_ofPred_eq, not_lt]
  rw [hfull, killedKernel_integral_ofContinuousPath K U hU s hf x,
    ← setIntegral_compl hsurv hint, hcomp, ← Real.norm_eq_abs]
  calc
    ‖∫ w in {w | ContinuousPath.exitTime U w ≤ (s : ENNReal)}, f (w s) ∂K x‖
      ≤ ∫ _w in {w | ContinuousPath.exitTime U w ≤ (s : ENNReal)}, (1 : ℝ) ∂K x :=
      norm_integral_le_of_norm_le (integrable_const 1)
        (Eventually.of_forall (fun w => hbound (w s)))
    _ = (K x {w | ContinuousPath.exitTime U w ≤ (s : ENNReal)}).toReal := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, mul_one, measureReal_def]

/-- Smoothing the actual killed mass with the original whole-space kernel
has error bounded by the original law's short-time exit probability. -/
theorem abs_killed_smoothing_error_le_exit {d : ℕ}
    (P : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset NNReal,
      K.map (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P I)
    (U : Set (Vec d)) (hU : IsOpen U) (s r : NNReal)
    (x : Vec d) (B : Set (Vec d)) (hB : MeasurableSet B) :
    |(killedKernel (K.map LifetimePath.ofContinuousPath) U hU (s + r) x B).toReal -
      kernelIntegral (P s)
        (fun y => (killedKernel (K.map LifetimePath.ofContinuousPath) U hU r y B).toReal) x| ≤
      (K x {w | ContinuousPath.exitTime U w ≤ (s : ENNReal)}).toReal := by
  let law := K.map LifetimePath.ofContinuousPath
  let : IsMarkovKernel law := Kernel.IsMarkovKernel.map K LifetimePath.measurable_ofContinuousPath
  let : IsFiniteKernel (killedKernel law U hU r) :=
    (killedKernel_subMarkov law U hU r).isFiniteKernel
  have hSM : StrongMarkov law := SubdiffusiveProcess.Probability.Diffusion.strongMarkov_of_restart
    (PhysicalAttachment.fellerRestart d P hP hFeller K inferInstance
      (fun I x => congrArg (fun Q : Kernel (Vec d) (I → Vec d) => Q x) (hfdd I)))
  let f : Vec d → ℝ := fun y => (killedKernel law U hU r y B).toReal
  have hf : Measurable f := ((killedKernel law U hU r).measurable_coe hB).ennreal_toReal
  have hbound : ∀ y, |f y| ≤ 1 := by
    intro y
    rw [abs_of_nonneg ENNReal.toReal_nonneg, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
      ((killedKernel_subMarkov law U hU r).measure_le_one y B)
  rw [killedKernel_mass_add law hSM U hU s r x B hB, abs_sub_comm]
  exact abs_free_sub_killed_integral_le_exit P hP K hfdd U hU s hf hbound x

end SubdiffusiveProcess.Section10
