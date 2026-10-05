
module

public import MarkovProcess.Trajectory.DynkinMartingale
public import SubdiffusiveProcess.Processes.FellerRealizationRestart

@[expose] public section

/-! Deterministic Dynkin identities for the actual supplied continuous-path
realization. Adapted from MarkovProcess.Trajectory.Dynkin: its moment hypothesis
is used only to construct the canonical law; here the supplied exact FDDs
provide every one-time marginal directly. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty
namespace SubdiffusiveProcess.Section10

variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha)

omit [SecondCountableTopology alpha] [LocallyCompactSpace alpha] in
/-- Every deterministic-time marginal of the supplied law is the transition law. -/
theorem realization_map_eval
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I) (t : NNReal) :
    Q.map (fun path ↦ path t) = P t := by
  classical
  let I : Finset NNReal := {t}
  let z : I := ⟨t, Finset.mem_singleton_self t⟩
  let i : Fin I.card := (I.orderIsoOfFin rfl).symm z
  let e : Fin 1 ↪o Fin I.card := OrderEmbedding.ofStrictMono (fun _ ↦ i) (by
    intro a b hab
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    simp only [ha, hb, lt_self_iff_false] at hab)
  have hfun : (fun path : ContinuousPath alpha ↦ path t) =
      (fun path : I → alpha ↦ path z) ∘ ContinuousPath.finsetEvaluation I := rfl
  have hEval : Measurable (ContinuousPath.finsetEvaluation (alpha := alpha) I) :=
    measurable_pi_iff.mpr fun t ↦ ContinuousPath.measurable_coordinateProcess t
  rw [hfun, Kernel.map_comp_right Q hEval
    (measurable_pi_apply z), hfdd I, finiteSetKernel_eq_map,
    ← Kernel.map_comp_right _ (measurable_orderedPathToFiniteSet I)
      (measurable_pi_apply z)]
  change (finiteTimeKernel P (finiteSetTimes I)).map (fun path ↦ path i) = _
  have hfun' : (fun path : Fin I.card → alpha ↦ path i) =
      (fun path : Fin 1 → alpha ↦ path 0) ∘ FiniteOrderedTimes.restrictPath e := rfl
  rw [hfun', Kernel.map_comp_right _ (FiniteOrderedTimes.measurable_restrictPath e)
    (measurable_pi_apply 0), hP.finiteTimeKernel_map_restrictPath P,
    finiteTimeKernel_one_map_eval]
  have htime : ((finiteSetTimes I).restrict e) 0 = t := by
    change ((I.orderIsoOfFin rfl ((I.orderIsoOfFin rfl).symm z) : I) : NNReal) = t
    rw [OrderIso.apply_symm_apply]
  rw [htime]


omit [SecondCountableTopology alpha] [LocallyCompactSpace alpha] in
/-- Position expectation under the supplied realization. -/
theorem integral_eval_realization
    (hP : P.IsConservative)
    (Q : Kernel alpha (ContinuousPath alpha))
    [IsMarkovKernel Q] (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I) (t : NNReal) (x : alpha)
    (f : C₀(alpha, ℝ)) :
    ∫ omega, f (omega t) ∂(Q x) = ∫ y, f y ∂(P t x) := by
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦ omega t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  have h := integral_map (μ := Q x) hmeas.aemeasurable
    (f := fun y ↦ f y) f.continuous.aestronglyMeasurable
  rw [← h, ← Kernel.map_apply _ hmeas, realization_map_eval P hP Q hfdd t]


omit [SecondCountableTopology alpha] in
/-- The actual expectation semigroup. -/
theorem c0Semigroup_apply_eq_integral_realization
    (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (Q : Kernel alpha (ContinuousPath alpha))
    [IsMarkovKernel Q] (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I) (t : NNReal) (x : alpha)
    (f : C₀(alpha, ℝ)) :
    hFeller.c0Semigroup t f x =
      ∫ omega, f (omega t) ∂(Q x) := by
  rw [IsFellerKernelSemigroup.c0Semigroup_apply_apply, kernelIntegral,
    integral_eval_realization P hP Q hfdd t x f]


/-- The deterministic Dynkin formula under the supplied realization. -/
theorem integral_eval_sub_eq_integral_integral_generator_realization
    (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (Q : Kernel alpha (ContinuousPath alpha))
    [IsMarkovKernel Q] (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (f : hFeller.c0Semigroup.generatorDomain) (t : NNReal) (x : alpha) :
    ∫ omega, (f : C₀(alpha, ℝ)) (omega t) ∂(Q x) -
        (f : C₀(alpha, ℝ)) x =
      ∫ omega, (∫ s in (0 : ℝ)..t, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
        ∂(Q x) := by
  have hint : IntervalIntegrable
      (fun s : ℝ ↦ hFeller.c0Semigroup (Real.toNNReal s) (hFeller.c0Semigroup.generator f))
      volume 0 t :=
    (hFeller.c0Semigroup.continuous_operator_toNNReal _).intervalIntegrable _ _
  have hstep : ∫ omega, (f : C₀(alpha, ℝ)) (omega t) ∂(Q x) -
      (f : C₀(alpha, ℝ)) x =
      ∫ s in (0 : ℝ)..t, ∫ omega, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s))
        ∂(Q x) := by
    calc ∫ omega, (f : C₀(alpha, ℝ)) (omega t) ∂(Q x) -
          (f : C₀(alpha, ℝ)) x
        = c0EvalCLM x (hFeller.c0Semigroup t (f : C₀(alpha, ℝ)) - (f : C₀(alpha, ℝ))) := by
          rw [map_sub, c0EvalCLM_apply, c0EvalCLM_apply,
            c0Semigroup_apply_eq_integral_realization P hP hFeller Q hfdd t x]
      _ = c0EvalCLM x (∫ s in (0 : ℝ)..t,
            hFeller.c0Semigroup (Real.toNNReal s) (hFeller.c0Semigroup.generator f)) := by
          rw [hFeller.c0Semigroup.operator_sub_eq_integral f t]
      _ = ∫ s in (0 : ℝ)..t,
            c0EvalCLM x (hFeller.c0Semigroup (Real.toNNReal s) (hFeller.c0Semigroup.generator f)) :=
          ((c0EvalCLM x).intervalIntegral_comp_comm hint).symm
      _ = ∫ s in (0 : ℝ)..t, ∫ omega, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s))
            ∂(Q x) := by
          refine intervalIntegral.integral_congr fun s _ ↦ ?_
          rw [c0EvalCLM_apply, c0Semigroup_apply_eq_integral_realization P hP hFeller Q hfdd]
  rw [hstep]
  have hcont : Continuous fun p : ℝ × ContinuousPath alpha ↦
      (hFeller.c0Semigroup.generator f) (p.2 (Real.toNNReal p.1)) :=
    (hFeller.c0Semigroup.generator f).continuous.comp
      ((ContinuousEval.continuous_eval.comp continuous_swap).comp
        (continuous_real_toNNReal.fst'.prodMk continuous_snd))
  have hbound : ∀ p : ℝ × ContinuousPath alpha,
      ‖(hFeller.c0Semigroup.generator f) (p.2 (Real.toNNReal p.1))‖ ≤
        ‖hFeller.c0Semigroup.generator f‖ := fun p ↦ by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact BoundedContinuousFunction.norm_coe_le_norm (hFeller.c0Semigroup.generator f).toBCF
      (p.2 (Real.toNNReal p.1))
  have hprodint : Integrable
      (Function.uncurry fun (s : ℝ) (omega : ContinuousPath alpha) ↦
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
      ((volume.restrict (Set.Ioc (0 : ℝ) t)).prod (Q x)) :=
    Integrable.of_bound hcont.aestronglyMeasurable _ (Eventually.of_forall hbound)
  rw [intervalIntegral.integral_of_le t.coe_nonneg, integral_integral_swap hprodint]
  refine integral_congr_ae (Eventually.of_forall fun omega ↦ ?_)
  exact (intervalIntegral.integral_of_le t.coe_nonneg).symm

end SubdiffusiveProcess.Section10
