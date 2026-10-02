/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import SubdiffusiveProcess.Section10.TorsionExitDynkinExpectation

/-! Dynkin martingales under the actual finite-dimensional realization.
Reuse the existing event-restricted Feller restart and Dynkin decomposition;
no Kolmogorov moment criterion, SDE realization or Itô input is imposed. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty
namespace SubdiffusiveProcess.Section10
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

/-- The actual law restarts conditionally at every deterministic time. -/
theorem condExp_shift_realization (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (Q : Kernel alpha (ContinuousPath alpha))
    [IsMarkovKernel Q] (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (x : alpha) (s : NNReal) (F : ContinuousPath alpha → ℝ)
    (hF : StronglyMeasurable F) (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    (Q x)[fun omega ↦ F (ContinuousPath.shift s omega)|
      ContinuousPath.canonicalFiltration (alpha := alpha) s] =ᵐ[Q x]
      fun omega ↦ ∫ eta, F eta ∂Q (omega s) := by
  apply ContinuousPath.condExp_shift_ae_eq_integral_pathKernel_of_restrict_map Q x s
  · exact hFeller.realization_restrict_map_shift P hP
      (ContinuousMap.const NNReal (Classical.arbitrary alpha)) Q hfdd x s
  · exact hF
  · exact hFC

omit [CompleteSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha] in
/-- The expectation of the actual Dynkin martingale is its initial value. -/
theorem integral_dynkinProcess_realization (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (Q : Kernel alpha (ContinuousPath alpha))
    [IsMarkovKernel Q] (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I) (f : hFeller.c0Semigroup.generatorDomain) (u : NNReal)
    (y : alpha) :
    ∫ omega, hFeller.dynkinProcess f u omega ∂(Q y) =
      (f : C₀(alpha, ℝ)) y := by
  have hpos : Integrable (fun omega : ContinuousPath alpha ↦ (f : C₀(alpha, ℝ)) (omega u))
      (Q y) :=
    Integrable.of_bound
      (StronglyMeasurable.aestronglyMeasurable
        ((f : C₀(alpha, ℝ)).continuous.comp_stronglyMeasurable
          (ContinuousPath.measurable_coordinateProcess (alpha := alpha) u).stronglyMeasurable))
      ‖(f : C₀(alpha, ℝ))‖ (Eventually.of_forall fun omega ↦ norm_c0_apply_le _ _)
  have hcorr : Integrable (fun omega : ContinuousPath alpha ↦
      ∫ s in (0 : ℝ)..u, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
      (Q y) := by
    refine Integrable.of_bound
      ((hFeller.stronglyMeasurable_integral_generator f u).mono
        ((ContinuousPath.canonicalFiltration (alpha := alpha)).le u)).aestronglyMeasurable
      ((u : ℝ) * ‖hFeller.c0Semigroup.generator f‖) (Eventually.of_forall fun omega ↦ ?_)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (u : ℝ)) (C := ‖hFeller.c0Semigroup.generator f‖)
      (f := fun s : ℝ ↦ (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
      (fun s _ ↦ norm_c0_apply_le _ _)
    rwa [sub_zero, abs_of_nonneg u.coe_nonneg, mul_comm] at h
  have hdynkin := integral_eval_sub_eq_integral_integral_generator_realization P hP hFeller Q hfdd f u y
  simp only [IsFellerKernelSemigroup.dynkinProcess_apply]
  rw [integral_sub hpos hcorr]
  linarith only [hdynkin]

/-- The actual continuous-path law solves the generator martingale problem. -/
theorem martingale_dynkinProcess_realization (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (Q : Kernel alpha (ContinuousPath alpha))
    [IsMarkovKernel Q] (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I) (f : hFeller.c0Semigroup.generatorDomain) (x : alpha) :
    Martingale (hFeller.dynkinProcess f)
      (ContinuousPath.canonicalFiltration (alpha := alpha))
      (Q x) := by
  refine ⟨hFeller.adapted_dynkinProcess f, fun s t hst ↦ ?_⟩
  have hdecomp : hFeller.dynkinProcess f t =
      (fun omega : ContinuousPath alpha ↦
          hFeller.dynkinProcess f s omega - (f : C₀(alpha, ℝ)) (omega s)) +
        fun omega : ContinuousPath alpha ↦
          hFeller.dynkinProcess f (t - s) (ContinuousPath.shift s omega) := by
    funext omega
    exact hFeller.dynkinProcess_eq_add_shift f s t hst omega
  have hmeasA : StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) s]
      (fun omega : ContinuousPath alpha ↦
        hFeller.dynkinProcess f s omega - (f : C₀(alpha, ℝ)) (omega s)) :=
    (hFeller.stronglyMeasurable_dynkinProcess_canonicalFiltration f s).sub
      ((f : C₀(alpha, ℝ)).continuous.comp_stronglyMeasurable
        (ContinuousPath.measurable_coordinateProcess_canonicalFiltration
          (alpha := alpha) s).stronglyMeasurable)
  have hintA : Integrable (fun omega : ContinuousPath alpha ↦
      hFeller.dynkinProcess f s omega - (f : C₀(alpha, ℝ)) (omega s))
      (Q x) := by
    refine Integrable.of_bound
      (hmeasA.mono
        ((ContinuousPath.canonicalFiltration (alpha := alpha)).le s)).aestronglyMeasurable
      (‖(f : C₀(alpha, ℝ))‖ + (s : ℝ) * ‖hFeller.c0Semigroup.generator f‖ +
        ‖(f : C₀(alpha, ℝ))‖) (Eventually.of_forall fun omega ↦ ?_)
    exact (norm_sub_le _ _).trans
      (add_le_add (hFeller.norm_dynkinProcess_le f s omega) (norm_c0_apply_le _ _))
  have hmeasF : StronglyMeasurable (hFeller.dynkinProcess f (t - s)) :=
    hFeller.stronglyMeasurable_dynkinProcess f (t - s)
  have hintB : Integrable (fun omega : ContinuousPath alpha ↦
      hFeller.dynkinProcess f (t - s) (ContinuousPath.shift s omega))
      (Q x) :=
    Integrable.of_bound
      (hmeasF.comp_measurable
        (ContinuousPath.measurable_shift_fixed (alpha := alpha) s)).aestronglyMeasurable
      _ (Eventually.of_forall fun omega ↦
        hFeller.norm_dynkinProcess_le f (t - s) (ContinuousPath.shift s omega))
  have hcondA := condExp_of_stronglyMeasurable
    ((ContinuousPath.canonicalFiltration (alpha := alpha)).le s) hmeasA hintA
  have hcondB := condExp_shift_realization P hP hFeller Q hfdd x s
    (hFeller.dynkinProcess f (t - s)) hmeasF
    (‖(f : C₀(alpha, ℝ))‖ + ((t - s : NNReal) : ℝ) * ‖hFeller.c0Semigroup.generator f‖)
    (hFeller.norm_dynkinProcess_le f (t - s))
  have hcondB' : (Q x)[fun omega ↦
      hFeller.dynkinProcess f (t - s) (ContinuousPath.shift s omega)|
        ContinuousPath.canonicalFiltration (alpha := alpha) s] =ᵐ[
      Q x]
      fun omega : ContinuousPath alpha ↦ (f : C₀(alpha, ℝ)) (omega s) := by
    refine hcondB.trans (Eventually.of_forall fun omega ↦ ?_)
    exact integral_dynkinProcess_realization P hP hFeller Q hfdd f (t - s) (omega s)
  rw [hdecomp]
  refine (condExp_add hintA hintB _).trans ?_
  rw [hcondA]
  refine (EventuallyEq.add (EventuallyEq.refl _ _) hcondB').trans
    (Eventually.of_forall fun omega ↦ ?_)
  show hFeller.dynkinProcess f s omega - (f : C₀(alpha, ℝ)) (omega s) +
    (f : C₀(alpha, ℝ)) (omega s) = hFeller.dynkinProcess f s omega
  ring

end SubdiffusiveProcess.Section10
