module

public import SubdiffusiveProcess.Section10.TorsionExitDynkinMartingale
public import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput
public import SubdiffusiveProcess.Section10.PhysicalAttachmentMeasurableGraph
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationGenerator

@[expose] public section




noncomputable section
open Homogenization MeasureTheory ProbabilityTheory Filter Topology MarkovProcess
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty CompactlySupported BigOperators
namespace SubdiffusiveProcess.Section10

/-- The compact-set derivative certificate implies ordinary `C¹` regularity. -/
theorem contDiff_one_of_locallyC11 {d : ℕ} {a : Vec d → ℝ}
    (ha : SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11 a) : ContDiff ℝ 1 a := by
  obtain ⟨Da, hDa, hLip⟩ := ha
  have hlocal : LocallyLipschitz Da := by
    intro x
    obtain ⟨C, hC⟩ := hLip (Metric.closedBall x 1) (isCompact_closedBall x 1)
    exact ⟨C, Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one,
      hC.mono Metric.ball_subset_closedBall⟩
  exact contDiff_one_iff_hasFDerivAt.mpr ⟨Da, hlocal.continuous, hDa⟩

/-- The exact compact `C₀` generator value, constructed from classical forcing. -/
def compactTestGenerator {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (w : C_c(Vec d, ℝ)) (hw : ContDiff ℝ (⊤ : ℕ∞) (w : Vec d → ℝ)) :
    C₀(Vec d, ℝ) :=
  compactSupportToC0 w - smoothForcingC0 B hc hrho 1 hw w.hasCompactSupport'

/-- No abstract promised generator value is used. -/
theorem compactTestGenerator_apply {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (w : C_c(Vec d, ℝ)) (hw : ContDiff ℝ (⊤ : ℕ∞) (w : Vec d → ℝ)) (x : Vec d) :
    compactTestGenerator B hc hrho w hw x = coeffFluxDiv c w x / rho x := by
  simp [compactTestGenerator, smoothMassiveForcing]

/-- The existing resolvent uniqueness theorem identifies this actual generator. -/
theorem exists_generator_of_compactTest {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hD : IsWeakEllipticResolvent c rho D)
    (w : C_c(Vec d, ℝ)) (hw : ContDiff ℝ (⊤ : ℕ∞) (w : Vec d → ℝ)) :
    let S := (D.isFellerKernelSemigroup_fellerKernelSemigroup hdense).c0Semigroup
    ∃ hm : compactSupportToC0 w ∈ S.generatorDomain,
      S.generator ⟨compactSupportToC0 w, hm⟩ = compactTestGenerator B hc hrho w hw := by
  apply exists_generator_of_smooth_c0 B hc D hdense hD _ _ hw
  exact compactTestGenerator_apply B hc hrho w hw

/-- Product differentiation with the source's energy convention (no factor `1/2`). -/
theorem coeffFluxDiv_div_self_eq {d : ℕ} {a : Vec d → ℝ}
    (hc : ContDiff ℝ 1 a) (hpos : ∀ x, 0 < a x) {w : Vec d → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x : Vec d) :
    coeffFluxDiv a w x / a x = euclideanCoordLaplacian w x +
      ∑ i : Fin d, (euclideanCoordDeriv i a x / a x) * euclideanCoordDeriv i w x := by
  have hterm (i : Fin d) :
      euclideanCoordDeriv i (fun y ↦ a y * euclideanCoordDeriv i w y) x =
        a x * euclideanCoordSecondDeriv i i w x +
          euclideanCoordDeriv i w x * euclideanCoordDeriv i a x := by
    change (fderiv ℝ (a * euclideanCoordDeriv i w) x) (basisVec i) = _
    rw [fderiv_mul (hc.differentiable (by decide) x)
      ((contDiff_euclideanCoordDeriv hw i).differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rfl
  simp only [coeffFluxDiv, hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
    add_div, euclideanCoordLaplacian]
  rw [mul_div_cancel_left₀ _ (hpos x).ne', Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual continuous-path law satisfies the compact-test martingale equation. -/
theorem martingale_compactTest_of_weakResolvent {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hD : IsWeakEllipticResolvent c rho D)
    (hcons : (D.fellerKernelSemigroup hdense).IsConservative)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset NNReal, K.map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel (D.fellerKernelSemigroup hdense) I)
    (w : C_c(Vec d, ℝ)) (hw : ContDiff ℝ (⊤ : ℕ∞) (w : Vec d → ℝ)) (x : Vec d) :
    Martingale (fun t : NNReal ↦ fun path : ContinuousPath (Vec d) ↦
      w (path t) - ∫ s in (0 : ℝ)..t, coeffFluxDiv c w (path (Real.toNNReal s)) /
        rho (path (Real.toNNReal s)))
      (ContinuousPath.canonicalFiltration (alpha := Vec d)) (K x) := by
  let hF := D.isFellerKernelSemigroup_fellerKernelSemigroup hdense
  obtain ⟨hm, hgen⟩ := exists_generator_of_compactTest B hc hrho D hdense hD w hw
  have h := martingale_dynkinProcess_realization (D.fellerKernelSemigroup hdense)
    hcons hF K hfdd ⟨compactSupportToC0 w, hm⟩ x
  change Martingale (fun t : NNReal ↦ fun path : ContinuousPath (Vec d) ↦
    compactSupportToC0 w (path t) - ∫ s in (0 : ℝ)..t,
      (hF.c0Semigroup.generator ⟨compactSupportToC0 w, hm⟩)
        (path (Real.toNNReal s))) _ _ at h
  simpa only [hgen,
    compactTestGenerator_apply, compactSupportToC0_apply] using! h

end SubdiffusiveProcess.Section10
