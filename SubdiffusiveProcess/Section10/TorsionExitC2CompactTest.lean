module

public import SubdiffusiveProcess.Section10.TorsionExitC2Generator

@[expose] public section

/-! Native compact `C²` tests for the actual continuous-path realization.
This interface matches the finite differentiability of older martingale-problem
formulations and preserves the literal diffusion generator `Δ`. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory Filter Topology MarkovProcess
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty CompactlySupported BigOperators
namespace SubdiffusiveProcess.Section10

/-- The continuous compactly supported classical generator for a `C²` test. -/
def compactC2TestGenerator {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (w : C_c(Vec d, ℝ)) (hw : ContDiff ℝ 2 (w : Vec d → ℝ)) :
    C₀(Vec d, ℝ) :=
  compactSupportToC0 {
    toFun := fun x ↦ coeffFluxDiv c w x / rho x
    continuous_toFun :=
      (continuous_finset_sum _ fun i _ ↦
        continuous_coeffFluxComponentDeriv_of_two hc hw i).div hrho
          (fun x ↦ (B.weight_pos x).ne')
    hasCompactSupport' := HasCompactSupport.intro w.hasCompactSupport' fun x hx ↦ by
      rw [coeffFluxDiv_eq_zero_of_notMem (c := c) (w := (w : Vec d → ℝ)) hx, zero_div] }

@[simp]
theorem compactC2TestGenerator_apply {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (w : C_c(Vec d, ℝ)) (hw : ContDiff ℝ 2 (w : Vec d → ℝ)) (x : Vec d) :
    compactC2TestGenerator B hc hrho w hw x = coeffFluxDiv c w x / rho x := rfl

/-- Native resolvent uniqueness identifies the actual generator on `C²` tests. -/
theorem exists_generator_of_compactC2Test {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hD : IsWeakEllipticResolvent c rho D)
    (w : C_c(Vec d, ℝ)) (hw : ContDiff ℝ 2 (w : Vec d → ℝ)) :
    let S := (D.isFellerKernelSemigroup_fellerKernelSemigroup hdense).c0Semigroup
    ∃ hm : compactSupportToC0 w ∈ S.generatorDomain,
      S.generator ⟨compactSupportToC0 w, hm⟩ = compactC2TestGenerator B hc hrho w hw := by
  apply exists_generator_of_c2_c0 B hc D hdense hD _ _ hw
  exact compactC2TestGenerator_apply B hc hrho w hw

/-- Product differentiation with the source's energy convention (no factor `1/2`). -/
theorem coeffFluxDiv_div_self_eq_of_two {d : ℕ} {a : Vec d → ℝ}
    (hc : ContDiff ℝ 1 a) (hpos : ∀ x, 0 < a x) {w : Vec d → ℝ}
    (hw : ContDiff ℝ 2 w) (x : Vec d) :
    coeffFluxDiv a w x / a x = euclideanCoordLaplacian w x +
      ∑ i : Fin d, (euclideanCoordDeriv i a x / a x) * euclideanCoordDeriv i w x := by
  have hterm (i : Fin d) :
      euclideanCoordDeriv i (fun y ↦ a y * euclideanCoordDeriv i w y) x =
        a x * euclideanCoordSecondDeriv i i w x +
          euclideanCoordDeriv i w x * euclideanCoordDeriv i a x := by
    change (fderiv ℝ (a * euclideanCoordDeriv i w) x) (basisVec i) = _
    rw [fderiv_mul (hc.differentiable (by decide) x)
      ((contDiff_one_euclideanCoordDeriv_of_two hw i).differentiable (by decide) x)]
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
theorem martingale_compactC2Test_of_weakResolvent {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hD : IsWeakEllipticResolvent c rho D)
    (hcons : (D.fellerKernelSemigroup hdense).IsConservative)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset NNReal, K.map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel (D.fellerKernelSemigroup hdense) I)
    (w : C_c(Vec d, ℝ)) (hw : ContDiff ℝ 2 (w : Vec d → ℝ)) (x : Vec d) :
    Martingale (fun t : NNReal ↦ fun path : ContinuousPath (Vec d) ↦
      w (path t) - ∫ s in (0 : ℝ)..t, coeffFluxDiv c w (path (Real.toNNReal s)) /
        rho (path (Real.toNNReal s)))
      (ContinuousPath.canonicalFiltration (alpha := Vec d)) (K x) := by
  let hF := D.isFellerKernelSemigroup_fellerKernelSemigroup hdense
  obtain ⟨hm, hgen⟩ := exists_generator_of_compactC2Test B hc hrho D hdense hD w hw
  have h := martingale_dynkinProcess_realization (D.fellerKernelSemigroup hdense)
    hcons hF K hfdd ⟨compactSupportToC0 w, hm⟩ x
  change Martingale (fun t : NNReal ↦ fun path : ContinuousPath (Vec d) ↦
    compactSupportToC0 w (path t) - ∫ s in (0 : ℝ)..t,
      (hF.c0Semigroup.generator ⟨compactSupportToC0 w, hm⟩)
        (path (Real.toNNReal s))) _ _ at h
  simpa only [hgen,
    compactC2TestGenerator_apply, compactSupportToC0_apply] using h

end SubdiffusiveProcess.Section10
