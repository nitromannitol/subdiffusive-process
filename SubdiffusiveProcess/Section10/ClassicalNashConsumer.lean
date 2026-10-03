module

public import SubdiffusiveProcess.Section10.ClassicalNashApplication

@[expose] public section

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDatumFields
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
open MarkovProcess.Semigroup
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Concrete conditional consumption of the proposed classical Nash leaf.
`hNash` is intentionally explicit: this theorem proves no classical leaf or source root. -/
theorem killed_ultracontractive_consumer
    {d : ℕ} {U : Set (Vec d)} {c rho : Vec d → ℝ} {lam Lam : ℝ}
    {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    (hEll : IsEllipticFieldOn lam Lam U (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField c))
    (Cd K : ℝ) (hK : 0 < K)
    (hsob : ∀ u : H10Function U,
      eLpNorm u.toH1Function.toFun
        (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1)))
        ((weightedMeasure rho).restrict U) ^ (2 : ℕ) ≤
          ENNReal.ofReal K *
            (∫⁻ x in U, ENNReal.ofReal
              (c x * vecDot (u.grad x) (u.grad x))))
    (hNash : ∀ (P : SubMarkovKernelSemigroup (Vec d))
        (S : StronglyContinuousContractionSemigroup
          (Lp ℝ 2 ((weightedMeasure rho).restrict U))),
        P.IsSubInvariant ((weightedMeasure rho).restrict U) →
        (∀ (t : ℝ≥0) (f g : Lp ℝ 2 ((weightedMeasure rho).restrict U)),
          ⟪S t f, g⟫ = ⟪f, S t g⟫) →
        (∀ (t : ℝ≥0) (f : Lp ℝ 2 ((weightedMeasure rho).restrict U)),
          ((S t f : Lp ℝ 2 ((weightedMeasure rho).restrict U)) : Vec d → ℝ)
            =ᵐ[(weightedMeasure rho).restrict U] kernelIntegral (P t) f) →
        ∀ K : ℝ, 0 < K →
        (∀ f : S.generatorDomain,
          eLpNorm ((f : Lp ℝ 2 ((weightedMeasure rho).restrict U)) : Vec d → ℝ)
            (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1)))
            ((weightedMeasure rho).restrict U) ^ (2 : ℕ) ≤
              ENNReal.ofReal K * ENNReal.ofReal (-⟪S.generator f, (f : Lp ℝ 2 ((weightedMeasure rho).restrict U))⟫)) →
        ∀ t : ℝ≥0, 0 < t → ∀ f : Vec d → ℝ,
          Integrable f ((weightedMeasure rho).restrict U) →
          eLpNorm (kernelIntegral (P t) f) ∞ ((weightedMeasure rho).restrict U) ≤
            ENNReal.ofReal Cd * (ENNReal.ofReal K / (t : ℝ≥0∞)) ^ d *
              eLpNorm f 1 ((weightedMeasure rho).restrict U))
    (t : ℝ≥0) (ht : 0 < t) (f : Vec d → ℝ)
    (hf : Integrable f ((weightedMeasure rho).restrict U)) :
    eLpNorm (kernelIntegral (killedFamily law U hU t) f) ∞
        ((weightedMeasure rho).restrict U) ≤
      ENNReal.ofReal Cd * (ENNReal.ofReal K / (t : ℝ≥0∞)) ^ d *
        eLpNorm f 1 ((weightedMeasure rho).restrict U) := by
  have hc : CoefficientOn U c :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration.coefficientOn_mono
      subset_closure (hD.2.1 (closure U) hUb.isCompact_closure).1
  have hs : ∀ u : H10Function U,
      eLpNorm u.toH1Function.toFun
        (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) - 1)))
        ((weightedMeasure rho).restrict U) ^ (2 : ℕ) ≤
          ENNReal.ofReal K * ENNReal.ofReal (energy c U u.toH1Function) := by
    intro u
    rw [ofReal_energy_eq_lintegral hc]
    exact hsob u
  exact hNash (killedSMKS law hD.1 U hU) (killedSCCS hD hD.1 hU hUb)
    (isSubInvariant_killedSMKS hD hD.1 hU hUb)
    (fun t => isSymmetricOp_killedLp (hD := hD) (hSM := hD.1) (hU := hU) (hUb := hUb) t)
    (fun t f => killedLp_coeFn (hD := hD) (hSM := hD.1) (hU := hU) (hUb := hUb) t f)
    K hK (killed_generator_sobolev_of_h10 hD hU hUb hEll _ K hs) t ht f hf

end SubdiffusiveProcess.Section10
