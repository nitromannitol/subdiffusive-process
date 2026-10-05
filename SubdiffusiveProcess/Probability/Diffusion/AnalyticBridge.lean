module

public import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput
public import SubdiffusiveProcess.Assumptions.CoefficientRegularity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossingMarkov
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationLevelEnergy
public import Homogenization.Sobolev.Truncation.WeakGradientLimit
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.VectorFieldAndApex.WeakEquationHelpers

@[expose] public section

/-!
# From primitive killed-generator data to a local diffusion

The stochastic/analytic hypotheses are defined in `AnalyticInput.lean`, whose
imports contain only Mathlib and MarkovProcess. This file constructs the Sobolev
witness by closure of weak derivatives, extends the smooth-test equation to all
`H¹₀` tests, and matches the normalization in the frozen multiscale vocabulary.

Source: the generators at `s.fixed.coefficient` and the
part-form heat kernels at `s.fixed.coefficient`. No realization input is discharged here.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossing
open SubdiffusiveProcess.Assumptions.CoefficientRegularity
open scoped ENNReal NNReal BigOperators Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- Measure-valued restart, including possible explosion, implies GMC's integral identity. -/
theorem strongMarkov_of_restart {law : Kernel (Vec d) (Path d)}
    (h : Input.Restart law) : StrongMarkov law := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro x T hT B hB g hg
  have htime : Measurable (fun w => (T w).toNNReal) := hT.measurable'.ennreal_toNNReal
  have hshift : Measurable (fun w : Path d => LifetimePath.shift (T w).toNNReal w) :=
    measurable_shift_uncurry.comp (htime.prodMk measurable_id)
  have hstate : Measurable (fun w : Path d => position (T w).toNNReal w) :=
    measurable_position_uncurry.comp (htime.prodMk measurable_id)
  have hbind : Measurable (fun w => law (Input.stateAt (T w).toNNReal w)) :=
    law.measurable.comp hstate
  rw [← lintegral_map hg hshift, h.2.2 x T hT B hB,
    Measure.lintegral_bind hbind.aemeasurable hg.aemeasurable]
  rfl

/-- Smooth compact-support approximation constructs an `H¹₀` function; the weak gradient
is proved by `L²` closure and is not an assumption of `BoundaryApproximation`. -/
def Input.BoundaryApproximation.toH10 {U : Set (Vec d)} {u : Vec d → ℝ}
    {Du : Vec d → Vec d} (A : Input.BoundaryApproximation U u Du) (hU : IsOpen U) :
    H10Function U where
  toFun := u
  grad := Du
  memL2 := A.memLp
  gradMemL2 := A.grad_memLp
  hasWeakGradient := by
    let v (n : ℕ) := H10Function.ofContDiff hU (A.smooth n) (A.compactSupport n)
      (A.support_subset n)
    exact HasWeakGradientOn.of_tendsto_eLpNorm_two A.memLp A.grad_memLp
      (fun n => (v n).toH1Function.memL2) (fun n => (v n).toH1Function.gradMemL2)
      (fun n => (v n).toH1Function.hasWeakGradient) A.tendsto_fun A.tendsto_grad
  approx := A.approx
  approx_smooth := A.smooth
  approx_hasCompactSupport := A.compactSupport
  approx_support_subset := A.support_subset
  tendsto_approx := A.tendsto_fun
  tendsto_approx_grad := A.tendsto_grad

/-- The constructed Sobolev function keeps the supplied representative literally. -/
theorem Input.BoundaryApproximation.toH10_toFun {U : Set (Vec d)} {u : Vec d → ℝ}
    {Du : Vec d → Vec d} (A : Input.BoundaryApproximation U u Du) (hU : IsOpen U) :
    (A.toH10 hU).toH1Function.toFun = u := rfl

/-- The constructed Sobolev gradient is the supplied `L²` limit of smooth gradients. -/
theorem Input.BoundaryApproximation.toH10_grad {U : Set (Vec d)} {u : Vec d → ℝ}
    {Du : Vec d → Vec d} (A : Input.BoundaryApproximation U u Du) (hU : IsOpen U) :
    (A.toH10 hU).toH1Function.grad = Du := rfl

/-- Extend the primitive smooth-test generator equation to the exact massive weak equation. -/
theorem isMassiveWeakSolutionOn_of_smooth_tests {U : Set (Vec d)} (hU : IsOpen U)
    {c rho f : Vec d → ℝ} {s : ℝ} (hc : CoefficientOn U c) (hrho : CoefficientOn U rho)
    (hf : MemLp f 2 ((weightedMeasure rho).restrict U)) (u : H10Function U)
    (htest : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      (∫ x in U, vecDot (c x • u.toH1Function.grad x) (euclideanGradient ψ x)) =
        ∫ x in U, (rho x * (s⁻¹ * (f x - u.toH1Function.toFun x))) * ψ x) :
    IsMassiveWeakSolutionOn c rho s⁻¹ U u.toH1Function (fun x => s⁻¹ * f x) := by
  obtain ⟨hcmeas, clo, chi, hclo, hcb⟩ := hc
  obtain ⟨hrmeas, rlo, rhi, hrlo, hrb⟩ := hrho
  have hcabs : ∀ᵐ x ∂volume.restrict U, |c x| ≤ chi :=
    hcb.mono fun _ hx => (abs_of_nonneg (hclo.le.trans hx.1)).symm ▸ hx.2
  have hrabs : ∀ᵐ x ∂volume.restrict U, |rho x| ≤ rhi :=
    hrb.mono fun _ hx => (abs_of_nonneg (hrlo.le.trans hx.1)).symm ▸ hx.2
  have hfvol : MemLp f 2 (volume.restrict U) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration.memLp_volume_restrict_of_weighted
      hU.measurableSet ⟨hrmeas, rlo, rhi, hrlo, hrb⟩ hf
  have hG : MemVectorL2 U (fun x => c x • u.toH1Function.grad x) :=
    MemLp.of_eval fun i =>
      memL2On_mul_of_bounded hcmeas hcabs (u.toH1Function.gradMemL2 i)
  have hF : MemScalarL2 U (fun x => rho x * (s⁻¹ * (f x - u.toH1Function.toFun x))) :=
    memL2On_mul_of_bounded hrmeas hrabs ((hfvol.sub u.toH1Function.memL2).const_mul s⁻¹)
  have hweak := h10WeakEquationOn_of_contDiff_tests hU hG hF htest
  intro φ
  have huf := integrableOn_mass_term hrmeas hrabs u.toH1Function.memL2 φ.toH1Function.memL2
  have hff := integrableOn_mass_term hrmeas hrabs hfvol φ.toH1Function.memL2
  have hsplit :
      (∫ x in U, (rho x * (s⁻¹ * (f x - u.toH1Function.toFun x))) * φ.toH1Function.toFun x) =
        s⁻¹ * (∫ x in U, rho x * f x * φ.toH1Function.toFun x) -
          s⁻¹ * (∫ x in U, rho x * u.toH1Function.toFun x * φ.toH1Function.toFun x) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub
      (hff.const_mul s⁻¹) (huf.const_mul s⁻¹)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  have hrhs :
      (∫ x in U, rho x * (s⁻¹ * f x) * φ.toH1Function.toFun x) =
        s⁻¹ * (∫ x in U, rho x * f x * φ.toH1Function.toFun x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [hweak φ, hsplit, hrhs]
  ring

/-- The primitive killed-generator input supplies the complete resolvent clause. -/
theorem killedResolvent_clause_of_killedGenerator {c rho : Vec d → ℝ}
    {law : Kernel (Vec d) (Path d)} (hgen : Input.KilledGenerator c rho law)
    {U : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hc : CoefficientOn U c) (hrho : CoefficientOn U rho)
    {s : ℝ} (hs : 0 < s) {f : Vec d → ℝ}
    (hf : MemLp f 2 ((weightedMeasure rho).restrict U)) :
    ∃ u : H10Function U,
      (u.toH1Function.toFun =ᵐ[(weightedMeasure rho).restrict U] killedResolvent law U s f) ∧
      IsMassiveWeakSolutionOn c rho s⁻¹ U u.toH1Function (fun x => s⁻¹ * f x) := by
  obtain ⟨u, Du, ⟨A⟩, heq, htest⟩ := hgen U hU hUb s hs f hf
  refine ⟨A.toH10 hU, heq, isMassiveWeakSolutionOn_of_smooth_tests hU hc hrho hf _ ?_⟩
  intro ψ hψ hcompact hsupp
  exact htest ψ hψ hcompact hsupp

/-- Assemble a local diffusion from the explicit killed-generator and density inputs.
The coefficient bounds on compact sets are proved from positivity and continuity. -/
theorem localDiffusionData_of_killedGenerator {c rho : Vec d → ℝ}
    {law : Kernel (Vec d) (Path d)} (hsm : StrongMarkov law)
    (hc : Continuous c) (hcpos : ∀ x, 0 < c x)
    (hrho : Continuous rho) (hrhopos : ∀ x, 0 < rho x)
    (hgen : Input.KilledGenerator c rho law) (hdens : Input.ContinuousKilledDensities rho law) :
    LocalDiffusionData c rho law := by
  refine ⟨⟨hsm, ?_, ?_⟩, ?_⟩
  · intro K hK
    exact ⟨coefficientOn_of_continuous_pos hc hcpos hK.isBounded,
      coefficientOn_of_continuous_pos hrho hrhopos hK.isBounded⟩
  · intro U hU hUb s hs f hf
    exact killedResolvent_clause_of_killedGenerator hgen hU hUb
      (coefficientOn_of_continuous_pos hc hcpos hUb)
      (coefficientOn_of_continuous_pos hrho hrhopos hUb) hs hf
  · intro U hU hUb
    obtain ⟨p, hmeas, hpos, hmass, hcont⟩ := hdens U hU hUb
    exact ⟨p, ⟨hmeas, hpos, hmass⟩, hcont⟩

/-- Local `C¹ˑ¹` regularity implies ordinary continuity. -/
theorem continuous_of_locallyC11 {a : Vec d → ℝ} (ha : Input.LocallyC11 a) : Continuous a := by
  obtain ⟨Da, hDa, _⟩ := ha
  exact continuous_iff_continuousAt.mpr fun x => (hDa x).continuousAt

/-- The honest smooth-coefficient existence reduction. The missing input is a theorem over
Mathlib/MarkovProcess objects, with neither `LocalDiffusion` nor a GMC Sobolev carrier. -/
theorem exists_localDiffusionData_of_smoothRealization (hrealize : Input.SmoothRealization d)
    (a : Vec d → ℝ) (hapos : ∀ x, 0 < a x) (ha : Input.LocallyC11 a)
    (rho : Vec d → ℝ) (hrho : rho = a ∨ rho = fun _ => 1) :
    ∃ law : Kernel (Vec d) (Path d), LocalDiffusionData a rho law := by
  obtain ⟨law, hrestart, hgen, hdens⟩ := hrealize a hapos ha rho hrho
  have hac := continuous_of_locallyC11 ha
  have hrhoc : Continuous rho := hrho.elim (fun h => h ▸ hac) (fun h => h ▸ continuous_const)
  have hrhopos : ∀ x, 0 < rho x := hrho.elim (fun h => h ▸ hapos)
    (fun h => h ▸ fun _ => one_pos)
  exact ⟨law, localDiffusionData_of_killedGenerator (strongMarkov_of_restart hrestart)
    hac hapos hrhoc hrhopos hgen hdens⟩

end SubdiffusiveProcess.Probability.Diffusion
