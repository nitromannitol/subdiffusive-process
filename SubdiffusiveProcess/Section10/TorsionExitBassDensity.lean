module

public import SubdiffusiveProcess.Section10.TorsionExitBassInterfaces
public import SubdiffusiveProcess.Section10.TorsionExitDensityPhysical
public import SubdiffusiveProcess.Section10.PhysicalAttachmentKilled

@[expose] public section

/-! Actual native killed heat-kernel assembly by the existing weighted RRK
construction. Every-start continuity is explicitly consumed, never inferred
from a.e. FOT association. No Friedman or new classical leaf is imported. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledResolventLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularityKilled
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderRegularity
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- Native RRK supplies the actual jointly continuous killed density once
smoothing and original-law starting-point continuity have both been proved. -/
theorem hasContinuousKilledDensityOn_of_smoothing_and_start_continuity
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) {a : Vec d → ℝ}
    {law : Kernel (Vec d) (Path d)} [IsMarkovKernel law]
    (hD : LocalDiffusion a a law) {U : Set (Vec d)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (ha : ContinuousOn a U)
    [IsFiniteMeasure ((weightedMeasure a).restrict U)]
    (N : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hsup : ∀ f : Lp ℝ 2 ((weightedMeasure a).restrict U),
      ∀ᵐ x ∂((weightedMeasure a).restrict U),
        |(((killedResolventLp hD hU hUb 1 (by norm_num)) ^ N) f) x| ≤ C * ‖f‖)
    (hcont : ∀ t : ℝ, 0 < t → ∀ B : Set (Vec d), MeasurableSet B →
      ContinuousOn (fun x => (killedKernel law U hU (Real.toNNReal t) x B).toReal) U) :
    HasContinuousKilledDensityOn a law U := by
  obtain ⟨D, hsemigroup, _, _⟩ :=
    exists_resolventRegularityDatum_of_continuousOn_of_ae_sup_bound
      hD hU hUb (by norm_num : (0 : ℝ) < 1) hd ha N hC hsup
  let H : KilledHeatKernelDatum a law U hU := {
    toDatum := D
    semigroup_eq_killed := by
      intro t ht f hf
      rw [hsemigroup]
      have h1 := killedLp_coeFn (hD := hD) (hSM := hD.1) (hU := hU) (hUb := hUb)
        (Real.toNNReal t) (hf.toLp f)
      have h2 := kernelIntegral_congr_ae
        (isSubInvariant_killedSMKS hD hD.1 hU hUb (Real.toNNReal t))
        (hf.coeFn_toLp)
      have htime : Real.toNNReal t ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr ht)
      simpa only [killedSMKS_apply, killedFamily_of_ne law U hU htime,
        kernelIntegral] using! h1.trans h2
    continuousOn_killedKernel := hcont }
  exact H.hasContinuousKilledDensityOn

/-- The actual source resolvent/FDD data supplies LocalDiffusion from the
already registered FOT part-process input, with its original a,a weighting. -/
theorem localDiffusion_of_reversible_weakResolvent
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess) {d : ℕ} {a : Vec d → ℝ}
    (hapos : ∀ x, 0 < a x) (ha : SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11 a)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hweak : IsWeakEllipticResolvent a a D)
    (hcons : (D.fellerKernelSemigroup hdense).IsConservative)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) [IsMarkovKernel K]
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x) :
    LocalDiffusion a a (K.map LifetimePath.ofContinuousPath) := by
  obtain ⟨hrestart, hgen⟩ := SubdiffusiveProcess.E7.e7_of_leaves
    SubdiffusiveProcess.Section10.PhysicalAttachment.fellerRestart hFOT d a a hapos hapos ha ha
    (D.fellerKernelSemigroup hdense) hcons D hdense hweak
    (D.solution_eq_laplace hdense) K inferInstance hfdd
  have hc := (contDiff_one_of_locallyC11 ha).continuous
  refine ⟨SubdiffusiveProcess.Probability.Diffusion.strongMarkov_of_restart hrestart, ?_, ?_⟩
  · intro S hS
    have hs := SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos
      hc hapos hS.isBounded
    exact ⟨hs, hs⟩
  · intro U hU hUb s hs f hf
    have hb := SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos
      hc hapos hUb
    exact SubdiffusiveProcess.Probability.Diffusion.killedResolvent_clause_of_killedGenerator hgen hU hUb
      hb hb hs hf

end SubdiffusiveProcess.Section10
