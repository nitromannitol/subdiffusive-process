module

public import SubdiffusiveProcess.Section10.TorsionExitCutoffEarlyExit

@[expose] public section

/-! Actual compact-start early-exit control for all reversible weak-resolvent
realizations. Every cutoff is put in the native generator domain by weak
uniqueness. The original clock is used, including physical cutoff zero/top. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open MarkovProcess.SubMarkovKernelSemigroup
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.Section10.PhysicalAttachment
open scoped ENNReal NNReal ZeroAtInfty CompactlySupported
namespace SubdiffusiveProcess.Section10

/-- Uniform early exit for the ORIGINAL all-start Feller realization, proved
from actual variational weak uniqueness and bounded Dynkin stopping. -/
theorem uniformEarlyExit_of_reversible_weakResolvent {d : ℕ} {a : Vec d → ℝ}
    (hapos : ∀ x, 0 < a x) (ha : SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11 a)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hweak : IsWeakEllipticResolvent a a D)
    (hcons : (D.fellerKernelSemigroup hdense).IsConservative)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) [IsMarkovKernel K]
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      finiteSetKernel (D.fellerKernelSemigroup hdense) I x) :
    UniformEarlyExit K := by
  have hfdd' : ∀ I : Finset NNReal,
      K.map (ContinuousPath.finsetEvaluation I) =
        finiteSetKernel (D.fellerKernelSemigroup hdense) I := by
    intro I
    ext x B hB
    exact congrArg (fun mu : Measure (I → Vec d) => mu B) (hfdd I x)
  have hc : ContDiff ℝ 1 a := contDiff_one_of_locallyC11 ha
  obtain ⟨bounds⟩ := pa_cube_bounds hc.continuous hapos hc.continuous hapos
  have hzero := (compactC2TestMartingaleProblem_of_weakResolvent hapos ha
    D hdense hweak hcons K hfdd').1
  intro U hU S hS hSU eps heps
  obtain ⟨w, hw, hwb, hwOne, hwsupp⟩ := exists_compact_smooth_cutoff hU hS hSU
  have hw2 : ContDiff ℝ 2 (w : Vec d → ℝ) :=
    hw.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨hm, _⟩ := exists_generator_of_compactC2Test bounds hc hc.continuous
    D hdense hweak w hw2
  let hF := D.isFellerKernelSemigroup_fellerKernelSemigroup hdense
  let f : hF.c0Semigroup.generatorDomain := ⟨compactSupportToC0 w, hm⟩
  let G := ‖hF.c0Semigroup.generator f‖
  have hG : 0 ≤ G := norm_nonneg _
  refine ⟨eps / (G + 1), div_pos heps (by linarith), ?_⟩
  intro t ht x hx
  have hb : ∀ y, 0 ≤ (f : C₀(Vec d, ℝ)) y ∧ (f : C₀(Vec d, ℝ)) y ≤ 1 := hwb
  have hfx : (f : C₀(Vec d, ℝ)) x = 1 := hwOne hx
  have hsupp : tsupport (f : Vec d → ℝ) ⊆ U := hwsupp
  have hrate := earlyExit_le_of_generator_cutoff (D.fellerKernelSemigroup hdense)
    hcons hF K hfdd' hzero f hU hb hsupp (hSU hx) hfx t
  refine hrate.trans (ENNReal.ofReal_le_ofReal ?_)
  change (t : ℝ) * G ≤ eps
  have hsmall : (t : ℝ) * (G + 1) < eps :=
    (lt_div_iff₀ (by linarith : 0 < G + 1)).mp ht
  nlinarith [t.coe_nonneg]

/-- Concrete actual finite/top family with uniform early exit, including
cutoff zero. No path-law tightness certificate is supplied by a caller. -/
theorem exists_physical_uniformEarlyExit {d : ℕ} [NeZero d]
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)] (M : GMCModel d) :
    ∃ X : WithTop ℕ → PhysicalKernel d,
      (∀ L, IsMarkovKernel (X L)) ∧
      ∀ᵐ omega ∂(physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
        UniformEarlyExit (physicalSlice (X L) omega) := by
  obtain ⟨X, hX, hactual⟩ := exists_physical_strongMarkov_family M
  refine ⟨X, hX, ?_⟩
  filter_upwards [hactual] with omega homega
  intro L
  obtain ⟨_, D, hdense, hweak, hcons, hfdd⟩ := homega L
  let := hX L
  let : IsMarkovKernel (physicalSlice (X L) omega) := by
    dsimp only [physicalSlice]
    infer_instance
  exact uniformEarlyExit_of_reversible_weakResolvent (coefficientAt_pos M L omega)
    (locallyC11_coefficientAt M L omega) D hdense hweak hcons _ hfdd

end SubdiffusiveProcess.Section10
