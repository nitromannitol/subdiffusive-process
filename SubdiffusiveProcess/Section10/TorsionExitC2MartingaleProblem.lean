import SubdiffusiveProcess.Section10.TorsionExitC2CompactTest
import SubdiffusiveProcess.Section10.TorsionExitMartingaleProblem

/-! The actual same-speed/energy physical law satisfies the compact `C²`
martingale formulation. This is the finite-differentiability adapter for the
older classical sources, with all starts and finite/top scale cases retained. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory Filter Topology MarkovProcess
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.Section10.PhysicalAttachment
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal CompactlySupported BigOperators
namespace SubdiffusiveProcess.Section10

/-- Classical compact-test martingale problem on the supplied continuous paths.
The initial point is part of the assertion; all starts use the same kernel. -/
def IsCompactC2TestMartingaleProblem {d : ℕ} (b : Vec d → Vec d)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) : Prop :=
  (∀ x, ∀ᵐ path ∂K x, path (0 : NNReal) = x) ∧
  ∀ w : C_c(Vec d, ℝ), ContDiff ℝ 2 (w : Vec d → ℝ) → ∀ x,
    Martingale (fun t : NNReal ↦ fun path : ContinuousPath (Vec d) ↦
      w (path t) - ∫ s in (0 : ℝ)..t,
        euclideanCoordLaplacian w (path (Real.toNNReal s)) +
          ∑ i : Fin d, b (path (Real.toNNReal s)) i *
            euclideanCoordDeriv i w (path (Real.toNNReal s)))
      (ContinuousPath.canonicalFiltration (alpha := Vec d)) (K x)

/-- An actual conservative same-speed/energy weak resolvent supplies the
compact-test martingale problem, with no probabilistic characterization slot. -/
theorem compactC2TestMartingaleProblem_of_weakResolvent {d : ℕ} {a : Vec d → ℝ}
    (hapos : ∀ x, 0 < a x) (ha : SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11 a)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hweak : IsWeakEllipticResolvent a a D)
    (hcons : (D.fellerKernelSemigroup hdense).IsConservative)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset NNReal, K.map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel (D.fellerKernelSemigroup hdense) I) :
    IsCompactC2TestMartingaleProblem (reversibleDrift a) K := by
  have hc : ContDiff ℝ 1 a := contDiff_one_of_locallyC11 ha
  obtain ⟨B⟩ := pa_cube_bounds hc.continuous hapos hc.continuous hapos
  constructor
  · exact (compactTestMartingaleProblem_of_weakResolvent hapos ha
      D hdense hweak hcons K hfdd).1
  · intro w hw x
    have h := martingale_compactC2Test_of_weakResolvent B hc hc.continuous
      D hdense hweak hcons K hfdd w hw x
    simpa only [coeffFluxDiv_div_self_eq_of_two hc hapos hw, reversibleDrift] using h

/-- Concrete finite/top physical-family consumer. All analytic and full-FDD
inputs come from the actual attachment, including cutoff zero. -/
theorem exists_physical_compactC2TestMartingaleProblem {d : ℕ} [NeZero d]
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)] (M : GMCModel d) :
    ∃ X : WithTop ℕ → PhysicalKernel d,
      (∀ L, IsMarkovKernel (X L)) ∧
      ∀ᵐ omega ∂(physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
        IsCompactC2TestMartingaleProblem (reversibleDrift (coefficientAt M L omega))
          (physicalSlice (X L) omega) := by
  obtain ⟨X, hX, hactual⟩ := exists_physical_strongMarkov_family M
  refine ⟨X, hX, ?_⟩
  filter_upwards [hactual] with omega homega
  intro L
  obtain ⟨_, D, hdense, hweak, hcons, hfdd⟩ := homega L
  letI := hX L
  letI : IsMarkovKernel (physicalSlice (X L) omega) := by
    dsimp only [physicalSlice]
    infer_instance
  apply compactC2TestMartingaleProblem_of_weakResolvent (coefficientAt_pos M L omega)
    (locallyC11_coefficientAt M L omega) D hdense hweak hcons
  intro I
  ext x A hA
  exact congrArg (fun mu : Measure (I → Vec d) ↦ mu A) (hfdd I x)

/-- Finite test regularity includes the original smooth-test formulation. -/
theorem IsCompactC2TestMartingaleProblem.toSmooth {d : ℕ} {b : Vec d → Vec d}
    {K : Kernel (Vec d) (ContinuousPath (Vec d))}
    (h : IsCompactC2TestMartingaleProblem b K) : IsCompactTestMartingaleProblem b K := by
  refine ⟨h.1, fun w hw x ↦ h.2 w (hw.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) x⟩

end SubdiffusiveProcess.Section10
