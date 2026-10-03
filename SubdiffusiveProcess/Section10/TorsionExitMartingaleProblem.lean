module

public import SubdiffusiveProcess.Section10.TorsionExitGenerator
public import SubdiffusiveProcess.Section10.PhysicalAttachmentStrongMarkov

@[expose] public section

/-! The actual same-speed/energy realization solves the classical compact-test
martingale problem. Both the start and the equation hold under its own path
law, for every start. No auxiliary SDE law or density premise is introduced. -/

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

/-- The source generator's literal drift, with diffusion generator `Δ`. -/
def reversibleDrift {d : ℕ} (a : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i ↦ euclideanCoordDeriv i a x / a x

/-- Classical compact-test martingale problem on the supplied continuous paths.
The initial point is part of the assertion; all starts use the same kernel. -/
def IsCompactTestMartingaleProblem {d : ℕ} (b : Vec d → Vec d)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) : Prop :=
  (∀ x, ∀ᵐ path ∂K x, path (0 : NNReal) = x) ∧
  ∀ w : C_c(Vec d, ℝ), ContDiff ℝ (⊤ : ℕ∞) (w : Vec d → ℝ) → ∀ x,
    Martingale (fun t : NNReal ↦ fun path : ContinuousPath (Vec d) ↦
      w (path t) - ∫ s in (0 : ℝ)..t,
        euclideanCoordLaplacian w (path (Real.toNNReal s)) +
          ∑ i : Fin d, b (path (Real.toNNReal s)) i *
            euclideanCoordDeriv i w (path (Real.toNNReal s)))
      (ContinuousPath.canonicalFiltration (alpha := Vec d)) (K x)

/-- An actual conservative same-speed/energy weak resolvent supplies the
compact-test martingale problem, with no probabilistic characterization slot. -/
theorem compactTestMartingaleProblem_of_weakResolvent {d : ℕ} {a : Vec d → ℝ}
    (hapos : ∀ x, 0 < a x) (ha : SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11 a)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hweak : IsWeakEllipticResolvent a a D)
    (hcons : (D.fellerKernelSemigroup hdense).IsConservative)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset NNReal, K.map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel (D.fellerKernelSemigroup hdense) I) :
    IsCompactTestMartingaleProblem (reversibleDrift a) K := by
  have hc : ContDiff ℝ 1 a := contDiff_one_of_locallyC11 ha
  obtain ⟨B⟩ := pa_cube_bounds hc.continuous hapos hc.continuous hapos
  constructor
  · intro x
    let evalZero : ContinuousPath (Vec d) → Vec d := fun path ↦ path 0
    have hEvalZero : Measurable evalZero := ContinuousPath.measurable_coordinateProcess 0
    have hmap : Measure.map evalZero (K x) = Measure.dirac x := by
      have h := congrArg (fun Q : Kernel (Vec d) (Vec d) ↦ Q x)
        (IsConservative.realization_map_eval_zero (D.fellerKernelSemigroup hdense)
          hcons K hfdd)
      change (K.map evalZero) x = Kernel.id x at h
      rw [Kernel.id_apply, Kernel.map_apply K hEvalZero x] at h
      exact h
    apply (mem_ae_iff_prob_eq_one (hEvalZero (MeasurableSet.singleton x))).mpr
    rw [← Measure.map_apply hEvalZero (MeasurableSet.singleton x), hmap]
    simp only [Measure.dirac_apply' x (MeasurableSet.singleton x),
      Set.indicator_of_mem (show x ∈ ({x} : Set (Vec d)) from rfl)]
    rfl
  · intro w hw x
    have h := martingale_compactTest_of_weakResolvent B hc hc.continuous
      D hdense hweak hcons K hfdd w hw x
    simpa only [coeffFluxDiv_div_self_eq hc hapos hw, reversibleDrift] using h

/-- Concrete finite/top physical-family consumer. All analytic and full-FDD
inputs come from the actual attachment, including cutoff zero. -/
theorem exists_physical_compactTestMartingaleProblem {d : ℕ} [NeZero d]
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)] (M : GMCModel d) :
    ∃ X : WithTop ℕ → PhysicalKernel d,
      (∀ L, IsMarkovKernel (X L)) ∧
      ∀ᵐ omega ∂(physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
        IsCompactTestMartingaleProblem (reversibleDrift (coefficientAt M L omega))
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
  apply compactTestMartingaleProblem_of_weakResolvent (coefficientAt_pos M L omega)
    (locallyC11_coefficientAt M L omega) D hdense hweak hcons
  intro I
  ext x A hA
  exact congrArg (fun mu : Measure (I → Vec d) ↦ mu A) (hfdd I x)

end SubdiffusiveProcess.Section10
