module

public import SubdiffusiveProcess.Section10.TorsionExitOccupation
public import SubdiffusiveProcess.Section10.TorsionRepresentative
public import MarkovProcess.Feller.FiniteSetCompactTestContinuity
public import MarkovProcess.Parameterized.ContinuousProcessProperties

@[expose] public section

/-! Full support promotes a lower-semicontinuous actual occupation bound.
AE analytic representatives are not silently identified at exceptional starts. -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- A lower-semicontinuous function bounded almost everywhere on an open set
is bounded at every point when the underlying measure has full support. -/
theorem lowerSemicontinuousOn_le_of_ae_restrict {X Y : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [LinearOrder Y] (μ : Measure X) [μ.IsOpenPosMeasure]
    {U : Set X} (hU : IsOpen U) {f : X → Y}
    (hf : LowerSemicontinuousOn f U) {B : Y}
    (hbound : ∀ᵐ x ∂μ.restrict U, f x ≤ B) : ∀ x ∈ U, f x ≤ B := by
  obtain ⟨V, hV, hUV⟩ := lowerSemicontinuousOn_iff_preimage_Ioi.mp hf B
  have hz : μ (U ∩ f ⁻¹' Ioi B) = 0 := by
    have h := ae_iff.mp hbound
    rw [Measure.restrict_apply' hU.measurableSet] at h
    simpa only [not_le, Set.preimage, Set.mem_Ioi, Set.inter_comm] using h
  rw [hUV] at hz
  have hempty := (hU.inter hV).eq_empty_of_measure_zero hz
  intro x hx
  by_contra h
  have hxV : x ∈ U ∩ V := hUV ▸ (show x ∈ U ∩ f ⁻¹' Ioi B from ⟨hx, lt_of_not_ge h⟩)
  simp only [hempty, mem_empty_iff_false] at hxV

/-- The original positive speed density supplies the required full support. -/
theorem discountedUnitOccupation_le_of_ae {d : ℕ}
    (law : Kernel (Vec d) (Path d)) {U : Set (Vec d)} (hU : IsOpen U)
    {b : Vec d → ℝ} (hb : CoefficientOn U b) {s : ℝ}
    (hls : LowerSemicontinuousOn (discountedUnitOccupation law U s) U)
    {B : ℝ≥0∞} (hbound : ∀ᵐ x ∂(weightedMeasure b).restrict U,
      discountedUnitOccupation law U s x ≤ B) :
    ∀ x ∈ U, discountedUnitOccupation law U s x ≤ B := by
  have hfull := volume_restrict_absolutelyContinuous_weightedMeasure_restrict hU.measurableSet hb
  exact lowerSemicontinuousOn_le_of_ae_restrict volume hU hls (hfull.ae_le hbound)

/-- Only countably many positive discounts need starting-point regularity. -/
def UnitDiscountOccupationLSC {d : ℕ} (law : Kernel (Vec d) (Path d))
    (U : Set (Vec d)) : Prop :=
  ∀ n : ℕ, LowerSemicontinuousOn
    (discountedUnitOccupation law U ((n : ℝ) + 1)) U

/-- Precise classical supplier target, with no density, Sobolev or exit estimate.
It is a named proposition and is not asserted to be inhabited here. -/
def FellerUnitCubeDiscountOccupationLSC : Prop :=
  ∀ (d : ℕ) (P : SubMarkovKernelSemigroup (Vec d)), P.IsConservative →
    P.IsFellerKernelSemigroup →
    ∀ K : Kernel (Vec d) (ContinuousPath (Vec d)), IsMarkovKernel K →
      (∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
        SubMarkovKernelSemigroup.finiteSetKernel P I x) →
      UnitDiscountOccupationLSC (K.map LifetimePath.ofContinuousPath)
        (Metric.ball (0 : Vec d) (1 / 2))

end SubdiffusiveProcess.Section10
