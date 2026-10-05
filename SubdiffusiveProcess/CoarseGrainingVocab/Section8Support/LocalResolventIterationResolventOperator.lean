module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationKernelIntegral
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSymmetry
@[expose] public section

/-!
# Symmetry and subinvariance of the local resolvent kernel

Weak reciprocity and the exact occupation formula identify the symmetric rectangle
masses. The sub-Markov mass bound then gives subinvariance.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal ProbabilityTheory
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration

/-- On indicator data the raw resolvent is the mass of the resolvent kernel. -/
theorem killedResolvent_indicator_one {d : ℕ}
    (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ) (hs : 0 < s)
    (D : Set (Vec d)) (hD : MeasurableSet D) (x : Vec d) :
    killedResolvent law U s (D.indicator (fun _ => (1:ℝ))) x =
      (resolventKernel law U hU s hs x D).toReal := by
  let := (resolventKernel_subMarkov law U hU s hs).isFiniteKernel
  rw [← resolventKernel_integral_eq_of_integrable law U hU s hs _ x
    ((integrable_const (1:ℝ)).indicator hD)]
  exact kernelIntegral_indicator_one _ D hD x

/-- The scalar pairing of an indicator is a set integral. -/
theorem integral_indicator_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (C : Set α) (hC : MeasurableSet C) (v : α → ℝ) :
    (∫ x, C.indicator (fun _ => (1:ℝ)) x * v x ∂μ) = ∫ x in C, v x ∂μ := by
  have hi : (fun x => C.indicator (fun _ => (1:ℝ)) x * v x) = C.indicator v := by
    funext x
    by_cases hx : x ∈ C <;> simp [hx]
  rw [hi, integral_indicator hC]

/-- Rectangle masses of the local resolvent are symmetric. -/
theorem resolventKernel_rectangle_symmetry {d : ℕ} {c rho : Vec d → ℝ}
    {law : Kernel (Vec d) (Path d)} [IsMarkovKernel law]
    (hD : LocalDiffusion c rho law) {U : Set (Vec d)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    (s : ℝ) (hs : 0 < s) (C D : Set (Vec d))
    (hC : MeasurableSet C) (hDs : MeasurableSet D) :
    (∫⁻ x in C, resolventKernel law U hU s hs x D ∂(weightedMeasure rho).restrict U) =
      ∫⁻ x in D, resolventKernel law U hU s hs x C ∂(weightedMeasure rho).restrict U := by
  let μ := (weightedMeasure rho).restrict U
  let κ := resolventKernel law U hU s hs
  have hκ : IsSubMarkovKernel κ := resolventKernel_subMarkov law U hU s hs
  let := hκ.isFiniteKernel
  have hpair := killedResolvent_pairing_eq hD hU hUb hs
    ((memLp_const (1:ℝ) : MemLp (fun _ : Vec d => (1:ℝ)) 2 μ).indicator hC)
    ((memLp_const (1:ℝ) : MemLp (fun _ : Vec d => (1:ℝ)) 2 μ).indicator hDs)
  rw [integral_indicator_mul _ C hC, integral_indicator_mul _ D hDs] at hpair
  simp only [killedResolvent_indicator_one law U hU s hs D hDs,
    killedResolvent_indicator_one law U hU s hs C hC] at hpair
  have hfinite : ∀ E F : Set (Vec d), (∫⁻ x in E, κ x F ∂μ) ≠ ∞ := by
    intro E F
    apply ne_top_of_le_ne_top (measure_ne_top μ E)
    calc
      (∫⁻ x in E, κ x F ∂μ) ≤ ∫⁻ _x in E, (1:ENNReal) ∂μ :=
        lintegral_mono (fun x => hκ.measure_le_one x F)
      _ = μ E := by simp
  have htoReal : ∀ E F : Set (Vec d), MeasurableSet F →
      (∫ x in E, (κ x F).toReal ∂μ) = (∫⁻ x in E, κ x F ∂μ).toReal := by
    intro E F hF
    exact integral_toReal (κ.measurable_coe hF).aemeasurable
      (Filter.Eventually.of_forall (fun x => measure_lt_top _ _))
  change (∫⁻ x in C, κ x D ∂μ) = ∫⁻ x in D, κ x C ∂μ
  apply (ENNReal.toReal_eq_toReal_iff' (hfinite C D) (hfinite D C)).mp
  change (∫ x in C, (κ x D).toReal ∂μ) = ∫ x in D, (κ x C).toReal ∂μ at hpair
  rwa [htoReal C D hDs, htoReal D C hC] at hpair

/-- The local resolvent preserves the upper measure bound needed for Lp contraction. -/
theorem resolventKernel_subinvariant {d : ℕ} {c rho : Vec d → ℝ}
    {law : Kernel (Vec d) (Path d)} [IsMarkovKernel law]
    (hD : LocalDiffusion c rho law) {U : Set (Vec d)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    (s : ℝ) (hs : 0 < s) :
    resolventKernel law U hU s hs ∘ₘ ((weightedMeasure rho).restrict U) ≤
      (weightedMeasure rho).restrict U :=
  subinvariant_of_rectangle_symmetry _ _ (resolventKernel_subMarkov law U hU s hs)
    (resolventKernel_rectangle_symmetry hD hU hUb s hs)

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
