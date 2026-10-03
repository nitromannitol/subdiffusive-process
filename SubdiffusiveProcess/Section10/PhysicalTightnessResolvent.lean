module

public import SubdiffusiveProcess.Section10.PhysicalTightnessPointwise
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledStrongContinuity

@[expose] public section

/-! The variational-to-probability passage for lifetime paths. The exponential
mixture calculation is factored from the proved `tight_fast_exit` application;
the pointwise density argument removes its former conservative/Feller attachment.
No semigroup attachment or caller law equality is required. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledStrongContinuity
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

theorem exit_probability_le_resolvent_defect {d : ℕ}
    (law : Kernel (Homogenization.Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Homogenization.Vec d)) (hU : IsOpen U) (t : ℝ) (ht : 0 < t)
    (eta : Homogenization.Vec d → ℝ) (heta : Measurable eta)
    (heta0 : ∀ x, 0 ≤ eta x) (heta1 : ∀ x, eta x ≤ 1)
    (x : Homogenization.Vec d) :
    law x {w | LifetimePath.exitTime U w ≤ ENNReal.ofReal t} ≤
      ENNReal.ofReal (4 * (1 - killedResolvent law U t eta x)) := by
  letI := exponential_probability t ht
  let P : Measure (ℝ × Path d) := (expMeasure t⁻¹).prod (law x)
  let S : Set (ℝ × Path d) := {q | ENNReal.ofReal q.1 < LifetimePath.exitTime U q.2}
  let E : Set (Path d) := {w | LifetimePath.exitTime U w ≤ ENNReal.ofReal t}
  let R := resolventKernel law U hU t ht
  letI : IsSubMarkovKernel R := resolventKernel_subMarkov law U hU t ht
  letI : IsFiniteKernel R := (resolventKernel_subMarkov law U hU t ht).isFiniteKernel
  have hS : MeasurableSet S := survival_measurable U hU
  have hRmass : R x Set.univ = P S := by
    dsimp only [R, resolventKernel]
    rw [Kernel.map_apply' _ joint_position x MeasurableSet.univ,
      Set.preimage_univ, Kernel.restrict_apply' _ _ x MeasurableSet.univ,
      Set.univ_inter, Kernel.prod_apply, Kernel.const_apply]
  have hetaInt : Integrable eta (R x) :=
    Integrable.of_bound heta.aestronglyMeasurable 1
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (heta0 z)]
        exact heta1 z)
  have hres : killedResolvent law U t eta x ≤ (P S).toReal := by
    rw [← resolventKernel_integral_eq_of_integrable law U hU t ht eta x hetaInt]
    change (∫ z, eta z ∂(R x)) ≤ _
    calc
      (∫ z, eta z ∂(R x)) ≤ ∫ _z, (1 : ℝ) ∂(R x) :=
        integral_mono hetaInt (integrable_const 1) heta1
      _ = (R x Set.univ).toReal := by
        simp only [integral_const, smul_eq_mul, mul_one, measureReal_def]
      _ = (P S).toReal := congrArg ENNReal.toReal hRmass
  have hsub : Set.Ioi t ×ˢ E ⊆ Sᶜ := by
    rintro ⟨v, w⟩ ⟨hv, hw⟩
    exact not_lt_of_ge (hw.trans (ENNReal.ofReal_le_ofReal hv.le))
  have hmono : (1 / 4 : ℝ) * (law x E).toReal ≤ (P Sᶜ).toReal := by
    calc
      (1 / 4 : ℝ) * (law x E).toReal ≤
          ((expMeasure t⁻¹) (Set.Ioi t)).toReal * (law x E).toReal :=
        mul_le_mul_of_nonneg_right (expMeasure_Ioi_toReal_ge ht) ENNReal.toReal_nonneg
      _ = (P (Set.Ioi t ×ˢ E)).toReal := by
        rw [show P (Set.Ioi t ×ˢ E) =
          (expMeasure t⁻¹) (Set.Ioi t) * law x E from Measure.prod_prod _ _,
          ENNReal.toReal_mul]
      _ ≤ (P Sᶜ).toReal := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hsum : (P S).toReal + (P Sᶜ).toReal = 1 := by
    exact probReal_add_probReal_compl hS
  have hbound : (law x E).toReal ≤ 4 * (1 - killedResolvent law U t eta x) := by
    linarith only [hmono, hres, hsum]
  rw [← ENNReal.ofReal_toReal (measure_ne_top (law x) E)]
  exact ENNReal.ofReal_le_ofReal hbound

/-- An a.e. variational/Moser resolvent-defect bound implies an early-exit bound
at every start in the open interior set, without first assuming conservativity. -/
theorem exit_probability_le_of_resolvent_defect_ae {d : ℕ}
    {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusionData c rho law) {U W : Set (Vec d)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hW : IsOpen W) (hWU : W ⊆ U) (t : ℝ) (ht : 0 < t)
    (eta : Vec d → ℝ) (heta : Measurable eta)
    (heta0 : ∀ x, 0 ≤ eta x) (heta1 : ∀ x, eta x ≤ 1)
    (b : ℝ) (hb : 0 ≤ b)
    (hres : ∀ᵐ x ∂(weightedMeasure rho).restrict U, x ∈ W →
      1 - killedResolvent law U t eta x ≤ b) :
    ∀ x ∈ W, law x {w | LifetimePath.exitTime U w ≤ ENNReal.ofReal t} ≤
      ENNReal.ofReal (4 * b) := by
  haveI : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD.1
  have hae : ∀ᵐ x ∂(weightedMeasure rho).restrict U, x ∈ W →
      law x {w | LifetimePath.exitTime U w ≤ ENNReal.ofReal t} ≤
        ENNReal.ofReal (4 * b) := by
    filter_upwards [hres] with x hx
    intro hxW
    exact (exit_probability_le_resolvent_defect law U hU t ht eta heta heta0 heta1 x).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hx hxW) (by norm_num)))
  exact exit_probability_le_of_ae hD hU hUb hW hWU (Real.toNNReal t) (4 * b)
    (mul_nonneg (by norm_num) hb) hae

end SubdiffusiveProcess.Section10.PhysicalTightness
