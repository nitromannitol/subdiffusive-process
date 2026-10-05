module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationKernel
@[expose] public section

/-!
# Joint measurability and exponential mixtures of killed kernels
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal ProbabilityTheory
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration

theorem resolventKernel_apply_mixture {d : ℕ} (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law] (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ) (hs : 0 < s) (x : Vec d) (B : Set (Vec d)) (hB : MeasurableSet B) : resolventKernel law U hU s hs x B = ∫⁻ t : ℝ, killedKernel law U hU (Real.toNNReal t) x B ∂expMeasure s⁻¹ := by
  let := exponential_probability s hs
  unfold resolventKernel
  rw [map_restrict_apply _ _ _ _ joint_position _ _ hB,
      Kernel.prod_apply,
      Kernel.const_apply,
      Measure.prod_apply ((joint_position hB).inter (survival_measurable U hU))]
  refine lintegral_congr fun t => ?_
  unfold killedKernel
  rw [map_restrict_apply _ _ _ _ (position_fixed_measurable _) _ _ hB]
  rfl

theorem killedKernel_joint_measurable {d : ℕ} (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) (B : Set (Vec d)) (hB : MeasurableSet B) :
    Measurable (fun q : NNReal × Vec d => killedKernel law U hU q.1 q.2 B) := by
  let E : Set ((NNReal × Vec d) × Path d) :=
    {p | position p.1.1 p.2 ∈ B ∧ (p.1.1 : ENNReal) < LifetimePath.exitTime U p.2}
  have hpos : Measurable (fun p : (NNReal × Vec d) × Path d => position p.1.1 p.2) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossing.measurable_position_uncurry.comp
      (measurable_fst.fst.prodMk measurable_snd)
  have hE : MeasurableSet E := (hpos hB).inter
    (measurableSet_lt measurable_fst.fst.coe_nnreal_ennreal
      ((LifetimePath.isStoppingTime_exitTime U hU).measurable'.comp measurable_snd))
  have hind : Measurable (E.indicator (fun _ => (1 : ENNReal))) :=
    measurable_const.indicator hE
  let κ : Kernel (NNReal × Vec d) (Path d) := law.comap Prod.snd measurable_snd
  have hf := hind.lintegral_kernel_prod_right' (κ := κ)
  have heq : (fun q : NNReal × Vec d => ∫⁻ w,
      E.indicator (fun _ => (1 : ENNReal)) (q,w) ∂κ q) =
      (fun q : NNReal × Vec d => killedKernel law U hU q.1 q.2 B) := by
    funext q
    rw [show κ q = law q.2 from rfl]
    calc
      (∫⁻ w, E.indicator (fun _ => (1 : ENNReal)) (q,w) ∂law q.2) =
          law q.2 ((Prod.mk q) ⁻¹' E) := by
        change (∫⁻ w, (((Prod.mk q) ⁻¹' E).indicator (fun _ => (1:ENNReal))) w ∂law q.2) = _
        rw [lintegral_indicator (measurable_prodMk_left hE)]
        simp
      _ = killedKernel law U hU q.1 q.2 B := by
        unfold killedKernel
        rw [map_restrict_apply _ _ _ _ (position_fixed_measurable q.1) _ _ hB]
        rfl
  exact heq ▸ hf

/-- The killed transition kernels with time included in their source parameter. -/
def killedJointKernel {d : ℕ} (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) : Kernel (NNReal × Vec d) (Vec d) where
  toFun q := killedKernel law U hU q.1 q.2
  measurable' := Measure.measurable_of_measurable_coe _ (killedKernel_joint_measurable law U hU)

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
