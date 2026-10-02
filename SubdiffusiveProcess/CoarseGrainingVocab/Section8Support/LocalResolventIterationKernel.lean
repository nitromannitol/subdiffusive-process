import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossingMarkov
import MarkovProcess.Kernel.Lp
/-!
# Killed transition and resolvent kernels

Restriction to survival followed by the live position map gives the killed kernel.
Its exponential-time mixture is the normalized resolvent occupation kernel.
The positive scale and probability-law hypotheses restrict the constructions to
their source domain.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossing
open scoped ENNReal NNReal ProbabilityTheory
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration

theorem survival_measurable {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) : MeasurableSet {q : ℝ × Path d | ENNReal.ofReal q.1 < LifetimePath.exitTime U q.2} := measurableSet_lt (measurable_fst.ennreal_ofReal)
  (((LifetimePath.isStoppingTime_exitTime U hU).measurable').comp measurable_snd)

theorem joint_position {d : ℕ} : Measurable (fun q : ℝ × Path d => position (Real.toNNReal q.1) q.2) := measurable_position_uncurry.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)

theorem exponential_probability (s : ℝ) (hs : 0 < s) : IsProbabilityMeasure (expMeasure s⁻¹) := by
  exact isProbabilityMeasure_expMeasure (by positivity)

theorem position_of_alive {d : ℕ} (t : NNReal) (w : Path d) (x : Vec d) (h : LifetimePath.coordinate t w = Cemetery.alive x) : position t w = x := by
  unfold position
  rw [h]
  rfl

theorem position_mem_of_lt_exit {d : ℕ} (U : Set (Vec d)) (w : Path d) (t : NNReal) (h : (t : ENNReal) < LifetimePath.exitTime U w) : position t w ∈ U := by
  obtain ⟨z, hz, hcoord⟩ :=
    LifetimePath.exists_coordinate_eq_alive_of_lt_exitTime U w t h
  simp only [position, hcoord]
  exact hz


theorem map_restrict_apply {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] (κ : Kernel α β) (S : Set β) (hS : MeasurableSet S) (g : β → γ) (hg : Measurable g) (a : α) (B : Set γ) (hB : MeasurableSet B) : ((κ.restrict hS).map g) a B = κ a (g ⁻¹' B ∩ S) := by
  rw [Kernel.map_apply' _ hg a hB, Kernel.restrict_apply' _ hS a (hg hB)]


theorem map_restrict_subMarkov {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] (κ : Kernel α β) (hκ : IsSubMarkovKernel κ) (S : Set β) (hS : MeasurableSet S) (g : β → γ) (hg : Measurable g) : IsSubMarkovKernel ((κ.restrict hS).map g) := by
  intro a
  rw [Kernel.map_apply' _ hg a MeasurableSet.univ, Kernel.restrict_apply' _ hS a (hg MeasurableSet.univ)]
  simp only [Set.preimage_univ, Set.univ_inter]
  exact hκ.measure_le_one a S

theorem position_fixed_measurable {d : ℕ} (t : NNReal) : Measurable (position t : Path d → Vec d) := (SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossing.measurable_position_uncurry.comp
    (measurable_const.prodMk measurable_id))

/-- The coordinate kernel restricted to paths which have not yet left the open set. -/
def killedKernel {d : ℕ} (law : Kernel (Vec d) (Path d)) (U : Set (Vec d))
    (hU : IsOpen U) (t : NNReal) : Kernel (Vec d) (Vec d) :=
  (law.restrict (measurableSet_lt (show Measurable (fun _ : Path d => (t : ENNReal)) from measurable_const)
    (LifetimePath.isStoppingTime_exitTime U hU).measurable')).map (position t)

/-- The normalized Laplace occupation kernel at a positive resolvent scale. -/
def resolventKernel {d : ℕ} (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ) (_hs : 0 < s) :
    Kernel (Vec d) (Vec d) :=
  ((Kernel.const (Vec d) (expMeasure s⁻¹) ×ₖ law).restrict
    (survival_measurable U hU)).map (fun q => position (Real.toNNReal q.1) q.2)

theorem killedKernel_subMarkov {d : ℕ} (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law] (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal) : IsSubMarkovKernel (killedKernel law U hU t) := by
  unfold killedKernel
  exact map_restrict_subMarkov law (IsSubMarkovKernel.of_isMarkovKernel law) _ _ _ (position_fixed_measurable t)

theorem resolventKernel_subMarkov {d : ℕ} (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law] (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ) (hs : 0 < s) : IsSubMarkovKernel (resolventKernel law U hU s hs) := by
  letI := exponential_probability s hs
  unfold resolventKernel
  exact map_restrict_subMarkov _ (IsSubMarkovKernel.of_isMarkovKernel _) _ _ _ joint_position

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
