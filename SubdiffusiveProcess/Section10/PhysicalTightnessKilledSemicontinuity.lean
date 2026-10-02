import SubdiffusiveProcess.Section10.PhysicalTightnessPointwise
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerPointwise
import Mathlib.Topology.Semicontinuous

/-! Spatial lower semicontinuity of survival follows from the actual continuous
killed density by Fatou. No continuity of a caller-supplied family is assumed. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

/-- Survival is lower semicontinuous in every interior starting point. -/
theorem lowerSemicontinuousOn_killed_survival {d : ℕ}
    {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusionData c rho law) {U : Set (Vec d)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) {t : ℝ} (ht : 0 < t) :
    LowerSemicontinuousOn
      (fun x => killedKernel law U hU (Real.toNNReal t) x univ) U := by
  obtain ⟨p, hp, hpc⟩ := hD.2 U hU hUb
  rw [← lowerSemicontinuous_restrict_iff]
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro b
  apply isSeqClosed_iff_isClosed.mp
  intro xs x hxs hlim
  have hlimval : Tendsto (fun n => (xs n : Vec d)) atTop (𝓝 (x : Vec d)) :=
    continuous_subtype_val.continuousAt.tendsto.comp hlim
  have hpoint : ∀ᵐ y ∂(weightedMeasure rho).restrict U,
      ENNReal.ofReal (p t x y) =
        liminf (fun n => ENNReal.ofReal (p t (xs n) y)) atTop := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
    have hwithin : Tendsto (fun n => ((t, (xs n : Vec d), y) : ℝ × Vec d × Vec d))
        atTop (𝓝[Ioi 0 ×ˢ U ×ˢ U] (t, (x : Vec d), y)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ⟨ht, (xs n).property, hy⟩⟩
      exact tendsto_const_nhds.prodMk_nhds (hlimval.prodMk_nhds tendsto_const_nhds)
    exact ((ENNReal.continuous_ofReal.tendsto _).comp
      ((hpc (t, (x : Vec d), y) ⟨ht, x.property, hy⟩).tendsto.comp hwithin)).liminf_eq.symm
  have hmass : ∀ y ∈ U, killedKernel law U hU (Real.toNNReal t) y univ =
      ∫⁻ z, ENNReal.ofReal (p t y z) ∂(weightedMeasure rho).restrict U := by
    intro y hy
    rw [killedKernel_eq_withDensity hU hp ht hy, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
  change killedKernel law U hU (Real.toNNReal t) x univ ≤ b
  rw [hmass x x.property]
  calc
    _ = ∫⁻ y, liminf (fun n => ENNReal.ofReal (p t (xs n) y)) atTop
        ∂(weightedMeasure rho).restrict U := lintegral_congr_ae hpoint
    _ ≤ liminf (fun n => ∫⁻ y, ENNReal.ofReal (p t (xs n) y)
        ∂(weightedMeasure rho).restrict U) atTop :=
      lintegral_liminf_le fun n => measurable_density hp ht (xs n)
    _ ≤ b := liminf_le_of_frequently_le' (Eventually.of_forall fun n => by
      rw [← hmass (xs n) (xs n).property]
      exact hxs n).frequently

/-- The exact survival/exit complement identity uses probability of the supplied
lifetime law; it does not assume that its lifetime is infinite. -/
theorem killed_survival_eq_one_sub_exit {d : ℕ}
    (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal) (x : Vec d) :
    killedKernel law U hU t x univ =
      1 - law x {w | LifetimePath.exitTime U w ≤ (t : ENNReal)} := by
  rw [killed_apply law U hU t x univ MeasurableSet.univ]
  have hevent : {w : Path d | position t w ∈ univ ∧ (t : ENNReal) < LifetimePath.exitTime U w} =
      {w : Path d | LifetimePath.exitTime U w ≤ (t : ENNReal)}ᶜ := by ext w; simp
  rw [hevent, measure_compl (measurableSet_le (localTorsion_exitTime_measurable U hU)
    measurable_const) (measure_ne_top _ _)]
  simp

end SubdiffusiveProcess.Section10.PhysicalTightness
