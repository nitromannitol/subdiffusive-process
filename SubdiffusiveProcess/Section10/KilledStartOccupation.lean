import SubdiffusiveProcess.Section10.TorsionExitDensity
import SubdiffusiveProcess.Section10.FellerKilledStartContinuity

/-! Continuity of actual killed masses gives lower semicontinuity of the
actual discounted unit occupation. Finiteness recovers ENNReal continuity
from real masses, and Fatou applies in the time variable for every discount.
-/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- Every-start continuity of positive-time killed survival masses implies
lower semicontinuity of actual occupation for any real discount parameter. -/
theorem discountedUnitOccupation_lowerSemicontinuousOn_of_killedStartContinuity
    {d : ℕ} {law : Kernel (Vec d) (Path d)} [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpen U)
    (hcont : ∀ t : ℝ, 0 < t →
      ContinuousOn (fun x => (killedKernel law U hU (Real.toNNReal t) x univ).toReal) U)
    (s : ℝ) :
    LowerSemicontinuousOn (discountedUnitOccupation law U s) U := by
  apply lowerSemicontinuousOn_of_seq_le_liminf
  intro x hx xs hxs hlim
  let F : ℕ → ℝ → ℝ≥0∞ := fun n t => ENNReal.ofReal (Real.exp (-t / s)) *
    law (xs n) {q | ENNReal.ofReal t < LifetimePath.exitTime U q}
  have hF (n : ℕ) : Measurable (F n) :=
    (Real.measurable_exp.comp (measurable_id.neg.div_const s)).ennreal_ofReal.mul
      (measurable_unitSurvival law hU (xs n))
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), liminf (fun n => F n t) atTop := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hwithin : Tendsto xs atTop (𝓝[U] x) :=
        tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hxs⟩
      have hreal := ((hcont t ht x hx).tendsto).comp hwithin
      have heq (z : Vec d) :
          ENNReal.ofReal ((killedKernel law U hU (Real.toNNReal t) z univ).toReal) =
            law z {q | ENNReal.ofReal t < LifetimePath.exitTime U q} := by
        rw [ENNReal.ofReal_toReal
          (ne_top_of_le_ne_top ENNReal.one_ne_top
            ((killedKernel_subMarkov law U hU (Real.toNNReal t)).measure_le_one z univ))]
        exact killedKernel_univ_eq_survival hU t z
      have hsurv : Tendsto
          (fun n => law (xs n) {q | ENNReal.ofReal t < LifetimePath.exitTime U q})
          atTop (𝓝 (law x {q | ENNReal.ofReal t < LifetimePath.exitTime U q})) := by
        simpa only [Function.comp_apply, heq] using ENNReal.tendsto_ofReal hreal
      exact (ENNReal.Tendsto.const_mul hsurv
        (Or.inr (show ENNReal.ofReal (Real.exp (-t / s)) ≠ ∞ from
          ENNReal.ofReal_ne_top))).liminf_eq.ge
    _ ≤ _ := lintegral_liminf_le hF

/-- Killed-start continuity supplies the countable positive-discount
regularity required by the every-start mean-exit upper bound. -/
theorem unitDiscountOccupationLSC_of_killedStartContinuity
    {d : ℕ} {law : Kernel (Vec d) (Path d)} [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpen U)
    (hcont : ∀ t : ℝ, 0 < t →
      ContinuousOn (fun x => (killedKernel law U hU (Real.toNNReal t) x univ).toReal) U) :
    UnitDiscountOccupationLSC law U :=
  fun _ => discountedUnitOccupation_lowerSemicontinuousOn_of_killedStartContinuity hU hcont _

end SubdiffusiveProcess.Section10
