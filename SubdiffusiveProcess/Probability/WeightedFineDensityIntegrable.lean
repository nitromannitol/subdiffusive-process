import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Probability.InfraredWholePrefixIndependence
import SubdiffusiveProcess.Probability.InfraredCharacterizationCompactExponentialMoment
import SubdiffusiveProcess.Main.FineDensity
import SubdiffusiveProcess.Probability.FineDensityMartingale
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sets.Compacts

open Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

theorem weightedFineDensity_integrable
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ)
    (x : SpatialCoordinates d)
    (hH : InfraredCharacterization M H) :
    Integrable (fun omega : BilateralField d =>
      Real.exp (H omega x) * fineDensity M N omega x)
      (chaosSampleLaw M).toMeasure := by
  classical
  let φ : C(SpatialCoordinates d, ℝ) → ℝ := fun f => Real.exp (f x)
  let ψ : ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) → ℝ :=
    fun y => Real.exp (∑ j : Fin (N + 1), (y j) x -
      (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  have hφmeas : Measurable φ :=
    (Real.continuous_exp.comp (continuous_eval_const x)).measurable
  have hψmeas : Measurable ψ := by
    apply Measurable.exp
    apply Measurable.sub
    · exact Finset.measurable_fun_sum _ (fun j hj =>
        (continuous_eval_const x).measurable.comp (measurable_pi_apply j))
    · exact measurable_const
  have hindep := infraredCharacterization_indepFun_H_finePrefix M H N hH
  have hcomp := hindep.comp hφmeas hψmeas
  have hleft : (φ ∘ H) =ᵐ[(chaosSampleLaw M).toMeasure]
      (fun omega : BilateralField d => Real.exp (H omega x)) := by
    filter_upwards [] with omega
    rfl
  have hright : (ψ ∘ (fun omega : BilateralField d =>
      fun j : Fin (N + 1) => omega (-(Int.ofNat j)))) =ᵐ[(chaosSampleLaw M).toMeasure]
      (fun omega : BilateralField d => fineDensity M N omega x) := by
    filter_upwards [] with omega
    show Real.exp (∑ j : Fin (N + 1), (omega (-(Int.ofNat j))) x -
        (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) = fineDensity M N omega x
    unfold fineDensity finePotential
    have hs : (∑ j : Fin (N + 1), (omega (-(Int.ofNat j))) x) =
        ∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))) x := by
      simpa using (Fin.sum_univ_eq_sum_range
        (fun j : ℕ => (omega (-(Int.ofNat j))) x) (N + 1))
    rw [hs]
  have hIndepWeight : IndepFun (fun omega : BilateralField d => Real.exp (H omega x))
      (fun omega : BilateralField d => fineDensity M N omega x)
      (chaosSampleLaw M).toMeasure :=
    hcomp.congr hleft hright
  let KBall : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall x 1, isCompact_closedBall _ _⟩
  have hxK : x ∈ (KBall : Set (SpatialCoordinates d)) :=
    Metric.mem_closedBall_self (by norm_num)
  have hExpMeas : Measurable (fun omega : BilateralField d => Real.exp (H omega x)) :=
    hφmeas.comp hH.1
  have hDomInt : Integrable (fun omega : BilateralField d =>
      Real.exp (1 * ‖(H omega).restrict (KBall : Set (SpatialCoordinates d))‖))
      (chaosSampleLaw M).toMeasure :=
    exists_compactExponentialMoment_of_infraredCharacterization hd M H hH KBall 1 (by norm_num)
  have hExpInt : Integrable (fun omega : BilateralField d => Real.exp (H omega x))
      (chaosSampleLaw M).toMeasure := by
    apply hDomInt.mono' hExpMeas.aestronglyMeasurable
    filter_upwards with omega
    have hb : |H omega x| ≤ ‖(H omega).restrict (KBall : Set (SpatialCoordinates d))‖ := by
      have h0 := ((H omega).restrict (KBall : Set (SpatialCoordinates d))).norm_coe_le_norm
        ⟨x, hxK⟩
      simpa [ContinuousMap.restrict_apply, Real.norm_eq_abs] using h0
    have hfin : H omega x ≤ ‖(H omega).restrict (KBall : Set (SpatialCoordinates d))‖ :=
      (abs_le.mp hb).2
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
    exact Real.exp_le_exp.mpr hfin
  have hDensityInt : Integrable (fun omega : BilateralField d => fineDensity M N omega x)
      (chaosSampleLaw M).toMeasure :=
    (conditionalFineFiltration_zero_eq_restrict_and_fineDensity_martingale M x).2.integrable N
  simpa [Pi.mul_apply] using hIndepWeight.integrable_mul hExpInt hDensityInt

end SubdiffusiveProcess
