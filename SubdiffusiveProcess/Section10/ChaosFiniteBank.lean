module

public import Mathlib
public import SubdiffusiveProcess.Probability.MartingaleMaximalMoment
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Lane1.ChaosMoment
public import SubdiffusiveProcess.Model.HeatSemigroupVec
@[expose] public section

open MeasureTheory ProbabilityTheory Module Filter Topology
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators CompactlySupported
noncomputable section
namespace Paper


theorem aux_lim_measure_density_retained
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n m : ℕ) (hnm : n ≤ m) (x : SpatialCoordinates d)
    (A : Set (BilateralField d))
    (hA : MeasurableSet[(conditionalFineFiltration
      (fun _ : BilateralField d => (0 : C(SpatialCoordinates d, ℝ))) measurable_const) n] A) :
    (∫ w in A, fineDensity M m w x ∂(chaosSampleLaw M).toMeasure) =
      ∫ w in A, fineDensity M n w x ∂(chaosSampleLaw M).toMeasure := by
  obtain ⟨_, hmart⟩ := conditionalFineFiltration_zero_eq_restrict_and_fineDensity_martingale M x
  exact (hmart.setIntegral_eq hnm hA).symm



theorem aux_lim_measure_density_lintegral_mean
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (x : SpatialCoordinates d) :
    (∫⁻ w, ENNReal.ofReal (fineDensity M n w x) ∂(chaosSampleLaw M).toMeasure) = 1 := by
  have h_int : ∫ (w : BilateralField d), fineDensity M n w x ∂(chaosSampleLaw M) = 1 :=
    integral_fineDensity_chaosSampleLaw M n x
  have hfi : Integrable (fun w : BilateralField d => fineDensity M n w x) (chaosSampleLaw M).toMeasure :=
    integrable_of_integral_eq_one h_int
  have hnn : 0 ≤ᶠ[ae (chaosSampleLaw M).toMeasure] (fun w : BilateralField d => fineDensity M n w x) :=
    Filter.Eventually.of_forall (fun w => le_of_lt (fineDensity_pos M n w x))
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hnn, h_int]
  norm_num



theorem aux_lim_measure_cutoff_mean_measure
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A) :
    (∫⁻ w, chaosCutoff M n w A ∂(chaosSampleLaw M).toMeasure) = volume A := by
  have hmeas : Measurable (Function.uncurry (fun (w : BilateralField d) (x : SpatialCoordinates d) => ENNReal.ofReal (fineDensity M n w x))) := by
    unfold fineDensity finePotential
    fun_prop
  have key : ∀ w, chaosCutoff M n w A
      = ∫⁻ x in A, ENNReal.ofReal (fineDensity M n w x) ∂(volume : Measure (SpatialCoordinates d)) := by
    intro w
    rw [chaosCutoff, withDensity_apply _ hA]
    rfl
  simp_rw [key]
  have hswap : (∫⁻ w, ∫⁻ x in A, ENNReal.ofReal (fineDensity M n w x) ∂(volume : Measure (SpatialCoordinates d)) ∂(chaosSampleLaw M).toMeasure)
      = ∫⁻ x in A, (∫⁻ w, ENNReal.ofReal (fineDensity M n w x) ∂(chaosSampleLaw M).toMeasure) ∂(volume : Measure (SpatialCoordinates d)) := by
    refine lintegral_lintegral_swap (f := fun w x => ENNReal.ofReal (fineDensity M n w x)) ?_
    exact hmeas.aemeasurable
  rw [hswap]
  have hinner : ∀ x, (∫⁻ w, ENNReal.ofReal (fineDensity M n w x) ∂(chaosSampleLaw M).toMeasure) = 1 := by
    intro x
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_of_integral_eq_one (integral_fineDensity_chaosSampleLaw M n x))
      (Filter.Eventually.of_forall (fun w => le_of_lt (fineDensity_pos M n w x)))]
    rw [integral_fineDensity_chaosSampleLaw, ENNReal.ofReal_one]
  simp_rw [hinner]
  rw [lintegral_const]
  simp



theorem aux_lim_measure_density_retained_lintegral
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n m : ℕ) (hnm : n ≤ m) (x : SpatialCoordinates d)
    (A : Set (BilateralField d))
    (hA : MeasurableSet[(conditionalFineFiltration
      (fun _ : BilateralField d => (0 : C(SpatialCoordinates d, ℝ))) measurable_const) n] A) :
    (∫⁻ w in A, ENNReal.ofReal (fineDensity M m w x) ∂(chaosSampleLaw M).toMeasure) =
    ∫⁻ w in A, ENNReal.ofReal (fineDensity M n w x) ∂(chaosSampleLaw M).toMeasure := by
  have hm : Integrable (fun w => fineDensity M m w x) (chaosSampleLaw M).toMeasure :=
    MeasureTheory.integrable_of_integral_eq_one
      (SubdiffusiveProcess.integral_fineDensity_chaosSampleLaw M m x)
  have hn : Integrable (fun w => fineDensity M n w x) (chaosSampleLaw M).toMeasure :=
    MeasureTheory.integrable_of_integral_eq_one
      (SubdiffusiveProcess.integral_fineDensity_chaosSampleLaw M n x)
  have hmA : Integrable (fun w => fineDensity M m w x) ((chaosSampleLaw M).toMeasure.restrict A) :=
    hm.restrict
  have hnA : Integrable (fun w => fineDensity M n w x) ((chaosSampleLaw M).toMeasure.restrict A) :=
    hn.restrict
  have hpm : 0 ≤ᶠ[ae ((chaosSampleLaw M).toMeasure.restrict A)]
      (fun w => fineDensity M m w x) :=
    Filter.Eventually.of_forall (fun w => le_of_lt (SubdiffusiveProcess.fineDensity_pos M m w x))
  have hpn : 0 ≤ᶠ[ae ((chaosSampleLaw M).toMeasure.restrict A)]
      (fun w => fineDensity M n w x) :=
    Filter.Eventually.of_forall (fun w => le_of_lt (SubdiffusiveProcess.fineDensity_pos M n w x))
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmA hpm,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hnA hpn]
  congr 1
  exact aux_lim_measure_density_retained M n m hnm x A hA



theorem aux_lim_measure_chaos_unit_second_moment
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 0 < d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (hdelta : 2 * M.delta ≤ 1)
    (hrate : chaosLayerRate M 2 / Real.log 3 ≤ (d : ℝ) / 4) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (N : ℕ) (z : SpatialCoordinates d),
      (∫⁻ w, ENNReal.ofReal (((chaosCutoff M N w)
        (centeredCube z 1 zero_lt_one : Set (SpatialCoordinates d))).toReal ^ 2)
          ∂(chaosSampleLaw M).toMeasure) ≤ B := by
  refine ⟨ENNReal.ofReal ((1 + (↑(2:ℕ) : ℝ) ^ 2 * (4 * Real.sqrt (↑d)) ^ d * (2 * 3 ^ d)) *
      1 ^ (↑d * ↑(2:ℕ) - 2 * (chaosLayerRate M 2 / Real.log 3))), ENNReal.ofReal_ne_top, ?_⟩
  intro N z
  have h := lintegral_chaosCutoff_pow_le_rpow hd M 2 (by norm_num) N
    (by simpa using hdelta) hrate z 1 zero_lt_one (le_refl 1)
  exact h


theorem aux_lim_measure_cutoff_apply {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (w : BilateralField d)
    (D : Set (SpatialCoordinates d)) (hD : MeasurableSet D) :
    chaosCutoff M n w D = ∫⁻ x in D, ENNReal.ofReal (fineDensity M n w x) ∂volume := by
  rw [chaosCutoff, withDensity_apply _ hD]
  rfl

theorem aux_lim_measure_finite_rectangle {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n m : ℕ) (hnm : n ≤ m)
    (A : Set (BilateralField d))
    (hA : MeasurableSet[(conditionalFineFiltration
      (fun _ : BilateralField d => (0 : C(SpatialCoordinates d, ℝ))) measurable_const) n] A)
    (D : Set (SpatialCoordinates d)) (hD : MeasurableSet D) :
    (∫⁻ w in A, chaosCutoff M m w D ∂(chaosSampleLaw M).toMeasure) =
      ∫⁻ w in A, chaosCutoff M n w D ∂(chaosSampleLaw M).toMeasure := by
  have hf (k : ℕ) : Measurable (Function.uncurry (fun (w : BilateralField d)
      (x : SpatialCoordinates d) => ENNReal.ofReal (fineDensity M k w x))) := by
    unfold fineDensity finePotential
    fun_prop
  simp_rw [aux_lim_measure_cutoff_apply M _ _ D hD]
  rw [lintegral_lintegral_swap (hf m).aemeasurable,
    lintegral_lintegral_swap (hf n).aemeasurable]
  exact lintegral_congr (fun x => aux_lim_measure_density_retained_lintegral M n m hnm x A hA)



theorem aux_lim_measure_chaos_unit_maximal_second_moment
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 0 < d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (hdelta : 2 * M.delta ≤ 1)
    (hrate : chaosLayerRate M 2 / Real.log 3 ≤ (d : ℝ) / 4) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ z : SpatialCoordinates d,
      (∫⁻ w, ⨆ N : ℕ, ENNReal.ofReal (((chaosCutoff M N w)
        (centeredCube z 1 zero_lt_one : Set (SpatialCoordinates d))).toReal ^ 2)
          ∂(chaosSampleLaw M).toMeasure) ≤ B := by
  obtain ⟨B0, hB0ne, hB0⟩ := aux_lim_measure_chaos_unit_second_moment hd M hdelta hrate
  refine ⟨4 * B0, ENNReal.mul_ne_top (by norm_num) hB0ne, ?_⟩
  intro z
  obtain ⟨hmart, hnonneg⟩ := chaosCutoff_centeredCube_martingale_nonnegative M z 1 zero_lt_one
  have hint : ∀ N : ℕ,
      Integrable (fun omega =>
        ((chaosCutoff M N omega)
          (centeredCube z 1 zero_lt_one : Set (SpatialCoordinates d))).toReal ^ 1)
        (chaosSampleLaw M).toMeasure := by
    intro N
    simpa only [pow_one] using hmart.integrable N
  have hbound : ∀ N : ℕ,
      (∫⁻ omega, ENNReal.ofReal (((chaosCutoff M N omega)
          (centeredCube z 1 zero_lt_one : Set (SpatialCoordinates d))).toReal ^ (2 * 1))
        ∂(chaosSampleLaw M).toMeasure) ≤ B0 := by
    intro N
    simpa using hB0 N z
  have h := lintegral_iSup_evenPow_le_of_nonneg_martingale (chaosSampleLaw M).toMeasure
    _ _ hmart hnonneg 1 (le_refl 1) hint B0 hbound
  simpa using h



theorem aux_lim_measure_square_sup_dominates
    (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n)
    (hfin : (⨆ n, ENNReal.ofReal ((x n)^2)) ≠ ⊤) (n : ℕ) :
    x n ≤ 1 + (⨆ k, ENNReal.ofReal ((x k)^2)).toReal := by
  have hle : ENNReal.ofReal ((x n)^2) ≤ ⨆ k, ENNReal.ofReal ((x k)^2) :=
    le_iSup (fun k => ENNReal.ofReal ((x k)^2)) n
  have hsq : (x n)^2 ≤ (⨆ k, ENNReal.ofReal ((x k)^2)).toReal := by
    have h1 := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).mpr hle
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  nlinarith [hx n, sq_nonneg (x n - 1), hsq]


theorem aux_lim_measure_unit_moment_smallness {d : ℕ} (hd : 0 < d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hdelta : M.delta ≤ 1 / 4) :
    2 * M.delta ≤ 1 ∧ chaosLayerRate M 2 / Real.log 3 ≤ (d : ℝ) / 4 := by
  have hM := M.shellPrefix.delta_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogs : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have hsq : M.delta ^ 2 ≤ 1 / 16 := by nlinarith
  have hmul : Real.log 2 * M.delta ^ 2 ≤ Real.log 3 / 16 := by
    have h := mul_le_mul_of_nonneg_left hsq hlog2.le
    nlinarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨by linarith, ?_⟩
  unfold chaosLayerRate
  norm_num
  apply (div_le_iff₀ hlog3).mpr
  nlinarith [mul_le_mul_of_nonneg_right hdR hlog3.le]

theorem aux_lim_measure_unit_integrable_envelope {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 0 < d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hdelta : M.delta ≤ 1 / 4) :
    ∃ D : SpatialCoordinates d → BilateralField d → ℝ,
      (∀ z, Measurable (D z)) ∧ (∀ z w, 0 ≤ D z w) ∧
      ∀ z, Integrable (D z) (chaosSampleLaw M).toMeasure ∧
        ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ N,
          ((chaosCutoff M N w) (centeredCube z 1 zero_lt_one : Set (SpatialCoordinates d))).toReal ≤ D z w := by
  obtain ⟨hsmall, hrate⟩ := aux_lim_measure_unit_moment_smallness hd M hdelta
  obtain ⟨B, hB, hbound⟩ := aux_lim_measure_chaos_unit_maximal_second_moment hd M hsmall hrate
  let S : SpatialCoordinates d → BilateralField d → ℝ≥0∞ := fun z w =>
    ⨆ N : ℕ, ENNReal.ofReal (((chaosCutoff M N w)
      (centeredCube z 1 zero_lt_one : Set (SpatialCoordinates d))).toReal ^ 2)
  have hS : ∀ z, Measurable (S z) := fun z =>
    Measurable.iSup (fun N => (measurable_chaosCutoff_pow M N z 1 zero_lt_one 2).ennreal_ofReal)
  have hfin : ∀ z, (∫⁻ w, S z w ∂(chaosSampleLaw M).toMeasure) ≠ ⊤ :=
    fun z => ne_top_of_le_ne_top hB (hbound z)
  refine ⟨fun z w => 1 + (S z w).toReal, fun z => measurable_const.add (hS z).ennreal_toReal,
    fun z w => add_nonneg zero_le_one ENNReal.toReal_nonneg, fun z => ⟨?_, ?_⟩⟩
  · exact (integrable_const 1).add (integrable_toReal_of_lintegral_ne_top (hS z).aemeasurable (hfin z))
  · filter_upwards [ae_lt_top (hS z) (hfin z)] with w hw
    exact fun N => aux_lim_measure_square_sup_dominates _ (fun _ => ENNReal.toReal_nonneg) hw.ne N


end Paper
