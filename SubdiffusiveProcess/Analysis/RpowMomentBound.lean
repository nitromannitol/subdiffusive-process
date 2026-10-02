import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment




open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess



theorem eLpNorm_le_ofReal_of_rpow_integral_le {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {g : α → ℝ} (hg_nonneg : 0 ≤ᵐ[μ] g) (q : ℝ) (hq : 0 < q)
    (hgq_int : Integrable (fun x => g x ^ q) μ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∫ x, g x ^ q ∂μ ≤ B ^ q) :
    eLpNorm g (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B := by
  have hq0 : (ENNReal.ofReal q) ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hqtop : (ENNReal.ofReal q) ≠ ∞ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop, ENNReal.toReal_ofReal hq.le]
  have hstep : (∫⁻ x, ‖g x‖ₑ ^ q ∂μ) = ENNReal.ofReal (∫ x, g x ^ q ∂μ) := by
    have hcongr : (fun x => ‖g x‖ₑ ^ q) =ᵐ[μ] (fun x => ENNReal.ofReal (g x ^ q)) := by
      filter_upwards [hg_nonneg] with x hx
      rw [Real.enorm_eq_ofReal hx, ENNReal.ofReal_rpow_of_nonneg hx hq.le]
    rw [lintegral_congr_ae hcongr]
    exact (ofReal_integral_eq_lintegral_ofReal hgq_int
      (hg_nonneg.mono (fun x hx => Real.rpow_nonneg hx q))).symm
  rw [hstep]
  have hqne : q ≠ 0 := ne_of_gt hq
  have hmono : ENNReal.ofReal (∫ x, g x ^ q ∂μ) ≤ ENNReal.ofReal (B ^ q) :=
    ENNReal.ofReal_le_ofReal hbound
  calc (ENNReal.ofReal (∫ x, g x ^ q ∂μ)) ^ (1 / q)
      ≤ (ENNReal.ofReal (B ^ q)) ^ (1 / q) := by
        gcongr
    _ = ENNReal.ofReal B := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
        congr 1
        rw [← Real.rpow_mul hB, mul_one_div, div_self hqne, Real.rpow_one]



theorem exp_H_point_eLpNorm_uniform_bound {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C : SpatialCoordinates d → ℝ, (∀ z, 0 ≤ C z) ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
      (z : SpatialCoordinates d) (q : ℝ), 0 < q →
      MemLp (fun om => Real.exp |H om z|) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => Real.exp |H om z|) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((2 * Real.exp (C z * q ^ 2 * M.delta ^ 2)) ^ (1 / q)) := by
  obtain ⟨Cf, hCfnonneg, hCf⟩ := exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  refine ⟨fun z => Cf ⟨{z}, isCompact_singleton⟩, fun z => hCfnonneg _, ?_⟩
  intro M H hH z q hq
  set K : Compacts (SpatialCoordinates d) := ⟨{z}, isCompact_singleton⟩ with hKdef
  have hzK : z ∈ (K : Set (SpatialCoordinates d)) := rfl
  have hmeasH : Measurable fun om => H om z := (continuous_eval_const z).measurable.comp hH.1
  have hmeasHabs : Measurable fun om => |H om z| := continuous_abs.measurable.comp hmeasH
  have hmeas : AEStronglyMeasurable (fun om => Real.exp |H om z|) (chaosSampleLaw M).toMeasure :=
    (Real.measurable_exp.comp hmeasHabs).aestronglyMeasurable
  have hmeasExpQ : AEStronglyMeasurable (fun om => Real.exp (q * |H om z|))
      (chaosSampleLaw M).toMeasure :=
    (Real.measurable_exp.comp (measurable_const.mul hmeasHabs)).aestronglyMeasurable
  have hle : ∀ om, |H om z| ≤ ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ := by
    intro om
    have := ContinuousMap.norm_coe_le_norm ((H om).restrict (K : Set (SpatialCoordinates d)))
      ⟨z, hzK⟩
    rwa [Real.norm_eq_abs] at this
  have hnonneg : 0 ≤ᵐ[(chaosSampleLaw M).toMeasure] (fun om => Real.exp |H om z|) :=
    Filter.Eventually.of_forall (fun om => (Real.exp_pos _).le)
  obtain ⟨hint, hbound⟩ := hCf M H hH K q hq.le
  have hpow_eq : (fun om => (Real.exp |H om z|) ^ q) = fun om => Real.exp (q * |H om z|) := by
    funext om
    rw [← Real.exp_mul, mul_comm]
  have hexp_le : ∀ om, Real.exp (q * |H om z|) ≤
      Real.exp (q * ‖(H om).restrict (K : Set (SpatialCoordinates d))‖) :=
    fun om => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hle om) hq.le)
  have hLHS_int : Integrable (fun om => Real.exp (q * |H om z|)) (chaosSampleLaw M).toMeasure := by
    refine hint.mono' hmeasExpQ (Filter.Eventually.of_forall (fun om => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact hexp_le om
  have hLHS_bound : ∫ om, Real.exp (q * |H om z|) ∂(chaosSampleLaw M).toMeasure ≤
      2 * Real.exp (Cf K * q ^ 2 * M.delta ^ 2) :=
    (integral_mono hLHS_int hint hexp_le).trans hbound
  have hint' : Integrable (fun om => (Real.exp |H om z|) ^ q) (chaosSampleLaw M).toMeasure := by
    rw [hpow_eq]; exact hLHS_int
  have hBpow : ((2 * Real.exp (Cf K * q ^ 2 * M.delta ^ 2)) ^ (1 / q)) ^ q =
      2 * Real.exp (Cf K * q ^ 2 * M.delta ^ 2) := by
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (ne_of_gt hq), Real.rpow_one]
  have hbound' : ∫ om, (Real.exp |H om z|) ^ q ∂(chaosSampleLaw M).toMeasure ≤
      ((2 * Real.exp (Cf K * q ^ 2 * M.delta ^ 2)) ^ (1 / q)) ^ q := by
    rw [hpow_eq, hBpow]
    exact hLHS_bound
  have hfinal := eLpNorm_le_ofReal_of_rpow_integral_le hnonneg q hq hint' _
    (Real.rpow_nonneg (by positivity) _) hbound'
  exact ⟨⟨hmeas, lt_of_le_of_lt hfinal ENNReal.ofReal_lt_top⟩, hfinal⟩



theorem exp_H_compact_eLpNorm_uniform_bound {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C : Compacts (SpatialCoordinates d) → ℝ, (∀ K, 0 ≤ C K) ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
      (K : Compacts (SpatialCoordinates d)) (q : ℝ), 0 < q →
      MemLp (fun om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
          (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((2 * Real.exp (C K * q ^ 2 * M.delta ^ 2)) ^ (1 / q)) := by
  obtain ⟨Cf, hCfnonneg, hCf⟩ := exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  refine ⟨Cf, hCfnonneg, ?_⟩
  intro M H hH K q hq
  letI : MeasurableSpace C(K, ℝ) := borel _
  haveI : BorelSpace C(K, ℝ) := ⟨rfl⟩
  have hmeasHK : Measurable fun om => ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ :=
    ((ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).measurable.comp
      hH.1).norm
  have hmeas : AEStronglyMeasurable
      (fun om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
      (chaosSampleLaw M).toMeasure :=
    (Real.measurable_exp.comp hmeasHK).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[(chaosSampleLaw M).toMeasure]
      (fun om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖) :=
    Filter.Eventually.of_forall (fun om => (Real.exp_pos _).le)
  obtain ⟨hint, hbound⟩ := hCf M H hH K q hq.le
  have hpow_eq : (fun om => (Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖) ^ q) =
      fun om => Real.exp (q * ‖(H om).restrict (K : Set (SpatialCoordinates d))‖) := by
    funext om
    rw [← Real.exp_mul, mul_comm]
  have hint' : Integrable
      (fun om => (Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖) ^ q)
      (chaosSampleLaw M).toMeasure := by
    rw [hpow_eq]; exact hint
  have hBpow : ((2 * Real.exp (Cf K * q ^ 2 * M.delta ^ 2)) ^ (1 / q)) ^ q =
      2 * Real.exp (Cf K * q ^ 2 * M.delta ^ 2) := by
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (ne_of_gt hq), Real.rpow_one]
  have hbound' : ∫ om, (Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖) ^ q
      ∂(chaosSampleLaw M).toMeasure ≤
      ((2 * Real.exp (Cf K * q ^ 2 * M.delta ^ 2)) ^ (1 / q)) ^ q := by
    rw [hpow_eq, hBpow]
    exact hbound
  have hfinal := eLpNorm_le_ofReal_of_rpow_integral_le hnonneg q hq hint' _
    (Real.rpow_nonneg (by positivity) _) hbound'
  exact ⟨⟨hmeas, lt_of_le_of_lt hfinal ENNReal.ofReal_lt_top⟩, hfinal⟩

end SubdiffusiveProcess
