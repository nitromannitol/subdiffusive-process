module

public import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment

@[expose] public section

/-!
For `SubdiffusiveProcess.Paper.prop_conc` and `prop_growth_uniform`: a real-exponent version of the moment bound
(the natural-number version uses exponents `n : ℕ`, via `(n : ℝ≥0∞)`), needed here because `aux_prop_growth_energy_assembly_root_extremes`
(`prop_growth_energy_assembly`) works at the REAL exponent
`ENNReal.ofReal q` throughout (`q` ranges over `lem_extremes`' own moment-order parameter, not
restricted to naturals).

Combined with the model-uniform exponential-moment bound
(`exists_uniform_compactExponentialMoment_of_infraredCharacterization`), this gives a model-uniform
`eLpNorm` bound for `fun om => Real.exp |H om z|` at any point `z` and real order `q > 0` — the
bound that turns `aux_prop_growth_energy_assembly_root_extremes`'s `CE0`
(obtainable via bare `MemLp` existence, `.toReal`'d from an unspecified `eLpNorm`, hence a
priori model-dependent) into an EXPLICIT bound depending only on `M.delta`, closing the gap once
`M.delta ≤ delta0` is fixed.
-/

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

/-- Real-exponent moment bound: a nonnegative real function with a bounded
Bochner `q`-th moment (`q : ℝ`, `q > 0`) has `eLpNorm` at `ENNReal.ofReal q` bounded by the moment's
`q`-th root. Same proof technique (`eLpNorm_eq_lintegral_rpow_enorm` +
`ofReal_integral_eq_lintegral_ofReal` + `ENNReal.ofReal_rpow_of_nonneg`), generalized from
`ENNReal.rpow_natCast`/`ENNReal.ofReal_pow` to their real-exponent counterparts. -/
theorem eLpNorm_le_ofReal_of_rpow_integral_le {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {g : α → ℝ} (hg_nonneg : 0 ≤ᵐ[μ] g) (q : ℝ) (hq : 0 < q)
    (hgq_int : Integrable (fun x => g x ^ q) μ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∫ x, g x ^ q ∂μ ≤ B ^ q) :
    eLpNorm g (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B := by
  have hq0 : (ENNReal.ofReal q) ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hqtop : (ENNReal.ofReal q) ≠ ∞ := ENNReal.ofReal_ne_top
  have hgmeas : AEStronglyMeasurable g μ := by
    have hroot := (hgq_int.aestronglyMeasurable.aemeasurable.pow_const (1 / q)).aestronglyMeasurable
    apply hroot.congr
    filter_upwards [hg_nonneg] with x hx
    rw [← Real.rpow_mul hx, mul_one_div, div_self hq.ne', Real.rpow_one]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop hgmeas, ENNReal.toReal_ofReal hq.le]
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

/-- **Model-uniform `eLpNorm` bound for `exp|H(z)|`.** For any `InfraredCharacterization M H` and
any point `z`, real order `q > 0`: `fun om => Real.exp |H om z|` has `eLpNorm` (at `ENNReal.ofReal
q`) bounded by `(2 * Real.exp (C z * q^2 * M.delta^2)) ^ (1/q)`, where `C : SpatialCoordinates d → ℝ`
is UNIFORM IN `M` (and in `H`, `q`) — the singleton-compact value of
`exists_uniform_compactExponentialMoment_of_infraredCharacterization`'s own constant function,
evaluated at `K = {z}` (that function's guarantee is only ever used with a FIXED `z` downstream,
matching `lem_coercivity_uniform`'s convention of keeping the cell's center as a fixed argument
rather than existentially quantifying over it, so `z`-dependence of `C` is harmless here).
Directly closes the model-uniformity gap in `aux_prop_growth_energy_assembly_exp_H_memLp`
(`prop_growth_energy_assembly`), whose `MemLp`-only conclusion gives no
usable numeric bound on `CE0 := (eLpNorm (fun om => Real.exp |H om z|) ...).toReal`. -/
theorem exp_H_point_eLpNorm_uniform_bound {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C : SpatialCoordinates d → ℝ, (∀ z, 0 ≤ C z) ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H)
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
  exact ⟨lt_of_le_of_lt hfinal ENNReal.ofReal_lt_top, hfinal⟩

/-- **Model-uniform `eLpNorm` bound for `exp‖H|_K‖`, at an ARBITRARY compact `K`** (not just a
singleton point). Needed for `aux_macro_moment_bank`'s own non-uniformity
(`aux_macro_moment_bank`), whose final conjunct bounds `Kmac N om`
by `(3:ℝ)^(t1*Lmac N om) * Real.exp |H om x|` for EVERY `x` in the cell `closedCube z r hr` — i.e. a
SUP over the cell, not a single point, so `exp_H_point_eLpNorm_uniform_bound` alone is not enough.
Simpler than the point version: no point-vs-restriction transfer step is needed, since the target
quantity `‖(H om).restrict K‖` IS `exists_uniform_compactExponentialMoment_of_infraredCharacterization`'s
own quantity verbatim. -/
theorem exp_H_compact_eLpNorm_uniform_bound {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C : Compacts (SpatialCoordinates d) → ℝ, (∀ K, 0 ≤ C K) ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H)
      (K : Compacts (SpatialCoordinates d)) (q : ℝ), 0 < q →
      MemLp (fun om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
          (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((2 * Real.exp (C K * q ^ 2 * M.delta ^ 2)) ^ (1 / q)) := by
  obtain ⟨Cf, hCfnonneg, hCf⟩ := exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  refine ⟨Cf, hCfnonneg, ?_⟩
  intro M H hH K q hq
  let : MeasurableSpace C(K, ℝ) := borel _
  have : BorelSpace C(K, ℝ) := ⟨rfl⟩
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
  exact ⟨lt_of_le_of_lt hfinal ENNReal.ofReal_lt_top, hfinal⟩

end SubdiffusiveProcess
