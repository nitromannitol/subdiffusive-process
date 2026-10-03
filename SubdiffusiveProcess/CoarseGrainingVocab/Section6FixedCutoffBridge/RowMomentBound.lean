module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.AllScaleProbeMoment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ResponseCoefficientMeasurability

@[expose] public section

/-!
# The `L^p` union bound over a descendant family

Step 1 of the `L^p` plan: an `L^p` bound for one row
`Ch02`/paper `scaleResponseAtScale` of the fixed-cutoff field, obtained from

* the finite probe reduction `cutoffProbeForm_le_finiteProbeSum`, which
  dominates every probe value on a cube `R` by the single random variable
  `finiteProbeSum M L alpha R`;
* the `xi`-power union bound `max_{R ∈ D} F_R ≤ (∑_{R ∈ D} F_R^xi)^{1/xi}`,
  whose `L^xi` cost is the *`xi`-th root* of the cardinality — the reason the
  auxiliary order `xi` has to be taken large;
* the all-cube decaying moment bound of `AllScaleProbeMoment.lean`.

Everything is carried out in `ℝ≥0∞`, where the tsum over the descendant scales
is unconditional, so no summability side condition ever appears.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section

abbrev S6 (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

variable {d : ℕ}

/-! ## Ambient measurability of the paper carriers -/

theorem coefficientSigma_aCutoff_le_ambient'
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    coefficientSigma (fun omega ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) ≤
      (inferInstance : MeasurableSpace (S6 d)) := by
  unfold coefficientSigma
  refine iSup_le fun x ↦ ?_
  exact (SubdiffusiveProcess.Frozen.Assumptions.measurable_aCutoff M L x).comap_le

theorem measurable_paperScaleResponseAtScale_ambient [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (Q : TriadicCube d) (k : ℤ) :
    Measurable fun omega : S6 d =>
      paperScaleResponseAtScale Q k .infinity
        (aCutoffFamily M L omega) (ahom M L) :=
  (measurable_paperScaleResponseAtScale_infinity_aCutoffFamily_coefficientSigma
    M L Q k).mono (coefficientSigma_aCutoff_le_ambient' M L) le_rfl

theorem measurable_paperHomogenizationError_ambient [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (Q : TriadicCube d)
    (n : ℤ) (s q : ℝ) :
    Measurable fun omega : S6 d =>
      paperHomogenizationError Q n s .infinity (.finite q)
        (aCutoffFamily M L omega) (ahom M L) :=
  (measurable_paperHomogenizationError_infinity_finite_aCutoffFamily_coefficientSigma
    M L Q n s q).mono (coefficientSigma_aCutoff_le_ambient' M L) le_rfl

/-! ## The probe reduction in the paper carrier -/

/-- Every paper probe maximum of the cutoff field is dominated by the finite
probe sum. -/
theorem paperScalarProbeMax_le_ofReal_finiteProbeSum [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {alpha : ℝ}
    (halpha : 0 < alpha) (R : TriadicCube d) (omega : S6 d) :
    paperScalarProbeMax R (aCutoffFamily M L omega) alpha ≤
      ENNReal.ofReal (finiteProbeSum M L alpha R omega) := by
  rw [paperScalarProbeMax]
  refine iSup_le ?_
  rintro ⟨v, hv⟩
  exact ENNReal.ofReal_le_ofReal
    (cutoffProbeForm_le_finiteProbeSum M L halpha R omega hv)

/-- **The `xi`-power union bound.**  The `2 xi`-th power of one row of the paper
response is dominated by the sum of the `xi`-th powers of the per-cube probe
sums. -/
theorem paperScaleResponseAtScale_rpow_le [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {alpha : ℝ}
    (halpha : 0 < alpha) (Q : TriadicCube d) (k : ℤ) (omega : S6 d)
    {xi : ℝ} (hxi : 0 < xi) :
    (paperScaleResponseAtScale Q k .infinity
        (aCutoffFamily M L omega) alpha) ^ (2 * xi) ≤
      ∑ R ∈ descendantsAtScale Q k,
        (ENNReal.ofReal (finiteProbeSum M L alpha R omega)) ^ xi := by
  classical
  set X : ℝ≥0∞ := ∑ R ∈ descendantsAtScale Q k,
    (ENNReal.ofReal (finiteProbeSum M L alpha R omega)) ^ xi with hX
  have hmax : paperMaxDescendantProbeAtScale Q k (aCutoffFamily M L omega) alpha
      ≤ X ^ xi⁻¹ := by
    rw [paperMaxDescendantProbeAtScale]
    refine iSup_le ?_
    rintro ⟨R, hR⟩
    refine le_trans
      (paperScalarProbeMax_le_ofReal_finiteProbeSum M L halpha R omega) ?_
    have hterm : (ENNReal.ofReal (finiteProbeSum M L alpha R omega)) ^ xi ≤ X :=
      Finset.single_le_sum
        (f := fun S : TriadicCube d =>
          (ENNReal.ofReal (finiteProbeSum M L alpha S omega)) ^ xi)
        (fun _ _ => zero_le) hR
    have hstep := ENNReal.rpow_le_rpow hterm (le_of_lt (inv_pos.2 hxi))
    rwa [← ENNReal.rpow_mul, mul_inv_cancel₀ hxi.ne', ENNReal.rpow_one] at hstep
  have h1 : (paperMaxDescendantProbeAtScale Q k
        (aCutoffFamily M L omega) alpha) ^ (1 / 2 : ℝ) ≤
      (X ^ xi⁻¹) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hmax (by norm_num)
  have h2 := ENNReal.rpow_le_rpow h1
    (le_of_lt (by positivity : (0 : ℝ) < 2 * xi))
  have hrhs : ((X ^ xi⁻¹) ^ (1 / 2 : ℝ)) ^ (2 * xi) = X := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    have hexp : xi⁻¹ * ((1 / 2 : ℝ) * (2 * xi)) = 1 := by
      field_simp
    rw [hexp, ENNReal.rpow_one]
  rw [paperScaleResponseAtScale]
  rw [hrhs] at h2
  exact h2

/-! ## The `L^xi` moment of the probe sum in `ℝ≥0∞` -/

theorem lintegral_ofReal_finiteProbeSum_rpow_eq [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (alpha : ℝ)
    (R : TriadicCube d) {xi : ℝ} (hxi : 1 ≤ xi) :
    (∫⁻ omega, (ENNReal.ofReal (finiteProbeSum M L alpha R omega)) ^ xi
        ∂M.P.toMeasure) =
      ENNReal.ofReal ((lpMoment M.P.toMeasure xi
        (fun omega => finiteProbeSum M L alpha R omega)) ^ xi) := by
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  have hnn : ∀ omega : S6 d, 0 ≤ finiteProbeSum M L alpha R omega :=
    fun omega => finiteProbeSum_nonneg M L alpha R omega
  have habs : (fun omega : S6 d => |finiteProbeSum M L alpha R omega| ^ xi) =
      fun omega : S6 d => (finiteProbeSum M L alpha R omega) ^ xi := by
    funext omega
    rw [abs_of_nonneg (hnn omega)]
  have hint : Integrable
      (fun omega : S6 d => (finiteProbeSum M L alpha R omega) ^ xi)
      M.P.toMeasure := by
    have := integrable_abs_rpow_of_memLp hxi0
      (memLp_finiteProbeSum M L alpha R hxi)
    rwa [habs] at this
  have hlp : (lpMoment M.P.toMeasure xi
      (fun omega => finiteProbeSum M L alpha R omega)) ^ xi =
      ∫ omega, (finiteProbeSum M L alpha R omega) ^ xi ∂M.P.toMeasure := by
    simp only [lpMoment, habs]
    rw [← Real.rpow_mul (integral_nonneg fun omega =>
      Real.rpow_nonneg (hnn omega) _), inv_mul_cancel₀ hxi0.ne',
      Real.rpow_one]
  rw [hlp, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun omega =>
      Real.rpow_nonneg (hnn omega) _)]
  refine lintegral_congr fun omega => ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (hnn omega) hxi0.le]

/-- **The `L^{2 xi}` bound for one row.**  The cardinality of the descendant
family enters only through its `xi`-th root — the whole point of the union
bound. -/
theorem lintegral_paperScaleResponseAtScale_rpow_le [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {alpha : ℝ}
    (halpha : 0 < alpha) (Q : TriadicCube d) (k : ℤ) {xi : ℝ} (hxi : 1 ≤ xi)
    (A : ℝ)
    (hA : ∀ R ∈ descendantsAtScale Q k,
      lpMoment M.P.toMeasure xi
        (fun omega => finiteProbeSum M L alpha R omega) ≤ A) :
    (∫⁻ omega, (paperScaleResponseAtScale Q k .infinity
        (aCutoffFamily M L omega) alpha) ^ (2 * xi) ∂M.P.toMeasure) ≤
      ((descendantsAtScale Q k).card : ℝ≥0∞) * ENNReal.ofReal (A ^ xi) := by
  classical
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  have hmono : (∫⁻ omega, (paperScaleResponseAtScale Q k .infinity
        (aCutoffFamily M L omega) alpha) ^ (2 * xi) ∂M.P.toMeasure) ≤
      ∫⁻ omega, (∑ R ∈ descendantsAtScale Q k,
        (ENNReal.ofReal (finiteProbeSum M L alpha R omega)) ^ xi)
        ∂M.P.toMeasure :=
    lintegral_mono fun omega =>
      paperScaleResponseAtScale_rpow_le M L halpha Q k omega hxi0
  refine hmono.trans ?_
  rw [lintegral_finset_sum _ (fun R _ => by
    exact ((measurable_finiteProbeSum M L alpha R).ennreal_ofReal).pow_const xi)]
  have hterm : ∀ R ∈ descendantsAtScale Q k,
      (∫⁻ omega, (ENNReal.ofReal (finiteProbeSum M L alpha R omega)) ^ xi
        ∂M.P.toMeasure) ≤ ENNReal.ofReal (A ^ xi) := by
    intro R hR
    rw [lintegral_ofReal_finiteProbeSum_rpow_eq M L alpha R hxi]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (lpMoment_nonneg _ _ _) (hA R hR) hxi0.le)
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
  rw [nsmul_eq_mul]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
