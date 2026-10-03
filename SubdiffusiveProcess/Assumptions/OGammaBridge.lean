module

public import SubdiffusiveProcess.Frozen.Assumptions.OGammaLE
public import Homogenization.Probability.IndependentSums.GammaSigma.Basic

@[expose] public section

/-!
# Bridges between expectation and tail stretched-exponential bounds
-/

namespace SubdiffusiveProcess.OGammaBridge

open MeasureTheory
open Homogenization IndependentSums

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Expectation-form control implies tail-form control at scale
`(1 + log 2)^(1/σ) A`. -/
theorem isBigO_gammaSigma_of_ogammaLE
    {σ A : ℝ} {X : Ω → ℝ}
    (hσ : 0 < σ) (hA : 0 < A)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hX : SubdiffusiveProcess.OGammaLE μ σ A X) :
    IsBigO μ (gammaSigma σ) X
      ((1 + Real.log 2) ^ σ⁻¹ * A) := by
  rw [isBigO_gammaSigma_iff]
  intro t ht
  let c : ℝ := (1 + Real.log 2) ^ σ⁻¹
  let W : Ω → ℝ := fun ω => Real.exp ((A⁻¹ * max (X ω) 0) ^ σ)
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc_base_pos : 0 < 1 + Real.log 2 := by linarith
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hc_base_pos _
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hc_pow : c ^ σ = 1 + Real.log 2 := by
    exact Real.rpow_inv_rpow hc_base_pos.le hσ.ne'
  have hct_pow : (c * t) ^ σ = (1 + Real.log 2) * t ^ σ := by
    rw [Real.mul_rpow hc_pos.le ht_pos.le, hc_pow]
  have ht_pow_one : 1 ≤ t ^ σ := Real.one_le_rpow ht hσ.le
  have hthreshold :
      Real.exp (Real.log 2 + t ^ σ) ≤ Real.exp ((c * t) ^ σ) := by
    rw [Real.exp_le_exp, hct_pow]
    nlinarith
  have hW_nonneg : 0 ≤ᵐ[μ] W :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  have hW_int : Integrable W μ := by
    simpa [W] using hX.1
  have hsubset :
      absTailEvent X (((1 + Real.log 2) ^ σ⁻¹ * A) * t) ⊆
        {ω | Real.exp ((c * t) ^ σ) ≤ W ω} := by
    intro ω hω
    have htail : (c * A) * t < X ω := by
      simpa [c, abs_of_nonneg (hX_nonneg ω)] using hω
    have hscaled : c * t < A⁻¹ * X ω := by
      rw [inv_mul_eq_div]
      apply (lt_div_iff₀ hA).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using htail
    have hpow : (c * t) ^ σ < (A⁻¹ * X ω) ^ σ := by
      exact (Real.rpow_lt_rpow_iff (mul_nonneg hc_pos.le ht_pos.le)
        (mul_nonneg (inv_nonneg.mpr hA.le) (hX_nonneg ω)) hσ).2 hscaled
    have hexp : Real.exp ((c * t) ^ σ) < W ω := by
      dsimp [W]
      rw [max_eq_left (hX_nonneg ω)]
      exact (Real.exp_lt_exp).2 hpow
    exact le_of_lt hexp
  have hmarkov :
      Real.exp ((c * t) ^ σ) *
          μ.real {ω | Real.exp ((c * t) ^ σ) ≤ W ω} ≤ 2 := by
    exact (mul_meas_ge_le_integral_of_nonneg (μ := μ) hW_nonneg hW_int
      (Real.exp ((c * t) ^ σ))).trans hX.2
  have htail_aux :
      μ.real (absTailEvent X (((1 + Real.log 2) ^ σ⁻¹ * A) * t)) ≤
        2 / Real.exp ((c * t) ^ σ) := by
    refine (measureReal_mono hsubset
      (ne_of_lt (hW_int.measure_ge_lt_top (Real.exp_pos _)))).trans ?_
    exact (le_div_iff₀' (Real.exp_pos _)).2 hmarkov
  calc
    μ.real (absTailEvent X (((1 + Real.log 2) ^ σ⁻¹ * A) * t))
        ≤ 2 / Real.exp ((c * t) ^ σ) := htail_aux
    _ ≤ 2 / Real.exp (Real.log 2 + t ^ σ) := by
      exact div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) hthreshold
    _ = Real.exp (-(t ^ σ)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      field_simp [Real.exp_ne_zero]
      rw [← Real.exp_add]
      simp

/-- Tail-form control implies expectation-form control at scale `4^(1/σ) A`.
The measure is assumed to be a probability measure; no sign assumption on
`X` is needed. -/
theorem ogammaLE_of_isBigO_gammaSigma
    [IsProbabilityMeasure μ]
    {σ A : ℝ} {X : Ω → ℝ}
    (hσ : 0 < σ) (hA : 0 < A)
    (hXm : Measurable X)
    (hX : IsBigO μ (gammaSigma σ) X A) :
    SubdiffusiveProcess.OGammaLE μ σ ((4 : ℝ) ^ σ⁻¹ * A) X := by
  let Y : Ω → ℝ := fun ω => A⁻¹ * max (X ω) 0
  let Z : Ω → ℝ := fun ω => (Y ω) ^ σ / 4
  have hY_nonneg : ∀ ω, 0 ≤ Y ω := by
    intro ω
    exact mul_nonneg (inv_nonneg.mpr hA.le) (le_max_right _ _)
  have hYm : Measurable Y := by
    exact measurable_const.mul (hXm.max measurable_const)
  have hZ_nonneg : ∀ ω, 0 ≤ Z ω := by
    intro ω
    exact div_nonneg (Real.rpow_nonneg (hY_nonneg ω) _) (by norm_num)
  have hZm : Measurable Z := by
    exact (hYm.pow measurable_const).div_const 4
  have htail :=
    (isBigO_gammaSigma_iff (μ := μ) (X := X) (A := A) (σ := σ)).1 hX
  have hTail :
      ∀ ⦃s : ℝ⦄, s ∈ Set.Ioi (0 : ℝ) →
        μ {ω | s < Z ω} ≤ ENNReal.ofReal (Real.exp (1 - 4 * s)) := by
    intro s hs
    by_cases hs_quarter : (1 : ℝ) / 4 ≤ s
    · let u : ℝ := (4 * s) ^ σ⁻¹
      have h4s_pos : 0 < 4 * s := mul_pos (by norm_num) hs
      have hu_pos : 0 < u := Real.rpow_pos_of_pos h4s_pos _
      have hu_pow : u ^ σ = 4 * s := by
        exact Real.rpow_inv_rpow h4s_pos.le hσ.ne'
      have hu_one : 1 ≤ u := by
        have h4s_one : 1 ≤ 4 * s := by linarith
        exact Real.one_le_rpow h4s_one (inv_nonneg.mpr hσ.le)
      have hsubset : {ω | s < Z ω} ⊆ absTailEvent X (A * u) := by
        intro ω hω
        have hpow_lt : u ^ σ < Y ω ^ σ := by
          dsimp [Z] at hω
          rw [hu_pow]
          linarith
        have hu_lt_Y : u < Y ω :=
          (Real.rpow_lt_rpow_iff hu_pos.le (hY_nonneg ω) hσ).1 hpow_lt
        have hmax_lt : A * u < max (X ω) 0 := by
          dsimp [Y] at hu_lt_Y
          rw [inv_mul_eq_div] at hu_lt_Y
          simpa [mul_comm] using (lt_div_iff₀ hA).1 hu_lt_Y
        have hmax_le_abs : max (X ω) 0 ≤ |X ω| := by
          exact max_le (le_abs_self _) (abs_nonneg _)
        exact lt_of_lt_of_le hmax_lt hmax_le_abs
      have hreal :
          μ.real (absTailEvent X (A * u)) ≤ Real.exp (-(4 * s)) := by
        simpa [hu_pow] using htail hu_one
      have hfinite := measure_lt_top μ (absTailEvent X (A * u))
      calc
        μ {ω | s < Z ω} ≤ μ (absTailEvent X (A * u)) := measure_mono hsubset
        _ = ENNReal.ofReal (μ.real (absTailEvent X (A * u))) := by
          simp [Measure.real, hfinite.ne]
        _ ≤ ENNReal.ofReal (Real.exp (-(4 * s))) := ENNReal.ofReal_le_ofReal hreal
        _ ≤ ENNReal.ofReal (Real.exp (1 - 4 * s)) := by
          exact ENNReal.ofReal_le_ofReal ((Real.exp_le_exp).2 (by linarith))
    · have hprob : μ {ω | s < Z ω} ≤ 1 := by
        calc
          μ {ω | s < Z ω} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      have hone : (1 : ENNReal) ≤ ENNReal.ofReal (Real.exp (1 - 4 * s)) := by
        have hexp : (1 : ℝ) ≤ Real.exp (1 - 4 * s) := by
          apply Real.one_le_exp
          have : s < (1 : ℝ) / 4 := lt_of_not_ge hs_quarter
          linarith
        simpa using ENNReal.ofReal_le_ofReal hexp
      exact hprob.trans hone
  have hLayer :=
    MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul
      (μ := μ) (f := Z) (g := Real.exp)
      (Filter.Eventually.of_forall hZ_nonneg) hZm.aemeasurable
      (fun t _ => Real.continuous_exp.intervalIntegrable 0 t)
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
  have hdom :
      ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        μ {ω | s < Z ω} * ENNReal.ofReal (Real.exp s) ≤
          ENNReal.ofReal (Real.exp (1 - 3 * s)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    calc
      μ {ω | s < Z ω} * ENNReal.ofReal (Real.exp s)
          ≤ ENNReal.ofReal (Real.exp (1 - 4 * s)) *
              ENNReal.ofReal (Real.exp s) := by
            exact mul_le_mul_of_nonneg_right (hTail hs) (by positivity)
      _ = ENNReal.ofReal (Real.exp (1 - 3 * s)) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
            congr 2
            ring
  have hDomInt :
      IntegrableOn (fun s : ℝ => Real.exp (1 - 3 * s)) (Set.Ioi 0) := by
    have hbase := (integrableOn_exp_mul_Ioi (a := (-3 : ℝ)) (by norm_num) 0).const_mul
      (Real.exp 1)
    simpa [IntegrableOn, Real.exp_sub, div_eq_mul_inv, Real.exp_neg, mul_assoc] using hbase
  have hDomNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun s : ℝ => Real.exp (1 - 3 * s) :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  have hDomLin :
      ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (1 - 3 * s)) =
        ENNReal.ofReal (Real.exp 1 / 3) := by
    have hEq := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := volume.restrict (Set.Ioi (0 : ℝ))) hDomInt hDomNonneg
    rw [← hEq]
    congr 1
    have hfun :
        (fun s : ℝ => Real.exp (1 - 3 * s)) =
          (fun s : ℝ => Real.exp 1 * Real.exp ((-3 : ℝ) * s)) := by
      funext s
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      ∫ s in Set.Ioi (0 : ℝ), Real.exp (1 - 3 * s)
          = Real.exp 1 * ∫ s in Set.Ioi (0 : ℝ), Real.exp ((-3 : ℝ) * s) := by
            rw [hfun, integral_const_mul]
      _ = Real.exp 1 / 3 := by
            rw [integral_exp_mul_Ioi (a := (-3 : ℝ)) (by norm_num) 0]
            simp [div_eq_mul_inv]
  have hLayerBound :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω) - 1) ∂μ ≤
        ENNReal.ofReal (Real.exp 1 / 3) := by
    calc
      ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω) - 1) ∂μ
          = ∫⁻ ω, ENNReal.ofReal (∫ s in (0 : ℝ)..Z ω, Real.exp s) ∂μ := by
              apply lintegral_congr
              intro ω
              rw [integral_exp, Real.exp_zero]
      _ = ∫⁻ s in Set.Ioi (0 : ℝ),
            μ {ω | s < Z ω} * ENNReal.ofReal (Real.exp s) := hLayer
      _ ≤ ∫⁻ s in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (Real.exp (1 - 3 * s)) := lintegral_mono_ae hdom
      _ = ENNReal.ofReal (Real.exp 1 / 3) := hDomLin
  have hExpLin :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω)) ∂μ ≤ ENNReal.ofReal 2 := by
    have hpoint : ∀ ω,
        ENNReal.ofReal (Real.exp (Z ω)) =
          ENNReal.ofReal (Real.exp (Z ω) - 1) + 1 := by
      intro ω
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add]
      · congr 1
        ring
      · exact sub_nonneg.mpr (Real.one_le_exp (hZ_nonneg ω))
      · norm_num
    calc
      ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω)) ∂μ
          = ∫⁻ ω, (ENNReal.ofReal (Real.exp (Z ω) - 1) + 1) ∂μ := by
              apply lintegral_congr
              exact hpoint
      _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω) - 1) ∂μ) + 1 := by
              rw [MeasureTheory.lintegral_add_right]
              · simp
              · exact measurable_const
      _ ≤ ENNReal.ofReal (Real.exp 1 / 3) + 1 := add_le_add hLayerBound le_rfl
      _ ≤ ENNReal.ofReal 2 := by
              have hadd :
                  ENNReal.ofReal (Real.exp 1 / 3) + 1 =
                    ENNReal.ofReal (Real.exp 1 / 3 + 1) := by
                rw [← ENNReal.ofReal_one]
                exact (ENNReal.ofReal_add
                  (by positivity : 0 ≤ Real.exp 1 / 3)
                  (by norm_num : (0 : ℝ) ≤ 1)).symm
              rw [hadd]
              exact ENNReal.ofReal_le_ofReal (by
                have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
                linarith)
  have hExpMeas : AEStronglyMeasurable (fun ω => Real.exp (Z ω)) μ :=
    (hZm.exp).aestronglyMeasurable
  have hExpInt : Integrable (fun ω => Real.exp (Z ω)) μ := by
    apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hExpMeas (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).1
    exact ne_of_lt (lt_of_le_of_lt hExpLin ENNReal.ofReal_lt_top)
  have hExpIntegral : ∫ ω, Real.exp (Z ω) ∂μ ≤ 2 := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le) hExpMeas]
    have hfinite : (∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω)) ∂μ) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt hExpLin ENNReal.ofReal_lt_top)
    have htoReal := (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).2 hExpLin
    simpa using htoReal
  have hscale_pos : 0 < (4 : ℝ) ^ σ⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  have hExponent : ∀ ω,
      ((((4 : ℝ) ^ σ⁻¹ * A)⁻¹ * max (X ω) 0) ^ σ) = Z ω := by
    intro ω
    have hbase :
        (((4 : ℝ) ^ σ⁻¹ * A)⁻¹ * max (X ω) 0) =
          Y ω / ((4 : ℝ) ^ σ⁻¹) := by
      dsimp [Y]
      field_simp [hA.ne', hscale_pos.ne']
    rw [hbase, Real.div_rpow (hY_nonneg ω) hscale_pos.le]
    rw [Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 4) hσ.ne']
  constructor
  · simpa only [hExponent] using hExpInt
  · simpa only [hExponent] using hExpIntegral

end

end SubdiffusiveProcess.OGammaBridge
