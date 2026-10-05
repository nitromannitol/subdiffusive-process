
module

public import SubdiffusiveProcess.CoarseGrainingVocab.NegativeBesovOneCube
public import SubdiffusiveProcess.Section9.MomentLogTail

@[expose] public section

/-! # One-cube logarithmic upper tail -/

open MeasureTheory ProbabilityTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.Section9

open SubdiffusiveProcess.CoarseGrainingVocab _root_.SubdiffusiveProcess.Model

noncomputable section

/-- The literal normalized cutoff average on the centered cube of scale `m`. -/
noncomputable def cutoffOriginCubeAverage {d : ℕ} (M : GMCModel d) (m : ℕ)
    (omega : PotentialSample d) : ℝ :=
  ∫ x, aCutoff M m omega x ∂normalizedCubeMeasure (originCube d (m : ℤ))

private theorem integrable_aCutoff_originCube {d : ℕ} (M : GMCModel d) (m : ℕ)
    (omega : PotentialSample d) :
    Integrable (aCutoff M m omega) (normalizedCubeMeasure (originCube d (m : ℤ))) := by
  exact (exactCircIntegrable_of_continuous (originCube d (m : ℤ))
    (continuous_aCutoff M m omega)).block 0 (originCube d (m : ℤ)) (by
      simp only [descendantsAtDepth_zero, Finset.mem_singleton])

theorem measurable_cutoffOriginCubeAverage {d : ℕ} (M : GMCModel d) (m : ℕ) :
    Measurable (cutoffOriginCubeAverage M m) := by
  exact (measurable_cutoff_uncurry M m).stronglyMeasurable.integral_prod_right'.measurable

theorem cutoffOriginCubeAverage_pos {d : ℕ} (M : GMCModel d) (m : ℕ)
    (omega : PotentialSample d) : 0 < cutoffOriginCubeAverage M m omega := by
  unfold cutoffOriginCubeAverage
  have hnonneg : 0 ≤ᵐ[normalizedCubeMeasure (originCube d (m : ℤ))]
      aCutoff M m omega := Filter.Eventually.of_forall fun x ↦ (aCutoff_pos M m omega x).le
  rw [integral_pos_iff_support_of_nonneg_ae hnonneg
    (integrable_aCutoff_originCube M m omega)]
  have hsupp : Function.support (aCutoff M m omega) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (aCutoff_pos M m omega x).ne'
  rw [hsupp, normalizedCubeMeasure_apply_univ]
  exact zero_lt_one

/-- At `n = -1` and depth zero, the exact-circ block mean is precisely the
centered normalized cutoff average. -/
theorem exactCircBlockMean_cutoffRatio_negOne_depth_zero {d : ℕ}
    (M : GMCModel d) (m : ℕ) (omega : PotentialSample d) :
    exactCircBlockMean (originCube d (m : ℤ)) (cutoffRatioMinusOne M m (-1) omega)
        ((cutoffRatioExactCircIntegrable M m (-1) omega).block 0
          (originCube d (m : ℤ)) (by simp [descendantsAtDepth_zero])) =
      cutoffOriginCubeAverage M m omega - 1 := by
  let : IsProbabilityMeasure (normalizedCubeMeasure (originCube d (m : ℤ))) :=
    ⟨normalizedCubeMeasure_apply_univ _⟩
  rw [exactCircBlockMean_eq]
  have hratio : cutoffRatioMinusOne M m (-1) omega =
      fun x ↦ aCutoff M m omega x - 1 := by
    funext x
    simp [cutoffRatioMinusOne, aCutoffAtInt]
  rw [hratio, integral_sub (integrable_aCutoff_originCube M m omega) (integrable_const 1)]
  simp [cutoffOriginCubeAverage]

/-- The actual depth-zero one-cube moment producer gives both the logarithmic
upper tail and the source failure-event estimate. -/
theorem cutoffOriginCube_log_tail_and_failure {d : ℕ} (M : GMCModel d)
    (m : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (hsmall : p * M.delta ^ 2 * Real.log (2 + p) ≤
      negativeBesovOneCubeSmallConst d)
    (hmomentSmall : negativeBesovOneCubeConst d * M.delta * Real.sqrt p *
      Real.log p ≤ 1 / 8) :
    SubdiffusiveProcess.OGammaLE M.P.toMeasure 1 p⁻¹
        (fun omega ↦ Real.log (cutoffOriginCubeAverage M m omega) -
          Real.log (9 / 8 : ℝ)) ∧
      M.P.toMeasure.real {omega | 1 / 2 ≤ |cutoffOriginCubeAverage M m omega - 1|} ≤
        Real.exp (-p * Real.log 4) := by
  let Q := originCube d (m : ℤ)
  let X : PotentialSample d → ℝ := fun omega ↦
    exactCircBlockMean Q (cutoffRatioMinusOne M m (-1) omega)
      ((cutoffRatioExactCircIntegrable M m (-1) omega).block 0 Q (by
        dsimp [Q]
        simp only [Finset.mem_singleton]))
  have hp0 : 0 < p := by linarith
  have hX : Measurable X := by
    exact measurable_exactCircBlockMean_of_uncurry Q
      (cutoffRatioMinusOne M m (-1)) (measurable_cutoffRatioMinusOne_uncurry M m (-1))
      (fun omega ↦ (cutoffRatioExactCircIntegrable M m (-1) omega).block 0 Q (by
        dsimp [Q]
        simp only [Finset.mem_singleton]))
  have hnorm : paperLpNorm M.P.toMeasure p X ≤
      ENNReal.ofReal (negativeBesovOneCubeConst d * M.delta * Real.sqrt p * Real.log p) := by
    simpa [X, Q] using!
      negativeBesov_cutoffRatio_oneCube_moment M hp hsmall m (-1) (by omega) (by omega)
        0 Q (by dsimp [Q]; simp only [Finset.mem_singleton])
  have hnormSmall : paperLpNorm M.P.toMeasure p X ≤ ENNReal.ofReal (1 / 8 : ℝ) :=
    hnorm.trans (ENNReal.ofReal_le_ofReal hmomentSmall)
  have hmem : MemLp X (ENNReal.ofReal p) M.P.toMeasure := by
    rw [← SubdiffusiveProcess.RawLp.old_memLp_iff_guarded]
    exact ⟨hX.aestronglyMeasurable, lt_of_le_of_lt hnormSmall ENNReal.ofReal_lt_top⟩
  have hmoment : Integrable (fun omega ↦ |X omega| ^ p) M.P.toMeasure := by
    have := (integrable_norm_rpow_iff hX.aestronglyMeasurable
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top).2 hmem
    simpa [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs] using! this
  let I : ℝ := ∫ omega, |X omega| ^ p ∂M.P.toMeasure
  have hI0 : 0 ≤ I := integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hroot : I ^ p⁻¹ ≤ 1 / 8 := by
    have heq := paperLpNorm_eq_ofReal_integral_abs_rpow_root
      M.P.toMeasure hp0 hX hmoment
    rw [heq] at hnormSmall
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hnormSmall
  have hIle : I ≤ (1 / 8 : ℝ) ^ p := by
    calc
      I = (I ^ p⁻¹) ^ p := (Real.rpow_inv_rpow hI0 hp0.ne').symm
      _ ≤ (1 / 8 : ℝ) ^ p := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _)
        hroot hp0.le
  have hmomentSmall' : (8 : ℝ) ^ p * I ≤ 1 := by
    calc
      (8 : ℝ) ^ p * I ≤ (8 : ℝ) ^ p * (1 / 8 : ℝ) ^ p := by gcongr
      _ = (8 * (1 / 8 : ℝ)) ^ p := (Real.mul_rpow (by norm_num) (by norm_num)).symm
      _ = 1 := by norm_num
  have hXA : X = fun omega ↦ cutoffOriginCubeAverage M m omega - 1 := by
    funext omega
    exact exactCircBlockMean_cutoffRatio_negOne_depth_zero M m omega
  have hAmeas := measurable_cutoffOriginCubeAverage M m
  have hmomentA : Integrable
      (fun omega ↦ |cutoffOriginCubeAverage M m omega - 1| ^ p) M.P.toMeasure := by
    have h := hmoment
    rw [hXA] at h
    exact h
  have hmomentSmallA : (8 : ℝ) ^ p *
      ∫ omega, |cutoffOriginCubeAverage M m omega - 1| ^ p ∂M.P.toMeasure ≤ 1 := by
    have h := hmomentSmall'
    dsimp only [I] at h
    rw [hXA] at h
    exact h
  have hlog := ogammaLE_one_log_sub_of_centered_moment M.P.toMeasure
    (cutoffOriginCubeAverage M m) p hAmeas
    (fun omega ↦ (cutoffOriginCubeAverage_pos M m omega).le) hp hmomentA hmomentSmallA
  refine ⟨hlog, ?_⟩
  have hmarkov := centered_moment_failure_bound M.P.toMeasure
    (cutoffOriginCubeAverage M m) p hp0 hmomentA
  have hIA : (∫ omega, |cutoffOriginCubeAverage M m omega - 1| ^ p
      ∂M.P.toMeasure) = I := by
    dsimp only [I]
    apply integral_congr_ae
    filter_upwards with omega
    rw [congrFun hXA omega]
  rw [hIA] at hmarkov
  have hhalf : 0 < (1 / 2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  calc
    M.P.toMeasure.real {omega | 1 / 2 ≤ |cutoffOriginCubeAverage M m omega - 1|} ≤
        I / (1 / 2 : ℝ) ^ p := (le_div_iff₀ hhalf).2 (by
          simpa only [mul_comm] using! hmarkov)
    _ ≤ (1 / 8 : ℝ) ^ p / (1 / 2 : ℝ) ^ p := by gcongr
    _ = (1 / 4 : ℝ) ^ p := by
      rw [← Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num
    _ = Real.exp (-p * Real.log 4) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 4), Real.log_div]
      · rw [Real.log_one]
        congr 1
        ring
      · norm_num
      · norm_num

end

end SubdiffusiveProcess.Section9
