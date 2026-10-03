module

public import SubdiffusiveProcess.Frozen.Section6.DensityOfGoodScales
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
public import SubdiffusiveProcess.PrefixTailNumerics
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper

theorem prefix_bad_density_tail (d : ℕ) (s eps theta A : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (heps : eps ∈ Set.Ioc (0 : ℝ) 1)
    (htheta : theta ∈ Set.Ioc (0 : ℝ) 1) (hA : 0 < A) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ delta0 →
      ∀ (n K : ℕ) (z : Vec d),
        M.P.toMeasure {om | (∑ j ∈ Finset.Icc n (n + K),
            if om ∈ goodEvent M none j z eps s then (1 : ℝ) else 0) /
              ((K : ℝ) + 1) ≤ 1 - theta} ≤
          ENNReal.ofReal (Real.exp (-(A * ((K : ℝ) + 1)))) := by
  classical
  obtain ⟨C, hC, hdensity⟩ := SubdiffusiveProcess.Frozen.Section6.density_of_good_scales d
  let B : ℝ := C * s ^ (-6 : ℤ) * eps⁻¹ ^ 2
  let R : ℝ := s ^ 6 * eps ^ 2 * theta
  have hB : 0 < B := mul_pos (mul_pos hC (zpow_pos hs.1 _)) (sq_pos_of_pos (inv_pos.mpr heps.1))
  have hR : 0 < R := mul_pos (mul_pos (pow_pos hs.1 _) (sq_pos_of_pos heps.1)) htheta.1
  refine ⟨min (theta / B) (R / (C * A)),
    lt_min (div_pos htheta.1 hB) (div_pos hR (mul_pos hC hA)), ?_⟩
  intro M hdelta n K z
  have hδ : 0 < M.delta := M.shellPrefix.delta_pos
  have hlog : 0 < |Real.log M.delta| := abs_pos.mpr
    (Real.log_neg hδ (M.shellPrefix.delta_le_half.trans_lt (by norm_num))).ne
  have hb := aux_prefix_accumulated_error_tail_log_budget hδ
    (M.shellPrefix.delta_le_half.trans (by norm_num))
  have hbudget : C * s ^ (-6 : ℤ) * eps⁻¹ ^ 2 * M.delta ^ 2 * |Real.log M.delta| ≤ theta := by
    have hc : M.delta * B ≤ theta :=
      (le_div_iff₀ hB).mp (hdelta.trans (min_le_left _ _))
    have hm := mul_le_mul_of_nonneg_left hb hB.le
    change B * M.delta ^ 2 * |Real.log M.delta| ≤ theta
    nlinarith
  have hrate : A ≤ R / (C * M.delta ^ 2 * |Real.log M.delta|) := by
    apply (le_div_iff₀ (by positivity : 0 < C * M.delta ^ 2 * |Real.log M.delta|)).mpr
    have hc : M.delta * (C * A) ≤ R :=
      (le_div_iff₀ (mul_pos hC hA)).mp (hdelta.trans (min_le_right _ _))
    have hm := mul_le_mul_of_nonneg_left hb (mul_pos hC hA).le
    nlinarith
  have htail := hdensity M s theta eps hs htheta heps hbudget n K
  have hgood : ∀ (om : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) j,
      (if om ∈ goodEvent M none j z eps s then (1 : ℝ) else 0) =
        (if translatePotentialSample z om ∈ goodEvent M none j 0 eps s then (1 : ℝ) else 0) := by
    intro om j
    rw [mem_goodEvent_iff_translate_zero M none j eps s z om]
  have hset : {om | (∑ j ∈ Finset.Icc n (n + K),
      if om ∈ goodEvent M none j z eps s then (1 : ℝ) else 0) / ((K : ℝ) + 1) ≤ 1 - theta} =
      translatePotentialSample z ⁻¹' {om | (∑ j ∈ Finset.Icc n (n + K),
      if om ∈ goodEvent M none j 0 eps s then (1 : ℝ) else 0) / ((K : ℝ) + 1) ≤ 1 - theta} := by
    ext om
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hgood]
  rw [hset, measure_preimage_translatePotentialSample]
  refine htail.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  change -(R / (C * M.delta ^ 2 * |Real.log M.delta|)) * ((K : ℝ) + 1) ≤
    -(A * ((K : ℝ) + 1))
  nlinarith [mul_le_mul_of_nonneg_right hrate (show 0 ≤ (K : ℝ) + 1 by positivity)]

end Paper
