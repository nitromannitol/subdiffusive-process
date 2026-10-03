module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6DerivedSupport
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Filter

noncomputable section

/-! ## 1. The substitution `s = |log δ|⁻¹` -/

/-- The algebraic identity behind the substitution: the proved concentration rate
`s ^ 2 * theta / (D * delta ^ 2)` at `s = |log delta|⁻¹` is the printed
`(theta / D) / (delta ^ 2 * |log delta| ^ 2)`. -/
theorem rate_inv_abs_log_eq (delta theta D : ℝ) (hdelta : delta ≠ 0)
    (hlog : Real.log delta ≠ 0) (hD : D ≠ 0) :
    (|Real.log delta|⁻¹) ^ 2 * theta / (D * delta ^ 2) =
      theta / D / (delta ^ 2 * |Real.log delta| ^ 2) := by
  have habs : |Real.log delta| ≠ 0 := abs_ne_zero.2 hlog
  field_simp

/-- **The shape converter.**  A proved concentration bound with rate
`s ^ 2 * theta / (D * delta ^ 2)` at `s = |log delta|⁻¹`, over a window count
`r ≥ 1`, dominates the printed `exp (-c / (delta ^ 2 * |log delta| ^ 2))` for
every `c ≤ theta / D`. -/
theorem exp_neg_rate_le_exp_neg_deltaLogSq {delta theta D c r : ℝ}
    (hdelta : 0 < delta) (hlog : Real.log delta ≠ 0) (hD : 0 < D)
    (hr : 1 ≤ r) (htheta : 0 ≤ theta) (hc : c ≤ theta / D) :
    Real.exp (-((|Real.log delta|⁻¹) ^ 2 * theta / (D * delta ^ 2)) * r) ≤
      Real.exp (-c / (delta ^ 2 * |Real.log delta| ^ 2)) := by
  have habs : (0 : ℝ) < |Real.log delta| := abs_pos.2 hlog
  have hden : (0 : ℝ) < delta ^ 2 * |Real.log delta| ^ 2 := by positivity
  refine Real.exp_le_exp.2 ?_
  rw [rate_inv_abs_log_eq delta theta D hdelta.ne' hlog hD.ne', neg_div]
  have hstep : theta / D / (delta ^ 2 * |Real.log delta| ^ 2) ≤
      theta / D / (delta ^ 2 * |Real.log delta| ^ 2) * r := by
    have hnn : (0 : ℝ) ≤ theta / D / (delta ^ 2 * |Real.log delta| ^ 2) := by positivity
    nlinarith
  have hcle : c / (delta ^ 2 * |Real.log delta| ^ 2) ≤
      theta / D / (delta ^ 2 * |Real.log delta| ^ 2) :=
    div_le_div_of_nonneg_right hc hden.le
  linarith

/-- **The packaged form.**  The anchors demand
`M.P.toMeasure bad ≤ ENNReal.ofReal (C * Real.exp (-c / (δ ^ 2 * |log δ| ^ 2)))`;
this converts a proved concentration bound into exactly that. -/
theorem measure_le_ofReal_exp_neg_deltaLogSq {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} {E : Set Omega}
    {delta theta D c r C : ℝ} (hdelta : 0 < delta) (hlog : Real.log delta ≠ 0)
    (hD : 0 < D) (hr : 1 ≤ r) (htheta : 0 ≤ theta) (hc : c ≤ theta / D)
    (hC : 1 ≤ C)
    (hE : mu E ≤ ENNReal.ofReal
      (Real.exp (-((|Real.log delta|⁻¹) ^ 2 * theta / (D * delta ^ 2)) * r))) :
    mu E ≤ ENNReal.ofReal
      (C * Real.exp (-c / (delta ^ 2 * |Real.log delta| ^ 2))) := by
  refine le_trans hE (ENNReal.ofReal_le_ofReal ?_)
  have hshape := exp_neg_rate_le_exp_neg_deltaLogSq hdelta hlog hD hr htheta hc
  have hpos : (0 : ℝ) < Real.exp (-c / (delta ^ 2 * |Real.log delta| ^ 2)) :=
    Real.exp_pos _
  nlinarith

/-! ## 2. The smallness calibration -/

/-- **The calibration.**  For every accuracy `eps > 0` there is a threshold
`c ∈ (0, 1)` below which `delta * |Real.log delta| ≤ eps`.

This is what discharges the smallness hypotheses of the proved concentration
headlines (`M.delta ≤ D⁻¹ * s * Real.sqrt theta`) after the substitution
`s = |Real.log M.delta|⁻¹`: that hypothesis becomes
`M.delta * |Real.log M.delta| ≤ D⁻¹ * Real.sqrt theta`. -/
theorem exists_smallDelta_mul_abs_log_le {eps : ℝ} (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ delta : ℝ, 0 < delta → delta ≤ c →
      delta * |Real.log delta| ≤ eps := by
  have htend : Tendsto (fun x : ℝ => Real.log x * x) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
    have h := _root_.tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
    simpa using h
  have hev : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      dist (Real.log x * x) 0 < eps := Metric.tendsto_nhds.1 htend eps heps
  rw [Filter.eventually_iff, mem_nhdsGT_iff_exists_Ioo_subset] at hev
  obtain ⟨u, hu, hsub⟩ := hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨min (u / 2) (1 / 2), by positivity, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  · intro delta hdelta hle
    have hlt : delta < u := by
      have := le_trans hle (min_le_left (u / 2) (1 / 2))
      linarith
    have hmem : delta ∈ Set.Ioo (0 : ℝ) u := ⟨hdelta, hlt⟩
    have hdist : dist (Real.log delta * delta) 0 < eps := hsub hmem
    rw [Real.dist_eq, sub_zero] at hdist
    have habs : delta * |Real.log delta| = |Real.log delta * delta| := by
      rw [abs_mul, abs_of_pos hdelta]
      ring
    rw [habs]
    exact hdist.le

end

end SubdiffusiveProcess.CoarseGrainingVocab
