module

public import SubdiffusiveProcess.Section10.EndpointPathsScalar

@[expose] public section

open Filter MeasureTheory Topology Set MarkovProcess SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.EndpointPaths

lemma coe_tendsto_nhdsGT_zero :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (NNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht

def oscillationConstant (eta epsilon : ℝ) : ℝ :=
  1 / (2 * ((3 : ℝ) ^ (2 + eta) *
    logScaleConstant eta ^ (1 + epsilon)) ^ (1 / (2 + eta)))

lemma oscillationConstant_pos (eta epsilon : ℝ) (heta : 0 < eta) :
    0 < oscillationConstant eta epsilon := by
  have hB : 0 < logScaleConstant eta := by
    unfold logScaleConstant
    have h : 0 < (2 + eta) * Real.log 3 / 2 :=
      div_pos (mul_pos (by linarith) (Real.log_pos (by norm_num))) (by norm_num)
    positivity
  unfold oscillationConstant
  exact one_div_pos.mpr (mul_pos (by norm_num)
    (Real.rpow_pos_of_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos hB _)) _))

/-- The constant depends only on the two exponents, not on the path or its
finite initial exceptions. -/
theorem oscillation_of_eventual_exits {d : ℕ} (eta epsilon : ℝ)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) (w : DiffusionPath d)
    (hexit : ∀ᶠ k : ℕ in atTop,
      smallExit k w ≤ ENNReal.ofReal (endpoint eta epsilon k)) :
    ∀ᶠ t : ℝ≥0 in 𝓝[>] 0,
      oscillationConstant eta epsilon *
        ((t : ℝ) / Real.log (1 / (t : ℝ)) ^ (1 + epsilon)) ^
          (1 / (2 + eta)) ≤ maximum t w := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hexit
  obtain ⟨delta, B, hdelta, hB, rfl, hbracket⟩ :=
    endpoint_bracket eta epsilon heta hepsilon N
  have hsmall : ∀ᶠ t : ℝ≥0 in 𝓝[>] 0, (t : ℝ) < delta :=
    coe_tendsto_nhdsGT_zero.eventually
      (mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds hdelta))
  filter_upwards [hsmall, self_mem_nhdsWithin] with t ht ht0
  have ht0' : 0 < (t : ℝ) := ht0
  obtain ⟨k, hkN, hkt, hL, _, hbound⟩ := hbracket t ht0' ht
  have hr := radius_le_maximum_of_smallExit_le w k t
    ((hN k hkN).trans (by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hkt))
  have hroot := root_lower_bound (2 + eta) (1 + epsilon) (logScaleConstant eta)
    t ((3 : ℝ) ^ (-(k : ℤ))) (by linarith) hB ht0'
    (lt_of_lt_of_le (by norm_num) hL) (by positivity)
    (by simpa only [rpow_radius] using hbound)
  have hD : 0 < ((3 : ℝ) ^ (2 + eta) * logScaleConstant eta ^ (1 + epsilon)) ^
      (1 / (2 + eta)) := Real.rpow_pos_of_pos
        (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hB _)) _
  apply le_trans _ hr
  unfold oscillationConstant
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hD)).mpr
  convert hroot using 1; field_simp

/-- A scalar ratio form used for both the Brownian comparison and every
forbidden pointwise Hölder exponent. -/
lemma logarithmic_ratio_eq (a b gamma t : ℝ) (_ha : 0 < a) (ht : 0 < t)
    (hL : 0 < Real.log (1 / t)) :
    (t / Real.log (1 / t) ^ b) ^ (1 / a) / t ^ gamma =
      Real.exp ((gamma - 1 / a) * Real.log (1 / t)) /
        Real.log (1 / t) ^ (b / a) := by
  have hLp := Real.rpow_pos_of_pos hL b
  have htp := Real.rpow_pos_of_pos ht gamma
  rw [Real.div_rpow ht.le hLp.le, ← Real.rpow_mul hL.le,
    div_div, mul_comm (Real.log (1 / t) ^ (b * (1 / a))), ← div_div,
    ← Real.rpow_sub ht]
  rw [Real.rpow_def_of_pos ht]
  have hlog : Real.log (1 / t) = -Real.log t := by rw [one_div, Real.log_inv]
  rw [hlog]
  congr 1
  · congr 1
    ring
  · congr 1
    ring

lemma logarithmic_ratio_tendsto (a b gamma : ℝ) (ha : 0 < a)
    (hgamma : 1 / a < gamma) :
    Tendsto (fun t : ℝ≥0 =>
      ((t : ℝ) / Real.log (1 / (t : ℝ)) ^ b) ^ (1 / a) / (t : ℝ) ^ gamma)
      (𝓝[>] 0) atTop := by
  have hL : Tendsto (fun t : ℝ≥0 => Real.log (1 / (t : ℝ))) (𝓝[>] 0) atTop := by
    simpa only [one_div, Function.comp_def] using
      Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp coe_tendsto_nhdsGT_zero)
  have h := (tendsto_exp_mul_div_rpow_atTop (b / a) (gamma - 1 / a)
    (sub_pos.mpr hgamma)).comp hL
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin, hL.eventually (eventually_gt_atTop 0)] with t ht hlog
  exact (logarithmic_ratio_eq a b gamma t ha ht hlog).symm

/-- Divergence actually holds against every time power above the endpoint
exponent. -/
theorem maximum_div_rpow_tendsto {d : ℕ} (eta epsilon : ℝ)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) (w : DiffusionPath d)
    (hexit : ∀ᶠ k : ℕ in atTop,
      smallExit k w ≤ ENNReal.ofReal (endpoint eta epsilon k))
    (gamma : ℝ) (hgamma : 1 / (2 + eta) < gamma) :
    Tendsto (fun t : ℝ≥0 => maximum t w / (t : ℝ) ^ gamma) (𝓝[>] 0) atTop := by
  have hc := oscillationConstant_pos eta epsilon heta
  have h := (logarithmic_ratio_tendsto (2 + eta) (1 + epsilon) gamma
    (by linarith) hgamma).const_mul_atTop hc
  apply tendsto_atTop_mono' _ _ h
  filter_upwards [oscillation_of_eventual_exits eta epsilon heta hepsilon w hexit,
    self_mem_nhdsWithin] with t ht ht0
  rw [← mul_div_assoc]
  gcongr

theorem maximum_div_sqrt_tendsto {d : ℕ} (eta epsilon : ℝ)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) (w : DiffusionPath d)
    (hexit : ∀ᶠ k : ℕ in atTop,
      smallExit k w ≤ ENNReal.ofReal (endpoint eta epsilon k)) :
    Tendsto (fun t : ℝ≥0 => maximum t w / Real.sqrt t) (𝓝[>] 0) atTop := by
  have hgamma : 1 / (2 + eta) < (1 / 2 : ℝ) := by
    apply (div_lt_div_iff₀ (by linarith : 0 < 2 + eta) (by norm_num : (0 : ℝ) < 2)).mpr
    linarith
  simpa only [Real.sqrt_eq_rpow] using
    maximum_div_rpow_tendsto eta epsilon heta hepsilon w hexit (1 / 2) hgamma

/-- A pointwise power bound near zero controls the literal maximum, including
its value at time zero. -/
lemma maximum_isBigO_of_displacement {d : ℕ} (w : DiffusionPath d) (gamma : ℝ)
    (hgamma : 0 ≤ gamma)
    (h : (fun t : ℝ≥0 => euclideanNorm (w t - w 0))
      =O[𝓝[>] 0] (fun t : ℝ≥0 => (t : ℝ) ^ gamma)) :
    (fun t : ℝ≥0 => maximum t w)
      =O[𝓝[>] 0] (fun t : ℝ≥0 => (t : ℝ) ^ gamma) := by
  obtain ⟨C, hC, hbound⟩ := h.exists_nonneg
  have hpoint : ∀ᶠ t : ℝ≥0 in 𝓝[>] 0,
      euclideanNorm (w t - w 0) ≤ C * (t : ℝ) ^ gamma := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] using hbound.bound
  obtain ⟨delta, hdelta, hpoint'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hpoint
  apply Asymptotics.IsBigO.of_bound C
  have hsmall : ∀ᶠ t : ℝ≥0 in 𝓝[>] 0, t ∈ Ioo 0 delta :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨delta, hdelta, subset_rfl⟩
  filter_upwards [hsmall] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (maximum_nonneg w t), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg t) gamma)]
  let : Nonempty (Set.Icc (0 : ℝ≥0) t) := ⟨⟨0, le_rfl, (zero_le : (0 : ℝ≥0) ≤ t)⟩⟩
  apply ciSup_le
  intro s
  by_cases hs : (s : ℝ≥0) = 0
  · simp only [hs, sub_self, euclideanNorm_zero]
    exact mul_nonneg hC (Real.rpow_nonneg t.property _)
  · have hs0 : 0 < (s : ℝ≥0) := lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ s) (Ne.symm hs)
    exact (hpoint' ⟨hs0, s.property.2.trans_lt ht.2⟩).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (NNReal.coe_nonneg _) (by exact_mod_cast s.property.2)
          hgamma) hC)

/-- The pointwise exponent conclusion is expressed by testing the paper's
`O(t^gamma)` condition; no chosen definition of a supremal exponent is needed. -/
theorem holder_exponent_le_of_eventual_exits {d : ℕ} (eta epsilon : ℝ)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) (w : DiffusionPath d)
    (hexit : ∀ᶠ k : ℕ in atTop,
      smallExit k w ≤ ENNReal.ofReal (endpoint eta epsilon k))
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hholder : (fun t : ℝ≥0 => euclideanNorm (w t - w 0))
      =O[𝓝[>] 0] (fun t : ℝ≥0 => (t : ℝ) ^ gamma)) :
    gamma ≤ 1 / (2 + eta) := by
  by_contra hle
  have hgt := lt_of_not_ge hle
  have hdiv := maximum_div_rpow_tendsto eta epsilon heta hepsilon w hexit gamma hgt
  obtain ⟨C, hC⟩ := (maximum_isBigO_of_displacement w gamma hgamma hholder).bound
  have hupper : ∀ᶠ t : ℝ≥0 in 𝓝[>] 0, maximum t w / (t : ℝ) ^ gamma ≤ C := by
    filter_upwards [hC, self_mem_nhdsWithin] with t ht ht0
    have htp : 0 < (t : ℝ) ^ gamma := Real.rpow_pos_of_pos ht0 _
    apply (div_le_iff₀ htp).mpr
    simpa only [Real.norm_eq_abs, abs_of_nonneg (maximum_nonneg w t),
      abs_of_nonneg htp.le] using ht
  obtain ⟨t, ht, htu⟩ := ((hdiv.eventually (eventually_gt_atTop C)).and hupper).exists
  exact ht.not_ge htu

end SubdiffusiveProcess.Section10.EndpointPaths
