module

public import SubdiffusiveProcess.Section10.EndpointPathsConsequences

@[expose] public section

open Filter MeasureTheory Topology Set SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.EndpointPaths

/-- The elementary probability/moment step requires no Markov property of the
path law, and no measurability assumption on the maximum. -/
lemma maximal_moment_lower_at_scale {d : ℕ} (P : Measure (DiffusionPath d))
    [IsProbabilityMeasure P] (k : ℕ) (t : ℝ≥0) (ht : 0 < t)
    (p : ℝ) (hp : 0 < p) (hmeas : Measurable (smallExit (d := d) k))
    (hmean : (∫⁻ w, smallExit k w ∂P) ≤ ENNReal.ofReal ((t : ℝ) / 2)) :
    ENNReal.ofReal (((3 : ℝ) ^ (-(k : ℤ)) / 2) ^ p / 2) ≤
      ∫⁻ w, ENNReal.ofReal (maximum t w ^ p) ∂P := by
  let E := {w : DiffusionPath d | smallExit k w ≤ (t : ℝ≥0∞)}
  have hE : MeasurableSet E := measurableSet_le hmeas measurable_const
  have hmarkov := meas_ge_le_lintegral_div (μ := P) (f := smallExit k)
    hmeas.aemeasurable (ENNReal.coe_ne_zero.mpr ht.ne') ENNReal.coe_ne_top
  have hcomp : P Eᶜ ≤ (1 / 2 : ℝ≥0∞) := by
    calc P Eᶜ ≤ P {w | (t : ℝ≥0∞) ≤ smallExit k w} :=
        measure_mono (fun w hw =>
          (lt_of_not_ge (show ¬ smallExit k w ≤ (t : ℝ≥0∞) from hw)).le)
      _ ≤ (∫⁻ w, smallExit k w ∂P) / (t : ℝ≥0∞) := hmarkov
      _ ≤ ENNReal.ofReal ((t : ℝ) / 2) / (t : ℝ≥0∞) :=
        ENNReal.div_le_div_right hmean _
      _ = 1 / 2 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
          ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_ofNat]
        rw [ENNReal.div_eq_inv_mul, div_eq_mul_inv,
          ENNReal.inv_mul_cancel_left (ENNReal.coe_ne_zero.mpr ht.ne') ENNReal.coe_ne_top]
        exact (one_div 2).symm
  have hprob : (1 / 2 : ℝ≥0∞) ≤ P E := by
    have hsum : P E + P Eᶜ = 1 := by rw [measure_add_measure_compl hE, measure_univ]
    have h : (1 : ℝ≥0∞) ≤ P E + 1 / 2 := by
      calc (1 : ℝ≥0∞) = P E + P Eᶜ := hsum.symm
        _ ≤ P E + 1 / 2 := add_le_add le_rfl hcomp
    have h' := tsub_le_iff_right.mpr h
    norm_num at h' ⊢
    exact h'
  let R := (3 : ℝ) ^ (-(k : ℤ)) / 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  calc ENNReal.ofReal (R ^ p / 2) = ENNReal.ofReal (R ^ p) * (1 / 2 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
          ENNReal.ofReal_ofNat, div_eq_mul_inv, one_div]
    _ ≤ ENNReal.ofReal (R ^ p) * P E := mul_le_mul_right hprob _
    _ = ∫⁻ w, E.indicator (fun _ => ENNReal.ofReal (R ^ p)) w ∂P := by
      rw [lintegral_indicator hE, setLIntegral_const]
    _ ≤ ∫⁻ w, ENNReal.ofReal (maximum t w ^ p) ∂P := by
      apply lintegral_mono
      intro w
      by_cases hw : w ∈ E
      · rw [Set.indicator_of_mem hw]
        exact ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow hR (radius_le_maximum_of_smallExit_le w k t hw) hp.le)
      · rw [Set.indicator_of_notMem hw]
        exact zero_le

def momentRadiusConstant (C eta : ℝ) : ℝ :=
  (1 / (2 * C * (3 : ℝ) ^ (2 + eta))) ^ (1 / (2 + eta)) / 2

lemma momentRadiusConstant_pos (C eta : ℝ) (hC : 0 < C) :
    0 < momentRadiusConstant C eta := by
  unfold momentRadiusConstant
  exact div_pos (Real.rpow_pos_of_pos (one_div_pos.mpr
    (mul_pos (mul_pos (by norm_num) hC) (Real.rpow_pos_of_pos (by norm_num) _))) _)
    (by norm_num)

/-- Smallest geometric scale. This includes all `0 < t ≤ 1` and the initial
scale `k = 0`, whose exclusion follows from `C ≥ 1`. -/
lemma mean_exit_scale (C eta t : ℝ) (hC : 1 ≤ C) (heta : 0 < eta)
    (ht : 0 < t) (ht1 : t ≤ 1) : ∃ k : ℕ,
      C * (3 : ℝ) ^ (-((2 + eta) * k)) ≤ t / 2 ∧
      momentRadiusConstant C eta * t ^ (1 / (2 + eta)) ≤
        (3 : ℝ) ^ (-(k : ℤ)) / 2 := by
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have ha : 0 < 2 + eta := by linarith
  have hlim : Tendsto (fun k : ℕ => C * (3 : ℝ) ^ (-((2 + eta) * k)))
      atTop (𝓝 0) := by
    simpa only [endpoint, add_neg_cancel, Real.rpow_zero, one_mul, mul_zero] using
      (endpoint_tendsto_zero eta (-1) heta).const_mul C
  have hex : ∃ k : ℕ, C * (3 : ℝ) ^ (-((2 + eta) * k)) ≤ t / 2 :=
    (((hlim.eventually (eventually_lt_nhds (half_pos ht))).mono (fun _ h => h.le)).exists)
  let k := Nat.find hex
  have hk : C * (3 : ℝ) ^ (-((2 + eta) * (k : ℝ))) ≤ t / 2 := Nat.find_spec hex
  have hk0 : 0 < k := by
    by_contra h
    have heq : k = 0 := Nat.eq_zero_of_not_pos h
    rw [heq] at hk
    norm_num at hk
    linarith
  have hj : t / 2 < C * (3 : ℝ) ^ (-((2 + eta) * ((k - 1 : ℕ) : ℝ))) :=
    lt_of_not_ge (Nat.find_min hex (show k - 1 < k by omega))
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ k by omega))
    linarith
  have hgeom : (3 : ℝ) ^ (-((2 + eta) * ((k - 1 : ℕ) : ℝ))) =
      (3 : ℝ) ^ (2 + eta) * ((3 : ℝ) ^ (-(k : ℤ))) ^ (2 + eta) := by
    rw [rpow_radius, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    rw [hkcast]
    ring
  have hD : 0 < 2 * C * (3 : ℝ) ^ (2 + eta) :=
    mul_pos (mul_pos (by norm_num) hC0) (Real.rpow_pos_of_pos (by norm_num) _)
  have hR : 0 ≤ (3 : ℝ) ^ (-(k : ℤ)) := by positivity
  have hpow : t / (2 * C * (3 : ℝ) ^ (2 + eta)) ≤
      ((3 : ℝ) ^ (-(k : ℤ))) ^ (2 + eta) := by
    apply (div_le_iff₀ hD).mpr
    rw [hgeom] at hj
    nlinarith only [hj]
  have hroot : (t / (2 * C * (3 : ℝ) ^ (2 + eta))) ^ (1 / (2 + eta)) ≤
      (3 : ℝ) ^ (-(k : ℤ)) := by
    simpa only [one_div] using
      (Real.rpow_inv_le_iff_of_pos (div_pos ht hD).le hR ha).mpr hpow
  refine ⟨k, hk, ?_⟩
  have hfactor : (t / (2 * C * (3 : ℝ) ^ (2 + eta))) ^ (1 / (2 + eta)) =
      (1 / (2 * C * (3 : ℝ) ^ (2 + eta))) ^ (1 / (2 + eta)) *
        t ^ (1 / (2 + eta)) := by
    rw [div_eq_mul_inv, ← one_div, Real.mul_rpow ht.le (one_div_pos.mpr hD).le,
      mul_comm]
  rw [hfactor] at hroot
  unfold momentRadiusConstant
  calc _ = ((1 / (2 * C * (3 : ℝ) ^ (2 + eta))) ^ (1 / (2 + eta)) *
      t ^ (1 / (2 + eta))) / 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hroot (by norm_num)

/-- Conditional moment consequence of a mean exit estimate. No physical mean
exit theorem is proved or assumed as an axiom. -/
theorem maximal_moment_lower_of_mean_exits {d : ℕ} (P : Measure (DiffusionPath d))
    [IsProbabilityMeasure P] (C eta : ℝ) (hC : 1 ≤ C) (heta : 0 < eta)
    (hmeas : ∀ k : ℕ, Measurable (smallExit (d := d) k))
    (hmean : ∀ k : ℕ, (∫⁻ w, smallExit k w ∂P) ≤
      ENNReal.ofReal (C * (3 : ℝ) ^ (-((2 + eta) * k))))
    (p : ℝ) (hp : 0 < p) (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1) :
    ENNReal.ofReal (momentRadiusConstant C eta ^ p / 2 * (t : ℝ) ^ (p / (2 + eta))) ≤
      ∫⁻ w, ENNReal.ofReal (maximum t w ^ p) ∂P := by
  obtain ⟨k, hkmean, hkradius⟩ := mean_exit_scale C eta t hC heta ht (by exact_mod_cast ht1)
  have hlow := maximal_moment_lower_at_scale P k t ht p hp (hmeas k)
    ((hmean k).trans (ENNReal.ofReal_le_ofReal hkmean))
  apply le_trans _ hlow
  apply ENNReal.ofReal_le_ofReal
  have hrad := Real.rpow_le_rpow
    (mul_nonneg (momentRadiusConstant_pos C eta (by linarith)).le
      (Real.rpow_nonneg t.property _)) hkradius hp.le
  rw [Real.mul_rpow (momentRadiusConstant_pos C eta (by linarith)).le
    (Real.rpow_nonneg t.property _), ← Real.rpow_mul t.property] at hrad
  rw [show 1 / (2 + eta) * p = p / (2 + eta) by ring] at hrad
  calc _ = (momentRadiusConstant C eta ^ p * (t : ℝ) ^ (p / (2 + eta))) / 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hrad (by norm_num)

end SubdiffusiveProcess.Section10.EndpointPaths
