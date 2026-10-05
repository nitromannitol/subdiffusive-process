module

public import SubdiffusiveProcess.Section10.EndpointPathsConsequences

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics MarkovProcess
open SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Section10.EndpointPaths
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.LegacyPathsSupNorm

/-- The legacy running maximum in the ambient supremum norm. -/
def maximum {d : ℕ} (t : ℝ≥0) (w : DiffusionPath d) : ℝ :=
  ⨆ s : Set.Icc (0 : ℝ≥0) t, ‖w s - w 0‖

lemma maximum_bddAbove {d : ℕ} (w : DiffusionPath d) (t : ℝ≥0) :
    BddAbove (Set.range (fun s : Set.Icc (0 : ℝ≥0) t => ‖w s - w 0‖)) := by
  exact (isCompact_range (((w.continuous.comp continuous_subtype_val).sub
    continuous_const).norm)).bddAbove

lemma maximum_nonneg {d : ℕ} (w : DiffusionPath d) (t : ℝ≥0) :
    0 ≤ maximum t w :=
  (norm_nonneg _).trans (le_ciSup (maximum_bddAbove w t) ⟨0, le_rfl, (zero_le : (0 : ℝ≥0) ≤ t)⟩)

lemma euclidean_maximum_le {d : ℕ} (w : DiffusionPath d) (t : ℝ≥0) :
    EndpointPaths.maximum t w ≤ (d : ℝ) * maximum t w := by
  let : Nonempty (Set.Icc (0 : ℝ≥0) t) := ⟨⟨0, le_rfl, (zero_le : (0 : ℝ≥0) ≤ t)⟩⟩
  apply ciSup_le
  intro s
  exact (euclideanNorm_le_dimension_mul_norm _).trans
    (mul_le_mul_of_nonneg_left (le_ciSup (maximum_bddAbove w t) s) (Nat.cast_nonneg d))

lemma div_rpow_tendsto {d : ℕ} (hd : 0 < d) (eta epsilon : ℝ)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) (w : DiffusionPath d)
    (hexit : ∀ᶠ k : ℕ in atTop,
      smallExit k w ≤ ENNReal.ofReal (endpoint eta epsilon k))
    (gamma : ℝ) (hgamma : 1 / (2 + eta) < gamma) :
    Tendsto (fun t : ℝ≥0 => maximum t w / (t : ℝ) ^ gamma) (𝓝[>] 0) atTop := by
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have h := (maximum_div_rpow_tendsto eta epsilon heta hepsilon w hexit gamma hgamma).atTop_div_const hd'
  apply tendsto_atTop_mono' _ _ h
  filter_upwards [] with t
  have hb := div_le_div_of_nonneg_right (euclidean_maximum_le w t)
    (Real.rpow_nonneg t.property gamma)
  have hb' := div_le_div_of_nonneg_right hb hd'.le
  simpa only [mul_div_assoc, mul_div_cancel_left₀ _ hd'.ne'] using! hb'

lemma legacy_power_and_sqrt {d : ℕ} (hd : 0 < d) (eta : ℝ) (heta : 0 < eta)
    (w : DiffusionPath d)
    (hexit : ∀ᶠ k : ℕ in atTop,
      smallExit k w ≤ ENNReal.ofReal (endpoint eta 1 k))
    (beta : ℝ) (hbeta : 0 < beta) (hbetaeta : beta < eta) :
    (∀ᶠ t : ℝ≥0 in 𝓝[>] 0,
      (1 / 6 : ℝ) * (t : ℝ) ^ (1 / (2 + beta)) ≤ maximum t w) ∧
    Tendsto (fun t : ℝ≥0 => maximum t w / Real.sqrt t) (𝓝[>] 0) atTop := by
  have hg : 1 / (2 + eta) < 1 / (2 + beta) := by
    exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  refine ⟨?_, ?_⟩
  · have h := (div_rpow_tendsto hd eta 1 heta one_pos w hexit _ hg).eventually
      (eventually_ge_atTop (1 / 6 : ℝ))
    filter_upwards [h, self_mem_nhdsWithin] with t ht ht0
    exact (le_div_iff₀ (Real.rpow_pos_of_pos ht0 _)).mp ht
  · have hg' : 1 / (2 + eta) < (1 / 2 : ℝ) :=
      one_div_lt_one_div_of_lt (by norm_num) (by linarith)
    simpa only [Real.sqrt_eq_rpow] using
      div_rpow_tendsto hd eta 1 heta one_pos w hexit (1 / 2) hg'

lemma holder_exponent_le {d : ℕ} (eta : ℝ) (heta : 0 < eta) (w : DiffusionPath d)
    (hexit : ∀ᶠ k : ℕ in atTop,
      smallExit k w ≤ ENNReal.ofReal (endpoint eta 1 k))
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hholder : (fun t : ℝ≥0 => ‖w t - w 0‖)
      =O[𝓝[>] 0] (fun t : ℝ≥0 => (t : ℝ) ^ gamma)) :
    gamma ≤ 1 / (2 + eta) := by
  have hnorm : (fun t : ℝ≥0 => euclideanNorm (w t - w 0))
      =O[𝓝[>] 0] (fun t : ℝ≥0 => ‖w t - w 0‖) := by
    apply IsBigO.of_bound (d : ℝ)
    filter_upwards [] with t
    simpa only [Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _),
      abs_of_nonneg (norm_nonneg _)] using euclideanNorm_le_dimension_mul_norm (w t - w 0)
  exact holder_exponent_le_of_eventual_exits eta 1 heta one_pos w hexit gamma hgamma
    (hnorm.trans hholder)

lemma moment_lower {d : ℕ} (hd : 0 < d) (P : Measure (DiffusionPath d))
    (p cp t eta : ℝ) (hp : 0 < p) (htime : ℝ≥0)
    (hbound : ENNReal.ofReal (cp * t ^ (p / (2 + eta))) ≤
      ∫⁻ w, ENNReal.ofReal (EndpointPaths.maximum htime w ^ p) ∂P) :
    ENNReal.ofReal ((cp * (d : ℝ) ^ (-p)) * t ^ (p / (2 + eta))) ≤
      ∫⁻ w, ENNReal.ofReal (maximum htime w ^ p) ∂P := by
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hdp : 0 < (d : ℝ) ^ (-p) := Real.rpow_pos_of_pos hd' _
  have hpoint : ∀ w : DiffusionPath d,
      (d : ℝ) ^ (-p) * EndpointPaths.maximum htime w ^ p ≤ maximum htime w ^ p := by
    intro w
    have h := Real.rpow_le_rpow (EndpointPaths.maximum_nonneg w htime)
      (euclidean_maximum_le w htime) hp.le
    have h' := mul_le_mul_of_nonneg_left h hdp.le
    rw [Real.mul_rpow hd'.le (maximum_nonneg w htime)] at h'
    simpa only [← mul_assoc, ← Real.rpow_add hd', neg_add_cancel, Real.rpow_zero,
      one_mul] using h'
  calc
    ENNReal.ofReal ((cp * (d : ℝ) ^ (-p)) * t ^ (p / (2 + eta))) =
        ENNReal.ofReal ((d : ℝ) ^ (-p)) *
          ENNReal.ofReal (cp * t ^ (p / (2 + eta))) := by
      rw [← ENNReal.ofReal_mul hdp.le]
      congr 1
      ring
    _ ≤ ENNReal.ofReal ((d : ℝ) ^ (-p)) *
        (∫⁻ w, ENNReal.ofReal (EndpointPaths.maximum htime w ^ p) ∂P) :=
      mul_le_mul' le_rfl hbound
    _ = ∫⁻ w, ENNReal.ofReal ((d : ℝ) ^ (-p) *
          EndpointPaths.maximum htime w ^ p) ∂P := by
      simp only [ENNReal.ofReal_mul hdp.le]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := lintegral_mono (fun w => ENNReal.ofReal_le_ofReal (hpoint w))

end SubdiffusiveProcess.Section10.LegacyPathsSupNorm
