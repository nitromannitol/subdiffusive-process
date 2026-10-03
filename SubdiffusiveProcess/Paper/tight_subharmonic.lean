module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.Paper.tight_static_estimates
public import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitEstimates
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserPowerTests
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserLpEndpoint

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper




section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

variable {d : ℕ}

lemma aux_tight_subharmonic_vol_cb (x : Fin d → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x r) = ENNReal.ofReal ((2 * r) ^ d) := by
  rw [Real.volume_pi_closedBall x hr, Fintype.card_fin]

lemma aux_tight_subharmonic_vol_cb_pos (x : Fin d → ℝ) {r : ℝ} (hr : 0 < r) : volume (closedBall x r) ≠ 0 := by
  rw [aux_tight_subharmonic_vol_cb x hr.le]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

lemma aux_tight_subharmonic_vol_cb_fin (x : Fin d → ℝ) {r : ℝ} (hr : 0 ≤ r) : volume (closedBall x r) ≠ ∞ := by
  rw [aux_tight_subharmonic_vol_cb x hr]; exact ENNReal.ofReal_ne_top

/-- `‖⨍_s f‖ₑ ≤ μ(s)⁻¹ ∫⁻_s ‖f‖ₑ` for a set of positive finite measure. -/
lemma aux_tight_subharmonic_enorm_setAverage_le {f : (Fin d → ℝ) → ℝ} {s : Set (Fin d → ℝ)}
    (hs0 : volume s ≠ 0) (hs : volume s ≠ ∞) :
    ‖⨍ y in s, f y‖ₑ ≤ (volume s)⁻¹ * ∫⁻ y in s, ‖f y‖ₑ := by
  rw [setAverage_eq, enorm_smul]
  gcongr
  · rw [Real.enorm_eq_ofReal_abs, abs_inv, abs_of_nonneg measureReal_nonneg, measureReal_def,
      ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hs0 hs), ENNReal.ofReal_toReal hs]
  · exact enorm_integral_le_lintegral_enorm _

/-- Difference of the averages over the concentric closed balls of radii `r/2` and `r`. -/
lemma aux_tight_subharmonic_avg_diff_le (w : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) {r : ℝ} (hr : 0 < r)
    (hint : IntegrableOn w (closedBall x r)) :
    ENNReal.ofReal |(⨍ y in closedBall x (r / 2), w y) - ⨍ y in closedBall x r, w y| ≤
      (volume (closedBall x (r / 2)))⁻¹ * (volume (closedBall x r))⁻¹ *
        ∫⁻ y in closedBall x r, ∫⁻ z in closedBall x r, ENNReal.ofReal |w y - w z| := by
  set B := closedBall x r with hB
  set B' := closedBall x (r / 2) with hB'
  have hBB : B' ⊆ B := closedBall_subset_closedBall (by linarith)
  have h0 : volume B ≠ 0 := aux_tight_subharmonic_vol_cb_pos x hr
  have hf : volume B ≠ ∞ := aux_tight_subharmonic_vol_cb_fin x hr.le
  have h0' : volume B' ≠ 0 := aux_tight_subharmonic_vol_cb_pos x (by linarith)
  have hf' : volume B' ≠ ∞ := aux_tight_subharmonic_vol_cb_fin x (by linarith)
  set a := ⨍ y in B, w y with ha
  have hint' : IntegrableOn w B' := hint.mono_set hBB
  haveI : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hf.lt_top⟩
  haveI : IsFiniteMeasure (volume.restrict B') := ⟨by simpa using hf'.lt_top⟩
  -- `A' - a` is the average over `B'` of `w - a`
  have hdiff : (⨍ y in B', w y) - a = ⨍ y in B', (w y - a) := by
    rw [setAverage_eq, setAverage_eq, integral_sub hint' (integrable_const a),
      setIntegral_const, smul_sub, smul_smul]
    rw [inv_mul_cancel₀ (by rw [measureReal_def]; exact (ENNReal.toReal_pos h0' hf').ne'),
      one_smul, smul_eq_mul]
  -- `w y - a` is the average over `B` of `w y - w z`
  have hpt : ∀ y, w y - a = ⨍ z in B, (w y - w z) := by
    intro y
    rw [setAverage_eq, integral_sub (integrable_const (w y)) hint,
      setIntegral_const, smul_sub, smul_smul]
    rw [inv_mul_cancel₀ (by rw [measureReal_def]; exact (ENNReal.toReal_pos h0 hf).ne'),
      one_smul, ha, setAverage_eq]
  calc ENNReal.ofReal |(⨍ y in B', w y) - a|
      = ‖⨍ y in B', (w y - a)‖ₑ := by rw [hdiff, Real.enorm_eq_ofReal_abs]
    _ ≤ (volume B')⁻¹ * ∫⁻ y in B', ‖w y - a‖ₑ := aux_tight_subharmonic_enorm_setAverage_le h0' hf'
    _ ≤ (volume B')⁻¹ * ∫⁻ y in B', (volume B)⁻¹ * ∫⁻ z in B, ‖w y - w z‖ₑ := by
        gcongr with y
        rw [hpt y]
        exact aux_tight_subharmonic_enorm_setAverage_le h0 hf
    _ ≤ (volume B')⁻¹ * ∫⁻ y in B, (volume B)⁻¹ * ∫⁻ z in B, ‖w y - w z‖ₑ := by
        gcongr
    _ = (volume B')⁻¹ * (volume B)⁻¹ *
          ∫⁻ y in B, ∫⁻ z in B, ENNReal.ofReal |w y - w z| := by
        rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 h0), mul_assoc]
        simp only [Real.enorm_eq_ofReal_abs]

/-- `(v y - v z)² ≤ (2r)^{d+2t} × kernel` whenever `‖y - z‖ ≤ 2r`. -/
lemma aux_tight_subharmonic_sq_le_kernel (a b : Fin d → ℝ) (u : ℝ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hab : ‖a - b‖ ≤ 2 * r) :
    ENNReal.ofReal (u ^ 2) ≤ ENNReal.ofReal ((2 * r) ^ ((d : ℝ) + 2 * t)) *
      (ENNReal.ofReal (u ^ 2) / ENNReal.ofReal (‖a - b‖ ^ ((d : ℝ) + 2 * t))) := by
  have hs : 0 < (d : ℝ) + 2 * t := by positivity
  rcases (norm_nonneg (a - b)).lt_or_eq with hpos | hzero
  · have hm : 0 < ‖a - b‖ ^ ((d : ℝ) + 2 * t) := Real.rpow_pos_of_pos hpos _
    have hM : ‖a - b‖ ^ ((d : ℝ) + 2 * t) ≤ (2 * r) ^ ((d : ℝ) + 2 * t) :=
      Real.rpow_le_rpow (norm_nonneg _) hab hs.le
    rw [← ENNReal.ofReal_div_of_pos hm, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_div_assoc', le_div_iff₀ hm]
    calc u ^ 2 * ‖a - b‖ ^ ((d : ℝ) + 2 * t) ≤ u ^ 2 * (2 * r) ^ ((d : ℝ) + 2 * t) :=
          mul_le_mul_of_nonneg_left hM (sq_nonneg u)
      _ = (2 * r) ^ ((d : ℝ) + 2 * t) * u ^ 2 := mul_comm _ _
  · rw [← hzero, Real.zero_rpow hs.ne', ENNReal.ofReal_zero]
    rcases (sq_nonneg u).lt_or_eq with hu | hu
    · rw [ENNReal.div_zero (ENNReal.ofReal_pos.2 hu).ne', ENNReal.mul_top
        (ENNReal.ofReal_pos.2 (by positivity)).ne']
      exact le_top
    · rw [← hu]; simp

/-- Cauchy–Schwarz on `B × B`: `∫∫_{B×B} f ≤ |B| (∫∫_{B×B} f²)^{1/2}`. -/
lemma aux_tight_subharmonic_double_cs (B : Set (Fin d → ℝ)) (hBf : volume B ≠ ∞)
    (f : (Fin d → ℝ) → (Fin d → ℝ) → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) :
    ∫⁻ y in B, ∫⁻ z in B, f y z ≤
      volume B * (∫⁻ y in B, ∫⁻ z in B, f y z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  set μB := volume.restrict B with hμB
  haveI : IsFiniteMeasure μB := ⟨by simpa [μB] using hBf.lt_top⟩
  have hf2 : Measurable (Function.uncurry fun y z ↦ f y z ^ (2 : ℝ)) :=
    hf.pow_const _
  rw [lintegral_lintegral hf.aemeasurable, lintegral_lintegral hf2.aemeasurable]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (μB.prod μB) Real.HolderConjugate.two_two
    hf.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have hone : (∫⁻ _ : (Fin d → ℝ) × (Fin d → ℝ), (1 : ℝ≥0∞) ^ (2 : ℝ) ∂(μB.prod μB)) ^
      (1 / 2 : ℝ) = volume B := by
    rw [ENNReal.one_rpow, lintegral_const, one_mul, ← Set.univ_prod_univ, Measure.prod_prod,
      hμB, Measure.restrict_apply_univ, ← pow_two, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp only [Pi.mul_apply, mul_one, Function.uncurry_apply_pair] at hH
  rw [hone] at hH
  rw [mul_comm]
  exact hH

/-- **Ball increment bound**: for `closedBall x r` of finite energy,
`|A(x, r/2) - A(x, r)| ≤ (r^d)⁻¹ (2r)^{(d+2t)/2} S(x,r)^{1/2}`. -/
lemma aux_tight_subharmonic_incr_le (w : (Fin d → ℝ) → ℝ) (hw : Measurable w) (x : Fin d → ℝ) {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hint : IntegrableOn w (closedBall x r)) :
    ENNReal.ofReal |(⨍ y in closedBall x (r / 2), w y) - ⨍ y in closedBall x r, w y| ≤
      ENNReal.ofReal ((r ^ d)⁻¹ * (2 * r) ^ (((d : ℝ) + 2 * t) / 2)) *
        (∫⁻ y in closedBall x r, ∫⁻ z in closedBall x r,
          ENNReal.ofReal ((w y - w z) ^ 2) /
            ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 2 * t))) ^ (1 / 2 : ℝ) := by
  set B := closedBall x r with hB
  have hBf : volume B ≠ ∞ := aux_tight_subharmonic_vol_cb_fin x hr.le
  have hB0 : volume B ≠ 0 := aux_tight_subharmonic_vol_cb_pos x hr
  have hmeas : Measurable (Function.uncurry fun y z : Fin d → ℝ ↦ ENNReal.ofReal |w y - w z|) :=
    ENNReal.measurable_ofReal.comp
      ((hw.comp measurable_fst).sub (hw.comp measurable_snd)).abs
  have h1 := aux_tight_subharmonic_avg_diff_le w x hr hint
  have h2 := aux_tight_subharmonic_double_cs B hBf _ hmeas
  have hsq : ∀ y z : Fin d → ℝ, ENNReal.ofReal |w y - w z| ^ (2 : ℝ) =
      ENNReal.ofReal ((w y - w z) ^ 2) := by
    intro y z
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  simp only [hsq] at h2
  -- kernel comparison on `B × B`
  have h3 : (∫⁻ y in B, ∫⁻ z in B, ENNReal.ofReal ((w y - w z) ^ 2)) ≤
      ENNReal.ofReal ((2 * r) ^ ((d : ℝ) + 2 * t)) *
        ∫⁻ y in B, ∫⁻ z in B, ENNReal.ofReal ((w y - w z) ^ 2) /
          ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 2 * t)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_closedBall fun y hy ↦ ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_closedBall fun z hz ↦ ?_
    apply aux_tight_subharmonic_sq_le_kernel y z _ hr ht
    calc ‖y - z‖ = dist y z := (dist_eq_norm y z).symm
      _ ≤ dist y x + dist z x := dist_triangle_right y z x
      _ ≤ r + r := add_le_add (mem_closedBall.1 hy) (mem_closedBall.1 hz)
      _ = 2 * r := by ring
  have hV' : volume (closedBall x (r / 2)) = ENNReal.ofReal (r ^ d) := by
    rw [aux_tight_subharmonic_vol_cb x (by linarith)]; ring_nf
  calc ENNReal.ofReal |(⨍ y in closedBall x (r / 2), w y) - ⨍ y in B, w y|
      ≤ (volume (closedBall x (r / 2)))⁻¹ * (volume B)⁻¹ *
          ∫⁻ y in B, ∫⁻ z in B, ENNReal.ofReal |w y - w z| := h1
    _ ≤ (volume (closedBall x (r / 2)))⁻¹ * (volume B)⁻¹ *
          (volume B * (∫⁻ y in B, ∫⁻ z in B, ENNReal.ofReal ((w y - w z) ^ 2)) ^
            (1 / 2 : ℝ)) := by gcongr
    _ = (volume (closedBall x (r / 2)))⁻¹ *
          (∫⁻ y in B, ∫⁻ z in B, ENNReal.ofReal ((w y - w z) ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [← mul_assoc, mul_assoc _ (volume B)⁻¹, ENNReal.inv_mul_cancel hB0 hBf, mul_one]
    _ ≤ (volume (closedBall x (r / 2)))⁻¹ *
          (ENNReal.ofReal ((2 * r) ^ ((d : ℝ) + 2 * t)) *
            ∫⁻ y in B, ∫⁻ z in B, ENNReal.ofReal ((w y - w z) ^ 2) /
              ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 2 * t))) ^ (1 / 2 : ℝ) := by gcongr
    _ = ENNReal.ofReal ((r ^ d)⁻¹ * (2 * r) ^ (((d : ℝ) + 2 * t) / 2)) *
          (∫⁻ y in B, ∫⁻ z in B, ENNReal.ofReal ((w y - w z) ^ 2) /
            ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 2 * t))) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← mul_assoc, hV',
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← Real.rpow_mul (by positivity)]
        congr 3
        ring

/-- The average over `closedBall x r` is measurable in the centre `x`. -/
lemma aux_tight_subharmonic_meas_avg (v : (Fin d → ℝ) → ℝ) (hv : Measurable v) (r : ℝ) :
    Measurable (fun x : Fin d → ℝ ↦ ⨍ y in closedBall x r, v y) := by
  have hS : MeasurableSet {p : (Fin d → ℝ) × (Fin d → ℝ) | dist p.2 p.1 ≤ r} :=
    measurableSet_le (continuous_snd.dist continuous_fst).measurable measurable_const
  have hF : StronglyMeasurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) ↦
      (closedBall p.1 r).indicator v p.2) := by
    have : (fun p : (Fin d → ℝ) × (Fin d → ℝ) ↦ (closedBall p.1 r).indicator v p.2) =
        {p : (Fin d → ℝ) × (Fin d → ℝ) | dist p.2 p.1 ≤ r}.indicator (fun p ↦ v p.2) := by
      funext p; simp [Set.indicator, mem_closedBall]
    rw [this]
    exact ((hv.comp measurable_snd).indicator hS).stronglyMeasurable
  have hI := hF.integral_prod_right' (ν := (volume : Measure (Fin d → ℝ)))
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ x : Fin d → ℝ, volume.real (closedBall x r) = c := by
    rcases le_or_gt 0 r with hr | hr
    · exact ⟨(2 * r) ^ d, fun x ↦ by
        rw [measureReal_def, aux_tight_subharmonic_vol_cb x hr, ENNReal.toReal_ofReal (by positivity)]⟩
    · exact ⟨0, fun x ↦ by rw [closedBall_eq_empty.2 hr]; simp⟩
  have heq : (fun x : Fin d → ℝ ↦ ⨍ y in closedBall x r, v y) =
      fun x ↦ c⁻¹ * ∫ y, (closedBall x r).indicator v y := by
    funext x; rw [setAverage_eq, integral_indicator measurableSet_closedBall, hc, smul_eq_mul]
  rw [heq]
  exact hI.measurable.const_mul _

/-- **Fubini mass step**: `∫ S(x, r) dν(x) ≤ M ∫_U ∫_U k` when `ν(closedBall y r) ≤ M` on `U`. -/
lemma aux_tight_subharmonic_fubini_mass (U : Set (Fin d → ℝ)) (hU : MeasurableSet U) (ν : Measure (Fin d → ℝ))
    [IsFiniteMeasure ν] (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ≥0∞)
    (hk : Measurable (Function.uncurry k)) {r : ℝ} (M : ℝ≥0∞)
    (hmass : ∀ y ∈ U, ν (closedBall y r) ≤ M)
    (hsupp : ∀ᵐ x ∂ν, closedBall x r ⊆ U) :
    ∫⁻ x, (∫⁻ y in closedBall x r, ∫⁻ z in closedBall x r, k y z) ∂ν ≤
      M * ∫⁻ y in U, ∫⁻ z in U, k y z := by
  set G : (Fin d → ℝ) → ℝ≥0∞ := fun y ↦ ∫⁻ z in U, k y z with hG
  have hGm : Measurable G := hk.lintegral_prod_right'
  have hS : MeasurableSet {p : (Fin d → ℝ) × (Fin d → ℝ) | dist p.2 p.1 ≤ r} :=
    measurableSet_le (continuous_snd.dist continuous_fst).measurable measurable_const
  have step1 : ∀ᵐ x ∂ν, (∫⁻ y in closedBall x r, ∫⁻ z in closedBall x r, k y z) ≤
      ∫⁻ y in U, (closedBall x r).indicator G y := by
    filter_upwards [hsupp] with x hx
    calc (∫⁻ y in closedBall x r, ∫⁻ z in closedBall x r, k y z)
        ≤ ∫⁻ y in closedBall x r, G y := by
          gcongr with y
          exact lintegral_mono_set hx
      _ = ∫⁻ y in U, (closedBall x r).indicator G y := by
          rw [lintegral_indicator measurableSet_closedBall, Measure.restrict_restrict
            measurableSet_closedBall, Set.inter_eq_left.2 hx]
  have hjoint : Measurable (Function.uncurry fun (x y : Fin d → ℝ) ↦
      (closedBall x r).indicator G y) := by
    have : (Function.uncurry fun (x y : Fin d → ℝ) ↦ (closedBall x r).indicator G y) =
        {p : (Fin d → ℝ) × (Fin d → ℝ) | dist p.2 p.1 ≤ r}.indicator (fun p ↦ G p.2) := by
      funext p; simp [Set.indicator, mem_closedBall, Function.uncurry]
    rw [this]
    exact (hGm.comp measurable_snd).indicator hS
  refine (lintegral_mono_ae step1).trans ?_
  rw [lintegral_lintegral_swap (μ := ν) (ν := volume.restrict U) hjoint.aemeasurable]
  calc ∫⁻ y in U, ∫⁻ x, (closedBall x r).indicator G y ∂ν
      = ∫⁻ y in U, G y * ν (closedBall y r) := by
        refine setLIntegral_congr_fun hU (fun y _ ↦ ?_)
        have : (fun x : Fin d → ℝ ↦ (closedBall x r).indicator G y) =
            (closedBall y r).indicator (fun _ ↦ G y) := by
          funext x; simp [Set.indicator, mem_closedBall, dist_comm]
        simp only [this, lintegral_indicator_const measurableSet_closedBall]
    _ ≤ ∫⁻ y in U, G y * M := by
        refine setLIntegral_mono' hU fun y hy ↦ ?_
        gcongr
        exact hmass y hy
    _ = M * ∫⁻ y in U, ∫⁻ z in U, k y z := by
        rw [lintegral_mul_const M hGm, mul_comm]

/-- The kernel `(v y - v z)² / ‖y - z‖^{s}` is measurable. -/
lemma aux_tight_subharmonic_meas_kernel (v : (Fin d → ℝ) → ℝ) (hv : Measurable v) (s : ℝ) :
    Measurable (Function.uncurry fun y z : Fin d → ℝ ↦
      ENNReal.ofReal ((v y - v z) ^ 2) / ENNReal.ofReal (‖y - z‖ ^ s)) := by
  apply Measurable.div
  · exact ENNReal.measurable_ofReal.comp
      (((hv.comp measurable_fst).sub (hv.comp measurable_snd)).pow_const 2)
  · exact ENNReal.measurable_ofReal.comp
      ((continuous_fst.sub continuous_snd).norm.measurable.pow_const s)

/-- **Per-scale `L^p(ν)` bound** for the increment of ball averages. -/
lemma aux_tight_subharmonic_gk_bound (U : Set (Fin d → ℝ)) (hU : MeasurableSet U) (ν : Measure (Fin d → ℝ))
    [IsFiniteMeasure ν] (v : (Fin d → ℝ) → ℝ) (hv : Measurable v)
    (hvU : MemLp v 2 (volume.restrict U)) {ρ t p : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (hp : 2 ≤ p)
    (M : ℝ≥0∞) (hmass : ∀ y ∈ U, ν (closedBall y ρ) ≤ M)
    (hsupp : ∀ᵐ x ∂ν, closedBall x ρ ⊆ U)
    (hGU : (∫⁻ y in U, ∫⁻ z in U, ENNReal.ofReal ((v y - v z) ^ 2) /
        ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 2 * t))) ≠ ⊤) :
    eLpNorm (fun x ↦ (⨍ y in closedBall x (ρ / 2), v y) - ⨍ y in closedBall x ρ, v y)
        (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal ((ρ ^ d)⁻¹ * (2 * ρ) ^ (((d : ℝ) + 2 * t) / 2)) * M ^ (1 / p) *
        (∫⁻ y in U, ∫⁻ z in U, ENNReal.ofReal ((v y - v z) ^ 2) /
          ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 2 * t))) ^ (1 / 2 : ℝ) := by
  set c := ENNReal.ofReal ((ρ ^ d)⁻¹ * (2 * ρ) ^ (((d : ℝ) + 2 * t) / 2)) with hc
  set k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ≥0∞ := fun y z ↦
    ENNReal.ofReal ((v y - v z) ^ 2) / ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 2 * t)) with hk
  set GU := ∫⁻ y in U, ∫⁻ z in U, k y z with hGUdef
  have hp0 : 0 < p := by linarith
  have ha : 0 ≤ (p - 2) / 2 := by linarith
  have hkm : Measurable (Function.uncurry k) := aux_tight_subharmonic_meas_kernel v hv _
  -- pointwise bound
  have hpt : ∀ᵐ x ∂ν,
      ENNReal.ofReal |(⨍ y in closedBall x (ρ / 2), v y) - ⨍ y in closedBall x ρ, v y| ^ p ≤
        c ^ p * GU ^ ((p - 2) / 2) *
          ∫⁻ y in closedBall x ρ, ∫⁻ z in closedBall x ρ, k y z := by
    filter_upwards [hsupp] with x hx
    haveI : IsFiniteMeasure (volume.restrict (closedBall x ρ)) :=
      ⟨by simpa using (aux_tight_subharmonic_vol_cb_fin x hρ.le).lt_top⟩
    have hint : IntegrableOn v (closedBall x ρ) :=
      (hvU.mono_measure (Measure.restrict_mono hx le_rfl)).integrable one_le_two
    have h1 := aux_tight_subharmonic_incr_le v hv x hρ ht hint
    set S := ∫⁻ y in closedBall x ρ, ∫⁻ z in closedBall x ρ, k y z with hS
    have hSle : S ≤ GU := by
      calc S ≤ ∫⁻ y in closedBall x ρ, ∫⁻ z in U, k y z :=
            lintegral_mono (fun y ↦ lintegral_mono_set hx)
        _ ≤ GU := lintegral_mono_set hx
    calc ENNReal.ofReal |(⨍ y in closedBall x (ρ / 2), v y) - ⨍ y in closedBall x ρ, v y| ^ p
        ≤ (c * S ^ (1 / 2 : ℝ)) ^ p := ENNReal.rpow_le_rpow h1 hp0.le
      _ = c ^ p * S ^ ((p - 2) / 2 + 1) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul]
          congr 2; ring
      _ = c ^ p * (S ^ ((p - 2) / 2) * S) := by
          rw [ENNReal.rpow_add_of_nonneg _ _ ha zero_le_one, ENNReal.rpow_one]
      _ ≤ c ^ p * (GU ^ ((p - 2) / 2) * S) :=
          mul_le_mul_right (mul_le_mul_left (ENNReal.rpow_le_rpow hSle ha) _) _
      _ = c ^ p * GU ^ ((p - 2) / 2) * S := by ring
  have hconst : c ^ p * GU ^ ((p - 2) / 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg ha hGU)
  have hint : ∫⁻ x, ENNReal.ofReal
      |(⨍ y in closedBall x (ρ / 2), v y) - ⨍ y in closedBall x ρ, v y| ^ p ∂ν ≤
      c ^ p * GU ^ ((p - 2) / 2) * (M * GU) := by
    calc _ ≤ ∫⁻ x, (c ^ p * GU ^ ((p - 2) / 2) *
          ∫⁻ y in closedBall x ρ, ∫⁻ z in closedBall x ρ, k y z) ∂ν := lintegral_mono_ae hpt
      _ = c ^ p * GU ^ ((p - 2) / 2) *
          ∫⁻ x, (∫⁻ y in closedBall x ρ, ∫⁻ z in closedBall x ρ, k y z) ∂ν :=
          lintegral_const_mul' _ _ hconst
      _ ≤ c ^ p * GU ^ ((p - 2) / 2) * (M * GU) := by
          gcongr
          exact aux_tight_subharmonic_fubini_mass U hU ν k hkm M hmass hsupp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top
      (show AEStronglyMeasurable (fun x ↦ (⨍ y in closedBall x (ρ / 2), v y) -
          ⨍ y in closedBall x ρ, v y) ν from
        ((aux_tight_subharmonic_meas_avg v hv (ρ / 2)).sub
          (aux_tight_subharmonic_meas_avg v hv ρ)).aestronglyMeasurable),
    ENNReal.toReal_ofReal hp0.le]
  simp only [Real.enorm_eq_ofReal_abs]
  calc (∫⁻ x, ENNReal.ofReal
        |(⨍ y in closedBall x (ρ / 2), v y) - ⨍ y in closedBall x ρ, v y| ^ p ∂ν) ^ (1 / p)
      ≤ (c ^ p * GU ^ ((p - 2) / 2) * (M * GU)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = c * M ^ (1 / p) * GU ^ (1 / 2 : ℝ) := by
        have e1 : c ^ p * GU ^ ((p - 2) / 2) * (M * GU) = c ^ p * M * GU ^ (p / 2) := by
          rw [show p / 2 = (p - 2) / 2 + 1 by ring,
            ENNReal.rpow_add_of_nonneg _ _ ha zero_le_one, ENNReal.rpow_one]
          ring
        rw [e1, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        rw [show p * (1 / p) = 1 by field_simp, show p / 2 * (1 / p) = 1 / 2 by field_simp,
          ENNReal.rpow_one]

/-- **Base term**: `‖⨍_{closedBall x ρ} v‖_{L^p(ν)} ≤ ν(univ)^{1/p} |B_ρ|^{-1/2} ‖v‖_{L²(U)}`. -/
lemma aux_tight_subharmonic_base_bound (U : Set (Fin d → ℝ)) (ν : Measure (Fin d → ℝ)) (v : (Fin d → ℝ) → ℝ)
    (hv : Measurable v) {ρ p : ℝ} (hρ : 0 < ρ) (hp : 2 ≤ p)
    (hsupp : ∀ᵐ x ∂ν, closedBall x ρ ⊆ U) :
    eLpNorm (fun x ↦ ⨍ y in closedBall x ρ, v y) (ENNReal.ofReal p) ν ≤
      ν Set.univ ^ (1 / p) * ENNReal.ofReal ((2 * ρ) ^ d) ^ (-(1 / 2 : ℝ)) *
        eLpNorm v 2 (volume.restrict U) := by
  have hp0 : 0 < p := by linarith
  set V := ENNReal.ofReal ((2 * ρ) ^ d) with hV
  have hV0 : V ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hVt : V ≠ ⊤ := ENNReal.ofReal_ne_top
  set b := V ^ (-(1 / 2 : ℝ)) * eLpNorm v 2 (volume.restrict U) with hb
  have hpt : ∀ᵐ x ∂ν, ‖⨍ y in closedBall x ρ, v y‖ₑ ≤ b := by
    filter_upwards [hsupp] with x hx
    have hvol : volume (closedBall x ρ) = V := aux_tight_subharmonic_vol_cb x hρ.le
    haveI : IsFiniteMeasure (volume.restrict (closedBall x ρ)) :=
      ⟨by simpa [hvol] using hVt.lt_top⟩
    calc ‖⨍ y in closedBall x ρ, v y‖ₑ
        ≤ (volume (closedBall x ρ))⁻¹ * ∫⁻ y in closedBall x ρ, ‖v y‖ₑ :=
          aux_tight_subharmonic_enorm_setAverage_le (hvol ▸ hV0) (hvol ▸ hVt)
      _ = V⁻¹ * eLpNorm v 1 (volume.restrict (closedBall x ρ)) := by
          rw [hvol, eLpNorm_one_eq_lintegral_enorm hv.aestronglyMeasurable]
      _ ≤ V⁻¹ * (eLpNorm v 2 (volume.restrict (closedBall x ρ)) *
            (volume.restrict (closedBall x ρ)) Set.univ ^ (1 / (1 : ℝ≥0∞).toReal -
              1 / (2 : ℝ≥0∞).toReal)) := by
          gcongr
          exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num)
            hv.aestronglyMeasurable
      _ = V⁻¹ * (eLpNorm v 2 (volume.restrict (closedBall x ρ)) * V ^ (1 / 2 : ℝ)) := by
          rw [Measure.restrict_apply_univ, hvol]; norm_num
      _ ≤ V⁻¹ * (eLpNorm v 2 (volume.restrict U) * V ^ (1 / 2 : ℝ)) := by
          gcongr
      _ = b := by
          rw [hb, ← mul_assoc, mul_comm (V⁻¹), mul_assoc, mul_comm]
          congr 1
          rw [← ENNReal.rpow_neg_one, ← ENNReal.rpow_add _ _ hV0 hVt]
          norm_num
  calc eLpNorm (fun x ↦ ⨍ y in closedBall x ρ, v y) (ENNReal.ofReal p) ν
      ≤ b • ν Set.univ ^ (ENNReal.ofReal p).toReal⁻¹ := eLpNorm_le_of_ae_enorm_bound (aux_tight_subharmonic_meas_avg v hv ρ).aestronglyMeasurable hpt
    _ = ν Set.univ ^ (1 / p) * ENNReal.ofReal ((2 * ρ) ^ d) ^ (-(1 / 2 : ℝ)) *
          eLpNorm v 2 (volume.restrict U) := by
        rw [ENNReal.toReal_ofReal hp0.le, smul_eq_mul, hb, one_div, ← hV]
        ring

lemma aux_tight_subharmonic_alg (σ t p K ρ : ℝ) (hρ : 0 < ρ) (hK : 0 < K) :
    (ρ ^ d)⁻¹ * (2 * ρ) ^ (((d : ℝ) + 2 * t) / 2) * (K * (2 * ρ) ^ ((d : ℝ) - σ)) ^ (1 / p) =
      K ^ (1 / p) * (2 ^ d * (2 * ρ) ^ (t - (d : ℝ) / 2 + ((d : ℝ) - σ) / p)) := by
  have h2ρ : 0 < 2 * ρ := by positivity
  have hρd : (ρ ^ d)⁻¹ = 2 ^ d * (2 * ρ) ^ (-(d : ℝ)) := by
    rw [Real.rpow_neg h2ρ.le, Real.rpow_natCast, mul_pow]
    field_simp
  have hcomb : (2 * ρ) ^ (-(d : ℝ)) * (2 * ρ) ^ (((d : ℝ) + 2 * t) / 2) *
      (2 * ρ) ^ (((d : ℝ) - σ) * (1 / p)) =
      (2 * ρ) ^ (t - (d : ℝ) / 2 + ((d : ℝ) - σ) / p) := by
    rw [← Real.rpow_add h2ρ, ← Real.rpow_add h2ρ]
    congr 1
    ring
  rw [hρd, Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul h2ρ.le]
  calc 2 ^ d * (2 * ρ) ^ (-(d : ℝ)) * (2 * ρ) ^ (((d : ℝ) + 2 * t) / 2) *
        (K ^ (1 / p) * (2 * ρ) ^ (((d : ℝ) - σ) * (1 / p)))
      = K ^ (1 / p) * (2 ^ d * ((2 * ρ) ^ (-(d : ℝ)) * (2 * ρ) ^ (((d : ℝ) + 2 * t) / 2) *
          (2 * ρ) ^ (((d : ℝ) - σ) * (1 / p)))) := by ring
    _ = _ := by rw [hcomb]

lemma aux_tight_subharmonic_geom (r0 e : ℝ) (hr0 : 0 < r0) (n : ℕ) :
    (2 * (r0 / 2 ^ (n + 1))) ^ e = r0 ^ e * ((2 ^ e)⁻¹) ^ n := by
  have h1 : 2 * (r0 / 2 ^ (n + 1)) = r0 / 2 ^ n := by rw [pow_succ]; field_simp
  rw [h1, Real.div_rpow hr0.le (by positivity), inv_pow, div_eq_mul_inv]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]

theorem aux_tight_subharmonic_aux_trace_Lp (d : ℕ) (σ t p r0 : ℝ) (hp : 2 ≤ p) (ht : 0 < t) (hr0 : 0 < r0)
    (hcrit : (d : ℝ) / 2 - ((d : ℝ) - σ) / p < t) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Set (Fin d → ℝ)) (ν : Measure (Fin d → ℝ)) (K : ℝ), 0 < K →
        IsFiniteMeasure ν → MeasurableSet U → ν ≪ volume →
        ν {x | ¬ Metric.closedBall x r0 ⊆ U} = 0 →
        (∀ y ∈ U, ∀ r : ℝ, 0 < r → r ≤ r0 →
          ν (Metric.ball y r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - σ))) →
        ∀ v : (Fin d → ℝ) → ℝ, Measurable v → MemLp v 2 (volume.restrict U) →
          eLpNorm v (ENNReal.ofReal p) ν ≤
            ENNReal.ofReal C *
              (ENNReal.ofReal (K ^ (1 / p)) *
                  (∫⁻ y in U, ∫⁻ z in U,
                    ENNReal.ofReal ((v y - v z) ^ 2) /
                      ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 2 * t))) ^ (1 / 2 : ℝ) +
                ν Set.univ ^ (1 / p) * ENNReal.ofReal (r0 ^ (-((d : ℝ) / 2))) *
                  eLpNorm v 2 (volume.restrict U)) := by
  have hp0 : 0 < p := by linarith
  set e : ℝ := t - (d : ℝ) / 2 + ((d : ℝ) - σ) / p with he
  have he0 : 0 < e := by rw [he]; linarith
  set q : ℝ := (2 ^ e)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) he0)
  set a : ℕ → ℝ := fun n ↦ 2 ^ d * (r0 ^ e * q ^ n) with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n ↦ by positivity
  have hasum : Summable a :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_left (r0 ^ e)).mul_left (2 ^ d)
  set Csum : ℝ := ∑' n, a n with hCsum
  refine ⟨max 1 Csum, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro U ν K hK hνfin hU hac hbad hmass v hv hvU
  set GU := ∫⁻ y in U, ∫⁻ z in U, ENNReal.ofReal ((v y - v z) ^ 2) /
    ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 2 * t)) with hGU
  -- the infinite-energy case is trivial
  by_cases hGUtop : GU = ⊤
  · have hKp : ENNReal.ofReal (K ^ (1 / p)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hK _)).ne'
    have hC : ENNReal.ofReal (max 1 Csum) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (lt_of_lt_of_le one_pos (le_max_left _ _))).ne'
    rw [hGUtop, ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top hKp]
    simp [hC]
  -- scales
  set ρ : ℕ → ℝ := fun n ↦ r0 / 2 ^ (n + 1) with hρ
  have hρpos : ∀ n, 0 < ρ n := fun n ↦ by positivity
  have hρsucc : ∀ n, ρ (n + 1) = ρ n / 2 := fun n ↦ by
    simp only [hρ, pow_succ]; field_simp
  have h2ρ : ∀ n, 2 * ρ n ≤ r0 := fun n ↦ by
    have : (2 : ℝ) ≤ 2 ^ (n + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    simp only [hρ]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hsupp0 : ∀ᵐ x ∂ν, closedBall x r0 ⊆ U := by
    rw [ae_iff]; simpa using hbad
  have hsupp : ∀ n, ∀ᵐ x ∂ν, closedBall x (ρ n) ⊆ U := fun n ↦ by
    filter_upwards [hsupp0] with x hx
    exact (closedBall_subset_closedBall (by linarith [h2ρ n, hρpos n])).trans hx
  have hmassn : ∀ n, ∀ y ∈ U, ν (closedBall y (ρ n)) ≤
      ENNReal.ofReal (K * (2 * ρ n) ^ ((d : ℝ) - σ)) := fun n y hy ↦ by
    calc ν (closedBall y (ρ n)) ≤ ν (Metric.ball y (2 * ρ n)) :=
          measure_mono (closedBall_subset_ball (by linarith [hρpos n]))
      _ ≤ _ := hmass y hy _ (by linarith [hρpos n]) (h2ρ n)
  -- the averages and their increments
  set A : ℕ → (Fin d → ℝ) → ℝ := fun n x ↦ ⨍ y in closedBall x (ρ n), v y with hA
  have hAm : ∀ n, Measurable (A n) := fun n ↦ aux_tight_subharmonic_meas_avg v hv (ρ n)
  set Δ : ℕ → (Fin d → ℝ) → ℝ := fun n x ↦ A (n + 1) x - A n x with hΔ
  have hΔm : ∀ n, AEStronglyMeasurable (Δ n) ν := fun n ↦
    ((hAm (n + 1)).sub (hAm n)).aestronglyMeasurable
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  -- per-scale bound
  have hΔbound : ∀ n, eLpNorm (Δ n) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal (a n) * ENNReal.ofReal (K ^ (1 / p)) * GU ^ (1 / 2 : ℝ) := by
    intro n
    have hg := aux_tight_subharmonic_gk_bound (t := t) U hU ν v hv hvU (hρpos n) ht hp _ (hmassn n) (hsupp n) hGUtop
    have hfun : Δ n = fun x ↦ (⨍ y in closedBall x (ρ n / 2), v y) -
        ⨍ y in closedBall x (ρ n), v y := by
      funext x; simp only [hΔ, hA, hρsucc]
    rw [hfun]
    refine hg.trans (le_of_eq ?_)
    congr 1
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      aux_tight_subharmonic_alg σ t p K (ρ n) (hρpos n) hK, mul_comm]
    congr 2
    simp only [ha, he]
    rw [← aux_tight_subharmonic_geom r0 _ hr0 n]
  -- base bound
  have hbase : eLpNorm (A 0) (ENNReal.ofReal p) ν ≤
      ν Set.univ ^ (1 / p) * ENNReal.ofReal (r0 ^ (-((d : ℝ) / 2))) *
        eLpNorm v 2 (volume.restrict U) := by
    refine (aux_tight_subharmonic_base_bound U ν v hv (hρpos 0) hp (hsupp 0)).trans (le_of_eq ?_)
    congr 2
    have h20 : 2 * ρ 0 = r0 := by simp only [hρ]; ring
    rw [h20, ENNReal.ofReal_rpow_of_pos (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hr0.le]
    congr 2; ring
  -- partial sums
  have hAn : ∀ n, A n = A 0 + ∑ k ∈ Finset.range n, Δ k := fun n ↦ by
    funext x
    simp only [Pi.add_apply, Finset.sum_apply, hΔ]
    rw [Finset.sum_range_sub (fun k ↦ A k x)]
    ring
  have hpartial : ∀ n, eLpNorm (A n) (ENNReal.ofReal p) ν ≤
      eLpNorm (A 0) (ENNReal.ofReal p) ν + ∑' k, eLpNorm (Δ k) (ENNReal.ofReal p) ν := by
    intro n
    rw [hAn n]
    refine (eLpNorm_add_le hp1).trans ?_
    gcongr
    exact (eLpNorm_sum_le hp1).trans (ENNReal.sum_le_tsum _)
  -- Lebesgue differentiation
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n ↦ A n x) atTop (𝓝 (v x)) := by
    set w := U.indicator v with hw
    have hwL : LocallyIntegrable w volume :=
      ((memLp_indicator_iff_restrict hU).2 hvU).locallyIntegrable one_le_two
    have hLeb := IsUnifLocDoublingMeasure.ae_tendsto_average (μ := volume) hwL 1
    have hρlim : Tendsto ρ atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hρpos⟩
      have : Tendsto (fun n : ℕ ↦ r0 / 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 (r0 / 2 * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
      rw [mul_zero] at this
      refine this.congr fun n ↦ ?_
      simp only [hρ]
      rw [div_pow, one_pow, pow_succ]
      field_simp
    filter_upwards [hac.ae_le hLeb, hsupp0] with x hx hxU
    have hconv := hx (fun _ : ℕ ↦ x) ρ hρlim
      (Eventually.of_forall fun n ↦ by simpa using (hρpos n).le)
    have hxU' : x ∈ U := hxU (mem_closedBall_self hr0.le)
    have hwx : w x = v x := Set.indicator_of_mem hxU' v
    rw [hwx] at hconv
    refine hconv.congr fun n ↦ ?_
    simp only [hA]
    rw [setAverage_eq, setAverage_eq]
    congr 1
    refine setIntegral_congr_fun measurableSet_closedBall fun y hy ↦ ?_
    exact Set.indicator_of_mem ((closedBall_subset_closedBall
      (by linarith [h2ρ n, hρpos n])).trans hxU hy) v
  -- assemble
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p)
    (fun n ↦ (hAm n).aestronglyMeasurable) v hv.aestronglyMeasurable hlim
  have hsumΔ : ∑' k, eLpNorm (Δ k) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal Csum * ENNReal.ofReal (K ^ (1 / p)) * GU ^ (1 / 2 : ℝ) := by
    calc ∑' k, eLpNorm (Δ k) (ENNReal.ofReal p) ν
        ≤ ∑' k, ENNReal.ofReal (a k) * (ENNReal.ofReal (K ^ (1 / p)) * GU ^ (1 / 2 : ℝ)) :=
          ENNReal.tsum_le_tsum fun k ↦ (hΔbound k).trans (le_of_eq (mul_assoc _ _ _))
      _ = (∑' k, ENNReal.ofReal (a k)) * (ENNReal.ofReal (K ^ (1 / p)) * GU ^ (1 / 2 : ℝ)) :=
          ENNReal.tsum_mul_right
      _ = ENNReal.ofReal Csum * ENNReal.ofReal (K ^ (1 / p)) * GU ^ (1 / 2 : ℝ) := by
          rw [hCsum, ENNReal.ofReal_tsum_of_nonneg ha0 hasum, mul_assoc]
  calc eLpNorm v (ENNReal.ofReal p) ν
      ≤ atTop.liminf fun n ↦ eLpNorm (A n) (ENNReal.ofReal p) ν := hfatou
    _ ≤ eLpNorm (A 0) (ENNReal.ofReal p) ν + ∑' k, eLpNorm (Δ k) (ENNReal.ofReal p) ν :=
        liminf_le_of_frequently_le' (Frequently.of_forall hpartial)
    _ ≤ ν Set.univ ^ (1 / p) * ENNReal.ofReal (r0 ^ (-((d : ℝ) / 2))) *
          eLpNorm v 2 (volume.restrict U) +
        ENNReal.ofReal Csum * ENNReal.ofReal (K ^ (1 / p)) * GU ^ (1 / 2 : ℝ) :=
        add_le_add hbase hsumΔ
    _ ≤ ENNReal.ofReal (max 1 Csum) *
          (ENNReal.ofReal (K ^ (1 / p)) * GU ^ (1 / 2 : ℝ) +
            ν Set.univ ^ (1 / p) * ENNReal.ofReal (r0 ^ (-((d : ℝ) / 2))) *
              eLpNorm v 2 (volume.restrict U)) := by
        have hC1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 Csum) := by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
        have hC2 : ENNReal.ofReal Csum ≤ ENNReal.ofReal (max 1 Csum) :=
          ENNReal.ofReal_le_ofReal (le_max_right _ _)
        rw [mul_add, add_comm (ENNReal.ofReal (max 1 Csum) * _)]
        refine add_le_add ?_ ?_
        · calc _ = 1 * (ν Set.univ ^ (1 / p) * ENNReal.ofReal (r0 ^ (-((d : ℝ) / 2))) *
                eLpNorm v 2 (volume.restrict U)) := (one_mul _).symm
            _ ≤ _ := mul_le_mul_left hC1 _
        · rw [mul_assoc]
          exact mul_le_mul_left hC2 _


theorem aux_tight_subharmonic_aux_trace_Lp_scaled (d : ℕ) (σ t p : ℝ) (hp : 2 ≤ p) (ht : 0 < t)
    (hcrit : (d : ℝ) / 2 - ((d : ℝ) - σ) / p < t) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r0 : ℝ), 0 < r0 → ∀ (U : Set (Fin d → ℝ)) (ν : Measure (Fin d → ℝ)) (K : ℝ), 0 < K →
        IsFiniteMeasure ν → MeasurableSet U → ν ≪ volume →
        ν {x | ¬ Metric.closedBall x r0 ⊆ U} = 0 →
        (∀ y ∈ U, ∀ r : ℝ, 0 < r → r ≤ r0 →
          ν (Metric.ball y r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - σ))) →
        ∀ v : (Fin d → ℝ) → ℝ, Measurable v → MemLp v 2 (volume.restrict U) →
          eLpNorm v (ENNReal.ofReal p) ν ≤
            ENNReal.ofReal C *
              (ENNReal.ofReal (K ^ (1 / p) * r0 ^ (t - (d : ℝ) / 2 + ((d : ℝ) - σ) / p)) *
                  (∫⁻ y in U, ∫⁻ z in U,
                    ENNReal.ofReal ((v y - v z) ^ 2) /
                      ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 2 * t))) ^ (1 / 2 : ℝ) +
                ν Set.univ ^ (1 / p) * ENNReal.ofReal (r0 ^ (-((d : ℝ) / 2))) *
                  eLpNorm v 2 (volume.restrict U)) := by
  have hp0 : 0 < p := by linarith
  set e : ℝ := t - (d : ℝ) / 2 + ((d : ℝ) - σ) / p with he
  have he0 : 0 < e := by rw [he]; linarith
  set q : ℝ := (2 ^ e)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) he0)
  set C0 : ℝ := ∑' n : ℕ, 2 ^ d * q ^ n with hC0
  refine ⟨max 1 C0, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro r0 hr0 U ν K hK hνfin hU hac hbad hmass v hv hvU
  set a : ℕ → ℝ := fun n ↦ 2 ^ d * (r0 ^ e * q ^ n) with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n ↦ by positivity
  have hasum : Summable a :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_left (r0 ^ e)).mul_left (2 ^ d)
  set Csum : ℝ := ∑' n, a n with hCsum
  have hCsum_eq : Csum = r0 ^ e * C0 := by
    rw [hCsum, hC0, ← tsum_mul_left]
    congr 1; funext n; simp only [ha]; ring
  set GU := ∫⁻ y in U, ∫⁻ z in U, ENNReal.ofReal ((v y - v z) ^ 2) /
    ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 2 * t)) with hGU
  -- the infinite-energy case is trivial
  by_cases hGUtop : GU = ⊤
  · have hKp : ENNReal.ofReal (K ^ (1 / p) * r0 ^ (t - (d : ℝ) / 2 + ((d : ℝ) - σ) / p)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (mul_pos (Real.rpow_pos_of_pos hK _) (Real.rpow_pos_of_pos hr0 _))).ne'
    have hC : ENNReal.ofReal (max 1 C0) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (lt_of_lt_of_le one_pos (le_max_left _ _))).ne'
    rw [hGUtop, ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top hKp]
    simp [hC]
  -- scales
  set ρ : ℕ → ℝ := fun n ↦ r0 / 2 ^ (n + 1) with hρ
  have hρpos : ∀ n, 0 < ρ n := fun n ↦ by positivity
  have hρsucc : ∀ n, ρ (n + 1) = ρ n / 2 := fun n ↦ by
    simp only [hρ, pow_succ]; field_simp
  have h2ρ : ∀ n, 2 * ρ n ≤ r0 := fun n ↦ by
    have : (2 : ℝ) ≤ 2 ^ (n + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    simp only [hρ]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hsupp0 : ∀ᵐ x ∂ν, closedBall x r0 ⊆ U := by
    rw [ae_iff]; simpa using hbad
  have hsupp : ∀ n, ∀ᵐ x ∂ν, closedBall x (ρ n) ⊆ U := fun n ↦ by
    filter_upwards [hsupp0] with x hx
    exact (closedBall_subset_closedBall (by linarith [h2ρ n, hρpos n])).trans hx
  have hmassn : ∀ n, ∀ y ∈ U, ν (closedBall y (ρ n)) ≤
      ENNReal.ofReal (K * (2 * ρ n) ^ ((d : ℝ) - σ)) := fun n y hy ↦ by
    calc ν (closedBall y (ρ n)) ≤ ν (Metric.ball y (2 * ρ n)) :=
          measure_mono (closedBall_subset_ball (by linarith [hρpos n]))
      _ ≤ _ := hmass y hy _ (by linarith [hρpos n]) (h2ρ n)
  -- the averages and their increments
  set A : ℕ → (Fin d → ℝ) → ℝ := fun n x ↦ ⨍ y in closedBall x (ρ n), v y with hA
  have hAm : ∀ n, Measurable (A n) := fun n ↦ aux_tight_subharmonic_meas_avg v hv (ρ n)
  set Δ : ℕ → (Fin d → ℝ) → ℝ := fun n x ↦ A (n + 1) x - A n x with hΔ
  have hΔm : ∀ n, AEStronglyMeasurable (Δ n) ν := fun n ↦
    ((hAm (n + 1)).sub (hAm n)).aestronglyMeasurable
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  -- per-scale bound
  have hΔbound : ∀ n, eLpNorm (Δ n) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal (a n) * ENNReal.ofReal (K ^ (1 / p)) * GU ^ (1 / 2 : ℝ) := by
    intro n
    have hg := aux_tight_subharmonic_gk_bound (t := t) U hU ν v hv hvU (hρpos n) ht hp _ (hmassn n) (hsupp n) hGUtop
    have hfun : Δ n = fun x ↦ (⨍ y in closedBall x (ρ n / 2), v y) -
        ⨍ y in closedBall x (ρ n), v y := by
      funext x; simp only [hΔ, hA, hρsucc]
    rw [hfun]
    refine hg.trans (le_of_eq ?_)
    congr 1
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      aux_tight_subharmonic_alg σ t p K (ρ n) (hρpos n) hK, mul_comm]
    congr 2
    simp only [ha, he]
    rw [← aux_tight_subharmonic_geom r0 _ hr0 n]
  -- base bound
  have hbase : eLpNorm (A 0) (ENNReal.ofReal p) ν ≤
      ν Set.univ ^ (1 / p) * ENNReal.ofReal (r0 ^ (-((d : ℝ) / 2))) *
        eLpNorm v 2 (volume.restrict U) := by
    refine (aux_tight_subharmonic_base_bound U ν v hv (hρpos 0) hp (hsupp 0)).trans (le_of_eq ?_)
    congr 2
    have h20 : 2 * ρ 0 = r0 := by simp only [hρ]; ring
    rw [h20, ENNReal.ofReal_rpow_of_pos (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hr0.le]
    congr 2; ring
  -- partial sums
  have hAn : ∀ n, A n = A 0 + ∑ k ∈ Finset.range n, Δ k := fun n ↦ by
    funext x
    simp only [Pi.add_apply, Finset.sum_apply, hΔ]
    rw [Finset.sum_range_sub (fun k ↦ A k x)]
    ring
  have hpartial : ∀ n, eLpNorm (A n) (ENNReal.ofReal p) ν ≤
      eLpNorm (A 0) (ENNReal.ofReal p) ν + ∑' k, eLpNorm (Δ k) (ENNReal.ofReal p) ν := by
    intro n
    rw [hAn n]
    refine (eLpNorm_add_le hp1).trans ?_
    gcongr
    exact (eLpNorm_sum_le hp1).trans (ENNReal.sum_le_tsum _)
  -- Lebesgue differentiation
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n ↦ A n x) atTop (𝓝 (v x)) := by
    set w := U.indicator v with hw
    have hwL : LocallyIntegrable w volume :=
      ((memLp_indicator_iff_restrict hU).2 hvU).locallyIntegrable one_le_two
    have hLeb := IsUnifLocDoublingMeasure.ae_tendsto_average (μ := volume) hwL 1
    have hρlim : Tendsto ρ atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hρpos⟩
      have : Tendsto (fun n : ℕ ↦ r0 / 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 (r0 / 2 * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
      rw [mul_zero] at this
      refine this.congr fun n ↦ ?_
      simp only [hρ]
      rw [div_pow, one_pow, pow_succ]
      field_simp
    filter_upwards [hac.ae_le hLeb, hsupp0] with x hx hxU
    have hconv := hx (fun _ : ℕ ↦ x) ρ hρlim
      (Eventually.of_forall fun n ↦ by simpa using (hρpos n).le)
    have hxU' : x ∈ U := hxU (mem_closedBall_self hr0.le)
    have hwx : w x = v x := Set.indicator_of_mem hxU' v
    rw [hwx] at hconv
    refine hconv.congr fun n ↦ ?_
    simp only [hA]
    rw [setAverage_eq, setAverage_eq]
    congr 1
    refine setIntegral_congr_fun measurableSet_closedBall fun y hy ↦ ?_
    exact Set.indicator_of_mem ((closedBall_subset_closedBall
      (by linarith [h2ρ n, hρpos n])).trans hxU hy) v
  -- assemble
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p)
    (fun n ↦ (hAm n).aestronglyMeasurable) v hv.aestronglyMeasurable hlim
  have hsumΔ : ∑' k, eLpNorm (Δ k) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal Csum * ENNReal.ofReal (K ^ (1 / p)) * GU ^ (1 / 2 : ℝ) := by
    calc ∑' k, eLpNorm (Δ k) (ENNReal.ofReal p) ν
        ≤ ∑' k, ENNReal.ofReal (a k) * (ENNReal.ofReal (K ^ (1 / p)) * GU ^ (1 / 2 : ℝ)) :=
          ENNReal.tsum_le_tsum fun k ↦ (hΔbound k).trans (le_of_eq (mul_assoc _ _ _))
      _ = (∑' k, ENNReal.ofReal (a k)) * (ENNReal.ofReal (K ^ (1 / p)) * GU ^ (1 / 2 : ℝ)) :=
          ENNReal.tsum_mul_right
      _ = ENNReal.ofReal Csum * ENNReal.ofReal (K ^ (1 / p)) * GU ^ (1 / 2 : ℝ) := by
          rw [hCsum, ENNReal.ofReal_tsum_of_nonneg ha0 hasum, mul_assoc]
  calc eLpNorm v (ENNReal.ofReal p) ν
      ≤ atTop.liminf fun n ↦ eLpNorm (A n) (ENNReal.ofReal p) ν := hfatou
    _ ≤ eLpNorm (A 0) (ENNReal.ofReal p) ν + ∑' k, eLpNorm (Δ k) (ENNReal.ofReal p) ν :=
        liminf_le_of_frequently_le' (Frequently.of_forall hpartial)
    _ ≤ ν Set.univ ^ (1 / p) * ENNReal.ofReal (r0 ^ (-((d : ℝ) / 2))) *
          eLpNorm v 2 (volume.restrict U) +
        ENNReal.ofReal Csum * ENNReal.ofReal (K ^ (1 / p)) * GU ^ (1 / 2 : ℝ) :=
        add_le_add hbase hsumΔ
    _ ≤ ENNReal.ofReal (max 1 C0) *
          (ENNReal.ofReal (K ^ (1 / p) * r0 ^ (t - (d : ℝ) / 2 + ((d : ℝ) - σ) / p)) *
              GU ^ (1 / 2 : ℝ) +
            ν Set.univ ^ (1 / p) * ENNReal.ofReal (r0 ^ (-((d : ℝ) / 2))) *
              eLpNorm v 2 (volume.restrict U)) := by
        have hC1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 C0) := by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
        have hC0nn : 0 ≤ C0 := tsum_nonneg fun n ↦ by positivity
        have hC2 : ENNReal.ofReal Csum * ENNReal.ofReal (K ^ (1 / p)) ≤
            ENNReal.ofReal (max 1 C0) *
              ENNReal.ofReal (K ^ (1 / p) * r0 ^ (t - (d : ℝ) / 2 + ((d : ℝ) - σ) / p)) := by
          rw [← ENNReal.ofReal_mul (by rw [hCsum_eq]; positivity),
            ← ENNReal.ofReal_mul (le_trans zero_le_one (le_max_left _ _))]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hCsum_eq, ← he]
          have hK' : 0 ≤ K ^ (1 / p) := Real.rpow_nonneg hK.le _
          have hr' : 0 ≤ r0 ^ e := Real.rpow_nonneg hr0.le _
          calc r0 ^ e * C0 * K ^ (1 / p) = C0 * (K ^ (1 / p) * r0 ^ e) := by ring
            _ ≤ max 1 C0 * (K ^ (1 / p) * r0 ^ e) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hK' hr')
        rw [mul_add, add_comm (ENNReal.ofReal (max 1 C0) * _)]
        refine add_le_add ?_ ?_
        · calc _ = 1 * (ν Set.univ ^ (1 / p) * ENNReal.ofReal (r0 ^ (-((d : ℝ) / 2))) *
                eLpNorm v 2 (volume.restrict U)) := (one_mul _).symm
            _ ≤ _ := mul_le_mul_left hC1 _
        · rw [← mul_assoc]
          exact mul_le_mul_left hC2 _

end




section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

variable {d : ℕ}

/-- `(a+b)² ≤ 2a²+2b²` in `ℝ≥0∞`. -/
lemma aux_tight_subharmonic_ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  by_cases ha : a = ⊤
  · simp [ha]
  by_cases hb : b = ⊤
  · simp [hb]
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  have h : ((a : ℝ≥0) + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    rw [← NNReal.coe_le_coe]; push_cast
    nlinarith [sq_nonneg ((a : ℝ) - b)]
  exact_mod_cast h

/-- `‖f‖₂² = ∫⁻ f²`. -/
lemma aux_tight_subharmonic_eLpNorm_two_sq (f : (Fin d → ℝ) → ℝ) (μ : Measure (Fin d → ℝ)) :
    SubdiffusiveProcess.RawLp.eLpNorm f 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ := by
  have hp2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral two_ne_zero (by norm_num) f μ, hp2]
  have hint : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [hint, ← ENNReal.rpow_natCast ((∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) ^ (1 / 2 : ℝ)) 2,
    ← ENNReal.rpow_mul]
  norm_num

lemma aux_tight_subharmonic_guarded_two_sq (f : (Fin d → ℝ) → ℝ)
    (μ : Measure (Fin d → ℝ)) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ := by
  rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hf]
  exact aux_tight_subharmonic_eLpNorm_two_sq f μ

/-- Pointwise splitting against a `μ`-average over `B`. -/
lemma aux_tight_subharmonic_pt_split (μ : Measure (Fin d → ℝ)) (g : (Fin d → ℝ) → ℝ) (hg : Measurable g)
    (B : Set (Fin d → ℝ)) (x : Fin d → ℝ) (h0 : μ B ≠ 0) (htop : μ B ≠ ∞) :
    ENNReal.ofReal (g x ^ 2) ≤ 2 * (μ B)⁻¹ * ∫⁻ y in B, ENNReal.ofReal ((g y - g x) ^ 2) ∂μ +
      2 * (μ B)⁻¹ * ∫⁻ y in B, ENNReal.ofReal (g y ^ 2) ∂μ := by
  have hpt : ∀ y, ENNReal.ofReal (g x ^ 2) ≤
      2 * ENNReal.ofReal ((g y - g x) ^ 2) + 2 * ENNReal.ofReal (g y ^ 2) := by
    intro y
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (g x - 2 * g y)])
  have hm1 : Measurable fun y ↦ 2 * ENNReal.ofReal ((g y - g x) ^ 2) :=
    (ENNReal.measurable_ofReal.comp ((hg.sub measurable_const).pow_const 2)).const_mul _
  calc ENNReal.ofReal (g x ^ 2) = (μ B)⁻¹ * ∫⁻ _ in B, ENNReal.ofReal (g x ^ 2) ∂μ := by
        rw [setLIntegral_const, mul_comm, mul_assoc, ENNReal.mul_inv_cancel h0 htop, mul_one]
    _ ≤ (μ B)⁻¹ * ∫⁻ y in B, (2 * ENNReal.ofReal ((g y - g x) ^ 2) +
          2 * ENNReal.ofReal (g y ^ 2)) ∂μ := by
        gcongr with y; exact hpt y
    _ = _ := by
        rw [lintegral_add_left hm1, lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ (by norm_num)]
        ring


lemma aux_tight_subharmonic_ball_integral_eq (μ : Measure (Fin d → ℝ)) (F : (Fin d → ℝ) → ℝ≥0∞) (R : ℝ)
    (x : Fin d → ℝ) :
    ∫⁻ y in ball x R, F y ∂μ =
      ∫⁻ y, ({p : (Fin d → ℝ) × (Fin d → ℝ) | dist p.2 p.1 < R}.indicator
        (fun p ↦ F p.2)) (x, y) ∂μ := by
  rw [← lintegral_indicator measurableSet_ball]
  rfl

lemma aux_tight_subharmonic_measurableSet_distLt (R : ℝ) :
    MeasurableSet {p : (Fin d → ℝ) × (Fin d → ℝ) | dist p.2 p.1 < R} :=
  measurableSet_lt (continuous_snd.dist continuous_fst).measurable measurable_const

lemma aux_tight_subharmonic_measurable_ball_integral (μ : Measure (Fin d → ℝ)) [SFinite μ]
    (F : (Fin d → ℝ) → ℝ≥0∞) (hF : Measurable F) (R : ℝ) :
    Measurable fun x ↦ ∫⁻ y in ball x R, F y ∂μ := by
  simp_rw [aux_tight_subharmonic_ball_integral_eq μ F R]
  exact ((hF.comp measurable_snd).indicator (aux_tight_subharmonic_measurableSet_distLt R)).lintegral_prod_right'

/-- Tonelli: integrating ball-averages over `x ∈ S` costs the volume of a ball. -/
lemma aux_tight_subharmonic_ball_tonelli (μ : Measure (Fin d → ℝ)) [SFinite μ] (F : (Fin d → ℝ) → ℝ≥0∞)
    (hF : Measurable F) (S U' : Set (Fin d → ℝ)) (hS : MeasurableSet S) (hU' : MeasurableSet U')
    {R : ℝ} (hR : 0 < R) (hSU : ∀ x ∈ S, ball x R ⊆ U') :
    ∫⁻ x in S, ∫⁻ y in ball x R, F y ∂μ ≤ ENNReal.ofReal ((2 * R) ^ d) * ∫⁻ y in U', F y ∂μ := by
  set G : (Fin d → ℝ) × (Fin d → ℝ) → ℝ≥0∞ :=
    {p : (Fin d → ℝ) × (Fin d → ℝ) | dist p.2 p.1 < R}.indicator (fun p ↦ U'.indicator F p.2)
    with hG
  have hGm : Measurable G :=
    (((hF.indicator hU').comp measurable_snd)).indicator (aux_tight_subharmonic_measurableSet_distLt R)
  have hpt : ∀ x ∈ S, ∫⁻ y in ball x R, F y ∂μ ≤ ∫⁻ y, G (x, y) ∂μ := by
    intro x hx
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_mono fun y ↦ ?_
    by_cases h : dist y x < R
    · have hyU : y ∈ U' := hSU x hx h
      rw [Set.indicator_of_mem (show y ∈ ball x R from h), hG,
        Set.indicator_of_mem (show (x, y) ∈ {p : (Fin d → ℝ) × (Fin d → ℝ) | dist p.2 p.1 < R} from h),
        Set.indicator_of_mem hyU]
    · rw [Set.indicator_of_notMem (show y ∉ ball x R from h)]; exact zero_le
  have hinner : ∀ y, ∫⁻ x, G (x, y) = U'.indicator F y * ENNReal.ofReal ((2 * R) ^ d) := by
    intro y
    have : (fun x ↦ G (x, y)) = (ball y R).indicator (fun _ ↦ U'.indicator F y) := by
      funext x
      by_cases h : dist y x < R
      · rw [hG, Set.indicator_of_mem (show (x, y) ∈ {p : (Fin d → ℝ) × (Fin d → ℝ) | dist p.2 p.1 < R} from h),
          Set.indicator_of_mem (show x ∈ ball y R by rw [mem_ball, dist_comm]; exact h)]
      · rw [hG, Set.indicator_of_notMem (show (x, y) ∉ {p : (Fin d → ℝ) × (Fin d → ℝ) | dist p.2 p.1 < R} from h),
          Set.indicator_of_notMem (show x ∉ ball y R by rw [mem_ball, dist_comm]; exact h)]
    rw [this, lintegral_indicator measurableSet_ball, setLIntegral_const, Real.volume_pi_ball y hR,
      Fintype.card_fin]
  calc ∫⁻ x in S, ∫⁻ y in ball x R, F y ∂μ ≤ ∫⁻ x in S, ∫⁻ y, G (x, y) ∂μ :=
        setLIntegral_mono hGm.lintegral_prod_right' hpt
    _ ≤ ∫⁻ x, ∫⁻ y, G (x, y) ∂μ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ y, (∫⁻ x, G (x, y)) ∂μ := lintegral_lintegral_swap (f := fun x y ↦ G (x, y)) hGm.aemeasurable
    _ = ∫⁻ y, U'.indicator F y * ENNReal.ofReal ((2 * R) ^ d) ∂μ :=
        lintegral_congr fun y ↦ hinner y
    _ = ENNReal.ofReal ((2 * R) ^ d) * ∫⁻ y in U', F y ∂μ := by
        rw [lintegral_mul_const _ (hF.indicator hU'), lintegral_indicator hU', mul_comm]


/-- Squaring the `p = 2` trace bound. -/
lemma aux_tight_subharmonic_sq_of_trace (ν μU : Measure (Fin d → ℝ)) (v : (Fin d → ℝ) → ℝ) (C0 a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (G : ℝ≥0∞)
    (h : SubdiffusiveProcess.RawLp.eLpNorm v (ENNReal.ofReal 2) ν ≤ ENNReal.ofReal C0 *
      (ENNReal.ofReal a * G ^ (1 / 2 : ℝ) + ν Set.univ ^ (1 / (2 : ℝ)) * ENNReal.ofReal b *
        SubdiffusiveProcess.RawLp.eLpNorm v 2 μU)) :
    ∫⁻ x, ENNReal.ofReal (v x ^ 2) ∂ν ≤ 2 * ENNReal.ofReal (C0 ^ 2) *
      (ENNReal.ofReal (a ^ 2) * G + ν Set.univ * ENNReal.ofReal (b ^ 2) *
        ∫⁻ x, ENNReal.ofReal (v x ^ 2) ∂μU) := by
  rw [ENNReal.ofReal_ofNat] at h
  rw [← aux_tight_subharmonic_eLpNorm_two_sq v ν, ← aux_tight_subharmonic_eLpNorm_two_sq v μU]
  have hhalf : ∀ z : ℝ≥0∞, (z ^ (1 / 2 : ℝ)) ^ 2 = z := fun z ↦ by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have hC : ENNReal.ofReal C0 ^ 2 ≤ ENNReal.ofReal (C0 ^ 2) := by
    rcases le_or_gt 0 C0 with h0 | h0
    · rw [ENNReal.ofReal_pow h0]
    · rw [ENNReal.ofReal_of_nonpos h0.le]; simp
  calc SubdiffusiveProcess.RawLp.eLpNorm v 2 ν ^ 2 ≤ (ENNReal.ofReal C0 *
        (ENNReal.ofReal a * G ^ (1 / 2 : ℝ) + ν Set.univ ^ (1 / (2 : ℝ)) * ENNReal.ofReal b *
          SubdiffusiveProcess.RawLp.eLpNorm v 2 μU)) ^ 2 := by gcongr
    _ = ENNReal.ofReal C0 ^ 2 * (ENNReal.ofReal a * G ^ (1 / 2 : ℝ) +
          ν Set.univ ^ (1 / (2 : ℝ)) * ENNReal.ofReal b * SubdiffusiveProcess.RawLp.eLpNorm v 2 μU) ^ 2 := mul_pow _ _ _
    _ ≤ ENNReal.ofReal (C0 ^ 2) * (2 * (ENNReal.ofReal a * G ^ (1 / 2 : ℝ)) ^ 2 +
          2 * (ν Set.univ ^ (1 / (2 : ℝ)) * ENNReal.ofReal b * SubdiffusiveProcess.RawLp.eLpNorm v 2 μU) ^ 2) := by
        gcongr
        exact aux_tight_subharmonic_ennreal_add_sq_le _ _
    _ = 2 * ENNReal.ofReal (C0 ^ 2) * (ENNReal.ofReal (a ^ 2) * G + ν Set.univ *
          ENNReal.ofReal (b ^ 2) * SubdiffusiveProcess.RawLp.eLpNorm v 2 μU ^ 2) := by
        rw [mul_pow, mul_pow, mul_pow, hhalf, hhalf, ← ENNReal.ofReal_pow ha,
          ← ENNReal.ofReal_pow hb]
        ring

/-- **Two norms** (proof.tex step (ii)), continuous-average form: the Lebesgue `L²` norm on `S` is
controlled by the `L²(μ)` norm and the Gagliardo energy on `U' ⊇ S + B_{3ρ}`, using the lower mass
bound at scale `ρ` and the trace inequality at scale `ρ`. -/
theorem aux_tight_subharmonic_two_norms (σ t : ℝ) (ht : 0 < t) (hcrit : σ / 2 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure (Fin d → ℝ)) [SFinite μ] (K ρ : ℝ)
      (S U' : Set (Fin d → ℝ)) (g : (Fin d → ℝ) → ℝ), 0 < K → 0 < ρ → MeasurableSet S →
      MeasurableSet U' → μ ≪ volume →
      (∀ x ∈ S, closedBall x (3 * ρ) ⊆ U') →
      (∀ x ∈ S, ENNReal.ofReal (K⁻¹ * ρ ^ ((d : ℝ) + σ)) ≤ μ (ball x ρ)) →
      (∀ y ∈ U', ∀ r : ℝ, 0 < r → r ≤ ρ → μ (ball y r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - σ))) →
      Measurable g → MemLp g 2 (volume.restrict U') →
      ∫⁻ x in S, ENNReal.ofReal (g x ^ 2) ≤
        ENNReal.ofReal (C * (K * ρ ^ (-σ))) * ∫⁻ y in U', ENNReal.ofReal (g y ^ 2) ∂μ +
        ENNReal.ofReal (C * (K ^ 2 * ρ ^ (2 * t - 2 * σ) + ρ ^ (2 * t))) *
          ∫⁻ y in U', ∫⁻ z in U', ENNReal.ofReal ((g y - g z) ^ 2) /
            ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 2 * t)) := by
  have hcrit' : (d : ℝ) / 2 - ((d : ℝ) - σ) / 2 < t := by
    have : (d : ℝ) / 2 - ((d : ℝ) - σ) / 2 = σ / 2 := by ring
    linarith
  obtain ⟨C0, hC0, htr⟩ := aux_tight_subharmonic_aux_trace_Lp_scaled d σ t 2 le_rfl ht hcrit'
  set e : ℝ := t - (d : ℝ) / 2 + ((d : ℝ) - σ) / 2 with he
  refine ⟨max (2 ^ (d + 1)) (4 * C0 ^ 2 * 6 ^ ((d : ℝ) + 2 * t)), by positivity, ?_⟩
  intro μ _ K ρ S U' g hK hρ hS hU' hac hball hlow hup hg hgL2
  set k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ≥0∞ := fun y z ↦
    ENNReal.ofReal ((g y - g z) ^ 2) / ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 2 * t)) with hkdef
  have hk : Measurable (Function.uncurry k) := aux_tight_subharmonic_meas_kernel g hg _
  set Φ : (Fin d → ℝ) → ℝ≥0∞ := fun y ↦ ∫⁻ z in U', k y z with hΦ
  have hΦm : Measurable Φ := hk.lintegral_prod_right'
  set Ψ : (Fin d → ℝ) → ℝ≥0∞ := fun x ↦ ∫⁻ y in U', k x y with hΨ
  have hΨm : Measurable Ψ := hk.lintegral_prod_right'
  have hF2m : Measurable fun y ↦ ENNReal.ofReal (g y ^ 2) :=
    ENNReal.measurable_ofReal.comp (hg.pow_const 2)
  have h3 : (0 : ℝ) < 3 * ρ := by positivity
  have hsub3 : ∀ x ∈ S, ball x (3 * ρ) ⊆ U' := fun x hx ↦
    ball_subset_closedBall.trans (hball x hx)
  have hsub1 : ∀ x ∈ S, ball x ρ ⊆ U' := fun x hx ↦
    (ball_subset_ball (by linarith)).trans (hsub3 x hx)
  have hSU : S ⊆ U' := fun x hx ↦ hsub1 x hx (mem_ball_self hρ)
  have hmpos : ∀ x ∈ S, μ (ball x ρ) ≠ 0 := fun x hx ↦
    (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by positivity)) (hlow x hx)).ne'
  have hmfin : ∀ x ∈ S, μ (ball x ρ) ≠ ∞ := fun x hx ↦
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hup x (hSU hx) ρ hρ le_rfl)
  have hminv : ∀ x ∈ S, (μ (ball x ρ))⁻¹ ≤ ENNReal.ofReal (K * ρ ^ (-((d : ℝ) + σ))) := by
    intro x hx
    have hpos : 0 < K⁻¹ * ρ ^ ((d : ℝ) + σ) := by positivity
    calc (μ (ball x ρ))⁻¹ ≤ (ENNReal.ofReal (K⁻¹ * ρ ^ ((d : ℝ) + σ)))⁻¹ :=
          ENNReal.inv_le_inv.2 (hlow x hx)
      _ = ENNReal.ofReal (K * ρ ^ (-((d : ℝ) + σ))) := by
          rw [← ENNReal.ofReal_inv_of_pos hpos, mul_inv, inv_inv, Real.rpow_neg hρ.le]
  -- the trace inequality at scale `ρ` around each `x ∈ S`
  have hI1 : ∀ x ∈ S, ∫⁻ y in ball x ρ, ENNReal.ofReal ((g y - g x) ^ 2) ∂μ ≤
      2 * ENNReal.ofReal (C0 ^ 2) * (ENNReal.ofReal (K * ρ ^ (2 * t - σ)) *
        (∫⁻ y in ball x (3 * ρ), ∫⁻ z in ball x (3 * ρ), k y z) +
        μ (ball x ρ) * ENNReal.ofReal (ρ ^ (-(d : ℝ))) *
          ∫⁻ y in ball x (3 * ρ), ENNReal.ofReal ((g y - g x) ^ 2)) := by
    intro x hx
    haveI : IsFiniteMeasure (μ.restrict (ball x ρ)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (hmfin x hx)⟩
    have hnull : μ.restrict (ball x ρ) {y | ¬ closedBall y ρ ⊆ ball x (3 * ρ)} = 0 := by
      rw [Measure.restrict_apply' measurableSet_ball]
      refine measure_mono_null (fun y hy ↦ ?_) (measure_empty (μ := μ))
      exfalso
      obtain ⟨hy1, hy2⟩ := hy
      apply hy1
      intro z hz
      rw [mem_closedBall] at hz
      rw [mem_ball] at hy2 ⊢
      calc dist z x ≤ dist z y + dist y x := dist_triangle z y x
        _ < ρ + ρ := by linarith
        _ ≤ 3 * ρ := by linarith
    have hmass : ∀ y ∈ ball x (3 * ρ), ∀ r : ℝ, 0 < r → r ≤ ρ →
        μ.restrict (ball x ρ) (ball y r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - σ)) :=
      fun y hy r hr hrρ ↦ (Measure.restrict_apply_le _ _).trans (hup y (hsub3 x hx hy) r hr hrρ)
    have hvL2 : MemLp (fun y ↦ g y - g x) 2 (volume.restrict (ball x (3 * ρ))) := by
      haveI : IsFiniteMeasure (volume.restrict (ball x (3 * ρ))) := ⟨by
        rw [Measure.restrict_apply_univ, Real.volume_pi_ball x h3]; exact ENNReal.ofReal_lt_top⟩
      exact (hgL2.mono_measure (Measure.restrict_mono (hsub3 x hx) le_rfl)).sub (memLp_const _)
    have hT := htr ρ hρ (ball x (3 * ρ)) (μ.restrict (ball x ρ)) K hK inferInstance
      measurableSet_ball ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hac)
      hnull hmass (fun y ↦ g y - g x) (hg.sub measurable_const) hvL2
    have hsq := aux_tight_subharmonic_sq_of_trace (μ.restrict (ball x ρ)) (volume.restrict (ball x (3 * ρ))) (fun y ↦ g y - g x) C0 (K ^ (1 / (2 : ℝ)) * ρ ^ e) (ρ ^ (-((d : ℝ) / 2))) (by positivity) (by positivity) _ (by simpa only [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (show AEStronglyMeasurable (fun y ↦ g y - g x) (μ.restrict (ball x ρ)) from (hg.sub_const (g x)).aestronglyMeasurable), SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (show AEStronglyMeasurable (fun y ↦ g y - g x) (volume.restrict (ball x (3 * ρ))) from (hg.sub_const (g x)).aestronglyMeasurable)] using! hT)
    have hKe : (K ^ (1 / (2 : ℝ)) * ρ ^ e) ^ 2 = K * ρ ^ (2 * t - σ) := by
      have h1 : (K ^ (1 / (2 : ℝ))) ^ 2 = K := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le]; norm_num
      have h2 : (ρ ^ e) ^ 2 = ρ ^ (2 * t - σ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]; congr 1; rw [he]; push_cast; ring
      rw [mul_pow, h1, h2]
    have hρd : (ρ ^ (-((d : ℝ) / 2))) ^ 2 = ρ ^ (-(d : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]; congr 1; push_cast; ring
    rw [hKe, hρd, Measure.restrict_apply_univ] at hsq
    beta_reduce at hsq
    simp only [sub_sub_sub_cancel_right] at hsq
    exact hsq
  have hΦle : ∀ x ∈ S, (∫⁻ y in ball x (3 * ρ), ∫⁻ z in ball x (3 * ρ), k y z) ≤
      ∫⁻ y in ball x (3 * ρ), Φ y :=
    fun x hx ↦ lintegral_mono fun y ↦ lintegral_mono_set (hsub3 x hx)
  have hL : ∀ x ∈ S, (∫⁻ y in ball x (3 * ρ), ENNReal.ofReal ((g y - g x) ^ 2)) ≤
      ENNReal.ofReal ((2 * (3 * ρ)) ^ ((d : ℝ) + 2 * t)) * Ψ x := by
    intro x hx
    rw [hΨ]
    dsimp only
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc _ ≤ ∫⁻ y in ball x (3 * ρ), ENNReal.ofReal ((2 * (3 * ρ)) ^ ((d : ℝ) + 2 * t)) * k x y := by
          refine setLIntegral_mono' measurableSet_ball fun y hy ↦ ?_
          have hxy : ‖x - y‖ ≤ 2 * (3 * ρ) := by
            rw [← dist_eq_norm, dist_comm]
            exact (mem_ball.1 hy).le.trans (by linarith)
          have := aux_tight_subharmonic_sq_le_kernel x y (g x - g y) h3 ht hxy
          rw [show (g y - g x) ^ 2 = (g x - g y) ^ 2 by ring]
          exact this
      _ ≤ _ := lintegral_mono_set (hsub3 x hx)
  have hpt : ∀ x ∈ S, ENNReal.ofReal (g x ^ 2) ≤
      4 * ENNReal.ofReal (C0 ^ 2) * ENNReal.ofReal (K * ρ ^ (-((d : ℝ) + σ))) *
          ENNReal.ofReal (K * ρ ^ (2 * t - σ)) * (∫⁻ y in ball x (3 * ρ), Φ y) +
        4 * ENNReal.ofReal (C0 ^ 2) * ENNReal.ofReal (ρ ^ (-(d : ℝ))) *
          ENNReal.ofReal ((2 * (3 * ρ)) ^ ((d : ℝ) + 2 * t)) * Ψ x +
        2 * ENNReal.ofReal (K * ρ ^ (-((d : ℝ) + σ))) * ∫⁻ y in ball x ρ, ENNReal.ofReal (g y ^ 2) ∂μ := by
    intro x hx
    have hs := aux_tight_subharmonic_pt_split μ g hg (ball x ρ) x (hmpos x hx) (hmfin x hx)
    refine hs.trans ?_
    gcongr ?_ + ?_
    · calc 2 * (μ (ball x ρ))⁻¹ * ∫⁻ y in ball x ρ, ENNReal.ofReal ((g y - g x) ^ 2) ∂μ
          ≤ 2 * (μ (ball x ρ))⁻¹ * (2 * ENNReal.ofReal (C0 ^ 2) *
              (ENNReal.ofReal (K * ρ ^ (2 * t - σ)) *
                (∫⁻ y in ball x (3 * ρ), ∫⁻ z in ball x (3 * ρ), k y z) +
              μ (ball x ρ) * ENNReal.ofReal (ρ ^ (-(d : ℝ))) *
                ∫⁻ y in ball x (3 * ρ), ENNReal.ofReal ((g y - g x) ^ 2))) := by
            gcongr; exact hI1 x hx
        _ = 4 * ENNReal.ofReal (C0 ^ 2) * (μ (ball x ρ))⁻¹ * ENNReal.ofReal (K * ρ ^ (2 * t - σ)) *
              (∫⁻ y in ball x (3 * ρ), ∫⁻ z in ball x (3 * ρ), k y z) +
            4 * ENNReal.ofReal (C0 ^ 2) * ((μ (ball x ρ))⁻¹ * μ (ball x ρ)) *
              ENNReal.ofReal (ρ ^ (-(d : ℝ))) *
                ∫⁻ y in ball x (3 * ρ), ENNReal.ofReal ((g y - g x) ^ 2) := by ring
        _ = 4 * ENNReal.ofReal (C0 ^ 2) * (μ (ball x ρ))⁻¹ * ENNReal.ofReal (K * ρ ^ (2 * t - σ)) *
              (∫⁻ y in ball x (3 * ρ), ∫⁻ z in ball x (3 * ρ), k y z) +
            4 * ENNReal.ofReal (C0 ^ 2) * ENNReal.ofReal (ρ ^ (-(d : ℝ))) *
                ∫⁻ y in ball x (3 * ρ), ENNReal.ofReal ((g y - g x) ^ 2) := by
            rw [ENNReal.inv_mul_cancel (hmpos x hx) (hmfin x hx), mul_one]
        _ ≤ 4 * ENNReal.ofReal (C0 ^ 2) * ENNReal.ofReal (K * ρ ^ (-((d : ℝ) + σ))) *
              ENNReal.ofReal (K * ρ ^ (2 * t - σ)) * (∫⁻ y in ball x (3 * ρ), Φ y) +
            4 * ENNReal.ofReal (C0 ^ 2) * ENNReal.ofReal (ρ ^ (-(d : ℝ))) *
              (ENNReal.ofReal ((2 * (3 * ρ)) ^ ((d : ℝ) + 2 * t)) * Ψ x) := by
            exact add_le_add (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl (hminv x hx)) le_rfl)
              (hΦle x hx)) (mul_le_mul' le_rfl (hL x hx))
        _ = _ := by ring
    · gcongr; exact hminv x hx
  have hJm : Measurable fun x ↦ ∫⁻ y in ball x (3 * ρ), Φ y :=
    aux_tight_subharmonic_measurable_ball_integral volume Φ hΦm _
  have hI2m : Measurable fun x ↦ ∫⁻ y in ball x ρ, ENNReal.ofReal (g y ^ 2) ∂μ :=
    aux_tight_subharmonic_measurable_ball_integral μ _ hF2m _
  set Gag := ∫⁻ y in U', ∫⁻ z in U', k y z with hGag
  set I := ∫⁻ y in U', ENNReal.ofReal (g y ^ 2) ∂μ with hI
  set c1 := 4 * ENNReal.ofReal (C0 ^ 2) * ENNReal.ofReal (K * ρ ^ (-((d : ℝ) + σ))) *
    ENNReal.ofReal (K * ρ ^ (2 * t - σ)) with hc1
  set c2 := 4 * ENNReal.ofReal (C0 ^ 2) * ENNReal.ofReal (ρ ^ (-(d : ℝ))) *
    ENNReal.ofReal ((2 * (3 * ρ)) ^ ((d : ℝ) + 2 * t)) with hc2
  set c3 := 2 * ENNReal.ofReal (K * ρ ^ (-((d : ℝ) + σ))) with hc3
  have hint : ∫⁻ x in S, ENNReal.ofReal (g x ^ 2) ≤
      c1 * (ENNReal.ofReal ((2 * (3 * ρ)) ^ d) * Gag) + c2 * Gag +
        c3 * (ENNReal.ofReal ((2 * ρ) ^ d) * I) := by
    have h1 := aux_tight_subharmonic_ball_tonelli volume Φ hΦm S U' hS hU' h3 hsub3
    have h2 : ∫⁻ x in S, Ψ x ≤ Gag := lintegral_mono_set hSU
    have h3' := aux_tight_subharmonic_ball_tonelli μ _ hF2m S U' hS hU' hρ hsub1
    calc ∫⁻ x in S, ENNReal.ofReal (g x ^ 2)
        ≤ ∫⁻ x in S, (c1 * (∫⁻ y in ball x (3 * ρ), Φ y) + c2 * Ψ x +
            c3 * (∫⁻ y in ball x ρ, ENNReal.ofReal (g y ^ 2) ∂μ)) :=
          setLIntegral_mono (((hJm.const_mul c1).add (hΨm.const_mul c2)).add (hI2m.const_mul c3))
            hpt
      _ = c1 * (∫⁻ x in S, ∫⁻ y in ball x (3 * ρ), Φ y) + c2 * (∫⁻ x in S, Ψ x) +
            c3 * (∫⁻ x in S, ∫⁻ y in ball x ρ, ENNReal.ofReal (g y ^ 2) ∂μ) := by
          have hAdd (f g : (Fin d → ℝ) → ℝ≥0∞) (hf : Measurable f) :
              (∫⁻ x in S, f x + g x) = (∫⁻ x in S, f x) + ∫⁻ x in S, g x := by
            simpa only [Pi.add_apply] using! (lintegral_add_left (μ := volume.restrict S) (g := g) hf)
          rw [hAdd (fun x ↦ c1 * (∫⁻ y in ball x (3 * ρ), Φ y) + c2 * Ψ x)
              (fun x ↦ c3 * (∫⁻ y in ball x ρ, ENNReal.ofReal (g y ^ 2) ∂μ))
              ((hJm.const_mul c1).add (hΨm.const_mul c2)),
            hAdd (fun x ↦ c1 * (∫⁻ y in ball x (3 * ρ), Φ y)) (fun x ↦ c2 * Ψ x)
              (hJm.const_mul c1), lintegral_const_mul _ hJm,
            lintegral_const_mul _ hΨm, lintegral_const_mul _ hI2m]
      _ ≤ _ := add_le_add (add_le_add (mul_le_mul' le_rfl h1) (mul_le_mul' le_rfl h2))
            (mul_le_mul' le_rfl h3')
  -- constants
  have hC0' : 0 ≤ 4 * C0 ^ 2 := by positivity
  have hr1 : (K * ρ ^ (-((d : ℝ) + σ))) * (K * ρ ^ (2 * t - σ)) * (2 * (3 * ρ)) ^ d =
      6 ^ d * (K ^ 2 * ρ ^ (2 * t - 2 * σ)) := by
    have hρe : ρ ^ (-((d : ℝ) + σ)) * ρ ^ (2 * t - σ) * ρ ^ (d : ℝ) = ρ ^ (2 * t - 2 * σ) := by
      rw [← Real.rpow_add hρ, ← Real.rpow_add hρ]; congr 1; ring
    calc (K * ρ ^ (-((d : ℝ) + σ))) * (K * ρ ^ (2 * t - σ)) * (2 * (3 * ρ)) ^ d
        = 6 ^ d * K ^ 2 * (ρ ^ (-((d : ℝ) + σ)) * ρ ^ (2 * t - σ) * ρ ^ (d : ℝ)) := by
          rw [Real.rpow_natCast, show 2 * (3 * ρ) = 6 * ρ by ring, mul_pow]; ring
      _ = 6 ^ d * (K ^ 2 * ρ ^ (2 * t - 2 * σ)) := by rw [hρe]; ring
  have hr2 : ρ ^ (-(d : ℝ)) * (2 * (3 * ρ)) ^ ((d : ℝ) + 2 * t) =
      6 ^ ((d : ℝ) + 2 * t) * ρ ^ (2 * t) := by
    rw [show 2 * (3 * ρ) = 6 * ρ by ring, Real.mul_rpow (by norm_num) hρ.le]
    have : ρ ^ (-(d : ℝ)) * ρ ^ ((d : ℝ) + 2 * t) = ρ ^ (2 * t) := by
      rw [← Real.rpow_add hρ]; congr 1; ring
    calc ρ ^ (-(d : ℝ)) * (6 ^ ((d : ℝ) + 2 * t) * ρ ^ ((d : ℝ) + 2 * t))
        = 6 ^ ((d : ℝ) + 2 * t) * (ρ ^ (-(d : ℝ)) * ρ ^ ((d : ℝ) + 2 * t)) := by ring
      _ = _ := by rw [this]
  have hr3 : (K * ρ ^ (-((d : ℝ) + σ))) * (2 * ρ) ^ d = 2 ^ d * (K * ρ ^ (-σ)) := by
    have : ρ ^ (-((d : ℝ) + σ)) * ρ ^ (d : ℝ) = ρ ^ (-σ) := by
      rw [← Real.rpow_add hρ]; congr 1; ring
    calc (K * ρ ^ (-((d : ℝ) + σ))) * (2 * ρ) ^ d
        = 2 ^ d * K * (ρ ^ (-((d : ℝ) + σ)) * ρ ^ (d : ℝ)) := by
          rw [Real.rpow_natCast, mul_pow]; ring
      _ = _ := by rw [this]; ring
  set Cf := max (2 ^ (d + 1)) (4 * C0 ^ 2 * 6 ^ ((d : ℝ) + 2 * t)) with hCf
  have h6 : (6 : ℝ) ^ d ≤ 6 ^ ((d : ℝ) + 2 * t) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hA : c1 * ENNReal.ofReal ((2 * (3 * ρ)) ^ d) + c2 ≤
      ENNReal.ofReal (Cf * (K ^ 2 * ρ ^ (2 * t - 2 * σ) + ρ ^ (2 * t))) := by
    have e1 : c1 * ENNReal.ofReal ((2 * (3 * ρ)) ^ d) =
        ENNReal.ofReal (4 * C0 ^ 2 * (6 ^ d * (K ^ 2 * ρ ^ (2 * t - 2 * σ)))) := by
      rw [hc1, show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← hr1]
      congr 1; ring
    have e2 : c2 = ENNReal.ofReal (4 * C0 ^ 2 * (6 ^ ((d : ℝ) + 2 * t) * ρ ^ (2 * t))) := by
      rw [hc2, show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← hr2]
      congr 1; ring
    rw [e1, e2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hK2 : 0 ≤ K ^ 2 * ρ ^ (2 * t - 2 * σ) := by positivity
    have hρ2 : 0 ≤ ρ ^ (2 * t) := by positivity
    have hCf : 4 * C0 ^ 2 * 6 ^ ((d : ℝ) + 2 * t) ≤ Cf := le_max_right _ _
    calc 4 * C0 ^ 2 * (6 ^ d * (K ^ 2 * ρ ^ (2 * t - 2 * σ))) +
          4 * C0 ^ 2 * (6 ^ ((d : ℝ) + 2 * t) * ρ ^ (2 * t))
        ≤ 4 * C0 ^ 2 * (6 ^ ((d : ℝ) + 2 * t) * (K ^ 2 * ρ ^ (2 * t - 2 * σ))) +
          4 * C0 ^ 2 * (6 ^ ((d : ℝ) + 2 * t) * ρ ^ (2 * t)) := by gcongr
      _ = 4 * C0 ^ 2 * 6 ^ ((d : ℝ) + 2 * t) * (K ^ 2 * ρ ^ (2 * t - 2 * σ) + ρ ^ (2 * t)) := by
          ring
      _ ≤ Cf * (K ^ 2 * ρ ^ (2 * t - 2 * σ) + ρ ^ (2 * t)) := by gcongr
  have hB : c3 * ENNReal.ofReal ((2 * ρ) ^ d) ≤ ENNReal.ofReal (Cf * (K * ρ ^ (-σ))) := by
    rw [hc3, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hCf : (2 : ℝ) ^ (d + 1) ≤ Cf := le_max_left _ _
    calc 2 * (K * ρ ^ (-((d : ℝ) + σ))) * (2 * ρ) ^ d = 2 ^ (d + 1) * (K * ρ ^ (-σ)) := by
          rw [mul_assoc, hr3, pow_succ]; ring
      _ ≤ Cf * (K * ρ ^ (-σ)) := by gcongr
  calc ∫⁻ x in S, ENNReal.ofReal (g x ^ 2)
      ≤ c1 * (ENNReal.ofReal ((2 * (3 * ρ)) ^ d) * Gag) + c2 * Gag +
          c3 * (ENNReal.ofReal ((2 * ρ) ^ d) * I) := hint
    _ = (c3 * ENNReal.ofReal ((2 * ρ) ^ d)) * I +
          (c1 * ENNReal.ofReal ((2 * (3 * ρ)) ^ d) + c2) * Gag := by ring
    _ ≤ _ := add_le_add (mul_le_mul' hB le_rfl) (mul_le_mul' hA le_rfl)

end




section
open MeasureTheory Metric
open scoped ENNReal

lemma aux_tight_subharmonic_cover_grid_mem {d : ℕ} {R δ : ℝ} (hδ : 0 < δ) {x : Fin d → ℝ} (hx : x ∈ ball (0 : Fin d → ℝ) R) :
    ∃ m : Fin d → ℤ, (∀ i, m i ∈ Finset.Icc (-(⌈R / δ⌉₊ : ℤ)) (⌈R / δ⌉₊ : ℤ)) ∧
      x ∈ ball (δ • (fun i ↦ (m i : ℝ))) δ ∧ ‖δ • (fun i ↦ (m i : ℝ))‖ < R + δ := by
  rw [mem_ball_zero_iff] at hx
  have hR : 0 ≤ R := (norm_nonneg _).trans hx.le
  refine ⟨fun i ↦ round (x i / δ), fun i ↦ ?_, ?_, ?_⟩
  · have hxi : |x i| < R := (norm_le_pi_norm x i).trans_lt hx |>.trans_le' (le_of_eq (Real.norm_eq_abs _).symm)
    have hr := abs_sub_round (x i / δ)
    have h1 : |(round (x i / δ) : ℝ)| < R / δ + 1 / 2 := by
      have : |x i / δ| < R / δ := by
        rw [abs_div, abs_of_pos hδ]; exact div_lt_div_of_pos_right hxi hδ
      have := abs_sub_abs_le_abs_sub (round (x i / δ) : ℝ) (x i / δ)
      rw [abs_sub_comm] at this
      linarith [abs_sub_comm (x i / δ) (round (x i / δ) : ℝ)]
    have hceil : R / δ ≤ (⌈R / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : |(round (x i / δ) : ℝ)| < (⌈R / δ⌉₊ : ℝ) + 1 := by linarith
    have h3 : |round (x i / δ)| < (⌈R / δ⌉₊ : ℤ) + 1 := by
      have : ((|round (x i / δ)| : ℤ) : ℝ) < (((⌈R / δ⌉₊ : ℤ) + 1 : ℤ) : ℝ) := by
        push_cast; simpa [Int.cast_abs] using h2
      exact_mod_cast this
    rw [Finset.mem_Icc]
    constructor <;> [linarith [neg_abs_le (round (x i / δ))]; linarith [le_abs_self (round (x i / δ))]]
  · rw [mem_ball, dist_eq_norm]
    refine (pi_norm_lt_iff hδ).2 fun i ↦ ?_
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    have hr := abs_sub_round (x i / δ)
    have : x i - δ * (round (x i / δ) : ℝ) = δ * (x i / δ - round (x i / δ)) := by
      field_simp
    rw [this, abs_mul, abs_of_pos hδ]
    nlinarith
  · have hsub : ‖x - δ • (fun i ↦ (round (x i / δ) : ℝ))‖ < δ := by
      refine (pi_norm_lt_iff hδ).2 fun i ↦ ?_
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
      have hr := abs_sub_round (x i / δ)
      have : x i - δ * (round (x i / δ) : ℝ) = δ * (x i / δ - round (x i / δ)) := by
        field_simp
      rw [this, abs_mul, abs_of_pos hδ]
      nlinarith
    calc ‖δ • (fun i ↦ (round (x i / δ) : ℝ))‖
        = ‖x - (x - δ • (fun i ↦ (round (x i / δ) : ℝ)))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - δ • (fun i ↦ (round (x i / δ) : ℝ))‖ := norm_sub_le _ _
      _ < R + δ := add_lt_add hx hsub

/-- Covering a sup-norm ball `ball 0 R` in `Fin d → ℝ` by the balls `ball (δ • m) δ`, `m ∈ ℤ^d`,
`|m i| ≤ ⌈R/δ⌉`, whose centres satisfy `‖c‖ < R + δ`: any measure is bounded by the number of
grid points times a uniform bound on those balls. -/
theorem aux_tight_subharmonic_cover_ball {d : ℕ} (Γ : Measure (Fin d → ℝ)) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    {M : ℝ≥0∞} (hM : ∀ c : Fin d → ℝ, ‖c‖ < R + δ → Γ (ball c δ) ≤ M) :
    Γ (ball 0 R) ≤ (((2 * ⌈R / δ⌉₊ + 1) ^ d : ℕ) : ℝ≥0∞) * M := by
  set N : ℕ := ⌈R / δ⌉₊
  set G : Finset (Fin d → ℤ) := Fintype.piFinset fun _ ↦ Finset.Icc (-(N : ℤ)) (N : ℤ)
  set c : (Fin d → ℤ) → (Fin d → ℝ) := fun m ↦ δ • (fun i ↦ (m i : ℝ))
  set G' : Finset (Fin d → ℤ) := G.filter fun m ↦ ‖c m‖ < R + δ
  have hcover : ball (0 : Fin d → ℝ) R ⊆ ⋃ m ∈ G', ball (c m) δ := by
    intro x hx
    obtain ⟨m, hm, hxm, hc⟩ := aux_tight_subharmonic_cover_grid_mem hδ hx
    have hmem : m ∈ G' := Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 hm, hc⟩
    exact Set.mem_biUnion (x := m) hmem hxm
  have hcard : G.card = (2 * N + 1) ^ d := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
    congr 1
    omega
  calc Γ (ball 0 R) ≤ Γ (⋃ m ∈ G', ball (c m) δ) := measure_mono hcover
    _ ≤ ∑ m ∈ G', Γ (ball (c m) δ) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _m ∈ G', M := Finset.sum_le_sum fun m hm ↦ hM _ (Finset.mem_filter.1 hm).2
    _ = (G'.card : ℝ≥0∞) * M := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (G.card : ℝ≥0∞) * M := by
        gcongr; exact Finset.filter_subset _ _
    _ = (((2 * N + 1) ^ d : ℕ) : ℝ≥0∞) * M := by rw [hcard]

end




section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- Hole-filling iteration: `f j ≤ θ f (j+1) + M D^j Y` with `f` bounded and `θ D < 1`. -/
theorem aux_tight_subharmonic_iter_absorb (f : ℕ → ℝ≥0∞) (F : ℝ≥0∞) (hF : F ≠ ⊤) (hfF : ∀ j, f j ≤ F)
    {θ D M : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hD : 0 ≤ D) (hθD : θ * D < 1) (hM : 0 ≤ M)
    (Y : ℝ≥0∞) (hstep : ∀ j, f j ≤ ENNReal.ofReal θ * f (j + 1) + ENNReal.ofReal (M * D ^ j) * Y) :
    f 0 ≤ ENNReal.ofReal (M / (1 - θ * D)) * Y := by
  have hq0 : 0 ≤ θ * D := mul_nonneg hθ0 hD
  have hclaim : ∀ n : ℕ, f 0 ≤ ENNReal.ofReal (θ ^ n) * f n +
      ENNReal.ofReal (∑ j ∈ Finset.range n, M * (θ * D) ^ j) * Y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ih.trans ?_
      have h1 : ENNReal.ofReal (θ ^ n) * f n ≤ ENNReal.ofReal (θ ^ (n + 1)) * f (n + 1) +
          ENNReal.ofReal (M * (θ * D) ^ n) * Y := by
        calc ENNReal.ofReal (θ ^ n) * f n
            ≤ ENNReal.ofReal (θ ^ n) * (ENNReal.ofReal θ * f (n + 1) +
                ENNReal.ofReal (M * D ^ n) * Y) := by gcongr; exact hstep n
          _ = ENNReal.ofReal (θ ^ (n + 1)) * f (n + 1) +
                ENNReal.ofReal (M * (θ * D) ^ n) * Y := by
              rw [mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
                ← ENNReal.ofReal_mul (by positivity), pow_succ, mul_pow]
              congr 2; ring
      calc ENNReal.ofReal (θ ^ n) * f n + ENNReal.ofReal (∑ j ∈ Finset.range n, M * (θ * D) ^ j) * Y
          ≤ ENNReal.ofReal (θ ^ (n + 1)) * f (n + 1) + ENNReal.ofReal (M * (θ * D) ^ n) * Y +
              ENNReal.ofReal (∑ j ∈ Finset.range n, M * (θ * D) ^ j) * Y := by gcongr
        _ = _ := by
            rw [Finset.sum_range_succ, ENNReal.ofReal_add
              (Finset.sum_nonneg fun j _ ↦ by positivity) (by positivity)]
            ring
  have hsum : ∀ n : ℕ, ∑ j ∈ Finset.range n, M * (θ * D) ^ j ≤ M / (1 - θ * D) := by
    intro n
    rw [← Finset.mul_sum, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ hM
    rw [← tsum_geometric_of_lt_one hq0 hθD]
    exact (summable_geometric_of_lt_one hq0 hθD).sum_le_tsum _ (fun j _ ↦ by positivity)
  have hbound : ∀ n : ℕ, f 0 ≤ ENNReal.ofReal (θ ^ n) * F + ENNReal.ofReal (M / (1 - θ * D)) * Y :=
    fun n ↦ (hclaim n).trans (add_le_add (mul_le_mul' le_rfl (hfF n))
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (hsum n)) le_rfl))
  have hlim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (θ ^ n) * F +
      ENNReal.ofReal (M / (1 - θ * D)) * Y) atTop
      (𝓝 (0 + ENNReal.ofReal (M / (1 - θ * D)) * Y)) := by
    refine Tendsto.add ?_ tendsto_const_nhds
    have h0 : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (θ ^ n)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1)
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hF)
  rw [zero_add] at hlim
  exact ge_of_tendsto' hlim hbound

end




section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

/-- Gagliardo energy with kernel exponent `d + 3/2` (`t = 3/4`) on `U`. -/
def aux_tight_subharmonic_gag {d : ℕ} (g : (Fin d → ℝ) → ℝ) (U : Set (Fin d → ℝ)) : ℝ≥0∞ :=
  ∫⁻ y in U, ∫⁻ z in U, ENNReal.ofReal ((g y - g z) ^ 2) /
    ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 3 / 2))

/-- `H^{3/4}`-type energy: Gagliardo energy plus Lebesgue `L²`. -/
def aux_tight_subharmonic_fE {d : ℕ} (g : (Fin d → ℝ) → ℝ) (U : Set (Fin d → ℝ)) : ℝ≥0∞ :=
  aux_tight_subharmonic_gag g U + ∫⁻ y in U, ENNReal.ofReal (g y ^ 2)

lemma aux_tight_subharmonic_gag_mono {d : ℕ} (g : (Fin d → ℝ) → ℝ) {U V : Set (Fin d → ℝ)} (h : U ⊆ V) :
    aux_tight_subharmonic_gag g U ≤ aux_tight_subharmonic_gag g V :=
  (lintegral_mono fun _ ↦ lintegral_mono_set h).trans (lintegral_mono_set h)

lemma aux_tight_subharmonic_gag_le_fE {d : ℕ} (g : (Fin d → ℝ) → ℝ) (U : Set (Fin d → ℝ)) : aux_tight_subharmonic_gag g U ≤ aux_tight_subharmonic_fE g U :=
  le_self_add

lemma aux_tight_subharmonic_sub_ball {d : ℕ} {x : Fin d → ℝ} {a s b : ℝ} (hx : x ∈ ball (0 : Fin d → ℝ) a)
    (h : a + s ≤ b) : ball x s ⊆ ball 0 b := by
  refine ball_subset_ball' ?_
  rw [mem_ball] at hx; linarith

lemma aux_tight_subharmonic_sub_closedBall {d : ℕ} {x : Fin d → ℝ} {a s b : ℝ} (hx : x ∈ ball (0 : Fin d → ℝ) a)
    (h : a + s ≤ b) : closedBall x s ⊆ ball 0 b := by
  refine closedBall_subset_ball' ?_
  rw [mem_ball] at hx; linarith

lemma aux_tight_subharmonic_memLp_of_bdd {d : ℕ} (g : (Fin d → ℝ) → ℝ) (hg : Measurable g) {Mg : ℝ}
    (hgb : ∀ x, |g x| ≤ Mg) (x0 : Fin d → ℝ) (a : ℝ) :
    MemLp g 2 (volume.restrict (ball x0 a)) := by
  haveI : IsFiniteMeasure (volume.restrict (ball x0 a)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  exact MemLp.of_bound hg.aestronglyMeasurable Mg
    (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hgb x)

lemma aux_tight_subharmonic_half_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma aux_tight_subharmonic_neg_half_sq {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x ^ (-(a / 2))) ^ 2 = x ^ (-a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; congr 1; push_cast; ring

/-- **One hole-filling step** (proof.tex (iii)+(iv) at the measure level).  Radii `r < r+h < r+2h < r+3h`.
`Γ` is the cutoff energy measure of a cutoff `≡ 1` on `ball 0 r`, supported in `ball 0 (r+h)`, with the upper
mass bound `KΓ ρ'^{d-1/2}` and total mass `≤ NΓ KΓ`; `hcc` is the Caccioppoli–coercivity inequality
(the output of CC).  Trace at scale `r0` on `U = ball 0 (r+2h)` and two norms at scale `ρ` on
`ball 0 (r+3h)` give the recursion with an explicit coefficient. -/
theorem aux_tight_subharmonic_hole_step {d : ℕ} : ∃ C : ℝ, 0 < C ∧ ∀ (μ Γ : Measure (Fin d → ℝ)) [SFinite μ]
    (g : (Fin d → ℝ) → ℝ) (Mg K KΓ NΓ Kcc Rmax r h r0 ρ : ℝ),
    Measurable g → (∀ x, |g x| ≤ Mg) → 0 < K → 0 < KΓ → 0 ≤ NΓ → 0 ≤ Kcc → 0 < h → 0 ≤ r →
    r + 3 * h + ρ ≤ Rmax → 0 < r0 → r0 ≤ h → r0 ≤ 1 → 0 < ρ → 3 * ρ ≤ h → ρ ≤ 1 →
    μ ≪ volume →
    (∀ x ρ', 0 < ρ' → ρ' ≤ 1 → ball x ρ' ⊆ ball 0 Rmax →
      ENNReal.ofReal (K⁻¹ * ρ' ^ ((d : ℝ) + 1 / 2)) ≤ μ (ball x ρ') ∧
        μ (ball x ρ') ≤ ENNReal.ofReal (K * ρ' ^ ((d : ℝ) - 1 / 2))) →
    Γ ≪ volume → Γ (ball 0 (r + h))ᶜ = 0 → Γ Set.univ ≤ ENNReal.ofReal (NΓ * KΓ) →
    (∀ x ρ', 0 < ρ' → ρ' ≤ 1 → Γ (ball x ρ') ≤ ENNReal.ofReal (KΓ * ρ' ^ ((d : ℝ) - 1 / 2))) →
    aux_tight_subharmonic_fE g (ball 0 r) ≤ ENNReal.ofReal Kcc * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂Γ →
    aux_tight_subharmonic_fE g (ball 0 r) ≤
      ENNReal.ofReal (C * Kcc * KΓ * (r0 + NΓ * r0 ^ (-(d : ℝ)) *
          (K ^ 2 * ρ ^ (1 / 2 : ℝ) + ρ ^ (3 / 2 : ℝ)))) * aux_tight_subharmonic_fE g (ball 0 (r + 3 * h)) +
        ENNReal.ofReal (C * Kcc * KΓ * NΓ * r0 ^ (-(d : ℝ)) * K * ρ ^ (-(1 / 2) : ℝ)) *
          ∫⁻ x in ball 0 (r + 3 * h), ENNReal.ofReal (g x ^ 2) ∂μ := by
  obtain ⟨CT, hCT, htr⟩ := aux_tight_subharmonic_aux_trace_Lp_scaled d (1 / 2) (3 / 4) 2 le_rfl (by norm_num)
    (by ring_nf; norm_num)
  obtain ⟨CN, hCN, htn⟩ := aux_tight_subharmonic_two_norms (d := d) (1 / 2) (3 / 4) (by norm_num) (by norm_num)
  refine ⟨2 * CT ^ 2 * max 1 CN, by positivity, ?_⟩
  intro μ Γ _ g Mg K KΓ NΓ Kcc Rmax r h r0 ρ hg hgb hK hKΓ hNΓ hKcc hh hr hRmax hr0 hr0h hr01
    hρ hρh hρ1 hac hmass hΓac hΓsupp hΓtot hΓup hcc
  set U : Set (Fin d → ℝ) := ball 0 (r + 2 * h) with hU
  set U' : Set (Fin d → ℝ) := ball 0 (r + 3 * h) with hU'
  set FR := aux_tight_subharmonic_fE g U' with hFR
  set Y := ∫⁻ x in U', ENNReal.ofReal (g x ^ 2) ∂μ with hY
  haveI : IsFiniteMeasure Γ := ⟨hΓtot.trans_lt ENNReal.ofReal_lt_top⟩
  -- trace on `U` with `ν = Γ`
  have hnull : Γ {x | ¬ closedBall x r0 ⊆ U} = 0 := by
    refine measure_mono_null (fun x hx ↦ ?_) hΓsupp
    intro hxb
    exact hx (aux_tight_subharmonic_sub_closedBall hxb (by linarith))
  have hT := htr r0 hr0 U Γ KΓ hKΓ inferInstance measurableSet_ball hΓac hnull
    (fun y _ r' hr' hr'0 ↦ hΓup y r' hr' (hr'0.trans hr01)) g hg (aux_tight_subharmonic_memLp_of_bdd g hg hgb 0 _)
  have e1 : (3 / 4 : ℝ) - (d : ℝ) / 2 + ((d : ℝ) - 1 / 2) / 2 = 1 / 2 := by ring
  have e2 : (d : ℝ) + 2 * (3 / 4 : ℝ) = (d : ℝ) + 3 / 2 := by norm_num
  rw [e1, e2] at hT
  have hsq := aux_tight_subharmonic_sq_of_trace Γ (volume.restrict U) g CT (KΓ ^ (1 / (2 : ℝ)) * r0 ^ (1 / (2 : ℝ))) (r0 ^ (-((d : ℝ) / 2))) (by positivity) (by positivity) _ (by simpa only [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hg.aestronglyMeasurable] using! hT)
  rw [mul_pow, aux_tight_subharmonic_half_sq hKΓ.le, aux_tight_subharmonic_half_sq hr0.le, aux_tight_subharmonic_neg_half_sq hr0.le] at hsq
  -- two norms on `U'` at scale `ρ`
  have hN := htn μ K ρ U U' g hK hρ measurableSet_ball measurableSet_ball hac
    (fun x hx ↦ aux_tight_subharmonic_sub_closedBall hx (by linarith))
    (fun x hx ↦ (hmass x ρ hρ hρ1 (aux_tight_subharmonic_sub_ball hx (by linarith))).1)
    (fun y hy r' hr' hr'ρ ↦ (hmass y r' hr' (hr'ρ.trans hρ1) (aux_tight_subharmonic_sub_ball hy (by linarith))).2)
    hg (aux_tight_subharmonic_memLp_of_bdd g hg hgb 0 _)
  have e3 : (2 : ℝ) * (3 / 4) - 2 * (1 / 2) = 1 / 2 := by norm_num
  have e4 : (2 : ℝ) * (3 / 4) = 3 / 2 := by norm_num
  have e5 : (d : ℝ) + 2 * (3 / 4 : ℝ) = (d : ℝ) + 3 / 2 := by norm_num
  rw [e3, e4] at hN
  have hGU : aux_tight_subharmonic_gag g U ≤ FR := (aux_tight_subharmonic_gag_mono g (ball_subset_ball (by linarith))).trans (aux_tight_subharmonic_gag_le_fE g U')
  have hGU' : aux_tight_subharmonic_gag g U' ≤ FR := aux_tight_subharmonic_gag_le_fE g U'
  have hL : ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂(volume.restrict U) ≤
      ENNReal.ofReal (CN * (K * ρ ^ (-(1 / 2) : ℝ))) * Y +
        ENNReal.ofReal (CN * (K ^ 2 * ρ ^ (1 / 2 : ℝ) + ρ ^ (3 / 2 : ℝ))) * FR :=
    hN.trans (add_le_add le_rfl (mul_le_mul' le_rfl hGU'))
  have hCN1 : CN ≤ max 1 CN := le_max_right _ _
  calc aux_tight_subharmonic_fE g (ball 0 r) ≤ ENNReal.ofReal Kcc * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂Γ := hcc
    _ ≤ ENNReal.ofReal Kcc * (2 * ENNReal.ofReal (CT ^ 2) *
          (ENNReal.ofReal (KΓ * r0) * aux_tight_subharmonic_gag g U + Γ Set.univ * ENNReal.ofReal (r0 ^ (-(d : ℝ))) *
            ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂(volume.restrict U))) := by
        gcongr; exact hsq
    _ ≤ ENNReal.ofReal Kcc * (2 * ENNReal.ofReal (CT ^ 2) *
          (ENNReal.ofReal (KΓ * r0) * FR + ENNReal.ofReal (NΓ * KΓ) *
            ENNReal.ofReal (r0 ^ (-(d : ℝ))) *
            (ENNReal.ofReal (CN * (K * ρ ^ (-(1 / 2) : ℝ))) * Y +
              ENNReal.ofReal (CN * (K ^ 2 * ρ ^ (1 / 2 : ℝ) + ρ ^ (3 / 2 : ℝ))) * FR))) := by
        gcongr
    _ = ENNReal.ofReal (2 * CT ^ 2 * Kcc * KΓ * (r0 + NΓ * r0 ^ (-(d : ℝ)) * CN *
            (K ^ 2 * ρ ^ (1 / 2 : ℝ) + ρ ^ (3 / 2 : ℝ)))) * FR +
          ENNReal.ofReal (2 * CT ^ 2 * CN * Kcc * KΓ * NΓ * r0 ^ (-(d : ℝ)) * K *
            ρ ^ (-(1 / 2) : ℝ)) * Y := by
        simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_add, ENNReal.ofReal_ofNat]
        ring
    _ ≤ _ := by
        gcongr ?_ * _ + ?_ * _
        · refine ENNReal.ofReal_le_ofReal ?_
          have h1 : r0 ≤ max 1 CN * r0 := le_mul_of_one_le_left hr0.le (le_max_left _ _)
          have hX : 0 ≤ K ^ 2 * ρ ^ (1 / 2 : ℝ) + ρ ^ (3 / 2 : ℝ) := by positivity
          have h2 : NΓ * r0 ^ (-(d : ℝ)) * CN * (K ^ 2 * ρ ^ (1 / 2 : ℝ) + ρ ^ (3 / 2 : ℝ)) ≤
              max 1 CN * (NΓ * r0 ^ (-(d : ℝ)) * (K ^ 2 * ρ ^ (1 / 2 : ℝ) + ρ ^ (3 / 2 : ℝ))) := by
            have : 0 ≤ NΓ * r0 ^ (-(d : ℝ)) * (K ^ 2 * ρ ^ (1 / 2 : ℝ) + ρ ^ (3 / 2 : ℝ)) := by positivity
            nlinarith
          calc 2 * CT ^ 2 * Kcc * KΓ * (r0 + NΓ * r0 ^ (-(d : ℝ)) * CN *
                (K ^ 2 * ρ ^ (1 / 2 : ℝ) + ρ ^ (3 / 2 : ℝ)))
              ≤ 2 * CT ^ 2 * Kcc * KΓ * (max 1 CN * r0 + max 1 CN * (NΓ * r0 ^ (-(d : ℝ)) *
                (K ^ 2 * ρ ^ (1 / 2 : ℝ) + ρ ^ (3 / 2 : ℝ)))) := by gcongr
            _ = _ := by ring
        · refine ENNReal.ofReal_le_ofReal ?_
          have : 0 ≤ 2 * CT ^ 2 * Kcc * KΓ * NΓ * r0 ^ (-(d : ℝ)) * K * ρ ^ (-(1 / 2) : ℝ) := by
            positivity
          calc 2 * CT ^ 2 * CN * Kcc * KΓ * NΓ * r0 ^ (-(d : ℝ)) * K * ρ ^ (-(1 / 2) : ℝ)
              = CN * (2 * CT ^ 2 * Kcc * KΓ * NΓ * r0 ^ (-(d : ℝ)) * K * ρ ^ (-(1 / 2) : ℝ)) := by ring
            _ ≤ max 1 CN * (2 * CT ^ 2 * Kcc * KΓ * NΓ * r0 ^ (-(d : ℝ)) * K * ρ ^ (-(1 / 2) : ℝ)) := by
                gcongr
            _ = _ := by ring

end




section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

/-- Parameter facts for `u = θ/(C₁Z²)`. -/
lemma aux_tight_subharmonic_u_facts {C1 θ Z h sl : ℝ} (hC1 : 1 ≤ C1) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hZ : 1 ≤ Z)
    (hZh : 1 ≤ Z * h) (hZsl : 1 ≤ Z * sl) :
    0 < θ / (C1 * Z ^ 2) ∧ Z ^ 2 * (θ / (C1 * Z ^ 2)) = θ / C1 ∧ Z * (θ / (C1 * Z ^ 2)) ≤ 1 ∧
      θ / (C1 * Z ^ 2) ≤ 1 ∧ θ / (C1 * Z ^ 2) ≤ h ∧ θ / (C1 * Z ^ 2) ≤ sl := by
  have hZ0 : 0 < Z := by linarith
  have hC1pos : 0 < C1 := by linarith
  set u : ℝ := θ / (C1 * Z ^ 2) with hu
  have hu0 : 0 < u := by positivity
  have hZ2u : Z ^ 2 * u = θ / C1 := by rw [hu]; field_simp
  have hZ2u1 : Z ^ 2 * u ≤ 1 := by
    rw [hZ2u, div_le_one hC1pos]; linarith
  have hZu : Z * u ≤ 1 := by
    have : Z * u ≤ Z ^ 2 * u := by
      apply mul_le_mul_of_nonneg_right _ hu0.le; nlinarith
    linarith
  have hu1 : u ≤ 1 := by
    have : u ≤ Z * u := le_mul_of_one_le_left hu0.le hZ
    linarith
  have huh : u ≤ h := by
    by_contra hcon; push_neg at hcon
    have : Z * h < Z * u := mul_lt_mul_of_pos_left hcon hZ0
    linarith
  have husl : u ≤ sl := by
    by_contra hcon; push_neg at hcon
    have : Z * sl < Z * u := mul_lt_mul_of_pos_left hcon hZ0
    linarith
  exact ⟨hu0, hZ2u, hZu, hu1, huh, husl⟩

lemma aux_tight_subharmonic_coef_theta {d : ℕ} {C C1 Kcc KΓ NΓ K Z θ u v : ℝ} (hC : 0 < C) (hC1 : C1 = 2 * C + 1)
    (hKcc : 0 ≤ Kcc) (hKΓ : 0 < KΓ) (hNΓ : 0 ≤ NΓ) (hK : 0 < K) (hZ : 1 ≤ Z) (hθ : 0 < θ)
    (hKccZ : Kcc ≤ Z) (hKZ : K ≤ Z) (hKΓZ : KΓ ≤ Z) (hNΓZ : NΓ ≤ Z)
    (hu0 : 0 < u) (hZ2u : Z ^ 2 * u = θ / C1) (hZu : Z * u ≤ 1) (hu1 : u ≤ 1)
    (hv : v = u ^ (d + 6) / 2) (hv1 : v ≤ u / 2) :
    C * Kcc * KΓ * (u + NΓ * (u ^ d)⁻¹ * (K ^ 2 * v + v ^ 3)) ≤ θ := by
  have hZ0 : 0 < Z := by linarith
  have hC1pos : 0 < C1 := by rw [hC1]; positivity
  have hv0 : 0 < v := by rw [hv]; positivity
  have hud0 : 0 < u ^ d := by positivity
  have hv3 : v ^ 3 ≤ v := by
    have : v ≤ 1 := by linarith
    calc v ^ 3 ≤ v ^ 1 := pow_le_pow_of_le_one hv0.le this (by norm_num)
      _ = v := pow_one v
  have hK2 : K ^ 2 ≤ Z ^ 2 := by gcongr
  have hsum : K ^ 2 * v + v ^ 3 ≤ 2 * Z ^ 2 * v := by
    have h1 : K ^ 2 * v ≤ Z ^ 2 * v := mul_le_mul_of_nonneg_right hK2 hv0.le
    have h2 : v ≤ Z ^ 2 * v := le_mul_of_one_le_left hv0.le (one_le_pow₀ hZ)
    linarith
  have hKK : Kcc * KΓ ≤ Z ^ 2 := by
    rw [sq]; exact mul_le_mul hKccZ hKΓZ hKΓ.le hZ0.le
  have hvu : (u ^ d)⁻¹ * v = u ^ 6 / 2 := by
    rw [hv, pow_add]; field_simp
  have h6 : Z ^ 5 * u ^ 6 ≤ Z ^ 2 * u := by
    have h1 : (Z * u) ^ 3 ≤ 1 := pow_le_one₀ (by positivity) hZu
    have h2 : u ^ 2 ≤ 1 := pow_le_one₀ hu0.le hu1
    have e : Z ^ 5 * u ^ 6 = (Z ^ 2 * u) * ((Z * u) ^ 3 * u ^ 2) := by ring
    rw [e]
    have h3 : (Z * u) ^ 3 * u ^ 2 ≤ 1 := by
      calc (Z * u) ^ 3 * u ^ 2 ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) (by norm_num)
        _ = 1 := by norm_num
    calc Z ^ 2 * u * ((Z * u) ^ 3 * u ^ 2) ≤ Z ^ 2 * u * 1 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = Z ^ 2 * u := mul_one _
  have hCC1 : C / C1 ≤ 1 / 2 := by rw [div_le_iff₀ hC1pos, hC1]; linarith
  calc C * Kcc * KΓ * (u + NΓ * (u ^ d)⁻¹ * (K ^ 2 * v + v ^ 3))
      ≤ C * Z ^ 2 * (u + Z * (u ^ d)⁻¹ * (2 * Z ^ 2 * v)) := by
        rw [mul_assoc C Kcc KΓ]
        gcongr
    _ = C * (Z ^ 2 * u) + C * (Z ^ 5 * ((u ^ d)⁻¹ * v) * 2) := by ring
    _ = C * (Z ^ 2 * u) + C * (Z ^ 5 * u ^ 6) := by rw [hvu]; ring
    _ ≤ C * (Z ^ 2 * u) + C * (Z ^ 2 * u) := by gcongr
    _ = 2 * (C / C1) * θ := by rw [hZ2u]; ring
    _ ≤ 2 * (1 / 2) * θ := by gcongr
    _ = θ := by ring

lemma aux_tight_subharmonic_coef_Y {d : ℕ} {C C1 Kcc KΓ NΓ K Z θ u v : ℝ} (hC : 0 < C) (hC1 : 0 < C1)
    (hKcc : 0 ≤ Kcc) (hKΓ : 0 < KΓ) (hNΓ : 0 ≤ NΓ) (hK : 0 < K) (hZ : 1 ≤ Z) (hθ : 0 < θ)
    (hKccZ : Kcc ≤ Z) (hKZ : K ≤ Z) (hKΓZ : KΓ ≤ Z) (hNΓZ : NΓ ≤ Z)
    (hu0 : 0 < u) (hu : u = θ / (C1 * Z ^ 2)) (hZu : Z * u ≤ 1)
    (hv : v = u ^ (d + 6) / 2) :
    C * Kcc * KΓ * NΓ * (u ^ d)⁻¹ * K * v⁻¹ ≤
      2 * C * C1 ^ (2 * d + 10) * (Z ^ 2 / θ) ^ (2 * d + 10) := by
  have hZ0 : 0 < Z := by linarith
  have hud0 : 0 < u ^ d := by positivity
  have hv0 : 0 < v := by rw [hv]; positivity
  have hZ4 : Z ^ 4 * u ^ 4 ≤ 1 := by
    rw [← mul_pow]; exact pow_le_one₀ (by positivity) hZu
  have hinvu : u⁻¹ = C1 * Z ^ 2 / θ := by rw [hu]; field_simp
  have hprod : Kcc * KΓ * NΓ * K ≤ Z ^ 4 := by
    have := mul_le_mul (mul_le_mul hKccZ hKΓZ hKΓ.le hZ0.le) (mul_le_mul hNΓZ hKZ hK.le hZ0.le)
      (by positivity) (by positivity)
    calc Kcc * KΓ * NΓ * K = (Kcc * KΓ) * (NΓ * K) := by ring
      _ ≤ (Z * Z) * (Z * Z) := this
      _ = Z ^ 4 := by ring
  have hsplit : (u ^ d)⁻¹ * v⁻¹ = 2 * u ^ 4 * (u⁻¹) ^ (2 * d + 10) := by
    rw [hv, inv_pow]; field_simp; ring
  calc C * Kcc * KΓ * NΓ * (u ^ d)⁻¹ * K * v⁻¹
      = C * (Kcc * KΓ * NΓ * K) * ((u ^ d)⁻¹ * v⁻¹) := by ring
    _ ≤ C * Z ^ 4 * ((u ^ d)⁻¹ * v⁻¹) := by gcongr
    _ = 2 * C * (Z ^ 4 * u ^ 4) * (u⁻¹) ^ (2 * d + 10) := by rw [hsplit]; ring
    _ ≤ 2 * C * 1 * (u⁻¹) ^ (2 * d + 10) := by gcongr
    _ = 2 * C * C1 ^ (2 * d + 10) * (Z ^ 2 / θ) ^ (2 * d + 10) := by
        rw [hinvu, mul_div_assoc, mul_pow]; ring

/-- Normalized hole-filling step: one size parameter `Z` dominates all data, the free scales are
fixed as `r0 = u = θ/(C₁Z²)` and `ρ = (u^{d+6}/2)²`. -/
theorem aux_tight_subharmonic_hole_step_Z {d : ℕ} : ∃ C : ℝ, 0 < C ∧ ∀ (μ Γ : Measure (Fin d → ℝ)) [SFinite μ]
    (g : (Fin d → ℝ) → ℝ) (Mg K KΓ NΓ Kcc Rmax r h θ Z : ℝ),
    Measurable g → (∀ x, |g x| ≤ Mg) → 0 < K → 0 < KΓ → 0 ≤ NΓ → 0 ≤ Kcc → 0 < h → 0 ≤ r →
    0 < θ → θ ≤ 1 → 1 ≤ Z → Kcc ≤ Z → K ≤ Z → KΓ ≤ Z → NΓ ≤ Z → 1 ≤ Z * h →
    1 ≤ Z * (Rmax - (r + 3 * h)) →
    μ ≪ volume →
    (∀ x ρ', 0 < ρ' → ρ' ≤ 1 → ball x ρ' ⊆ ball 0 Rmax →
      ENNReal.ofReal (K⁻¹ * ρ' ^ ((d : ℝ) + 1 / 2)) ≤ μ (ball x ρ') ∧
        μ (ball x ρ') ≤ ENNReal.ofReal (K * ρ' ^ ((d : ℝ) - 1 / 2))) →
    Γ ≪ volume → Γ (ball 0 (r + h))ᶜ = 0 → Γ Set.univ ≤ ENNReal.ofReal (NΓ * KΓ) →
    (∀ x ρ', 0 < ρ' → ρ' ≤ 1 → Γ (ball x ρ') ≤ ENNReal.ofReal (KΓ * ρ' ^ ((d : ℝ) - 1 / 2))) →
    aux_tight_subharmonic_fE g (ball 0 r) ≤ ENNReal.ofReal Kcc * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂Γ →
    aux_tight_subharmonic_fE g (ball 0 r) ≤ ENNReal.ofReal θ * aux_tight_subharmonic_fE g (ball 0 (r + 3 * h)) +
        ENNReal.ofReal (C * (Z ^ 2 / θ) ^ (2 * d + 10)) *
          ∫⁻ x in ball 0 (r + 3 * h), ENNReal.ofReal (g x ^ 2) ∂μ := by
  obtain ⟨C, hC, hs⟩ := aux_tight_subharmonic_hole_step (d := d)
  set C1 : ℝ := 2 * C + 1 with hC1
  have hC1pos : 0 < C1 := by positivity
  refine ⟨2 * C * C1 ^ (2 * d + 10), by positivity, ?_⟩
  intro μ Γ _ g Mg K KΓ NΓ Kcc Rmax r h θ Z hg hgb hK hKΓ hNΓ hKcc hh hr hθ hθ1 hZ hKccZ hKZ
    hKΓZ hNΓZ hZh hZsl hac hmass hΓac hΓsupp hΓtot hΓup hcc
  obtain ⟨hu0, hZ2u, hZu, hu1, huh, husl⟩ :=
    aux_tight_subharmonic_u_facts (C1 := C1) (by rw [hC1]; linarith) hθ hθ1 hZ hZh hZsl
  set u : ℝ := θ / (C1 * Z ^ 2) with hu
  set v : ℝ := u ^ (d + 6) / 2 with hv
  have hv0 : 0 < v := by positivity
  have hv1 : v ≤ u / 2 := by
    rw [hv]; gcongr; exact pow_le_of_le_one hu0.le hu1 (by omega)
  set ρ : ℝ := v ^ 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρu : ρ ≤ u / 4 := by
    have h1 : ρ ≤ (u / 2) ^ 2 := by rw [hρ]; gcongr
    have h2 : (u / 2) ^ 2 ≤ u / 4 := by nlinarith
    linarith
  have hρhalf : ρ ^ (1 / 2 : ℝ) = v := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hv0.le]; norm_num
  have hρ32 : ρ ^ (3 / 2 : ℝ) = v ^ 3 := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hv0.le]; norm_num
  have hρm : ρ ^ (-(1 / 2) : ℝ) = v⁻¹ := by
    rw [Real.rpow_neg hρ0.le, hρhalf]
  have hud : u ^ (-(d : ℝ)) = (u ^ d)⁻¹ := by rw [Real.rpow_neg hu0.le, Real.rpow_natCast]
  have hR : r + 3 * h + ρ ≤ Rmax := by linarith
  have h3ρ : 3 * ρ ≤ h := by linarith
  have hρ1 : ρ ≤ 1 := by linarith
  have hmain := hs μ Γ g Mg K KΓ NΓ Kcc Rmax r h u ρ hg hgb hK hKΓ hNΓ hKcc hh hr
    hR hu0 huh hu1 hρ0 h3ρ hρ1 hac hmass hΓac hΓsupp hΓtot hΓup hcc
  clear hs
  rw [hρhalf, hρ32, hρm, hud] at hmain
  refine hmain.trans (add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl))
  · exact aux_tight_subharmonic_coef_theta hC hC1 hKcc hKΓ hNΓ hK hZ hθ hKccZ hKZ hKΓZ hNΓZ hu0 hZ2u hZu hu1 hv hv1
  · exact aux_tight_subharmonic_coef_Y hC hC1pos hKcc hKΓ hNΓ hK hZ hθ hKccZ hKZ hKΓZ hNΓZ hu0 hu hZu hv

end




section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

/-- Two-sided mass bounds for `μ` on balls of radius `≤ 1` inside `ball 0 Rmax`. -/
def aux_tight_subharmonic_MassBd {d : ℕ} (μ : Measure (Fin d → ℝ)) (K Rmax : ℝ) : Prop :=
  ∀ x ρ', 0 < ρ' → ρ' ≤ 1 → ball x ρ' ⊆ ball (0 : Fin d → ℝ) Rmax →
    ENNReal.ofReal (K⁻¹ * ρ' ^ ((d : ℝ) + 1 / 2)) ≤ μ (ball x ρ') ∧
      μ (ball x ρ') ≤ ENNReal.ofReal (K * ρ' ^ ((d : ℝ) - 1 / 2))

/-- The cutoff family between rational radii in `[qlo, qhi]`, each with the
Caccioppoli–coercivity inequality (CC) for `g`. -/
def aux_tight_subharmonic_CutFam {d : ℕ} (g : (Fin d → ℝ) → ℝ) (K B ρ0 Kcc : ℝ) (qlo qhi : ℚ) : Prop :=
  ∀ q q' : ℚ, qlo ≤ q → q < q' → q' ≤ qhi → ∃ Γ : Measure (Fin d → ℝ),
    Γ ≪ volume ∧ Γ (ball 0 (ρ0 * (q' : ℝ) / 2))ᶜ = 0 ∧
    (∀ x ρ', 0 < ρ' → ρ' ≤ 1 →
      Γ (ball x ρ') ≤ ENNReal.ofReal (K * (ρ0 * ((q' : ℝ) - q) / 2) ^ (-B) *
        ρ' ^ ((d : ℝ) - 1 / 2))) ∧
    aux_tight_subharmonic_fE g (ball 0 (ρ0 * (q : ℝ) / 2)) ≤ ENNReal.ofReal Kcc * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂Γ

lemma aux_tight_subharmonic_fE_mono {d : ℕ} (g : (Fin d → ℝ) → ℝ) {U V : Set (Fin d → ℝ)} (h : U ⊆ V) :
    aux_tight_subharmonic_fE g U ≤ aux_tight_subharmonic_fE g V :=
  add_le_add (aux_tight_subharmonic_gag_mono g h) (lintegral_mono_set h)

/-- Total mass of a cutoff measure by the unit-ball cover. -/
lemma aux_tight_subharmonic_cut_total {d : ℕ} (Γ : Measure (Fin d → ℝ)) {R KΓ ρ0 : ℝ} (hR : 0 ≤ R) (hRρ : R ≤ ρ0 / 2)
    (hKΓ : 0 ≤ KΓ) (hsupp : Γ (ball 0 R)ᶜ = 0)
    (hup : ∀ x ρ', 0 < ρ' → ρ' ≤ 1 → Γ (ball x ρ') ≤ ENNReal.ofReal (KΓ * ρ' ^ ((d : ℝ) - 1 / 2))) :
    Γ Set.univ ≤ ENNReal.ofReal ((((2 * ⌈ρ0 / 2⌉₊ + 1) ^ d : ℕ) : ℝ) * KΓ) := by
  have h1 : Γ Set.univ = Γ (ball 0 R) := by
    rw [← measure_add_measure_compl (measurableSet_ball (x := (0 : Fin d → ℝ)) (ε := R)), hsupp,
      add_zero]
  rw [h1]
  have hc := aux_tight_subharmonic_cover_ball Γ hR one_pos (M := ENNReal.ofReal KΓ)
    (fun c _ ↦ (hup c 1 one_pos le_rfl).trans (by rw [Real.one_rpow, mul_one]))
  refine hc.trans ?_
  have hceil : ⌈R / 1⌉₊ ≤ ⌈ρ0 / 2⌉₊ := by rw [div_one]; exact Nat.ceil_mono hRρ
  have hN : (((2 * ⌈R / 1⌉₊ + 1) ^ d : ℕ) : ℝ≥0∞) ≤ (((2 * ⌈ρ0 / 2⌉₊ + 1) ^ d : ℕ) : ℝ≥0∞) := by
    exact_mod_cast Nat.pow_le_pow_left (by omega) d
  calc (((2 * ⌈R / 1⌉₊ + 1) ^ d : ℕ) : ℝ≥0∞) * ENNReal.ofReal KΓ
      ≤ (((2 * ⌈ρ0 / 2⌉₊ + 1) ^ d : ℕ) : ℝ≥0∞) * ENNReal.ofReal KΓ := by gcongr
    _ = ENNReal.ofReal ((((2 * ⌈ρ0 / 2⌉₊ + 1) ^ d : ℕ) : ℝ) * KΓ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

/-- The dyadic radii of the hole filling. -/
def aux_tight_subharmonic_qseq (qs qe : ℚ) (j : ℕ) : ℚ := qs + (qe - qs) * (1 - 1 / 2 ^ j)

lemma aux_tight_subharmonic_qseq_facts (ρ0 : ℝ) {qs qe : ℚ} (hq : qs < qe) (j : ℕ) :
    ρ0 * (aux_tight_subharmonic_qseq qs qe (j + 1) : ℝ) / 2 = ρ0 * (aux_tight_subharmonic_qseq qs qe j : ℝ) / 2 + 3 * (ρ0 * (qe - qs) / 12 / 2 ^ j) ∧
    ρ0 * ((aux_tight_subharmonic_qseq qs qe j + (aux_tight_subharmonic_qseq qs qe (j + 1) - aux_tight_subharmonic_qseq qs qe j) / 3 : ℚ) : ℝ) / 2 =
      ρ0 * (aux_tight_subharmonic_qseq qs qe j : ℝ) / 2 + ρ0 * (qe - qs) / 12 / 2 ^ j ∧
    ρ0 * (((aux_tight_subharmonic_qseq qs qe j + (aux_tight_subharmonic_qseq qs qe (j + 1) - aux_tight_subharmonic_qseq qs qe j) / 3 : ℚ) : ℝ) - (aux_tight_subharmonic_qseq qs qe j : ℝ)) / 2 =
      ρ0 * (qe - qs) / 12 / 2 ^ j ∧
    qs ≤ aux_tight_subharmonic_qseq qs qe j ∧ aux_tight_subharmonic_qseq qs qe j < aux_tight_subharmonic_qseq qs qe j + (aux_tight_subharmonic_qseq qs qe (j + 1) - aux_tight_subharmonic_qseq qs qe j) / 3 ∧
    aux_tight_subharmonic_qseq qs qe (j + 1) ≤ qe ∧ aux_tight_subharmonic_qseq qs qe j + (aux_tight_subharmonic_qseq qs qe (j + 1) - aux_tight_subharmonic_qseq qs qe j) / 3 ≤ qe := by
  have hd : 0 < qe - qs := sub_pos.2 hq
  have hdiff : aux_tight_subharmonic_qseq qs qe (j + 1) - aux_tight_subharmonic_qseq qs qe j = (qe - qs) / 2 ^ (j + 1) := by
    simp only [aux_tight_subharmonic_qseq]; field_simp; ring
  have hpos : 0 < aux_tight_subharmonic_qseq qs qe (j + 1) - aux_tight_subharmonic_qseq qs qe j := by rw [hdiff]; positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [aux_tight_subharmonic_qseq]; push_cast; field_simp; ring
  · simp only [aux_tight_subharmonic_qseq]; push_cast; field_simp; ring
  · simp only [aux_tight_subharmonic_qseq]; push_cast; field_simp; ring
  · simp only [aux_tight_subharmonic_qseq]
    have : (0 : ℚ) ≤ 1 - 1 / 2 ^ j := by
      rw [sub_nonneg, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    nlinarith
  · linarith
  · simp only [aux_tight_subharmonic_qseq]
    have : (0 : ℚ) < 1 / 2 ^ (j + 1) := by positivity
    nlinarith
  · have h1 : aux_tight_subharmonic_qseq qs qe (j + 1) ≤ qe := by
      simp only [aux_tight_subharmonic_qseq]
      have : (0 : ℚ) < 1 / 2 ^ (j + 1) := by positivity
      nlinarith
    linarith

lemma aux_tight_subharmonic_rpow_le_natpow {x B : ℝ} {n : ℕ} (hx : 1 ≤ x) (hB : B ≤ n) : x ^ B ≤ x ^ n := by
  rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hx hB

/-- Size parameter bounds at step `j` of the hole filling. -/
lemma aux_tight_subharmonic_Zj_facts {K Kcc NΓ h0 sl B : ℝ} {nB : ℕ} (hK : 1 ≤ K) (hKcc : 1 ≤ Kcc) (hNΓ : 0 ≤ NΓ)
    (hh0 : 0 < h0) (hsl : 0 < sl) (hB : 0 < B) (hnB : B ≤ nB) (hnB1 : 1 ≤ nB) (j : ℕ) :
    1 ≤ Kcc * K * (NΓ + 1) * (1 + 1 / h0) ^ nB * (1 + 1 / sl) * 2 ^ (j * nB) ∧
    Kcc ≤ Kcc * K * (NΓ + 1) * (1 + 1 / h0) ^ nB * (1 + 1 / sl) * 2 ^ (j * nB) ∧
    K ≤ Kcc * K * (NΓ + 1) * (1 + 1 / h0) ^ nB * (1 + 1 / sl) * 2 ^ (j * nB) ∧
    K * (h0 / 2 ^ j) ^ (-B) ≤ Kcc * K * (NΓ + 1) * (1 + 1 / h0) ^ nB * (1 + 1 / sl) * 2 ^ (j * nB) ∧
    NΓ ≤ Kcc * K * (NΓ + 1) * (1 + 1 / h0) ^ nB * (1 + 1 / sl) * 2 ^ (j * nB) ∧
    1 ≤ Kcc * K * (NΓ + 1) * (1 + 1 / h0) ^ nB * (1 + 1 / sl) * 2 ^ (j * nB) * (h0 / 2 ^ j) ∧
    ∀ s', sl ≤ s' → 1 ≤ Kcc * K * (NΓ + 1) * (1 + 1 / h0) ^ nB * (1 + 1 / sl) * 2 ^ (j * nB) * s' := by
  set a : ℝ := 1 + 1 / h0 with ha
  set b : ℝ := 1 + 1 / sl with hb
  have ha1 : 1 ≤ a := by rw [ha]; linarith [one_div_pos.2 hh0]
  have hb1 : 1 ≤ b := by rw [hb]; linarith [one_div_pos.2 hsl]
  have han : 1 ≤ a ^ nB := one_le_pow₀ ha1
  have h2 : (1 : ℝ) ≤ 2 ^ (j * nB) := one_le_pow₀ (by norm_num)
  have hN1 : 1 ≤ NΓ + 1 := by linarith
  set Z := Kcc * K * (NΓ + 1) * a ^ nB * b * 2 ^ (j * nB) with hZ
  have hrest : 1 ≤ (NΓ + 1) * a ^ nB * b * 2 ^ (j * nB) := by
    have := mul_le_mul (mul_le_mul (mul_le_mul hN1 han zero_le_one (by positivity)) hb1 zero_le_one
      (by positivity)) h2 zero_le_one (by positivity)
    simpa using this
  have hZK : Z = (Kcc * K) * ((NΓ + 1) * a ^ nB * b * 2 ^ (j * nB)) := by rw [hZ]; ring
  have hKK : 1 ≤ Kcc * K := one_le_mul_of_one_le_of_one_le hKcc hK
  have hZ1 : 1 ≤ Z := by rw [hZK]; exact one_le_mul_of_one_le_of_one_le hKK hrest
  have hKccZ : Kcc ≤ Z := by
    rw [hZK]
    calc Kcc = Kcc * 1 * 1 := by ring
      _ ≤ Kcc * K * ((NΓ + 1) * a ^ nB * b * 2 ^ (j * nB)) := by gcongr
  have hKZ : K ≤ Z := by
    rw [hZK]
    calc K = 1 * K * 1 := by ring
      _ ≤ Kcc * K * ((NΓ + 1) * a ^ nB * b * 2 ^ (j * nB)) := by gcongr
  have hNZ : NΓ ≤ Z := by
    have : NΓ ≤ (NΓ + 1) * a ^ nB * b * 2 ^ (j * nB) := by
      have h3 : 1 ≤ a ^ nB * b * 2 ^ (j * nB) := by
        have := mul_le_mul (mul_le_mul han hb1 zero_le_one (by positivity)) h2 zero_le_one
          (by positivity)
        simpa using! this
      nlinarith
    rw [hZK]; nlinarith
  have hpow2 : ((2 : ℝ) ^ j) ^ B ≤ 2 ^ (j * nB) := by
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    calc ((2 : ℝ) ^ j) ^ B ≤ ((2 : ℝ) ^ j) ^ nB := aux_tight_subharmonic_rpow_le_natpow h2j hnB
      _ = 2 ^ (j * nB) := by rw [← pow_mul]
  have hinvh : (1 / h0) ^ B ≤ a ^ nB := by
    calc (1 / h0) ^ B ≤ a ^ B := Real.rpow_le_rpow (by positivity) (by rw [ha]; linarith) hB.le
      _ ≤ a ^ nB := aux_tight_subharmonic_rpow_le_natpow ha1 hnB
  have hKΓ : K * (h0 / 2 ^ j) ^ (-B) ≤ Z := by
    have e : (h0 / 2 ^ j) ^ (-B) = ((2 : ℝ) ^ j) ^ B * (1 / h0) ^ B := by
      rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div,
        div_eq_mul_one_div, Real.mul_rpow (by positivity) (by positivity)]
    rw [e, hZK]
    calc K * (((2 : ℝ) ^ j) ^ B * (1 / h0) ^ B) ≤ K * (2 ^ (j * nB) * a ^ nB) := by gcongr
      _ = 1 * K * (1 * a ^ nB * 1 * 2 ^ (j * nB)) := by ring
      _ ≤ Kcc * K * ((NΓ + 1) * a ^ nB * b * 2 ^ (j * nB)) := by gcongr
  have hZh : 1 ≤ Z * (h0 / 2 ^ j) := by
    have h2j : (0 : ℝ) < 2 ^ j := by positivity
    have hjn : (2 : ℝ) ^ j ≤ 2 ^ (j * nB) := by
      apply pow_le_pow_right₀ (by norm_num); nlinarith
    have hah : 1 ≤ a * h0 := by rw [ha]; field_simp; linarith
    calc (1 : ℝ) ≤ a * h0 := hah
      _ ≤ a ^ nB * h0 := by
          gcongr; calc a = a ^ 1 := (pow_one a).symm
            _ ≤ a ^ nB := pow_le_pow_right₀ ha1 hnB1
      _ = (1 * 1 * 1 * a ^ nB * 1 * 2 ^ j) * (h0 / 2 ^ j) := by field_simp
      _ ≤ (Kcc * K * (NΓ + 1) * a ^ nB * b * 2 ^ (j * nB)) * (h0 / 2 ^ j) := by gcongr
  refine ⟨hZ1, hKccZ, hKZ, hKΓ, hNZ, hZh, fun s' hs' ↦ ?_⟩
  have hbs : 1 ≤ b * sl := by rw [hb]; field_simp; linarith
  have hbZ : b ≤ Z := by
    rw [hZK]
    calc b = 1 * 1 * (1 * 1 * b * 1) := by ring
      _ ≤ Kcc * K * ((NΓ + 1) * a ^ nB * b * 2 ^ (j * nB)) := by gcongr
  have hsl' : 0 ≤ s' := by linarith
  calc (1 : ℝ) ≤ b * sl := hbs
    _ ≤ b * s' := by gcongr
    _ ≤ Z * s' := mul_le_mul_of_nonneg_right hbZ hsl'

end




section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

/-- The content of `aux_tight_subharmonic_hole_step_Z` for a given constant. -/
def aux_tight_subharmonic_HoleSpec (d : ℕ) (C : ℝ) : Prop :=
  ∀ (μ Γ : Measure (Fin d → ℝ)) [SFinite μ]
    (g : (Fin d → ℝ) → ℝ) (Mg K KΓ NΓ Kcc Rmax r h θ Z : ℝ),
    Measurable g → (∀ x, |g x| ≤ Mg) → 0 < K → 0 < KΓ → 0 ≤ NΓ → 0 ≤ Kcc → 0 < h → 0 ≤ r →
    0 < θ → θ ≤ 1 → 1 ≤ Z → Kcc ≤ Z → K ≤ Z → KΓ ≤ Z → NΓ ≤ Z → 1 ≤ Z * h →
    1 ≤ Z * (Rmax - (r + 3 * h)) →
    μ ≪ volume →
    (∀ x ρ', 0 < ρ' → ρ' ≤ 1 → ball x ρ' ⊆ ball 0 Rmax →
      ENNReal.ofReal (K⁻¹ * ρ' ^ ((d : ℝ) + 1 / 2)) ≤ μ (ball x ρ') ∧
        μ (ball x ρ') ≤ ENNReal.ofReal (K * ρ' ^ ((d : ℝ) - 1 / 2))) →
    Γ ≪ volume → Γ (ball 0 (r + h))ᶜ = 0 → Γ Set.univ ≤ ENNReal.ofReal (NΓ * KΓ) →
    (∀ x ρ', 0 < ρ' → ρ' ≤ 1 → Γ (ball x ρ') ≤ ENNReal.ofReal (KΓ * ρ' ^ ((d : ℝ) - 1 / 2))) →
    aux_tight_subharmonic_fE g (ball 0 r) ≤ ENNReal.ofReal Kcc * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂Γ →
    aux_tight_subharmonic_fE g (ball 0 r) ≤ ENNReal.ofReal θ * aux_tight_subharmonic_fE g (ball 0 (r + 3 * h)) +
        ENNReal.ofReal (C * (Z ^ 2 / θ) ^ (2 * d + 10)) *
          ∫⁻ x in ball 0 (r + 3 * h), ENNReal.ofReal (g x ^ 2) ∂μ

lemma aux_tight_subharmonic_hole_step_Z' {d : ℕ} : ∃ C : ℝ, 0 < C ∧ aux_tight_subharmonic_HoleSpec d C := aux_tight_subharmonic_hole_step_Z

lemma aux_tight_subharmonic_pow_rescale (C Z0 θ : ℝ) (j nB β : ℕ) :
    C * ((Z0 * 2 ^ (j * nB)) ^ 2 / θ) ^ β = C * (Z0 ^ 2 / θ) ^ β * ((4 : ℝ) ^ (nB * β)) ^ j := by
  have h4 : ((2 : ℝ) ^ (j * nB)) ^ 2 = (4 : ℝ) ^ (j * nB) := by
    rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  rw [mul_pow, h4, mul_div_right_comm, mul_pow, ← pow_mul, ← pow_mul]
  ring_nf

lemma aux_tight_subharmonic_sq_le_of_abs {a M : ℝ} (h : |a| ≤ M) : a ^ 2 ≤ M ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg a) h 2

/-- One step of the dyadic hole filling. -/
lemma aux_tight_subharmonic_fill_step {d : ℕ} {C' B ρ0 : ℝ} (hZs : aux_tight_subharmonic_HoleSpec d C') (hB : 0 < B) (hρ0 : 0 < ρ0)
    (μ : Measure (Fin d → ℝ)) [SFinite μ] (g : (Fin d → ℝ) → ℝ) (Mg K Kcc θ : ℝ)
    (qlo qs qe qhi : ℚ) (hg : Measurable g) (hgb : ∀ x, |g x| ≤ Mg) (hK : 1 ≤ K)
    (hKcc : 1 ≤ Kcc) (hqs0 : 0 ≤ qs) (hlo : qlo ≤ qs) (hse : qs < qe) (hehi : qe < qhi)
    (hhi : qhi ≤ 1) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hac : μ ≪ volume) (hmass : aux_tight_subharmonic_MassBd μ K (ρ0 / 2)) (hfam : aux_tight_subharmonic_CutFam g K B ρ0 Kcc qlo qhi) (j : ℕ) :
    aux_tight_subharmonic_fE g (ball 0 (ρ0 * (aux_tight_subharmonic_qseq qs qe j : ℝ) / 2)) ≤
      ENNReal.ofReal θ * aux_tight_subharmonic_fE g (ball 0 (ρ0 * (aux_tight_subharmonic_qseq qs qe (j + 1) : ℝ) / 2)) +
      ENNReal.ofReal (C' * ((Kcc * K * ((((2 * ⌈ρ0 / 2⌉₊ + 1) ^ d : ℕ) : ℝ) + 1) *
          (1 + 1 / (ρ0 * (qe - qs) / 12)) ^ (⌈B⌉₊ + 1) * (1 + 1 / (ρ0 * (1 - qe) / 2)) *
          2 ^ (j * (⌈B⌉₊ + 1))) ^ 2 / θ) ^ (2 * d + 10)) *
        ∫⁻ x in ball 0 (ρ0 * (qe : ℝ) / 2), ENNReal.ofReal (g x ^ 2) ∂μ := by
  obtain ⟨hA, hB', hC'', hq0, hqlt, hq1, hqc⟩ := aux_tight_subharmonic_qseq_facts ρ0 hse j
  set qj := aux_tight_subharmonic_qseq qs qe j with hqj
  set q' := qj + (aux_tight_subharmonic_qseq qs qe (j + 1) - qj) / 3 with hq'
  set h : ℝ := ρ0 * (qe - qs) / 12 / 2 ^ j with hh
  have hqe_qs : (0 : ℝ) < (qe : ℝ) - qs := by exact_mod_cast sub_pos.2 hse
  have hh0 : 0 < h := by rw [hh]; positivity
  obtain ⟨Γ, hΓac, hΓsupp, hΓup, hcc⟩ :=
    hfam qj q' (hlo.trans hq0) hqlt (hqc.trans hehi.le)
  rw [hB'] at hΓsupp
  rw [hC''] at hΓup
  have hq'1 : (q' : ℝ) ≤ 1 := by exact_mod_cast (hqc.trans hehi.le).trans hhi
  have hqj0 : (0 : ℝ) ≤ qj := by exact_mod_cast hqs0.trans hq0
  have hq'0 : (0 : ℝ) ≤ q' := by exact_mod_cast (hqs0.trans hq0).trans hqlt.le
  have hKΓ0 : 0 ≤ K * h ^ (-B) := by positivity
  have htot := aux_tight_subharmonic_cut_total (d := d) Γ (R := ρ0 * q' / 2) (ρ0 := ρ0) (by positivity)
    (by nlinarith) hKΓ0 (by rw [hB']; exact hΓsupp) hΓup
  have hh0' : (0 : ℝ) < ρ0 * (qe - qs) / 12 := by positivity
  have hsl0 : (0 : ℝ) < ρ0 * (1 - qe) / 2 := by
    have : (qe : ℝ) < 1 := by exact_mod_cast hehi.trans_le hhi
    have : (0 : ℝ) < 1 - qe := by linarith
    positivity
  obtain ⟨hZ1, hKccZ, hKZ, hKΓZ, hNZ, hZh, hZsl⟩ :=
    aux_tight_subharmonic_Zj_facts (NΓ := ((((2 * ⌈ρ0 / 2⌉₊ + 1) ^ d : ℕ) : ℝ))) (nB := ⌈B⌉₊ + 1) hK hKcc (by positivity) hh0' hsl0 hB
      (by push_cast; linarith [Nat.le_ceil B]) (by omega) j
  have hslle : ρ0 * (1 - qe) / 2 ≤ ρ0 / 2 - (ρ0 * (qj : ℝ) / 2 + 3 * h) := by
    rw [← hA]
    have : (aux_tight_subharmonic_qseq qs qe (j + 1) : ℝ) ≤ qe := by exact_mod_cast hq1
    nlinarith
  have hstep := hZs μ Γ g Mg K (K * h ^ (-B)) ((((2 * ⌈ρ0 / 2⌉₊ + 1) ^ d : ℕ) : ℝ)) Kcc (ρ0 / 2)
    (ρ0 * (qj : ℝ) / 2) h θ _ hg hgb (by linarith) (by positivity) (by positivity) (by linarith)
    hh0 (by positivity) hθ hθ1 hZ1 hKccZ hKZ hKΓZ hNZ hZh
    (hZsl _ hslle) hac hmass hΓac hΓsupp htot hΓup hcc
  rw [← hA] at hstep
  refine hstep.trans (add_le_add le_rfl (mul_le_mul' le_rfl (lintegral_mono_set ?_)))
  refine ball_subset_ball ?_
  have : (aux_tight_subharmonic_qseq qs qe (j + 1) : ℝ) ≤ qe := by exact_mod_cast hq1
  nlinarith

lemma aux_tight_subharmonic_fE_fin_of_fam {d : ℕ} {g : (Fin d → ℝ) → ℝ} {Mg K B ρ0 Kcc : ℝ} {qlo qe qhi : ℚ}
    (hρ0 : 0 < ρ0) (hgb : ∀ x, |g x| ≤ Mg) (hK : 0 ≤ K) (hlo : qlo ≤ qe) (hehi : qe < qhi)
    (hhi : qhi ≤ 1) (hqe0 : 0 ≤ qe) (hfam : aux_tight_subharmonic_CutFam g K B ρ0 Kcc qlo qhi) :
    aux_tight_subharmonic_fE g (ball 0 (ρ0 * (qe : ℝ) / 2)) ≠ ⊤ := by
  obtain ⟨Γ, _, hΓsupp, hΓup, hcc⟩ := hfam qe ((qe + qhi) / 2) hlo (by linarith) (by linarith)
  have hq1 : (((qe + qhi) / 2 : ℚ) : ℝ) ≤ 1 := by
    have : (qe + qhi) / 2 ≤ 1 := by linarith
    exact_mod_cast this
  have hq0 : (0 : ℝ) ≤ (((qe + qhi) / 2 : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ (qe + qhi) / 2 := by linarith
    exact_mod_cast this
  have hbase : (0 : ℝ) ≤ ρ0 * ((((qe + qhi) / 2 : ℚ) : ℝ) - qe) / 2 := by
    have : (qe : ℝ) ≤ (((qe + qhi) / 2 : ℚ) : ℝ) := by
      have : qe ≤ (qe + qhi) / 2 := by linarith
      exact_mod_cast this
    have : (0 : ℝ) ≤ (((qe + qhi) / 2 : ℚ) : ℝ) - qe := by linarith
    positivity
  have htot := aux_tight_subharmonic_cut_total (d := d) Γ (R := ρ0 * (((qe + qhi) / 2 : ℚ) : ℝ) / 2) (ρ0 := ρ0)
    (by positivity) (by nlinarith) (mul_nonneg hK (Real.rpow_nonneg hbase _)) hΓsupp hΓup
  refine ne_top_of_le_ne_top ?_ hcc
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top ?_
    (lintegral_mono (fun x ↦ ENNReal.ofReal_le_ofReal (aux_tight_subharmonic_sq_le_of_abs (hgb x)))))
  rw [lintegral_const]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top htot)

lemma aux_tight_subharmonic_fill_const (C' D NΓ Kcc K a b : ℝ) (β nB : ℕ) (hD : 0 < D) :
    C' * ((Kcc * K * (NΓ + 1) * a ^ nB * b) ^ 2 / (1 / (2 * D))) ^ β / (1 - 1 / 2) =
      2 * C' * (2 * D) ^ β * (NΓ + 1) ^ (2 * β) * (Kcc * K * a ^ nB * b) ^ (2 * β) := by
  have hX : (Kcc * K * (NΓ + 1) * a ^ nB * b) ^ 2 / (1 / (2 * D)) =
      (2 * D) * ((NΓ + 1) ^ 2 * (Kcc * K * a ^ nB * b) ^ 2) := by
    field_simp
  rw [hX, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  simp only [mul_pow, ← pow_mul]
  ring

/-- **Hole filling** (proof.tex (iv)): the `H^{3/4}`-energy on `ball 0 (ρ0 qs/2)` is bounded by the
`L²(μ)` norm on `ball 0 (ρ0 qe/2)`, polynomially in `Kcc`, `K` and the reciprocal gaps. -/
theorem aux_tight_subharmonic_hole_fill {d : ℕ} (B ρ0 : ℝ) (hB : 0 < B) (hρ0 : 0 < ρ0) : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure (Fin d → ℝ)) [SFinite μ] (g : (Fin d → ℝ) → ℝ) (Mg K Kcc : ℝ)
      (qlo qs qe qhi : ℚ),
      Measurable g → (∀ x, |g x| ≤ Mg) → 1 ≤ K → 1 ≤ Kcc → 0 ≤ qs → qlo ≤ qs → qs < qe →
      qe < qhi → qhi ≤ 1 → μ ≪ volume → aux_tight_subharmonic_MassBd μ K (ρ0 / 2) → aux_tight_subharmonic_CutFam g K B ρ0 Kcc qlo qhi →
      aux_tight_subharmonic_fE g (ball 0 (ρ0 * (qs : ℝ) / 2)) ≤
        ENNReal.ofReal (C * (Kcc * K * (1 + 1 / (ρ0 * (qe - qs) / 12)) ^ (⌈B⌉₊ + 1) *
          (1 + 1 / (ρ0 * (1 - qe) / 2))) ^ (2 * (2 * d + 10))) *
          ∫⁻ x in ball 0 (ρ0 * (qe : ℝ) / 2), ENNReal.ofReal (g x ^ 2) ∂μ := by
  obtain ⟨C', hC', hZs⟩ := aux_tight_subharmonic_hole_step_Z' (d := d)
  set nB : ℕ := ⌈B⌉₊ + 1 with hnB
  set β : ℕ := 2 * d + 10 with hβ
  set D : ℝ := (4 : ℝ) ^ (nB * β) with hD
  set NΓ : ℝ := ((((2 * ⌈ρ0 / 2⌉₊ + 1) ^ d : ℕ) : ℝ)) with hNΓ
  have hD1 : 1 ≤ D := one_le_pow₀ (by norm_num)
  refine ⟨2 * C' * (2 * D) ^ β * (NΓ + 1) ^ (2 * β), by positivity, ?_⟩
  intro μ _ g Mg K Kcc qlo qs qe qhi hg hgb hK hKcc hqs0 hlo hse hehi hhi hac hmass hfam
  set θ : ℝ := 1 / (2 * D) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθD : θ * D = 1 / 2 := by rw [hθ]; field_simp
  have hθ1 : θ < 1 := by
    have : θ ≤ θ * D := le_mul_of_one_le_right hθ0.le hD1
    linarith
  set a : ℝ := 1 + 1 / (ρ0 * (qe - qs) / 12) with ha
  set b : ℝ := 1 + 1 / (ρ0 * (1 - qe) / 2) with hb
  set Z0 : ℝ := Kcc * K * (NΓ + 1) * a ^ nB * b with hZ0
  set M : ℝ := C' * (Z0 ^ 2 / θ) ^ β with hM
  set f : ℕ → ℝ≥0∞ := fun j ↦ aux_tight_subharmonic_fE g (ball 0 (ρ0 * (aux_tight_subharmonic_qseq qs qe j : ℝ) / 2)) with hf
  set Y := ∫⁻ x in ball 0 (ρ0 * (qe : ℝ) / 2), ENNReal.ofReal (g x ^ 2) ∂μ with hY
  have hstep : ∀ j, f j ≤ ENNReal.ofReal θ * f (j + 1) + ENNReal.ofReal (M * D ^ j) * Y := by
    intro j
    have h := aux_tight_subharmonic_fill_step hZs hB hρ0 μ g Mg K Kcc θ qlo qs qe qhi hg hgb hK hKcc hqs0 hlo hse hehi hhi
      hθ0 hθ1.le hac hmass hfam j
    have e := aux_tight_subharmonic_pow_rescale C' Z0 θ j nB β
    rw [e] at h
    exact h
  have hfF : ∀ j, f j ≤ aux_tight_subharmonic_fE g (ball 0 (ρ0 * (qe : ℝ) / 2)) := by
    intro j
    obtain ⟨-, -, -, -, hqlt, -, hqc⟩ := aux_tight_subharmonic_qseq_facts ρ0 hse j
    refine aux_tight_subharmonic_fE_mono g (ball_subset_ball ?_)
    have : (aux_tight_subharmonic_qseq qs qe j : ℝ) ≤ qe := by exact_mod_cast hqlt.le.trans hqc
    nlinarith
  have hF := aux_tight_subharmonic_fE_fin_of_fam hρ0 hgb (by linarith) (hlo.trans hse.le) hehi hhi
    (hqs0.trans hse.le) hfam
  have hM0 : 0 ≤ M := by positivity
  have habs := aux_tight_subharmonic_iter_absorb f _ hF hfF hθ0.le hθ1 (by linarith) (by rw [hθD]; norm_num) hM0 Y hstep
  have hq0 : aux_tight_subharmonic_qseq qs qe 0 = qs := by simp only [aux_tight_subharmonic_qseq, pow_zero, div_one, sub_self, mul_zero, add_zero]
  have hf0 : f 0 = aux_tight_subharmonic_fE g (ball 0 (ρ0 * (qs : ℝ) / 2)) := by rw [hf]; dsimp only; rw [hq0]
  rw [hf0, hθD] at habs
  refine habs.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) le_rfl)
  exact aux_tight_subharmonic_fill_const C' D NΓ Kcc K a b β nB (by positivity)

end




section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

/-- Total `μ`-mass of `ball 0 R` from the upper mass bound at scale `r0`. -/
lemma aux_tight_subharmonic_mass_total {d : ℕ} (μ : Measure (Fin d → ℝ)) {K ρ0 R r0 : ℝ} (hK : 0 < K) (hR : 0 ≤ R)
    (hr0 : 0 < r0) (hr01 : r0 ≤ 1) (hRr : R + 2 * r0 ≤ ρ0 / 2) (hmass : aux_tight_subharmonic_MassBd μ K (ρ0 / 2)) :
    μ (ball 0 R) ≤ ENNReal.ofReal ((ρ0 + 3) ^ d * K * r0 ^ (-(1 / 2 : ℝ))) := by
  have hc := aux_tight_subharmonic_cover_ball μ hR hr0 (M := ENNReal.ofReal (K * r0 ^ ((d : ℝ) - 1 / 2))) (fun c hc ↦
    (hmass c r0 hr0 hr01 (ball_subset_ball' (by rw [dist_zero_right]; linarith))).2)
  refine hc.trans ?_
  have hN : ((2 * ⌈R / r0⌉₊ + 1 : ℕ) : ℝ) ≤ (ρ0 + 3) / r0 := by
    have h1 : (⌈R / r0⌉₊ : ℝ) < R / r0 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : R / r0 ≤ ρ0 / 2 / r0 := by gcongr; linarith
    have h3 : (3 : ℝ) ≤ 3 / r0 := by rw [le_div_iff₀ hr0]; linarith
    push_cast
    calc 2 * (⌈R / r0⌉₊ : ℝ) + 1 ≤ 2 * (ρ0 / 2 / r0) + 3 := by linarith
      _ ≤ 2 * (ρ0 / 2 / r0) + 3 / r0 := by linarith
      _ = (ρ0 + 3) / r0 := by field_simp
  have hρ3 : 0 ≤ ρ0 + 3 := by linarith
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpow : (((2 * ⌈R / r0⌉₊ + 1) ^ d : ℕ) : ℝ) ≤ ((ρ0 + 3) / r0) ^ d := by
    push_cast; exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hN) d
  have hsplit : r0 ^ ((d : ℝ) - 1 / 2) = r0 ^ d * r0 ^ (-(1 / 2 : ℝ)) := by
    rw [sub_eq_add_neg, Real.rpow_add hr0, Real.rpow_natCast]
  calc (((2 * ⌈R / r0⌉₊ + 1) ^ d : ℕ) : ℝ) * (K * r0 ^ ((d : ℝ) - 1 / 2))
      ≤ ((ρ0 + 3) / r0) ^ d * (K * r0 ^ ((d : ℝ) - 1 / 2)) := by gcongr
    _ = (ρ0 + 3) ^ d * K * r0 ^ (-(1 / 2 : ℝ)) := by
        rw [hsplit, div_pow]; field_simp

lemma aux_tight_subharmonic_rpow_inv_le_one_add {x p : ℝ} (hx : 0 ≤ x) (hp : 1 ≤ p) : x ^ (1 / p) ≤ 1 + x := by
  have hp0 : 0 < p := by linarith
  rcases le_or_gt x 1 with h | h
  · have := Real.rpow_le_one hx h (by positivity : (0 : ℝ) ≤ 1 / p); linarith
  · have h1 : x ^ (1 / p) ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h.le (by rw [div_le_one hp0]; exact hp)
    rw [Real.rpow_one] at h1; linarith

/-- Squaring the `L^p` trace bound against the `H^{3/4}` energy. -/
lemma aux_tight_subharmonic_trace_sq_fE {d : ℕ} (ν : Measure (Fin d → ℝ)) (g : (Fin d → ℝ) → ℝ) (U : Set (Fin d → ℝ))
    (p CT a b V0 : ℝ) (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hV0 : 0 ≤ V0) (hCT : 0 ≤ CT)
    (hν : ν Set.univ ≤ ENNReal.ofReal V0)
    (h : SubdiffusiveProcess.RawLp.eLpNorm g (ENNReal.ofReal p) ν ≤ ENNReal.ofReal CT *
      (ENNReal.ofReal a * aux_tight_subharmonic_gag g U ^ (1 / 2 : ℝ) +
        ν Set.univ ^ (1 / p) * ENNReal.ofReal b * SubdiffusiveProcess.RawLp.eLpNorm g 2 (volume.restrict U))) :
    SubdiffusiveProcess.RawLp.eLpNorm g (ENNReal.ofReal p) ν ^ 2 ≤ ENNReal.ofReal ((CT * (a + (1 + V0) * b)) ^ 2) * aux_tight_subharmonic_fE g U := by
  have hhalf : ∀ z : ℝ≥0∞, (z ^ (1 / 2 : ℝ)) ^ 2 = z := fun z ↦ by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have hG : aux_tight_subharmonic_gag g U ^ (1 / 2 : ℝ) ≤ aux_tight_subharmonic_fE g U ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow (aux_tight_subharmonic_gag_le_fE g U) (by norm_num)
  have hL : SubdiffusiveProcess.RawLp.eLpNorm g 2 (volume.restrict U) ≤ aux_tight_subharmonic_fE g U ^ (1 / 2 : ℝ) := by
    have h2 : SubdiffusiveProcess.RawLp.eLpNorm g 2 (volume.restrict U) ^ 2 ≤ aux_tight_subharmonic_fE g U := by
      rw [aux_tight_subharmonic_eLpNorm_two_sq]; exact le_add_self
    calc SubdiffusiveProcess.RawLp.eLpNorm g 2 (volume.restrict U) = (SubdiffusiveProcess.RawLp.eLpNorm g 2 (volume.restrict U) ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      _ ≤ aux_tight_subharmonic_fE g U ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h2 (by norm_num)
  have hp1 : 0 ≤ 1 / p := one_div_nonneg.2 (by linarith)
  have hνp : ν Set.univ ^ (1 / p) ≤ ENNReal.ofReal (1 + V0) := by
    calc ν Set.univ ^ (1 / p) ≤ ENNReal.ofReal V0 ^ (1 / p) :=
          ENNReal.rpow_le_rpow hν hp1
      _ = ENNReal.ofReal (V0 ^ (1 / p)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hV0 hp1]
      _ ≤ ENNReal.ofReal (1 + V0) := ENNReal.ofReal_le_ofReal (aux_tight_subharmonic_rpow_inv_le_one_add hV0 hp)
  have h1 : SubdiffusiveProcess.RawLp.eLpNorm g (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal (CT * (a + (1 + V0) * b)) * aux_tight_subharmonic_fE g U ^ (1 / 2 : ℝ) := by
    refine h.trans ?_
    calc ENNReal.ofReal CT * (ENNReal.ofReal a * aux_tight_subharmonic_gag g U ^ (1 / 2 : ℝ) +
          ν Set.univ ^ (1 / p) * ENNReal.ofReal b * SubdiffusiveProcess.RawLp.eLpNorm g 2 (volume.restrict U))
        ≤ ENNReal.ofReal CT * (ENNReal.ofReal a * aux_tight_subharmonic_fE g U ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (1 + V0) * ENNReal.ofReal b * aux_tight_subharmonic_fE g U ^ (1 / 2 : ℝ)) := by gcongr
      _ = ENNReal.ofReal (CT * (a + (1 + V0) * b)) * aux_tight_subharmonic_fE g U ^ (1 / 2 : ℝ) := by
          rw [ENNReal.ofReal_mul hCT, ENNReal.ofReal_add ha (by positivity),
            ENNReal.ofReal_mul (by positivity)]
          ring
  calc SubdiffusiveProcess.RawLp.eLpNorm g (ENNReal.ofReal p) ν ^ 2
      ≤ (ENNReal.ofReal (CT * (a + (1 + V0) * b)) * aux_tight_subharmonic_fE g U ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = ENNReal.ofReal ((CT * (a + (1 + V0) * b)) ^ 2) * aux_tight_subharmonic_fE g U := by
        rw [mul_pow, hhalf, ENNReal.ofReal_pow (by positivity)]

lemma aux_tight_subharmonic_gain_lin {d : ℕ} {ρ0 K G a b V0 : ℝ} (hρ0 : 0 < ρ0) (hK : 1 ≤ K) (hG : 1 ≤ G) (ha : a ≤ K)
    (hb0 : 0 ≤ b) (hb : b ≤ (16 * G) ^ d) (hV0 : V0 ≤ (ρ0 + 3) ^ d * K * (16 * G)) :
    a + (1 + V0) * b ≤ (1 + 16 ^ d + (ρ0 + 3) ^ d * 16 ^ (d + 1)) * K * G ^ (d + 1) := by
  have hG0 : 0 < G := by linarith
  have hGd : G ^ d ≤ G ^ (d + 1) := pow_le_pow_right₀ hG (by omega)
  have hKG : 1 ≤ K * G ^ (d + 1) := one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hG)
  have h1 : a ≤ K * G ^ (d + 1) := ha.trans (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hG))
  have h2 : b ≤ 16 ^ d * (K * G ^ (d + 1)) := by
    calc b ≤ (16 * G) ^ d := hb
      _ = 16 ^ d * G ^ d := mul_pow _ _ _
      _ ≤ 16 ^ d * (1 * G ^ (d + 1)) := by rw [one_mul]; gcongr
      _ ≤ 16 ^ d * (K * G ^ (d + 1)) := by gcongr
  have h3 : V0 * b ≤ (ρ0 + 3) ^ d * 16 ^ (d + 1) * (K * G ^ (d + 1)) := by
    have hV0' : 0 ≤ (ρ0 + 3) ^ d * K * (16 * G) := by positivity
    calc V0 * b ≤ ((ρ0 + 3) ^ d * K * (16 * G)) * (16 * G) ^ d := by
          rcases le_or_gt 0 V0 with hv | hv
          · exact mul_le_mul hV0 hb hb0 hV0'
          · nlinarith [mul_nonneg hV0' (pow_nonneg (by positivity : (0 : ℝ) ≤ 16 * G) d)]
      _ = (ρ0 + 3) ^ d * 16 ^ (d + 1) * (K * G ^ (d + 1)) := by ring
  nlinarith

lemma aux_tight_subharmonic_gain_final {d nB β : ℕ} {CT c1 CF K Kcc G X a' b' : ℝ} (hCT : 0 ≤ CT) (hCF : 0 ≤ CF)
    (hK : 1 ≤ K) (hKcc : 1 ≤ Kcc) (hG : 1 ≤ G) (hX0 : 0 ≤ X) (hX : X ≤ c1 * K * G ^ (d + 1))
    (ha'1 : 1 ≤ a') (ha' : a' ≤ 32 * G) (hb'1 : 1 ≤ b') (hb' : b' ≤ 4 * G) (hnB : 1 ≤ nB) :
    (CT * X) ^ 2 * (CF * (Kcc * K * a' ^ nB * b') ^ (2 * β)) ≤
      CT ^ 2 * c1 ^ 2 * CF * 32 ^ (2 * β * nB) * 4 ^ (2 * β) *
        (Kcc * K * G) ^ (2 * β * (nB + 1) + 2 * d + 2) := by
  have hG0 : 0 < G := by linarith
  have h1 : (CT * X) ^ 2 ≤ CT ^ 2 * c1 ^ 2 * (K ^ 2 * G ^ (2 * d + 2)) := by
    calc (CT * X) ^ 2 ≤ (CT * (c1 * K * G ^ (d + 1))) ^ 2 := by gcongr
      _ = CT ^ 2 * c1 ^ 2 * (K ^ 2 * G ^ (2 * d + 2)) := by ring
  have h2 : (Kcc * K * a' ^ nB * b') ^ (2 * β) ≤
      32 ^ (2 * β * nB) * 4 ^ (2 * β) * ((Kcc * K) ^ (2 * β) * G ^ (2 * β * (nB + 1))) := by
    calc (Kcc * K * a' ^ nB * b') ^ (2 * β) ≤ (Kcc * K * (32 * G) ^ nB * (4 * G)) ^ (2 * β) := by
          gcongr
      _ = 32 ^ (2 * β * nB) * 4 ^ (2 * β) * ((Kcc * K) ^ (2 * β) * G ^ (2 * β * (nB + 1))) := by
          simp only [mul_pow, ← pow_mul]
          ring
  have h3 : K ^ 2 * G ^ (2 * d + 2) * ((Kcc * K) ^ (2 * β) * G ^ (2 * β * (nB + 1))) ≤
      (Kcc * K * G) ^ (2 * β * (nB + 1) + 2 * d + 2) := by
    have hKK : 1 ≤ Kcc * K := one_le_mul_of_one_le_of_one_le hKcc hK
    have e1 : (Kcc * K * G) ^ (2 * β * (nB + 1) + 2 * d + 2) =
        (Kcc * K) ^ (2 * β * (nB + 1) + 2 * d + 2) * G ^ (2 * β * (nB + 1) + 2 * d + 2) := mul_pow _ _ _
    have e2 : K ^ 2 * G ^ (2 * d + 2) * ((Kcc * K) ^ (2 * β) * G ^ (2 * β * (nB + 1))) =
        (K ^ 2 * (Kcc * K) ^ (2 * β)) * G ^ (2 * β * (nB + 1) + 2 * d + 2) := by ring
    rw [e1, e2]
    gcongr
    calc K ^ 2 * (Kcc * K) ^ (2 * β) ≤ (Kcc * K) ^ 2 * (Kcc * K) ^ (2 * β) := by
          gcongr; exact le_mul_of_one_le_left (by linarith) hKcc
      _ = (Kcc * K) ^ (2 * β + 2) := by ring
      _ ≤ (Kcc * K) ^ (2 * β * (nB + 1) + 2 * d + 2) := pow_le_pow_right₀ hKK (by nlinarith)
  calc (CT * X) ^ 2 * (CF * (Kcc * K * a' ^ nB * b') ^ (2 * β))
      ≤ (CT ^ 2 * c1 ^ 2 * (K ^ 2 * G ^ (2 * d + 2))) *
          (CF * (32 ^ (2 * β * nB) * 4 ^ (2 * β) * ((Kcc * K) ^ (2 * β) * G ^ (2 * β * (nB + 1))))) := by
        gcongr
    _ = CT ^ 2 * c1 ^ 2 * CF * 32 ^ (2 * β * nB) * 4 ^ (2 * β) *
          (K ^ 2 * G ^ (2 * d + 2) * ((Kcc * K) ^ (2 * β) * G ^ (2 * β * (nB + 1)))) := by ring
    _ ≤ _ := by gcongr

end




section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

lemma aux_tight_subharmonic_crit_p {d : ℕ} (hd : 1 ≤ d) :
    (d : ℝ) / 2 - ((d : ℝ) - 1 / 2) / (2 + 1 / (d : ℝ)) < 3 / 4 := by
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : (0 : ℝ) < 2 + 1 / (d : ℝ) := by positivity
  rw [sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', lt_div_iff₀ hpos]
  field_simp
  nlinarith

/-- Geometry of the Moser gain step. -/
lemma aux_tight_subharmonic_gain_geom {ρ0 : ℝ} (hρ0 : 0 < ρ0) {qa qb : ℚ} (hqa : 0 ≤ qa) (hab : qa < qb) (hb1 : qb ≤ 1) :
    let Δ : ℝ := (qb : ℝ) - qa
    let r0 : ℝ := min 1 (ρ0 * Δ / 16)
    let q1 : ℚ := qa + (qb - qa) / 8
    let qm : ℚ := qa + (qb - qa) / 2
    0 < Δ ∧ 0 < r0 ∧ r0 ≤ 1 ∧ r0 ≤ ρ0 * Δ / 16 ∧ r0⁻¹ ≤ 16 * (1 + 1 / (ρ0 * Δ)) ∧
    ρ0 * (qa : ℝ) / 2 + 2 * r0 ≤ ρ0 / 2 ∧ ρ0 * (qa : ℝ) / 2 + r0 ≤ ρ0 * (q1 : ℝ) / 2 ∧
    ρ0 * (q1 : ℝ) / 2 + r0 ≤ ρ0 / 2 ∧
    0 ≤ q1 ∧ qa ≤ q1 ∧ q1 < qm ∧ qm < qb ∧ (qm : ℝ) ≤ qb ∧
    1 + 1 / (ρ0 * ((qm : ℝ) - q1) / 12) = 1 + 32 / (ρ0 * Δ) ∧
    1 + 1 / (ρ0 * (1 - (qm : ℝ)) / 2) ≤ 4 * (1 + 1 / (ρ0 * Δ)) := by
  intro Δ r0 q1 qm
  have hΔ : 0 < Δ := by simp only [Δ]; exact_mod_cast sub_pos.2 hab
  have hb1' : (qb : ℝ) ≤ 1 := by exact_mod_cast hb1
  have hqa' : (0 : ℝ) ≤ qa := by exact_mod_cast hqa
  have hq1 : (q1 : ℝ) = qa + Δ / 8 := by simp only [q1, Δ]; push_cast; ring
  have hqm : (qm : ℝ) = qa + Δ / 2 := by simp only [qm, Δ]; push_cast; ring
  have hr0a : r0 ≤ 1 := min_le_left _ _
  have hr0b : r0 ≤ ρ0 * Δ / 16 := min_le_right _ _
  have hr0 : 0 < r0 := lt_min one_pos (by positivity)
  have hqb : (qb : ℝ) = qa + Δ := by simp only [Δ]; ring
  refine ⟨hΔ, hr0, hr0a, hr0b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [inv_le_iff_one_le_mul₀ hr0]
    rcases le_total 1 (ρ0 * Δ / 16) with h | h
    · have : r0 = 1 := min_eq_left h
      rw [this]; have : 0 ≤ 1 / (ρ0 * Δ) := by positivity
      nlinarith
    · have : r0 = ρ0 * Δ / 16 := min_eq_right h
      rw [this]; field_simp; nlinarith [mul_pos hρ0 hΔ]
  · nlinarith
  · rw [hq1]; nlinarith
  · rw [hq1]; nlinarith
  · simp only [q1]; have : (0 : ℚ) < (qb - qa) / 8 := by have := sub_pos.2 hab; positivity
    linarith
  · simp only [q1]; have : (0 : ℚ) < (qb - qa) / 8 := by have := sub_pos.2 hab; positivity
    linarith
  · simp only [q1, qm]; have := sub_pos.2 hab; linarith
  · simp only [qm]; have := sub_pos.2 hab; linarith
  · rw [hqm, hqb]; linarith
  · rw [hqm, hq1]
    have e : ρ0 * (((qa : ℝ) + Δ / 2) - (qa + Δ / 8)) / 12 = ρ0 * Δ / 32 := by ring
    rw [e, one_div_div]
  · rw [hqm]
    have h1 : ρ0 * Δ / 4 ≤ ρ0 * (1 - (qa + Δ / 2)) / 2 := by nlinarith
    have h2 : 1 / (ρ0 * (1 - (qa + Δ / 2)) / 2) ≤ 1 / (ρ0 * Δ / 4) :=
      one_div_le_one_div_of_le (by positivity) h1
    have h3 : 1 / (ρ0 * Δ / 4) = 4 * (1 / (ρ0 * Δ)) := by field_simp
    nlinarith

/-- **Moser gain** (proof.tex (v), one step): trace at `p = 2 + 1/d` on the inner cube plus hole
filling. -/
theorem aux_tight_subharmonic_moser_gain {d : ℕ} (hd : 1 ≤ d) (B ρ0 : ℝ) (hB : 0 < B) (hρ0 : 0 < ρ0) : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure (Fin d → ℝ)) [SFinite μ] (g : (Fin d → ℝ) → ℝ) (Mg K Kcc : ℝ) (qa qb : ℚ),
      Measurable g → (∀ x, |g x| ≤ Mg) → 1 ≤ K → 1 ≤ Kcc → 0 ≤ qa → qa < qb → qb ≤ 1 →
      μ ≪ volume → aux_tight_subharmonic_MassBd μ K (ρ0 / 2) → aux_tight_subharmonic_CutFam g K B ρ0 Kcc qa qb →
      eLpNorm g (ENNReal.ofReal (2 + 1 / (d : ℝ))) (μ.restrict (ball 0 (ρ0 * (qa : ℝ) / 2))) ^ 2 ≤
        ENNReal.ofReal (C * (Kcc * K * (1 + 1 / (ρ0 * ((qb : ℝ) - qa)))) ^
          (2 * (2 * d + 10) * ((⌈B⌉₊ + 1) + 1) + 2 * d + 2)) *
          ∫⁻ x in ball 0 (ρ0 * (qb : ℝ) / 2), ENNReal.ofReal (g x ^ 2) ∂μ := by
  obtain ⟨CF, hCF, hfill⟩ := aux_tight_subharmonic_hole_fill (d := d) B ρ0 hB hρ0
  have h1d : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  have hp2 : (2 : ℝ) ≤ 2 + 1 / (d : ℝ) := by linarith
  obtain ⟨CT, hCT, htr⟩ := aux_tight_subharmonic_aux_trace_Lp_scaled d (1 / 2) (3 / 4) (2 + 1 / (d : ℝ)) hp2
    (by norm_num) (aux_tight_subharmonic_crit_p hd)
  set nB : ℕ := ⌈B⌉₊ + 1 with hnB
  set β : ℕ := 2 * d + 10 with hβ
  set c1 : ℝ := 1 + 16 ^ d + (ρ0 + 3) ^ d * 16 ^ (d + 1) with hc1
  refine ⟨CT ^ 2 * c1 ^ 2 * CF * 32 ^ (2 * β * nB) * 4 ^ (2 * β), by positivity, ?_⟩
  intro μ _ g Mg K Kcc qa qb hg hgb hK hKcc hqa hab hb1 hac hmass hfam
  obtain ⟨hΔ, hr0, hr01, hr0b, hr0inv, hRa, hRa1, hR1, hq10, hqaq1, hq1m, hqmb, hqmb', ha'eq, hb'le⟩ :=
    aux_tight_subharmonic_gain_geom hρ0 hqa hab hb1
  set Δ : ℝ := (qb : ℝ) - qa with hΔdef
  set r0 : ℝ := min 1 (ρ0 * Δ / 16) with hr0def
  set q1 : ℚ := qa + (qb - qa) / 8 with hq1def
  set qm : ℚ := qa + (qb - qa) / 2 with hqmdef
  set G : ℝ := 1 + 1 / (ρ0 * Δ) with hG
  have hG0' : 0 ≤ 1 / (ρ0 * Δ) := by positivity
  have hG1 : 1 ≤ G := by rw [hG]; linarith
  -- hole filling on `[q1, qm]`
  have hF := hfill μ g Mg K Kcc qa q1 qm qb hg hgb hK hKcc hq10 hqaq1 hq1m hqmb hb1 hac hmass hfam
  -- trace on `U = ball 0 (ρ0 q1/2)` for `ν = μ|ball 0 (ρ0 qa/2)`
  set p : ℝ := 2 + 1 / (d : ℝ) with hp
  set ν : Measure (Fin d → ℝ) := μ.restrict (ball 0 (ρ0 * (qa : ℝ) / 2)) with hν
  set V0 : ℝ := (ρ0 + 3) ^ d * K * r0 ^ (-(1 / 2 : ℝ)) with hV0
  have hqa' : (0 : ℝ) ≤ qa := by exact_mod_cast hqa
  have hνtot : ν Set.univ ≤ ENNReal.ofReal V0 := by
    rw [hν, Measure.restrict_apply_univ]
    exact aux_tight_subharmonic_mass_total μ (by linarith) (by positivity) hr0 hr01 hRa hmass
  haveI : IsFiniteMeasure ν := ⟨hνtot.trans_lt ENNReal.ofReal_lt_top⟩
  have hnull : ν {x | ¬ closedBall x r0 ⊆ ball 0 (ρ0 * (q1 : ℝ) / 2)} = 0 := by
    rw [hν, Measure.restrict_apply' measurableSet_ball]
    refine measure_mono_null (fun x hx ↦ ?_) (measure_empty (μ := μ))
    exact hx.1 (aux_tight_subharmonic_sub_closedBall hx.2 hRa1)
  have hνmass : ∀ y ∈ ball (0 : Fin d → ℝ) (ρ0 * (q1 : ℝ) / 2), ∀ r : ℝ, 0 < r → r ≤ r0 →
      ν (ball y r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2)) := fun y hy r hr hrr0 ↦
    (Measure.restrict_apply_le _ _).trans
      (hmass y r hr (hrr0.trans hr01) (aux_tight_subharmonic_sub_ball hy (by linarith))).2
  have hT := htr r0 hr0 (ball 0 (ρ0 * (q1 : ℝ) / 2)) ν K (by linarith) inferInstance
    measurableSet_ball ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hac)
    hnull hνmass g hg (aux_tight_subharmonic_memLp_of_bdd g hg hgb 0 _)
  clear htr hfill
  rw [show (d : ℝ) + 2 * (3 / 4 : ℝ) = (d : ℝ) + 3 / 2 by norm_num] at hT
  set e : ℝ := 3 / 4 - (d : ℝ) / 2 + ((d : ℝ) - 1 / 2) / p with he
  have he0 : 0 < e := by have := aux_tight_subharmonic_crit_p hd; rw [he]; linarith
  have hsq := aux_tight_subharmonic_trace_sq_fE ν g (ball 0 (ρ0 * (q1 : ℝ) / 2)) p CT (K ^ (1 / p) * r0 ^ e)
    (r0 ^ (-((d : ℝ) / 2))) V0 (by linarith) (by positivity) (by positivity) (by positivity)
    hCT.le hνtot (by simpa only [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hg.aestronglyMeasurable] using! hT)
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hg.aestronglyMeasurable] at hsq
  -- the real constant bounds
  have hp1 : 1 ≤ p := by linarith
  have ha : K ^ (1 / p) * r0 ^ e ≤ K := by
    have h1 : K ^ (1 / p) ≤ K := by
      have := Real.rpow_le_rpow_of_exponent_le hK (show 1 / p ≤ 1 by
        rw [div_le_one (by linarith)]; exact hp1)
      rwa [Real.rpow_one] at this
    have h2 : r0 ^ e ≤ 1 := Real.rpow_le_one hr0.le hr01 he0.le
    calc K ^ (1 / p) * r0 ^ e ≤ K * 1 := mul_le_mul h1 h2 (by positivity) (by linarith)
      _ = K := mul_one K
  have hinv1 : 1 ≤ r0⁻¹ := one_le_inv₀ hr0 |>.2 hr01
  have hb : r0 ^ (-((d : ℝ) / 2)) ≤ (16 * G) ^ d := by
    rw [Real.rpow_neg hr0.le, ← Real.inv_rpow hr0.le]
    have hd2 : (d : ℝ) / 2 ≤ d := by
      have : (0 : ℝ) ≤ d := by positivity
      linarith
    calc r0⁻¹ ^ ((d : ℝ) / 2) ≤ r0⁻¹ ^ (d : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hinv1 hd2
      _ = r0⁻¹ ^ d := Real.rpow_natCast _ _
      _ ≤ (16 * G) ^ d := pow_le_pow_left₀ (by positivity) hr0inv d
  have hV0b : V0 ≤ (ρ0 + 3) ^ d * K * (16 * G) := by
    rw [hV0]
    have : r0 ^ (-(1 / 2 : ℝ)) ≤ 16 * G := by
      rw [Real.rpow_neg hr0.le, ← Real.inv_rpow hr0.le]
      calc r0⁻¹ ^ (1 / 2 : ℝ) ≤ r0⁻¹ ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hinv1 (by norm_num)
        _ = r0⁻¹ := Real.rpow_one _
        _ ≤ 16 * G := hr0inv
    gcongr
  have hlin := aux_tight_subharmonic_gain_lin (d := d) hρ0 hK hG1 ha (by positivity) hb hV0b
  -- combine
  rw [ha'eq] at hF
  have h32 : 0 ≤ 32 / (ρ0 * Δ) := by positivity
  have ha'1 : 1 ≤ 1 + 32 / (ρ0 * Δ) := by linarith
  have ha'2 : 1 + 32 / (ρ0 * Δ) ≤ 32 * G := by
    rw [hG]; have : 0 ≤ 1 / (ρ0 * Δ) := by positivity
    have e32 : 32 / (ρ0 * Δ) = 32 * (1 / (ρ0 * Δ)) := by ring
    linarith
  have hb'1 : 1 ≤ 1 + 1 / (ρ0 * (1 - (qm : ℝ)) / 2) := by
    have h1 : (qm : ℝ) < 1 := by exact_mod_cast hqmb.trans_le hb1
    have : 0 ≤ 1 / (ρ0 * (1 - (qm : ℝ)) / 2) := by
      have : (0 : ℝ) < 1 - qm := by linarith
      positivity
    linarith
  have hfin := aux_tight_subharmonic_gain_final (d := d) (nB := nB) (β := β) hCT.le hCF.le hK hKcc hG1 (by positivity)
    hlin ha'1 ha'2 hb'1 hb'le (by omega)
  calc eLpNorm g (ENNReal.ofReal p) ν ^ 2
      ≤ ENNReal.ofReal ((CT * (K ^ (1 / p) * r0 ^ e + (1 + V0) * r0 ^ (-((d : ℝ) / 2)))) ^ 2) *
          aux_tight_subharmonic_fE g (ball 0 (ρ0 * (q1 : ℝ) / 2)) := hsq
    _ ≤ ENNReal.ofReal ((CT * (K ^ (1 / p) * r0 ^ e + (1 + V0) * r0 ^ (-((d : ℝ) / 2)))) ^ 2) *
          (ENNReal.ofReal (CF * (Kcc * K * (1 + 32 / (ρ0 * Δ)) ^ nB *
            (1 + 1 / (ρ0 * (1 - (qm : ℝ)) / 2))) ^ (2 * β)) *
          ∫⁻ x in ball 0 (ρ0 * (qm : ℝ) / 2), ENNReal.ofReal (g x ^ 2) ∂μ) := by gcongr
    _ ≤ ENNReal.ofReal ((CT * (K ^ (1 / p) * r0 ^ e + (1 + V0) * r0 ^ (-((d : ℝ) / 2)))) ^ 2) *
          (ENNReal.ofReal (CF * (Kcc * K * (1 + 32 / (ρ0 * Δ)) ^ nB *
            (1 + 1 / (ρ0 * (1 - (qm : ℝ)) / 2))) ^ (2 * β)) *
          ∫⁻ x in ball 0 (ρ0 * (qb : ℝ) / 2), ENNReal.ofReal (g x ^ 2) ∂μ) := by
        gcongr
    _ = ENNReal.ofReal ((CT * (K ^ (1 / p) * r0 ^ e + (1 + V0) * r0 ^ (-((d : ℝ) / 2)))) ^ 2 *
          (CF * (Kcc * K * (1 + 32 / (ρ0 * Δ)) ^ nB *
            (1 + 1 / (ρ0 * (1 - (qm : ℝ)) / 2))) ^ (2 * β))) *
          ∫⁻ x in ball 0 (ρ0 * (qb : ℝ) / 2), ENNReal.ofReal (g x ^ 2) ∂μ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        gcongr

end




section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

/-- Moser product with an explicit constant (generalizes GMC `exists_moser_iteration_constant`). -/
theorem aux_tight_subharmonic_moser_product {chi A Λ : ℝ} (hchi : 1 < chi) (hA : 0 ≤ A) (hΛ : 0 ≤ Λ) (N : ℕ → ℝ≥0∞)
    (hN : ∀ n, N (n + 1) ^ (chi ^ n) ≤ ENNReal.ofReal (A * Λ ^ n) * N n ^ (chi ^ n)) :
    ∀ n, N n ≤ ENNReal.ofReal (max 1 (max A Λ) ^ (∑' k : ℕ, ((k : ℝ) + 1) / chi ^ k)) * N 0 := by
  have hchi0 : 0 < chi := by linarith
  set D : ℝ := max 1 (max A Λ) with hDdef
  have hD1 : 1 ≤ D := le_max_left _ _
  have hAD : A ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hΛD : Λ ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have hD0 : 0 < D := by linarith
  let b : ℕ → ℝ := fun n => ((n : ℝ) + 1) / chi ^ n
  have hb0 (n : ℕ) : 0 ≤ b n := by dsimp only [b]; positivity
  have hnorm : ‖chi⁻¹‖ < 1 := by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hchi0.le)]
    exact (inv_lt_one₀ hchi0).mpr hchi
  have hsum : Summable b := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    have h0 := summable_geometric_of_norm_lt_one hnorm
    simpa only [b, pow_one, add_mul, one_mul, div_eq_mul_inv, inv_pow] using h1.add h0
  intro n
  have hcoef (k : ℕ) : A * Λ ^ k ≤ D ^ (k + 1) := by
    rw [pow_succ']
    exact mul_le_mul hAD (pow_le_pow_left₀ hΛ hΛD k) (by positivity) hD0.le
  have hstep (k : ℕ) : N (k + 1) ≤ ENNReal.ofReal (D ^ b k) * N k := by
    have hk0 : 0 < chi ^ k := pow_pos hchi0 k
    have h := (hN k).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hcoef k)) le_rfl)
    have hr := ENNReal.rpow_le_rpow h (inv_nonneg.mpr hk0.le)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hk0.le),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_inv_cancel₀ hk0.ne', ENNReal.rpow_one] at hr
    have hDpow : (ENNReal.ofReal (D ^ (k + 1))) ^ (chi ^ k)⁻¹ =
        ENNReal.ofReal (D ^ b k) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hD0.le _) (inv_nonneg.mpr hk0.le),
        ← Real.rpow_natCast D (k + 1), ← Real.rpow_mul hD0.le]
      simp only [b, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
    simpa only [hDpow, ENNReal.rpow_one] using hr
  have hfinite (k : ℕ) : N k ≤ ENNReal.ofReal (D ^ (∑ j ∈ Finset.range k, b j)) * N 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      refine (hstep k).trans ((mul_le_mul' le_rfl ih).trans_eq ?_)
      rw [Finset.sum_range_succ, Real.rpow_add hD0,
        ENNReal.ofReal_mul (Real.rpow_nonneg hD0.le _)]
      ring
  refine (hfinite n).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  exact Real.rpow_le_rpow_of_exponent_le hD1 (hsum.sum_le_tsum (Finset.range n) (fun k _ => hb0 k))

lemma aux_tight_subharmonic_CutFam_mono {d : ℕ} {g : (Fin d → ℝ) → ℝ} {K B ρ0 Kcc : ℝ} {qlo qhi qlo' qhi' : ℚ}
    (h : aux_tight_subharmonic_CutFam g K B ρ0 Kcc qlo qhi) (hlo : qlo ≤ qlo') (hhi : qhi' ≤ qhi) :
    aux_tight_subharmonic_CutFam g K B ρ0 Kcc qlo' qhi' :=
  fun q q' hq hqq' hq' ↦ h q q' (hlo.trans hq) hqq' (hq'.trans hhi)

lemma aux_tight_subharmonic_eLpNorm_rpow_nonneg {d : ℕ} {W : (Fin d → ℝ) → ℝ} (hW : ∀ x, 0 ≤ W x) {s p : ℝ} (hs : 0 < s)
    (hp : 0 ≤ p) (ν : Measure (Fin d → ℝ)) :
    SubdiffusiveProcess.RawLp.eLpNorm (fun x ↦ W x ^ s) (ENNReal.ofReal p) ν = SubdiffusiveProcess.RawLp.eLpNorm W (ENNReal.ofReal (p * s)) ν ^ s  := by
  by_cases hp0 : p = 0
  · simp [hp0, SubdiffusiveProcess.RawLp.eLpNorm, ENNReal.zero_rpow_of_pos hs]
  have hpPos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hps : 0 < p * s := mul_pos hpPos hs
  have hf : (fun x ↦ W x ^ s) = (fun x ↦ ‖W x‖ ^ s) := by
    funext x
    rw [Real.norm_of_nonneg (hW x)]
  simp only [SubdiffusiveProcess.RawLp.eLpNorm, ENNReal.ofReal_ne_zero_iff.mpr hpPos,
    ENNReal.ofReal_ne_zero_iff.mpr hps, ENNReal.ofReal_ne_top, ite_false,
    ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hps.le]
  rw [hf]
  exact eLpNorm'_norm_rpow W p s hs

lemma aux_tight_subharmonic_lintegral_rpow_sq {d : ℕ} {W : (Fin d → ℝ) → ℝ} (hW : ∀ x, 0 ≤ W x) {s : ℝ} (hs : 0 < s)
    (ν : Measure (Fin d → ℝ)) :
    ∫⁻ x, ENNReal.ofReal ((W x ^ s) ^ 2) ∂ν =
      (SubdiffusiveProcess.RawLp.eLpNorm W (ENNReal.ofReal (2 * s)) ν ^ (2 * s)) := by
  have h := aux_tight_subharmonic_eLpNorm_two_sq (fun x ↦ W x ^ s) ν
  rw [← h, ← ENNReal.ofReal_ofNat 2, aux_tight_subharmonic_eLpNorm_rpow_nonneg hW hs (by norm_num),
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  ring_nf

end




section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

/-- The content of `aux_tight_subharmonic_moser_gain` for a given constant. -/
def aux_tight_subharmonic_GainSpec (d : ℕ) (B ρ0 C : ℝ) : Prop :=
  ∀ (μ : Measure (Fin d → ℝ)) [SFinite μ] (g : (Fin d → ℝ) → ℝ) (Mg K Kcc : ℝ) (qa qb : ℚ),
      Measurable g → (∀ x, |g x| ≤ Mg) → 1 ≤ K → 1 ≤ Kcc → 0 ≤ qa → qa < qb → qb ≤ 1 →
      μ ≪ volume → aux_tight_subharmonic_MassBd μ K (ρ0 / 2) → aux_tight_subharmonic_CutFam g K B ρ0 Kcc qa qb →
      eLpNorm g (ENNReal.ofReal (2 + 1 / (d : ℝ))) (μ.restrict (ball 0 (ρ0 * (qa : ℝ) / 2))) ^ 2 ≤
        ENNReal.ofReal (C * (Kcc * K * (1 + 1 / (ρ0 * ((qb : ℝ) - qa)))) ^
          (2 * (2 * d + 10) * ((⌈B⌉₊ + 1) + 1) + 2 * d + 2)) *
          ∫⁻ x in ball 0 (ρ0 * (qb : ℝ) / 2), ENNReal.ofReal (g x ^ 2) ∂μ

lemma aux_tight_subharmonic_moser_gain' {d : ℕ} (hd : 1 ≤ d) (B ρ0 : ℝ) (hB : 0 < B) (hρ0 : 0 < ρ0) :
    ∃ C : ℝ, 0 < C ∧ aux_tight_subharmonic_GainSpec d B ρ0 C := aux_tight_subharmonic_moser_gain hd B ρ0 hB hρ0

/-- Moser radii. -/
def aux_tight_subharmonic_qi (q1 q2 : ℚ) (i : ℕ) : ℚ := q1 + (q2 - q1) / 2 ^ i

lemma aux_tight_subharmonic_qi_facts {q1 q2 : ℚ} (h : q1 < q2) (i : ℕ) :
    aux_tight_subharmonic_qi q1 q2 (i + 1) < aux_tight_subharmonic_qi q1 q2 i ∧ q1 ≤ aux_tight_subharmonic_qi q1 q2 i ∧ aux_tight_subharmonic_qi q1 q2 i ≤ q2 ∧
      ((aux_tight_subharmonic_qi q1 q2 i : ℝ) - aux_tight_subharmonic_qi q1 q2 (i + 1)) = ((q2 : ℝ) - q1) / 2 ^ (i + 1) := by
  have hd : 0 < q2 - q1 := sub_pos.2 h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [aux_tight_subharmonic_qi]
    have : (q2 - q1) / 2 ^ (i + 1) < (q2 - q1) / 2 ^ i := by
      apply div_lt_div_of_pos_left hd (by positivity)
      rw [pow_succ]; linarith [pow_pos (by norm_num : (0 : ℚ) < 2) i]
    linarith
  · simp only [aux_tight_subharmonic_qi]; have : 0 ≤ (q2 - q1) / 2 ^ i := by positivity
    linarith
  · simp only [aux_tight_subharmonic_qi]
    have : (q2 - q1) / 2 ^ i ≤ q2 - q1 := div_le_self hd.le (one_le_pow₀ (by norm_num))
    linarith
  · simp only [aux_tight_subharmonic_qi]; push_cast; field_simp; ring

lemma aux_tight_subharmonic_moser_const_step {Cg Kc K G0 κ ρ0 Δ : ℝ} {γ : ℕ} (hCg : 0 < Cg) (hKc : 1 ≤ Kc) (hK : 1 ≤ K)
    (hκ : 1 ≤ κ) (hρ0 : 0 < ρ0) (hΔ : 0 < Δ) (hG0 : G0 = 1 + 1 / (ρ0 * Δ)) (i : ℕ) :
    Cg * (Kc * (8 * (κ ^ i) ^ 2 + 2) * K * (1 + 1 / (ρ0 * (Δ / 2 ^ (i + 1))))) ^ γ ≤
      (max 1 Cg * (20 * Kc * K * G0) ^ γ) * ((2 * κ ^ 2) ^ γ) ^ i := by
  have hk1 : 1 ≤ (κ ^ i) ^ 2 := one_le_pow₀ (one_le_pow₀ hκ)
  have h1 : 8 * (κ ^ i) ^ 2 + 2 ≤ 10 * (κ ^ i) ^ 2 := by linarith
  have h2 : 1 + 1 / (ρ0 * (Δ / 2 ^ (i + 1))) ≤ 2 * 2 ^ i * G0 := by
    rw [hG0]
    have e : 1 / (ρ0 * (Δ / 2 ^ (i + 1))) = 2 * 2 ^ i * (1 / (ρ0 * Δ)) := by
      rw [pow_succ]; field_simp
    rw [e]
    have : (1 : ℝ) ≤ 2 * 2 ^ i := by
      have := one_le_pow₀ (M₀ := ℝ) (a := 2) (by norm_num) (n := i); linarith
    have h0 : 0 ≤ 1 / (ρ0 * Δ) := by positivity
    nlinarith
  have hG1 : 1 ≤ G0 := by rw [hG0]; have : 0 ≤ 1 / (ρ0 * Δ) := by positivity
                          linarith
  have hbase : Kc * (8 * (κ ^ i) ^ 2 + 2) * K * (1 + 1 / (ρ0 * (Δ / 2 ^ (i + 1)))) ≤
      (20 * Kc * K * G0) * (2 * κ ^ 2) ^ i := by
    calc Kc * (8 * (κ ^ i) ^ 2 + 2) * K * (1 + 1 / (ρ0 * (Δ / 2 ^ (i + 1))))
        ≤ Kc * (10 * (κ ^ i) ^ 2) * K * (2 * 2 ^ i * G0) := by
          gcongr
      _ = (20 * Kc * K * G0) * (2 * κ ^ 2) ^ i := by rw [mul_pow, ← pow_mul, ← pow_mul]; ring
  have hpos : 0 ≤ Kc * (8 * (κ ^ i) ^ 2 + 2) * K * (1 + 1 / (ρ0 * (Δ / 2 ^ (i + 1)))) := by
    positivity
  calc Cg * (Kc * (8 * (κ ^ i) ^ 2 + 2) * K * (1 + 1 / (ρ0 * (Δ / 2 ^ (i + 1))))) ^ γ
      ≤ max 1 Cg * ((20 * Kc * K * G0) * (2 * κ ^ 2) ^ i) ^ γ := by
        gcongr
        · exact le_max_right _ _
    _ = (max 1 Cg * (20 * Kc * K * G0) ^ γ) * ((2 * κ ^ 2) ^ γ) ^ i := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i γ]; ring

lemma aux_tight_subharmonic_ennreal_sq_rpow (x : ℝ≥0∞) (s : ℝ) (hs : 0 ≤ s) : (x ^ s) ^ 2 = (x ^ (2 : ℝ)) ^ s := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]; congr 1; push_cast; ring

/-- One Moser step in `N`-form. -/
lemma aux_tight_subharmonic_moser_Nstep {d : ℕ} (hd : 1 ≤ d) {B ρ0 Cg : ℝ} (hgain : aux_tight_subharmonic_GainSpec d B ρ0 Cg) (hCg : 0 < Cg)
    (hρ0 : 0 < ρ0) (μ : Measure (Fin d → ℝ)) [SFinite μ] (W : (Fin d → ℝ) → ℝ) (Mw K Kc : ℝ)
    (q1 q2 : ℚ) (hq1 : 0 ≤ q1) (hq12 : q1 < q2) (hq2 : q2 ≤ 1) (hW : Measurable W)
    (hW0 : ∀ x, 0 ≤ W x) (hWM : ∀ x, W x ≤ Mw) (hK : 1 ≤ K) (hKc : 1 ≤ Kc) (hac : μ ≪ volume)
    (hmass : aux_tight_subharmonic_MassBd μ K (ρ0 / 2))
    (hfam : ∀ s : ℝ, 1 ≤ s → aux_tight_subharmonic_CutFam (fun x ↦ W x ^ s) K B ρ0 (Kc * (8 * s ^ 2 + 2)) q1 q2) (i : ℕ) :
    (eLpNorm W (ENNReal.ofReal (2 * ((2 + 1 / (d : ℝ)) / 2) ^ (i + 1)))
        (μ.restrict (ball 0 (ρ0 * (aux_tight_subharmonic_qi q1 q2 (i + 1) : ℝ) / 2))) ^ (2 : ℝ)) ^ (((2 + 1 / (d : ℝ)) / 2) ^ i) ≤
      ENNReal.ofReal ((max 1 Cg * (20 * Kc * K * (1 + 1 / (ρ0 * ((q2 : ℝ) - q1)))) ^
          (2 * (2 * d + 10) * ((⌈B⌉₊ + 1) + 1) + 2 * d + 2)) *
        ((2 * ((2 + 1 / (d : ℝ)) / 2) ^ 2) ^ (2 * (2 * d + 10) * ((⌈B⌉₊ + 1) + 1) + 2 * d + 2)) ^ i) *
      (eLpNorm W (ENNReal.ofReal (2 * ((2 + 1 / (d : ℝ)) / 2) ^ i))
        (μ.restrict (ball 0 (ρ0 * (aux_tight_subharmonic_qi q1 q2 i : ℝ) / 2))) ^ (2 : ℝ)) ^ (((2 + 1 / (d : ℝ)) / 2) ^ i) := by
  set κ : ℝ := (2 + 1 / (d : ℝ)) / 2 with hκ
  have hκ1 : 1 ≤ κ := by rw [hκ]; have : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
                         linarith
  set s : ℝ := κ ^ i with hs
  have hs1 : 1 ≤ s := one_le_pow₀ hκ1
  have hs0 : 0 < s := by linarith
  obtain ⟨hlt, hq1i, hqi2, hgap⟩ := aux_tight_subharmonic_qi_facts hq12 i
  obtain ⟨-, hq1i', -, -⟩ := aux_tight_subharmonic_qi_facts hq12 (i + 1)
  have hMw0 : 0 ≤ Mw := (hW0 0).trans (hWM 0)
  have hgb : ∀ x, |W x ^ s| ≤ Mw ^ s := fun x ↦ by
    rw [abs_of_nonneg (Real.rpow_nonneg (hW0 x) _)]
    exact Real.rpow_le_rpow (hW0 x) (hWM x) hs0.le
  have hKcc : 1 ≤ Kc * (8 * s ^ 2 + 2) := by nlinarith [sq_nonneg s]
  have hg := hgain μ (fun x ↦ W x ^ s) (Mw ^ s) K (Kc * (8 * s ^ 2 + 2)) (aux_tight_subharmonic_qi q1 q2 (i + 1))
    (aux_tight_subharmonic_qi q1 q2 i) (hW.pow_const s) hgb hK hKcc (hq1.trans hq1i') hlt (hqi2.trans hq2) hac hmass
    (aux_tight_subharmonic_CutFam_mono (hfam s hs1) hq1i' hqi2)
  clear hgain
  have hrpow : eLpNorm (fun x ↦ W x ^ s) (ENNReal.ofReal (2 + 1 / (d : ℝ)))
      (μ.restrict (ball 0 (ρ0 * (aux_tight_subharmonic_qi q1 q2 (i + 1) : ℝ) / 2))) =
      eLpNorm W (ENNReal.ofReal ((2 + 1 / (d : ℝ)) * s))
        (μ.restrict (ball 0 (ρ0 * (aux_tight_subharmonic_qi q1 q2 (i + 1) : ℝ) / 2))) ^ s := by
    simpa only [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (hW.pow_const s).aestronglyMeasurable,
      SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hW.aestronglyMeasurable] using!
        (aux_tight_subharmonic_eLpNorm_rpow_nonneg hW0 hs0 (by positivity)
          (μ.restrict (ball 0 (ρ0 * (aux_tight_subharmonic_qi q1 q2 (i + 1) : ℝ) / 2))))
  rw [hrpow, aux_tight_subharmonic_lintegral_rpow_sq hW0 hs0,
    SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hW.aestronglyMeasurable, hgap] at hg
  have e1 : (2 + 1 / (d : ℝ)) * s = 2 * κ ^ (i + 1) := by rw [hs, hκ, pow_succ]; ring
  have e2 : 2 * s = 2 * κ ^ i := by rw [hs]
  rw [e1, e2] at hg
  have hR : (eLpNorm W (ENNReal.ofReal (2 * κ ^ i))
        (μ.restrict (ball 0 (ρ0 * (aux_tight_subharmonic_qi q1 q2 i : ℝ) / 2))) ^ (2 : ℝ)) ^ s =
      eLpNorm W (ENNReal.ofReal (2 * κ ^ i))
        (μ.restrict (ball 0 (ρ0 * (aux_tight_subharmonic_qi q1 q2 i : ℝ) / 2))) ^ (2 * s) := by
    rw [← ENNReal.rpow_mul]
  rw [hR]
  calc (eLpNorm W (ENNReal.ofReal (2 * κ ^ (i + 1)))
        (μ.restrict (ball 0 (ρ0 * (aux_tight_subharmonic_qi q1 q2 (i + 1) : ℝ) / 2))) ^ (2 : ℝ)) ^ s
      = (eLpNorm W (ENNReal.ofReal (2 * κ ^ (i + 1)))
        (μ.restrict (ball 0 (ρ0 * (aux_tight_subharmonic_qi q1 q2 (i + 1) : ℝ) / 2))) ^ s) ^ 2 :=
        (aux_tight_subharmonic_ennreal_sq_rpow _ s hs0.le).symm
    _ ≤ _ := hg
    _ ≤ _ := by
        have hΔ : (0 : ℝ) < (q2 : ℝ) - q1 := by
          have : (q1 : ℝ) < q2 := by exact_mod_cast hq12
          linarith
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal
          (aux_tight_subharmonic_moser_const_step hCg hKc hK hκ1 hρ0 hΔ rfl i)) le_rfl

end




section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

lemma aux_tight_subharmonic_half_rpow_bound {X Y : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c) (h : X ^ (2 : ℝ) ≤ ENNReal.ofReal c * Y ^ (2 : ℝ)) :
    X ≤ ENNReal.ofReal (c ^ (1 / 2 : ℝ)) * Y := by
  have hr := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ENNReal.ofReal_rpow_of_nonneg hc (by norm_num)] at hr
  norm_num at hr
  exact hr

lemma aux_tight_subharmonic_const_split {Cg Kc K G0 Λ S : ℝ} {γ : ℕ} (hCg : 0 < Cg) (hKc : 1 ≤ Kc) (hK : 1 ≤ K) (hG0 : 1 ≤ G0)
    (hΛ : 1 ≤ Λ) (hS : 0 ≤ S) :
    (((max 1 Cg * (20 * Kc * K * G0) ^ γ) * Λ) ^ S) ^ (1 / 2 : ℝ) ≤
      (max 1 Cg * (20 * G0) ^ γ * Λ) ^ (S / 2) * (K * Kc) ^ ((γ : ℝ) * S / 2 + 1) := by
  have hM : 1 ≤ max 1 Cg := le_max_left _ _
  have hKK : 1 ≤ K * Kc := one_le_mul_of_one_le_of_one_le hK hKc
  have e : (max 1 Cg * (20 * Kc * K * G0) ^ γ) * Λ = (max 1 Cg * (20 * G0) ^ γ * Λ) * (K * Kc) ^ γ := by
    rw [show 20 * Kc * K * G0 = (20 * G0) * (K * Kc) by ring, mul_pow]; ring
  rw [e, ← Real.rpow_mul (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast (K * Kc) γ, ← Real.rpow_mul (by positivity)]
  have h1 : S * (1 / 2) = S / 2 := by ring
  rw [h1]
  gcongr
  nlinarith

/-- **Moser iteration** (proof.tex (v)), abstract form. -/
theorem aux_tight_subharmonic_moser_iter {d : ℕ} (hd : 1 ≤ d) (B ρ0 : ℝ) (hB : 0 < B) (hρ0 : 0 < ρ0) (q1 q2 : ℚ)
    (hq1 : 0 ≤ q1) (hq12 : q1 < q2) (hq2 : q2 ≤ 1) :
    ∃ C Bm : ℝ, 0 < C ∧ 0 < Bm ∧ ∀ (μ : Measure (Fin d → ℝ)) [SFinite μ]
      (W : (Fin d → ℝ) → ℝ) (Mw K Kc : ℝ),
      Measurable W → (∀ x, 0 ≤ W x) → (∀ x, W x ≤ Mw) → 1 ≤ K → 1 ≤ Kc → μ ≪ volume →
      aux_tight_subharmonic_MassBd μ K (ρ0 / 2) →
      (∀ s : ℝ, 1 ≤ s → aux_tight_subharmonic_CutFam (fun x ↦ W x ^ s) K B ρ0 (Kc * (8 * s ^ 2 + 2)) q1 q2) →
      ∀ᵐ x ∂(μ.restrict (ball 0 (ρ0 * (q1 : ℝ) / 2))),
        ENNReal.ofReal (W x) ≤ ENNReal.ofReal (C * (K * Kc) ^ Bm) *
          (∫⁻ x in ball 0 (ρ0 * (q2 : ℝ) / 2), ENNReal.ofReal (W x ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  obtain ⟨Cg, hCg, hgain⟩ := aux_tight_subharmonic_moser_gain' hd B ρ0 hB hρ0
  set κ : ℝ := (2 + 1 / (d : ℝ)) / 2 with hκ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hκ1 : 1 < κ := by rw [hκ]; have : (0 : ℝ) < 1 / (d : ℝ) := by positivity
                         linarith
  set γ : ℕ := 2 * (2 * d + 10) * ((⌈B⌉₊ + 1) + 1) + 2 * d + 2 with hγ
  set G0 : ℝ := 1 + 1 / (ρ0 * ((q2 : ℝ) - q1)) with hG0
  have hΔ : (0 : ℝ) < (q2 : ℝ) - q1 := by
    have : (q1 : ℝ) < q2 := by exact_mod_cast hq12
    linarith
  have hG01 : 1 ≤ G0 := by
    rw [hG0]; have : 0 ≤ 1 / (ρ0 * ((q2 : ℝ) - q1)) := by positivity
    linarith
  set Λ : ℝ := (2 * κ ^ 2) ^ γ with hΛ
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ (by nlinarith)
  set S : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) / κ ^ k with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun k ↦ by positivity
  refine ⟨(max 1 Cg * (20 * G0) ^ γ * Λ) ^ (S / 2), (γ : ℝ) * S / 2 + 1, by positivity,
    by positivity, ?_⟩
  intro μ _ W Mw K Kc hW hW0 hWM hK hKc hac hmass hfam
  set N : ℕ → ℝ≥0∞ := fun j ↦ eLpNorm W (ENNReal.ofReal (2 * κ ^ j))
    (μ.restrict (ball 0 (ρ0 * (aux_tight_subharmonic_qi q1 q2 j : ℝ) / 2))) with hN
  set A : ℝ := max 1 Cg * (20 * Kc * K * G0) ^ γ with hA
  have hA1 : 1 ≤ A := by
    rw [hA]
    have h20 : 1 ≤ 20 * Kc * K * G0 := by
      have : 1 ≤ Kc * K := one_le_mul_of_one_le_of_one_le hKc hK
      nlinarith
    exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ h20)
  have hstep : ∀ i, (N (i + 1) ^ (2 : ℝ)) ^ (κ ^ i) ≤
      ENNReal.ofReal (A * Λ ^ i) * (N i ^ (2 : ℝ)) ^ (κ ^ i) := fun i ↦
    aux_tight_subharmonic_moser_Nstep hd hgain hCg hρ0 μ W Mw K Kc q1 q2 hq1 hq12 hq2 hW hW0 hWM hK hKc hac hmass hfam i
  clear hgain
  have hprod := aux_tight_subharmonic_moser_product hκ1 (by linarith) (by linarith) (fun j ↦ N j ^ (2 : ℝ)) hstep
  have hDle : max 1 (max A Λ) ≤ A * Λ := by
    refine max_le (one_le_mul_of_one_le_of_one_le hA1 hΛ1) (max_le ?_ ?_)
    · exact le_mul_of_one_le_right (by linarith) hΛ1
    · exact le_mul_of_one_le_left (by linarith) hA1
  have hNn : ∀ n, N n ≤ ENNReal.ofReal ((max 1 Cg * (20 * G0) ^ γ * Λ) ^ (S / 2) *
      (K * Kc) ^ ((γ : ℝ) * S / 2 + 1)) * N 0 := by
    intro n
    have h1 := hprod n
    have h2 : max 1 (max A Λ) ^ S ≤ (A * Λ) ^ S :=
      Real.rpow_le_rpow (by positivity) hDle hS0
    have h3 : N n ^ (2 : ℝ) ≤ ENNReal.ofReal ((A * Λ) ^ S) * N 0 ^ (2 : ℝ) :=
      h1.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal h2) le_rfl)
    refine (aux_tight_subharmonic_half_rpow_bound (by positivity) h3).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    exact aux_tight_subharmonic_const_split hCg hKc hK hG01 hΛ1 hS0
  -- the endpoint
  set Cf : ℝ := (max 1 Cg * (20 * G0) ^ γ * Λ) ^ (S / 2) * (K * Kc) ^ ((γ : ℝ) * S / 2 + 1) with hCf
  have hCf0 : 0 < Cf := by positivity
  set I := ∫⁻ x in ball 0 (ρ0 * (q2 : ℝ) / 2), ENNReal.ofReal (W x ^ 2) ∂μ with hI
  have hN0 : N 0 = I ^ (1 / 2 : ℝ) := by
    have h := aux_tight_subharmonic_guarded_two_sq W (μ.restrict (ball 0 (ρ0 * (q2 : ℝ) / 2))) hW.aestronglyMeasurable
    have hq0 : aux_tight_subharmonic_qi q1 q2 0 = q2 := by simp [aux_tight_subharmonic_qi]
    simp only [hN, pow_zero, mul_one, hq0, ENNReal.ofReal_ofNat]
    rw [hI, ← h, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  by_cases hItop : I = ⊤
  · refine Eventually.of_forall fun x ↦ ?_
    rw [hItop, ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top (by positivity)]
    exact le_top
  have hbd : ∀ n : ℕ, eLpNorm W (ENNReal.ofReal (2 * κ ^ n))
      (μ.restrict (ball 0 (ρ0 * (q1 : ℝ) / 2))) ≤
      ENNReal.ofReal (ENNReal.ofReal Cf * I ^ (1 / 2 : ℝ)).toReal := by
    intro n
    have hsub : ball (0 : Fin d → ℝ) (ρ0 * (q1 : ℝ) / 2) ⊆ ball 0 (ρ0 * (aux_tight_subharmonic_qi q1 q2 n : ℝ) / 2) := by
      obtain ⟨-, h1, -, -⟩ := aux_tight_subharmonic_qi_facts hq12 n
      exact ball_subset_ball (by have : (q1 : ℝ) ≤ aux_tight_subharmonic_qi q1 q2 n := by exact_mod_cast h1
                                 nlinarith)
    rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hItop))]
    calc eLpNorm W (ENNReal.ofReal (2 * κ ^ n)) (μ.restrict (ball 0 (ρ0 * (q1 : ℝ) / 2)))
        ≤ N n := eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)
      _ ≤ ENNReal.ofReal Cf * N 0 := hNn n
      _ = ENNReal.ofReal Cf * I ^ (1 / 2 : ℝ) := by rw [hN0]
  have hae := SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.moser_ae_bound_of_eLpNorm_bounds
    hW.aestronglyMeasurable (p := fun n ↦ 2 * κ ^ n) (fun n ↦ by positivity)
    (Tendsto.const_mul_atTop (by norm_num) (tendsto_pow_atTop_atTop_of_one_lt hκ1))
    ENNReal.toReal_nonneg hbd
  filter_upwards [hae] with x hx
  rw [abs_of_nonneg (hW0 x)] at hx
  calc ENNReal.ofReal (W x) ≤ ENNReal.ofReal (ENNReal.ofReal Cf * I ^ (1 / 2 : ℝ)).toReal :=
        ENNReal.ofReal_le_ofReal hx
    _ = ENNReal.ofReal Cf * I ^ (1 / 2 : ℝ) := ENNReal.ofReal_toReal (ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hItop))

end


/-! ### (CC) cutoff Caccioppoli–coercivity -/
section
open Filter MeasureTheory ProbabilityTheory Topology Metric
open MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators







/-- A one-sided version of the nonlinear test identity. Copied verbatim from
`steps_ii_v.lean` (itself copied from `tight_subharmonic_base.lean`). -/
theorem aux_tight_subharmonic_cc_power_test_inequality
    {d : ℕ} {U : Set (SpatialCoordinates d)}
    (hU : Homogenization.IsOpenBoundedConvexDomain U) {a : SpatialCoordinates d → ℝ}
    (u w f : Homogenization.H1Function U)
    (hu : SubdiffusiveProcess.CoarseGrainingVocab.Section11.IsWeakSubSolutionOn a U u)
    {s : ℝ}
    (hpair : SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserPowerPair u w f s)
    (hf : ∀ x, 0 ≤ f.toFun x)
    {eta : SpatialCoordinates d → ℝ}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetac : HasCompactSupport eta) (hetasub : tsupport eta ⊆ U) :
    (∫ x in U, a x * ((2 * s - 1) *
      (eta x ^ 2 * Homogenization.vecNormSq (w.grad x)) +
      s * (w.toFun x * Homogenization.vecDot (w.grad x)
        ((2 * eta x) • Homogenization.euclideanGradient eta x)))) ≤ 0 := by
  have hsmooth := heta.pow 2
  have hcompact : HasCompactSupport (fun x => eta x ^ 2) := by
    simpa only [pow_two] using! hetac.mul_right (f' := eta)
  have hsupport : tsupport (fun x => eta x ^ 2) ⊆ U := by
    simpa only [pow_two] using
      (tsupport_mul_subset_left (f := eta) (g := eta)).trans hetasub
  let psi := f.mulContDiffHasCompactSupportToH10 hU hsmooth hcompact hsupport
  have hpsi := Homogenization.WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae
    f hU hsmooth hcompact hsupport
  have hnonneg : ∀ x, 0 ≤ psi.toH1Function.toFun x := by
    intro x
    rw [Homogenization.H1Function.mulContDiffHasCompactSupportToH10_toFun]
    exact mul_nonneg (sq_nonneg _) (hf x)
  have heq : (fun x => s ^ 2 *
      Homogenization.vecDot (a x • u.grad x) (psi.toH1Function.grad x)) =ᵐ[volume.restrict U]
      (fun x => a x * ((2 * s - 1) *
        (eta x ^ 2 * Homogenization.vecNormSq (w.grad x)) +
        s * (w.toFun x * Homogenization.vecDot (w.grad x)
          ((2 * eta x) • Homogenization.euclideanGradient eta x)))) := by
    filter_upwards [hpsi, hpair] with x hx hp
    rw [hx]
    simp_rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.fderiv_cutoff_sq_apply
      eta heta]
    have hfirst := hp.1
    have hsecond := hp.2
    simp only [Homogenization.vecDot, Homogenization.vecNormSq,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      Homogenization.euclideanGradient, Homogenization.euclideanCoordDeriv] at hfirst ⊢
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i : Fin d, (
          (a x * eta x ^ 2) * (s ^ 2 * (u.grad x i * f.grad x i)) +
            (2 * a x * eta x * s * (fderiv ℝ eta x) (Homogenization.basisVec i)) *
            (s * f.toFun x * u.grad x i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp_rw [hsecond]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfirst]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have htest := hu psi hnonneg
  have hscaled : s ^ 2 *
      (∫ x in U, Homogenization.vecDot (a x • u.grad x)
        (psi.toH1Function.grad x) ∂volume) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg s) htest
  rw [← integral_const_mul, integral_congr_ae heq] at hscaled
  exact hscaled

private theorem aux_tight_subharmonic_cc_integral_le_two_mul_of_le_neg_of_abs_le
    {d : ℕ} {U : Set (SpatialCoordinates d)} {Acal cross remainder : SpatialCoordinates d → ℝ}
    (hAcal : IntegrableOn Acal U) (hcross : IntegrableOn cross U)
    (hremainder : IntegrableOn remainder U)
    (hle : ∫ x in U, Acal x ≤ -∫ x in U, cross x)
    (hpoint : ∀ᵐ x ∂(volume.restrict U), |cross x| ≤ Acal x / 2 + remainder x) :
    ∫ x in U, Acal x ≤ 2 * ∫ x in U, remainder x := by
  have hhalf : IntegrableOn (fun x => Acal x / 2) U := hAcal.div_const 2
  have hsum : IntegrableOn (fun x => Acal x / 2 + remainder x) U := hhalf.add hremainder
  have habs : |∫ x in U, cross x| ≤ ∫ x in U, |cross x| := abs_integral_le_integral_abs
  have hmono : ∫ x in U, |cross x| ≤ ∫ x in U, (Acal x / 2 + remainder x) :=
    setIntegral_mono_ae_restrict hcross.abs hsum hpoint
  have hsplit : ∫ x in U, (Acal x / 2 + remainder x) =
      (∫ x in U, Acal x) / 2 + ∫ x in U, remainder x := by
    rw [integral_add hhalf hremainder, integral_div]
  have hchain : ∫ x in U, Acal x ≤
      (∫ x in U, Acal x) / 2 + ∫ x in U, remainder x := by
    calc ∫ x in U, Acal x ≤ -∫ x in U, cross x := hle
      _ ≤ |∫ x in U, cross x| := neg_le_abs _
      _ ≤ ∫ x in U, |cross x| := habs
      _ ≤ ∫ x in U, (Acal x / 2 + remainder x) := hmono
      _ = (∫ x in U, Acal x) / 2 + ∫ x in U, remainder x := hsplit
  linarith

private theorem aux_tight_subharmonic_cc_integrable_mul_bounded
    {d : ℕ} {U : Set (SpatialCoordinates d)} {a f : SpatialCoordinates d → ℝ} {M : ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict U))
    (hbound : ∀ᵐ x ∂volume.restrict U, |a x| ≤ M)
    (hf : IntegrableOn f U) : IntegrableOn (fun x => a x * f x) U := by
  refine (hf.abs.const_mul M).mono' (ha.mul hf.aestronglyMeasurable) ?_
  filter_upwards [hbound] with x hx
  simpa only [Real.norm_eq_abs, abs_mul] using
    mul_le_mul_of_nonneg_right hx (abs_nonneg (f x))

/-- `aux_tight_subharmonic_caccioppoli`, relaxed: `eta` need only be BOUNDED (not `[0,1]`-valued).
Same proof, only the two integrability side-conditions (`hE`, `hT`) change. -/
theorem aux_tight_subharmonic_cc_caccioppoli
    {d : ℕ} {U : Set (SpatialCoordinates d)}
    (hU : Homogenization.IsOpenBoundedConvexDomain U) {A : SpatialCoordinates d → ℝ}
    (hAmeas : AEStronglyMeasurable A (volume.restrict U)) (hApos : ∀ x, 0 ≤ A x)
    {MA : ℝ} (hAbound : ∀ x ∈ U, A x ≤ MA)
    (u w f : Homogenization.H1Function U)
    (hu : SubdiffusiveProcess.CoarseGrainingVocab.Section11.IsWeakSubSolutionOn A U u)
    {s : ℝ} (hs : 1 ≤ s)
    (hpair : SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserPowerPair u w f s)
    (hf : ∀ x, 0 ≤ f.toFun x)
    {eta : SpatialCoordinates d → ℝ}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetac : HasCompactSupport eta) (hetasub : tsupport eta ⊆ U)
    {Meta : ℝ} (hetaBound : ∀ x, |eta x| ≤ Meta) :
    ∫ x in U, A x * (eta x ^ 2 * Homogenization.vecNormSq (w.grad x)) ≤
      (4 * s ^ 2) * ∫ x in U, A x *
        (w.toFun x ^ 2 * Homogenization.vecNormSq (Homogenization.euclideanGradient eta x)) := by
  classical
  let E : SpatialCoordinates d → ℝ := fun x => eta x ^ 2 * Homogenization.vecNormSq (w.grad x)
  let Acal : SpatialCoordinates d → ℝ := fun x => A x * ((2 * s - 1) * E x)
  let B : SpatialCoordinates d → ℝ :=
    fun x => w.toFun x ^ 2 * Homogenization.vecNormSq (Homogenization.euclideanGradient eta x)
  let T : SpatialCoordinates d → ℝ := fun x =>
    w.toFun x * Homogenization.vecDot (w.grad x)
      ((2 * eta x) • Homogenization.euclideanGradient eta x)
  have habs : ∀ᵐ x ∂volume.restrict U, |A x| ≤ MA := by
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    rw [abs_of_nonneg (hApos x)]
    exact hAbound x hx
  have hE : IntegrableOn E U := by
    apply aux_tight_subharmonic_cc_integrable_mul_bounded (a := fun x => eta x ^ 2) (M := Meta ^ 2)
      (heta.continuous.aestronglyMeasurable.pow 2)
    · exact Filter.Eventually.of_forall fun x => by
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (eta x)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hetaBound x) 2
    · exact Homogenization.integrableOn_vecNormSq_h1Grad w
  have hAcal : IntegrableOn Acal U :=
    aux_tight_subharmonic_cc_integrable_mul_bounded hAmeas habs (hE.const_mul _)
  have hB : IntegrableOn B U := by
    have hb := Homogenization.WeakPoissonEquationOn.integrableOn_mul_left_of_continuous_hasCompactSupport
      (Homogenization.continuous_vecNormSq_euclideanGradient_of_contDiff heta)
      (Homogenization.hasCompactSupport_vecNormSq_euclideanGradient hetac) w.memL2.integrable_sq
    exact hb.congr_fun (fun x _ => mul_comm _ _) hU.isOpen.measurableSet
  have hdot : IntegrableOn
      (fun x => Homogenization.vecDot (w.grad x)
        (w.toFun x • Homogenization.euclideanGradient eta x)) U :=
    Homogenization.integrableOn_vecDot_of_memVectorL2 w.grad_memVectorL2
      (by
        rw [Homogenization.MemVectorL2]
        apply MemLp.of_eval
        intro i
        have hm : MemLp (fun x => Homogenization.euclideanGradient eta x i) ⊤
            (Homogenization.volumeMeasureOn U) :=
          (Homogenization.contDiff_euclideanCoordDeriv heta i).continuous.memLp_top_of_hasCompactSupport
            (Homogenization.hasCompactSupport_euclideanCoordDeriv hetac i) _
        change MemLp (fun x => w.toFun x * Homogenization.euclideanGradient eta x i) 2
          (Homogenization.volumeMeasureOn U)
        simpa only [mul_comm] using w.memL2.mul' (r := 2) hm)
  have hT : IntegrableOn T U := by
    have ht := aux_tight_subharmonic_cc_integrable_mul_bounded
      (a := fun x => 2 * eta x) (M := 2 * Meta)
      (aestronglyMeasurable_const.mul heta.continuous.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
        linarith [hetaBound x]) hdot
    apply ht.congr_fun _ hU.isOpen.measurableSet
    intro x _
    dsimp only [T]
    rw [Homogenization.vecDot_smul_right, Homogenization.vecDot_smul_right]
    ring
  have haT : IntegrableOn (fun x => A x * (s * T x)) U :=
    aux_tight_subharmonic_cc_integrable_mul_bounded hAmeas habs (hT.const_mul s)
  have hineq : ∫ x in U, Acal x ≤ -∫ x in U, A x * (s * T x) := by
    have hweak := aux_tight_subharmonic_cc_power_test_inequality hU u w f hu hpair hf heta hetac
      hetasub
    change (∫ x in U, A x * ((2 * s - 1) * E x + s * T x)) ≤ 0 at hweak
    simp_rw [mul_add] at hweak
    rw [integral_add hAcal haT] at hweak
    linarith
  let Bcal : SpatialCoordinates d → ℝ := fun x => A x * B x
  have hBcal : IntegrableOn Bcal U :=
    aux_tight_subharmonic_cc_integrable_mul_bounded hAmeas habs hB
  have hpoint : ∀ᵐ x ∂volume.restrict U,
      |A x * (s * T x)| ≤ Acal x / 2 + (2 * s ^ 2) * Bcal x := by
    filter_upwards [] with x
    have ha0 : 0 ≤ A x := hApos x
    have ht := Homogenization.WeakPoissonEquationOn.abs_sq_cutoff_error_integrand_le
      (eta x) (s * w.toFun x) (w.grad x) (Homogenization.euclideanGradient eta x)
    have ht' : |s * T x| ≤ E x / 2 + (2 * s ^ 2) * B x := by
      change |s * (w.toFun x * Homogenization.vecDot (w.grad x)
        (fun j => 2 * eta x * Homogenization.euclideanGradient eta x j))| ≤ _
      simpa only [E, B, mul_pow, mul_assoc] using ht
    have hE0 : 0 ≤ E x := mul_nonneg (sq_nonneg _) (Homogenization.vecNormSq_nonneg _)
    have hAE_le : A x * E x ≤ Acal x := by
      dsimp only [Acal]
      have h1 : 0 ≤ (s - 1) * (A x * E x) :=
        mul_nonneg (by linarith) (mul_nonneg ha0 hE0)
      nlinarith [h1]
    calc
      |A x * (s * T x)| = A x * |s * T x| := by rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ A x * (E x / 2 + (2 * s ^ 2) * B x) := mul_le_mul_of_nonneg_left ht' ha0
      _ = (A x * E x) / 2 + (2 * s ^ 2) * Bcal x := by dsimp only [Bcal]; ring
      _ ≤ Acal x / 2 + (2 * s ^ 2) * Bcal x := by linarith [hAE_le]
  have hbound := aux_tight_subharmonic_cc_integral_le_two_mul_of_le_neg_of_abs_le
    hAcal haT (hBcal.const_mul (2 * s ^ 2)) hineq hpoint
  rw [integral_const_mul] at hbound
  have hlow : ∫ x in U, A x * E x ≤ ∫ x in U, Acal x := by
    apply integral_mono_ae (aux_tight_subharmonic_cc_integrable_mul_bounded hAmeas habs hE) hAcal
    filter_upwards [] with x
    have ha0 : 0 ≤ A x := hApos x
    have hE0 : 0 ≤ E x := mul_nonneg (sq_nonneg _) (Homogenization.vecNormSq_nonneg _)
    dsimp only [Acal]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s - 1) (mul_nonneg ha0 hE0)]
  have hfinal : ∫ x in U, A x * E x ≤ (4 * s ^ 2) * ∫ x in U, Bcal x := by
    nlinarith [hlow, hbound]
  change (∫ x in U, A x * E x) ≤ (4 * s ^ 2) * ∫ x in U, Bcal x
  exact hfinal

/-- `aux_tight_subharmonic_gradient_energy`, relaxed (bounded `eta`, not `[0,1]`-valued) AND with
the SHARPER constant `8s²+2` (not `10s²`) that `aux_tight_subharmonic_cutoff_coercive` needs:
same proof, the final combination step stops one `nlinarith` earlier. -/
theorem aux_tight_subharmonic_cc_gradient_energy
    {d : ℕ} {U : Set (SpatialCoordinates d)}
    (hU : Homogenization.IsOpenBoundedConvexDomain U) {A : SpatialCoordinates d → ℝ}
    (hAmeas : AEStronglyMeasurable A (volume.restrict U)) (hApos : ∀ x, 0 ≤ A x)
    {MA : ℝ} (hAbound : ∀ x ∈ U, A x ≤ MA)
    (u w f : Homogenization.H1Function U)
    (hu : SubdiffusiveProcess.CoarseGrainingVocab.Section11.IsWeakSubSolutionOn A U u)
    {s : ℝ} (hs : 1 ≤ s)
    (hpair : SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserPowerPair u w f s)
    (hf : ∀ x, 0 ≤ f.toFun x)
    {eta : SpatialCoordinates d → ℝ}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetac : HasCompactSupport eta) (hetasub : tsupport eta ⊆ U)
    {Meta : ℝ} (hetaBound : ∀ x, |eta x| ≤ Meta) :
    ∫ x in U, A x * Homogenization.vecNormSq
        ((w.mulContDiffHasCompactSupport heta hetac).grad x) ≤
      (8 * s ^ 2 + 2) * ∫ x in U, A x *
        (w.toFun x ^ 2 * Homogenization.vecNormSq (Homogenization.euclideanGradient eta x)) := by
  have hbase := aux_tight_subharmonic_cc_caccioppoli hU hAmeas hApos hAbound u w f hu hs hpair hf
    heta hetac hetasub hetaBound
  have habs : ∀ᵐ x ∂volume.restrict U, |A x| ≤ MA := by
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    rw [abs_of_nonneg (hApos x)]
    exact hAbound x hx
  have hE : IntegrableOn (fun x => eta x ^ 2 * Homogenization.vecNormSq (w.grad x)) U := by
    apply aux_tight_subharmonic_cc_integrable_mul_bounded (a := fun x => eta x ^ 2) (M := Meta ^ 2)
      (heta.continuous.aestronglyMeasurable.pow 2)
    · exact Filter.Eventually.of_forall fun x => by
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (eta x)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hetaBound x) 2
    · exact Homogenization.integrableOn_vecNormSq_h1Grad w
  have hB : IntegrableOn
      (fun x => w.toFun x ^ 2 * Homogenization.vecNormSq (Homogenization.euclideanGradient eta x))
      U := by
    have hb := Homogenization.WeakPoissonEquationOn.integrableOn_mul_left_of_continuous_hasCompactSupport
      (Homogenization.continuous_vecNormSq_euclideanGradient_of_contDiff heta)
      (Homogenization.hasCompactSupport_vecNormSq_euclideanGradient hetac) w.memL2.integrable_sq
    exact hb.congr_fun (fun x _ => mul_comm _ _) hU.isOpen.measurableSet
  have hAE : IntegrableOn
      (fun x => A x * (eta x ^ 2 * Homogenization.vecNormSq (w.grad x))) U :=
    aux_tight_subharmonic_cc_integrable_mul_bounded hAmeas habs hE
  have hAB : IntegrableOn
      (fun x => A x * (w.toFun x ^ 2 *
        Homogenization.vecNormSq (Homogenization.euclideanGradient eta x))) U :=
    aux_tight_subharmonic_cc_integrable_mul_bounded hAmeas habs hB
  have hAprod : IntegrableOn
      (fun x => A x * Homogenization.vecNormSq
        ((w.mulContDiffHasCompactSupport heta hetac).grad x)) U := by
    have hprodmemL2 := Homogenization.integrableOn_vecNormSq_h1Grad
      (w.mulContDiffHasCompactSupport heta hetac)
    exact aux_tight_subharmonic_cc_integrable_mul_bounded hAmeas habs hprodmemL2
  have hpoint : ∀ x, A x * Homogenization.vecNormSq
      ((w.mulContDiffHasCompactSupport heta hetac).grad x) ≤
      2 * (A x * (eta x ^ 2 * Homogenization.vecNormSq (w.grad x))) +
        2 * (A x * (w.toFun x ^ 2 *
          Homogenization.vecNormSq (Homogenization.euclideanGradient eta x))) := by
    intro x
    have hb : Homogenization.vecNormSq
        ((w.mulContDiffHasCompactSupport heta hetac).grad x) ≤
        2 * (eta x ^ 2 * Homogenization.vecNormSq (w.grad x)) +
          2 * (w.toFun x ^ 2 *
            Homogenization.vecNormSq (Homogenization.euclideanGradient eta x)) := by
      rw [Homogenization.H1Function.mulContDiffHasCompactSupport_grad]
      refine (Homogenization.vecNormSq_add_le (eta x • w.grad x)
        (w.toFun x • Homogenization.euclideanGradient eta x)).trans_eq ?_
      rw [Homogenization.vecNormSq_smul, Homogenization.vecNormSq_smul]
      ring
    calc A x * Homogenization.vecNormSq ((w.mulContDiffHasCompactSupport heta hetac).grad x)
        ≤ A x * (2 * (eta x ^ 2 * Homogenization.vecNormSq (w.grad x)) +
            2 * (w.toFun x ^ 2 *
              Homogenization.vecNormSq (Homogenization.euclideanGradient eta x))) :=
          mul_le_mul_of_nonneg_left hb (hApos x)
      _ = _ := by ring
  have hmono := integral_mono_ae hAprod
    ((hAE.const_mul 2).add (hAB.const_mul 2))
    (Filter.Eventually.of_forall hpoint)
  simp only [Pi.add_apply] at hmono
  rw [integral_add (hAE.const_mul 2) (hAB.const_mul 2), integral_const_mul,
    integral_const_mul] at hmono
  linarith [hbase, hmono]

/-- A continuous function with compact support is bounded (everywhere, not just a.e.). -/
private theorem aux_tight_subharmonic_cc_bound_of_contDiff_hasCompactSupport {d : ℕ}
    {φ : SpatialCoordinates d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∃ M : ℝ, ∀ x, |φ x| ≤ M := by
  rcases (tsupport φ).eq_empty_or_nonempty with hempty | hne
  · refine ⟨0, fun x => ?_⟩
    have hx : x ∉ tsupport φ := by rw [hempty]; exact Set.notMem_empty x
    rw [image_eq_zero_of_notMem_tsupport hx]; simp
  · obtain ⟨x0, _, hmax⟩ := hφc.isCompact.exists_isMaxOn hne hφ.continuous.abs.continuousOn
    refine ⟨|φ x0|, fun x => ?_⟩
    by_cases hx : x ∈ tsupport φ
    · exact (isMaxOn_iff.mp hmax) x hx
    · rw [image_eq_zero_of_notMem_tsupport hx]; simp [abs_nonneg]

/-- A continuous function is bounded above on a bounded set. -/
private theorem aux_tight_subharmonic_cc_bound_on_isBounded {d : ℕ} {S : Set (SpatialCoordinates d)}
    (hS : Bornology.IsBounded S) {A : SpatialCoordinates d → ℝ} (hA : Continuous A) :
    ∃ M : ℝ, ∀ x ∈ S, A x ≤ M := by
  rcases (closure S).eq_empty_or_nonempty with hempty | hne
  · refine ⟨0, fun x hx => absurd (subset_closure hx) ?_⟩
    rw [hempty]; exact Set.notMem_empty x
  · obtain ⟨x0, _, hmax⟩ := hS.isCompact_closure.exists_isMaxOn hne hA.continuousOn
    exact ⟨A x0, fun x hx => (isMaxOn_iff.mp hmax) x (subset_closure hx)⟩

/-- `eLpNorm f 2 μ → 0` implies `∫ f² dμ → 0` (real-valued Bochner integral), for `f n ∈ L²`. -/
private theorem aux_tight_subharmonic_cc_integral_sq_tendsto_zero_of_eLpNorm_tendsto_zero {d : ℕ}
    {U : Set (SpatialCoordinates d)} {f : ℕ → SpatialCoordinates d → ℝ}
    (hf2 : ∀ n, MemLp (f n) 2 (volume.restrict U))
    (hf : Filter.Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict U)) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫ x in U, (f n x) ^ 2) Filter.atTop (𝓝 (0 : ℝ)) := by
  have hsq_nonneg : ∀ n, 0 ≤ ∫ x in U, (f n x) ^ 2 :=
    fun n => integral_nonneg (fun x => sq_nonneg _)
  have heq : ∀ n, eLpNorm (f n) 2 (volume.restrict U) =
      ENNReal.ofReal (Real.sqrt (∫ x in U, (f n x) ^ 2)) := by
    intro n
    rw [(hf2 n).eLpNorm_eq_integral_rpow_norm (two_ne_zero) (by norm_num), Real.sqrt_eq_rpow]
    norm_num
  have hsqrt_tendsto : Filter.Tendsto (fun n => Real.sqrt (∫ x in U, (f n x) ^ 2))
      Filter.atTop (𝓝 (0:ℝ)) := by
    have hofReal := hf.congr heq
    have htoReal : Filter.Tendsto
        (fun n => (ENNReal.ofReal (Real.sqrt (∫ x in U, (f n x) ^ 2))).toReal)
        Filter.atTop (𝓝 (0:ℝ)) :=
      (ENNReal.tendsto_toReal (a := (0:ℝ≥0∞)) (by simp)).comp hofReal
    simpa [ENNReal.toReal_ofReal, Real.sqrt_nonneg] using htoReal
  have hcont := (continuous_pow 2).continuousAt.tendsto.comp hsqrt_tendsto
  rw [show ((0:ℝ)) ^ 2 = (0:ℝ) by norm_num] at hcont
  exact hcont.congr (fun n => Real.sq_sqrt (hsq_nonneg n))

private instance aux_tight_subharmonic_cc_holderTriple_two_two_one :
    ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) (1 : ℝ≥0∞) := by
  constructor
  rw [← two_mul, inv_one]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- An a.e. fact w.r.t. `volume.restrict U` that holds pointwise-everywhere off `U` upgrades to an
a.e. fact w.r.t. `volume.restrict V` for any `U ⊆ V` (no measurability of `U` needed): the failure
set is a subset of `U`, and `Measure.restrict_eq_self` identifies the restricted measure of any
subset of the restricting set with its unrestricted measure, for either restricting set. -/
private theorem aux_tight_subharmonic_cc_ae_restrict_of_ae_restrict_subset {d : ℕ}
    {U V : Set (SpatialCoordinates d)} {P : SpatialCoordinates d → Prop} (hUV : U ⊆ V)
    (h : ∀ᵐ x ∂volume.restrict U, P x) (hcompl : ∀ x, x ∉ U → P x) :
    ∀ᵐ x ∂volume.restrict V, P x := by
  rw [ae_iff] at h ⊢
  have hNU : {x | ¬P x} ⊆ U := fun x hx => by_contra fun hxU => hx (hcompl x hxU)
  rw [Measure.restrict_eq_self volume hNU] at h
  rw [Measure.restrict_eq_self volume (hNU.trans hUV)]
  exact h

/-- A pointwise bound `∀ x ∈ U, |K x| ≤ MK` upgrades to an a.e. bound w.r.t. `volume.restrict U`,
for ANY set `U` (no `MeasurableSet U` needed): the "bad set" `{|K| > MK}` is null-measurable from
`K`'s own (ae)strong measurability, and disjoint from `U`, so `Measure.restrict_apply₀` gives it
measure zero without ever needing `U` itself to be measurable. -/
private theorem aux_tight_subharmonic_cc_ae_bound_of_forall_mem {d : ℕ} {U : Set (SpatialCoordinates d)}
    {K : SpatialCoordinates d → ℝ} {MK : ℝ}
    (hKmeas : AEStronglyMeasurable K (volume.restrict U))
    (hbound : ∀ x ∈ U, |K x| ≤ MK) :
    ∀ᵐ x ∂volume.restrict U, |K x| ≤ MK := by
  have hKabs_meas : AEStronglyMeasurable (fun x => |K x|) (volume.restrict U) := by
    simpa [Real.norm_eq_abs] using hKmeas.norm
  have h1 : NullMeasurableSet {x | |K x| ≤ MK} (volume.restrict U) :=
    hKabs_meas.nullMeasurableSet_le aestronglyMeasurable_const
  rw [ae_iff]
  rw [show {x | ¬|K x| ≤ MK} = {x | |K x| ≤ MK}ᶜ from rfl, Measure.restrict_apply₀ h1.compl]
  have hempty : {x | |K x| ≤ MK}ᶜ ∩ U = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨hlt, hxU⟩
    exact hlt (hbound x hxU)
  rw [hempty]
  exact measure_empty

/-- Bounded times `L²` is `L²`. -/
private theorem aux_tight_subharmonic_cc_memLp_mul_bounded {d : ℕ} {U : Set (SpatialCoordinates d)}
    {K ψ : SpatialCoordinates d → ℝ} {MK : ℝ}
    (hKmeas : AEStronglyMeasurable K (volume.restrict U))
    (hKbound : ∀ᵐ x ∂volume.restrict U, |K x| ≤ MK) (hψ : MemLp ψ 2 (volume.restrict U)) :
    MemLp (fun x => K x * ψ x) 2 (volume.restrict U) := by
  refine MemLp.mono' (hψ.abs.const_mul MK) (hKmeas.mul hψ.aestronglyMeasurable) ?_
  filter_upwards [hKbound] with x hx
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

/-- Superadditivity of `liminf` for `ℝ≥0∞`-valued sequences (Mathlib's `le_liminf_add` needs an
`AddCommGroup`, unavailable for `ℝ≥0∞`). Supplied by db (multifractaldiffusion-ca), compiled in
their harness. -/
private theorem aux_tight_subharmonic_cc_le_liminf_add_ennreal (u v : ℕ → ℝ≥0∞) :
    Filter.liminf u Filter.atTop + Filter.liminf v Filter.atTop ≤
      Filter.liminf (fun n => u n + v n) Filter.atTop := by
  simp only [liminf_eq_iSup_iInf_of_nat]
  rw [ENNReal.iSup_add_iSup]
  · refine iSup_mono fun n => le_iInf₂ fun i hi => add_le_add (iInf₂_le i hi) (iInf₂_le i hi)
  · intro i j
    refine ⟨max i j, add_le_add ?_ ?_⟩
    · exact le_iInf₂ fun k hk => iInf₂_le k ((le_max_left i j).trans hk)
    · exact le_iInf₂ fun k hk => iInf₂_le k ((le_max_right i j).trans hk)

/-- If `K` is bounded and measurable, `φ n → ψ` in `L²`, then `∫ K φ n² → ∫ K ψ²`. -/
private theorem aux_tight_subharmonic_cc_weighted_sq_tendsto {d : ℕ} {U : Set (SpatialCoordinates d)}
    {K : SpatialCoordinates d → ℝ} {MK : ℝ} (hMK : 0 ≤ MK)
    (hKmeas : AEStronglyMeasurable K (volume.restrict U))
    (hKbound : ∀ᵐ x ∂volume.restrict U, |K x| ≤ MK)
    {φ : ℕ → SpatialCoordinates d → ℝ} {ψ : SpatialCoordinates d → ℝ}
    (hφmemLp : ∀ n, MemLp (φ n) 2 (volume.restrict U))
    (hψmemLp : MemLp ψ 2 (volume.restrict U))
    (hδ : Filter.Tendsto (fun n => eLpNorm (fun x => φ n x - ψ x) 2 (volume.restrict U))
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫ x in U, K x * (φ n x) ^ 2) Filter.atTop
      (𝓝 (∫ x in U, K x * (ψ x) ^ 2)) := by
  have hdiffmemLp : ∀ n, MemLp (fun x => φ n x - ψ x) 2 (volume.restrict U) :=
    fun n => (hφmemLp n).sub hψmemLp
  have hδ0 := aux_tight_subharmonic_cc_integral_sq_tendsto_zero_of_eLpNorm_tendsto_zero hdiffmemLp hδ
  have hKψmemLp : MemLp (fun x => K x * ψ x) 2 (volume.restrict U) :=
    aux_tight_subharmonic_cc_memLp_mul_bounded hKmeas hKbound hψmemLp
  have hψsq_int : IntegrableOn (fun x => K x * (ψ x) ^ 2) U :=
    aux_tight_subharmonic_cc_integrable_mul_bounded hKmeas hKbound hψmemLp.integrable_sq
  have hdiffsq_int : ∀ n, IntegrableOn (fun x => K x * (φ n x - ψ x) ^ 2) U :=
    fun n => aux_tight_subharmonic_cc_integrable_mul_bounded hKmeas hKbound (hdiffmemLp n).integrable_sq
  have hcross_int : ∀ n, Integrable (fun x => (φ n x - ψ x) * (K x * ψ x))
      (volume.restrict U) :=
    fun n => (hdiffmemLp n).integrable_mul hKψmemLp
  have hsplit : ∀ n, ∫ x in U, K x * (φ n x) ^ 2 =
      (∫ x in U, K x * (ψ x) ^ 2) + (∫ x in U, K x * (φ n x - ψ x) ^ 2) +
        2 * ∫ x in U, (φ n x - ψ x) * (K x * ψ x) := by
    intro n
    have hident : ∀ x, K x * (φ n x) ^ 2 =
        (K x * (ψ x) ^ 2 + K x * (φ n x - ψ x) ^ 2) +
          2 * ((φ n x - ψ x) * (K x * ψ x)) := by
      intro x; ring
    calc ∫ x in U, K x * (φ n x) ^ 2
        = ∫ x in U, ((K x * (ψ x) ^ 2 + K x * (φ n x - ψ x) ^ 2) +
            2 * ((φ n x - ψ x) * (K x * ψ x))) :=
          integral_congr_ae (Filter.Eventually.of_forall hident)
      _ = (∫ x in U, (K x * (ψ x) ^ 2 + K x * (φ n x - ψ x) ^ 2)) +
            ∫ x in U, 2 * ((φ n x - ψ x) * (K x * ψ x)) :=
          integral_add (hψsq_int.add (hdiffsq_int n)) ((hcross_int n).const_mul 2)
      _ = ((∫ x in U, K x * (ψ x) ^ 2) + ∫ x in U, K x * (φ n x - ψ x) ^ 2) +
            2 * ∫ x in U, (φ n x - ψ x) * (K x * ψ x) := by
          rw [integral_add hψsq_int (hdiffsq_int n), integral_const_mul]
  have hcross_le : ∀ n, |∫ x in U, (φ n x - ψ x) * (K x * ψ x)| ≤
      Real.sqrt (∫ x in U, (φ n x - ψ x) ^ 2) * Real.sqrt (∫ x in U, (K x * ψ x) ^ 2) := by
    intro n
    have hofReal2 : ENNReal.ofReal (2:ℝ) = (2:ℝ≥0∞) := by norm_num
    have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (f := fun x => |φ n x - ψ x|)
      (g := fun x => |K x * ψ x|) (p := 2) (q := 2)
      ⟨by norm_num, by norm_num, by norm_num⟩
      (Filter.Eventually.of_forall (fun x => abs_nonneg _))
      (Filter.Eventually.of_forall (fun x => abs_nonneg _))
      (hofReal2 ▸ (hdiffmemLp n).abs) (hofReal2 ▸ hKψmemLp.abs)
    have habs1 : ∀ x, |φ n x - ψ x| ^ (2:ℝ) = (φ n x - ψ x) ^ 2 := by
      intro x
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have habs2 : ∀ x, |K x * ψ x| ^ (2:ℝ) = (K x * ψ x) ^ 2 := by
      intro x
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    simp only [habs1, habs2] at hCS
    calc |∫ x in U, (φ n x - ψ x) * (K x * ψ x)|
        ≤ ∫ x in U, |(φ n x - ψ x) * (K x * ψ x)| := abs_integral_le_integral_abs
      _ = ∫ x in U, |φ n x - ψ x| * |K x * ψ x| := by
          apply integral_congr_ae; filter_upwards [] with x; rw [abs_mul]
      _ ≤ _ := by
          rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]; exact hCS
  have hcross_tendsto : Filter.Tendsto
      (fun n => ∫ x in U, (φ n x - ψ x) * (K x * ψ x)) Filter.atTop (𝓝 (0:ℝ)) := by
    have hbound : Filter.Tendsto
        (fun n => Real.sqrt (∫ x in U, (φ n x - ψ x) ^ 2) *
          Real.sqrt (∫ x in U, (K x * ψ x) ^ 2)) Filter.atTop (𝓝 (0:ℝ)) := by
      have h1 : Filter.Tendsto (fun n => Real.sqrt (∫ x in U, (φ n x - ψ x) ^ 2))
          Filter.atTop (𝓝 (0:ℝ)) := by
        have := (Real.continuous_sqrt.continuousAt.tendsto).comp hδ0
        simpa using! this
      simpa using h1.mul_const (Real.sqrt (∫ x in U, (K x * ψ x) ^ 2))
    exact squeeze_zero_norm' (Filter.Eventually.of_forall (fun n => by
      rw [Real.norm_eq_abs]; exact hcross_le n)) hbound
  have hleft_tendsto : Filter.Tendsto
      (fun n => ∫ x in U, K x * (φ n x - ψ x) ^ 2) Filter.atTop (𝓝 (0:ℝ)) := by
    have hbound : Filter.Tendsto (fun n => MK * ∫ x in U, (φ n x - ψ x) ^ 2)
        Filter.atTop (𝓝 (0:ℝ)) := by
      simpa using hδ0.const_mul MK
    refine squeeze_zero_norm' (Filter.Eventually.of_forall (fun n => ?_)) hbound
    rw [Real.norm_eq_abs]
    calc |∫ x in U, K x * (φ n x - ψ x) ^ 2|
        ≤ ∫ x in U, |K x * (φ n x - ψ x) ^ 2| := abs_integral_le_integral_abs
      _ ≤ ∫ x in U, MK * (φ n x - ψ x) ^ 2 := by
          apply integral_mono_ae (hdiffsq_int n).abs
            ((hdiffmemLp n).integrable_sq.const_mul MK)
          filter_upwards [hKbound] with x hx
          rw [abs_mul, abs_of_nonneg (sq_nonneg (φ n x - ψ x))]
          exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)
      _ = MK * ∫ x in U, (φ n x - ψ x) ^ 2 := integral_const_mul _ _
  have hconst : Filter.Tendsto (fun _ : ℕ => ∫ x in U, K x * (ψ x) ^ 2) Filter.atTop
      (𝓝 (∫ x in U, K x * (ψ x) ^ 2)) := tendsto_const_nhds
  have := Filter.Tendsto.add (Filter.Tendsto.add hconst hleft_tendsto)
    (hcross_tendsto.const_mul 2)
  simp only [add_zero, mul_zero] at this
  refine this.congr (fun n => ?_)
  rw [hsplit n]

/-- The `H¹₀(V)` test `eta_n · w'` used throughout the CC principal, named so that the separate
`aux_cc_*` lemmas below refer to syntactically the same term. -/
private noncomputable def aux_tight_subharmonic_cc_G {d : ℕ} {V U : Set (SpatialCoordinates d)}
    (hV : Homogenization.IsOpenBoundedConvexDomain V) (hUV : U ⊆ V)
    (w' : Homogenization.H1Function V) (chi : Homogenization.H10Function U) (n : ℕ) :
    Homogenization.H10Function V :=
  w'.mulContDiffHasCompactSupportToH10 hV (chi.approx_smooth n) (chi.approx_hasCompactSupport n)
    ((chi.approx_support_subset n).trans hUV)

/-- Per-`n` Caccioppoli/gradient-energy bound for `g_n := aux_tight_subharmonic_cc_G hV hUV w' chi n`, DESIGN.md §(CC)
steps up to `hstepR`. -/
private theorem aux_tight_subharmonic_cc_stepR {d : ℕ} {V U : Set (SpatialCoordinates d)}
    (hV : Homogenization.IsOpenBoundedConvexDomain V) (hUV : U ⊆ V)
    {A : SpatialCoordinates d → ℝ} (hA : Continuous A) (hApos : ∀ x, 0 < A x)
    (w : Homogenization.H1Function V) (hw0 : ∀ x, 0 ≤ w.toFun x) {Mw : ℝ}
    (hwM : ∀ x, w.toFun x ≤ Mw)
    (hsub : SubdiffusiveProcess.CoarseGrainingVocab.Section11.IsWeakSubSolutionOn A V w)
    {s : ℝ} (hs : 1 ≤ s) (chi : Homogenization.H10Function U)
    (w' f' : Homogenization.H1Function V)
    (hpair : SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserPowerPair w w' f' s)
    (hf'nonneg : ∀ x, 0 ≤ f'.toFun x) (hw'toFun : ∀ x, w'.toFun x = w.toFun x ^ s) :
    ∀ n, ∫ x in V, A x * Homogenization.vecNormSq
        ((aux_tight_subharmonic_cc_G hV hUV w' chi n).toH1Function.grad x) ≤
      (8 * s ^ 2 + 2) * ∫ x in U, w.toFun x ^ (2 * s) *
        (A x * Homogenization.vecNormSq
          (Homogenization.euclideanGradient (chi.approx n) x)) := by
  have hw'sq : ∀ x, w'.toFun x ^ 2 = w.toFun x ^ (2 * s) := by
    intro x
    rw [hw'toFun x, ← Real.rpow_natCast (w.toFun x ^ s) 2, ← Real.rpow_mul (hw0 x)]
    congr 1
    push_cast
    ring
  have hAmeas : AEStronglyMeasurable A (volume.restrict V) := hA.aestronglyMeasurable
  have hApos' : ∀ x, 0 ≤ A x := fun x => (hApos x).le
  obtain ⟨MA, hMAbound⟩ := aux_tight_subharmonic_cc_bound_on_isBounded hV.isBoundedDomain.isBounded hA
  have habsA : ∀ᵐ x ∂volume.restrict V, |A x| ≤ MA := by
    filter_upwards [ae_restrict_mem hV.isOpen.measurableSet] with x hx
    rw [abs_of_nonneg (hApos' x)]; exact hMAbound x hx
  have hrestrict : ∀ n,
      ∫ x in V, A x * (w'.toFun x ^ 2 *
          Homogenization.vecNormSq (Homogenization.euclideanGradient (chi.approx n) x)) =
        ∫ x in U, w.toFun x ^ (2 * s) *
          (A x * Homogenization.vecNormSq
            (Homogenization.euclideanGradient (chi.approx n) x)) := by
    intro n
    rw [show (fun x => A x * (w'.toFun x ^ 2 *
            Homogenization.vecNormSq (Homogenization.euclideanGradient (chi.approx n) x))) =
          (fun x => w.toFun x ^ (2 * s) *
            (A x * Homogenization.vecNormSq
              (Homogenization.euclideanGradient (chi.approx n) x))) from
        funext fun x => by rw [hw'sq x]; ring]
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero hV.isOpen.measurableSet hUV
    intro x hx
    have hxsupp : x ∉ tsupport (chi.approx n) :=
      fun hmem => hx.2 (chi.approx_support_subset n hmem)
    rw [Homogenization.euclideanGradient_eq_zero_of_notMem_tsupport hxsupp]
    simp [Homogenization.vecNormSq, Homogenization.vecDot]
  have hgrad_energy : ∀ n,
      ∫ x in V, A x * Homogenization.vecNormSq
          ((w'.mulContDiffHasCompactSupport (chi.approx_smooth n)
            (chi.approx_hasCompactSupport n)).grad x) ≤
        (8 * s ^ 2 + 2) * ∫ x in U, w.toFun x ^ (2 * s) *
          (A x * Homogenization.vecNormSq
            (Homogenization.euclideanGradient (chi.approx n) x)) := by
    intro n
    obtain ⟨Meta, hMetaBound⟩ :=
      aux_tight_subharmonic_cc_bound_of_contDiff_hasCompactSupport (chi.approx_smooth n)
        (chi.approx_hasCompactSupport n)
    have h := aux_tight_subharmonic_cc_gradient_energy hV hAmeas hApos' hMAbound w w' f' hsub hs hpair hf'nonneg
      (chi.approx_smooth n) (chi.approx_hasCompactSupport n)
      ((chi.approx_support_subset n).trans hUV) hMetaBound
    rw [hrestrict n] at h
    exact h
  have hg_grad_ae : ∀ n, (fun x => (aux_tight_subharmonic_cc_G hV hUV w' chi n).toH1Function.grad x) =ᵐ[volume.restrict V]
      fun x => (w'.mulContDiffHasCompactSupport (chi.approx_smooth n)
        (chi.approx_hasCompactSupport n)).grad x := by
    intro n
    have h := Homogenization.WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae
      w' hV (chi.approx_smooth n) (chi.approx_hasCompactSupport n)
      ((chi.approx_support_subset n).trans hUV)
    simpa [Homogenization.H1Function.mulContDiffHasCompactSupport_grad] using! h
  intro n
  calc ∫ x in V, A x * Homogenization.vecNormSq ((aux_tight_subharmonic_cc_G hV hUV w' chi n).toH1Function.grad x)
      = ∫ x in V, A x * Homogenization.vecNormSq
          ((w'.mulContDiffHasCompactSupport (chi.approx_smooth n)
            (chi.approx_hasCompactSupport n)).grad x) := by
        apply integral_congr_ae
        filter_upwards [hg_grad_ae n] with x hx
        rw [hx]
    _ ≤ (8 * s ^ 2 + 2) * ∫ x in U, w.toFun x ^ (2 * s) *
          (A x * Homogenization.vecNormSq
            (Homogenization.euclideanGradient (chi.approx n) x)) :=
        hgrad_energy n

/-- The RHS tendsto: `∫ x in U, w^{2s}*(A*|∇eta_n|²) → ∫ x in U, w^{2s}*(A*|∇chi|²)`. No Moser
data needed. -/
private theorem aux_tight_subharmonic_cc_rhs_tendsto {d : ℕ} {V U : Set (SpatialCoordinates d)}
    (hV : Homogenization.IsOpenBoundedConvexDomain V) (hUV : U ⊆ V)
    {A : SpatialCoordinates d → ℝ} (hA : Continuous A) (hApos : ∀ x, 0 < A x)
    (w : Homogenization.H1Function V) (hw0 : ∀ x, 0 ≤ w.toFun x) {Mw : ℝ}
    (hwM : ∀ x, w.toFun x ≤ Mw) {s : ℝ} (hs : 1 ≤ s) (chi : Homogenization.H10Function U) :
    Filter.Tendsto
      (fun n => ∫ x in U, w.toFun x ^ (2 * s) *
        (A x * Homogenization.vecNormSq (Homogenization.euclideanGradient (chi.approx n) x)))
      Filter.atTop
      (𝓝 (∫ x in U, w.toFun x ^ (2 * s) *
        (A x * Homogenization.vecNormSq (chi.grad x)))) := by
  have hw0M : 0 ≤ Mw := le_trans (hw0 0) (hwM 0)
  have hwU_memLp : Homogenization.MemL2On U w.toFun :=
    w.memL2.mono_measure (Measure.restrict_mono_set volume hUV)
  have hwrpow_cont : Continuous (fun t : ℝ => t ^ (2 * s)) :=
    continuous_iff_continuousAt.mpr
      (fun x => Real.continuousAt_rpow_const x (2 * s) (Or.inr (by linarith)))
  have hK_meas : AEStronglyMeasurable (fun x => w.toFun x ^ (2 * s) * A x)
      (volume.restrict U) :=
    (hwrpow_cont.comp_aestronglyMeasurable hwU_memLp.aestronglyMeasurable).mul hA.aestronglyMeasurable
  obtain ⟨MA, hMAbound⟩ := aux_tight_subharmonic_cc_bound_on_isBounded hV.isBoundedDomain.isBounded hA
  have hK_bound_forall : ∀ x ∈ U,
      |w.toFun x ^ (2 * s) * A x| ≤ |Mw ^ (2 * s) * MA| := by
    intro x hxU
    have hxV : x ∈ V := hUV hxU
    calc |w.toFun x ^ (2 * s) * A x|
        = w.toFun x ^ (2 * s) * A x := by
          rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hw0 x) _) (hApos x).le)]
      _ ≤ Mw ^ (2 * s) * MA :=
          mul_le_mul (Real.rpow_le_rpow (hw0 x) (hwM x) (by linarith))
            (hMAbound x hxV) (hApos x).le (Real.rpow_nonneg hw0M _)
      _ ≤ |Mw ^ (2 * s) * MA| := le_abs_self _
  have hK_bound : ∀ᵐ x ∂volume.restrict U,
      |w.toFun x ^ (2 * s) * A x| ≤ |Mw ^ (2 * s) * MA| :=
    aux_tight_subharmonic_cc_ae_bound_of_forall_mem hK_meas hK_bound_forall
  have hφmemLp : ∀ i n, MemLp (fun x => (fderiv ℝ (chi.approx n) x) (Homogenization.basisVec i)) 2
      (volume.restrict U) := by
    intro i n
    have hcont : Continuous (fun x => (fderiv ℝ (chi.approx n) x) (Homogenization.basisVec i)) :=
      ((chi.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
    have hcs : HasCompactSupport (fun x => (fderiv ℝ (chi.approx n) x) (Homogenization.basisVec i)) :=
      (chi.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (Homogenization.basisVec i)
    exact (hcont.memLp_of_hasCompactSupport hcs).restrict U
  have hψmemLp : ∀ i : Fin d, MemLp (fun x => chi.grad x i) 2 (volume.restrict U) :=
    chi.gradMemL2
  have hcomp_tendsto : ∀ i : Fin d, Filter.Tendsto
      (fun n => ∫ x in U, (w.toFun x ^ (2 * s) * A x) *
        ((fderiv ℝ (chi.approx n) x) (Homogenization.basisVec i)) ^ 2)
      Filter.atTop (𝓝 (∫ x in U, (w.toFun x ^ (2 * s) * A x) * (chi.grad x i) ^ 2)) :=
    fun i => aux_tight_subharmonic_cc_weighted_sq_tendsto (abs_nonneg _) hK_meas hK_bound
      (hφmemLp i) (hψmemLp i) (chi.tendsto_approx_grad i)
  have hcompsq_int : ∀ i n, IntegrableOn (fun x => (w.toFun x ^ (2 * s) * A x) *
      ((fderiv ℝ (chi.approx n) x) (Homogenization.basisVec i)) ^ 2) U :=
    fun i n => aux_tight_subharmonic_cc_integrable_mul_bounded hK_meas hK_bound (hφmemLp i n).integrable_sq
  have hchisq_int : ∀ i, IntegrableOn (fun x => (w.toFun x ^ (2 * s) * A x) *
      (chi.grad x i) ^ 2) U :=
    fun i => aux_tight_subharmonic_cc_integrable_mul_bounded hK_meas hK_bound (hψmemLp i).integrable_sq
  have heta_eq : ∀ n, ∫ x in U, w.toFun x ^ (2 * s) *
      (A x * Homogenization.vecNormSq (Homogenization.euclideanGradient (chi.approx n) x)) =
      ∑ i : Fin d, ∫ x in U, (w.toFun x ^ (2 * s) * A x) *
        ((fderiv ℝ (chi.approx n) x) (Homogenization.basisVec i)) ^ 2 := by
    intro n
    rw [show (fun x => w.toFun x ^ (2 * s) * (A x * Homogenization.vecNormSq
            (Homogenization.euclideanGradient (chi.approx n) x))) =
          (fun x => ∑ i : Fin d, (w.toFun x ^ (2 * s) * A x) *
            ((fderiv ℝ (chi.approx n) x) (Homogenization.basisVec i)) ^ 2) from
        funext fun x => by
          simp only [Homogenization.vecNormSq, Homogenization.vecDot,
            Homogenization.euclideanGradient, Homogenization.euclideanCoordDeriv,
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring]
    exact integral_finset_sum Finset.univ (fun i _ => hcompsq_int i n)
  have hchi_eq : ∫ x in U, w.toFun x ^ (2 * s) *
      (A x * Homogenization.vecNormSq (chi.grad x)) =
      ∑ i : Fin d, ∫ x in U, (w.toFun x ^ (2 * s) * A x) * (chi.grad x i) ^ 2 := by
    rw [show (fun x => w.toFun x ^ (2 * s) *
            (A x * Homogenization.vecNormSq (chi.grad x))) =
          (fun x => ∑ i : Fin d, (w.toFun x ^ (2 * s) * A x) * (chi.grad x i) ^ 2) from
        funext fun x => by
          simp only [Homogenization.vecNormSq, Homogenization.vecDot, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring]
    exact integral_finset_sum Finset.univ (fun i _ => hchisq_int i)
  have hsum : Filter.Tendsto
      (fun n => ∑ i : Fin d, ∫ x in U, (w.toFun x ^ (2 * s) * A x) *
        ((fderiv ℝ (chi.approx n) x) (Homogenization.basisVec i)) ^ 2)
      Filter.atTop
      (𝓝 (∑ i : Fin d, ∫ x in U, (w.toFun x ^ (2 * s) * A x) * (chi.grad x i) ^ 2)) :=
    tendsto_finset_sum Finset.univ (fun i _ => hcomp_tendsto i)
  rw [hchi_eq]
  exact hsum.congr (fun n => (heta_eq n).symm)

/-- Subsequence extraction + double/single Fatou + one `hcoer` application, giving the target's
LHS bounded by the `liminf` of `ofReal Kc` times the (lintegral) gradient energy of `g_(σ n)`. -/
private theorem aux_tight_subharmonic_cc_fatou_bound {d : ℕ} {V U : Set (SpatialCoordinates d)}
    (hV : Homogenization.IsOpenBoundedConvexDomain V) (hUV : U ⊆ V)
    {A : SpatialCoordinates d → ℝ} (hApos : ∀ x, 0 < A x)
    (w : Homogenization.H1Function V) (hw0 : ∀ x, 0 ≤ w.toFun x)
    {s : ℝ} {Kc : ℝ} (hKc : 0 ≤ Kc)
    (hcoer : ∀ v : Homogenization.H10Function V,
        (∫⁻ x in V, ∫⁻ z in V, ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
            ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
          ∫⁻ x in V, ENNReal.ofReal (v.toFun x ^ 2) ≤
        ENNReal.ofReal Kc *
          ∫⁻ x in V, ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x)))
    (chi : Homogenization.H10Function U) (hchisupp : tsupport chi.toFun ⊆ U)
    (w' : Homogenization.H1Function V) (hw'toFun : ∀ x, w'.toFun x = w.toFun x ^ s) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ((∫⁻ x in V, ∫⁻ z in V,
          ENNReal.ofReal ((chi.toFun x * w.toFun x ^ s - chi.toFun z * w.toFun z ^ s) ^ 2) /
            ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
        ∫⁻ x in V, ENNReal.ofReal ((chi.toFun x * w.toFun x ^ s) ^ 2)) ≤
      Filter.liminf (fun n => ENNReal.ofReal Kc * ∫⁻ x in V, ENNReal.ofReal
        (A x * Homogenization.vecDot ((aux_tight_subharmonic_cc_G hV hUV w' chi (σ n)).toH1Function.grad x)
          ((aux_tight_subharmonic_cc_G hV hUV w' chi (σ n)).toH1Function.grad x))) Filter.atTop := by
  set g : ℕ → Homogenization.H10Function V := fun n => aux_tight_subharmonic_cc_G hV hUV w' chi n with hg_def
  have hg_toFun : ∀ n, (g n).toH1Function.toFun = fun x => chi.approx n x * w'.toFun x := fun n =>
    Homogenization.H1Function.mulContDiffHasCompactSupportToH10_toFun w' hV
      (chi.approx_smooth n) (chi.approx_hasCompactSupport n)
      ((chi.approx_support_subset n).trans hUV)
  have htendstoInMeasure :
      MeasureTheory.TendstoInMeasure (volume.restrict U) chi.approx Filter.atTop chi.toFun :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero chi.tendsto_approx
  obtain ⟨σ, hσ_mono, hσ_ae⟩ := htendstoInMeasure.exists_seq_tendsto_ae
  have hcompl_eta : ∀ x, x ∉ U → Filter.Tendsto (fun k => chi.approx (σ k) x) Filter.atTop
      (𝓝 (chi.toFun x)) := by
    intro x hxU
    have h1 : ∀ k, chi.approx (σ k) x = 0 := fun k =>
      image_eq_zero_of_notMem_tsupport (fun hmem => hxU (chi.approx_support_subset (σ k) hmem))
    have h2 : chi.toFun x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hmem => hxU (hchisupp hmem))
    simpa [h1, h2] using tendsto_const_nhds (α := ℝ) (x := (0:ℝ)) (f := Filter.atTop (α := ℕ))
  have hσ_ae_V : ∀ᵐ x ∂volume.restrict V,
      Filter.Tendsto (fun k => chi.approx (σ k) x) Filter.atTop (𝓝 (chi.toFun x)) :=
    aux_tight_subharmonic_cc_ae_restrict_of_ae_restrict_subset hUV hσ_ae hcompl_eta
  have hg_ae_tendsto : ∀ᵐ x ∂volume.restrict V,
      Filter.Tendsto (fun k => (g (σ k)).toFun x) Filter.atTop
        (𝓝 (chi.toFun x * w.toFun x ^ s)) := by
    filter_upwards [hσ_ae_V] with x hx
    have heq : (fun k => (g (σ k)).toFun x) = (fun k => chi.approx (σ k) x * w'.toFun x) :=
      funext fun k => congrFun (hg_toFun (σ k)) x
    rw [heq, ← hw'toFun x]
    exact hx.mul_const (w'.toFun x)
  have hg_toFun_meas : ∀ k, AEStronglyMeasurable (fun x => (g k).toFun x)
      (volume.restrict V) := by
    intro k
    rw [hg_toFun]
    exact ((chi.approx_smooth k).continuous.aestronglyMeasurable).mul w'.memL2.aestronglyMeasurable
  have hL2_meas : ∀ k, AEMeasurable (fun x => ENNReal.ofReal (((g (σ k)).toFun x) ^ 2))
      (volume.restrict V) :=
    fun k => (ENNReal.continuous_ofReal.comp (continuous_pow 2)).aemeasurable.comp_aemeasurable
      (hg_toFun_meas (σ k)).aemeasurable
  have hL2_fatou : ∫⁻ x in V, ENNReal.ofReal ((chi.toFun x * w.toFun x ^ s) ^ 2) ≤
      Filter.liminf (fun k => ∫⁻ x in V, ENNReal.ofReal (((g (σ k)).toFun x) ^ 2))
        Filter.atTop := by
    have hstep := MeasureTheory.lintegral_liminf_le' (u := Filter.atTop) hL2_meas
    have hliminf_eq :
        (fun x => Filter.liminf (fun k => ENNReal.ofReal (((g (σ k)).toFun x) ^ 2))
            Filter.atTop) =ᵐ[volume.restrict V]
          (fun x => ENNReal.ofReal ((chi.toFun x * w.toFun x ^ s) ^ 2)) := by
      filter_upwards [hg_ae_tendsto] with x hx
      have hcont2 : Continuous (fun t : ℝ => ENNReal.ofReal (t ^ 2)) :=
        ENNReal.continuous_ofReal.comp (continuous_pow 2)
      exact (hcont2.continuousAt.tendsto.comp hx).liminf_eq
    rw [lintegral_congr_ae hliminf_eq] at hstep
    exact hstep
  have hlim_meas : AEStronglyMeasurable (fun x => chi.toFun x * w.toFun x ^ s)
      (volume.restrict V) :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop (fun k => hg_toFun_meas (σ k)) hg_ae_tendsto
  set den : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (‖p.1 - p.2‖ ^ ((d : ℝ) + 3 / 2)) with hden_def
  set qn : ℕ → SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ :=
    fun n p => ENNReal.ofReal (((g (σ n)).toFun p.1 - (g (σ n)).toFun p.2) ^ 2) / den p
    with hqn_def
  set qlim : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((chi.toFun p.1 * w.toFun p.1 ^ s -
      chi.toFun p.2 * w.toFun p.2 ^ s) ^ 2) / den p with hqlim_def
  have hden_meas : Measurable den := by
    have h1 : Continuous (fun p : SpatialCoordinates d × SpatialCoordinates d => ‖p.1 - p.2‖) := by
      fun_prop
    have h2 : Continuous (fun t : ℝ => t ^ ((d : ℝ) + 3 / 2)) :=
      continuous_iff_continuousAt.mpr
        (fun x => Real.continuousAt_rpow_const x _ (Or.inr (by positivity)))
    exact (ENNReal.continuous_ofReal.comp (h2.comp h1)).measurable
  have hfn : ∀ n, AEMeasurable (fun x => (g (σ n)).toFun x) (volume.restrict V) :=
    fun n => (hg_toFun_meas (σ n)).aemeasurable
  have hlimfn : AEMeasurable (fun x => chi.toFun x * w.toFun x ^ s) (volume.restrict V) :=
    hlim_meas.aemeasurable
  have hnum : ∀ n, AEMeasurable
      (fun p : SpatialCoordinates d × SpatialCoordinates d =>
        ENNReal.ofReal (((g (σ n)).toFun p.1 - (g (σ n)).toFun p.2) ^ 2))
      ((volume.restrict V).prod (volume.restrict V)) := by
    intro n
    apply AEMeasurable.ennreal_ofReal
    exact ((hfn n).comp_fst.sub (hfn n).comp_snd).pow_const 2
  have hq : ∀ n, AEMeasurable (qn n) ((volume.restrict V).prod (volume.restrict V)) :=
    fun n => (hnum n).div hden_meas.aemeasurable
  have hnumlim : AEMeasurable
      (fun p : SpatialCoordinates d × SpatialCoordinates d =>
        ENNReal.ofReal ((chi.toFun p.1 * w.toFun p.1 ^ s -
          chi.toFun p.2 * w.toFun p.2 ^ s) ^ 2))
      ((volume.restrict V).prod (volume.restrict V)) := by
    apply AEMeasurable.ennreal_ofReal
    exact (hlimfn.comp_fst.sub hlimfn.comp_snd).pow_const 2
  have hqlim : AEMeasurable qlim ((volume.restrict V).prod (volume.restrict V)) :=
    hnumlim.div hden_meas.aemeasurable
  have hfst : ∀ᵐ p ∂(volume.restrict V).prod (volume.restrict V),
      Filter.Tendsto (fun k => (g (σ k)).toFun p.1) Filter.atTop
        (𝓝 (chi.toFun p.1 * w.toFun p.1 ^ s)) := by
    simpa only [Function.comp_apply] using
      (Measure.quasiMeasurePreserving_fst (μ := volume.restrict V) (ν := volume.restrict V)).ae
        hg_ae_tendsto
  have hsnd : ∀ᵐ p ∂(volume.restrict V).prod (volume.restrict V),
      Filter.Tendsto (fun k => (g (σ k)).toFun p.2) Filter.atTop
        (𝓝 (chi.toFun p.2 * w.toFun p.2 ^ s)) := by
    simpa only [Function.comp_apply] using
      (Measure.quasiMeasurePreserving_snd (μ := volume.restrict V) (ν := volume.restrict V)).ae
        hg_ae_tendsto
  have hq_tendsto : ∀ᵐ p ∂(volume.restrict V).prod (volume.restrict V),
      Filter.Tendsto (fun n => qn n p) Filter.atTop (𝓝 (qlim p)) := by
    filter_upwards [hfst, hsnd] with p hp hq'
    rcases p with ⟨x, z⟩
    by_cases hxz : x = z
    · subst z
      simp [hqn_def, hqlim_def]
    · have hxz_pos : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
      have hden0 : den (x, z) ≠ 0 := by
        rw [hden_def]
        exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hxz_pos _)).ne'
      have hdiff : Filter.Tendsto
          (fun n => (g (σ n)).toFun x - (g (σ n)).toFun z) Filter.atTop
          (𝓝 (chi.toFun x * w.toFun x ^ s - chi.toFun z * w.toFun z ^ s)) := hp.sub hq'
      have hsq := hdiff.pow 2
      have hnum_tendsto := ENNReal.tendsto_ofReal hsq
      simpa [hqn_def, hqlim_def] using ENNReal.Tendsto.div_const hnum_tendsto (Or.inr hden0)
  have hGag_fatou : ∫⁻ p, qlim p ∂(volume.restrict V).prod (volume.restrict V) ≤
      Filter.liminf (fun n => ∫⁻ p, qn n p ∂(volume.restrict V).prod (volume.restrict V))
        Filter.atTop := by
    calc ∫⁻ p, qlim p ∂(volume.restrict V).prod (volume.restrict V)
        = ∫⁻ p, Filter.liminf (fun n => qn n p) Filter.atTop
            ∂(volume.restrict V).prod (volume.restrict V) := by
          apply lintegral_congr_ae
          filter_upwards [hq_tendsto] with p hp
          exact hp.liminf_eq.symm
      _ ≤ Filter.liminf (fun n => ∫⁻ p, qn n p ∂(volume.restrict V).prod (volume.restrict V))
            Filter.atTop :=
          MeasureTheory.lintegral_liminf_le' hq
  have htonelli : ∀ n, ∫⁻ p, qn n p ∂(volume.restrict V).prod (volume.restrict V) =
      ∫⁻ x, ∫⁻ z, qn n (x, z) ∂volume.restrict V ∂volume.restrict V :=
    fun n => MeasureTheory.lintegral_prod (qn n) (hq n)
  have htonelli_lim : ∫⁻ p, qlim p ∂(volume.restrict V).prod (volume.restrict V) =
      ∫⁻ x, ∫⁻ z, qlim (x, z) ∂volume.restrict V ∂volume.restrict V :=
    MeasureTheory.lintegral_prod qlim hqlim
  set Gagn : ℕ → ℝ≥0∞ := fun n => ∫⁻ x in V, ∫⁻ z in V,
      ENNReal.ofReal (((g (σ n)).toFun x - (g (σ n)).toFun z) ^ 2) /
        ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2)) with hGagn_def
  set L2n : ℕ → ℝ≥0∞ := fun n => ∫⁻ x in V, ENNReal.ofReal (((g (σ n)).toFun x) ^ 2)
    with hL2n_def
  have hGag_step :
      (∫⁻ x in V, ∫⁻ z in V,
        ENNReal.ofReal ((chi.toFun x * w.toFun x ^ s - chi.toFun z * w.toFun z ^ s) ^ 2) /
          ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) ≤ Filter.liminf Gagn Filter.atTop := by
    have heq1 : Filter.liminf Gagn Filter.atTop =
        Filter.liminf (fun n => ∫⁻ p, qn n p ∂(volume.restrict V).prod (volume.restrict V))
          Filter.atTop := by
      congr 1
      funext n
      exact (htonelli n).symm
    rw [heq1, show (∫⁻ x in V, ∫⁻ z in V,
        ENNReal.ofReal ((chi.toFun x * w.toFun x ^ s - chi.toFun z * w.toFun z ^ s) ^ 2) /
          ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) =
        ∫⁻ p, qlim p ∂(volume.restrict V).prod (volume.restrict V) from htonelli_lim.symm]
    exact hGag_fatou
  have hL2_step : (∫⁻ x in V, ENNReal.ofReal ((chi.toFun x * w.toFun x ^ s) ^ 2)) ≤
      Filter.liminf L2n Filter.atTop := hL2_fatou
  have hsum_step : (∫⁻ x in V, ∫⁻ z in V,
        ENNReal.ofReal ((chi.toFun x * w.toFun x ^ s - chi.toFun z * w.toFun z ^ s) ^ 2) /
          ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
      ∫⁻ x in V, ENNReal.ofReal ((chi.toFun x * w.toFun x ^ s) ^ 2) ≤
      Filter.liminf (fun n => Gagn n + L2n n) Filter.atTop := by
    calc _ ≤ Filter.liminf Gagn Filter.atTop + Filter.liminf L2n Filter.atTop :=
          add_le_add hGag_step hL2_step
      _ ≤ Filter.liminf (fun n => Gagn n + L2n n) Filter.atTop :=
          aux_tight_subharmonic_cc_le_liminf_add_ennreal Gagn L2n
  have hcoer_n : ∀ n, Gagn n + L2n n ≤ ENNReal.ofReal Kc * ∫⁻ x in V, ENNReal.ofReal
      (A x * Homogenization.vecDot ((g (σ n)).grad x) ((g (σ n)).grad x)) :=
    fun n => hcoer (g (σ n))
  exact ⟨σ, hσ_mono, hsum_step.trans (Filter.liminf_le_liminf (Filter.Eventually.of_forall hcoer_n))⟩

theorem aux_tight_subharmonic_cutoff_coercive
    {d : ℕ} {V U : Set (SpatialCoordinates d)}
    (hV : Homogenization.IsOpenBoundedConvexDomain V) (hUV : U ⊆ V)
    {A : SpatialCoordinates d → ℝ} (hA : Continuous A) (hApos : ∀ x, 0 < A x)
    (w : Homogenization.H1Function V) (hw0 : ∀ x, 0 ≤ w.toFun x) {Mw : ℝ}
    (hwM : ∀ x, w.toFun x ≤ Mw)
    (hsub : SubdiffusiveProcess.CoarseGrainingVocab.Section11.IsWeakSubSolutionOn A V w)
    {s : ℝ} (hs : 1 ≤ s) {Kc : ℝ} (hKc : 0 ≤ Kc)
    (hcoer : ∀ v : Homogenization.H10Function V,
        (∫⁻ x in V, ∫⁻ z in V, ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
            ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
          ∫⁻ x in V, ENNReal.ofReal (v.toFun x ^ 2) ≤
        ENNReal.ofReal Kc *
          ∫⁻ x in V, ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x)))
    (chi : Homogenization.H10Function U) (hchisupp : tsupport chi.toFun ⊆ U) :
    (∫⁻ x in V, ∫⁻ z in V,
        ENNReal.ofReal ((chi.toFun x * w.toFun x ^ s - chi.toFun z * w.toFun z ^ s) ^ 2) /
          ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
      ∫⁻ x in V, ENNReal.ofReal ((chi.toFun x * w.toFun x ^ s) ^ 2) ≤
    ENNReal.ofReal (Kc * (8 * s ^ 2 + 2)) *
      ∫⁻ x in U, ENNReal.ofReal
        (w.toFun x ^ (2 * s) * (A x * Homogenization.vecDot (chi.grad x) (chi.grad x))) := by
  have hw0M : 0 ≤ Mw := le_trans (hw0 0) (hwM 0)
  have hwbound : ∀ᵐ x ∂volume.restrict V, |w.toFun x| ≤ Mw :=
    Filter.Eventually.of_forall (fun x => by rw [abs_of_nonneg (hw0 x)]; exact hwM x)
  obtain ⟨w', f', hw'eq, hf'eq, hpair⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.exists_moser_power_pair hV w hw0M hwbound hs
  have hw'toFun : ∀ x, w'.toFun x = w.toFun x ^ s := by
    intro x; rw [hw'eq]; simp [max_eq_left (hw0 x)]
  have hf'nonneg : ∀ x, 0 ≤ f'.toFun x := by
    intro x; rw [hf'eq]; exact Real.rpow_nonneg (le_max_right _ _) _
  obtain ⟨σ, hσ_mono, hFatouBound⟩ :=
    aux_tight_subharmonic_cc_fatou_bound hV hUV hApos w hw0 hKc hcoer chi hchisupp w' hw'toFun
  have hstepR := aux_tight_subharmonic_cc_stepR hV hUV hA hApos w hw0 hwM hsub hs chi w' f' hpair hf'nonneg hw'toFun
  have hRHS_tendsto := aux_tight_subharmonic_cc_rhs_tendsto hV hUV hA hApos w hw0 hwM hs chi
  have hAmeas : AEStronglyMeasurable A (volume.restrict V) := hA.aestronglyMeasurable
  have hApos' : ∀ x, 0 ≤ A x := fun x => (hApos x).le
  obtain ⟨MA, hMAbound⟩ := aux_tight_subharmonic_cc_bound_on_isBounded hV.isBoundedDomain.isBounded hA
  have habsA : ∀ᵐ x ∂volume.restrict V, |A x| ≤ MA := by
    filter_upwards [ae_restrict_mem hV.isOpen.measurableSet] with x hx
    rw [abs_of_nonneg (hApos' x)]; exact hMAbound x hx
  have hgn_int : ∀ n, IntegrableOn
      (fun x => A x * Homogenization.vecNormSq ((aux_tight_subharmonic_cc_G hV hUV w' chi n).toH1Function.grad x)) V :=
    fun n => aux_tight_subharmonic_cc_integrable_mul_bounded hAmeas habsA
      (Homogenization.integrableOn_vecNormSq_h1Grad (aux_tight_subharmonic_cc_G hV hUV w' chi n).toH1Function)
  have hgn_nonneg : ∀ n, 0 ≤ᵐ[volume.restrict V]
      (fun x => A x * Homogenization.vecNormSq
        ((aux_tight_subharmonic_cc_G hV hUV w' chi n).toH1Function.grad x)) :=
    fun n => Filter.Eventually.of_forall
      (fun x => mul_nonneg (hApos' x) (Homogenization.vecNormSq_nonneg _))
  have hBound_n : ∀ n, ENNReal.ofReal Kc * ∫⁻ x in V, ENNReal.ofReal
      (A x * Homogenization.vecDot ((aux_tight_subharmonic_cc_G hV hUV w' chi n).toH1Function.grad x)
        ((aux_tight_subharmonic_cc_G hV hUV w' chi n).toH1Function.grad x)) ≤
      ENNReal.ofReal (Kc * (8 * s ^ 2 + 2) * ∫ x in U, w.toFun x ^ (2 * s) *
        (A x * Homogenization.vecNormSq
          (Homogenization.euclideanGradient (chi.approx n) x))) := by
    intro n
    have heq1 : ∫⁻ x in V, ENNReal.ofReal
        (A x * Homogenization.vecDot ((aux_tight_subharmonic_cc_G hV hUV w' chi n).toH1Function.grad x)
          ((aux_tight_subharmonic_cc_G hV hUV w' chi n).toH1Function.grad x)) =
        ENNReal.ofReal (∫ x in V, A x *
          Homogenization.vecNormSq ((aux_tight_subharmonic_cc_G hV hUV w' chi n).toH1Function.grad x)) :=
      (ofReal_integral_eq_lintegral_ofReal (hgn_int n) (hgn_nonneg n)).symm
    rw [heq1, ← ENNReal.ofReal_mul hKc]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hstepR n) hKc
  have hRHS_int : IntegrableOn (fun x => w.toFun x ^ (2 * s) *
      (A x * Homogenization.vecNormSq (chi.grad x))) U := by
    have hK_meas' : AEStronglyMeasurable (fun x => w.toFun x ^ (2 * s) * A x)
        (volume.restrict U) := by
      have hwU_memLp : Homogenization.MemL2On U w.toFun :=
        w.memL2.mono_measure (Measure.restrict_mono_set volume hUV)
      have hwrpow_cont : Continuous (fun t : ℝ => t ^ (2 * s)) :=
        continuous_iff_continuousAt.mpr
          (fun x => Real.continuousAt_rpow_const x (2 * s) (Or.inr (by linarith)))
      exact (hwrpow_cont.comp_aestronglyMeasurable hwU_memLp.aestronglyMeasurable).mul hA.aestronglyMeasurable
    obtain ⟨MA', hMA'bound⟩ := aux_tight_subharmonic_cc_bound_on_isBounded hV.isBoundedDomain.isBounded hA
    have hK_bound' : ∀ᵐ x ∂volume.restrict U,
        |w.toFun x ^ (2 * s) * A x| ≤ |Mw ^ (2 * s) * MA'| :=
      aux_tight_subharmonic_cc_ae_bound_of_forall_mem hK_meas' (fun x hxU => by
        have hxV : x ∈ V := hUV hxU
        calc |w.toFun x ^ (2 * s) * A x|
            = w.toFun x ^ (2 * s) * A x := by
              rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hw0 x) _) (hApos x).le)]
          _ ≤ Mw ^ (2 * s) * MA' :=
              mul_le_mul (Real.rpow_le_rpow (hw0 x) (hwM x) (by linarith))
                (hMA'bound x hxV) (hApos x).le (Real.rpow_nonneg hw0M _)
          _ ≤ |Mw ^ (2 * s) * MA'| := le_abs_self _)
    have hpw : (fun x => w.toFun x ^ (2 * s) * (A x * Homogenization.vecNormSq (chi.grad x))) =
        (fun x => ∑ i : Fin d, (w.toFun x ^ (2 * s) * A x) * (chi.grad x i) ^ 2) := by
      funext x
      simp only [Homogenization.vecNormSq, Homogenization.vecDot, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hpw]
    exact integrable_finset_sum Finset.univ
      (fun i _ => aux_tight_subharmonic_cc_integrable_mul_bounded hK_meas' hK_bound' (chi.gradMemL2 i).integrable_sq)
  have hBoundσ_tendsto : Filter.Tendsto (fun n => Kc * (8 * s ^ 2 + 2) *
      ∫ x in U, w.toFun x ^ (2 * s) *
        (A x * Homogenization.vecNormSq (Homogenization.euclideanGradient (chi.approx (σ n)) x)))
      Filter.atTop
      (𝓝 (Kc * (8 * s ^ 2 + 2) * ∫ x in U, w.toFun x ^ (2 * s) *
        (A x * Homogenization.vecNormSq (chi.grad x)))) :=
    (hRHS_tendsto.comp (hσ_mono.tendsto_atTop)).const_mul (Kc * (8 * s ^ 2 + 2))
  have hBoundσ_ofReal_tendsto : Filter.Tendsto (fun n => ENNReal.ofReal (Kc * (8 * s ^ 2 + 2) *
      ∫ x in U, w.toFun x ^ (2 * s) *
        (A x * Homogenization.vecNormSq (Homogenization.euclideanGradient (chi.approx (σ n)) x))))
      Filter.atTop
      (𝓝 (ENNReal.ofReal (Kc * (8 * s ^ 2 + 2) * ∫ x in U, w.toFun x ^ (2 * s) *
        (A x * Homogenization.vecNormSq (chi.grad x))))) :=
    (ENNReal.continuous_ofReal.continuousAt.tendsto).comp hBoundσ_tendsto
  have hFinalBound : Filter.liminf (fun n => ENNReal.ofReal Kc * ∫⁻ x in V, ENNReal.ofReal
      (A x * Homogenization.vecDot ((aux_tight_subharmonic_cc_G hV hUV w' chi (σ n)).toH1Function.grad x)
        ((aux_tight_subharmonic_cc_G hV hUV w' chi (σ n)).toH1Function.grad x))) Filter.atTop ≤
      ENNReal.ofReal (Kc * (8 * s ^ 2 + 2) * ∫ x in U, w.toFun x ^ (2 * s) *
        (A x * Homogenization.vecNormSq (chi.grad x))) := by
    calc Filter.liminf (fun n => ENNReal.ofReal Kc * ∫⁻ x in V, ENNReal.ofReal
        (A x * Homogenization.vecDot ((aux_tight_subharmonic_cc_G hV hUV w' chi (σ n)).toH1Function.grad x)
          ((aux_tight_subharmonic_cc_G hV hUV w' chi (σ n)).toH1Function.grad x))) Filter.atTop
        ≤ Filter.liminf (fun n => ENNReal.ofReal (Kc * (8 * s ^ 2 + 2) *
            ∫ x in U, w.toFun x ^ (2 * s) * (A x * Homogenization.vecNormSq
              (Homogenization.euclideanGradient (chi.approx (σ n)) x)))) Filter.atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun n => hBound_n (σ n)))
      _ = ENNReal.ofReal (Kc * (8 * s ^ 2 + 2) * ∫ x in U, w.toFun x ^ (2 * s) *
            (A x * Homogenization.vecNormSq (chi.grad x))) := hBoundσ_ofReal_tendsto.liminf_eq
  calc (∫⁻ x in V, ∫⁻ z in V,
        ENNReal.ofReal ((chi.toFun x * w.toFun x ^ s - chi.toFun z * w.toFun z ^ s) ^ 2) /
          ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
      ∫⁻ x in V, ENNReal.ofReal ((chi.toFun x * w.toFun x ^ s) ^ 2)
      ≤ ENNReal.ofReal (Kc * (8 * s ^ 2 + 2) * ∫ x in U, w.toFun x ^ (2 * s) *
          (A x * Homogenization.vecNormSq (chi.grad x))) := hFatouBound.trans hFinalBound
    _ = ENNReal.ofReal (Kc * (8 * s ^ 2 + 2)) *
          ∫⁻ x in U, ENNReal.ofReal (w.toFun x ^ (2 * s) *
            (A x * Homogenization.vecNormSq (chi.grad x))) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hKc (by positivity))]
          rw [ofReal_integral_eq_lintegral_ofReal hRHS_int
            (Filter.Eventually.of_forall (fun x => mul_nonneg (Real.rpow_nonneg (hw0 x) _)
              (mul_nonneg (hApos x).le (Homogenization.vecNormSq_nonneg _))))]
    _ = ENNReal.ofReal (Kc * (8 * s ^ 2 + 2)) *
          ∫⁻ x in U, ENNReal.ofReal (w.toFun x ^ (2 * s) *
            (A x * Homogenization.vecDot (chi.grad x) (chi.grad x))) := by
          rfl

end


/-! ### assembly -/
section
open Metric
open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

lemma aux_tight_subharmonic_gag_congr_ae {d : ℕ} {f₁ f₂ : (Fin d → ℝ) → ℝ} {U : Set (Fin d → ℝ)}
    (h : f₁ =ᵐ[volume.restrict U] f₂) : aux_tight_subharmonic_fE f₁ U = aux_tight_subharmonic_fE f₂ U := by
  unfold aux_tight_subharmonic_fE aux_tight_subharmonic_gag
  congr 1
  · have hin : ∀ y, (∫⁻ z in U, ENNReal.ofReal ((f₁ y - f₁ z) ^ 2) /
        ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 3 / 2))) =
        ∫⁻ z in U, ENNReal.ofReal ((f₁ y - f₂ z) ^ 2) /
          ENNReal.ofReal (‖y - z‖ ^ ((d : ℝ) + 3 / 2)) := fun y ↦
      lintegral_congr_ae (h.mono fun z hz ↦ by simp only [hz])
    rw [lintegral_congr hin]
    exact lintegral_congr_ae (h.mono fun y hy ↦ by simp only [hy])
  · exact lintegral_congr_ae (h.mono fun y hy ↦ by simp only [hy])

lemma aux_tight_subharmonic_meas_mod {d : ℕ} {V : Set (Fin d → ℝ)} (w : (Fin d → ℝ) → ℝ)
    (hw : AEStronglyMeasurable w (volume.restrict V)) (hw0 : ∀ x, 0 ≤ w x) {Mw : ℝ}
    (hwM : ∀ x, w x ≤ Mw) :
    ∃ W : (Fin d → ℝ) → ℝ, Measurable W ∧ (∀ x, 0 ≤ W x) ∧ (∀ x, W x ≤ Mw) ∧
      W =ᵐ[volume.restrict V] w := by
  have hMw : 0 ≤ Mw := (hw0 0).trans (hwM 0)
  refine ⟨fun x ↦ max 0 (min Mw (hw.mk w x)),
    measurable_const.max (measurable_const.min hw.stronglyMeasurable_mk.measurable),
    fun x ↦ le_max_left _ _, fun x ↦ max_le hMw (min_le_left _ _), ?_⟩
  filter_upwards [hw.ae_eq_mk] with x hx
  rw [← hx, min_eq_right (hwM x), max_eq_right (hw0 x)]

lemma aux_tight_subharmonic_dens_aemeas {d : ℕ} {U : Set (Fin d → ℝ)} {A : (Fin d → ℝ) → ℝ} (hA : Continuous A)
    (chi : Homogenization.H1Function U) :
    AEMeasurable (fun z ↦ ENNReal.ofReal (A z * Homogenization.vecDot (chi.grad z) (chi.grad z)))
      (volume.restrict U) := by
  refine ENNReal.measurable_ofReal.comp_aemeasurable (hA.measurable.aemeasurable.mul ?_)
  unfold Homogenization.vecDot
  refine Finset.aemeasurable_fun_sum (M := ℝ) _ fun i _ ↦ ?_
  have := (chi.gradMemL2 i).aestronglyMeasurable.aemeasurable
  exact this.mul this

/-- The cutoff family of `tight_static_estimates`, with the Caccioppoli–coercivity inequality (CC)
for `W^s` (`W` a measurable modification of the subsolution `w`). -/
lemma aux_tight_subharmonic_cutfam {d : ℕ} {b A : SpatialCoordinates d → ℝ} {K B rho0 : ℝ}
    (hA : Continuous A) (hApos : ∀ x, 0 < A x) (hrho0 : 0 < rho0) (hK : 1 ≤ K)
    (hstatic : tight_static_estimates b A rho0 K B) {q1 q2 : ℚ} (hq1 : 0 < q1) (hq2 : q2 ≤ 1)
    (w : Homogenization.H1Function (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2)))
    (hw0 : ∀ x, 0 ≤ w.toFun x) {Mw : ℝ} (hwM : ∀ x, w.toFun x ≤ Mw)
    (hsub : SubdiffusiveProcess.CoarseGrainingVocab.Section11.IsWeakSubSolutionOn A
      (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2)) w)
    (W : (Fin d → ℝ) → ℝ) (hWm : Measurable W)
    (hWae : W =ᵐ[volume.restrict (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2))] w.toFun)
    (s : ℝ) (hs : 1 ≤ s) :
    aux_tight_subharmonic_CutFam (fun x ↦ W x ^ s) K B rho0 (K * (q2.den : ℝ) ^ B * (8 * s ^ 2 + 2)) q1 q2 := by
  intro q q' hq hqq' hq'
  have hq0 : 0 < q := lt_of_lt_of_le hq1 hq
  have hq2pos : 0 < q2 := hq1.trans_le (hq.trans (hqq'.le.trans hq'))
  obtain ⟨chi, _, hchi1, hchisupp, hchien⟩ := hstatic.2.2 q q' hq0 hqq' (hq'.trans hq2)
  have hq'q2 : (q' : ℝ) ≤ q2 := by exact_mod_cast hq'
  have hqq'r : (q : ℝ) ≤ q' := by exact_mod_cast hqq'.le
  have hq2r : (0 : ℝ) < q2 := by exact_mod_cast hq2pos
  have hUV : Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2) ⊆
      Metric.ball 0 (rho0 * (q2 : ℝ) / 2) := Metric.ball_subset_ball (by nlinarith)
  have hdm := aux_tight_subharmonic_dens_aemeas (U := Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2))
    hA chi.toH1Function
  refine ⟨(volume.restrict (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2))).withDensity
      (fun z ↦ ENNReal.ofReal (A z * Homogenization.vecDot (chi.grad z) (chi.grad z))),
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self), ?_, ?_, ?_⟩
  · rw [withDensity_apply _ Metric.isOpen_ball.measurableSet.compl,
      Measure.restrict_restrict Metric.isOpen_ball.measurableSet.compl, Set.compl_inter_self,
      Measure.restrict_empty, lintegral_zero_measure]
  · intro x ρ' hρ' hρ'1
    rw [withDensity_apply _ Metric.isOpen_ball.measurableSet,
      Measure.restrict_restrict Metric.isOpen_ball.measurableSet]
    exact hchien x ρ' hρ' hρ'1
  · -- (CC) through the stub
    have hcoer := (hstatic.2.1 q2 hq2pos hq2).2
    have hCC := aux_tight_subharmonic_cutoff_coercive
      (Homogenization.isOpenBoundedConvexDomain_ball 0 (div_pos (mul_pos hrho0 hq2r) two_pos)) hUV hA hApos w hw0 hwM hsub
      hs (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hcoer chi hchisupp
    have hVq : Metric.ball (0 : SpatialCoordinates d) (rho0 * (q : ℝ) / 2) ⊆
        Metric.ball 0 (rho0 * (q2 : ℝ) / 2) := Metric.ball_subset_ball (by nlinarith)
    have hL : aux_tight_subharmonic_fE (fun x ↦ W x ^ s) (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q : ℝ) / 2)) =
        aux_tight_subharmonic_fE (fun x ↦ chi.toFun x * w.toFun x ^ s) (Metric.ball 0 (rho0 * (q : ℝ) / 2)) := by
      refine aux_tight_subharmonic_gag_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hVq hWae,
        ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxm
      simp only [hx, hchi1 x hxm, one_mul]
    have hR : ∫⁻ x, ENNReal.ofReal ((W x ^ s) ^ 2) ∂((volume.restrict
          (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2))).withDensity
          (fun z ↦ ENNReal.ofReal (A z * Homogenization.vecDot (chi.grad z) (chi.grad z)))) =
        ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2), ENNReal.ofReal
          (w.toFun x ^ (2 * s) * (A x * Homogenization.vecDot (chi.grad x) (chi.grad x))) := by
      have hgm : AEMeasurable (fun x ↦ ENNReal.ofReal ((W x ^ s) ^ 2))
          (volume.restrict (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2))) :=
        (ENNReal.measurable_ofReal.comp ((hWm.pow_const s).pow_const 2)).aemeasurable
      rw [lintegral_withDensity_eq_lintegral_mul₀ hdm hgm]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hUV hWae] with x hx
      have hvd : 0 ≤ A x * Homogenization.vecDot (chi.grad x) (chi.grad x) :=
        mul_nonneg (hApos x).le (Homogenization.vecNormSq_nonneg _)
      simp only [Pi.mul_apply, Function.comp_apply, hx]
      rw [← ENNReal.ofReal_mul hvd, ← Real.rpow_natCast, ← Real.rpow_mul (hw0 x), mul_comm s,
        mul_comm]
      norm_num
    rw [hL, hR]
    exact (aux_tight_subharmonic_fE_mono _ hVq).trans hCC

/-- Lemma `tight:lem-subharmonic` (Local bound for subharmonic functions), in its deterministic
form: for fixed concentric cubes `V' ⋐ V` (relative sides `q1 < q2` of a reference cube of side
`rho0`), the estimates of `tight_static_estimates` with constant `K` imply
`ess sup_{V'} w ≤ C K^{Bm} (∫_V w² dμ)^{1/2}` for every bounded nonnegative weak subsolution
`∇·(A∇w) ≥ 0` in `V`.  `C, Bm` depend only on `d, B, rho0, q1, q2`, so the constant `C K^{Bm}`
has every prescribed moment whenever `K` does ("the constant may be enlarged by fixed powers"),
and it does not see any zeroth-order term of the equation of `w`. -/
theorem tight_subharmonic {d : ℕ} (hd : 2 ≤ d) :
    ∀ (B rho0 : ℝ), 0 < B → 0 < rho0 → ∀ (q1 q2 : ℚ), 0 < q1 → q1 < q2 → q2 ≤ 1 →
    ∃ C Bm : ℝ, 0 < C ∧ 0 < Bm ∧
      ∀ (b A : SpatialCoordinates d → ℝ) (K : ℝ),
        Continuous b → Continuous A → (∀ x, 0 < b x) → (∀ x, 0 < A x) → 1 ≤ K →
        tight_static_estimates b A rho0 K B →
        ∀ w : Homogenization.H1Function
            (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2)),
          (∀ x, 0 ≤ w.toFun x) → (∃ Mw : ℝ, ∀ x, w.toFun x ≤ Mw) →
          SubdiffusiveProcess.CoarseGrainingVocab.Section11.IsWeakSubSolutionOn A
            (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2)) w →
          ∀ᵐ x ∂(volume.restrict
              (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q1 : ℝ) / 2))),
            ENNReal.ofReal (w.toFun x) ≤
              ENNReal.ofReal (C * K ^ Bm) *
                (∫⁻ z in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2),
                  ENNReal.ofReal (w.toFun z ^ 2 * b z)) ^ (1 / 2 : ℝ) := by

  intro B rho0 hB hrho0 q1 q2 hq1 hq12 hq2
  obtain ⟨C, Bm, hC, hBm, hiter⟩ := aux_tight_subharmonic_moser_iter (d := d) (by omega) B rho0 hB hrho0 q1 q2
    hq1.le hq12 hq2
  refine ⟨C * ((q2.den : ℝ) ^ B) ^ Bm, 2 * Bm, by positivity, by positivity, ?_⟩
  intro b A K hb hA hbpos hApos hK hstatic w hw0 hwbdd hsub
  obtain ⟨Mw, hwM⟩ := hwbdd
  obtain ⟨W, hWm, hW0, hWM, hWae⟩ := aux_tight_subharmonic_meas_mod w.toFun w.memL2.aestronglyMeasurable hw0 hwM
  have hden : (1 : ℝ) ≤ (q2.den : ℝ) := by exact_mod_cast q2.pos
  have hKc : 1 ≤ K * (q2.den : ℝ) ^ B :=
    one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow hden hB.le)
  have hfam : ∀ s : ℝ, 1 ≤ s → aux_tight_subharmonic_CutFam (fun x ↦ W x ^ s) K B rho0
      (K * (q2.den : ℝ) ^ B * (8 * s ^ 2 + 2)) q1 q2 := fun s hs ↦
    aux_tight_subharmonic_cutfam hA hApos hrho0 hK hstatic hq1 hq2 w hw0 hwM hsub W hWm hWae s hs
  have hbm : Measurable fun z ↦ ENNReal.ofReal (b z) := ENNReal.measurable_ofReal.comp hb.measurable
  have hmass : aux_tight_subharmonic_MassBd (volume.withDensity fun z ↦ ENNReal.ofReal (b z)) K (rho0 / 2) :=
    fun x r hr hr1 hsub ↦ hstatic.1 x r hr hr1 hsub
  have hh := hiter (volume.withDensity fun z ↦ ENNReal.ofReal (b z)) W Mw K (K * (q2.den : ℝ) ^ B)
    hWm hW0 hWM hK hKc (withDensity_absolutelyContinuous _ _) hmass hfam
  clear hiter hfam
  have hac : volume.restrict (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q1 : ℝ) / 2)) ≪
      (volume.withDensity fun z ↦ ENNReal.ofReal (b z)).restrict
        (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q1 : ℝ) / 2)) :=
    (withDensity_absolutelyContinuous' hbm.aemeasurable
      (Eventually.of_forall fun x ↦ (ENNReal.ofReal_pos.2 (hbpos x)).ne')).restrict _
  have hq1r : (q1 : ℝ) ≤ q2 := by exact_mod_cast hq12.le
  have hsub12 : Metric.ball (0 : SpatialCoordinates d) (rho0 * (q1 : ℝ) / 2) ⊆
      Metric.ball 0 (rho0 * (q2 : ℝ) / 2) := Metric.ball_subset_ball (by nlinarith)
  have hint : ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2),
        ENNReal.ofReal (W x ^ 2) ∂(volume.withDensity fun z ↦ ENNReal.ofReal (b z)) =
      ∫⁻ z in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2),
        ENNReal.ofReal (w.toFun z ^ 2 * b z) := by
    have hgm : Measurable fun x ↦ ENNReal.ofReal (W x ^ 2) :=
      ENNReal.measurable_ofReal.comp (hWm.pow_const 2)
    rw [setLIntegral_withDensity_eq_setLIntegral_mul volume hbm hgm Metric.isOpen_ball.measurableSet]
    refine lintegral_congr_ae ?_
    filter_upwards [hWae] with x hx
    simp only [Pi.mul_apply, Function.comp_apply, hx]
    rw [← ENNReal.ofReal_mul (hbpos x).le, mul_comm]
  have hconst : C * (K * (K * (q2.den : ℝ) ^ B)) ^ Bm = C * ((q2.den : ℝ) ^ B) ^ Bm * K ^ (2 * Bm) := by
    have hK0 : 0 ≤ K := by linarith
    rw [← mul_assoc, Real.mul_rpow (by positivity) (by positivity), ← sq,
      ← Real.rpow_natCast K 2, ← Real.rpow_mul hK0]
    push_cast
    ring
  rw [hint, hconst] at hh
  filter_upwards [hac.ae_le hh, ae_restrict_of_ae_restrict_of_subset hsub12 hWae] with x hx hxW
  rw [← hxW]
  exact hx

end


end Paper
