import Mathlib
import SubdiffusiveProcess.CubeTrace.Scale
import SubdiffusiveProcess.CubeTrace.Radial

/-!
# Cube trace extension: the fractional (Gagliardo) double integral of a function with
`|F| ≲ M m^{β-1}` and `|∇F| ≲ M m^{β-2}`

Splitting `y` into the sup-ball `‖y - x‖ < m(x)/2` (mean value bound for `F`) and its complement
(`|F(x)-F(y)|² ≤ 2F(x)² + 2F(y)²`, symmetrized by Tonelli using `m(y) ≤ 3‖x-y‖`), the integral is
`≲ M² ∫_Q m^{2β-2-2σ}`, which is finite as soon as `σ < β - 1/2`.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff Topology
noncomputable section
namespace SubdiffusiveProcess.CubeTrace

variable {d : ℕ}

/-- The Euclidean Gagliardo kernel of a scalar function, as in `cubeFractionalL2Seminorm`. -/
def ctFracKer (σ : ℝ) (F : (Fin d → ℝ) → ℝ) (x y : (Fin d → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((F x - F y) ^ 2) /
    (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ ((d : ℝ) + 2 * σ)

/-- The sup-norm kernel dominates the Euclidean one (`‖x - y‖ ≤ |x - y|₂`). -/
theorem ctFracKer_le_sup (σ : ℝ) (hσ : 0 ≤ σ) (F : (Fin d → ℝ) → ℝ)
    (x y : (Fin d → ℝ)) :
    ctFracKer σ F x y ≤
      ENNReal.ofReal ((F x - F y) ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) := by
  unfold ctFracKer
  apply ENNReal.div_le_div_left
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (norm_le_euclid x y)) (by positivity)

/-- **Near part.** If `|F(x) - F(y)| ≤ M m(x)^{β-2} ‖x - y‖` for `‖y - x‖ < m(x)/2`, then the near
integral is `≲ M² m(x)^{2β-2-2σ}`. -/
theorem ct_frac_near [NeZero d] {β σ : ℝ} (hβ : β ∈ Set.Ioo (1 / 2 : ℝ) 1) (hσ : 0 < σ)
    (hσβ : σ < β - 1 / 2) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ (z : (Fin d → ℝ)) (M : ℝ) (F : (Fin d → ℝ) → ℝ),
      0 ≤ M → (∀ x ∈ ctQ z, ∀ y, ‖y - x‖ < ctM z x / 2 →
        |F x - F y| ≤ M * ctM z x ^ (β - 2) * ‖x - y‖) →
      ∀ x ∈ ctQ z,
        ∫⁻ y in Metric.ball x (ctM z x / 2),
          ENNReal.ofReal ((F x - F y) ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) ≤
          ENNReal.ofReal (Cn * M ^ 2 * ctM z x ^ (2 * β - 2 - 2 * σ)) := by
  have hσ1 : σ < 1 / 2 := by linarith [hβ.2]
  have hγ : 0 < 2 - 2 * σ := by linarith
  refine ⟨ctCd d * (1 / 2) ^ (2 - 2 * σ) / (2 - 2 * σ), by
    have := ctCd_nonneg d
    positivity, ?_⟩
  intro z M F hM hlip x hx
  have hm : 0 < ctM z x := ctM_pos hx
  have hr : 0 < ctM z x / 2 := by positivity
  set A : ℝ := (M * ctM z x ^ (β - 2)) ^ 2 with hAdef
  have hA0 : 0 ≤ A := sq_nonneg _
  have hpt : ∀ y ∈ Metric.ball x (ctM z x / 2),
      ENNReal.ofReal ((F x - F y) ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) ≤
        ENNReal.ofReal A * ENNReal.ofReal (‖y - x‖ ^ ((2 - 2 * σ) - (d : ℝ))) := by
    intro y hy
    have hyx : ‖y - x‖ < ctM z x / 2 := by simpa [mem_ball_iff_norm] using hy
    have hlipy := hlip x hx y hyx
    by_cases hxy : y = x
    · subst hxy; simp
    · have ht : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
      rw [ENNReal.ofReal_rpow_of_pos ht,
        ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos ht _), ← ENNReal.ofReal_mul hA0]
      apply ENNReal.ofReal_le_ofReal
      rw [norm_sub_rev y x]
      have hsq : (F x - F y) ^ 2 ≤ (M * ctM z x ^ (β - 2) * ‖x - y‖) ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hlipy 2
        rwa [sq_abs] at this
      have hpos : 0 < ‖x - y‖ ^ ((d : ℝ) + 2 * σ) := Real.rpow_pos_of_pos ht _
      calc (F x - F y) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + 2 * σ)
          ≤ (M * ctM z x ^ (β - 2) * ‖x - y‖) ^ 2 / ‖x - y‖ ^ ((d : ℝ) + 2 * σ) :=
            div_le_div_of_nonneg_right hsq hpos.le
        _ = A * ‖x - y‖ ^ ((2 - 2 * σ) - (d : ℝ)) := by
            have e1 : ‖x - y‖ ^ ((2 - 2 * σ) - (d : ℝ)) =
                ‖x - y‖ ^ (2 : ℝ) / ‖x - y‖ ^ ((d : ℝ) + 2 * σ) := by
              rw [← Real.rpow_sub ht]; congr 1; ring
            rw [e1, Real.rpow_two, hAdef]
            ring
  calc ∫⁻ y in Metric.ball x (ctM z x / 2),
        ENNReal.ofReal ((F x - F y) ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ)
      ≤ ∫⁻ y in Metric.ball x (ctM z x / 2),
          ENNReal.ofReal A * ENNReal.ofReal (‖y - x‖ ^ ((2 - 2 * σ) - (d : ℝ))) :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = ENNReal.ofReal A * ∫⁻ y in Metric.ball x (ctM z x / 2),
          ENNReal.ofReal (‖y - x‖ ^ ((2 - 2 * σ) - (d : ℝ))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal A * ∫⁻ z in Metric.ball (0 : Fin d → ℝ) (ctM z x / 2),
          ENNReal.ofReal (‖z‖ ^ ((2 - 2 * σ) - (d : ℝ))) := by
        rw [lintegral_ball_center x (ctM z x / 2)
          (fun t => ENNReal.ofReal (t ^ ((2 - 2 * σ) - (d : ℝ))))]
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (ctCd d * (ctM z x / 2) ^ (2 - 2 * σ) / (2 - 2 * σ)) :=
        mul_le_mul_right (lintegral_ball_norm_rpow_le hγ hr) _
    _ = ENNReal.ofReal (A * (ctCd d * (ctM z x / 2) ^ (2 - 2 * σ) / (2 - 2 * σ))) :=
        (ENNReal.ofReal_mul hA0).symm
    _ = ENNReal.ofReal (ctCd d * (1 / 2) ^ (2 - 2 * σ) / (2 - 2 * σ) * M ^ 2 *
          ctM z x ^ (2 * β - 2 - 2 * σ)) := by
        congr 1
        have h1 : (ctM z x ^ (β - 2)) ^ 2 = ctM z x ^ (2 * β - 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le]
          congr 1; push_cast; ring
        have h2 : (ctM z x / 2) ^ (2 - 2 * σ) = (1 / 2) ^ (2 - 2 * σ) * ctM z x ^ (2 - 2 * σ) := by
          rw [div_eq_mul_inv, mul_comm, Real.mul_rpow (by norm_num) hm.le, one_div]
        have h3 : ctM z x ^ (2 * β - 2 - 2 * σ) =
            ctM z x ^ (2 * β - 4) * ctM z x ^ (2 - 2 * σ) := by
          rw [← Real.rpow_add hm]; congr 1; ring
        rw [hAdef, mul_pow, h1, h2, h3]
        ring

/-- The exterior kernel integral about `x`: `∫_{‖y-x‖ ≥ r} ‖x-y‖^{-d-2σ} ≤ C r^{-2σ}/(2σ)`. -/
theorem ct_frac_exterior [NeZero d] {σ : ℝ} (hσ : 0 < σ) {r : ℝ} (hr : 0 < r)
    (x : (Fin d → ℝ)) :
    ∫⁻ y in (Metric.ball x r)ᶜ, (ENNReal.ofReal ‖x - y‖) ^ (-((d : ℝ) + 2 * σ)) ≤
      ENNReal.ofReal (ctCd d * r ^ (-(2 * σ)) / (2 * σ)) := by
  have hr' := lintegral_compl_ball_norm_rpow_le (d := d) (a := 2 * σ) (ρ := r) (by linarith) hr
  calc ∫⁻ y in (Metric.ball x r)ᶜ, (ENNReal.ofReal ‖x - y‖) ^ (-((d : ℝ) + 2 * σ))
      = ∫⁻ y in (Metric.ball x r)ᶜ, ENNReal.ofReal (‖y - x‖ ^ (-((d : ℝ) + 2 * σ))) := by
        apply setLIntegral_congr_fun measurableSet_ball.compl
        intro y hy
        have hyx : r ≤ ‖y - x‖ := by
          simpa [mem_ball_iff_norm, not_lt, dist_eq_norm] using hy
        show ENNReal.ofReal ‖x - y‖ ^ (-((d : ℝ) + 2 * σ)) =
          ENNReal.ofReal (‖y - x‖ ^ (-((d : ℝ) + 2 * σ)))
        rw [norm_sub_rev x y, ENNReal.ofReal_rpow_of_pos (lt_of_lt_of_le hr hyx)]
    _ = ∫⁻ z in (Metric.ball (0 : Fin d → ℝ) r)ᶜ, ENNReal.ofReal (‖z‖ ^ (-((d : ℝ) + 2 * σ))) :=
        lintegral_compl_ball_center x r (fun t => ENNReal.ofReal (t ^ (-((d : ℝ) + 2 * σ))))
    _ ≤ _ := hr'

/-- **Far part, `F(x)²` term.** -/
theorem ct_frac_far_x [NeZero d] {β σ : ℝ} (hσ : 0 < σ) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧ ∀ (z : (Fin d → ℝ)) (F : (Fin d → ℝ) → ℝ),
      ∀ x ∈ ctQ z,
        ∫⁻ y in (Metric.ball x (ctM z x / 2))ᶜ,
          ENNReal.ofReal (F x ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) ≤
          ENNReal.ofReal (Cx * F x ^ 2 * ctM z x ^ (-(2 * σ))) := by
  refine ⟨ctCd d * 2 ^ (2 * σ) / (2 * σ), by
    have := ctCd_nonneg d
    positivity, ?_⟩
  intro z F x hx
  have hm := ctM_pos hx
  have hr : 0 < ctM z x / 2 := by positivity
  have hext := ct_frac_exterior (d := d) hσ hr x
  have hstep : ∫⁻ y in (Metric.ball x (ctM z x / 2))ᶜ,
        ENNReal.ofReal (F x ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) =
      ENNReal.ofReal (F x ^ 2) * ∫⁻ y in (Metric.ball x (ctM z x / 2))ᶜ,
        (ENNReal.ofReal ‖x - y‖) ^ (-((d : ℝ) + 2 * σ)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro y
    rw [div_eq_mul_inv, ← ENNReal.rpow_neg]
  rw [hstep]
  have hreal : F x ^ 2 * (ctCd d * (ctM z x / 2) ^ (-(2 * σ)) / (2 * σ)) =
      ctCd d * 2 ^ (2 * σ) / (2 * σ) * F x ^ 2 * ctM z x ^ (-(2 * σ)) := by
    have h1 : (ctM z x / 2) ^ (-(2 * σ)) = 2 ^ (2 * σ) * ctM z x ^ (-(2 * σ)) := by
      rw [div_eq_mul_inv, Real.mul_rpow hm.le (by norm_num), Real.inv_rpow (by norm_num),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
      ring
    rw [h1]; ring
  calc ENNReal.ofReal (F x ^ 2) * ∫⁻ y in (Metric.ball x (ctM z x / 2))ᶜ,
        (ENNReal.ofReal ‖x - y‖) ^ (-((d : ℝ) + 2 * σ))
      ≤ ENNReal.ofReal (F x ^ 2) * ENNReal.ofReal (ctCd d * (ctM z x / 2) ^ (-(2 * σ)) / (2 * σ)) :=
        mul_le_mul_right hext _
    _ = ENNReal.ofReal (F x ^ 2 * (ctCd d * (ctM z x / 2) ^ (-(2 * σ)) / (2 * σ))) :=
        (ENNReal.ofReal_mul (sq_nonneg _)).symm
    _ = ENNReal.ofReal (ctCd d * 2 ^ (2 * σ) / (2 * σ) * F x ^ 2 * ctM z x ^ (-(2 * σ))) := by
        rw [hreal]

/-- **Far part, `F(y)²` term** (Tonelli swap, `m(y) ≤ 3 ‖x - y‖` on the far region). -/
theorem ct_frac_far_y [NeZero d] {σ : ℝ} (hσ : 0 < σ) :
    ∃ Cy : ℝ, 0 ≤ Cy ∧ ∀ (z : (Fin d → ℝ)) (F : (Fin d → ℝ) → ℝ),
      Measurable F →
      ∫⁻ x in ctQ z, ∫⁻ y in ctQ z ∩ (Metric.ball x (ctM z x / 2))ᶜ,
          ENNReal.ofReal (F y ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) ≤
        ∫⁻ y in ctQ z, ENNReal.ofReal (Cy * F y ^ 2 * ctM z y ^ (-(2 * σ))) := by
  refine ⟨ctCd d * 3 ^ (2 * σ) / (2 * σ), by
    have := ctCd_nonneg d
    positivity, ?_⟩
  intro z F hF
  set g : (Fin d → ℝ) → (Fin d → ℝ) → ℝ≥0∞ := fun x y =>
    ENNReal.ofReal (F y ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) with hgdef
  set S : Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
    {p | p.2 ∈ (Metric.ball p.1 (ctM z p.1 / 2))ᶜ} with hSdef
  have hSm : MeasurableSet S := by
    have : S = {p | ctM z p.1 / 2 ≤ dist p.2 p.1} := by
      ext p; simp [hSdef, not_lt]
    rw [this]
    exact measurableSet_le (((continuous_ctM z).measurable.comp measurable_fst).div_const 2)
      (continuous_snd.dist continuous_fst).measurable
  set H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ≥0∞ := fun x y => S.indicator (fun p => g p.1 p.2) (x, y)
    with hHdef
  have hgm : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => g p.1 p.2) := by
    simp only [hgdef, div_eq_mul_inv]
    have h1 : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => ENNReal.ofReal (F p.2 ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((hF.comp measurable_snd).pow_const 2)
    have h2 : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => ENNReal.ofReal ‖p.1 - p.2‖) :=
      ENNReal.measurable_ofReal.comp (measurable_fst.sub measurable_snd).norm
    exact h1.mul (h2.pow_const _).inv
  have hHm : Measurable (Function.uncurry H) := hgm.indicator hSm
  -- inner integral as an indicator integral
  have hinner : ∀ x, ∫⁻ y in ctQ z ∩ (Metric.ball x (ctM z x / 2))ᶜ, g x y =
      ∫⁻ y in ctQ z, H x y := by
    intro x
    have hT : MeasurableSet (Metric.ball x (ctM z x / 2))ᶜ := measurableSet_ball.compl
    have : ∀ y, H x y = ((Metric.ball x (ctM z x / 2))ᶜ).indicator (g x) y := by
      intro y
      by_cases hy : y ∈ (Metric.ball x (ctM z x / 2))ᶜ
      · rw [Set.indicator_of_mem hy]
        exact Set.indicator_of_mem (show (x, y) ∈ S from hy) _
      · rw [Set.indicator_of_notMem hy]
        exact Set.indicator_of_notMem (show (x, y) ∉ S from hy) _
    simp_rw [this]
    rw [lintegral_indicator hT, Measure.restrict_restrict hT, Set.inter_comm]
  show ∫⁻ x in ctQ z, ∫⁻ y in ctQ z ∩ (Metric.ball x (ctM z x / 2))ᶜ, g x y ≤ _
  simp_rw [hinner]
  rw [lintegral_lintegral_swap hHm.aemeasurable]
  apply setLIntegral_mono' isOpen_ball.measurableSet
  intro y hy
  have hm := ctM_pos hy
  have hr : 0 < ctM z y / 3 := by positivity
  set k : (Fin d → ℝ) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (F y ^ 2) * (ENNReal.ofReal ‖y - x‖) ^ (-((d : ℝ) + 2 * σ)) with hkdef
  have hpt : ∀ x, (ctQ z).indicator (fun x => H x y) x ≤
      ((Metric.ball y (ctM z y / 3))ᶜ).indicator k x := by
    intro x
    by_cases hx : x ∈ ctQ z
    · rw [Set.indicator_of_mem hx]
      by_cases hxS : (x, y) ∈ S
      · have hfar : ctM z x / 2 ≤ ‖y - x‖ := by
          have : y ∈ (Metric.ball x (ctM z x / 2))ᶜ := hxS
          simpa [mem_ball_iff_norm, not_lt] using this
        have hlip := abs_ctM_sub_le hx hy
        have h3 : ctM z y / 3 ≤ ‖y - x‖ := by
          have h4 : ctM z y ≤ ctM z x + ‖x - y‖ := by
            have := (abs_le.1 hlip).1
            linarith
          rw [norm_sub_rev x y] at h4
          linarith
        have hxB : x ∈ (Metric.ball y (ctM z y / 3))ᶜ := by
          rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, dist_eq_norm, norm_sub_rev]
          exact h3
        rw [Set.indicator_of_mem hxB]
        simp only [hHdef, Set.indicator_of_mem hxS, hgdef, hkdef]
        rw [div_eq_mul_inv, ← ENNReal.rpow_neg, norm_sub_rev x y]
      · simp only [hHdef, Set.indicator_of_notMem hxS]
        exact zero_le _
    · rw [Set.indicator_of_notMem hx]; exact zero_le _
  have hext := ct_frac_exterior (d := d) hσ hr y
  calc ∫⁻ x in ctQ z, H x y
      = ∫⁻ x, (ctQ z).indicator (fun x => H x y) x := (lintegral_indicator
          isOpen_ball.measurableSet _).symm
    _ ≤ ∫⁻ x, ((Metric.ball y (ctM z y / 3))ᶜ).indicator k x := lintegral_mono hpt
    _ = ∫⁻ x in (Metric.ball y (ctM z y / 3))ᶜ, k x :=
        lintegral_indicator measurableSet_ball.compl _
    _ = ENNReal.ofReal (F y ^ 2) * ∫⁻ x in (Metric.ball y (ctM z y / 3))ᶜ,
          (ENNReal.ofReal ‖y - x‖) ^ (-((d : ℝ) + 2 * σ)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (F y ^ 2) *
          ENNReal.ofReal (ctCd d * (ctM z y / 3) ^ (-(2 * σ)) / (2 * σ)) :=
        mul_le_mul_right hext _
    _ = ENNReal.ofReal (F y ^ 2 * (ctCd d * (ctM z y / 3) ^ (-(2 * σ)) / (2 * σ))) :=
        (ENNReal.ofReal_mul (sq_nonneg _)).symm
    _ = ENNReal.ofReal (ctCd d * 3 ^ (2 * σ) / (2 * σ) * F y ^ 2 * ctM z y ^ (-(2 * σ))) := by
        congr 1
        have h1 : (ctM z y / 3) ^ (-(2 * σ)) = 3 ^ (2 * σ) * ctM z y ^ (-(2 * σ)) := by
          rw [div_eq_mul_inv, Real.mul_rpow hm.le (by norm_num), Real.inv_rpow (by norm_num),
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), inv_inv]
          ring
        rw [h1]; ring

/-- `∫_Q c m^{-a} ≤ c d 4^a/(1-a)` as a lower Lebesgue integral. -/
theorem ct_lintegral_ctM_rpow_le [NeZero d] (z : (Fin d → ℝ)) {a c : ℝ} (hc : 0 ≤ c)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    ∫⁻ x in ctQ z, ENNReal.ofReal (c * ctM z x ^ (-a)) ≤
      ENNReal.ofReal (c * ((d : ℝ) * (4 ^ a / (1 - a)))) := by
  obtain ⟨hint, hle⟩ := integral_ctM_rpow_le z ha ha1
  have h1 : ∫⁻ x in ctQ z, ENNReal.ofReal (c * ctM z x ^ (-a)) =
      ENNReal.ofReal c * ∫⁻ x in ctQ z, ENNReal.ofReal (ctM z x ^ (-a)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_mul hc]
  have h2 : ∫⁻ x in ctQ z, ENNReal.ofReal (ctM z x ^ (-a)) =
      ENNReal.ofReal (∫ x in ctQ z, ctM z x ^ (-a)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint]
    exact ae_restrict_of_forall_mem isOpen_ball.measurableSet
      (fun x hx => Real.rpow_nonneg (ctM_pos hx).le _)
  rw [h1, h2, ← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hle hc)

/-- Splitting the inner `y`-integral over `Q` into the near ball and the far region. -/
theorem ct_frac_inner_split [NeZero d] {σ : ℝ} (hσ : 0 < σ) (z x : (Fin d → ℝ))
    (F : (Fin d → ℝ) → ℝ) (hF : Measurable F) :
    ∫⁻ y in ctQ z, ctFracKer σ F x y ≤
      (∫⁻ y in Metric.ball x (ctM z x / 2),
          ENNReal.ofReal ((F x - F y) ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ)) +
      (2 * (∫⁻ y in (Metric.ball x (ctM z x / 2))ᶜ,
          ENNReal.ofReal (F x ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ)) +
        2 * (∫⁻ y in ctQ z ∩ (Metric.ball x (ctM z x / 2))ᶜ,
          ENNReal.ofReal (F y ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ))) := by
  set B : Set (Fin d → ℝ) := Metric.ball x (ctM z x / 2) with hB
  have hBm : MeasurableSet B := measurableSet_ball
  have hcov : ctQ z ⊆ B ∪ (ctQ z ∩ Bᶜ) := by
    intro y hy
    by_cases hyB : y ∈ B
    · exact Or.inl hyB
    · exact Or.inr ⟨hy, hyB⟩
  have hD : Measurable (fun y : Fin d → ℝ =>
      ((ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ))⁻¹) :=
    ((ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_id).norm).pow_const _).inv
  have hFy : Measurable (fun y : Fin d → ℝ => ENNReal.ofReal (F y ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hF.pow_const 2)
  have hpt : ∀ y, ctFracKer σ F x y ≤
      ENNReal.ofReal ((F x - F y) ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) :=
    fun y => ctFracKer_le_sup σ hσ.le F x y
  have hfar : ∀ y, ENNReal.ofReal ((F x - F y) ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) ≤
      2 * (ENNReal.ofReal (F x ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ)) +
      2 * (ENNReal.ofReal (F y ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ)) := by
    intro y
    have h1 : ENNReal.ofReal ((F x - F y) ^ 2) ≤
        2 * ENNReal.ofReal (F x ^ 2) + 2 * ENNReal.ofReal (F y ^ 2) := by
      have : (F x - F y) ^ 2 ≤ 2 * F x ^ 2 + 2 * F y ^ 2 := by
        nlinarith [sq_nonneg (F x + F y)]
      calc ENNReal.ofReal ((F x - F y) ^ 2) ≤ ENNReal.ofReal (2 * F x ^ 2 + 2 * F y ^ 2) :=
            ENNReal.ofReal_le_ofReal this
        _ = 2 * ENNReal.ofReal (F x ^ 2) + 2 * ENNReal.ofReal (F y ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
            simp
    calc ENNReal.ofReal ((F x - F y) ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ)
        ≤ (2 * ENNReal.ofReal (F x ^ 2) + 2 * ENNReal.ofReal (F y ^ 2)) /
            (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) := ENNReal.div_le_div_right h1 _
      _ = _ := by
          rw [ENNReal.add_div, mul_div_assoc, mul_div_assoc]
  calc ∫⁻ y in ctQ z, ctFracKer σ F x y
      ≤ ∫⁻ y in ctQ z, ENNReal.ofReal ((F x - F y) ^ 2) /
          (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) := lintegral_mono hpt
    _ ≤ ∫⁻ y in B ∪ (ctQ z ∩ Bᶜ), ENNReal.ofReal ((F x - F y) ^ 2) /
          (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) := lintegral_mono_set hcov
    _ ≤ (∫⁻ y in B, ENNReal.ofReal ((F x - F y) ^ 2) /
          (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ)) +
        ∫⁻ y in ctQ z ∩ Bᶜ, ENNReal.ofReal ((F x - F y) ^ 2) /
          (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) := lintegral_union_le _ _ _
    _ ≤ _ := by
        gcongr
        calc ∫⁻ y in ctQ z ∩ Bᶜ, ENNReal.ofReal ((F x - F y) ^ 2) /
              (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ)
            ≤ ∫⁻ y in ctQ z ∩ Bᶜ,
              (2 * (ENNReal.ofReal (F x ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ)) +
              2 * (ENNReal.ofReal (F y ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ))) :=
              lintegral_mono hfar
          _ = 2 * (∫⁻ y in ctQ z ∩ Bᶜ,
                ENNReal.ofReal (F x ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ)) +
              2 * (∫⁻ y in ctQ z ∩ Bᶜ,
                ENNReal.ofReal (F y ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ)) := by
              have hm1 : Measurable (fun y : Fin d → ℝ => 2 * (ENNReal.ofReal (F x ^ 2) /
                  (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ))) := by
                simp_rw [div_eq_mul_inv]
                exact (measurable_const.mul hD).const_mul 2
              rw [lintegral_add_left hm1, lintegral_const_mul' 2 _ (by norm_num),
                lintegral_const_mul' 2 _ (by norm_num)]
          _ ≤ _ := by
              gcongr
              exact Set.inter_subset_right

/-- **The fractional double integral** for a measurable `F`. -/
theorem ct_fractional_double_integral_meas [NeZero d] {β σ : ℝ} (hβ : β ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hσ : 0 < σ) (hσβ : σ < β - 1 / 2) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (z : (Fin d → ℝ)) (M : ℝ) (F : (Fin d → ℝ) → ℝ),
      0 ≤ M → Measurable F →
      (∀ x ∈ ctQ z, |F x| ≤ M * ctM z x ^ (β - 1)) →
      (∀ x ∈ ctQ z, ∀ y, ‖y - x‖ < ctM z x / 2 →
        |F x - F y| ≤ M * ctM z x ^ (β - 2) * ‖x - y‖) →
      ∫⁻ x in ctQ z, ∫⁻ y in ctQ z, ctFracKer σ F x y ≤ ENNReal.ofReal (Cf * M ^ 2) := by
  obtain ⟨Cn, hCn0, hn⟩ := ct_frac_near (d := d) hβ hσ hσβ
  obtain ⟨Cx, hCx0, hx⟩ := ct_frac_far_x (d := d) (β := β) hσ
  obtain ⟨Cy, hCy0, hy⟩ := ct_frac_far_y (d := d) hσ
  have hβ1 := hβ.1
  have hβ2 := hβ.2
  set a : ℝ := 2 * σ + 2 - 2 * β with hadef
  have ha0 : 0 ≤ a := by linarith
  have ha1 : a < 1 := by linarith
  have hea : 2 * β - 2 - 2 * σ = -a := by rw [hadef]; ring
  have h1a : 0 < 1 - a := by linarith
  set K : ℝ := (d : ℝ) * (4 ^ a / (1 - a)) with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine ⟨((Cn + 2 * Cx) + 2 * Cy) * K, by positivity, ?_⟩
  intro z M F hM hF hbd hlip
  have hpow : ∀ x ∈ ctQ z, F x ^ 2 * ctM z x ^ (-(2 * σ)) ≤ M ^ 2 * ctM z x ^ (-a) := by
    intro x hx
    have hm := ctM_pos hx
    have h1 : F x ^ 2 ≤ (M * ctM z x ^ (β - 1)) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) (hbd x hx) 2
      rwa [sq_abs] at this
    have h2 : (M * ctM z x ^ (β - 1)) ^ 2 * ctM z x ^ (-(2 * σ)) = M ^ 2 * ctM z x ^ (-a) := by
      rw [mul_pow, mul_assoc]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le, ← Real.rpow_add hm]
      congr 1
      push_cast
      rw [hadef]
      ring
    calc F x ^ 2 * ctM z x ^ (-(2 * σ))
        ≤ (M * ctM z x ^ (β - 1)) ^ 2 * ctM z x ^ (-(2 * σ)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hm.le _)
      _ = M ^ 2 * ctM z x ^ (-a) := h2
  -- the near part and the `F(x)²` far part, pointwise
  have hP : ∀ x ∈ ctQ z,
      (∫⁻ y in Metric.ball x (ctM z x / 2),
          ENNReal.ofReal ((F x - F y) ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ)) +
      2 * (∫⁻ y in (Metric.ball x (ctM z x / 2))ᶜ,
          ENNReal.ofReal (F x ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ)) ≤
      ENNReal.ofReal ((Cn + 2 * Cx) * M ^ 2 * ctM z x ^ (-a)) := by
    intro x hxQ
    have hm := ctM_pos hxQ
    have hnr := hn z M F hM hlip x hxQ
    have hxr := hx z F x hxQ
    have hrpow : 0 ≤ ctM z x ^ (-a) := Real.rpow_nonneg hm.le _
    have hx2 : Cx * F x ^ 2 * ctM z x ^ (-(2 * σ)) ≤ Cx * (M ^ 2 * ctM z x ^ (-a)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hpow x hxQ) hCx0
    calc _ ≤ ENNReal.ofReal (Cn * M ^ 2 * ctM z x ^ (2 * β - 2 - 2 * σ)) +
          2 * ENNReal.ofReal (Cx * (M ^ 2 * ctM z x ^ (-a))) := by
            gcongr
            exact hxr.trans (ENNReal.ofReal_le_ofReal hx2)
      _ = ENNReal.ofReal ((Cn + 2 * Cx) * M ^ 2 * ctM z x ^ (-a)) := by
          rw [hea]
          have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
          rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          congr 1
          ring
  -- the `F(y)²` far part after the swap
  have hY : ∫⁻ x in ctQ z, ∫⁻ y in ctQ z ∩ (Metric.ball x (ctM z x / 2))ᶜ,
        ENNReal.ofReal (F y ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) ≤
      ENNReal.ofReal ((Cy * M ^ 2) * ((d : ℝ) * (4 ^ a / (1 - a)))) := by
    refine (hy z F hF).trans (le_trans ?_ (ct_lintegral_ctM_rpow_le z (by positivity) ha0 ha1))
    apply setLIntegral_mono' isOpen_ball.measurableSet
    intro y hyQ
    apply ENNReal.ofReal_le_ofReal
    have := mul_le_mul_of_nonneg_left (hpow y hyQ) hCy0
    calc Cy * F y ^ 2 * ctM z y ^ (-(2 * σ)) = Cy * (F y ^ 2 * ctM z y ^ (-(2 * σ))) := by ring
      _ ≤ Cy * (M ^ 2 * ctM z y ^ (-a)) := this
      _ = Cy * M ^ 2 * ctM z y ^ (-a) := by ring
  have hmeasC : Measurable (fun x : Fin d → ℝ =>
      ENNReal.ofReal ((Cn + 2 * Cx) * M ^ 2 * ctM z x ^ (-a))) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul ((continuous_ctM z).measurable.pow_const (-a)))
  calc ∫⁻ x in ctQ z, ∫⁻ y in ctQ z, ctFracKer σ F x y
      ≤ ∫⁻ x in ctQ z, (ENNReal.ofReal ((Cn + 2 * Cx) * M ^ 2 * ctM z x ^ (-a)) +
          2 * ∫⁻ y in ctQ z ∩ (Metric.ball x (ctM z x / 2))ᶜ,
            ENNReal.ofReal (F y ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ)) := by
        apply setLIntegral_mono' isOpen_ball.measurableSet
        intro x hxQ
        refine (ct_frac_inner_split hσ z x F hF).trans ?_
        rw [← add_assoc]
        exact add_le_add (hP x hxQ) le_rfl
    _ = (∫⁻ x in ctQ z, ENNReal.ofReal ((Cn + 2 * Cx) * M ^ 2 * ctM z x ^ (-a))) +
          ∫⁻ x in ctQ z, 2 * ∫⁻ y in ctQ z ∩ (Metric.ball x (ctM z x / 2))ᶜ,
            ENNReal.ofReal (F y ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) :=
        lintegral_add_left hmeasC _
    _ = (∫⁻ x in ctQ z, ENNReal.ofReal ((Cn + 2 * Cx) * M ^ 2 * ctM z x ^ (-a))) +
          2 * ∫⁻ x in ctQ z, ∫⁻ y in ctQ z ∩ (Metric.ball x (ctM z x / 2))ᶜ,
            ENNReal.ofReal (F y ^ 2) / (ENNReal.ofReal ‖x - y‖) ^ ((d : ℝ) + 2 * σ) := by
        rw [lintegral_const_mul' 2 _ (by norm_num)]
    _ ≤ ENNReal.ofReal (((Cn + 2 * Cx) * M ^ 2) * K) +
          2 * ENNReal.ofReal ((Cy * M ^ 2) * K) :=
        add_le_add (ct_lintegral_ctM_rpow_le z (by positivity) ha0 ha1)
          (mul_le_mul_right hY 2)
    _ = ENNReal.ofReal (((Cn + 2 * Cx) + 2 * Cy) * K * M ^ 2) := by
        have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        ring

/-- **The fractional double integral.** -/
theorem ct_fractional_double_integral [NeZero d] {β σ : ℝ} (hβ : β ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hσ : 0 < σ) (hσβ : σ < β - 1 / 2) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (z : (Fin d → ℝ)) (M : ℝ) (F : (Fin d → ℝ) → ℝ),
      0 ≤ M → ContinuousOn F (ctQ z) →
      (∀ x ∈ ctQ z, |F x| ≤ M * ctM z x ^ (β - 1)) →
      (∀ x ∈ ctQ z, ∀ y, ‖y - x‖ < ctM z x / 2 →
        |F x - F y| ≤ M * ctM z x ^ (β - 2) * ‖x - y‖) →
      ∫⁻ x in ctQ z, ∫⁻ y in ctQ z, ctFracKer σ F x y ≤ ENNReal.ofReal (Cf * M ^ 2) := by
  obtain ⟨Cf, hCf0, hCf⟩ := ct_fractional_double_integral_meas (d := d) hβ hσ hσβ
  refine ⟨Cf, hCf0, ?_⟩
  intro z M F hM hcont hbd hlip
  classical
  set F₀ : (Fin d → ℝ) → ℝ := (ctQ z).piecewise F (fun _ => 0) with hF₀
  have hF₀m : Measurable F₀ :=
    ContinuousOn.measurable_piecewise hcont continuousOn_const isOpen_ball.measurableSet
  have hF₀eq : ∀ x ∈ ctQ z, F₀ x = F x := fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have h := hCf z M F₀ hM hF₀m (fun x hx => by rw [hF₀eq x hx]; exact hbd x hx)
    (fun x hx y hy => by
      have hm := ctM_pos hx
      have hyQ : y ∈ ctQ z := mem_ctQ_of_dist_lt_ctM hx (by linarith)
      rw [hF₀eq x hx, hF₀eq y hyQ]
      exact hlip x hx y hy)
  calc ∫⁻ x in ctQ z, ∫⁻ y in ctQ z, ctFracKer σ F x y
      = ∫⁻ x in ctQ z, ∫⁻ y in ctQ z, ctFracKer σ F₀ x y := by
        apply setLIntegral_congr_fun isOpen_ball.measurableSet
        intro x hx
        apply setLIntegral_congr_fun isOpen_ball.measurableSet
        intro y hy
        simp only [ctFracKer, hF₀eq x hx, hF₀eq y hy]
    _ ≤ _ := h

end SubdiffusiveProcess.CubeTrace
