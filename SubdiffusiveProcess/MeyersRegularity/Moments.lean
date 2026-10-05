module

public import SubdiffusiveProcess.MeyersRegularity.Basic
public import SubdiffusiveProcess.Analysis.RawLp

@[expose] public section

/-! Interior Meyers regularity: Moments. -/

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]


/-- Expanded moment formula in the original measure. -/
theorem truncatedMoment_eq_lintegral {μ : Measure α} {f : α → E} (p T : ℝ)
    (hf : AEStronglyMeasurable f μ) :
    truncatedMoment μ f p T =
      ∫⁻ x, ENNReal.ofReal (‖f x‖^2 * (min ‖f x‖ T)^(p-2)) ∂μ := by
  unfold truncatedMoment CubeCalderonZygmund.sqWeightedMeasure
  rw [lintegral_withDensity_eq_lintegral_mul₀
    (hf.norm.aemeasurable.pow aemeasurable_const).ennreal_ofReal
    ((hf.norm.aemeasurable.min aemeasurable_const).pow aemeasurable_const).ennreal_ofReal]
  apply lintegral_congr
  intro x
  change ENNReal.ofReal (‖f x‖^2) * ENNReal.ofReal ((min ‖f x‖ T)^(p-2)) = _
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]

theorem sqWeightedMeasure_univ_eq {μ : Measure α} (f : α → E) :
    CubeCalderonZygmund.sqWeightedMeasure f μ univ = (SubdiffusiveProcess.RawLp.eLpNorm f 2 μ)^2 := by
  rw [CubeCalderonZygmund.sqWeightedMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [← ENNReal.rpow_natCast,
    SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (by norm_num) (by norm_num) f μ, ← ENNReal.rpow_mul]
  norm_num

theorem eLpNorm_rpow_eq_lintegral {μ : Measure α} (f : α → E) {p : ℝ} (hp : 0 < p) :
    (SubdiffusiveProcess.RawLp.eLpNorm f (ENNReal.ofReal p) μ)^p =
      ∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ := by
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral
    (by simpa only [ne_eq, ENNReal.ofReal_eq_zero] using not_le.mpr hp)
    ENNReal.ofReal_ne_top f μ, ← ENNReal.rpow_mul, ENNReal.toReal_ofReal hp.le,
    one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]

theorem truncatedMoment_mono_measure {μ ν : Measure α} (hμ : μ ≤ ν)
    (f : α → E) (p T : ℝ) :
    truncatedMoment μ f p T ≤ truncatedMoment ν f p T := by
  unfold truncatedMoment
  apply lintegral_mono' ?_ (fun _ => le_rfl)
  apply Measure.le_iff.2
  intro s hs
  rw [CubeCalderonZygmund.sqWeightedMeasure, CubeCalderonZygmund.sqWeightedMeasure,
    withDensity_apply _ hs, withDensity_apply _ hs]
  exact lintegral_mono' (Measure.restrict_mono Subset.rfl hμ) (fun _ => le_rfl)

theorem truncatedMoment_le_energy {μ : Measure α} {f : α → E} {p T : ℝ}
    (hf : MemLp f 2 μ) (hp : 2 < p) (hT : 0 ≤ T) :
    truncatedMoment μ f p T ≤
      ENNReal.ofReal (T ^ (p - 2)) * (eLpNorm f 2 μ)^2 := by
  calc
    truncatedMoment μ f p T ≤
        ∫⁻ x, ENNReal.ofReal (T^(p-2)) ∂(CubeCalderonZygmund.sqWeightedMeasure f μ) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
        (le_min (norm_nonneg _) hT) (min_le_right _ _) (by linarith))
    _ = _ := by rw [lintegral_const, sqWeightedMeasure_univ_eq, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hf.aestronglyMeasurable]

theorem truncatedMoment_ne_top {μ : Measure α} {f : α → E} {p T : ℝ}
    (hf : MemLp f 2 μ) (hp : 2 < p) (hT : 0 ≤ T) :
    truncatedMoment μ f p T ≠ ⊤ := by
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hf.eLpNorm_ne_top))
    (truncatedMoment_le_energy hf hp hT)

theorem truncatedMoment_le_full {μ : Measure α} {f : α → E} {p T : ℝ}
    (hf : AEStronglyMeasurable f μ) (hp : 2 < p) (hT : 0 ≤ T) :
    truncatedMoment μ f p T ≤ (eLpNorm f (ENNReal.ofReal p) μ) ^ p := by
  rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hf, truncatedMoment_eq_lintegral p T hf, eLpNorm_rpow_eq_lintegral f (by linarith : 0 < p)]
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  calc
    ‖f x‖^2 * (min ‖f x‖ T)^(p-2) ≤ ‖f x‖^2 * ‖f x‖^(p-2) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (le_min (norm_nonneg _) hT) (min_le_left _ _) (by linarith))
        (sq_nonneg _)
    _ = ‖f x‖^p := by
      rw [← Real.rpow_two, ← Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num)
        (by linarith : 0 ≤ p-2)]
      congr 1
      ring

theorem sq_mul_rpow_sub_two {x p : ℝ} (hx : 0 ≤ x) (hp : 2 ≤ p) :
    x^2 * x^(p-2) = x^p := by
  rw [← Real.rpow_two, ← Real.rpow_add_of_nonneg hx (by norm_num) (sub_nonneg.mpr hp)]
  congr 1
  ring

theorem full_moment_le_of_truncatedMoment_le {μ : Measure α} {f : α → E}
    {p : ℝ} {K : ℝ≥0∞} (hf : AEStronglyMeasurable f μ) (hp : 2 < p)
    (h : ∀ T : ℝ, 0 ≤ T → truncatedMoment μ f p T ≤ K) :
    (eLpNorm f (ENNReal.ofReal p) μ) ^ p ≤ K := by
  let v : ℕ → α → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal (‖f x‖^2 * (min ‖f x‖ (n : ℝ))^(p-2))
  have hv : ∀ n, AEMeasurable (v n) μ := fun n =>
    ((hf.norm.aemeasurable.pow aemeasurable_const).mul
      ((hf.norm.aemeasurable.min aemeasurable_const).pow aemeasurable_const)).ennreal_ofReal
  have hmono : ∀ᵐ x ∂μ, Monotone (fun n => v n x) := by
    apply ae_of_all
    intro x n m hnm
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact Real.rpow_le_rpow (le_min (norm_nonneg _) (Nat.cast_nonneg n))
      (min_le_min le_rfl (Nat.cast_le.mpr hnm)) (by linarith)
  have hsup : ∀ x, (⨆ n, v n x) = ENNReal.ofReal (‖f x‖^p) := by
    intro x
    apply le_antisymm
    · apply iSup_le
      intro n
      apply ENNReal.ofReal_le_ofReal
      calc
        ‖f x‖^2 * (min ‖f x‖ (n : ℝ))^(p-2) ≤ ‖f x‖^2 * ‖f x‖^(p-2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
            (le_min (norm_nonneg _) (Nat.cast_nonneg n)) (min_le_left _ _) (by linarith))
            (sq_nonneg _)
        _ = _ := sq_mul_rpow_sub_two (norm_nonneg _) hp.le
    · obtain ⟨n, hn⟩ := exists_nat_ge ‖f x‖
      apply le_iSup_of_le n
      simp only [v, min_eq_left hn, sq_mul_rpow_sub_two (norm_nonneg _) hp.le, le_refl]
  rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hf, eLpNorm_rpow_eq_lintegral f (by linarith : 0 < p)]
  calc
    (∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ) = ∫⁻ x, ⨆ n, v n x ∂μ := by
      apply lintegral_congr
      intro x
      exact (hsup x).symm
    _ = ⨆ n, ∫⁻ x, v n x ∂μ := lintegral_iSup' hv hmono
    _ ≤ K := by
      apply iSup_le
      intro n
      simpa only [truncatedMoment_eq_lintegral p (n : ℝ) hf] using h (n : ℝ) (Nat.cast_nonneg n)


/-- Pointwise estimate for the squared weighted truncation. -/
theorem truncated_power_perturbation {x y z p T δ : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hp : 2 < p) (hT : 0 ≤ T)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hbound : y ≤ δ*x+z) :
    y^2 * (min y T)^(p-2) ≤ (2 : ℝ)^p *
      (δ^2 * (x^2 * (min x T)^(p-2)) + z^p) := by
  have hr : 0 ≤ p-2 := by linarith
  have hpow : 4 * (2 : ℝ)^(p-2) = (2 : ℝ)^p := by
    calc
      4 * (2 : ℝ)^(p-2) = (2 : ℝ)^(2 : ℝ) * (2 : ℝ)^(p-2) := by norm_num
      _ = (2 : ℝ)^(2+(p-2)) := (Real.rpow_add (by norm_num) _ _).symm
      _ = _ := by congr 1; ring
  have hmp : 0 ≤ (min x T)^(p-2) := Real.rpow_nonneg (le_min hx hT) _
  have hzpow : 0 ≤ z^p := Real.rpow_nonneg hz _
  have hcpow : 0 ≤ (2 : ℝ)^p := Real.rpow_nonneg (by norm_num) _
  by_cases hzx : z ≤ δ*x
  · have hyx : y ≤ 2*δ*x := by linarith
    have hyx' : y ≤ 2*x := by nlinarith
    have hmin : min y T ≤ 2*min x T := by
      rw [mul_min_of_nonneg x T (by norm_num : (0 : ℝ) ≤ 2)]
      exact min_le_min hyx' (by linarith)
    have hsq : y^2 ≤ (2*δ*x)^2 := (sq_le_sq₀ hy (by positivity)).2 hyx
    have hclip : (min y T)^(p-2) ≤ (2*min x T)^(p-2) :=
      Real.rpow_le_rpow (le_min hy hT) hmin hr
    calc
      y^2 * (min y T)^(p-2) ≤ (2*δ*x)^2 * (2*min x T)^(p-2) :=
        mul_le_mul hsq hclip (Real.rpow_nonneg (le_min hy hT) _) (sq_nonneg _)
      _ = (2 : ℝ)^p * (δ^2 * (x^2 * (min x T)^(p-2))) := by
        rw [Real.mul_rpow (by norm_num) (le_min hx hT)]
        calc
          (2*δ*x)^2 * ((2 : ℝ)^(p-2) * (min x T)^(p-2)) =
              (4 * (2 : ℝ)^(p-2)) * (δ^2 * (x^2 * (min x T)^(p-2))) := by ring
          _ = _ := by rw [hpow]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hzpow) hcpow
  · have hyz : y ≤ 2*z := by linarith
    calc
      y^2 * (min y T)^(p-2) ≤ y^2 * y^(p-2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_min hy hT)
          (min_le_left _ _) hr) (sq_nonneg _)
      _ = y^p := sq_mul_rpow_sub_two hy hp.le
      _ ≤ (2*z)^p := Real.rpow_le_rpow hy hyz (by linarith)
      _ = (2 : ℝ)^p * z^p := Real.mul_rpow (by norm_num) hz
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hmp))) hcpow


theorem truncatedMoment_perturbation {μ : Measure α} {f g H : α → E} {p T δ : ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hH : AEStronglyMeasurable H μ) (hp : 2 < p) (hT : 0 ≤ T)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hbound : ∀ᵐ x ∂μ, ‖g x‖ ≤ δ * ‖f x‖ + ‖H x‖) :
    truncatedMoment μ g p T ≤ ENNReal.ofReal ((2 : ℝ)^p) *
      (ENNReal.ofReal (δ^2) * truncatedMoment μ f p T +
        (eLpNorm H (ENNReal.ofReal p) μ)^p) := by
  rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hH, truncatedMoment_eq_lintegral p T hg,
    truncatedMoment_eq_lintegral p T hf,
    eLpNorm_rpow_eq_lintegral H (by linarith : 0 < p)]
  have hfint : AEMeasurable (fun x => ENNReal.ofReal
      (‖f x‖^2 * (min ‖f x‖ T)^(p-2))) μ :=
    ((hf.norm.aemeasurable.pow aemeasurable_const).mul
      ((hf.norm.aemeasurable.min aemeasurable_const).pow aemeasurable_const)).ennreal_ofReal
  have hHint : AEMeasurable (fun x => ENNReal.ofReal (‖H x‖^p)) μ :=
    (hH.norm.aemeasurable.pow aemeasurable_const).ennreal_ofReal
  calc
    (∫⁻ x, ENNReal.ofReal (‖g x‖^2 * (min ‖g x‖ T)^(p-2)) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal ((2 : ℝ)^p) *
          (ENNReal.ofReal (δ^2) * ENNReal.ofReal
            (‖f x‖^2 * (min ‖f x‖ T)^(p-2)) + ENNReal.ofReal (‖H x‖^p)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hbound] with x hx
      rw [← ENNReal.ofReal_mul (sq_nonneg _),
        ← ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (le_min (norm_nonneg _) hT) _)))
          (Real.rpow_nonneg (norm_nonneg _) _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
      exact ENNReal.ofReal_le_ofReal (truncated_power_perturbation
        (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hp hT hδ hδ1 hx)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left' (hfint.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]


/-- Uniform real bounds on the finite moments establish Lp membership and its norm estimate. -/
theorem memLp_and_norm_le_of_truncatedMoment_le {μ : Measure α} {f : α → E} {p K : ℝ}
    (hf : MemLp f 2 μ) (hp : 2 < p) (hK : 0 ≤ K)
    (h : ∀ T : ℝ, 0 ≤ T → (truncatedMoment μ f p T).toReal ≤ K^p) :
    MemLp f (ENNReal.ofReal p) μ ∧ (eLpNorm f (ENNReal.ofReal p) μ).toReal ≤ K := by
  have hp0 : 0 < p := by linarith
  have hm : ∀ T : ℝ, 0 ≤ T → truncatedMoment μ f p T ≤ ENNReal.ofReal (K^p) := by
    intro T hT
    rw [← ENNReal.ofReal_toReal (truncatedMoment_ne_top hf hp hT)]
    exact ENNReal.ofReal_le_ofReal (h T hT)
  have hh := full_moment_le_of_truncatedMoment_le hf.aestronglyMeasurable hp hm
  rw [← ENNReal.ofReal_rpow_of_nonneg hK hp0.le] at hh
  have hnorm := (ENNReal.rpow_le_rpow_iff hp0).mp hh
  refine ⟨memLp_iff.mpr (hnorm.trans_lt ENNReal.ofReal_lt_top), ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm).trans_eq (ENNReal.toReal_ofReal hK)


end SubdiffusiveProcess.MeyersRegularity
