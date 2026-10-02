import SubdiffusiveProcess.Meyers.Restrict
import SubdiffusiveProcess.Meyers.PoincareBridge

/-! The estimate on one grid ball: the exact Meyers leaf (as the hypothesis `MeyersEstimate`) applied on
`B_E(y_k, l/3) ⊂ B_E(y_k, 2l/3) ⊂ Ω = B_E(y_k, l) ⊂ B∞(x0, 2l)`. -/

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Meyers

variable {d : ℕ}

theorem toReal_eLpNorm_bounded_le {μ : Measure (Vec d)} [IsFiniteMeasure μ] {f : Vec d → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ᵐ x ∂μ, |f x| ≤ B) {p : ℝ} (hp : 0 < p) :
    (eLpNorm f (ENNReal.ofReal p) μ).toReal ≤ B * (μ Set.univ).toReal ^ (1 / p) := by
  have h1 := eLpNorm_le_of_ae_bound (p := ENNReal.ofReal p) (μ := μ) (f := f) (C := B)
    (by simpa [Real.norm_eq_abs] using hf)
  have h2 : (eLpNorm f (ENNReal.ofReal p) μ).toReal ≤
      ((μ Set.univ) ^ (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal B).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by
      rw [ENNReal.toReal_ofReal hp.le]; positivity) (measure_ne_top _ _)) ENNReal.ofReal_ne_top) h1
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hB,
    ENNReal.toReal_ofReal hp.le, inv_eq_one_div] at h2
  linarith [mul_comm B ((μ Set.univ).toReal ^ (1 / p))]

theorem ball_bound {p epsilon C0 : ℝ} (hp : 2 ≤ p) (hC0 : 0 < C0)
    (hM : MeyersEstimate d p epsilon C0)
    (x0 : Vec d) {l : ℝ} (hl : 0 < l) (a : Vec d → ℝ) {a0 : ℝ} (ha0 : 0 < a0)
    (haM : AEMeasurable a (volume.restrict (Metric.ball x0 (2 * l))))
    (hnear : ∀ᵐ x ∂volume.restrict (Metric.ball x0 (2 * l)), |a x - a0| ≤ epsilon * a0)
    (F : Vec d → ℝ) (Kf : ℝ) (hFM : AEMeasurable F (volume.restrict (Metric.ball x0 (2 * l))))
    (hKf : 0 ≤ Kf) (hFb : ∀ᵐ x ∂volume.restrict (Metric.ball x0 (2 * l)), |F x| ≤ Kf)
    (v : H1Function (Metric.ball x0 (2 * l)))
    (heq : ∀ phi : H10Function (Metric.ball x0 (2 * l)),
      (∫ x in Metric.ball x0 (2 * l), a x * (∑ i : Fin d, v.grad x i * phi.toH1Function.grad x i)) =
        ∫ x in Metric.ball x0 (2 * l), F x * phi.toH1Function.toFun x)
    (k : Fin d → Fin (3 * d + 1)) :
    MemLp (fun x => Real.sqrt (∑ i : Fin d, (v.grad x i) ^ 2)) (ENNReal.ofReal p)
        (volume.restrict (eBall (x0 + l • gridCenter d k) (l / 3))) ∧
      (eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (v.grad x i) ^ 2)) (ENNReal.ofReal p)
        (volume.restrict (eBall (x0 + l • gridCenter d k) (l / 3)))).toReal ≤
      C0 * ((l / 3) ^ ((d : ℝ) * (1 / p - 1 / 2) - 1) *
          (eLpNorm v.toFun 2 (volume.restrict (Metric.ball x0 (2 * l)))).toReal
        + (l / 3) * ((Kf / a0) * (volume.real (Metric.ball x0 (2 * l))) ^ (1 / p))) := by
  have hp0 : 0 < p := by linarith
  have hρ : 0 < l / 3 := by positivity
  have hsub3 : eBall (x0 + l • gridCenter d k) (3 * (l / 3)) ⊆ Metric.ball x0 (2 * l) := by
    have : 3 * (l / 3) = l := by ring
    rw [this]; exact eBall_grid_subset x0 hl k
  have hsub2 : eBall (x0 + l • gridCenter d k) (2 * (l / 3)) ⊆ Metric.ball x0 (2 * l) :=
    (eBall_mono _ (by positivity) (by linarith)).trans hsub3
  have hfin3 : IsFiniteMeasure (volume.restrict (eBall (x0 + l • gridCenter d k) (3 * (l / 3)))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_lt (measure_mono hsub3) measure_ball_lt_top⟩
  have hfin2 : IsFiniteMeasure (volume.restrict (eBall (x0 + l • gridCenter d k) (2 * (l / 3)))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_lt (measure_mono hsub2) measure_ball_lt_top⟩
  have hnorm := normalize_weak_eq (a0 := a0) a F v heq
  have hrestr := restrict_weak_eq Metric.isOpen_ball (isOpen_eBall (x0 + l • gridCenter d k) (3 * (l / 3)))
    hsub3 (fun x => a x / a0) (fun x => -F x / a0) v hnorm
  have haM' : AEMeasurable (fun x => a x / a0)
      (volume.restrict (eBall (x0 + l • gridCenter d k) (3 * (l / 3)))) :=
    (haM.div_const a0).mono_measure (Measure.restrict_mono hsub3 le_rfl)
  have hnear' : ∀ᵐ x ∂volume.restrict (eBall (x0 + l • gridCenter d k) (3 * (l / 3))),
      |a x / a0 - 1| ≤ epsilon := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub3 hnear] with x hx
    rw [show a x / a0 - 1 = (a x - a0) / a0 by field_simp, abs_div, abs_of_pos ha0, div_le_iff₀ ha0]
    exact hx
  have hh' : MemLp (fun x => -F x / a0) (ENNReal.ofReal p)
      (volume.restrict (eBall (x0 + l • gridCenter d k) (3 * (l / 3)))) := by
    apply MemLp.of_bound (C := Kf / a0)
    · exact ((hFM.mono_measure (Measure.restrict_mono hsub3 le_rfl)).neg.div_const a0).aestronglyMeasurable
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub3 hFb] with x hx
      rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos ha0]
      exact div_le_div_of_nonneg_right hx ha0.le
  have hres := hM (x0 + l • gridCenter d k) (l / 3) hρ (fun x => a x / a0) (fun x => -F x / a0)
    haM' hnear' hh' (v.restrict (isOpen_eBall _ _) hsub3) hrestr
  refine ⟨hres.1, hres.2.trans ?_⟩
  have hA : (eLpNorm v.toFun 2
      (volume.restrict (eBall (x0 + l • gridCenter d k) (2 * (l / 3))))).toReal ≤
      (eLpNorm v.toFun 2 (volume.restrict (Metric.ball x0 (2 * l)))).toReal :=
    ENNReal.toReal_mono v.memL2.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono hsub2 le_rfl))
  have hB : (eLpNorm (fun x => -F x / a0) (ENNReal.ofReal p)
      (volume.restrict (eBall (x0 + l • gridCenter d k) (2 * (l / 3))))).toReal ≤
      (Kf / a0) * (volume.real (Metric.ball x0 (2 * l))) ^ (1 / p) := by
    have h1 := toReal_eLpNorm_bounded_le (μ := volume.restrict (eBall (x0 + l • gridCenter d k) (2 * (l / 3))))
      (f := fun x => -F x / a0) (B := Kf / a0) (by positivity) (by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub2 hFb] with x hx
        rw [abs_div, abs_neg, abs_of_pos ha0]
        exact div_le_div_of_nonneg_right hx ha0.le) hp0
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow ENNReal.toReal_nonneg _ (by positivity)
    rw [Measure.restrict_apply_univ, Measure.real]
    exact ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono hsub2)
  have hpow : 0 ≤ (l / 3) ^ ((d : ℝ) * (1 / p - 1 / 2) - 1) := Real.rpow_nonneg hρ.le _
  apply mul_le_mul_of_nonneg_left _ hC0.le
  exact add_le_add (mul_le_mul_of_nonneg_left hA hpow) (mul_le_mul_of_nonneg_left hB hρ.le)

end SubdiffusiveProcess.Meyers
