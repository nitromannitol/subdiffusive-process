module

public import SubdiffusiveProcess.Static.CutoffChartCoercivity

@[expose] public section

/-! # Exact translation of native real-cube coercivity -/

open MeasureTheory Homogenization SubdiffusiveProcess.Static
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

private theorem translate_origin_ball {d : ℕ} (y : Vec d) (s : ℝ) :
    translateSet y (Metric.ball (0 : Vec d) (s / 2)) = Metric.ball y (s / 2) := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  simp only [Metric.mem_ball, dist_eq_norm, sub_zero]

private def translatedH1 {d : ℕ} (y : Vec d) (s : ℝ)
    (H : H1Function (Metric.ball y (s / 2))) : H1Function (Metric.ball (0 : Vec d) (s / 2)) :=
  H1Function.untranslate y ((translate_origin_ball y s).symm ▸ H)

private def translatedH10 {d : ℕ} (y : Vec d) (s : ℝ)
    (H : H10Function (Metric.ball y (s / 2))) : H10Function (Metric.ball (0 : Vec d) (s / 2)) :=
  H10Function.untranslate y ((translate_origin_ball y s).symm ▸ H)

private theorem translatedH1_values {d : ℕ} (y : Vec d) (s : ℝ)
    (H : H1Function (Metric.ball y (s / 2))) :
    (translatedH1 y s H).toFun = (fun x => H.toFun (y + x)) ∧
    (translatedH1 y s H).grad = (fun x => H.grad (y + x)) := by
  have hf : ∀ {U V : Set (Vec d)} (h : U = V) (H : H1Function U),
      (h ▸ H : H1Function V).toFun = H.toFun ∧ (h ▸ H : H1Function V).grad = H.grad := by
    intro U V h H; subst V; exact ⟨rfl, rfl⟩
  constructor
  · funext x
    simp only [translatedH1, H1Function.untranslate_toFun, (hf _ H).1, add_comm]
  · funext x
    simp only [translatedH1, H1Function.untranslate_grad, (hf _ H).2, add_comm]

private theorem translatedH10_values {d : ℕ} (y : Vec d) (s : ℝ)
    (H : H10Function (Metric.ball y (s / 2))) :
    (translatedH10 y s H).toFun = (fun x => H.toFun (y + x)) ∧
    (translatedH10 y s H).grad = (fun x => H.grad (y + x)) := by
  have hf : ∀ {U V : Set (Vec d)} (h : U = V) (H : H10Function U),
      (h ▸ H : H10Function V).toFun = H.toFun ∧ (h ▸ H : H10Function V).grad = H.grad := by
    intro U V h H; subst V; exact ⟨rfl, rfl⟩
  change (H1Function.untranslate y ((translate_origin_ball y s).symm ▸ H).toH1Function).toFun = _ ∧
    (H1Function.untranslate y ((translate_origin_ball y s).symm ▸ H).toH1Function).grad = _
  constructor
  · funext x
    simp only [H1Function.untranslate_toFun, (hf _ H).1, add_comm]
  · funext x
    simp only [H1Function.untranslate_grad, (hf _ H).2, add_comm]

theorem cubeCoercivityEstimates_translate {d : ℕ} (y : Vec d) {s K : ℝ}
    (hs : 0 < s) (A : Vec d → ℝ)
    (h : cubeCoercivityEstimates (fun x => A (y + x)) 0 s K) :
    cubeCoercivityEstimates A y s K := by
  have hn : ∀ u : Vec d → ℝ, fractionalSqNorm (Metric.ball y (s / 2)) u =
      fractionalSqNorm (Metric.ball (0 : Vec d) (s / 2)) (fun x => u (y + x)) := by
    intro u
    change fractionalSeminormSq _ _ + _ = fractionalSeminormSq _ _ + _
    rw [fractionalSeminormSq_ball_affine y hs, fractionalSeminormSq_ball_affine 0 hs,
      l2Sq_ball_affine y hs, l2Sq_ball_affine 0 hs]
    simp only [zero_add]
  have he : ∀ F : Vec d → Vec d, energy (Metric.ball y (s / 2)) A F =
      energy (Metric.ball (0 : Vec d) (s / 2)) (fun x => A (y + x)) (fun x => F (y + x)) := by
    intro F
    rw [energy_ball_affine y hs, energy_ball_affine 0 hs]
    simp only [zero_add]
  have hl : ∀ u : Vec d → ℝ,
      (∫⁻ x in Metric.ball y (s / 2), ENNReal.ofReal (u x ^ 2)) =
        ∫⁻ x in Metric.ball (0 : Vec d) (s / 2), ENNReal.ofReal (u (y + x) ^ 2) := by
    intro u
    rw [l2Sq_ball_affine y hs, l2Sq_ball_affine 0 hs]
    simp only [zero_add]
  constructor
  · intro H
    have hh := h.1 (translatedH1 y s H)
    rw [(translatedH1_values y s H).1, (translatedH1_values y s H).2] at hh
    simpa only [hn, he, hl] using hh
  · intro H
    have hh := h.2 (translatedH10 y s H)
    rw [(translatedH10_values y s H).1, (translatedH10_values y s H).2] at hh
    simpa only [hn, he] using hh

end SubdiffusiveProcess.Static
