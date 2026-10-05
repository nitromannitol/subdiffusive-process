module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrierGrowth

@[expose] public section

/-!
# Logarithmic derivative growth without a smallness condition

The derivative Borel–Cantelli argument in
 is independent of the value-growth argument.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
open Filter Topology MeasureTheory _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

theorem logGradient_le_of_deriv_dyadic {d : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (g : PotentialField d) (x : Vec d)
    (hderiv : ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ ≤
      C * gradSeriesConst * Real.sqrt ((dyadicIndex x : ℝ) + 1)) :
    euclideanNorm (shellGradient g x) ≤
      logEnvelopeOf d C * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by
  have h0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have h1 : euclideanNorm (shellGradient g x) ≤
      (d : ℝ) * (C * gradSeriesConst * Real.sqrt ((dyadicIndex x : ℝ) + 1)) :=
    euclideanNorm_shellGradient_le g x |>.trans (mul_le_mul_of_nonneg_left hderiv h0)
  have hB : (0 : ℝ) ≤ C * gradSeriesConst * Real.sqrt ((dyadicIndex x : ℝ) + 1) := by
    have hgn : 0 ≤ gradSeriesConst := gradSeriesConst_nonneg
    positivity
  have := logDeriv_growth_bound hC (v := shellGradient g x)
    (by simpa using h1) hB
  simpa only [add_zero] using this

/-- Summing the shell derivative bounds gives the logarithmic envelope for
all partial sums, without any bound on their values. -/
theorem partial_logGradient_growth_of_gauge {d : ℕ} (omega : PotentialSample d)
    {C : ℝ} (hC : 0 ≤ C)
    (hgauge : ∀ n k : ℕ, ∀ p ∈ shellCoverShifts d (coverExp n k),
      translatedShellG2 k (shellCoverCenter p) omega ≤
        C * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) :
    ∀ x L, euclideanNorm (shellGradient (anchoredPartialSumField omega L) x) ≤
      logEnvelopeOf d C * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by
  have hbounds := growingBall_shell_bounds_of_forall_le omega hC hgauge
  intro x L
  have hxnorm : ‖x‖ ≤ (2 : ℝ) ^ dyadicIndex x := by
    linarith [two_add_norm_le_two_pow_dyadicIndex x]
  have hderiv := norm_deriv_anchoredPartialSumField_le hC
    (fun k ↦ (hbounds (dyadicIndex x) k).1) L (mem_closedBall_growingBallRadius hxnorm)
  exact logGradient_le_of_deriv_dyadic hC (anchoredPartialSumField omega L) x hderiv

theorem measurable_logGradientEnvelope {d : ℕ} :
    Measurable (fun omega : AnchoredC11Sample d ↦ logEnvelopeOf d (derivEnvelope omega.val)) := by
  unfold logEnvelopeOf
  exact ((((measurable_derivEnvelope (d := d)).comp measurable_subtype_coe).const_mul ((d : ℝ) + 1)).mul_const gradSeriesConst).mul_const sqrtLogConst

theorem linearGrowth_exp_of_logGradient {d : ℕ} (g : PotentialField d) {C : ℝ}
    (hC : 0 ≤ C)
    (hlog : ∀ x, euclideanNorm (shellGradient g x) ≤
      C * (1 + Real.sqrt (Real.log (2 + ‖x‖)))) :
    ∀ x, euclideanNorm (euclideanGradient (fun y ↦ Real.exp (g y)) x) + Real.exp (g x) ≤
      (5 * C / 2 + 1) * Real.exp (g x) * (1 + ‖x‖) := by
  intro x
  have h1 := mul_le_mul_of_nonneg_left (one_add_sqrt_log_le ‖x‖ (norm_nonneg x)) hC
  have h2 : euclideanNorm (shellGradient g x) ≤ C * (5 / 2 * (1 + ‖x‖)) := by
    calc euclideanNorm (shellGradient g x)
        ≤ C * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := hlog x
      _ ≤ C * (5 / 2 * (1 + ‖x‖)) := by nlinarith
  rw [euclideanGradient_exp_potentialField, euclideanNorm_smul,
    abs_of_pos (Real.exp_pos (g x))]
  have h3 : Real.exp (g x) * euclideanNorm (shellGradient g x)
      ≤ Real.exp (g x) * (5 * C / 2 * (1 + ‖x‖)) := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos (g x)).le
    have hrw : C * (5 / 2 * (1 + ‖x‖)) = 5 * C / 2 * (1 + ‖x‖) := by ring
    linarith [h2, hrw]
  have h4 : Real.exp (g x) * ‖x‖ ≥ 0 := by
    nlinarith [norm_nonneg x, Real.exp_pos (g x)]
  nlinarith [h3, h4]

theorem ae_partial_logGradient_growth {d : ℕ} (M : GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ x L,
      euclideanNorm (shellGradient (anchoredPartialSumField omega L) x) ≤
        logEnvelopeOf d (derivEnvelope omega) * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by
  filter_upwards [ae_forall_translatedShellG2_le_derivEnvelope M] with omega h
  exact partial_logGradient_growth_of_gauge omega (derivEnvelope_nonneg omega) h

theorem logGradient_anchoredLog_le {d : ℕ} (omega : AnchoredC11Sample d) {C : ℝ}
    (h : ∀ x L, euclideanNorm (shellGradient (anchoredPartialSumField omega.val L) x) ≤
      C * (1 + Real.sqrt (Real.log (2 + ‖x‖)))) :
    ∀ x, euclideanNorm (shellGradient (anchoredLog omega) x) ≤
      C * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by
  intro x
  exact euclideanNorm_shellGradient_anchoredLog_le omega x (fun L => h x L)

theorem reversible_linearGrowth_pos_mul {d : ℕ} {a : Vec d → ℝ}
    (ha : Differentiable ℝ a) {s K : ℝ} (hs : 0 < s)
    (h : ∀ x, euclideanNorm (euclideanGradient a x) + a x ≤ K * a x * (1 + ‖x‖)) :
    ∀ x, euclideanNorm (euclideanGradient (fun y ↦ s * a y) x) + s * a x ≤
      K * (s * a x) * (1 + ‖x‖) := by
  intro x
  rw [euclideanGradient_const_mul ha s x, euclideanNorm_smul, abs_of_pos hs]
  nlinarith [mul_le_mul_of_nonneg_left (h x) hs.le]

theorem aCutoff_eq_origin_mul_exp_partial {d : ℕ} (M : GMCModel d)
    (omega : AnchoredC11Sample d) (L : ℕ) :
    aCutoff M L omega.val = fun x ↦ aCutoff M L omega.val 0 *
      Real.exp (anchoredPartialSumField omega.val L x) := by
  nth_rw 1 [← coefficientAt_natCast M L omega]
  rw [coefficientAt_natCast_eq_const_mul_anchoredCutoff M L omega]
  funext x
  rw [anchoredCutoff_eq_exp_field]

theorem divergence_linearGrowth_pos_mul {d : ℕ} {a : Vec d → ℝ}
    (ha : Differentiable ℝ a) {s K : ℝ} (hs : 0 < s)
    (h : ∀ x, euclideanNorm (euclideanGradient a x) + a x ≤ K * (1 + ‖x‖)) :
    ∀ x, euclideanNorm (euclideanGradient (fun y ↦ s * a y) x) + s * a x ≤
      (s * K) * (1 + ‖x‖) := by
  intro x
  rw [euclideanGradient_const_mul ha s x, euclideanNorm_smul, abs_of_pos hs]
  nlinarith [mul_le_mul_of_nonneg_left (h x) hs.le]

theorem anchoredCutoff_eq_inv_origin_mul {d : ℕ} (M : GMCModel d)
    (omega : PotentialSample d) (L : ℕ) :
    anchoredCutoff M L omega = fun x ↦ (aCutoff M L omega 0)⁻¹ * aCutoff M L omega x := by
  funext x
  simp only [anchoredCutoff, div_eq_mul_inv, mul_comm]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
