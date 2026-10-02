import SubdiffusiveProcess.Static.CutoffMassMomentBound
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Moment calculus for native coercivity suppliers -/

open MeasureTheory SubdiffusiveProcess.Static
open scoped ENNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Static

theorem coercivity_norm_of_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    {K : Ω → ℝ} (hK : ∀ ω, 0 ≤ K ω)
    (h : (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂μ) ≤ ENNReal.ofReal C) :
    eLpNorm K (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (C ^ q⁻¹) := by
  rw [lintegral_rpow_eq_eLpNorm_rpow μ K hK hq] at h
  have h' := ENNReal.rpow_le_rpow h (inv_nonneg.mpr hq.le)
  rw [ENNReal.rpow_rpow_inv hq.ne',
    ENNReal.ofReal_rpow_of_nonneg hC (inv_nonneg.mpr hq.le)] at h'
  exact h'

theorem coercivity_moment_of_norm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {q B : ℝ} (hq : 0 < q) (hB : 0 ≤ B)
    {K : Ω → ℝ} (hK : ∀ ω, 0 ≤ K ω)
    (h : eLpNorm K (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B) :
    (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂μ) ≤ ENNReal.ofReal (B ^ q) := by
  rw [lintegral_rpow_eq_eLpNorm_rpow μ K hK hq]
  exact (ENNReal.rpow_le_rpow h hq.le).trans_eq
    (ENNReal.ofReal_rpow_of_nonneg hB hq.le)

theorem coercivity_norm_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {q : ℝ} (hq : 0 < q) {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun ω => f ω * g ω) (ENNReal.ofReal q) μ ≤
      eLpNorm f (ENNReal.ofReal (2 * q)) μ *
        eLpNorm g (ENNReal.ofReal (2 * q)) μ := by
  have h2q : 0 < 2 * q := by positivity
  simp only [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hq).ne'
    ENNReal.ofReal_ne_top, eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr h2q).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le,
    ENNReal.toReal_ofReal h2q.le]
  have h := eLpNorm'_le_eLpNorm'_mul_eLpNorm' hf hg (fun a b : ℝ => a * b) 1
    (Filter.Eventually.of_forall fun ω => by simp [nnnorm_mul]) hq
    (by linarith : q < 2 * q)
    (by field_simp; ring : 1 / q = 1 / (2 * q) + 1 / (2 * q))
  simpa only [ENNReal.coe_one, one_mul] using h

theorem coercivity_norm_const {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {q a : ℝ}
    (hq : 0 < q) (ha : 0 ≤ a) :
    eLpNorm (fun _ : Ω => a) (ENNReal.ofReal q) μ = ENNReal.ofReal a := by
  rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr hq).ne' (NeZero.ne μ)]
  simp only [measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal ha]

theorem coercivity_norm_scale {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q : ℝ) {a : ℝ} (ha : 0 ≤ a) (f : Ω → ℝ) :
    eLpNorm (fun ω => f ω * a) (ENNReal.ofReal q) μ =
      ENNReal.ofReal a * eLpNorm f (ENNReal.ofReal q) μ := by
  simpa only [Pi.smul_apply, smul_eq_mul, mul_comm, Real.enorm_eq_ofReal ha] using
    eLpNorm_const_smul a f (ENNReal.ofReal q) μ

theorem coercivity_norm_finite_bank {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q : ℝ) (F : ℕ → Ω → ℝ) (S : Finset ℕ)
    (hF : ∀ i, eLpNorm (F i) (ENNReal.ofReal q) μ < ⊤) {L : ℕ} (hL : L ∈ S) :
    eLpNorm (F L) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (1 + ∑ i ∈ S, (eLpNorm (F i) (ENNReal.ofReal q) μ).toReal) := by
  calc
    eLpNorm (F L) (ENNReal.ofReal q) μ =
        ENNReal.ofReal (eLpNorm (F L) (ENNReal.ofReal q) μ).toReal :=
      (ENNReal.ofReal_toReal (hF L).ne).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hh : (eLpNorm (F L) (ENNReal.ofReal q) μ).toReal ≤
          ∑ i ∈ S, (eLpNorm (F i) (ENNReal.ofReal q) μ).toReal :=
        Finset.single_le_sum (f := fun i => (eLpNorm (F i) (ENNReal.ofReal q) μ).toReal)
          (fun _ _ => ENNReal.toReal_nonneg) hL
      linarith

end SubdiffusiveProcess.Static
