module

public import Mathlib

@[expose] public section

/-! Scalar estimates for the local torsion survival constant and its exponential bound. -/

set_option autoImplicit false

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support

open scoped ENNReal NNReal

noncomputable section

theorem localTorsion_probability_algebra {kappa A F p : ℝ}
    (hA : 0 < A) (hF : 0 < F)
    (h : kappa * F ≤ kappa * F / 2 + A * F * p) : kappa / (2 * A) ≤ p := by
  apply (div_le_iff₀ (by linarith : (0:ℝ) < 2 * A)).2
  have hm : kappa * F ≤ p * (2 * A) * F := by nlinarith only [h]
  exact le_of_mul_le_mul_right hm hF

theorem localTorsion_laplace_constant {a e : ℝ} (ha : 0 < a)
    (he0 : 0 ≤ e) (he1 : e < 1) : 0 < a * (1 - e) ∧ a * (1 - e) ≤ a := by
  constructor
  · exact mul_pos ha (by linarith)
  · have h1 : 1 - e ≤ 1 := by linarith
    have h2 : a * (1 - e) ≤ a * 1 := mul_le_mul_of_nonneg_left h1 ha.le
    simpa using h2

theorem localTorsion_laplace_tail {tau : ℝ≥0∞} {kappa F : ℝ}
    (hk : 0 < kappa) (hF : 0 < F) (ht : ENNReal.ofReal (kappa * F / 2) ≤ tau) :
    (if tau = ∞ then 0 else ENNReal.ofReal (Real.exp (-tau.toReal / F))) ≤
      ENNReal.ofReal (Real.exp (-kappa / 2)) := by
  by_cases htop : tau = ∞
  · simp [htop]
  · rw [if_neg htop]
    have h := ENNReal.toReal_mono htop ht
    rw [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ kappa * F / 2)] at h
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hF).2
    nlinarith only [h]

theorem localTorsion_toReal_bound {a t M : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hM : 0 ≤ M) {p : ℝ≥0∞} (hp : p ≠ ∞)
    (h : ENNReal.ofReal a ≤ ENNReal.ofReal t + ENNReal.ofReal M * p) :
    a ≤ t + M * p.toReal := by
  have hm : ENNReal.ofReal M * p ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp
  have hf : ENNReal.ofReal t + ENNReal.ofReal M * p ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hm⟩
  have hr := ENNReal.toReal_mono hf h
  rw [ENNReal.toReal_ofReal ha, ENNReal.toReal_add ENNReal.ofReal_ne_top hm,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ht, ENNReal.toReal_ofReal hM] at hr
  exact hr

theorem localTorsion_ofReal_bound {a : ℝ} {p : ℝ≥0∞}
    (hp : p ≠ ∞) (h : a ≤ p.toReal) : ENNReal.ofReal a ≤ p := by
  have hm := ENNReal.ofReal_le_ofReal h
  simpa only [ENNReal.ofReal_toReal hp] using hm

theorem localTorsion_survival_constant {kappa A : ℝ} (hk : 0 < kappa)
    (hkA : kappa ≤ A) : 0 < kappa / (2 * A) ∧ kappa / (2 * A) ≤ 1 := by
  have hA : 0 < A := hk.trans_le hkA
  have h2 : 0 < 2 * A := by positivity
  refine ⟨div_pos hk h2, (div_le_iff₀ h2).2 ?_⟩
  nlinarith only [hkA, hA]

theorem localTorsion_exp_constant {kappa : ℝ} (hk : 0 < kappa) :
    0 < Real.exp (-kappa / 2) ∧ Real.exp (-kappa / 2) < 1 := by
  constructor
  · exact Real.exp_pos _
  · have h : -kappa / 2 < 0 := by linarith
    have := Real.exp_lt_exp.mpr h
    simpa only [Real.exp_zero] using this

theorem localTorsion_laplace_one (tau : ℝ≥0∞) {F : ℝ} (hF : 0 < F) :
    (if tau = ∞ then 0 else ENNReal.ofReal (Real.exp (-tau.toReal / F))) ≤ 1 := by
  by_cases h : tau = ∞
  · simp [h]
  · simp only [if_neg h]
    have h1 : (-tau.toReal / F) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (ENNReal.toReal_nonneg (a := tau))) hF.le
    have h2 : Real.exp (-tau.toReal / F) ≤ Real.exp 0 := Real.exp_le_exp.mpr h1
    rw [Real.exp_zero] at h2
    exact ENNReal.ofReal_le_one.mpr h2

theorem localTorsion_laplace_weights {a p q e : ℝ}
    (hap : a ≤ p) (hsum : p + q = 1) (he : e ≤ 1) :
    e * p + q ≤ 1 - a * (1 - e) := by
  have hm : 0 ≤ (1 - e) * (p - a) :=
    mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hap)
  nlinarith only [hm, hsum]

theorem localTorsion_weighted_ofReal {p q : ℝ≥0∞} (hp : p ≠ ∞) (hq : q ≠ ∞)
    {e : ℝ} (he : 0 ≤ e) :
    ENNReal.ofReal e * p + q = ENNReal.ofReal (e * p.toReal + q.toReal) := by
  calc ENNReal.ofReal e * p + q
      = ENNReal.ofReal e * ENNReal.ofReal p.toReal + ENNReal.ofReal q.toReal := by
        rw [ENNReal.ofReal_toReal hp, ENNReal.ofReal_toReal hq]
    _ = ENNReal.ofReal (e * p.toReal) + ENNReal.ofReal q.toReal := by
        rw [← ENNReal.ofReal_mul he]
    _ = ENNReal.ofReal (e * p.toReal + q.toReal) := by
        rw [← ENNReal.ofReal_add (mul_nonneg he ENNReal.toReal_nonneg)
          ENNReal.toReal_nonneg]

theorem localTorsion_probability_real {a : ℝ} (ha : 0 ≤ a)
    {p : ℝ≥0∞} (hp : p ≠ ∞) (h : ENNReal.ofReal a ≤ p) : a ≤ p.toReal := by
  simpa only [ENNReal.toReal_ofReal ha] using ENNReal.toReal_mono hp h

theorem localTorsion_time_coe {t : ℝ≥0} {r : ℝ} (ht : (t : ℝ) = r) :
    (t : ℝ≥0∞) = ENNReal.ofReal r := by
  rw [← ht, ENNReal.ofReal_coe_nnreal]

theorem localTorsion_coefficients_nonneg {kappa A F : ℝ}
    (hk : 0 ≤ kappa) (hA : 0 < A) (hF : 0 < F) :
    0 ≤ kappa * F ∧ 0 ≤ kappa * F / 2 ∧ 0 ≤ A * F := by
  refine ⟨?_, ?_, ?_⟩ <;> positivity

theorem localTorsion_constants {kappa A : ℝ} (hk : 0 < kappa)
    (hkA : kappa ≤ A) :
    0 < kappa / (2 * A) * (1 - Real.exp (-kappa / 2)) ∧
    kappa / (2 * A) * (1 - Real.exp (-kappa / 2)) ≤ kappa / (2 * A) ∧
    0 < kappa / (2 * A) ∧ 0 ≤ Real.exp (-kappa / 2) ∧ Real.exp (-kappa / 2) ≤ 1 := by
  obtain ⟨ha, _⟩ := localTorsion_survival_constant hk hkA
  obtain ⟨he0, he1⟩ := localTorsion_exp_constant hk
  obtain ⟨h1, h2⟩ := localTorsion_laplace_constant ha he0.le he1
  exact ⟨h1, h2, ha, he0.le, he1.le⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
