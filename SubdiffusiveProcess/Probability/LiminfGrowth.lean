import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Tactic

/-! A common growth bound for a limiting random measure, obtained from finite
approximants by Fatou. The bound keeps the original moment constant; no
supremum over cutoffs or sample-dependent subsequence is needed. -/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess

/-- Fatou preserves the moment bound for the finite real version of the
pointwise lower limit of the extended norms. -/
theorem eLpNorm_liminf_enorm_toReal_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (p C : ℝ≥0) (hp : p ≠ 0)
    (hf : ∀ n, Measurable (f n))
    (hb : ∀ n, eLpNorm (f n) p P ≤ C) :
    Measurable (fun om => (liminf (fun n => ‖f n om‖ₑ) atTop).toReal) ∧
      eLpNorm (fun om => (liminf (fun n => ‖f n om‖ₑ) atTop).toReal) p P ≤ C ∧
      ∀ᵐ om ∂P, liminf (fun n => ‖f n om‖ₑ) atTop < ⊤ := by
  let k : Ω → ℝ≥0∞ := fun om => liminf (fun n => ‖f n om‖ₑ) atTop
  have hk : Measurable k := Measurable.liminf (fun n => (hf n).enorm)
  have hfin : ∀ᵐ om ∂P, k om < ⊤ :=
    ae_bdd_liminf_atTop_of_eLpNorm_bdd (by exact_mod_cast hp) hf hb
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hp)
  have hpow (om : Ω) :
      k om ^ (p : ℝ) = liminf (fun n => ‖f n om‖ₑ ^ (p : ℝ)) atTop := by
    exact OrderIso.liminf_apply (ENNReal.orderIsoRpow p hpR)
      (by isBoundedDefault) (by isBoundedDefault)
      (by isBoundedDefault) (by isBoundedDefault)
  have hint : ∫⁻ om, k om ^ (p : ℝ) ∂P ≤ (C : ℝ≥0∞) ^ (p : ℝ) := by
    simp_rw [hpow]
    refine (lintegral_liminf_le (fun n => (hf n).enorm.pow_const (p : ℝ))).trans ?_
    apply liminf_le_of_frequently_le'
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro n
    rw [← eLpNorm_nnreal_pow_eq_lintegral hp]
    exact ENNReal.rpow_le_rpow (hb n) hpR.le
  have hnorm : eLpNorm (fun om => (k om).toReal) p P ≤ C := by
    apply (ENNReal.rpow_le_rpow_iff hpR).mp
    rw [eLpNorm_nnreal_pow_eq_lintegral hp]
    calc
      ∫⁻ om, ‖(k om).toReal‖ₑ ^ (p : ℝ) ∂P = ∫⁻ om, k om ^ (p : ℝ) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hfin] with om hom
        rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hom.ne]
      _ ≤ (C : ℝ≥0∞) ^ (p : ℝ) := hint
  exact ⟨hk.ennreal_toReal, hnorm, hfin⟩

/-- A single measurable random constant controls every test set of a limiting
measure. The lower-semicontinuity and finite growth assertions are each made
on one event before the test-set quantifier. -/
theorem exists_measure_growth_of_liminf
    {Ω X T : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (muN : ℕ → Ω → Measure X) (mu : Ω → Measure X)
    (tests : T → Set X) (scale : T → ℝ≥0)
    (f : ℕ → Ω → ℝ) (p C : ℝ≥0) (hp : p ≠ 0)
    (hf : ∀ n, Measurable (f n))
    (hb : ∀ n, eLpNorm (f n) p P ≤ C)
    (hlim : ∀ᵐ om ∂P, ∀ t, mu om (tests t) ≤
      liminf (fun n => muN n om (tests t)) atTop)
    (hgrowth : ∀ᵐ om ∂P, ∀ n t,
      muN n om (tests t) ≤ (scale t : ℝ≥0∞) * ‖f n om‖ₑ) :
    ∃ K : Ω → ℝ, Measurable K ∧ (∀ om, 0 ≤ K om) ∧
      eLpNorm K p P ≤ C ∧
      ∀ᵐ om ∂P, ∀ t, mu om (tests t) ≤ ENNReal.ofReal (K om) * (scale t : ℝ≥0∞) := by
  let k : Ω → ℝ≥0∞ := fun om => liminf (fun n => ‖f n om‖ₑ) atTop
  obtain ⟨hk, hnorm, hfin⟩ := eLpNorm_liminf_enorm_toReal_le P f p C hp hf hb
  refine ⟨fun om => (k om).toReal, hk, fun _ => ENNReal.toReal_nonneg, hnorm, ?_⟩
  filter_upwards [hfin, hlim, hgrowth] with om hfinite hmu hbound
  intro t
  rw [ENNReal.ofReal_toReal hfinite.ne]
  calc
    mu om (tests t) ≤ liminf (fun n => muN n om (tests t)) atTop := hmu t
    _ ≤ liminf (fun n => (scale t : ℝ≥0∞) * ‖f n om‖ₑ) atTop := by
      exact liminf_le_liminf (Filter.Eventually.of_forall (fun n => hbound n t))
    _ ≤ (scale t : ℝ≥0∞) * k om := by
      simpa only [limsup_const] using
        (ENNReal.liminf_mul_le (u := fun _ : ℕ => (scale t : ℝ≥0∞))
          (v := fun n => ‖f n om‖ₑ) (f := atTop)
          (Or.inr hfinite.ne) (Or.inl (by simpa only [limsup_const] using
            (ENNReal.coe_ne_top : (scale t : ℝ≥0∞) ≠ ⊤))))
    _ = k om * (scale t : ℝ≥0∞) := mul_comm _ _

end SubdiffusiveProcess


