module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalTorsionSurvivalArithmetic

@[expose] public section

/-! Probability bounds obtained by splitting an integral at a survival event. -/

set_option autoImplicit false

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

theorem localTorsion_integral_restart {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {tau f : Omega → ℝ≥0∞}
    {B : Set Omega} (hB : MeasurableSet B) {t M : ℝ≥0∞}
    (hpoint : ∀ w, tau w ≤ t + B.indicator f w)
    (hrest : ∫⁻ w in B, f w ∂mu ≤ M * mu B) :
    ∫⁻ w, tau w ∂mu ≤ t + M * mu B := by
  calc ∫⁻ w, tau w ∂mu
      ≤ ∫⁻ w, t + B.indicator f w ∂mu := lintegral_mono hpoint
    _ = t + ∫⁻ w in B, f w ∂mu := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ,
          mul_one, lintegral_indicator hB]
    _ ≤ t + M * mu B := by gcongr

theorem localTorsion_indicator_bound {Omega : Type*} {tau f : Omega → ℝ≥0∞}
    {t : ℝ≥0∞} (hshift : ∀ w, tau w ≤ t + f w) (w : Omega) :
    tau w ≤ t + {v | t < tau v}.indicator f w := by
  by_cases hw : w ∈ {v : Omega | t < tau v}
  · rw [Set.indicator_of_mem (s := {v : Omega | t < tau v}) (a := w) hw f]
    exact hshift w
  · rw [Set.indicator_of_notMem (s := {v : Omega | t < tau v}) (a := w) hw f, add_zero]
    exact le_of_not_gt hw

theorem localTorsion_restricted_integral {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {B : Set Omega} (hB : MeasurableSet B)
    {f : Omega → ℝ≥0∞} {C : ℝ≥0∞} (hC : ∀ w ∈ B, f w ≤ C) :
    ∫⁻ w in B, f w ∂mu ≤ C * mu B := by
  calc ∫⁻ w in B, f w ∂mu ≤ ∫⁻ w in B, C ∂mu :=
      lintegral_mono_ae (by
        filter_upwards [ae_restrict_mem hB] with w hw
        exact hC w hw)
    _ = C * (mu.restrict B) univ := by rw [lintegral_const]
    _ = C * mu B := by rw [Measure.restrict_apply_univ]

theorem localTorsion_probability_finite {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (B : Set Omega) :
    mu B ≤ 1 ∧ mu B ≠ ∞ := by
  have h : mu B ≤ 1 := (measure_mono (Set.subset_univ B)).trans_eq measure_univ
  exact ⟨h, ne_of_lt (lt_of_le_of_lt h ENNReal.one_lt_top)⟩

theorem localTorsion_complement_real {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {B : Set Omega} (hB : MeasurableSet B) :
    (mu B).toReal + (mu Bᶜ).toReal = 1 := by
  have hp := (localTorsion_probability_finite mu B).2
  have hq := (localTorsion_probability_finite mu Bᶜ).2
  have hs : mu B + mu Bᶜ = 1 := (measure_add_measure_compl hB).trans measure_univ
  have hr := congrArg ENNReal.toReal hs
  simpa only [ENNReal.toReal_add hp hq, ENNReal.toReal_one] using hr

theorem localTorsion_two_piece_integral {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {B : Set Omega} (hB : MeasurableSet B) {f : Omega → ℝ≥0∞}
    {e : ℝ≥0∞} (hBf : ∀ w ∈ B, f w ≤ e) (hf : ∀ w, f w ≤ 1) :
    ∫⁻ w, f w ∂mu ≤ e * mu B + mu Bᶜ := by
  rw [← lintegral_add_compl f hB]
  exact add_le_add (localTorsion_restricted_integral mu hB hBf)
    (by simpa only [one_mul] using localTorsion_restricted_integral mu hB.compl (fun w _ => hf w))

theorem localTorsion_weighted_bound {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {B : Set Omega} (hB : MeasurableSet B)
    {a e : ℝ} (ha : 0 ≤ a) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hprob : ENNReal.ofReal a ≤ mu B) :
    ENNReal.ofReal e * mu B + mu Bᶜ ≤ ENNReal.ofReal (1 - a * (1 - e)) := by
  have hp : mu B ≠ ∞ := (localTorsion_probability_finite mu B).2
  have hq : mu Bᶜ ≠ ∞ := (localTorsion_probability_finite mu Bᶜ).2
  rw [localTorsion_weighted_ofReal hp hq he0]
  apply ENNReal.ofReal_le_ofReal
  exact localTorsion_laplace_weights (localTorsion_probability_real ha hp hprob)
    (localTorsion_complement_real mu hB) he1

theorem localTorsion_survival_probability {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (B : Set Omega)
    {kappa A F : ℝ} (hk : 0 ≤ kappa) (hA : 0 < A) (hF : 0 < F)
    (h : ENNReal.ofReal (kappa * F) ≤ ENNReal.ofReal (kappa * F / 2) +
      ENNReal.ofReal (A * F) * mu B) : ENNReal.ofReal (kappa / (2 * A)) ≤ mu B := by
  have hp := (localTorsion_probability_finite mu B).2
  have hh : kappa * F ≤ kappa * F / 2 + A * F * (mu B).toReal :=
    localTorsion_toReal_bound (show 0 ≤ kappa * F by positivity)
      (show 0 ≤ kappa * F / 2 by positivity)
      (show 0 ≤ A * F by positivity) hp h
  exact localTorsion_ofReal_bound hp (localTorsion_probability_algebra hA hF hh)

theorem localTorsion_survival_mono {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (tau : Omega → ℝ≥0∞) {t c : ℝ≥0∞}
    (h : c ≤ mu {w | t < tau w}) : c ≤ mu {w | t ≤ tau w} := by
  apply h.trans (measure_mono ?_)
  intro w hw
  change t < tau w at hw
  change t ≤ tau w
  exact hw.le

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
