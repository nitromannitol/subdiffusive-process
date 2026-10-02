import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousC1
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory Filter Set Topology
open scoped ContDiff NNReal

noncomputable section
namespace DirichletForm.FOTConstruction

/-- A compactly supported C¹ modification agrees with the original function
on any prescribed bounded interval. -/
theorem assembly_c1_modification (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    (hΦ0 : Φ 0 = 0) (R : ℝ) (hR : 0 < R) :
    ∃ Ψ : ℝ → ℝ, ContDiff ℝ 1 Ψ ∧ Ψ 0 = 0 ∧
      (∃ L : ℝ≥0, LipschitzWith L Ψ) ∧
      ∀ s : ℝ, |s| < R → Ψ =ᶠ[𝓝 s] Φ := by
  let β : ContDiffBump (0 : ℝ) := ⟨R, R + 1, hR, by linarith⟩
  let Ψ : ℝ → ℝ := fun s => β s * Φ s
  have hΨ : ContDiff ℝ 1 Ψ := β.contDiff.mul hΦ
  refine ⟨Ψ, hΨ, ?_, ?_, ?_⟩
  · simp only [Ψ, hΦ0, mul_zero]
  · exact ContDiff.lipschitzWith_of_hasCompactSupport
      (β.hasCompactSupport.mul_right) hΨ le_rfl
  · intro s hs
    have hsB : s ∈ Metric.ball (0 : ℝ) R := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hs
    filter_upwards [β.eventuallyEq_one_of_mem_ball hsB] with t ht
    simp only [Ψ, ht, Pi.one_apply, one_mul]

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] [SecondCountableTopology X] {m : Measure X}

/-- The bounded C¹ representative rule, expressed as an equality of measures. -/
theorem EnergyFamily.continuous_lipschitz_density
    {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) (q : RepresentativeFamily Γ)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) {uc : X → ℝ}
    (huc : Continuous uc) (huae : ⇑u =ᵐ[m] uc)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) {L : ℝ≥0}
    (hL : LipschitzWith L Φ) (hΦ0 : Φ 0 = 0)
    {w : Lp ℝ 2 m} (hw : w ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => Φ (uc x)) :
    Γ.measure w = (Γ.measure u).withDensity
      (fun x => ENNReal.ofReal ((deriv Φ (uc x)) ^ 2)) := by
  letI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu⟩
  have hagree := q.continuous_agree u hu uc huc huae u hu
  have hwrep : ⇑w =ᵐ[m] fun x => Φ (q.rep u hu x) := by
    filter_upwards [hwae, q.ae_rep u hu, huae] with x hx hq hc
    rw [hx, ← hc, hq]
  have hmeas : Measurable (fun x => (deriv Φ (uc x)) ^ 2) :=
    (hΦ.continuous_deriv (by norm_num)).measurable.comp huc.measurable |>.pow_const 2
  have hint : Integrable (fun x => (deriv Φ (uc x)) ^ 2) (Γ.measure u) := by
    apply (integrable_const ((L : ℝ) ^ 2)).mono' hmeas.aestronglyMeasurable
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by
      simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz hL) 2
  apply Measure.ext
  intro B hB
  rw [withDensity_apply _ hB,
    ← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (Eventually.of_forall fun x => sq_nonneg _)]
  have hchain := Γ.quasiContinuous_chain h q hu Φ hΦ hL hΦ0 hw hwrep hB
  have hi : (∫ x in B, (deriv Φ (q.rep u hu x)) ^ 2 ∂Γ.measure u) =
      ∫ x in B, (deriv Φ (uc x)) ^ 2 ∂Γ.measure u := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hagree] with x hx
    rw [hx]
  rw [← hi, ← hchain]
  exact (ENNReal.ofReal_toReal (lt_of_le_of_lt
    (measure_mono (subset_univ B)) (Γ.finite w hw)).ne).symm

end DirichletForm.FOTConstruction
