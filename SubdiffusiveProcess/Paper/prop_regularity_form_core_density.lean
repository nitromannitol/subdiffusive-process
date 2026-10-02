import SubdiffusiveProcess.Paper.prop_regularity_collar_core
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.DirichletForm.All

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem prop_regularity_form_core_density
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
    (G : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (D : Submodule ℚ (DomainL2 (centeredCube z R hR)))
    [Countable D]
    (alpha eta t : ℝ)
    (halpha_gt : 1 / 2 < alpha) (halpha_lt : alpha < 1)
    (heta_pos : 0 < eta)
    (ht : (d : ℝ) - 1 < t)
    (heta_lt : 1 + eta < 2 * alpha)
    (rho : ℕ → ℝ) (hrho : ∀ k : ℕ, rho k = R / (10 * (3 : ℝ) ^ k))
    (hCollarCore : ∀ f : D, ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ k : ℕ,
      ∃ v : DomainL2 (centeredCube z R hR),
        E.toClosedForm.MemCoreOn
          (centeredCube z R hR : Set (SpatialCoordinates d)) v ∧
        E.toClosedForm.energyNormSq (G f.val - v) ≤
          Kf * ((rho k) ^ (t - (d : ℝ) + 1) +
            (rho k) ^ (2 * alpha - 1 - eta))) :
    ∀ f : D, ∀ ε : ℝ, 0 < ε →
      ∃ v : DomainL2 (centeredCube z R hR),
        E.toClosedForm.MemCoreOn
          (centeredCube z R hR : Set (SpatialCoordinates d)) v ∧
        E.toClosedForm.energyNormSq (G f.val - v) < ε := by
  have hp₁ : 0 < t - (d : ℝ) + 1 := by
    linarith
  have hp₂ : 0 < 2 * alpha - 1 - eta := by
    linarith
  have hpow : Tendsto (fun k : ℕ => (3 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hden : Tendsto (fun k : ℕ => (10 : ℝ) * (3 : ℝ) ^ k) atTop atTop := by
    exact hpow.const_mul_atTop (by norm_num)
  have hrho_lim : Tendsto rho atTop (𝓝 0) := by
    apply Tendsto.congr' (Eventually.of_forall (fun k => (hrho k).symm))
    exact hden.const_div_atTop R
  have hpow₁ : Tendsto (fun k : ℕ => (rho k) ^ (t - (d : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow hp₁.ne'] using
      (hrho_lim.rpow (tendsto_const_nhds : Tendsto (fun _ : ℕ => t - (d : ℝ) + 1) atTop
        (𝓝 (t - (d : ℝ) + 1))) (Or.inr hp₁))
  have hpow₂ : Tendsto (fun k : ℕ => (rho k) ^ (2 * alpha - 1 - eta)) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow hp₂.ne'] using
      (hrho_lim.rpow (tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * alpha - 1 - eta) atTop
        (𝓝 (2 * alpha - 1 - eta))) (Or.inr hp₂))
  have hsum : Tendsto
      (fun k : ℕ => (rho k) ^ (t - (d : ℝ) + 1) +
        (rho k) ^ (2 * alpha - 1 - eta)) atTop (𝓝 0) := by
    simpa only [add_zero] using hpow₁.add hpow₂
  intro f ε hε
  obtain ⟨Kf, hKf, hbound⟩ := hCollarCore f
  have hbound_lim : Tendsto
      (fun k : ℕ => Kf * ((rho k) ^ (t - (d : ℝ) + 1) +
        (rho k) ^ (2 * alpha - 1 - eta))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsum.const_mul Kf
  have hev : ∀ᶠ k : ℕ in atTop,
      Kf * ((rho k) ^ (t - (d : ℝ) + 1) +
        (rho k) ^ (2 * alpha - 1 - eta)) < ε :=
    hbound_lim.eventually (Iio_mem_nhds hε)
  obtain ⟨k, hk⟩ := hev.exists
  obtain ⟨v, hvcore, hvle⟩ := hbound k
  exact ⟨v, hvcore, hvle.trans_lt hk⟩

end Paper
