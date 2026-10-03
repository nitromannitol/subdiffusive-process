module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerHarmonic
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Small L2 error from a positive profile and a bounded harmonic correction give an interior lower bound. -/
theorem goodCube_lower_of_l2_and_harmonic_correction
    {d : ℕ} {V W U : Set (Vec d)} (hV : MeasurableSet V)
    (hVW : V ⊆ W) (hWU : W ⊆ U)
    (f g v : Vec d → ℝ) {a b E eta eps : ℝ}
    (hb : 0 < b) (hE : 0 ≤ E) (heta : 0 ≤ eta) (heps : 0 ≤ eps)
    (hf : ∀ x ∈ W, 0 ≤ f x ∧ f x ≤ E)
    (hv : ∀ x ∈ W, |v x| ≤ eta)
    (hcontract : oscillation V (fun x => f x - v x) ≤
      ENNReal.ofReal eps * oscillation W (fun x => f x - v x))
    (hg : ∀ᵐ x ∂volume.restrict V, a ≤ g x)
    (hdistance : eLpNorm (fun x => f x - g x) 2 (volume.restrict U) <
      ENNReal.ofReal b * volume V ^ (1 / 2 : ℝ)) :
    ∀ x ∈ V, a - b - (eps * (E + 2 * eta) + 2 * eta) ≤ f x := by
  have hE2 : 0 ≤ E + 2 * eta := by linarith
  -- Step 1: there exists a witness point in V where f exceeds a - b.
  have hyex : ∃ y ∈ V, a - b < f y := by
    by_contra hcon
    push_neg at hcon
    have hae : ∀ᵐ x ∂(volume.restrict V),
        ‖(fun _ : Vec d => (b : ℝ)) x‖ₑ ≤ ‖(fun x : Vec d => f x - g x) x‖ₑ := by
      filter_upwards [hg, ae_restrict_mem hV] with x hx hxV
      show ‖(b : ℝ)‖ₑ ≤ ‖(f x - g x : ℝ)‖ₑ
      have hfx : f x ≤ a - b := hcon x hxV
      have h1 : ‖(f x - g x : ℝ)‖ₑ = ENNReal.ofReal (g x - f x) := by
        have habs : |f x - g x| = g x - f x := by
          rw [abs_of_nonpos (show f x - g x ≤ 0 by linarith)]
          ring
        rw [Real.enorm_eq_ofReal_abs, habs]
      rw [h1, Real.enorm_eq_ofReal hb.le]
      exact ENNReal.ofReal_le_ofReal (by linarith : b ≤ g x - f x)
    have hmeas : (volume.restrict V) Set.univ = volume V := by
      exact Measure.restrict_apply_univ V
    have h2exp : ENNReal.toReal (2 : ℝ≥0∞) = 2 := by simp
    have key : eLpNorm (fun _ : Vec d => (b : ℝ)) 2 (volume.restrict V)
        = ‖(b : ℝ)‖ₑ * (volume.restrict V) Set.univ ^ (1 / ENNReal.toReal (2 : ℝ≥0∞)) :=
      eLpNorm_const' _ (by simp) (by simp)
    have hmono : ENNReal.ofReal b * volume V ^ (1 / 2 : ℝ)
        ≤ eLpNorm (fun x : Vec d => f x - g x) 2 (volume.restrict U) := by
      calc ENNReal.ofReal b * volume V ^ (1 / 2 : ℝ)
          = eLpNorm (fun _ : Vec d => (b : ℝ)) 2 (volume.restrict V) := by
            rw [key, Real.enorm_eq_ofReal hb.le, hmeas, h2exp]
        _ ≤ eLpNorm (fun x : Vec d => f x - g x) 2 (volume.restrict V) :=
            eLpNorm_mono_ae' aestronglyMeasurable_const hae
        _ ≤ eLpNorm (fun x : Vec d => f x - g x) 2 (volume.restrict U) :=
            eLpNorm_mono_measure _ (Measure.restrict_mono (hVW.trans hWU) le_rfl)
    exact absurd (lt_of_le_of_lt hmono hdistance) (lt_irrefl _)
  -- Step 2: the oscillation of f - v on W is bounded by E + 2 * eta.
  have hoscW : oscillation W (fun x => f x - v x) ≤ ENNReal.ofReal (E + 2 * eta) := by
    refine oscillation_le_ofReal ?_
    intro x hx y hy
    obtain ⟨hfx0, hfxE⟩ := hf x hx
    obtain ⟨hfy0, hfyE⟩ := hf y hy
    have hvx := hv x hx
    have hvy := hv y hy
    have h1 : |f x - f y| ≤ E := by
      rw [abs_le]
      constructor <;> linarith
    have h2 : |v x - v y| ≤ 2 * eta := by
      have h3 := abs_sub_le (v x) 0 (v y)
      simp only [sub_zero, zero_sub, abs_neg] at h3
      linarith
    have heq : (f x - v x) - (f y - v y) = (f x - f y) - (v x - v y) := by ring
    rw [heq]
    calc |(f x - f y) - (v x - v y)|
        ≤ |f x - f y| + |v x - v y| := by
          exact abs_sub _ _
      _ ≤ E + 2 * eta := by linarith
  -- Step 3: contraction gives the oscillation bound on V.
  have hoscV : oscillation V (fun x => f x - v x) ≤
      ENNReal.ofReal (eps * (E + 2 * eta)) := by
    calc oscillation V (fun x => f x - v x)
        ≤ ENNReal.ofReal eps * oscillation W (fun x => f x - v x) := hcontract
      _ ≤ ENNReal.ofReal eps * ENNReal.ofReal (E + 2 * eta) :=
          mul_le_mul_right hoscW _
      _ = ENNReal.ofReal (eps * (E + 2 * eta)) := (ENNReal.ofReal_mul heps).symm
  -- Step 4: propagate from the witness point to every point of V.
  obtain ⟨y, hyV, hfy⟩ := hyex
  have hbound : 0 ≤ eps * (E + 2 * eta) := mul_nonneg heps hE2
  intro x hx
  have hdiff : |(f x - v x) - (f y - v y)| ≤ eps * (E + 2 * eta) :=
    abs_sub_le_of_oscillation_le hbound hoscV hx hyV
  have hvx := hv x (hVW hx)
  have hvy := hv y (hVW hyV)
  have h2 : |f x - f y| ≤ eps * (E + 2 * eta) + 2 * eta := by
    have hvy2 : |v x - v y| ≤ 2 * eta := by
      have h3 := abs_sub_le (v x) 0 (v y)
      simp only [sub_zero, zero_sub, abs_neg] at h3
      linarith
    have key : f x - f y = ((f x - v x) - (f y - v y)) + (v x - v y) := by ring
    calc |f x - f y|
        = |((f x - v x) - (f y - v y)) + (v x - v y)| := by rw [key]
      _ ≤ |(f x - v x) - (f y - v y)| + |v x - v y| := abs_add_le _ _
      _ ≤ eps * (E + 2 * eta) + 2 * eta := by linarith
  have h4 : f y - (eps * (E + 2 * eta) + 2 * eta) ≤ f x := by
    obtain ⟨h5, h6⟩ := abs_le.1 h2
    linarith
  linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
