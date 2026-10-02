import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.EssentialHarmonicScaledContraction

/-! # Iteration of essential intervals on shrinking cubes -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.Section9 (centeredAxisCube)

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The value intervals shrink geometrically on concentric cubes. The
initial qualitative bound enters only the interval width. -/
theorem exists_essential_harmonic_shrinking_intervals {d : ℕ} (hd : 2 ≤ d) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      ∀ (a : Vec d → ℝ) (z : Vec d) (R : ℝ), 0 < R →
      (∀ᵐ x ∂volume.restrict (centeredAxisCube z R), 1 / 4 ≤ a x ∧ a x ≤ 4) →
      AEStronglyMeasurable a (volume.restrict (centeredAxisCube z R)) →
      ∀ u : H1Function (centeredAxisCube z R), IsWeaklyHarmonicOn a (centeredAxisCube z R) u →
      ∀ M : ℝ, 0 ≤ M →
      (∀ᵐ x ∂volume.restrict (centeredAxisCube z R), |u.toFun x| ≤ M) →
      ∀ n : ℕ, ∃ l H : ℝ, l ≤ H ∧ H - l ≤ t ^ n * (2 * M) ∧
        ∀ᵐ x ∂volume.restrict (centeredAxisCube z (R / 8 ^ n)),
          l ≤ u.toFun x ∧ u.toFun x ≤ H := by
  obtain ⟨t, ht, ht1, hcontract⟩ := exists_essential_harmonic_scaled_contraction hd
  refine ⟨t, ht, ht1, ?_⟩
  intro a z R hR hab ha u hu M hM hub n
  induction n with
  | zero =>
    refine ⟨-M, M, by linarith, by simp; linarith, ?_⟩
    simpa only [pow_zero, div_one, abs_le] using hub
  | succ n ih =>
    obtain ⟨l, H, hlH, hwidth, hbound⟩ := ih
    have hR' : 0 < R / 8 ^ n := by positivity
    have hle : R / 8 ^ n ≤ R :=
      (div_le_self hR.le (one_le_pow₀ (by norm_num))).trans le_rfl
    have hsub : centeredAxisCube z (R / 8 ^ n) ⊆ centeredAxisCube z R := centeredAxisCube_mono hle
    let v := u.restrict (isOpen_axisCube (fun i => z i - (R / 8 ^ n) / 2) (R / 8 ^ n)) hsub
    have hv := SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.isWeaklyHarmonicOn_restrict
      (isOpen_axisCube (fun i => z i - R / 2) R) (isOpen_axisCube (fun i => z i - (R / 8 ^ n) / 2) (R / 8 ^ n)) hsub hu
    obtain ⟨l', H', _, _, hlH', hwidth', hbound'⟩ :=
      hcontract a z (R / 8 ^ n) hR' (ae_restrict_of_ae_restrict_of_subset hsub hab)
        (ha.mono_set hsub) v hv l H hlH hbound
    refine ⟨l', H', hlH', ?_, ?_⟩
    · calc
        H' - l' ≤ t * (H - l) := hwidth'
        _ ≤ t * (t ^ n * (2 * M)) := mul_le_mul_of_nonneg_left hwidth ht.le
        _ = t ^ (n + 1) * (2 * M) := by rw [pow_succ]; ring
    · have heq : R / 8 ^ n / 8 = R / 8 ^ (n + 1) := by rw [pow_succ, div_div]
      dsimp only [v, H1Function.restrict] at hbound'
      rwa [heq] at hbound'

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
