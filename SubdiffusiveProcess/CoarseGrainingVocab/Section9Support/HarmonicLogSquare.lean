import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicLogControl

/-!
# Anchored logarithmic square bound

For a harmonic function with values in `[0,1]`, a half-measure set above
`1/2` gives a normalized logarithmic square bound uniform in the positive
regularization. The subsequent level-set argument will produce the
half-measure alternative by choosing the function or its complement.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The full logarithmic square bound has only a dimensional constant. -/
theorem exists_harmonic_unit_log_square (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Vec d → ℝ) (z : Vec d),
      (∀ x ∈ centeredAxisCube z 1, 1 / 4 ≤ a x ∧ a x ≤ 4) →
      AEStronglyMeasurable a (volume.restrict (centeredAxisCube z 1)) →
      ∀ h : Vec d → ℝ, WeakHarmonic a (centeredAxisCube z 1) h →
      (∀ x ∈ centeredAxisCube z 1, 0 ≤ h x ∧ h x ≤ 1) →
      ∀ E : Set (Vec d),
      (volume (centeredAxisCube z (1 / 2))).toReal / 2 ≤
        ((volume.restrict (centeredAxisCube z (1 / 2))) E).toReal →
      (∀ᵐ x ∂(volume.restrict (centeredAxisCube z (1 / 2))).restrict E, 1 / 2 ≤ h x) →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 / 4 →
      ∃ u : H1Function (centeredAxisCube z (1 / 2)),
        (∀ᵐ x ∂volume.restrict (centeredAxisCube z (1 / 2)),
          u.toFun x = Real.log (h x + epsilon)) ∧
        (∫ x in centeredAxisCube z (1 / 2), u.toFun x ^ 2) ≤
          C * (volume (centeredAxisCube z (1 / 2))).toReal := by
  obtain ⟨E0, hE0, henergy⟩ := exists_harmonic_unit_log_energy d
  let P : ℝ := unitMeanZeroPoincareConst d * (d : ℝ)
  let M : ℝ := (1 / 2 : ℝ) ^ d
  have hM : 0 < M := pow_pos (by norm_num) d
  let C : ℝ := (10 * P ^ 2 * E0 + 8 * (Real.log 2) ^ 2 * M) / M + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro a z hab ha h hh hh01 E hhalf hgood epsilon hepsilon hepsilon1
  obtain ⟨u, hu, hgrad⟩ := henergy a z hab ha h hh (fun x hx => (hh01 x hx).1) epsilon hepsilon
  refine ⟨u, hu, ?_⟩
  have hBsub : centeredAxisCube z (1 / 2) ⊆ centeredAxisCube z 1 := centeredAxisCube_mono (by norm_num)
  have hgoodlog : ∀ᵐ x ∂(volume.restrict (centeredAxisCube z (1 / 2))).restrict E,
      |u.toFun x| ≤ Real.log 2 := by
    have hue := hu.filter_mono (ae_mono (Measure.restrict_le_self (s := E)))
    have hBe := (ae_restrict_mem (isOpen_axisCube _ _).measurableSet).filter_mono
      (ae_mono (Measure.restrict_le_self (μ := volume.restrict (centeredAxisCube z (1 / 2))) (s := E)))
    filter_upwards [hue, hgood, hBe] with x hux hx hxB
    rw [hux]
    apply harmonic_abs_log_le_log_two
    · linarith
    · linarith [(hh01 x (hBsub hxB)).2]
  have hbound := harmonic_sq_le_gradient_of_half_measure z (by norm_num : (0 : ℝ) < 1 / 2)
    u hhalf hgoodlog
  have hvol : (volume (centeredAxisCube z (1 / 2))).toReal = M :=
    SubdiffusiveProcess.Section9.volume_centeredAxisCube_toReal z (by norm_num)
  rw [hvol] at hbound ⊢
  have hnonneg : 0 ≤ ∫ x in centeredAxisCube z (1 / 2), vecNormSq (u.grad x) :=
    integral_nonneg fun x => vecNormSq_nonneg _
  have hprice : 10 * P ^ 2 * (1 / 2 : ℝ) ^ 2 *
      (∫ x in centeredAxisCube z (1 / 2), vecNormSq (u.grad x)) ≤ 10 * P ^ 2 * E0 := by
    have hm := mul_le_mul_of_nonneg_left hgrad (by positivity : 0 ≤ 10 * P ^ 2)
    have hz := mul_nonneg (sq_nonneg P) hnonneg
    nlinarith only [hm, hz]
  have hCM : C * M = 10 * P ^ 2 * E0 + 8 * (Real.log 2) ^ 2 * M + M := by
    dsimp only [C]
    field_simp
  rw [hCM]
  change (∫ x in centeredAxisCube z (1 / 2), u.toFun x ^ 2) ≤
    10 * P ^ 2 * (1 / 2 : ℝ) ^ 2 *
      (∫ x in centeredAxisCube z (1 / 2), vecNormSq (u.grad x)) +
        8 * (Real.log 2) ^ 2 * M at hbound
  linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
