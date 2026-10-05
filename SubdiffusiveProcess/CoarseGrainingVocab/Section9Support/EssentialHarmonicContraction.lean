module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.EssentialHarmonicInterval

@[expose] public section

/-! # Contraction of essential value intervals -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.Section9 (centeredAxisCube)

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A bounded weak solution takes values in an interval whose width
contracts by a dimensional factor on the eighth cube. -/
theorem exists_essential_harmonic_unit_contraction {d : ℕ} (hd : 2 ≤ d) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      ∀ (a : Vec d → ℝ) (z : Vec d),
      (∀ᵐ x ∂volume.restrict (centeredAxisCube z 1), 1 / 4 ≤ a x ∧ a x ≤ 4) →
      AEStronglyMeasurable a (volume.restrict (centeredAxisCube z 1)) →
      ∀ u : H1Function (centeredAxisCube z 1), IsWeaklyHarmonicOn a (centeredAxisCube z 1) u →
      ∀ l H : ℝ, l ≤ H →
      (∀ᵐ x ∂volume.restrict (centeredAxisCube z 1), l ≤ u.toFun x ∧ u.toFun x ≤ H) →
      ∃ l' H' : ℝ, l ≤ l' ∧ H' ≤ H ∧ l' ≤ H' ∧ H' - l' ≤ t * (H - l) ∧
        ∀ᵐ x ∂volume.restrict (centeredAxisCube z (1 / 8)),
          l' ≤ u.toFun x ∧ u.toFun x ≤ H' := by
  obtain ⟨k, hk, hk1, hreduce⟩ := exists_essential_harmonic_interval_reduction hd
  refine ⟨1 - k, by linarith, by linarith, ?_⟩
  intro a z hab ha u hu l H hlH hub
  have hsub : centeredAxisCube z (1 / 8) ⊆ centeredAxisCube z 1 := centeredAxisCube_mono (by norm_num)
  have hsmall := ae_restrict_of_ae_restrict_of_subset hsub hub
  rcases hlH.eq_or_lt with heq | hlt
  · refine ⟨l, H, le_rfl, le_rfl, hlH, ?_, hsmall⟩
    rw [heq]
    simp
  let : IsFiniteMeasure (volume.restrict (centeredAxisCube z 1)) :=
    (isOpenBoundedConvexDomain_axisCube (fun i => z i - 1 / 2) 1).isFiniteMeasure_restrict_volume
  let v := ((H - l)⁻¹ • u).addConst (-l / (H - l))
  have hv := essential_harmonic_affine u hu (H - l)⁻¹ (-l / (H - l))
  have hvf : v.toFun = fun x => (u.toFun x - l) / (H - l) := by
    funext x
    change (H - l)⁻¹ * u.toFun x + -l / (H - l) = _
    ring
  have hv01 : ∀ᵐ x ∂volume.restrict (centeredAxisCube z 1), 0 ≤ v.toFun x ∧ v.toFun x ≤ 1 := by
    filter_upwards [hub] with x hx
    rw [hvf]
    exact ⟨div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hlt).le,
      (div_le_one (sub_pos.mpr hlt)).mpr (by linarith [hx.2])⟩
  rcases hreduce a z hab ha v hv hv01 with hlo | hhi
  · refine ⟨l + k * (H - l), H, by nlinarith, le_rfl, ?_, le_of_eq (by ring), ?_⟩
    · nlinarith
    · filter_upwards [hsmall, hlo] with x hx hxl
      rw [hvf] at hxl
      have he := (le_div_iff₀ (sub_pos.mpr hlt)).mp hxl
      exact ⟨by linarith, hx.2⟩
  · refine ⟨l, H - k * (H - l), le_rfl, by nlinarith, by nlinarith, le_of_eq (by ring), ?_⟩
    filter_upwards [hsmall, hhi] with x hx hxh
    rw [hvf] at hxh
    have he := (div_le_iff₀ (sub_pos.mpr hlt)).mp hxh
    exact ⟨hx.1, by nlinarith⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
