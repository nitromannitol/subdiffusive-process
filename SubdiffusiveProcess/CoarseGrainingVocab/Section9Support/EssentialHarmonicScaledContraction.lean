import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.EssentialHarmonicContraction
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.EssentialHarmonicScaling

/-! # Essential interval contraction on arbitrary cubes -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped Pointwise

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

private def essentialCastH1 {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    (u : H1Function U) : H1Function V := hUV ▸ u

private theorem essentialCastH1_toFun {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    (u : H1Function U) : (essentialCastH1 hUV u).toFun = u.toFun := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.aux_dedup_d263_essentialCastH1_toFun (d := d) (U := U) (V := V) (hUV := hUV) (u := u)

private theorem essentialCastH1_harmonic {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    {a : Vec d → ℝ} {u : H1Function U} (hu : IsWeaklyHarmonicOn a U u) :
    IsWeaklyHarmonicOn a V (essentialCastH1 hUV u) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.aux_dedup_d178_essentialCastH1_harmonic (d := d) (U := U) (V := V) (hUV := hUV) (a := a) (u := u) (hu := hu)

/-- Dilation preserves the contraction factor; only the cube size changes. -/
theorem exists_essential_harmonic_scaled_contraction {d : ℕ} (hd : 2 ≤ d) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      ∀ (a : Vec d → ℝ) (z : Vec d) (R : ℝ), 0 < R →
      (∀ᵐ x ∂volume.restrict (centeredAxisCube z R), 1 / 4 ≤ a x ∧ a x ≤ 4) →
      AEStronglyMeasurable a (volume.restrict (centeredAxisCube z R)) →
      ∀ u : H1Function (centeredAxisCube z R), IsWeaklyHarmonicOn a (centeredAxisCube z R) u →
      ∀ l H : ℝ, l ≤ H →
      (∀ᵐ x ∂volume.restrict (centeredAxisCube z R), l ≤ u.toFun x ∧ u.toFun x ≤ H) →
      ∃ l' H' : ℝ, l ≤ l' ∧ H' ≤ H ∧ l' ≤ H' ∧ H' - l' ≤ t * (H - l) ∧
        ∀ᵐ x ∂volume.restrict (centeredAxisCube z (R / 8)),
          l' ≤ u.toFun x ∧ u.toFun x ≤ H' := by
  obtain ⟨t, ht, ht1, hcontract⟩ := exists_essential_harmonic_unit_contraction hd
  refine ⟨t, ht, ht1, ?_⟩
  intro a z R hR hab ha u hu l H hlH hub
  let U : Set (Vec d) := centeredAxisCube (R⁻¹ • z) 1
  have hdom : R • U = centeredAxisCube z R := by
    rw [harmonic_smul_centeredAxisCube _ _ hR]
    simp only [smul_inv_smul₀ hR.ne', mul_one]
  let u' := essentialCastH1 hdom.symm u
  have hu' : IsWeaklyHarmonicOn a (R • U) u' := essentialCastH1_harmonic hdom.symm hu
  have hband := harmonic_ae_smul hR (hdom.symm ▸ hab)
  have hub' : ∀ᵐ y ∂volume.restrict (R • U), l ≤ u'.toFun y ∧ u'.toFun y ≤ H := by
    simp only [u', essentialCastH1_toFun]
    exact hdom.symm ▸ hub
  have hbounded := harmonic_ae_smul hR hub'
  have haMap : AEStronglyMeasurable a (Measure.map (fun y : Vec d => R • y) (volume.restrict U)) := by
    rw [map_smul_volume_restrict hR, hdom]
    exact ha.smul_measure _
  have hameas := haMap.comp_aemeasurable (measurable_const_smul R).aemeasurable
  obtain ⟨l', H', hl', hH', hlH', hwidth, hinterval⟩ :=
    hcontract (fun y => a (R • y)) (R⁻¹ • z) hband hameas (u'.unscale hR)
      (harmonic_isWeaklyHarmonic_unscale hR u' hu') l H hlH hbounded
  refine ⟨l', H', hl', hH', hlH', hwidth, ?_⟩
  simp only [H1Function.unscale_toFun, u', essentialCastH1_toFun] at hinterval
  have hinner : R • centeredAxisCube (R⁻¹ • z) (1 / 8) = centeredAxisCube z (R / 8) := by
    rw [harmonic_smul_centeredAxisCube _ _ hR]
    simp only [smul_inv_smul₀ hR.ne', mul_one_div]
  have hpushed := essential_ae_smul_image hR
    (U := centeredAxisCube (R⁻¹ • z) (1 / 8))
    (P := fun y => l' ≤ u.toFun y ∧ u.toFun y ≤ H') hinterval
  rwa [hinner] at hpushed

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
