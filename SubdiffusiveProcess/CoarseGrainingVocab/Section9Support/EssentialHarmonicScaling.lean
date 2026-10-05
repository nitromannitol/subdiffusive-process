module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.EssentialHarmonicBoundedness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicScaledBoundedness

@[expose] public section

/-! # Dilation of the essential Moser endpoint -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Filter Set
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped Pointwise ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

public def essentialCastH1 {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    (u : H1Function U) : H1Function V := hUV ▸ u

theorem aux_dedup_d263_essentialCastH1_toFun {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    (u : H1Function U) : (essentialCastH1 hUV u).toFun = u.toFun := by cases hUV; rfl

private theorem essentialCastH1_toFun {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    (u : H1Function U) : (essentialCastH1 hUV u).toFun = u.toFun := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.aux_dedup_d263_essentialCastH1_toFun (d := d) (U := U) (V := V) (hUV := hUV) (u := u)

theorem aux_dedup_d178_essentialCastH1_harmonic {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    {a : Vec d → ℝ} {u : H1Function U} (hu : IsWeaklyHarmonicOn a U u) :
    IsWeaklyHarmonicOn a V (essentialCastH1 hUV u) := by cases hUV; exact hu

private theorem essentialCastH1_harmonic {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    {a : Vec d → ℝ} {u : H1Function U} (hu : IsWeaklyHarmonicOn a U u) :
    IsWeaklyHarmonicOn a V (essentialCastH1 hUV u) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.aux_dedup_d178_essentialCastH1_harmonic (d := d) (U := U) (V := V) (hUV := hUV) (a := a) (u := u) (hu := hu)

/-- Almost-everywhere assertions push forward under positive dilation. -/
theorem essential_ae_smul_image {d : ℕ} {U : Set (Vec d)} {r : ℝ} (hr : 0 < r)
    {P : Vec d → Prop} (hP : ∀ᵐ x ∂volume.restrict U, P (r • x)) :
    ∀ᵐ x ∂volume.restrict (r • U), P x := by
  have hdom : r⁻¹ • (r • U) = U := by rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have h := harmonic_ae_smul (inv_pos.mpr hr) (hdom.symm ▸ hP)
  simpa only [smul_inv_smul₀ hr.ne'] using h

/-- The bounded H¹ weak solution has the scale-invariant essential upper estimate. -/
theorem exists_essential_harmonic_scaled_positive_bound {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Vec d → ℝ) (z : Vec d) (R : ℝ), 0 < R →
      (∀ᵐ x ∂volume.restrict (centeredAxisCube z R), 1 / 4 ≤ a x ∧ a x ≤ 4) →
      AEStronglyMeasurable a (volume.restrict (centeredAxisCube z R)) →
      ∀ u : H1Function (centeredAxisCube z R), IsWeaklyHarmonicOn a (centeredAxisCube z R) u →
      ∀ M : ℝ, 0 ≤ M → (∀ᵐ x ∂volume.restrict (centeredAxisCube z R), |u.toFun x| ≤ M) →
      ∀ᵐ x ∂volume.restrict (centeredAxisCube z (R / 4)),
        ENNReal.ofReal (max (u.toFun x) 0) ≤
          ENNReal.ofReal C * volume (centeredAxisCube z R) ^ (-(1 / 2) : ℝ) *
            eLpNorm (fun y => max (u.toFun y) 0) 2 (volume.restrict (centeredAxisCube z R)) := by
  obtain ⟨C, hC, hbound⟩ := exists_essential_harmonic_positive_bound hd
  refine ⟨C, hC, ?_⟩
  intro a z R hR hab ha u hu M hM hub
  let U : Set (Vec d) := centeredAxisCube (R⁻¹ • z) 1
  have hdom : R • U = centeredAxisCube z R := by
    rw [harmonic_smul_centeredAxisCube _ _ hR]
    simp only [smul_inv_smul₀ hR.ne', mul_one]
  let u' := essentialCastH1 hdom.symm u
  have hu' : IsWeaklyHarmonicOn a (R • U) u' := essentialCastH1_harmonic hdom.symm hu
  have hband := harmonic_ae_smul hR (hdom.symm ▸ hab)
  have hub' : ∀ᵐ y ∂volume.restrict (R • U), |u'.toFun y| ≤ M := by
    simp only [u', essentialCastH1_toFun]
    exact hdom.symm ▸ hub
  have hbounded := harmonic_ae_smul hR hub'
  have haMap : AEStronglyMeasurable a (Measure.map (fun y : Vec d => R • y) (volume.restrict U)) := by
    rw [map_smul_volume_restrict hR, hdom]
    exact ha.smul_measure _
  have hameas := haMap.comp_aemeasurable (measurable_const_smul R).aemeasurable
  have hresult := hbound (fun y => a (R • y)) (R⁻¹ • z) hband hameas (u'.unscale hR)
    (harmonic_isWeaklyHarmonic_unscale hR u' hu') M hM hbounded
  have hnorm := harmonic_eLpNorm_positive_smul hR u'.memL2.aestronglyMeasurable
  simp only [H1Function.unscale_toFun] at hresult
  rw [hnorm] at hresult
  simp only [u', essentialCastH1_toFun] at hresult
  rw [hdom] at hresult
  have hinner : R • centeredAxisCube (R⁻¹ • z) (1 / 4) = centeredAxisCube z (R / 4) := by
    rw [harmonic_smul_centeredAxisCube _ _ hR]
    simp only [smul_inv_smul₀ hR.ne', mul_one_div]
  have hpushed := essential_ae_smul_image hR
    (U := centeredAxisCube (R⁻¹ • z) (1 / 4))
    (P := fun y => ENNReal.ofReal (max (u.toFun y) 0) ≤
      ENNReal.ofReal C * (ENNReal.ofReal (R ^ d) ^ (-(1 / 2) : ℝ) *
        eLpNorm (fun x => max (u.toFun x) 0) 2 (volume.restrict (centeredAxisCube z R)))) hresult
  rw [hinner] at hpushed
  rw [volume_centeredAxisCube_eq z hR.le]
  simpa only [mul_assoc] using hpushed

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
