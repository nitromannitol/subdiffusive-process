module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicRatioBoundedness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicWeakScaling

@[expose] public section

/-!
# Scaled positive-part bounds with local coefficient hypotheses

The coefficient band is required only on the cube in question. Dilation
then gives the exact volume normalization on arbitrary positive-side cubes.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Filter Set
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped Pointwise ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The local weak equation depends only on the coefficient almost everywhere. -/
theorem harmonic_weakHarmonic_coefficient_congr_ae {d : ℕ} {U : Set (Vec d)}
    {a b h : Vec d → ℝ} (hh : WeakHarmonic a U h)
    (hab : a =ᵐ[volume.restrict U] b) : WeakHarmonic b U h := by
  refine ⟨hh.1, ?_⟩
  intro W hW hcompact hsub
  obtain ⟨u, hueq, hu⟩ := hh.2 W hW hcompact hsub
  refine ⟨u, hueq, fun phi => ?_⟩
  rw [← hu phi]
  apply integral_congr_ae
  have habW := hab.filter_mono (ae_mono (Measure.restrict_mono (subset_closure.trans hsub) le_rfl))
  filter_upwards [habW] with x hx
  rw [hx]

/-- Constant multiplication of the coefficient preserves the weak equation. -/
theorem harmonic_weakHarmonic_const_mul_coefficient {d : ℕ} {U : Set (Vec d)}
    {a h : Vec d → ℝ} (hh : WeakHarmonic a U h) (c : ℝ) :
    WeakHarmonic (fun x => c * a x) U h := by
  refine ⟨hh.1, ?_⟩
  intro W hW hcompact hsub
  obtain ⟨u, hueq, hu⟩ := hh.2 W hW hcompact hsub
  refine ⟨u, hueq, fun phi => ?_⟩
  simp only [mul_assoc, integral_const_mul, hu phi, mul_zero]

/-- The ratio-sixteen upper bound requires the coefficient band only on
the unit cube, since clipping elsewhere does not change its equation. -/
theorem exists_harmonic_unit_positive_bound_local_coefficient {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Vec d → ℝ) (z : Vec d),
      (∀ x ∈ centeredAxisCube z 1, 1 / 4 ≤ a x ∧ a x ≤ 4) →
      AEStronglyMeasurable a (volume.restrict (centeredAxisCube z 1)) →
      ∀ h : Vec d → ℝ, WeakHarmonic a (centeredAxisCube z 1) h →
      ∀ x ∈ centeredAxisCube z (1 / 4),
        ENNReal.ofReal (max (h x) 0) ≤
          ENNReal.ofReal C * eLpNorm (fun y => max (h y) 0) 2
            (volume.restrict (centeredAxisCube z 1)) := by
  obtain ⟨C, hC, hbound⟩ := exists_harmonic_ratio_positive_bound hd
  refine ⟨C, hC, ?_⟩
  intro a z hab ha h hh x hx
  let b : Vec d → ℝ := fun y => max (1 / 4) (min 4 (a y))
  have hb : ∀ y, 1 / 4 ≤ b y ∧ b y ≤ 4 := by
    intro y
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hbmeas : AEStronglyMeasurable b (volume.restrict (centeredAxisCube z 1)) :=
    aestronglyMeasurable_const.sup (aestronglyMeasurable_const.inf ha)
  have heq : a =ᵐ[volume.restrict (centeredAxisCube z 1)] b := by
    filter_upwards [ae_restrict_mem (isOpen_axisCube _ _).measurableSet] with y hy
    simp only [b, min_eq_right (hab y hy).2, max_eq_right (hab y hy).1]
  exact hbound b z hb hbmeas h (harmonic_weakHarmonic_coefficient_congr_ae hh heq) x hx

/-- Pullback changes the positive-part `L²` norm by the exact volume factor. -/
theorem harmonic_eLpNorm_positive_smul {d : ℕ} {U : Set (Vec d)} {r : ℝ}
    (hr : 0 < r) {h : Vec d → ℝ}
    (hh : AEStronglyMeasurable h (volume.restrict (r • U))) :
    eLpNorm (fun x => max (h (r • x)) 0) 2 (volume.restrict U) =
      ENNReal.ofReal (r ^ d) ^ (-(1 / 2) : ℝ) *
        eLpNorm (fun x => max (h x) 0) 2 (volume.restrict (r • U)) := by
  let T : Vec d → Vec d := fun x => r • x
  have hmap := map_smul_volume_restrict hr U
  have hg : AEStronglyMeasurable (fun x => max (h x) 0) (volume.restrict (r • U)) :=
    hh.sup aestronglyMeasurable_const
  have hgmap : AEStronglyMeasurable (fun x => max (h x) 0) (Measure.map T (volume.restrict U)) := by
    rw [hmap]
    exact hg.smul_measure _
  have hnorm := eLpNorm_map_measure (p := (2 : ℝ≥0∞)) hgmap (measurable_const_smul r).aemeasurable
  rw [hmap, eLpNorm_smul_measure_of_ne_zero (by positivity)] at hnorm
  simp only [Function.comp_def, T] at hnorm
  rw [← hnorm]
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul,
    ENNReal.ofReal_inv_of_pos (pow_pos hr d), ENNReal.inv_rpow, ENNReal.rpow_neg]

/-- Scale-invariant positive-part boundedness for the exact local
weak-harmonicity predicate and the localized coefficient band. -/
theorem exists_harmonic_scaled_positive_bound {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Vec d → ℝ) (z : Vec d) (R : ℝ), 0 < R →
      (∀ x ∈ centeredAxisCube z R, 1 / 4 ≤ a x ∧ a x ≤ 4) →
      AEStronglyMeasurable a (volume.restrict (centeredAxisCube z R)) →
      ∀ h : Vec d → ℝ, WeakHarmonic a (centeredAxisCube z R) h →
      ∀ x ∈ centeredAxisCube z (R / 4),
        ENNReal.ofReal (max (h x) 0) ≤
          ENNReal.ofReal C * volume (centeredAxisCube z R) ^ (-(1 / 2) : ℝ) *
            eLpNorm (fun y => max (h y) 0) 2 (volume.restrict (centeredAxisCube z R)) := by
  obtain ⟨C, hC, hbound⟩ := exists_harmonic_unit_positive_bound_local_coefficient hd
  refine ⟨C, hC, ?_⟩
  intro a z R hR hab ha h hh x hx
  let U : Set (Vec d) := centeredAxisCube (R⁻¹ • z) 1
  have hdom : R • U = centeredAxisCube z R := by
    rw [harmonic_smul_centeredAxisCube _ _ hR]
    simp only [smul_inv_smul₀ hR.ne', mul_one]
  have hh' : WeakHarmonic a (R • U) h := hdom.symm ▸ hh
  have hscaled := harmonic_weakHarmonic_unscale hR hh'
  have hband : ∀ y ∈ U, 1 / 4 ≤ a (R • y) ∧ a (R • y) ≤ 4 := by
    intro y hy
    apply hab
    rw [← hdom]
    exact ⟨y, hy, rfl⟩
  have haMap : AEStronglyMeasurable a (Measure.map (fun y : Vec d => R • y) (volume.restrict U)) := by
    rw [map_smul_volume_restrict hR, hdom]
    exact ha.smul_measure _
  have hameas := haMap.comp_aemeasurable (measurable_const_smul R).aemeasurable
  have hinner : R⁻¹ • x ∈ centeredAxisCube (R⁻¹ • z) (1 / 4) := by
    have hdomeq : R • centeredAxisCube (R⁻¹ • z) (1 / 4) = centeredAxisCube z (R / 4) := by
      rw [harmonic_smul_centeredAxisCube _ _ hR]
      simp only [smul_inv_smul₀ hR.ne', mul_one_div]
    rw [← hdomeq] at hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa only [inv_smul_smul₀ hR.ne'] using hy
  have hresult := hbound (fun y => a (R • y)) (R⁻¹ • z) hband hameas
    (fun y => h (R • y)) hscaled (R⁻¹ • x) hinner
  have hnorm := harmonic_eLpNorm_positive_smul hR
    (hh'.1.aestronglyMeasurable (by rw [hdom]; exact (isOpen_axisCube _ _).measurableSet))
  rw [smul_inv_smul₀ hR.ne', hnorm, hdom] at hresult
  rw [volume_centeredAxisCube_eq z hR.le]
  simpa only [mul_assoc] using hresult

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
