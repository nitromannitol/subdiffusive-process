import SubdiffusiveProcess.Static.CutoffHolderEnergyGrowth

/-! # Macroscopic energy-growth arithmetic in the native cutoff carrier -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The native three-quarter gradient row has exactly energy exponent
`d - 1/2`, including windows which meet a boundary face or corner. -/
theorem cutoff_window_energy_growth_threeQuarters {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (m X : ℕ)
    (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hrow : ∀ (n : ℕ), (n : ℤ) ≤ (m : ℤ) - (X : ℤ) →
      ∀ x ∈ cube d (m : ℤ),
        vectorNormalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
          (fun z => Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega z) • u.grad z) ≤
          C * (3 : ℝ) ^ (((m : ℝ) - (n : ℝ)) / 4) * D)
    (n : ℕ) (hn : (n : ℤ) ≤ (m : ℤ) - (X : ℤ))
    (x : Vec d) (hx : x ∈ cube d (m : ℤ)) :
    ∫⁻ z in truncatedCube d (m : ℤ) (n : ℤ) x,
      ENNReal.ofReal (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega z *
        vecDot (u.grad z) (u.grad z)) ≤
      ENNReal.ofReal (C ^ 2 * D ^ 2 * (3 : ℝ) ^ ((m : ℝ) / 2) *
        ((3 : ℝ) ^ n) ^ ((d : ℝ) - 1 / 2)) := by
  let W := truncatedCube d (m : ℤ) (n : ℤ) x
  have hnm : (n : ℤ) - 1 ≤ (m : ℤ) := by omega
  have hint := (Section6HarmonicApproximation.integrableOn_aCutoff_energy M L omega
    (originCube d (m : ℤ)) u).mono_set
      (Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) (n : ℤ) x)
  have hbound := hrow n hn x hx
  have hraw := lintegral_energy_le_volume_mul_sq W
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) u.grad
    (fun z => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega z).le)
    (Section6ExcessDecay.volume_toReal_truncatedCube_pos x hx hnm) hint
    (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)) hD) hbound
  have hvolume : (volume W).toReal ≤ ((3 : ℝ) ^ n) ^ d := by
    simpa only [Int.cast_natCast, zpow_natCast] using
      (Section6ExcessDecay.volume_toReal_truncatedCube_bounds x hx hnm).2
  refine hraw.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    (volume W).toReal * (C * (3 : ℝ) ^ (((m : ℝ) - (n : ℝ)) / 4) * D) ^ 2 ≤
        ((3 : ℝ) ^ n) ^ d * (C * (3 : ℝ) ^ (((m : ℝ) - (n : ℝ)) / 4) * D) ^ 2 :=
      mul_le_mul_of_nonneg_right hvolume (sq_nonneg _)
    _ = _ := by
      have hscales : ((3 : ℝ) ^ n) ^ d *
          ((3 : ℝ) ^ (((m : ℝ) - (n : ℝ)) / 4)) ^ 2 =
          (3 : ℝ) ^ ((m : ℝ) / 2) * ((3 : ℝ) ^ n) ^ ((d : ℝ) - 1 / 2) := by
        rw [← Real.rpow_natCast (3 : ℝ) n,
          ← Real.rpow_mul_natCast (by norm_num),
          ← Real.rpow_mul_natCast (by norm_num),
          ← Real.rpow_add (by norm_num),
          ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1
        ring
      calc
        _ = C ^ 2 * D ^ 2 * (((3 : ℝ) ^ n) ^ d *
          ((3 : ℝ) ^ (((m : ℝ) - (n : ℝ)) / 4)) ^ 2) := by ring
        _ = _ := by rw [hscales]; ring

/-- The macroscopic gradient row yields its exact raw energy exponent,
with the exponent parameter retained for the microscopic joining margin. -/
theorem cutoff_window_energy_growth_of_gradient_row {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (m X : ℕ) (alpha : ℝ)
    (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hrow : ∀ (n : ℕ), (n : ℤ) ≤ (m : ℤ) - (X : ℤ) →
      ∀ x ∈ cube d (m : ℤ),
        vectorNormalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
          (fun z => Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega z) • u.grad z) ≤
          C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) * D)
    (n : ℕ) (hn : (n : ℤ) ≤ (m : ℤ) - (X : ℤ))
    (x : Vec d) (hx : x ∈ cube d (m : ℤ)) :
    ∫⁻ z in truncatedCube d (m : ℤ) (n : ℤ) x,
      ENNReal.ofReal (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega z *
        vecDot (u.grad z) (u.grad z)) ≤
      ENNReal.ofReal (C ^ 2 * D ^ 2 * (3 : ℝ) ^ (2 * (1 - alpha) * (m : ℝ)) *
        ((3 : ℝ) ^ n) ^ ((d : ℝ) - 2 * (1 - alpha))) := by
  let W := truncatedCube d (m : ℤ) (n : ℤ) x
  have hnm : (n : ℤ) - 1 ≤ (m : ℤ) := by omega
  have hint := (Section6HarmonicApproximation.integrableOn_aCutoff_energy M L omega
    (originCube d (m : ℤ)) u).mono_set
      (Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) (n : ℤ) x)
  have hbound := hrow n hn x hx
  have hraw := lintegral_energy_le_volume_mul_sq W
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) u.grad
    (fun z => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega z).le)
    (Section6ExcessDecay.volume_toReal_truncatedCube_pos x hx hnm) hint
    (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)) hD) hbound
  have hvolume : (volume W).toReal ≤ ((3 : ℝ) ^ n) ^ d := by
    simpa only [Int.cast_natCast, zpow_natCast] using
      (Section6ExcessDecay.volume_toReal_truncatedCube_bounds x hx hnm).2
  refine hraw.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    (volume W).toReal * (C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) * D) ^ 2 ≤
        ((3 : ℝ) ^ n) ^ d * (C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) * D) ^ 2 :=
      mul_le_mul_of_nonneg_right hvolume (sq_nonneg _)
    _ = _ := by
      have hscales : ((3 : ℝ) ^ n) ^ d *
          ((3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) ^ 2 =
          (3 : ℝ) ^ (2 * (1 - alpha) * (m : ℝ)) * ((3 : ℝ) ^ n) ^ ((d : ℝ) - 2 * (1 - alpha)) := by
        rw [← Real.rpow_natCast (3 : ℝ) n,
          ← Real.rpow_mul_natCast (by norm_num),
          ← Real.rpow_mul_natCast (by norm_num),
          ← Real.rpow_add (by norm_num),
          ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1
        ring
      calc
        _ = C ^ 2 * D ^ 2 * (((3 : ℝ) ^ n) ^ d *
          ((3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) ^ 2) := by ring
        _ = _ := by rw [hscales]; ring

end SubdiffusiveProcess.Static
