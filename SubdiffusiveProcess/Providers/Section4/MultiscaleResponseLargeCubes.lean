module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.LargeCubeAggregation

@[expose] public section

/-!
# Provider for the large-cube multiscale response estimate

The proof follows : split the scale sum above the
cutoff, between zero and the cutoff, and below zero; take the finite spatial
maximum; then sum the normalized geometric weights.
-/

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

namespace SubdiffusiveProcess.Providers.Section4

open Homogenization Homogenization.Book

/-- Exact provider export for `l.multiscale.response.large.cubes`. -/
theorem multiscale_response_large_cubes {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (L m0 : ℕ) (s delta1 xi : ℝ),
        0 < s → s ≤ 1 → M.delta ^ 2 ≤ delta1 → delta1 < 1 →
        L ≤ m0 →
        4 * (d : ℝ) * s⁻¹ ≤ xi →
        xi ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
        inductionHypothesis M m0 xi delta1 →
        ∀ K : ℕ, L ≤ K → ∀ z : PaperCubeTranslate d, ∀ r : ℕ,
          (r = 1 ∨ r = 2) →
          paperENNRealLpNorm M.P.toMeasure xi
              (translatedHomogenizationErrorRandom M L K z s r) ≤
            ENNReal.ofReal
              (C * Real.rpow s (-(1 / (r : ℝ))) * Real.sqrt delta1) := by
  rcases positiveScaleResponseMoment_of_annealed_ordering
      (fun M m k hkm =>
        SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds.2 M m k hkm) with
    ⟨cPos, CPos, hcPos, _hcPos1, hCPos, hpos⟩
  rcases subunit_response_moment (d := d) with
    ⟨cSub, CSub, hcSub, _hcSub1, hCSub, hsub⟩
  let c := min cPos cSub
  let C0 := max CPos CSub
  let C := 40 * C0
  have hc : 0 < c := lt_min hcPos hcSub
  have hC0 : 1 ≤ C0 := hCPos.trans (le_max_left _ _)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨c, C, hc, hC, ?_⟩
  intro M L m0 s delta1 xi hs hs1 hdelta hdelta1 hLm0 hdim hupper hS
    K hLK z r hr
  have hdNat : 0 < d := lt_of_lt_of_le (by omega) M.shellPrefix.dimension
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hxi : 0 < xi := lt_of_lt_of_le (by positivity) hdim
  have hxi1 : 1 ≤ xi := hS.1
  have hdelta0 : 0 ≤ delta1 := (sq_nonneg M.delta).trans hdelta
  have hfactor0 : 0 ≤ s * (M.delta ^ 2)⁻¹ * delta1 := by positivity
  have hupperPos : xi ≤ cPos * s * (M.delta ^ 2)⁻¹ * delta1 :=
    hupper.trans (calc
      c * s * (M.delta ^ 2)⁻¹ * delta1 =
          c * (s * (M.delta ^ 2)⁻¹ * delta1) := by ring
      _ ≤ cPos * (s * (M.delta ^ 2)⁻¹ * delta1) :=
        mul_le_mul_of_nonneg_right (min_le_left cPos cSub) hfactor0
      _ = _ := by ring)
  have hupperSub : xi ≤ cSub * s * (M.delta ^ 2)⁻¹ * delta1 :=
    hupper.trans (calc
      c * s * (M.delta ^ 2)⁻¹ * delta1 =
          c * (s * (M.delta ^ 2)⁻¹ * delta1) := by ring
      _ ≤ cSub * (s * (M.delta ^ 2)⁻¹ * delta1) :=
        mul_le_mul_of_nonneg_right (min_le_right cPos cSub) hfactor0
      _ = _ := by ring)
  let a : ℝ := (d : ℝ) / xi + s / 2
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    exact add_nonneg (div_nonneg hd.le hxi.le) (by positivity)
  have hdOver : (d : ℝ) / xi ≤ s / 4 := by
    have hratio : (4 * (d : ℝ) * s⁻¹) / xi ≤ 1 :=
      (div_le_one hxi).2 hdim
    calc
      (d : ℝ) / xi = ((4 * (d : ℝ) * s⁻¹) / xi) * (s / 4) := by
        field_simp [hs.ne', hxi.ne']
      _ ≤ 1 * (s / 4) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = s / 4 := one_mul _
  have ha : a ≤ 3 * s / 4 := by dsimp only [a]; linarith
  have hscale : ∀ l : ℕ,
      paperENNRealLpNorm M.P.toMeasure xi
          (largeCubeScaleMaximum M L K ((K : ℤ) - (l : ℤ))) ≤
        ENNReal.ofReal (C0 * Real.sqrt delta1 *
          Real.rpow 3 (a * (l : ℝ))) := by
    intro l
    have hki : (K : ℤ) - (l : ℤ) ≤ (K : ℤ) := by omega
    have hEach : ∀ Q ∈ descendantsAtScale (originCube d (K : ℤ))
        ((K : ℤ) - (l : ℤ)),
        paperENNRealLpNorm M.P.toMeasure xi
            (normalizedDefect M L (Ch02.cubeDomain Q)) ≤
          ENNReal.ofReal (C0 * delta1 *
            Real.rpow 3 (s * (l : ℝ))) := by
      intro Q hQ
      have hQscale : Q.scale = (K : ℤ) - (l : ℤ) :=
        Homogenization.Book.Ch04.scale_eq_of_mem_descendantsAtScale_originCube
          hki hQ
      by_cases hkneg : (K : ℤ) - (l : ℤ) < 0
      · have hsubMoment := hsub M xi delta1 s L ((K : ℤ) - (l : ℤ))
          hxi1 hdelta hdelta1 hs hs1 hdim hupperSub hkneg
        have hraw := normalizedDefect_negative_scale_moment M hxi.le hkneg
          hsubMoment Q hQscale
        refine hraw.trans (ENNReal.ofReal_le_ofReal ?_)
        have hLl : L ≤ l := by omega
        have hLlR : (L : ℝ) ≤ (l : ℝ) := by exact_mod_cast hLl
        have hpow := Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 3)
          (mul_le_mul_of_nonneg_left hLlR hs.le)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (le_max_right CPos CSub) hdelta0) hpow
          (Real.rpow_nonneg (by norm_num) _)
          (mul_nonneg (zero_le_one.trans hC0) hdelta0)
      · have hk0 : 0 ≤ (K : ℤ) - (l : ℤ) := le_of_not_gt hkneg
        let k := Int.toNat ((K : ℤ) - (l : ℤ))
        have hkEq : (k : ℤ) = (K : ℤ) - (l : ℤ) :=
          Int.toNat_of_nonneg hk0
        have hkK : k ≤ K := by omega
        by_cases hLk : L ≤ k
        · have hraw := normalizedDefect_largeCube_lpnorm_le_induction
            M hxi1 hS hLk hLm0 Q (by simpa only [hkEq] using hQscale)
          refine hraw.trans (ENNReal.ofReal_le_ofReal ?_)
          have hpow1 : 1 ≤ Real.rpow 3 (s * (l : ℝ)) :=
            Real.one_le_rpow (by norm_num) (by positivity)
          calc
            delta1 = 1 * delta1 * 1 := by ring
            _ ≤ C0 * delta1 * Real.rpow 3 (s * (l : ℝ)) := by gcongr
        · have hkL : k ≤ L := le_of_lt (lt_of_not_ge hLk)
          have hk0m : k ≤ m0 := hkL.trans hLm0
          have hraw := normalizedDefect_positive_scale_moment M hpos hS
            hdelta hdelta1 hs hs1 hupperPos hxi.le hk0m hkL Q
            (by simpa only [hkEq] using hQscale)
          refine hraw.trans (ENNReal.ofReal_le_ofReal ?_)
          have hdepth : L - k ≤ l := by omega
          have hdepthR : ((L - k : ℕ) : ℝ) ≤ (l : ℝ) := by
            exact_mod_cast hdepth
          have hpow := Real.rpow_le_rpow_of_exponent_le
            (by norm_num : (1 : ℝ) ≤ 3)
            (mul_le_mul_of_nonneg_left hdepthR hs.le)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right (le_max_left CPos CSub) hdelta0) hpow
            (Real.rpow_nonneg (by norm_num) _)
            (mul_nonneg (zero_le_one.trans hC0) hdelta0)
    simpa only [a] using!
      largeCubeScaleMaximum_moment_profile_of_each M L K l hxi hdelta0 hC0 hEach
  have hrNat : 0 < r := by omega
  have hstart := translatedHomogenizationErrorRandom_lpnorm_le_scaleMaximumMoments
    M L K z s xi hrNat hxi1
  refine hstart.trans ?_
  have hrR : 0 < (r : ℝ) := by
    rcases hr with rfl | rfl <;> norm_num
  have hp0 : 0 ≤ (r : ℝ)⁻¹ := inv_nonneg.mpr hrR.le
  have hterm : ∀ l : ℕ,
      (ENNReal.ofReal (Ch02.geometricWeight s (r : ℝ) l)) ^ ((r : ℝ)⁻¹) *
          paperENNRealLpNorm M.P.toMeasure xi
            (largeCubeScaleMaximum M L K ((K : ℤ) - (l : ℤ))) ≤
        ENNReal.ofReal
          (Real.rpow (Ch02.geometricWeight s (r : ℝ) l) ((r : ℝ)⁻¹) *
            (C0 * Real.sqrt delta1 * Real.rpow 3 (a * (l : ℝ)))) := by
    intro l
    calc
      _ ≤ (ENNReal.ofReal (Ch02.geometricWeight s (r : ℝ) l)) ^ ((r : ℝ)⁻¹) *
          ENNReal.ofReal
            (C0 * Real.sqrt delta1 * Real.rpow 3 (a * (l : ℝ))) :=
        mul_le_mul_right (hscale l) _
      _ = _ := by
        calc
          _ = ENNReal.ofReal
              ((Ch02.geometricWeight s (r : ℝ) l) ^ ((r : ℝ)⁻¹)) *
                ENNReal.ofReal
                  (C0 * Real.sqrt delta1 * Real.rpow 3 (a * (l : ℝ))) := by
            exact congrArg (fun x : ℝ≥0∞ => x * ENNReal.ofReal
              (C0 * Real.sqrt delta1 * Real.rpow 3 (a * (l : ℝ))))
              (ENNReal.ofReal_rpow_of_nonneg
                (Homogenization.geometricWeight_nonneg l (by positivity)) hp0)
          _ = ENNReal.ofReal
              ((Ch02.geometricWeight s (r : ℝ) l) ^ ((r : ℝ)⁻¹) *
                (C0 * Real.sqrt delta1 * Real.rpow 3 (a * (l : ℝ)))) :=
            (ENNReal.ofReal_mul
              (Real.rpow_nonneg
                (Homogenization.geometricWeight_nonneg l (by positivity)) _)).symm
          _ = _ := by rfl
  have hsum := summable_geometricWeight_root_mul_profile
    (A := C0 * Real.sqrt delta1) hr hs ha
  calc
    _ ≤ ∑' l : ℕ, ENNReal.ofReal
          (Real.rpow (Ch02.geometricWeight s (r : ℝ) l) ((r : ℝ)⁻¹) *
            (C0 * Real.sqrt delta1 * Real.rpow 3 (a * (l : ℝ)))) :=
      ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' l : ℕ,
          Real.rpow (Ch02.geometricWeight s (r : ℝ) l) ((r : ℝ)⁻¹) *
            (C0 * Real.sqrt delta1 * Real.rpow 3 (a * (l : ℝ)))) := by
      rw [ENNReal.ofReal_tsum_of_nonneg]
      · intro l
        exact mul_nonneg
          (Real.rpow_nonneg
            (Homogenization.geometricWeight_nonneg l (by positivity)) _)
          (mul_nonneg (mul_nonneg (zero_le_one.trans hC0)
            (Real.sqrt_nonneg _)) (Real.rpow_nonneg (by norm_num) _))
      · exact hsum
    _ ≤ ENNReal.ofReal
          (40 * (C0 * Real.sqrt delta1) *
            Real.rpow s (-(1 / (r : ℝ)))) :=
      ENNReal.ofReal_le_ofReal
        (tsum_geometricWeight_root_mul_profile_le hr hs hs1
          (mul_nonneg (zero_le_one.trans hC0) (Real.sqrt_nonneg _)) ha0 ha)
    _ = ENNReal.ofReal
          (C * Real.rpow s (-(1 / (r : ℝ))) * Real.sqrt delta1) := by
      congr 1
      dsimp only [C]
      ring

end SubdiffusiveProcess.Providers.Section4
