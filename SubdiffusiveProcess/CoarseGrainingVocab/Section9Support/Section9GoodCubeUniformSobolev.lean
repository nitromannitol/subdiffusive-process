module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeUniformSobolevBesov
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeUniformSobolevEllipticity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeUniformSobolevClock
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubePositiveScaleSobolev
public import Homogenization.Geometry.TriadicCubeTranslation

@[expose] public section

/-!
# The good-cube Sobolev display from a local coefficient ratio

On a cube where the actual coefficient lies between `c` and `2 * c`, its
normalized negative Besov test is at most one and the product of inverse
lower ellipticity with coefficient average is at most `8 * d`. The intrinsic
clock pays the Euclidean squared radius at every integer scale. Consequently
the Sobolev exponent and constant depend only on dimension, including below
the unit scale and independently of the actual cutoff.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open Homogenization.Book MeasureTheory _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- One exponent and constant work for both the local ratio criterion at all
integer scales and the positive descendant coefficient tests. -/
theorem exists_goodCube_sobolev_common_tests (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p A : ℝ, 2 < p ∧ 1 ≤ A ∧
      (∀ (M : GMCModel d) (L : ℕ) (omega : PotentialSample d) (m : ℤ) (z : Vec d),
        (∃ c : ℝ, 0 < c ∧ ∀ x ∈ openCubeSet (originCube d m),
          c ≤ aCutoff M L omega (x + z) ∧ aCutoff M L omega (x + z) ≤ 2 * c) →
        GoodCubeSobolevDisplay (aCutoff M L omega) p A
          (Section7Process.timeScale (ahom M)) (z, (3 : ℝ) ^ m)) ∧
      (∀ (M : GMCModel d) (n m : ℕ), m ≤ n →
      ∀ (omega : PotentialSample d) (z : Vec d),
        ellipticityMomentObservable M n (m : ℤ) (1 / 8)
          (translatePotentialSample z omega) ≤ 1 →
        cubeAverage (originCube d (m : ℤ)) (fun x => aCutoff M n omega (x + z)) ≤ 3 / 2 →
        ahom M m ≤ 2 * ahom M n →
        let Q0 := originCube d (m : ℤ)
        let b0 : Vec d → ℝ := fun x => aCutoff M n omega (x + z)
        ∀ hb : ExactCircIntegrable Q0 (fun x => b0 x / cubeAverage Q0 b0 - 1),
          ENNReal.ofReal (Real.rpow 3 (-(1 / 8 : ℝ) * (m : ℝ))) *
            paperNegativeBesovCircDiagonal Q0 (1 / 8) (4 * (d : ℝ))
              (fun x => b0 x / cubeAverage Q0 b0 - 1) hb ≤ 1 →
          GoodCubeSobolevDisplay (aCutoff M n omega) p A
            (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M))
            (z, (3 : ℝ) ^ m)) := by
  obtain ⟨p, C, hp, hC, hbridge⟩ := goodCube_weighted_local_sobolev_cutoff d hd
  let A : ℝ := max 1 (max (27 * C * (2 : ℝ) ^ (2 / p))
    (C * (2 : ℝ) ^ (2 / p) * (8 * (d : ℝ))))
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hApositive : 27 * C * (2 : ℝ) ^ (2 / p) ≤ A :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hAnegative : C * (2 : ℝ) ^ (2 / p) * (8 * (d : ℝ)) ≤ A :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨p, A, hp, hA1, ?_, ?_⟩
  · intro M L omega m z hratio
    obtain ⟨c, hc, hbound⟩ := hratio
    let Q := originCube d m
    let b : Vec d → ℝ := fun x => aCutoff M L omega (x + z)
    have hbcont : Continuous b :=
      (continuous_aCutoff M L omega).comp (continuous_id.add continuous_const)
    obtain ⟨havglo, havghi, hbesov⟩ :=
      goodCube_normalized_besov_of_ratio hd Q b hbcont hc hbound
    obtain ⟨_, hb, _⟩ := goodCube_cutoff_sobolev_data M L omega z Q
    have hbound' : ∀ x ∈ openCubeSet Q,
        c ≤ aCutoff M L (translatePotentialSample z omega) x ∧
          aCutoff M L (translatePotentialSample z omega) x ≤ 2 * c := by
      intro x hx
      simpa only [Section6Covariance.aCutoff_translatePotentialSample] using! hbound x hx
    have hlam := goodCube_cutoff_lambdaSq_inv_le_of_bounds M L
      (translatePotentialSample z omega) Q hc hbound' (by norm_num : (0 : ℝ) < 1 / 2)
    have havg0 : 0 ≤ cubeAverage Q b := hc.le.trans havglo
    have hprice :
        (Ch02.lambdaSq Q (1 / 2) (.finite 1)
          (aCutoffFamily M L (translatePotentialSample z omega)))⁻¹ * cubeAverage Q b ≤
          8 * (d : ℝ) := by
      calc _ ≤ (4 * (d : ℝ) * c⁻¹) * (2 * c) :=
          mul_le_mul hlam havghi havg0 (by positivity)
        _ = 8 * (d : ℝ) := by field_simp; ring
    apply hbridge M L omega m z hb 1 (by norm_num)
      (by simpa using! hbesov hb) A (Section7Process.timeScale (ahom M)) hA0
    have hK : 0 ≤ C * (2 : ℝ) ^ (2 / p) * ((3 : ℝ) ^ m) ^ 2 := by positivity
    calc C * (1 + 1) ^ (2 / p) * ((3 : ℝ) ^ m) ^ 2 *
          (Ch02.lambdaSq (originCube d m) (1 / 2) (.finite 1)
            (aCutoffFamily M L (translatePotentialSample z omega)))⁻¹ *
          cubeAverage (originCube d m) (fun x => aCutoff M L omega (x + z))
        = C * (2 : ℝ) ^ (2 / p) * ((3 : ℝ) ^ m) ^ 2 *
            ((Ch02.lambdaSq Q (1 / 2) (.finite 1)
              (aCutoffFamily M L (translatePotentialSample z omega)))⁻¹ * cubeAverage Q b) := by
            norm_num only [one_add_one_eq_two]; ring
      _ ≤ C * (2 : ℝ) ^ (2 / p) * ((3 : ℝ) ^ m) ^ 2 * (8 * (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hprice hK
      _ = (C * (2 : ℝ) ^ (2 / p) * (8 * (d : ℝ))) * ((3 : ℝ) ^ m) ^ 2 := by ring
      _ ≤ A * ((3 : ℝ) ^ m) ^ 2 :=
        mul_le_mul_of_nonneg_right hAnegative (sq_nonneg _)
      _ ≤ A * Section7Process.timeScale (ahom M) ((3 : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_left (goodCube_sq_triadic_le_clock M m) hA0
  · intro M n m hmn omega z hE1 havg hscale Q0 b0 hb hbesov
    have hahomn : 0 < ahom M n := ahom_pos M n
    have hahomm : 0 < ahom M m := ahom_pos M m
    have hE : ellipticityMomentObservable M n (m : ℤ) (1 / 8)
        (translatePotentialSample z omega) ≤ ENNReal.ofReal (1 : ℝ) := by
      rw [ENNReal.ofReal_one]; exact hE1
    have hlam9' : ahom M n * (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
        (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ ≤ 9 := by
      have h1 := goodCube_cutoff_lambda_price_le_of_ellipticity_test M n m hmn z omega
        (by norm_num : (0 : ℝ) ≤ 1) hE
      have hsqrt : Real.sqrt 2 ≤ 2 := by
        have hs1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have hs3 : 0 < 2 + Real.sqrt 2 := by linarith
        nlinarith
      have h3 : (1 + Real.sqrt 2 * 1) ^ 2 ≤ 9 := by
        have hs1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        nlinarith [hsqrt, hs1]
      linarith
    have hlam0 : 0 ≤ (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
        (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ :=
      inv_nonneg.mpr (le_of_lt (Ch02.lambdaSq_pos (originCube d (m : ℤ))
        (aCutoffFamily M n (translatePotentialSample z omega)) (by norm_num) (by norm_num [Ch02.MultiscaleExponent.IsAdmissible])))
    have hlamle : (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
        (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ ≤ 9 / ahom M n := by
      have h2 : (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
          (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ * ahom M n ≤ 9 := by
        rw [mul_comm]; exact hlam9'
      have hinv : 0 < (ahom M n)⁻¹ := inv_pos.mpr hahomn
      have h3 : (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
          (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ * ahom M n * (ahom M n)⁻¹
          ≤ 9 * (ahom M n)⁻¹ := mul_le_mul_of_nonneg_right h2 (le_of_lt hinv)
      have h4 : (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
          (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ * ahom M n * (ahom M n)⁻¹
          = (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
          (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hahomn), mul_one]
      rw [div_eq_mul_inv 9 (ahom M n), ← h4]
      exact h3
    have hs : 0 < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num : (0 : ℝ) < 3) (m : ℤ)
    have hprice : C * (1 + 1) ^ (2 / p) * ((3 : ℝ) ^ (m : ℤ)) ^ 2 *
        (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
          (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ *
        cubeAverage Q0 b0 ≤
        A *
          SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) ((3 : ℝ) ^ (m : ℤ)) := by
      have h2p : (1 + 1 : ℝ) ^ (2 / p) = (2 : ℝ) ^ (2 / p) := by norm_num
      have hclock : SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)
          ((3 : ℝ) ^ (m : ℤ)) = ((3 : ℝ) ^ (m : ℤ)) ^ 2 / ahom M m := by
        rw [zpow_natCast, SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale_triadic]
        show (3 : ℝ) ^ (2 * m) / ahom M m = ((3 : ℝ) ^ m) ^ 2 / ahom M m
        rw [← pow_mul, mul_comm m 2]
      rw [h2p, hclock, ← mul_div_assoc]
      exact goodCube_price_algebra p C (A)
        ((3 : ℝ) ^ (m : ℤ)) (ahom M m) (ahom M n) _ (cubeAverage Q0 b0)
        (by linarith) hC hs hahomm hahomn hscale hlam0 hlamle havg hApositive
    have hbound : ENNReal.ofReal (Real.rpow 3 (-(1 / 8 : ℝ) * (m : ℝ))) *
        paperNegativeBesovCircDiagonal Q0 (1 / 8) (4 * (d : ℝ))
          (fun x => b0 x / cubeAverage Q0 b0 - 1) hb ≤ ENNReal.ofReal (1 : ℝ) := by
      rw [ENNReal.ofReal_one]; exact hbesov
    have hdisp := hbridge M n omega (m : ℤ) z hb 1 le_rfl hbound
      (A)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)) hA0 hprice
    rw [zpow_natCast] at hdisp
    exact hdisp

/-- A factor-two local coefficient ratio supplies the exact good-cube Sobolev
display at every integer scale. The hypothesis is expressed in the reference
frame of the translated cube. -/
theorem exists_goodCube_sobolev_of_local_ratio (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p A : ℝ, 2 < p ∧ 1 ≤ A ∧
      ∀ (M : GMCModel d) (L : ℕ) (omega : PotentialSample d) (m : ℤ) (z : Vec d),
        (∃ c : ℝ, 0 < c ∧ ∀ x ∈ openCubeSet (originCube d m),
          c ≤ aCutoff M L omega (x + z) ∧ aCutoff M L omega (x + z) ≤ 2 * c) →
        GoodCubeSobolevDisplay (aCutoff M L omega) p A
          (Section7Process.timeScale (ahom M)) (z, (3 : ℝ) ^ m) := by
  obtain ⟨p, A, hp, hA, hratio, _⟩ := exists_goodCube_sobolev_common_tests d hd
  exact ⟨p, A, hp, hA, hratio⟩

/-- The physical form of the ratio criterion on an arbitrary translated
triadic cube, with the same constants chosen before the model and cutoff. -/
theorem exists_goodCube_sobolev_of_translated_ratio (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p A : ℝ, 2 < p ∧ 1 ≤ A ∧
      ∀ (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
        (Q : TriadicCube d) (z : Vec d),
        (∃ c : ℝ, 0 < c ∧ ∀ x ∈ translateSet z (openCubeSet Q),
          c ≤ aCutoff M L omega x ∧ aCutoff M L omega x ≤ 2 * c) →
        GoodCubeSobolevDisplay (aCutoff M L omega) p A
          (Section7Process.timeScale (ahom M))
          (cubeCenter Q + z, (3 : ℝ) ^ Q.scale) := by
  obtain ⟨p, A, hp, hA, hratio⟩ := exists_goodCube_sobolev_of_local_ratio d hd
  refine ⟨p, A, hp, hA, ?_⟩
  intro M L omega Q z hbound
  obtain ⟨c, hc, hbound⟩ := hbound
  apply hratio M L omega Q.scale (triadicCubeShift Q + z)
  refine ⟨c, hc, ?_⟩
  intro x hx
  have hxQ : x + triadicCubeShift Q ∈ openCubeSet Q := by
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube]
    exact ⟨x, hx, rfl⟩
  have hxz : (x + triadicCubeShift Q) + z ∈ translateSet z (openCubeSet Q) :=
    ⟨x + triadicCubeShift Q, hxQ, rfl⟩
  simpa only [add_assoc] using! hbound _ hxz

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
