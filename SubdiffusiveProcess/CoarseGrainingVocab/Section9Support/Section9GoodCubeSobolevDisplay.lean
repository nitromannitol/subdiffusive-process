import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSobolevNormalization
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSobolevTranslation
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSobolevCoefficient
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeHarmonicContraction




set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open Set MeasureTheory
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The translated cutoff Sobolev display under its Besov and clock-price tests.
`goodCube_cutoff_sobolev_data` supplies the `ExactCircIntegrable` proof for
every sample, so that carrier imposes no additional probabilistic condition. -/
theorem goodCube_weighted_local_sobolev_cutoff (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p C : ℝ, 2 < p ∧ 0 < C ∧
      ∀ (M : GMCModel d) (L : ℕ) (omega : PotentialSample d) (m : ℤ) (z : Vec d),
        let Q0 := originCube d m
        let b0 : Vec d → ℝ := fun x => aCutoff M L omega (x + z)
        ∀ hb : ExactCircIntegrable Q0 (fun x => b0 x / cubeAverage Q0 b0 - 1),
        ∀ B : ℝ, 1 ≤ B →
        ENNReal.ofReal (Real.rpow 3 (-(1 / 8 : ℝ) * (m : ℝ))) *
          SubdiffusiveProcess.CoarseGrainingVocab.paperNegativeBesovCircDiagonal Q0 (1 / 8)
            (4 * (d : ℝ)) (fun x => b0 x / cubeAverage Q0 b0 - 1) hb ≤
          ENNReal.ofReal B →
        ∀ (A : ℝ) (clock : ℝ → ℝ), 0 ≤ A →
          C * (1 + B) ^ (2 / p) * ((3 : ℝ) ^ m) ^ 2 *
              (Homogenization.Book.Ch02.lambdaSq Q0 (1 / 2) (.finite 1)
                (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffFamily M L
                  (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample z omega)))⁻¹ *
              cubeAverage Q0 b0 ≤ A * clock ((3 : ℝ) ^ m) →
          GoodCubeSobolevDisplay (aCutoff M L omega) p A clock (z, (3 : ℝ) ^ m) := by
  obtain ⟨p, C, hp, hC, htrans⟩ := goodCube_weighted_local_sobolev_translated d hd
  refine ⟨p, C, hp, hC, ?_⟩
  intro M L omega m z Q0 b0 hb B hB hbound A clock hA hprice
  obtain ⟨hcoef, hb0, hpt⟩ := goodCube_cutoff_sobolev_data M L omega z (originCube d m)
  have hs : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num : (0:ℝ) < 3) m
  have hp0 : 0 < p := by linarith
  have hdom : Homogenization.translateSet z (openCubeSet (originCube d m))
      = cubeSet (z, (3 : ℝ) ^ m) := by
    rw [← translatedCube_eq_cubeSet m z]
    ext x
    simp only [SubdiffusiveProcess.CoarseGrainingVocab.translatedCube, Set.mem_image,
      Homogenization.translateSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, hx⟩; exact ⟨y, hy, (hx.trans (add_comm y z)).symm⟩
    · rintro ⟨y, hy, hx⟩; exact ⟨y, hy, hx.symm.trans (add_comm z y)⟩
  have havg : volumeAverage (cubeSet (z, (3 : ℝ) ^ m)) (aCutoff M L omega)
      = cubeAverage (originCube d m) (fun x => aCutoff M L omega (x + z)) := by
    rw [← hdom]
    simp only [volumeAverage]
    rw [volume_translateSet_eq z (openCubeSet (originCube d m)),
      ← setIntegral_comp_addRight_translateSet z (openCubeSet (originCube d m))
        (fun x => aCutoff M L omega x),
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.weightedSobolev_cubeAverage_open,
      Homogenization.volume_openCubeSet_toReal]
  have hnorm0 := htrans m z (fun x => aCutoff M L omega x) hcoef hb0
    (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffFamily M L
      (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample z omega))
    (ae_of_all _ hpt) B hB hbound
  have hnorm : ∀ f : H10Function (translateSet z (openCubeSet (originCube d m))),
      (ENNReal.ofReal ((cubeAverage (originCube d m) (fun x => aCutoff M L omega (x + z)))⁻¹) *
        (volume (translateSet z (openCubeSet (originCube d m))))⁻¹ *
          ∫⁻ x in translateSet z (openCubeSet (originCube d m)),
            ENNReal.ofReal (|f.toH1Function.toFun x| ^ p * aCutoff M L omega x)) ^ (2 / p) ≤
        ENNReal.ofReal (C * (1 + B) ^ (2 / p) * ((3 : ℝ) ^ m) ^ 2 *
          (Homogenization.Book.Ch02.lambdaSq (originCube d m) (1 / 2) (.finite 1)
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffFamily M L
              (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample z omega)))⁻¹ *
          volumeAverage (translateSet z (openCubeSet (originCube d m))) (fun x =>
            aCutoff M L omega x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x))) := by
    intro f
    exact hnorm0 f.toH1Function (Or.inl ⟨f, rfl⟩)
  rw [hdom, ← havg] at hnorm
  refine goodCube_sobolevDisplay_cutoff_of_normalized
    (k := C * (1 + B) ^ (2 / p) * ((3 : ℝ) ^ m) ^ 2 *
      (Homogenization.Book.Ch02.lambdaSq (originCube d m) (1 / 2) (.finite 1)
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffFamily M L
          (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample z omega)))⁻¹) M L omega (z, (3 : ℝ) ^ m) hs hp0 hA ?_ ?_
  · rw [havg]; exact hprice
  · exact hnorm

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
