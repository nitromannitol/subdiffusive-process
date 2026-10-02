import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeExitTransfer
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubePositiveMass
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeNativeClock
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeHarmonicContraction
/-!
The actual cutoff Sobolev display supplies a uniform physical mean-exit upper bound. The constant is chosen before the model, while positive finite mass and continuous killed density are derived from existing cutoff and diffusion data. The clock comparison covers every integer native scale.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The native clock and actual Sobolev display give the physical exit upper cap, with the cap constant chosen from p and A alone. -/
theorem exists_goodCube_cutoff_sobolev_meanExit_upper_constant
    (p A : ℝ) (hp : 2 < p) (hA : 1 ≤ A) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (d : ℕ), 2 ≤ d → ∀ (M : GMCModel d) (J n : ℕ)
        (omega : PotentialSample d) (m : ℤ) (z : Vec d)
        (law : Kernel (Vec d) (Path d)),
        m ≤ (n : ℤ) →
        2 * M.delta^2 * ((J : ℝ) + 1) ≤ Real.log 2 →
        LocalDiffusionData (aCutoff M n omega) (aCutoff M n omega) law →
        GoodCubeSobolevDisplay (aCutoff M n omega) p A
          (Section7Process.timeScale (ahom M)) (z, (3 : ℝ)^m) →
        ∀ x ∈ translateSet z (openCubeSet (originCube d m)),
          meanExit law (translateSet z (openCubeSet (originCube d m))) x ≤
            ENNReal.ofReal (K * ((3 : ℝ)^m)^2 / (if J ≤ n then ahom M n else 1)) := by
  obtain ⟨CE, hCE0, hCE⟩ := exists_goodCube_exit_upper_constant hp
  refine ⟨max 1 (2 * CE * A ^ CE), le_max_left _ _, ?_⟩
  intro d hd M J n omega m z law hmn hbudget hD hSob x hx
  obtain ⟨hσ0, hcmp⟩ := goodCube_native_clock_le_comparison_clock M J n m hmn hbudget
  have hσpos : 0 < (if J ≤ n then ahom M n else 1) := hσ0
  have h3pos : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num : (0 : ℝ) < 3) m
  have hQ : 0 < (z, (3 : ℝ) ^ m).2 := h3pos
  have hclock : 0 < Section7Process.timeScale (ahom M) ((3 : ℝ) ^ m) :=
    Section7Process.timeScale_pos (ahom_pos M) h3pos
  obtain ⟨hm0, hmT⟩ := goodCube_weightedMeasure_aCutoff_ne_zero_ne_top M n omega
    (z, (3 : ℝ) ^ m) hQ
  have hkilled : HasContinuousKilledDensity (aCutoff M n omega) law
      (cubeSet (z, (3 : ℝ) ^ m)) :=
    hD.2 (cubeSet (z, (3 : ℝ) ^ m)) (isOpen_centeredAxisCube (z, (3 : ℝ) ^ m).1
      (z, (3 : ℝ) ^ m).2) (isBounded_centeredAxisCube (z, (3 : ℝ) ^ m).1
      (z, (3 : ℝ) ^ m).2)
  have hdom : Homogenization.translateSet z (openCubeSet (originCube d m))
      = cubeSet (z, (3 : ℝ) ^ m) := by
    rw [← translatedCube_eq_cubeSet m z]
    ext x
    simp only [SubdiffusiveProcess.CoarseGrainingVocab.translatedCube, Set.mem_image,
      Homogenization.translateSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, hx⟩; exact ⟨y, hy, (hx.trans (add_comm y z)).symm⟩
    · rintro ⟨y, hy, hx⟩; exact ⟨y, hy, hx.symm.trans (add_comm z y)⟩
  rw [hdom] at hx ⊢
  have hbound := hCE d hd (aCutoff M n omega) law hD.1
    (Section7Process.timeScale (ahom M)) A hA (z, (3 : ℝ) ^ m) hQ hclock hm0 hmT hSob
    hkilled x hx
  have hAnonneg : 0 ≤ A ^ CE := Real.rpow_nonneg (le_trans zero_le_one hA) CE
  have hCA : 0 ≤ CE * A ^ CE := mul_nonneg (le_of_lt hCE0) hAnonneg
  have hstep : CE * A ^ CE * Section7Process.timeScale (ahom M) ((3 : ℝ) ^ m) ≤
      (max 1 (2 * CE * A ^ CE)) * ((3 : ℝ) ^ m) ^ 2 /
        (if J ≤ n then ahom M n else 1) := by
    calc CE * A ^ CE * Section7Process.timeScale (ahom M) ((3 : ℝ) ^ m)
        ≤ CE * A ^ CE * (2 * ((3 : ℝ) ^ m) ^ 2 / (if J ≤ n then ahom M n else 1)) :=
          mul_le_mul_of_nonneg_left hcmp hCA
      _ = (2 * CE * A ^ CE) * ((3 : ℝ) ^ m) ^ 2 / (if J ≤ n then ahom M n else 1) := by
          ring
      _ ≤ (max 1 (2 * CE * A ^ CE)) * ((3 : ℝ) ^ m) ^ 2 /
            (if J ≤ n then ahom M n else 1) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
            (le_of_lt hσpos)
  exact hbound.trans (ENNReal.ofReal_le_ofReal hstep)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
