module

public import SubdiffusiveProcess.Paper.inputs_extension_source
public import SubdiffusiveProcess.Paper.inputs_extension_harmonic
public import SubdiffusiveProcess.Paper.inputs_extension_split

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_extension_witness (d : ℕ) (hd : 2 ≤ d) (Jc : Paper.in_J d) :
    (Nonempty (Paper.in_extension d hd Jc)) := by
  obtain ⟨C, hC, hsource⟩ := inputs_extension_source d hd Jc
  obtain ⟨Ch, hCh, hharm⟩ := inputs_extension_harmonic d hd Jc
  refine ⟨⟨max C Ch, lt_max_of_lt_left hC, ?_⟩⟩
  intro z m hr a s hs g hg hDatum v hhfin hweak htrace
  obtain ⟨w, t, hw, ht, htr, htriangle⟩ :=
    inputs_extension_split d hd z m hr a g hDatum v hweak htrace
  have hforce := hsource z m hr a s hs g hg w hw
  have hboundary := hharm z m hr a s hs hDatum t hhfin ht htr
  have hs0 : 0 < s := hs.1
  have hP1 : 0 ≤ s ^ (-3 : ℝ) *
      (Jc.lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ (-(1 / 2) : ℝ) *
        (3 : ℝ) ^ (s * (m : ℝ)) *
        Real.sqrt (cubeFractionalVecSeminormSq hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
          (fun i => g i)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
      (Real.rpow_nonneg (Jc.lam_pos z _ hr a z _ (s / 2) 2).le _))
      (Real.rpow_nonneg (by norm_num) _)) (Real.sqrt_nonneg _)
  have hP2 : 0 ≤ s ^ (-(3 / 2) : ℝ) *
      (Jc.Lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ ((1 / 2) : ℝ) *
        (3 : ℝ) ^ (s * (m : ℝ)) *
        cubeFractionalL2Norm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
          ⟨fun i => sobolevGradient (hDatum : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) i,
            lt_top_iff_ne_top.2 hhfin⟩ := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
      (Real.rpow_nonneg (Jc.Lam_pos z _ hr a z _ (s / 2) 2).le _))
      (Real.rpow_nonneg (by norm_num) _)) ?_
    unfold cubeFractionalL2Norm
    exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg
      (Real.rpow_nonneg (by positivity) _) (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  refine htriangle.trans (add_le_add ?_ ?_)
  · calc _ ≤ C * (s ^ (-3 : ℝ) *
          (Jc.lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ (-(1 / 2) : ℝ) *
            (3 : ℝ) ^ (s * (m : ℝ)) *
            Real.sqrt (cubeFractionalVecSeminormSq hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
              (fun i => g i))) := by
          refine hforce.trans (le_of_eq ?_)
          ring
      _ ≤ max C Ch * (s ^ (-3 : ℝ) *
          (Jc.lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ (-(1 / 2) : ℝ) *
            (3 : ℝ) ^ (s * (m : ℝ)) *
            Real.sqrt (cubeFractionalVecSeminormSq hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
              (fun i => g i))) := mul_le_mul_of_nonneg_right (le_max_left _ _) hP1
      _ = _ := by ring
  · calc _ ≤ Ch * (s ^ (-(3 / 2) : ℝ) *
          (Jc.Lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ ((1 / 2) : ℝ) *
            (3 : ℝ) ^ (s * (m : ℝ)) *
            cubeFractionalL2Norm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
              ⟨fun i => sobolevGradient (hDatum : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) i,
                lt_top_iff_ne_top.2 hhfin⟩) := by
          refine hboundary.trans (le_of_eq ?_)
          ring
      _ ≤ max C Ch * (s ^ (-(3 / 2) : ℝ) *
          (Jc.Lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ ((1 / 2) : ℝ) *
            (3 : ℝ) ^ (s * (m : ℝ)) *
            cubeFractionalL2Norm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
              ⟨fun i => sobolevGradient (hDatum : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) i,
                lt_top_iff_ne_top.2 hhfin⟩) := mul_le_mul_of_nonneg_right (le_max_right _ _) hP2
      _ = _ := by ring

end Paper
