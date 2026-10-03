module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.AnnularLocalization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.GoodScaleSaturation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.GoodEventCap
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.RawErrorFiniteness

@[expose] public section

/-!
# Theta-perturbed ladder: the finite-cutoff paper-error identity

The ordinary good-scale API bounds the real-valued Section 6 error, whereas
the product comparator consumes the underlying `ENNReal` paper error.  Below
the cutoff the existing uncut identity applies.  Above the cutoff the landed
annular budget proves finiteness, after which the same raw-to-real identity
applies.  This module packages that two-branch conversion.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- On a finite-cutoff good event, the finite-two paper error is literally the
`ofReal` of `section6HomogenizationError`, at every translated centre and on
both sides of the cutoff. -/
theorem paperHomogenizationError_eq_ofReal_cutoffGoodEvent
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (L m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hgood : omega ∈ goodEvent M (some L) m z epsilon s) :
    paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) s
        .infinity (.finite 2)
        (aCutoffFamily M L (translatePotentialSample z omega))
        (tailCoefficientCubeAverage M L m (translatePotentialSample z omega)) =
      ENNReal.ofReal (section6HomogenizationError M s L m omega z) := by
  rcases le_or_gt m L with hmL | hLm
  · have hgoodOneSome : omega ∈ goodEvent M (some L) m z 1 s :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.goodEvent_mono hepsilon0
        hepsilon1 hgood
    have hgoodOneNone : omega ∈ goodEvent M none m z 1 s :=
      (mem_goodEvent_some_iff_none_of_scale_le_cutoff
        M hmL z 1 s omega).1 hgoodOneSome
    exact paperHomogenizationError_eq_ofReal_section6HomogenizationError_of_goodEvent
      M hsLower hsUpper hmL omega z hgoodOneNone
  · let nu := translatePotentialSample z omega
    have hgood0 : nu ∈ goodEvent M (some L) m 0 epsilon s :=
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.mem_goodEvent_iff_translate_zero
        M (some L) m epsilon s z omega).mp hgood
    have hbudget := annularSupTwo_le_cutoffGoodScaleBudget M hLm.le hepsilon0
      hepsilon1 hsLower hsUpper nu hgood0
    have hfinite0 : annularSupTwo s (m : ℤ)
        (section6LocalProbeMax M L nu 0
          (tailCoefficientCubeAverage M L m nu)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbudget
    have hlocal : section6LocalProbeMax M L nu 0
          (tailCoefficientCubeAverage M L m nu) =
        section6LocalProbeMax M L omega z
          (tailCoefficientCubeAverage M L m (translatePotentialSample z omega)) := by
      funext R
      simp only [nu, section6LocalProbeMax,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.translatePotentialSample_zero]
    have hfinite : annularSupTwo s (m : ℤ)
        (section6LocalProbeMax M L omega z
          (tailCoefficientCubeAverage M L m
            (translatePotentialSample z omega))) ≠ ⊤ := by
      rw [← hlocal]
      exact hfinite0
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (sq_pos_of_pos M.shellPrefix.delta_pos)).trans_le hsLower
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    exact
      paperHomogenizationError_eq_ofReal_section6HomogenizationError_of_annular_ne_top
        hs0 hsUpper hd1 M L m omega z hfinite

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
