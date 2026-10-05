module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary.RowOneAbsorption

@[expose] public section

/-!
# Boundary Holder row-one datum budget

This file contains the abstract nonnegative arithmetic that combines the
forcing, accumulated boundary mean, and boundary seminorm terms.  The factor
three is harmless and keeps the proof independent of the concrete constants
chosen by the Campanato ladder.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

noncomputable section

/-- Three nonnegative recurrence terms fit one forcing-plus-boundary slot.
The mean term uses `lambda * (gap + 1) <= 1 + lambda * gap`; the other two
terms use `1 <= exponential`. -/
theorem boundaryRowOne_dataBudget_le
    {K Aforce Amean Abound lambda gap exponential scale forcing boundary
      supTerm seminormTerm : ℝ}
    (hK : 0 ≤ K) (hAmean0 : 0 ≤ Amean) (hAbound0 : 0 ≤ Abound)
    (hAforce : Aforce ≤ K) (hAmean : Amean ≤ K)
    (hAbound : Abound ≤ K) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hgap : 0 ≤ gap) (hexponential : 1 ≤ exponential)
    (hscale : 0 ≤ scale) (hforcing : 0 ≤ forcing) (hboundary : 0 ≤ boundary)
    (hsupBound : supTerm ≤ scale * boundary)
    (hseminormBound : seminormTerm ≤ boundary) :
    Aforce * exponential * (scale * forcing) +
        Amean * lambda * (gap + 1) * supTerm +
        Abound * (scale * seminormTerm) ≤
      3 * K * ((1 + lambda * gap) * exponential) *
        (scale * (forcing + boundary)) := by
  have hlinear1 : 1 ≤ 1 + lambda * gap := by
    exact le_add_of_nonneg_right (mul_nonneg hlambda0 hgap)
  have hlambdaGap : lambda * (gap + 1) ≤ 1 + lambda * gap := by
    nlinarith only [hlambda1]
  have hexponential0 : 0 ≤ exponential := by linarith
  have hlinear0 : 0 ≤ 1 + lambda * gap := zero_le_one.trans hlinear1
  have hproduct1 : 1 ≤ (1 + lambda * gap) * exponential := by
    calc
      1 ≤ 1 + lambda * gap := hlinear1
      _ ≤ (1 + lambda * gap) * exponential := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hexponential hlinear0
  have hKforce : 0 ≤ K * ((1 + lambda * gap) * exponential) := by positivity
  have hdata : 0 ≤ scale * (forcing + boundary) := by positivity
  have hforceTerm : Aforce * exponential * (scale * forcing) ≤
      K * ((1 + lambda * gap) * exponential) * (scale * (forcing + boundary)) := by
    have hcoef : Aforce * exponential ≤
        K * ((1 + lambda * gap) * exponential) := by
      calc
        Aforce * exponential ≤ K * exponential :=
          mul_le_mul_of_nonneg_right hAforce hexponential0
        _ ≤ K * ((1 + lambda * gap) * exponential) := by
          apply mul_le_mul_of_nonneg_left _ hK
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hlinear1 hexponential0
    have hslot : 0 ≤ scale * forcing := mul_nonneg hscale hforcing
    exact (mul_le_mul_of_nonneg_right hcoef hslot).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hboundary) hscale)
        hKforce)
  have hmeanTerm : Amean * lambda * (gap + 1) * supTerm ≤
      K * ((1 + lambda * gap) * exponential) * (scale * (forcing + boundary)) := by
    have hcoef : Amean * (lambda * (gap + 1)) ≤
        K * ((1 + lambda * gap) * exponential) := by
      calc
        Amean * (lambda * (gap + 1)) ≤ Amean * (1 + lambda * gap) :=
          mul_le_mul_of_nonneg_left hlambdaGap hAmean0
        _ ≤ K * (1 + lambda * gap) :=
          mul_le_mul_of_nonneg_right hAmean hlinear0
        _ ≤ K * ((1 + lambda * gap) * exponential) := by
          apply mul_le_mul_of_nonneg_left _ hK
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hexponential hlinear0
    have hcoef0 : 0 ≤ Amean * (lambda * (gap + 1)) := by positivity
    calc
      Amean * lambda * (gap + 1) * supTerm =
          (Amean * (lambda * (gap + 1))) * supTerm := by ring
      _ ≤ (Amean * (lambda * (gap + 1))) * (scale * boundary) :=
        mul_le_mul_of_nonneg_left hsupBound hcoef0
      _ ≤ K * ((1 + lambda * gap) * exponential) * (scale * boundary) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hscale hboundary)
      _ ≤ K * ((1 + lambda * gap) * exponential) *
          (scale * (forcing + boundary)) := by
        apply mul_le_mul_of_nonneg_left _ hKforce
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hforcing) hscale
  have hboundaryTerm : Abound * (scale * seminormTerm) ≤
      K * ((1 + lambda * gap) * exponential) * (scale * (forcing + boundary)) := by
    have hcoef : Abound ≤ K * ((1 + lambda * gap) * exponential) := by
      calc
        Abound ≤ K := hAbound
        _ ≤ K * ((1 + lambda * gap) * exponential) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hproduct1 hK
    calc
      Abound * (scale * seminormTerm) ≤ Abound * (scale * boundary) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hseminormBound hscale) hAbound0
      _ ≤ K * ((1 + lambda * gap) * exponential) * (scale * boundary) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hscale hboundary)
      _ ≤ K * ((1 + lambda * gap) * exponential) *
          (scale * (forcing + boundary)) := by
        apply mul_le_mul_of_nonneg_left _ hKforce
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hforcing) hscale
  linarith only [hforceTerm, hmeanTerm, hboundaryTerm, hKforce, hdata]

/-- The preceding budget in the boundary-datum carrier.  A local
boundary-touch indicator bounded by the outside-cell indicator prices
both the gradient supremum and its Holder seminorm by the single
`fractionalInfinityNormOnReal` term. -/
theorem boundaryRowOne_dataBudget_le_fractionalInfinityNormOn
    {d : ℕ} [NeZero d] {m : ℤ} {f : Vec d → Vec d}
    (hf : MemHolder (cube d m) (1 / 2) f)
    {K Aforce Amean Abound lambda gap exponential forcing
      boundaryIndicator outsideIndicator : ℝ}
    (hK : 0 ≤ K) (hAmean0 : 0 ≤ Amean) (hAbound0 : 0 ≤ Abound)
    (hAforce : Aforce ≤ K) (hAmean : Amean ≤ K) (hAbound : Abound ≤ K)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) (hgap : 0 ≤ gap)
    (hexponential : 1 ≤ exponential) (hforcing : 0 ≤ forcing)
    (hboundaryIndicator : 0 ≤ boundaryIndicator)
    (houtsideIndicator : 0 ≤ outsideIndicator)
    (hindicator : boundaryIndicator ≤ outsideIndicator) :
    Aforce * exponential * ((3 : ℝ) ^ ((m : ℝ) / 2) * forcing) +
        Amean * lambda * (gap + 1) *
          (vectorSupNormOn (cube d m) f * boundaryIndicator) +
        Abound * ((3 : ℝ) ^ ((m : ℝ) / 2) *
          (holderSeminormOn (cube d m) (1 / 2) f * boundaryIndicator)) ≤
      3 * K * ((1 + lambda * gap) * exponential) *
        ((3 : ℝ) ^ ((m : ℝ) / 2) *
          (forcing + outsideIndicator *
            fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) f)) := by
  have hnorm0 : 0 ≤
      fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) f :=
    fractionalInfinityNormOn_cube_nonneg hf
  have hscale0 : 0 ≤ (3 : ℝ) ^ ((m : ℝ) / 2) := by positivity
  have hsupBound :
      vectorSupNormOn (cube d m) f * boundaryIndicator ≤
        (3 : ℝ) ^ ((m : ℝ) / 2) *
          (outsideIndicator *
            fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) f) := by
    calc
      vectorSupNormOn (cube d m) f * boundaryIndicator ≤
          ((3 : ℝ) ^ ((m : ℝ) / 2) *
            fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) f) *
              boundaryIndicator :=
        mul_le_mul_of_nonneg_right
          (vectorSupNormOn_cube_le_scale_mul_fractionalInfinityNormOn hf)
          hboundaryIndicator
      _ ≤ ((3 : ℝ) ^ ((m : ℝ) / 2) *
            fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) f) *
              outsideIndicator :=
        mul_le_mul_of_nonneg_left hindicator (mul_nonneg hscale0 hnorm0)
      _ = (3 : ℝ) ^ ((m : ℝ) / 2) *
          (outsideIndicator *
            fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) f) := by ring
  have hseminormBound :
      holderSeminormOn (cube d m) (1 / 2) f * boundaryIndicator ≤
        outsideIndicator *
          fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) f := by
    calc
      holderSeminormOn (cube d m) (1 / 2) f * boundaryIndicator ≤
          fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) f *
            boundaryIndicator :=
        mul_le_mul_of_nonneg_right
          (holderSeminormOn_cube_le_fractionalInfinityNormOn hf)
          hboundaryIndicator
      _ ≤ fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) f *
          outsideIndicator := mul_le_mul_of_nonneg_left hindicator hnorm0
      _ = outsideIndicator *
          fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) f := mul_comm _ _
  exact boundaryRowOne_dataBudget_le hK hAmean0 hAbound0 hAforce hAmean hAbound
    hlambda0 hlambda1 hgap hexponential hscale0 hforcing
    (mul_nonneg houtsideIndicator hnorm0) hsupBound hseminormBound

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary
