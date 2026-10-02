import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary.RowTwoDataPairing
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.WindowMean
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoForcingLeg




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]

/-- Dimension-only coefficient of the fractional boundary-gradient leg. -/
def rowTwoBoundaryFractionalConst (d : ℕ) : ℝ :=
  (interiorFractionalOrder).1 ^ (-2 : ℝ) *
    Section6ExcessDecay.fractionalHolderConst d *
    Real.sqrt (interiorFractionalOrder).1

theorem rowTwoBoundaryFractionalConst_nonneg (d : ℕ) :
    0 ≤ rowTwoBoundaryFractionalConst d := by
  rw [rowTwoBoundaryFractionalConst, interiorFractionalOrder_val]
  have := Section6ExcessDecay.fractionalHolderConst_nonneg d
  positivity

/-- The local affine boundary slope is controlled by the top boundary datum. -/
theorem boundaryRowTwo_meanLeg
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C1 C2 alpha : ℝ)
    (step m n gate L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z x : Vec d)
    (hzgrid : OnTriadicGrid n z) (hz : z ∈ cube d m) (hx : x ∈ cube d (m : ℤ))
    (hstop : (Section6Stopping.measurableHolderStoppingScale M alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (hnm : n < m) (hng : n ≤ gate + 2) (hgm : gate + 2 ≤ m) (hmL : m ≤ L)
    (hlambda0 : 0 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (hlambda1 : Section6Stopping.holderStoppingLambda C1 alpha < 1)
    (hepsilon : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha)
    (hdelta : M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (hh : MemHolder (cube d (m : ℤ)) (1 / 2) h.grad) :
    Real.sqrt (tailAverage M L (gate + 2) omega
        (translatedCube d ((gate : ℤ) + 2) z)) *
        Real.sqrt (vecNormSq
          (averageVecOn (truncatedCube d (m : ℤ) (gate : ℤ) x) h.grad)) ≤
      rowTwoRatioBound d C1 alpha m n *
        ((tailAverage M L m omega (cube d (m : ℤ))) ^ (1 / 2 : ℝ) *
          (3 : ℝ) ^ ((m : ℝ) / 2) *
          fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
            (1 / 2) h.grad) := by
  have hmean := Section6Holder.sqrt_vecNormSq_averageVecOn_truncatedCube_le_vectorSupNormOn_cube
    (j := (gate : ℤ)) h hx (by omega) hh
  have hmul := mul_le_mul_of_nonneg_left hmean (Real.sqrt_nonneg
    (tailAverage M L (gate + 2) omega (translatedCube d ((gate : ℤ) + 2) z)))
  refine hmul.trans ?_
  simpa only [show ((gate + 2 : ℕ) : ℤ) = (gate : ℤ) + 2 by omega] using
    (Section6HolderBoundary.sqrt_tailAverage_mul_vectorSupNorm_le_boundaryDatum
      M C1 C2 alpha step m n (gate + 2) L omega z hzgrid hz hstop hnm hng hgm
      hmL hlambda0 hlambda1 hepsilon hdelta h hh)

/-- The local fractional boundary-gradient square is controlled by the same
top boundary datum. -/
theorem boundaryRowTwo_fractionalLeg
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C1 C2 alpha : ℝ)
    (step m n gate L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z x : Vec d)
    (hzgrid : OnTriadicGrid n z) (hz : z ∈ cube d m) (hx : x ∈ cube d (m : ℤ))
    (hstop : (Section6Stopping.measurableHolderStoppingScale M alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (hnm : n < m) (hng : n ≤ gate + 2) (hgm : gate + 2 ≤ m) (hmL : m ≤ L)
    (hlambda0 : 0 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (hlambda1 : Section6Stopping.holderStoppingLambda C1 alpha < 1)
    (hepsilon : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha)
    (hdelta : M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (hh : MemHolder (cube d (m : ℤ)) (1 / 2) h.grad) :
    Real.sqrt (tailAverage M L (gate + 2) omega
        (translatedCube d ((gate : ℤ) + 2) z)) *
        (interiorFractionalOrder).1 ^ (-2 : ℝ) *
        (3 : ℝ) ^ ((interiorFractionalOrder).1 * (gate : ℝ)) *
        (fractionalSeminormOn (truncatedCube d (m : ℤ) (gate : ℤ) x)
          (interiorFractionalOrder).1 h.grad).toReal ≤
      rowTwoBoundaryFractionalConst d * rowTwoRatioBound d C1 alpha m n *
        ((tailAverage M L m omega (cube d (m : ℤ))) ^ (1 / 2 : ℝ) *
          (3 : ℝ) ^ ((m : ℝ) / 2) *
          fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
            (1 / 2) h.grad) := by
  have hembed := Section6Holder.forcing_fractional_window_le (d := d)
    (m := (m : ℤ)) (j := (gate : ℤ)) (x := x) (g := h.grad)
    (s := (interiorFractionalOrder).1) hx
    (by rw [interiorFractionalOrder_val]; norm_num)
    (by rw [interiorFractionalOrder_val]) hh
  have htop := Section6HolderBoundary.sqrt_tailAverage_mul_topBoundary_le_boundaryDatum
    M C1 C2 alpha step m n (gate + 2) gate L omega z hzgrid hz hstop hnm
    hng hgm (by omega) hmL hlambda0 hlambda1 hepsilon hdelta h hh
  rw [show ((gate + 2 : ℕ) : ℤ) = (gate : ℤ) + 2 by omega] at htop
  have hscale : (3 : ℝ) ^ ((gate : ℝ) / 2) =
      (3 : ℝ) ^ (-(((m : ℝ) - (gate : ℝ)) / 2)) *
        (3 : ℝ) ^ ((m : ℝ) / 2) := by
    simpa only [Int.cast_natCast] using
      Section6Holder.three_half_scale_decay (m : ℤ) (gate : ℤ)
  rw [show (((gate : ℤ) : ℝ)) = (gate : ℝ) by norm_num, hscale] at hembed
  have hcoef : 0 ≤ (interiorFractionalOrder).1 ^ (-2 : ℝ) *
      Section6ExcessDecay.fractionalHolderConst d *
      Real.sqrt (interiorFractionalOrder).1 := by
    exact rowTwoBoundaryFractionalConst_nonneg d
  have hs2 : 0 ≤ (interiorFractionalOrder).1 ^ (-2 : ℝ) := by
    rw [interiorFractionalOrder_val]
    positivity
  have hleft :
      (Real.sqrt (tailAverage M L (gate + 2) omega
          (translatedCube d ((gate : ℤ) + 2) z)) *
        (interiorFractionalOrder).1 ^ (-2 : ℝ)) *
          ((3 : ℝ) ^ ((interiorFractionalOrder).1 * (gate : ℝ)) *
            (fractionalSeminormOn (truncatedCube d (m : ℤ) (gate : ℤ) x)
              (interiorFractionalOrder).1 h.grad).toReal) ≤
        (Real.sqrt (tailAverage M L (gate + 2) omega
          (translatedCube d ((gate : ℤ) + 2) z)) *
        (interiorFractionalOrder).1 ^ (-2 : ℝ)) *
          (Section6ExcessDecay.fractionalHolderConst d *
            Real.sqrt (interiorFractionalOrder).1 *
            ((3 : ℝ) ^ (-(((m : ℝ) - (gate : ℝ)) / 2)) *
              (3 : ℝ) ^ ((m : ℝ) / 2)) *
            holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad) :=
    mul_le_mul_of_nonneg_left hembed
      (mul_nonneg (Real.sqrt_nonneg _) hs2)
  have hright := mul_le_mul_of_nonneg_left htop hcoef
  rw [rowTwoBoundaryFractionalConst]
  calc
    _ ≤ Real.sqrt (tailAverage M L (gate + 2) omega
          (translatedCube d ((gate : ℤ) + 2) z)) *
        (interiorFractionalOrder).1 ^ (-2 : ℝ) *
        (Section6ExcessDecay.fractionalHolderConst d *
          Real.sqrt (interiorFractionalOrder).1 *
          ((3 : ℝ) ^ (-(((m : ℝ) - (gate : ℝ)) / 2)) *
            (3 : ℝ) ^ ((m : ℝ) / 2)) *
          holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad) := by
      convert hleft using 1
      ring
    _ = ((interiorFractionalOrder).1 ^ (-2 : ℝ) *
          Section6ExcessDecay.fractionalHolderConst d *
          Real.sqrt (interiorFractionalOrder).1) *
        (Real.sqrt (tailAverage M L (gate + 2) omega
          (translatedCube d ((gate : ℤ) + 2) z)) *
          ((3 : ℝ) ^ (-(((m : ℝ) - (gate : ℝ)) / 2)) *
            ((3 : ℝ) ^ ((m : ℝ) / 2) *
              holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad))) := by ring
    _ ≤ ((interiorFractionalOrder).1 ^ (-2 : ℝ) *
          Section6ExcessDecay.fractionalHolderConst d *
          Real.sqrt (interiorFractionalOrder).1) *
        (rowTwoRatioBound d C1 alpha m n *
          ((tailAverage M L m omega (cube d (m : ℤ))) ^ (1 / 2 : ℝ) *
            (3 : ℝ) ^ ((m : ℝ) / 2) *
            fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
              (1 / 2) h.grad)) := hright
    _ = _ := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
