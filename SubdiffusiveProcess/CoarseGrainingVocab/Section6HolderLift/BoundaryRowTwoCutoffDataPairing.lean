import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary.BoundaryNorm
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowTwoDataPairing

/-!
# Boundary row-two datum pairings

The datum-bearing Campanato recurrence has a supremum term and a Hölder
seminorm term.  After multiplication by the local tail-average square root,
both are bounded by the single datum carrier printed in row two.  The only
stochastic price is the same stopped tail ratio used by the forcing datum.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]

/-- The local tail square root paired with the datum-gradient supremum. -/
theorem sqrt_tailAverage_mul_vectorSupNorm_le_boundaryDatum_cutoff
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C1 C2 alpha : ℝ)
    (step m n q L : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (z : Vec d) (hzgrid : OnTriadicGrid n z) (hz : z ∈ cube d m)
    (hstop : (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (hnm : n < m) (hnq : n ≤ q) (hqm : q ≤ m)
    (hlambda0 : 0 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (hlambda1 : Section6Stopping.holderStoppingLambda C1 alpha < 1)
    (hepsilon : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha)
    (hdelta : M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (hh : MemHolder (cube d (m : ℤ)) (1 / 2) h.grad) :
    Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) *
        vectorSupNormOn (cube d (m : ℤ)) h.grad ≤
      rowTwoRatioBound_cut d C1 alpha m n *
        ((tailAverage M L m omega (cube d (m : ℤ))) ^ (1 / 2 : ℝ) *
          (3 : ℝ) ^ ((m : ℝ) / 2) *
          fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
            (1 / 2) h.grad) := by
  have hb : 0 < tailCoefficientCubeAverage M L m omega :=
    tailCoefficientCubeAverage_pos M L m omega
  have hbeq : tailCoefficientCubeAverage M L m omega =
      tailAverage M L m omega (cube d (m : ℤ)) :=
    tailCoefficientCubeAverage_eq_tailAverage_cube M L m omega
  have hpair := sqrt_mul_inv_sqrt_tail_le_cut M C1 C2 alpha step m n q L omega z
    hzgrid hz hstop hnm hnq hqm hlambda0 hlambda1 hepsilon hdelta
  have hrootb : 0 < Real.sqrt (tailCoefficientCubeAverage M L m omega) :=
    Real.sqrt_pos.2 hb
  have hsigma : Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) ≤
      rowTwoRatioBound_cut d C1 alpha m n *
        Real.sqrt (tailCoefficientCubeAverage M L m omega) := by
    calc
      Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) =
          (Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) *
            (Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹) *
              Real.sqrt (tailCoefficientCubeAverage M L m omega) := by
            field_simp
      _ ≤ rowTwoRatioBound_cut d C1 alpha m n *
            Real.sqrt (tailCoefficientCubeAverage M L m omega) :=
        mul_le_mul_of_nonneg_right hpair hrootb.le
  have hsup := vectorSupNormOn_cube_le_scale_mul_fractionalInfinityNormOn hh
  have hsup0 : 0 ≤ vectorSupNormOn (cube d (m : ℤ)) h.grad :=
    Section6Holder.vectorSupNormOn_cube_nonneg hh
  have hright0 : 0 ≤ (3 : ℝ) ^ ((m : ℝ) / 2) *
      fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
        (1 / 2) h.grad := by
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (fractionalInfinityNormOn_cube_nonneg hh)
  have hmul := mul_le_mul hsigma hsup hsup0
    (mul_nonneg (rowTwoRatioBound_nonneg_cut d C1 alpha m n) hrootb.le)
  rw [← hbeq, ← Real.sqrt_eq_rpow]
  calc
    Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) *
        vectorSupNormOn (cube d (m : ℤ)) h.grad
      ≤ (rowTwoRatioBound_cut d C1 alpha m n *
          Real.sqrt (tailCoefficientCubeAverage M L m omega)) *
        ((3 : ℝ) ^ ((m : ℝ) / 2) *
          fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
            (1 / 2) h.grad) := hmul
    _ = rowTwoRatioBound_cut d C1 alpha m n *
        (Real.sqrt (tailCoefficientCubeAverage M L m omega) *
          (3 : ℝ) ^ ((m : ℝ) / 2) *
          fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
            (1 / 2) h.grad) := by ring

/-- The top-window boundary seminorm paired with the local tail square root. -/
theorem sqrt_tailAverage_mul_topBoundary_le_boundaryDatum_cutoff
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C1 C2 alpha : ℝ)
    (step m n q top L : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (z : Vec d) (hzgrid : OnTriadicGrid n z) (hz : z ∈ cube d m)
    (hstop : (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (hnm : n < m) (hnq : n ≤ q) (hqm : q ≤ m) (htopm : top ≤ m)

    (hlambda0 : 0 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (hlambda1 : Section6Stopping.holderStoppingLambda C1 alpha < 1)
    (hepsilon : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha)
    (hdelta : M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (hh : MemHolder (cube d (m : ℤ)) (1 / 2) h.grad) :
    Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) *
        ((3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) *
            holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad)) ≤
      rowTwoRatioBound_cut d C1 alpha m n *
        ((tailAverage M L m omega (cube d (m : ℤ))) ^ (1 / 2 : ℝ) *
          (3 : ℝ) ^ ((m : ℝ) / 2) *
          fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
            (1 / 2) h.grad) := by
  have hsemi := holderSeminormOn_cube_le_fractionalInfinityNormOn hh
  have ht : (3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    simp only [neg_nonpos]
    have htopmR : (top : ℝ) ≤ (m : ℝ) := by exact_mod_cast htopm
    linarith
  have hlocal0 : 0 ≤ Real.sqrt
      (tailAverage M L q omega (translatedCube d (q : ℕ) z)) := Real.sqrt_nonneg _
  have hpowm0 : 0 ≤ (3 : ℝ) ^ ((m : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hsemi0 : 0 ≤ holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad :=
    Section6ExcessDecay.holderSeminormOn_nonneg hh
  have hfrac0 := fractionalInfinityNormOn_cube_nonneg hh
  have hleft :
      Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) *
          ((3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) *
            ((3 : ℝ) ^ ((m : ℝ) / 2) *
              holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad)) ≤
        Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) *
            fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
              (1 / 2) h.grad) := by
    calc
      _ = (Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) *
            (3 : ℝ) ^ (-(((m : ℝ) - (top : ℝ)) / 2)) *
              (3 : ℝ) ^ ((m : ℝ) / 2)) *
            holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad := by ring
      _ ≤ (Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) *
            1 * (3 : ℝ) ^ ((m : ℝ) / 2)) *
            holderSeminormOn (cube d (m : ℤ)) (1 / 2) h.grad := by
          gcongr
      _ ≤ (Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) *
            1 * (3 : ℝ) ^ ((m : ℝ) / 2)) *
            fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
              (1 / 2) h.grad := by
          exact mul_le_mul_of_nonneg_left hsemi (by positivity)
      _ = _ := by ring
  -- Use the same tail pairing as the supremum row, now with the seminorm
  -- component of the frozen boundary norm.
  have hb : 0 < tailCoefficientCubeAverage M L m omega :=
    tailCoefficientCubeAverage_pos M L m omega
  have hbeq : tailCoefficientCubeAverage M L m omega =
      tailAverage M L m omega (cube d (m : ℤ)) :=
    tailCoefficientCubeAverage_eq_tailAverage_cube M L m omega
  have hpair := sqrt_mul_inv_sqrt_tail_le_cut M C1 C2 alpha step m n q L omega z
    hzgrid hz hstop hnm hnq hqm hlambda0 hlambda1 hepsilon hdelta
  have hrootb : 0 < Real.sqrt (tailCoefficientCubeAverage M L m omega) :=
    Real.sqrt_pos.2 hb
  have hsigma : Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) ≤
      rowTwoRatioBound_cut d C1 alpha m n *
        Real.sqrt (tailCoefficientCubeAverage M L m omega) := by
    calc
      Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) =
          (Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) *
            (Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹) *
              Real.sqrt (tailCoefficientCubeAverage M L m omega) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hpair hrootb.le
  calc
    _ ≤ Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) *
          ((3 : ℝ) ^ ((m : ℝ) / 2) *
            fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
              (1 / 2) h.grad) := hleft
    _ ≤ (rowTwoRatioBound_cut d C1 alpha m n *
          Real.sqrt (tailCoefficientCubeAverage M L m omega)) *
        ((3 : ℝ) ^ ((m : ℝ) / 2) *
          fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
            (1 / 2) h.grad) :=
      mul_le_mul_of_nonneg_right hsigma (mul_nonneg hpowm0 hfrac0)
    _ = _ := by
      rw [hbeq, ← Real.sqrt_eq_rpow]
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
