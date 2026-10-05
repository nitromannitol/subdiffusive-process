module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoRatioScales

@[expose] public section

/-!
# The defect budget's datum, paired against the frozen datum

The Campanato family's defect budget carries the ladder's forcing carrier
`topForcing = b^{-1} 3^{m/2} [g]`, while the frozen row-2 datum is
`b^{-1/2} 3^{m/2} [g]`.  Multiplying the first by the Step-6 coefficient
`sigma^{1/2}` and using `sigma^{1/2} b^{-1/2} ≤ exp(C lambda (m-n))` turns one
into the other.  This is the same pairing as
`RowTwoRatioScales.sqrt_tailAverage_pairing_at`, read with the domain-scale
average in the denominator slot.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- `sigma^{1/2} b^{-1/2} ≤ exp(C lambda (m-n))`. -/
theorem sqrt_mul_inv_sqrt_tail_le (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (C1 C2 alpha : ℝ) (step m n q L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
    (hzgrid : OnTriadicGrid n z) (hz : z ∈ cube d m)
    (hstop : (Section6Stopping.measurableHolderStoppingScale M alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (hnm : n < m) (hnq : n ≤ q) (hqm : q ≤ m) (hmL : m ≤ L)
    (hlambda0 : 0 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (hlambda1 : Section6Stopping.holderStoppingLambda C1 alpha < 1)
    (hepsilon : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha)
    (hdelta : M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha) :
    Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) *
        (Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹ ≤
      rowTwoRatioBound d C1 alpha m n := by
  have hb : 0 < tailCoefficientCubeAverage M L m omega :=
    tailCoefficientCubeAverage_pos M L m omega
  have hbounds := stoppedRatio_bounds_at M C1 C2 alpha step m n q L omega z
    hzgrid hz hstop hnm hnq hqm hmL hlambda0 hlambda1 hepsilon hdelta
  refine sqrt_tailAverage_pairing
    (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _) hb hb
    (rowTwoRatioBound_nonneg d C1 alpha m n) hbounds.1 ?_
  rw [div_self hb.ne']
  exact one_le_rowTwoRatioBound d hlambda0 (le_of_lt hnm)

/-- **The defect budget's datum against the frozen datum.** -/
theorem rowTwo_data_pairing (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (C1 C2 alpha : ℝ) (step m n q L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
    (hzgrid : OnTriadicGrid n z) (hz : z ∈ cube d m)
    (hstop : (Section6Stopping.measurableHolderStoppingScale M alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (hnm : n < m) (hnq : n ≤ q) (hqm : q ≤ m) (hmL : m ≤ L)
    (hlambda0 : 0 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (hlambda1 : Section6Stopping.holderStoppingLambda C1 alpha < 1)
    (hepsilon : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha)
    (hdelta : M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (g : Vec d → Vec d) (hg : MemHolder (cube d (m : ℤ)) (1 / 2) g) :
    Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) *
        ((tailCoefficientCubeAverage M L m omega)⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) *
          holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) ≤
      rowTwoRatioBound d C1 alpha m n *
        ((tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
          (3 : ℝ) ^ ((m : ℝ) / 2) *
          holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) := by
  have hb : 0 < tailCoefficientCubeAverage M L m omega :=
    tailCoefficientCubeAverage_pos M L m omega
  have hbeq : tailCoefficientCubeAverage M L m omega =
      tailAverage M L m omega (cube d (m : ℤ)) :=
    tailCoefficientCubeAverage_eq_tailAverage_cube M L m omega
  have hb12 : (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) =
      (Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹ := by
    rw [hbeq, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg (by rw [← hbeq]; exact hb.le), ← Real.sqrt_eq_rpow]
  have hbinv : (tailCoefficientCubeAverage M L m omega)⁻¹ =
      (Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹ *
        (Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hb.le]
  have hH0 : 0 ≤ holderSeminormOn (cube d (m : ℤ)) (1 / 2) g :=
    Section6ExcessDecay.holderSeminormOn_nonneg hg
  have hpow0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hrest : (0 : ℝ) ≤ (Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹ *
      (3 : ℝ) ^ ((m : ℝ) / 2) * holderSeminormOn (cube d (m : ℤ)) (1 / 2) g := by
    have h1 : (0 : ℝ) ≤ (Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    positivity
  have hpair := sqrt_mul_inv_sqrt_tail_le M C1 C2 alpha step m n q L omega z hzgrid
    hz hstop hnm hnq hqm hmL hlambda0 hlambda1 hepsilon hdelta
  rw [hb12, hbinv]
  calc Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) *
        ((Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹ *
          (Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹ *
          (3 : ℝ) ^ ((m : ℝ) / 2) *
          holderSeminormOn (cube d (m : ℤ)) (1 / 2) g)
      = (Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)) *
          (Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹) *
          ((Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹ *
            (3 : ℝ) ^ ((m : ℝ) / 2) *
            holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) := by ring
    _ ≤ rowTwoRatioBound d C1 alpha m n *
          ((Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹ *
            (3 : ℝ) ^ ((m : ℝ) / 2) *
            holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) :=
        mul_le_mul_of_nonneg_right hpair hrest

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
