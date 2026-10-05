module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary.RowOneShared
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.WindowMean

@[expose] public section

/-!
# Boundary Holder datum carrier

The boundary Campanato recurrence has two datum terms: the top-cube Holder
seminorm of the datum gradient and its top-cube supremum.  The rows use
their sum in the single normalized `fractionalInfinityNormOnReal` carrier.

This module proves the two component bounds at the paper's length
`ell = 3^m` and order `s = 1/2`.  They are deterministic and use only the
`MemHolder` guard already present in the theorem.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

noncomputable section

variable {d : ℕ}

/-- The explicit Holder seminorm is the first nonnegative component of the
fractional-infinity norm. -/
theorem holderSeminormOn_cube_le_fractionalInfinityNormOn
    [NeZero d] {m : ℤ} {f : Vec d → Vec d} (hf : MemHolder (cube d m) (1 / 2) f) :
    holderSeminormOn (cube d m) (1 / 2) f ≤
      fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) f := by
  rw [fractionalInfinityNormOnReal_eq_of_bddAbove (by positivity)
    (bddAbove_holderQuotients_of_memHolder hf)
    (bddAbove_vectorValues_cube_of_memHolder hf)]
  exact le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (vectorSupNormOn_cube_nonneg hf))

/-- The supremum component, with the normalization undone. -/
theorem vectorSupNormOn_cube_le_scale_mul_fractionalInfinityNormOn
    [NeZero d] {m : ℤ} {f : Vec d → Vec d} (hf : MemHolder (cube d m) (1 / 2) f) :
    vectorSupNormOn (cube d m) f ≤
      (3 : ℝ) ^ ((m : ℝ) / 2) *
        fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) f := by
  have hsemi : 0 ≤ holderSeminormOn (cube d m) (1 / 2) f :=
    holderSeminormOn_nonneg hf
  have hcomponent :
      ((3 : ℝ) ^ m) ^ (-(1 / 2 : ℝ)) * vectorSupNormOn (cube d m) f ≤
        fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) f := by
    rw [fractionalInfinityNormOnReal_eq_of_bddAbove (by positivity)
    (bddAbove_holderQuotients_of_memHolder hf)
    (bddAbove_vectorValues_cube_of_memHolder hf)]
    exact le_add_of_nonneg_left hsemi
  have hscaled := mul_le_mul_of_nonneg_left hcomponent
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) ((m : ℝ) / 2))
  have hpower : ((3 : ℝ) ^ m) ^ (-(1 / 2 : ℝ)) =
      (3 : ℝ) ^ (-((m : ℝ) / 2)) := by
    rw [← Real.rpow_intCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [hpower] at hscaled
  have hcancel :
      (3 : ℝ) ^ ((m : ℝ) / 2) *
          ((3 : ℝ) ^ (-((m : ℝ) / 2)) * vectorSupNormOn (cube d m) f) =
        vectorSupNormOn (cube d m) f := by
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    norm_num
  rw [hcancel] at hscaled
  exact hscaled

/-- The boundary datum carrier is nonnegative. -/
theorem fractionalInfinityNormOn_cube_nonneg
    [NeZero d] {m : ℤ} {f : Vec d → Vec d} (hf : MemHolder (cube d m) (1 / 2) f) :
    0 ≤ fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) f := by
  exact (holderSeminormOn_nonneg hf).trans
    (holderSeminormOn_cube_le_fractionalInfinityNormOn hf)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary
