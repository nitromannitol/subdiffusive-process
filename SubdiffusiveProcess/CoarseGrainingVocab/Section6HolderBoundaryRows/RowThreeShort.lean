module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowThreeShort
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ConclusionAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary.BoundaryNorm

@[expose] public section

/-!
# Boundary Holder row three: the short-gap branch

The short branch is geometric and does not use harmonic approximation or the
excess-decay input.  Unlike the interior version, its statement retains the
datum-bearing boundary summand of `HolderRegularityConclusions`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The short-gap part of the datum-bearing third Holder row. -/
theorem boundaryRowThree_short
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C alpha : ℝ) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (m X : ℕ)
    (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
    (hC : Real.sqrt 3 * (9 : ℝ) ^ (d + 1) ≤ C)
    (halpha : alpha ≤ 1) (hX : 0 < X)
    (hg : MemHolder (cube d m) (1 / 2) g)
    (hh : MemHolder (cube d m) (1 / 2) h.grad) :
    ∀ n : ℕ, (X : ℤ) ≤ (m : ℤ) - (n : ℤ) →
      (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
      ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → ell ≤ n + 2 →
      ∀ x ∈ cube d m,
        excess n (truncatedCube d m n x) u.toFun ≤
          C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) *
              excess ell (truncatedCube d m ell x) u.toFun +
            C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ)) *
              normalizedL2On (truncatedCube d m ell x)
                (fun z ↦ u.toFun z - averageOn (truncatedCube d m ell x) u.toFun) +
            C * (tailAverage M L m omega (cube d m))⁻¹ *
              (3 : ℝ) ^ ((ell : ℝ) / 2) *
              holderSeminormOn (cube d m) (1 / 2) g +
            (if x ∈ cube d (m - 1) then 0 else
              C * ((1 - alpha) * ((m : ℝ) - (n : ℝ)) *
                  vectorSupNormOn (cube d m) h.grad +
                (3 : ℝ) ^ ((ell : ℝ) / 2) *
                  fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                    (1 / 2) h.grad)) := by
  intro n hn _hwindow ell hnell hellm hshort x hx
  have hC0 : (0 : ℝ) ≤ C := le_trans (by positivity) hC
  have hnm : (n : ℤ) - 1 ≤ (m : ℤ) := by
    have hell : (ell : ℤ) ≤ (m : ℤ) := by exact_mod_cast (by omega : ell ≤ m)
    have hne : (n : ℤ) ≤ (ell : ℤ) := by exact_mod_cast hnell
    omega
  have hlm : (ell : ℤ) - 1 ≤ (m : ℤ) := by
    have : (ell : ℤ) ≤ (m : ℤ) := by exact_mod_cast (by omega : ell ≤ m)
    omega
  have hnl : (n : ℤ) ≤ (ell : ℤ) := by exact_mod_cast hnell
  have huWindow : MemLp u.toFun 2
      (volume.restrict (truncatedCube d m ell x)) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedCube_subset_cube d m ell x) le_rfl)
  have hcmp := excess_truncatedCube_le (d := d) (m := (m : ℤ)) (j := (n : ℤ))
    (l := (ell : ℤ)) (x := x) hx hnm hlm hnl (u := u.toFun) huWindow
  have hgap2 : (ell : ℤ) - (n : ℤ) ≤ 2 := by
    have : (ell : ℤ) ≤ (n : ℤ) + 2 := by exact_mod_cast hshort
    omega
  have hfac := Section6HolderInterior.short_factor_le d hgap2
  have hex0 : (0 : ℝ) ≤ excess (ell : ℤ) (truncatedCube d m ell x) u.toFun :=
    excess_nonneg _ _ _
  have hchain : excess (n : ℤ) (truncatedCube d m n x) u.toFun ≤
      (9 : ℝ) ^ (d + 1) * excess (ell : ℤ) (truncatedCube d m ell x) u.toFun :=
    hcmp.trans (mul_le_mul_of_nonneg_right hfac hex0)
  have hcoef := Section6HolderInterior.short_coefficient_ge d hC hnell hshort
  have hmain : excess (n : ℤ) (truncatedCube d m n x) u.toFun ≤
      C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) *
        excess (ell : ℤ) (truncatedCube d m ell x) u.toFun := by
    simpa only [Section6HolderInterior.interiorStepSevenFirstCoefficient] using
      hchain.trans (mul_le_mul_of_nonneg_right hcoef hex0)
  refine hmain.trans ?_
  have hosc0 : 0 ≤ C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ)) *
      normalizedL2On (truncatedCube d m ell x)
        (fun z ↦ u.toFun z - averageOn (truncatedCube d m ell x) u.toFun) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC0 (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by norm_num) _))
      (Section6Iteration.normalizedL2On_nonneg _ _)
  have hforcing0 : 0 ≤ C * (tailAverage M L m omega (cube d m))⁻¹ *
      (3 : ℝ) ^ ((ell : ℝ) / 2) * holderSeminormOn (cube d m) (1 / 2) g := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC0 (inv_nonneg.mpr (tailAverage_nonneg _ _ _ _ _)))
        (Real.rpow_nonneg (by norm_num) _))
      (holderSeminormOn_nonneg hg)
  have hdatum0 : 0 ≤ if x ∈ cube d (m - 1) then 0 else
      C * ((1 - alpha) * ((m : ℝ) - (n : ℝ)) *
          vectorSupNormOn (cube d m) h.grad +
        (3 : ℝ) ^ ((ell : ℝ) / 2) *
          fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) h.grad) := by
    split_ifs
    · exact le_rfl
    · have hnm : (n : ℝ) ≤ (m : ℝ) := by
        have hnZ : (n : ℤ) ≤ (m : ℤ) := by
          have hXZ : (0 : ℤ) < (X : ℤ) := by exact_mod_cast hX
          omega
        exact_mod_cast hnZ
      have hfirst : 0 ≤ (1 - alpha) * ((m : ℝ) - (n : ℝ)) *
          vectorSupNormOn (cube d m) h.grad :=
        mul_nonneg (mul_nonneg (sub_nonneg.mpr halpha) (sub_nonneg.mpr hnm))
          (Section6Holder.vectorSupNormOn_cube_nonneg hh)
      have hsecond : 0 ≤ (3 : ℝ) ^ ((ell : ℝ) / 2) *
          fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) h.grad :=
        mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Section6HolderBoundary.fractionalInfinityNormOn_cube_nonneg hh)
      exact mul_nonneg hC0 (add_nonneg hfirst hsecond)
  linarith only [hosc0, hforcing0, hdatum0]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows
