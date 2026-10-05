module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.DescentPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.StepSeven

@[expose] public section

/-!
# Row 3, short range: `ell ≤ n + 2`

`interiorStepSeven_of_short_and_scaledGrid` splits row 3 at `ell = n + 2`.  In
the short branch the two windows are within two scales of each other, so there is
no decay to extract and the estimate is a pure **volume-ratio** comparison:
`Section6ExcessDecay.excess_truncatedCube_le` gives

```text
  excess n (U_n) u ≤ 3 ^ (ell - n) * sqrt ((3 ^ (ell - n + 2)) ^ d) *
                       excess ell (U_ell) u ,
```

whose factor is `3 ^ gap * scaleTransferPrice d gap` — the same price object as
the row-2 descent.  Over `0 ≤ gap ≤ 2` it is at most `9 ^ (d + 1)`, while the
target coefficient `interiorStepSevenFirstCoefficient C n ell = C * 3 ^ (-gap/4)`
is at least `C / sqrt 3`.  So the branch closes as soon as

```text
  C ≥ sqrt 3 * 9 ^ (d + 1) ,
```

a **dimension-only** lower bound on the constant, recorded in the constant
table.  The other two summands of row 3 are nonnegative and are simply dropped.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Over a two-scale gap the comparison factor is at most `9 ^ (d + 1)`. -/
theorem short_factor_le (d : ℕ) {gap : ℤ} (h2 : gap ≤ 2) :
    (3 : ℝ) ^ gap * Real.sqrt (((3 : ℝ) ^ (gap + 2)) ^ d) ≤ (9 : ℝ) ^ (d + 1) := by
  have h1 : (1 : ℝ) ≤ 3 := by norm_num
  have hz : (3 : ℝ) ^ gap ≤ (3 : ℝ) ^ (2 : ℤ) := zpow_le_zpow_right₀ h1 h2
  have hz' : (3 : ℝ) ^ gap ≤ 9 := by
    have : (3 : ℝ) ^ (2 : ℤ) = 9 := by norm_num
    linarith [hz, this.ge, this.le]
  have hprice : Real.sqrt (((3 : ℝ) ^ (gap + 2)) ^ d) ≤ (9 : ℝ) ^ d := by
    have heq : Real.sqrt (((3 : ℝ) ^ (gap + 2)) ^ d) =
        (3 : ℝ) ^ ((((gap : ℝ) + 2) * (d : ℝ)) / 2) := by
      have := scaleTransferPrice_eq_rpow d gap
      unfold scaleTransferPrice at this
      exact this
    rw [heq]
    have hexp : (((gap : ℝ) + 2) * (d : ℝ)) / 2 ≤ 2 * (d : ℝ) := by
      have hg : (gap : ℝ) ≤ 2 := by exact_mod_cast h2
      have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      nlinarith only [hg, hd]
    refine (Real.rpow_le_rpow_of_exponent_le h1 hexp).trans ?_
    have h9 : (9 : ℝ) ^ d = (3 : ℝ) ^ (2 * (d : ℝ)) := by
      rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast
        ((3 : ℝ) ^ (2 : ℕ)) d, ← Real.rpow_natCast (3 : ℝ) 2, ← Real.rpow_mul
        (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    exact le_of_eq h9.symm
  have hz0 : (0 : ℝ) ≤ (3 : ℝ) ^ gap := le_of_lt (zpow_pos (by norm_num) _)
  have hp0 : (0 : ℝ) ≤ Real.sqrt (((3 : ℝ) ^ (gap + 2)) ^ d) := Real.sqrt_nonneg _
  have h9d : (0 : ℝ) ≤ (9 : ℝ) ^ d := by positivity
  calc (3 : ℝ) ^ gap * Real.sqrt (((3 : ℝ) ^ (gap + 2)) ^ d)
      ≤ 9 * (9 : ℝ) ^ d := by
        exact mul_le_mul hz' hprice hp0 (by norm_num)
    _ = (9 : ℝ) ^ (d + 1) := by ring

/-- Over a two-scale gap the target coefficient is at least `C / sqrt 3`, hence
at least `9 ^ (d + 1)` under the dimension-only constant condition. -/
theorem short_coefficient_ge (d : ℕ) {C : ℝ} {n ell : ℕ}
    (hC : Real.sqrt 3 * (9 : ℝ) ^ (d + 1) ≤ C)
    (hne : n ≤ ell) (h2 : ell ≤ n + 2) :
    (9 : ℝ) ^ (d + 1) ≤ interiorStepSevenFirstCoefficient C n ell := by
  have h1 : (1 : ℝ) ≤ 3 := by norm_num
  have hgap : ((ell : ℝ) - (n : ℝ)) ≤ 2 := by
    have : (ell : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast h2
    linarith
  have hgap0 : (0 : ℝ) ≤ ((ell : ℝ) - (n : ℝ)) := by
    have : (n : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hne
    linarith
  have hexp : (-(1 : ℝ) / 2) ≤ -((ell : ℝ) - (n : ℝ)) / 4 := by linarith
  have hmono : (3 : ℝ) ^ (-(1 : ℝ) / 2) ≤
      (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) :=
    Real.rpow_le_rpow_of_exponent_le h1 hexp
  have hsqrt3 : (3 : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt 3)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h9 : (0 : ℝ) ≤ (9 : ℝ) ^ (d + 1) := by positivity
  have hstep : (9 : ℝ) ^ (d + 1) ≤ C * (Real.sqrt 3)⁻¹ := by
    rw [le_mul_inv_iff₀ hs3]
    linarith [hC]
  have hC0 : (0 : ℝ) ≤ C := le_trans (by positivity) hC
  unfold interiorStepSevenFirstCoefficient
  refine hstep.trans ?_
  rw [← hsqrt3]
  exact mul_le_mul_of_nonneg_left hmono hC0

/-- **Row 3's short branch, discharged.**  This is exactly the `hshort`
hypothesis of `interiorStepSeven_of_short_and_scaledGrid`, under the
dimension-only constant condition `C ≥ sqrt 3 * 9 ^ (d + 1)`. -/
theorem interiorRowThree_short (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (C alpha : ℝ) (L : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (m X : ℕ) (u : H1Function (openCubeSet (originCube d m)))
    (g : Vec d → Vec d)
    (hC : Real.sqrt 3 * (9 : ℝ) ^ (d + 1) ≤ C)
    (hg : MemHolder (cube d m) (1 / 2) g) :
    ∀ n : ℕ, (X : ℤ) ≤ (m : ℤ) - (n : ℤ) →
      (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
      ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → ell ≤ n + 2 →
      ∀ x ∈ cube d ((m : ℤ) - 1),
        excess n (truncatedCube d m n x) u.toFun ≤
          interiorStepSevenFirstCoefficient C n ell *
              excess ell (truncatedCube d m ell x) u.toFun +
            interiorStepSevenOscillationCoefficient C alpha ell *
              normalizedL2On (truncatedCube d m ell x)
                (fun z ↦ u.toFun z -
                  averageOn (truncatedCube d m ell x) u.toFun) +
            interiorStepSevenRemainder M C L omega m ell g := by
  intro n _hn _hwindow ell hnell hellm hshort x hx
  have hC0 : (0 : ℝ) ≤ C := le_trans (by positivity) hC
  have hxm : x ∈ cube d (m : ℤ) := mem_cube_of_mem_cube_sub_one hx
  have hnm : (n : ℤ) - 1 ≤ (m : ℤ) := by
    have : (ell : ℤ) ≤ (m : ℤ) := by exact_mod_cast (by omega : ell ≤ m)
    have hn : (n : ℤ) ≤ (ell : ℤ) := by exact_mod_cast hnell
    omega
  have hlm : (ell : ℤ) - 1 ≤ (m : ℤ) := by
    have : (ell : ℤ) ≤ (m : ℤ) := by exact_mod_cast (by omega : ell ≤ m)
    omega
  have hnl : (n : ℤ) ≤ (ell : ℤ) := by exact_mod_cast hnell
  have huWindow : MemLp u.toFun 2
      (volume.restrict (truncatedCube d m ell x)) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedCube_subset_cube d m ell x) le_rfl)
  -- the volume-ratio comparison
  have hcmp := excess_truncatedCube_le (d := d) (m := (m : ℤ)) (j := (n : ℤ))
    (l := (ell : ℤ)) (x := x) hxm hnm hlm hnl (u := u.toFun) huWindow
  -- its factor is at most `9 ^ (d + 1)`
  have hgap2 : (ell : ℤ) - (n : ℤ) ≤ 2 := by
    have : (ell : ℤ) ≤ (n : ℤ) + 2 := by exact_mod_cast (by omega : ell ≤ n + 2)
    omega
  have hfac := short_factor_le d (gap := (ell : ℤ) - (n : ℤ)) hgap2
  have hex0 : (0 : ℝ) ≤ excess (ell : ℤ) (truncatedCube d m ell x) u.toFun :=
    excess_nonneg _ _ _
  have hchain : excess (n : ℤ) (truncatedCube d m n x) u.toFun ≤
      (9 : ℝ) ^ (d + 1) * excess (ell : ℤ) (truncatedCube d m ell x) u.toFun :=
    hcmp.trans (mul_le_mul_of_nonneg_right hfac hex0)
  -- and `9 ^ (d + 1)` is below the target coefficient
  have hcoef := short_coefficient_ge d hC hnell hshort
  have hmain : excess (n : ℤ) (truncatedCube d m n x) u.toFun ≤
      interiorStepSevenFirstCoefficient C n ell *
        excess (ell : ℤ) (truncatedCube d m ell x) u.toFun :=
    hchain.trans (mul_le_mul_of_nonneg_right hcoef hex0)
  -- the remaining two summands are nonnegative
  have hosc0 : (0 : ℝ) ≤ interiorStepSevenOscillationCoefficient C alpha ell *
      normalizedL2On (truncatedCube d m ell x)
        (fun z ↦ u.toFun z - averageOn (truncatedCube d m ell x) u.toFun) := by
    refine mul_nonneg ?_ (Section6Iteration.normalizedL2On_nonneg _ _)
    unfold interiorStepSevenOscillationCoefficient
    exact mul_nonneg (mul_nonneg hC0 (Real.sqrt_nonneg _))
      (Real.rpow_nonneg (by norm_num) _)
  have hrem0 : (0 : ℝ) ≤ interiorStepSevenRemainder M C L omega m ell g := by
    unfold interiorStepSevenRemainder
    refine mul_nonneg (mul_nonneg (mul_nonneg hC0 ?_) ?_) ?_
    · exact inv_nonneg.2 (tailAverage_nonneg _ _ _ _ _)
    · exact Real.rpow_nonneg (by norm_num) _
    · exact Section6ExcessDecay.holderSeminormOn_nonneg hg
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
