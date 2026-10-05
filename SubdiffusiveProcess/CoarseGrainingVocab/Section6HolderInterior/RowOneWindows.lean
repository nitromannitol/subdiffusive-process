module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneAbsorption

@[expose] public section

/-!
# The window inputs of row 1

Three facts the row-1 assembly needs, none of them in the ladder itself.

* **The stopping scale is always at least `5`.**  `holderStoppingScale` is
  `max (error depth) (good depth) + step + 5` by construction, so the frozen
  hypothesis `X ≤ m - n` already forces `n ≤ m - 5`.  This is exactly the
  hypothesis `WindowMonotone.interiorGate_of_descendant` needs, and without it
  the interior gate would not be available at the frozen row's base points.
* **The top window at depth `m - 5`** against the global oscillation, at the
  dimension-only ratio `√((3^7)^d)`.
* **The shallow window at depth `ell`** against the same, valid exactly when
  `m - ell ≤ 5`.

Both window bounds are instantiations of the proved, datum-free
`Section6Holder.normalizedL2On_truncatedCube_sub_average_le_global`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The stopping scale never drops below `5`.** -/
theorem five_le_measurableHolderStoppingScale
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    5 ≤ Section6Stopping.measurableHolderStoppingScale M alpha lambda epsilon
      step m omega := by
  have heq := Section6Stopping.holderStoppingScale_eq_max_depth_add
    M alpha lambda epsilon step m omega
  have hle := Section6Stopping.holderStoppingScale_le_measurable
    M alpha lambda epsilon step m omega
  omega

/-- The frozen stopping hypothesis puts the base point five scales inside. -/
theorem base_scale_le_of_stopping
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m n : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hstop : (Section6Stopping.measurableHolderStoppingScale M alpha lambda
        epsilon step m omega : ℤ) ≤ (m : ℤ) - (n : ℤ)) :
    (n : ℤ) ≤ (m : ℤ) - 5 := by
  have h5 := five_le_measurableHolderStoppingScale M alpha lambda epsilon
    step m omega
  omega

/-- Monotonicity of the dimension-only volume ratio in the scale. -/
theorem sqrt_pow_le_topWindowRatio_factor {j : ℤ} (hj : j ≤ 7) :
    Real.sqrt (((3 : ℝ) ^ j) ^ d) ≤ Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) := by
  apply Real.sqrt_le_sqrt
  have hbase : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ (7 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) hj
  have hcast : (3 : ℝ) ^ (7 : ℤ) = (3 : ℝ) ^ (7 : ℕ) := by norm_num
  rw [hcast] at hbase
  exact pow_le_pow_left₀ (by positivity) hbase d

/-- The top window at depth `m - 5` against the global oscillation. -/
theorem topWindow_le_global
    {m : ℕ} {y : Vec d} (hy : y ∈ cube d (m : ℤ))
    (u : H1Function (openCubeSet (originCube d (m : ℤ)))) :
    normalizedL2On (truncatedCube d (m : ℤ) ((m : ℤ) - 5) y)
        (fun p => u.toFun p -
          averageOn (truncatedCube d (m : ℤ) ((m : ℤ) - 5) y) u.toFun) ≤
      Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) *
        normalizedL2On (cube d (m : ℤ))
          (fun p => u.toFun p - averageOn (cube d (m : ℤ)) u.toFun) := by
  have hraw := Section6Holder.normalizedL2On_truncatedCube_sub_average_le_global
    (m := (m : ℤ)) (j := (m : ℤ) - 5) hy (by omega) u
  have hexp : (m : ℤ) - ((m : ℤ) - 5) + 2 = (7 : ℤ) := by ring
  rw [hexp] at hraw
  have hcast : ((3 : ℝ) ^ (7 : ℤ)) ^ d = ((3 : ℝ) ^ (7 : ℕ)) ^ d := by norm_num
  rwa [hcast] at hraw

/-- The shallow window at depth `ell`, valid exactly when `m - ell ≤ 5`. -/
theorem shallowWindow_le_global
    {m ell : ℕ} {y : Vec d} (hy : y ∈ cube d (m : ℤ))
    (hellm : (ell : ℤ) ≤ (m : ℤ)) (hshallow : (m : ℤ) - (ell : ℤ) ≤ 5)
    (u : H1Function (openCubeSet (originCube d (m : ℤ)))) :
    normalizedL2On (truncatedCube d (m : ℤ) (ell : ℤ) y)
        (fun p => u.toFun p -
          averageOn (truncatedCube d (m : ℤ) (ell : ℤ) y) u.toFun) ≤
      Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) *
        normalizedL2On (cube d (m : ℤ))
          (fun p => u.toFun p - averageOn (cube d (m : ℤ)) u.toFun) := by
  have hraw := Section6Holder.normalizedL2On_truncatedCube_sub_average_le_global
    (m := (m : ℤ)) (j := (ell : ℤ)) hy (by omega) u
  have hglobal0 : 0 ≤ normalizedL2On (cube d (m : ℤ))
      (fun p => u.toFun p - averageOn (cube d (m : ℤ)) u.toFun) :=
    Section6Iteration.normalizedL2On_nonneg _ _
  refine hraw.trans ?_
  exact mul_le_mul_of_nonneg_right
    (sqrt_pow_le_topWindowRatio_factor (by omega)) hglobal0

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
