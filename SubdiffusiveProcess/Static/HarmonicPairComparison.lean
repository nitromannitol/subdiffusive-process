module

public import SubdiffusiveProcess.Static.HarmonicPairFactors
public import SubdiffusiveProcess.Static.AffineChart

@[expose] public section

/-! # Literal comparison of parent and own-scale cell coefficients -/
open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- Exact side of a physical cell in a parent chart. -/
theorem pair_physical_cell_scale (m n : ℕ) :
    (3 : ℝ) ^ ((m : ℤ) - n) = (3 : ℝ) ^ m * ((3 : ℝ) ^ n)⁻¹ := by
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast, zpow_natCast, div_eq_mul_inv]

/-- Origin cubes use exactly the sup-norm radius one half of their side. -/
theorem pair_originCube_eq_ball (d : ℕ) (k : ℤ) :
    openCubeSet (originCube d k) = Metric.ball (0 : Vec d) ((3 : ℝ) ^ k / 2) := by
  have hcenter : cubeCenter (originCube d k) = (0 : Vec d) := by
    funext i
    simp [cubeCenter, originCube]
  have h := (ball_cubeCenter_eq_openCubeSet (originCube d k)).symm
  rw [hcenter] at h
  convert h using 1
  simp [cubeRadius, cubeScaleFactor, originCube, div_eq_mul_inv, mul_comm]

/-- A physical subunit cell lies in the own-cutoff comparison window. -/
theorem pair_scaled_unit_mem {d : ℕ} {k l : ℤ} (hkl : k ≤ l)
    {w : Vec d} (hw : w ∈ openCubeSet (originCube d 0)) :
    (3 : ℝ) ^ k • w ∈ openCubeSet (originCube d l) := by
  rw [pair_originCube_eq_ball, mem_ball_zero_iff, norm_smul,
    Real.norm_eq_abs, abs_of_pos (zpow_pos (by norm_num) k)]
  rw [unitCube_eq_ball, mem_ball_zero_iff] at hw
  calc
    (3 : ℝ) ^ k * ‖w‖ < (3 : ℝ) ^ k * (1 / 2) :=
      mul_lt_mul_of_pos_left hw (zpow_pos (by norm_num) k)
    _ ≤ (3 : ℝ) ^ l / 2 := by
      have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hkl
      linarith

/-- The physical coefficient in a parent chart compares to the normalized
own-cutoff coefficient in each fine cell, including negative physical scales. -/
theorem pair_normalized_coefficient_comparison {d : ℕ} (M : GMCModel d)
    (j m n : ℕ) (z y : Vec d) (omega : PotentialSample d)
    {w : Vec d} (hw : w ∈ openCubeSet (originCube d 0)) :
    let k : ℤ := (m : ℤ) - n
    let l : ℕ := min j k.toNat
    let Y := z + (3 : ℝ) ^ m • y
    (ahom M j)⁻¹ * aCutoff M j omega
        (z + (3 : ℝ) ^ m • (y + ((3 : ℝ) ^ n)⁻¹ • w)) ≤
      (ahom M l / ahom M j * cutoffBlockFactor M j l Y omega) *
        ((ahom M l)⁻¹ * aCutoff M l omega (Y + (3 : ℝ) ^ k • w)) := by
  dsimp only
  let k : ℤ := (m : ℤ) - n
  let l : ℕ := min j k.toNat
  let Y := z + (3 : ℝ) ^ m • y
  have hpoint : z + (3 : ℝ) ^ m • (y + ((3 : ℝ) ^ n)⁻¹ • w) =
      Y + (3 : ℝ) ^ k • w := by
    rw [smul_add, smul_smul, ← pair_physical_cell_scale]
    simp only [Y, k, add_assoc]
  rw [hpoint]
  change (ahom M j)⁻¹ * aCutoff M j omega (Y + (3 : ℝ) ^ k • w) ≤
    (ahom M l / ahom M j * cutoffBlockFactor M j l Y omega) *
      ((ahom M l)⁻¹ * aCutoff M l omega (Y + (3 : ℝ) ^ k • w))
  have hlj : l ≤ j := min_le_left _ _
  by_cases hsame : l = j
  · simp [hsame, cutoffBlockFactor, div_self (ahom_pos M j).ne']
  · have hkl : k ≤ (l : ℤ) := by dsimp only [l]; omega
    have hx : (Y + (3 : ℝ) ^ k • w) - Y ∈ openCubeSet (originCube d (l : ℤ)) := by
      rw [add_sub_cancel_left]
      exact pair_scaled_unit_mem hkl hw
    have hcomp := (cutoffBlockFactor_comparison M hlj Y omega hx).1
    have h := mul_le_mul_of_nonneg_left hcomp (inv_pos.mpr (ahom_pos M j)).le
    refine h.trans_eq ?_
    field_simp [(ahom_pos M l).ne', (ahom_pos M j).ne']

end SubdiffusiveProcess.Static
