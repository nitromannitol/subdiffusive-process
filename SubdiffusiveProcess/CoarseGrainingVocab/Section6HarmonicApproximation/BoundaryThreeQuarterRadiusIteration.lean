module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCombinedSignedLocalizedStep

@[expose] public section

/-!
# Radius iteration for the signed three-quarter row

The combined signed cutoff estimate naturally produces a `3/4` contraction
after the residual-to-physical readout.  This file records the corresponding
fixed-exponent (`8`) deterministic iteration, keeping it separate from the
Chapter-3 library's `1/2` recurrence.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization
open scoped BigOperators

noncomputable section

/-- The weighted error term for the signed boundary recurrence. -/
noncomputable def boundaryThreeQuarterRadiusIterationTerm (n : ℕ) : ℝ :=
  (3 / 4 : ℝ) ^ n * Real.rpow
    (coarseCaccioppoliRadiusSequence (n + 1) -
      coarseCaccioppoliRadiusSequence n) (-8 : ℝ)

/-- The finite deterministic constant in the signed boundary recurrence. -/
noncomputable def boundaryThreeQuarterRadiusIterationConst : ℝ :=
  ∑' n : ℕ, boundaryThreeQuarterRadiusIterationTerm n

theorem boundaryThreeQuarterRadiusIterationTerm_nonneg (n : ℕ) :
    0 ≤ boundaryThreeQuarterRadiusIterationTerm n := by
  have hgap : 0 ≤ coarseCaccioppoliRadiusSequence (n + 1) -
      coarseCaccioppoliRadiusSequence n :=
    sub_nonneg.mpr
      (coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n)).le
  exact mul_nonneg (by positivity) (Real.rpow_nonneg hgap _)

private theorem boundaryThreeQuarterRadiusIterationTerm_le_majorant (n : ℕ) :
    boundaryThreeQuarterRadiusIterationTerm n ≤
      (2 : ℝ) ^ (8 : ℕ) *
        ((((n + 2 : ℕ) : ℝ) ^ (16 : ℕ)) * (3 / 4 : ℝ) ^ n) := by
  let m : ℝ := (((n + 1) * (n + 2) : ℕ) : ℝ)
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hbase0 : 0 ≤ (3 / 2 : ℝ) * m := by positivity
  have hbase : (3 / 2 : ℝ) * m ≤
      2 * (((n + 2 : ℕ) : ℝ) ^ 2) := by
    have hn : ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ (n + 1)
    have hm : m ≤ (((n + 2 : ℕ) : ℝ) ^ 2) := by
      dsimp [m]
      simpa only [Nat.cast_mul, pow_two] using
        mul_le_mul_of_nonneg_right hn (by positivity)
    nlinarith
  have hgap : Real.rpow
      (coarseCaccioppoliRadiusSequence (n + 1) -
        coarseCaccioppoliRadiusSequence n) (-8 : ℝ) =
      ((3 / 2 : ℝ) * m) ^ (8 : ℕ) := by
    rw [coarseCaccioppoliRadiusSequence_succ_sub]
    have hmpos : 0 < m := by dsimp [m]; positivity
    have hinv : (2 / (3 * m))⁻¹ = (3 / 2 : ℝ) * m := by
      field_simp [hmpos.ne']
    calc
      Real.rpow (2 / (3 * (((n + 1) * (n + 2) : ℕ) : ℝ))) (-8 : ℝ) =
          Real.rpow ((2 / (3 * m))⁻¹) (8 : ℝ) := by
            simpa only [m] using!
              Real.rpow_neg_eq_inv_rpow
                (2 / (3 * (((n + 1) * (n + 2) : ℕ) : ℝ))) (8 : ℝ)
      _ = Real.rpow ((3 / 2 : ℝ) * m) (8 : ℝ) := by rw [hinv]
      _ = ((3 / 2 : ℝ) * m) ^ (8 : ℕ) := Real.rpow_natCast _ 8
  rw [boundaryThreeQuarterRadiusIterationTerm, hgap]
  have hp := pow_le_pow_left₀ hbase0 hbase 8
  calc
    (3 / 4 : ℝ) ^ n * ((3 / 2 : ℝ) * m) ^ (8 : ℕ) ≤
        (3 / 4 : ℝ) ^ n *
          (2 * (((n + 2 : ℕ) : ℝ) ^ 2)) ^ (8 : ℕ) := by gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; norm_num; ring

private theorem summable_boundaryThreeQuarterRadiusIterationTerm :
    Summable boundaryThreeQuarterRadiusIterationTerm := by
  have hq : ‖(3 / 4 : ℝ)‖ < 1 := by norm_num
  have hpoly : Summable (fun n : ℕ ↦
      (n : ℝ) ^ (16 : ℕ) * (3 / 4 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 16 hq
  have hshift : Summable (fun n : ℕ ↦
      ((n + 2 : ℕ) : ℝ) ^ (16 : ℕ) * (3 / 4 : ℝ) ^ (n + 2)) :=
    (summable_nat_add_iff
      (f := fun n : ℕ ↦ (n : ℝ) ^ (16 : ℕ) * (3 / 4 : ℝ) ^ n) 2).2
      hpoly
  have hmajor : Summable (fun n : ℕ ↦
      (2 : ℝ) ^ (8 : ℕ) *
        (((n + 2 : ℕ) : ℝ) ^ (16 : ℕ) * (3 / 4 : ℝ) ^ n)) := by
    convert hshift.mul_left ((2 : ℝ) ^ (8 : ℕ) * (16 / 9 : ℝ)) using 1
    funext n
    rw [pow_add]
    norm_num
    ring
  exact hmajor.of_nonneg_of_le boundaryThreeQuarterRadiusIterationTerm_nonneg
    boundaryThreeQuarterRadiusIterationTerm_le_majorant

theorem boundaryThreeQuarterRadiusIterationConst_nonneg :
    0 ≤ boundaryThreeQuarterRadiusIterationConst := by
  unfold boundaryThreeQuarterRadiusIterationConst
  exact tsum_nonneg boundaryThreeQuarterRadiusIterationTerm_nonneg

/-- Fixed-exponent radius iteration for a nonnegative profile satisfying the
combined signed `3/4` recurrence on the canonical radii. -/
theorem boundary_threeQuarter_radius_iteration
    {F : ℝ → ℝ} {A : ℝ}
    (hA : 0 ≤ A)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hrec : ∀ n : ℕ,
      F (coarseCaccioppoliRadiusSequence n) ≤
        (3 / 4 : ℝ) * F (coarseCaccioppoliRadiusSequence (n + 1)) +
          A * Real.rpow
            (coarseCaccioppoliRadiusSequence (n + 1) -
              coarseCaccioppoliRadiusSequence n) (-8 : ℝ)) :
    F (1 / 3 : ℝ) ≤ A * boundaryThreeQuarterRadiusIterationConst := by
  rcases hbounded with ⟨B, hB⟩
  have hraw : ∀ N : ℕ,
      F (coarseCaccioppoliRadiusSequence 0) ≤
        (3 / 4 : ℝ) ^ N * F (coarseCaccioppoliRadiusSequence N) +
          A * ∑ n ∈ Finset.range N, boundaryThreeQuarterRadiusIterationTerm n := by
    intro N
    induction N with
    | zero => simp
    | succ N hN =>
        have hs := hrec N
        calc
          _ ≤ (3 / 4 : ℝ) ^ N * F (coarseCaccioppoliRadiusSequence N) +
              A * ∑ n ∈ Finset.range N,
                boundaryThreeQuarterRadiusIterationTerm n := hN
          _ ≤ (3 / 4 : ℝ) ^ N *
                ((3 / 4 : ℝ) * F (coarseCaccioppoliRadiusSequence (N + 1)) +
                  A * Real.rpow
                    (coarseCaccioppoliRadiusSequence (N + 1) -
                      coarseCaccioppoliRadiusSequence N) (-8 : ℝ)) +
              A * ∑ n ∈ Finset.range N,
                boundaryThreeQuarterRadiusIterationTerm n := by gcongr
          _ = (3 / 4 : ℝ) ^ (N + 1) *
                F (coarseCaccioppoliRadiusSequence (N + 1)) +
              A * ∑ n ∈ Finset.range (N + 1),
                boundaryThreeQuarterRadiusIterationTerm n := by
            rw [Finset.sum_range_succ, boundaryThreeQuarterRadiusIterationTerm,
              pow_succ]
            ring
  have hsum := summable_boundaryThreeQuarterRadiusIterationTerm
  apply le_of_forall_pos_le_add
  intro eps heps
  have hpow :=
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      (by norm_num : |(3 / 4 : ℝ)| < 1)).mul_const B
  rcases Metric.tendsto_atTop.1 hpow eps heps with ⟨N, hN⟩
  have hsmallAbs : |(3 / 4 : ℝ) ^ N * B| < eps := by
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)] using hN N le_rfl
  have hsmall : (3 / 4 : ℝ) ^ N * B ≤ eps :=
    (le_abs_self _).trans hsmallAbs.le
  have hBN := hB (coarseCaccioppoliRadiusSequence_mem_Icc N).1
    (coarseCaccioppoliRadiusSequence_mem_Icc N).2
  have hfinite : ∑ n ∈ Finset.range N,
      boundaryThreeQuarterRadiusIterationTerm n ≤
      boundaryThreeQuarterRadiusIterationConst := by
    unfold boundaryThreeQuarterRadiusIterationConst
    exact hsum.sum_le_tsum (Finset.range N) fun n _ ↦
      boundaryThreeQuarterRadiusIterationTerm_nonneg n
  calc
    F (1 / 3 : ℝ) = F (coarseCaccioppoliRadiusSequence 0) := by
      simp [coarseCaccioppoliRadiusSequence_zero]
    _ ≤ (3 / 4 : ℝ) ^ N * F (coarseCaccioppoliRadiusSequence N) +
        A * ∑ n ∈ Finset.range N,
          boundaryThreeQuarterRadiusIterationTerm n := hraw N
    _ ≤ (3 / 4 : ℝ) ^ N * B +
        A * ∑ n ∈ Finset.range N,
          boundaryThreeQuarterRadiusIterationTerm n := by gcongr
    _ ≤ eps + A * ∑ n ∈ Finset.range N,
          boundaryThreeQuarterRadiusIterationTerm n := by gcongr
    _ ≤ eps + A * boundaryThreeQuarterRadiusIterationConst := by gcongr
    _ = A * boundaryThreeQuarterRadiusIterationConst + eps := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
