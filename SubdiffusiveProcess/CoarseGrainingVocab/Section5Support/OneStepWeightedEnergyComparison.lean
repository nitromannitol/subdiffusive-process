module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepLayerReplacement
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepWeightedPrincipalSymmetry
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-!
# Global weighted-energy comparison for the one-step argument

This module begins the quantitative half of the cancellation. The local Taylor estimate in
`OneStepLayerReplacement` assumes a pointwise small shell.  The GMC shell is
unbounded, so the actual stochastic argument instead uses the global
exponential-envelope remainder proved below.

The decomposition mirrors the exponential-remainder step
and is kept separate from the later Holder and fresh-shell estimates.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

noncomputable local instance continuousMapMeasurableSpace (d : ℕ) :
    MeasurableSpace C(Vec d, ℝ) :=
  borel C(Vec d, ℝ)

local instance continuousMapBorelSpace (d : ℕ) :
    BorelSpace C(Vec d, ℝ) :=
  ⟨rfl⟩

/-- The finite shell block is Borel as a compact-open continuous field.  This
upgrades the pointwise joint-measurability endpoint in the symmetry module
and is the parameter carrier used by the weighted quadratic functional. -/
theorem measurable_oneStepShellSumContinuousMap {d : ℕ} (n h : ℕ) :
    Measurable (oneStepShellSumContinuousMap (d := d) n h) := by
  have hforget : Continuous
      (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d ↦ g.1.1) :=
    continuous_subtype_val.fst
  have hsum : Measurable fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
      ∑ k ∈ cutoffShellIndices (n + h) (n : ℤ), (omega k).1.1 :=
    Finset.measurable_sum _ fun k _ ↦
    hforget.measurable.comp
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)
  convert hsum using 1
  funext omega
  ext x
  simp [oneStepShellSumContinuousMap, cutoffShellSum]

private theorem exp_sub_one_sub_id_le_half_sq_mul_exp_max (z : ℝ) :
    Real.exp z - (1 + z) ≤ (z ^ (2 : ℕ) / 2) * Real.exp (max z 0) := by
  by_cases hz : 0 ≤ z
  · rcases eq_or_lt_of_le hz with rfl | hzpos
    · norm_num
    have hu : UniqueDiffOn ℝ (Set.Icc 0 z) := uniqueDiffOn_Icc hzpos
    obtain ⟨ξ, hξ, hξeq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.exp) (x₀ := 0) (x := z) (n := 1) (ne_of_lt hzpos)
        Real.contDiff_exp.contDiffOn
    simp only [Set.uIcc_of_le hz, Set.uIoo_of_lt hzpos] at hξ hξeq
    have hderiv0 : derivWithin Real.exp (Set.Icc 0 z) 0 = 1 := by
      simpa using ((Real.hasDerivAt_exp 0).hasDerivWithinAt).derivWithin
        (hu.uniqueDiffWithinAt ⟨le_rfl, hzpos.le⟩)
    have htaylor : taylorWithinEval Real.exp 1 (Set.Icc 0 z) 0 z = 1 + z := by
      simp [taylor_within_apply, hderiv0]
    have hiter : iteratedDeriv 2 Real.exp ξ = Real.exp ξ := by
      rw [iteratedDeriv_eq_iterate]
      exact congrFun (Real.iter_deriv_exp 2) ξ
    have hformula : Real.exp z - (1 + z) = Real.exp ξ * z ^ (2 : ℕ) / 2 := by
      rw [← htaylor, hξeq, hiter]
      norm_num [Nat.factorial]
    have hξexp : Real.exp ξ ≤ Real.exp z := Real.exp_le_exp.2 hξ.2.le
    have hzsq_nonneg : 0 ≤ z ^ (2 : ℕ) / 2 := by positivity
    calc
      Real.exp z - (1 + z) = Real.exp ξ * z ^ (2 : ℕ) / 2 := hformula
      _ = (z ^ (2 : ℕ) / 2) * Real.exp ξ := by ring
      _ ≤ (z ^ (2 : ℕ) / 2) * Real.exp z :=
        mul_le_mul_of_nonneg_left hξexp hzsq_nonneg
      _ = (z ^ (2 : ℕ) / 2) * Real.exp (max z 0) := by
        simp [max_eq_left hz]
  · have hzneg : z < 0 := lt_of_not_ge hz
    let u : ℝ := -z
    have hupos : 0 < u := by simpa [u] using neg_pos.mpr hzneg
    have hu : UniqueDiffOn ℝ (Set.Icc 0 u) := uniqueDiffOn_Icc hupos
    obtain ⟨ξ, hξ, hξeq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := fun s : ℝ ↦ Real.exp (-s)) (x₀ := 0) (x := u) (n := 1) (ne_of_lt hupos)
        (by
          simpa only [Set.uIcc_of_le hupos.le] using!
            ((Real.contDiff_exp.comp (by fun_prop)).contDiffOn :
              ContDiffOn ℝ 2 (fun s : ℝ ↦ Real.exp (-s)) (Set.Icc 0 u)))
    simp only [Set.uIcc_of_le hupos.le, Set.uIoo_of_lt hupos] at hξ hξeq
    have hderiv0 :
        derivWithin (fun s : ℝ ↦ Real.exp (-s)) (Set.Icc 0 u) 0 = -1 := by
      have hderivAt : HasDerivAt (fun s : ℝ ↦ Real.exp (-s)) (-1) 0 := by
        simpa using ((hasDerivAt_id 0).neg.exp)
      exact hderivAt.hasDerivWithinAt.derivWithin
        (hu.uniqueDiffWithinAt ⟨le_rfl, hupos.le⟩)
    have htaylor :
        taylorWithinEval (fun s : ℝ ↦ Real.exp (-s)) 1
            (Set.Icc 0 u) 0 u = 1 - u := by
      simp [taylor_within_apply, hderiv0]
      ring
    have hiter :
        iteratedDeriv 2 (fun s : ℝ ↦ Real.exp (-s)) ξ = Real.exp (-ξ) := by
      simpa [pow_two] using
        congrFun (iteratedDeriv_exp_const_mul (n := 2) (-1)) ξ
    have hξle : Real.exp (-ξ) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [hξ.1])
    have hformula0 :
        Real.exp (-u) - (1 - u) = Real.exp (-ξ) * u ^ (2 : ℕ) / 2 := by
      rw [← htaylor, hξeq, hiter]
      norm_num [Nat.factorial]
    have hformula :
        Real.exp (-u) - (1 + -u) = Real.exp (-ξ) * u ^ (2 : ℕ) / 2 := by
      simpa only [sub_eq_add_neg] using! hformula0
    have husq_nonneg : 0 ≤ u ^ (2 : ℕ) / 2 := by positivity
    have haux : Real.exp z - (1 + z) ≤ u ^ (2 : ℕ) / 2 := by
      calc
        Real.exp z - (1 + z) = Real.exp (-u) - (1 + -u) := by simp [u]
        _ = Real.exp (-ξ) * u ^ (2 : ℕ) / 2 := hformula
        _ = (u ^ (2 : ℕ) / 2) * Real.exp (-ξ) := by ring
        _ ≤ (u ^ (2 : ℕ) / 2) * 1 :=
          mul_le_mul_of_nonneg_left hξle husq_nonneg
        _ = u ^ (2 : ℕ) / 2 := by ring
    have hmax : max z 0 = 0 := max_eq_right (le_of_lt hzneg)
    have hzsq : z ^ (2 : ℕ) = u ^ (2 : ℕ) := by simp [u, pow_two]
    rw [hmax, Real.exp_zero, hzsq]
    simpa using haux

/-- Global second-order Taylor remainder for the exponential. -/
theorem abs_exp_sub_one_sub_id_le_half_sq_mul_exp_abs (s : ℝ) :
    |Real.exp s - 1 - s| ≤ (s ^ 2 / 2) * Real.exp |s| := by
  have hnonneg : 0 ≤ Real.exp s - 1 - s := by
    linarith [Real.add_one_le_exp s]
  rw [abs_of_nonneg hnonneg]
  calc
    Real.exp s - 1 - s = Real.exp s - (1 + s) := by ring
    _ ≤ (s ^ 2 / 2) * Real.exp (max s 0) :=
      exp_sub_one_sub_id_le_half_sq_mul_exp_max s
    _ ≤ (s ^ 2 / 2) * Real.exp |s| := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.exp_le_exp.mpr (max_le (le_abs_self s) (abs_nonneg s))
      · positivity

/-- Global quadratic-error comparison.  Unlike the local predecessor this
has no pointwise smallness assumption; the exponential envelope is retained
for the subsequent fresh-shell Holder estimate. -/
theorem abs_oneStep_quadraticError_le_global {d : ℕ}
    (v r : Vec d) (s : ℝ) :
    |vecNormSq (v + r) * (Real.exp s - 1) - vecNormSq v * s| ≤
      Real.sqrt (vecNormSq r) *
          Real.sqrt (vecNormSq ((v + r) + v)) * |s| +
        vecNormSq (v + r) * ((s ^ 2 / 2) * Real.exp |s|) := by
  rw [oneStep_quadraticError_identity]
  have hnorm :
      |vecNormSq (v + r) - vecNormSq v| ≤
        Real.sqrt (vecNormSq r) *
          Real.sqrt (vecNormSq ((v + r) + v)) := by
    rw [vecNormSq_sub_vecNormSq]
    have hdiff : (v + r) - v = r := by
      ext i
      simp
    rw [hdiff]
    exact abs_vecDot_le_sqrt_mul_sqrt r ((v + r) + v)
  calc
    |(vecNormSq (v + r) - vecNormSq v) * s +
        vecNormSq (v + r) * (Real.exp s - 1 - s)| ≤
        |vecNormSq (v + r) - vecNormSq v| * |s| +
          vecNormSq (v + r) * |Real.exp s - 1 - s| := by
      calc
        _ ≤ |(vecNormSq (v + r) - vecNormSq v) * s| +
              |vecNormSq (v + r) * (Real.exp s - 1 - s)| :=
          abs_add_le _ _
        _ = _ := by
          rw [abs_mul, abs_mul,
            abs_of_nonneg (vecNormSq_nonneg (v + r))]
    _ ≤
        (Real.sqrt (vecNormSq r) *
          Real.sqrt (vecNormSq ((v + r) + v))) * |s| +
          vecNormSq (v + r) * ((s ^ 2 / 2) * Real.exp |s|) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hnorm (abs_nonneg s))
        (mul_le_mul_of_nonneg_left
          (abs_exp_sub_one_sub_id_le_half_sq_mul_exp_abs s)
          (vecNormSq_nonneg (v + r)))
    _ = _ := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
