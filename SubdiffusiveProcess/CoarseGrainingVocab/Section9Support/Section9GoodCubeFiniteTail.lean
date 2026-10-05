module

public import Mathlib

@[expose] public section

/-!
# Absorbing finite good-cube tail factors

For every fixed positive prefactor and decay constant, shrinking the disorder
threshold absorbs the prefactor into a tail with exponent `-c²/(δ² log² δ)`.
The new threshold can be bounded by any prescribed positive constant. Thus a
finite template may be chosen before this threshold without enlarging the
spatial constant used in the good-cube geometry.
-/

set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A logarithmic budget absorbs a finite prefactor into an exponential tail. -/
theorem goodCube_finite_tail_absorption {K a D c : ℝ}
    (hK : 0 < K) (hD : 0 < D) (hbudget : D * Real.log K + c ^ 2 ≤ a) :
    K * Real.exp (-a / D) ≤ Real.exp (-(c ^ 2 / D)) := by
  have hexp : Real.exp (Real.log K + (-a / D)) = K * Real.exp (-a / D) := by
    rw [Real.exp_add]
    rw [Real.exp_log hK]
  have hnum : D * Real.log K - a ≤ -(c ^ 2) := by linarith
  have hdiv : (D * Real.log K - a) / D ≤ -(c ^ 2 / D) := by
    simpa only [neg_div] using div_le_div_of_nonneg_right hnum hD.le
  have hkey : Real.log K + (-a / D) ≤ -(c ^ 2 / D) := by
    have hfrac : (D * Real.log K - a) / D = Real.log K - a / D := by
      field_simp [ne_of_gt hD]
    rw [hfrac] at hdiv
    simpa only [neg_div, sub_eq_add_neg] using hdiv
  calc K * Real.exp (-a / D)
      = Real.exp (Real.log K + (-a / D)) := hexp.symm
    _ ≤ Real.exp (-(c ^ 2 / D)) := by
        apply Real.exp_le_exp.mpr hkey

/-- A single sufficiently small positive threshold absorbs a fixed finite
prefactor uniformly for every positive disorder below it. -/
theorem goodCube_exists_finite_tail_absorption (K a b : ℝ)
    (hK : 0 < K) (ha : 0 < a) (hb : 0 < b) :
    ∃ c : ℝ, 0 < c ∧ c ≤ b ∧ c ≤ 1 / 2 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ c →
        K * Real.exp (-a / (delta ^ 2 * Real.log delta ^ 2)) ≤
          Real.exp (-(c ^ 2 / (delta ^ 2 * Real.log delta ^ 2))) := by
  have hcont : Continuous (fun x : ℝ => (x * Real.log x) ^ 2 * Real.log K) :=
    (Real.continuous_mul_log.pow 2).mul continuous_const
  have hca : ContinuousAt (fun x : ℝ => (x * Real.log x) ^ 2 * Real.log K) 0 :=
    hcont.continuousAt
  rw [Metric.continuousAt_iff] at hca
  obtain ⟨r, hr, hrep⟩ := hca (a / 2) (by linarith)
  set c : ℝ := min b (min (1 / 2) (min (a / 2) (r / 2))) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    apply lt_min hb
    apply lt_min (by norm_num)
    apply lt_min (by linarith) (by linarith)
  have hcb : c ≤ b := min_le_left _ _
  have hcle : c ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hca2 : c ≤ a / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcr : c ≤ r / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcsq : c ^ 2 ≤ c := by
    nlinarith [mul_nonneg hcpos.le (show 0 ≤ 1 - c by linarith)]
  refine ⟨c, hcpos, hcb, hcle, ?_⟩
  intro delta hdpos hdlec
  have hd1 : delta < 1 := lt_of_le_of_lt (le_trans hdlec hcle) (by norm_num)
  have hlogneg : Real.log delta < 0 := Real.log_neg hdpos hd1
  have hD : 0 < delta ^ 2 * (Real.log delta) ^ 2 :=
    mul_pos (sq_pos_of_pos hdpos) (sq_pos_of_ne_zero (ne_of_lt hlogneg))
  have hdist : dist ((delta * Real.log delta) ^ 2 * Real.log K)
      ((0 * Real.log 0) ^ 2 * Real.log K) < a / 2 := by
    apply hrep
    rw [Real.dist_eq]
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hdpos] using
      lt_of_le_of_lt (le_trans hdlec hcr) (by linarith)
  simp only [zero_mul, zero_pow (by decide : (2:ℕ) ≠ 0), Real.dist_eq, sub_zero] at hdist
  have hF : (delta * Real.log delta) ^ 2 * Real.log K
      = delta ^ 2 * (Real.log delta) ^ 2 * Real.log K := by
    rw [mul_pow]
  rw [hF] at hdist
  have hbound : delta ^ 2 * (Real.log delta) ^ 2 * Real.log K + c ^ 2 ≤ a := by
    have h2 : delta ^ 2 * (Real.log delta) ^ 2 * Real.log K < a / 2 := by
      have := abs_lt.mp hdist
      linarith
    linarith
  exact goodCube_finite_tail_absorption hK hD hbound

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
