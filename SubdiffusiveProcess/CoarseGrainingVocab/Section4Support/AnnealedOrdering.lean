module

public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import SubdiffusiveProcess.Frozen.Section5.HomogenizedCoefficientReciprocalLower

@[expose] public section

/-!
# Annealed ordering and ratio estimates

The declarations here prove the algebraic consequences of two-sided
annealed coefficient comparisons. The comparison is an explicit premise
of these reusable lemmas. The concrete Section 4 providers supply it in
their applications; the premise is not a new public model assumption.
-/

open SubdiffusiveProcess.CoarseGrainingVocab

namespace SubdiffusiveProcess.CoarseGrainingVocab

/-- A two-sided multiplicative comparison controls the sum of the forward and
reciprocal ratio defects. -/
theorem ratio_defect_le_two_mul_exp
    {a b u : ℝ} (ha : 0 < a) (hb : 0 < b) (hu : 0 ≤ u)
    (hab : a ≤ b) (hba : b ≤ Real.exp u * a) :
    |a * b⁻¹ - 1| + |a⁻¹ * b - 1| ≤ 2 * u * Real.exp u := by
  let r : ℝ := b / a
  have hrpos : 0 < r := div_pos hb ha
  have hr1 : 1 ≤ r := (one_le_div₀ ha).2 hab
  have hre : r ≤ Real.exp u := by
    dsimp [r]
    rw [div_le_iff₀ ha]
    simpa [mul_comm] using hba
  have hlog : Real.log r ≤ u := by
    rw [← Real.log_exp u]
    exact Real.log_le_log hrpos hre
  have hleftId : a * b⁻¹ = r⁻¹ := by
    dsimp [r]
    field_simp
  have hrightId : a⁻¹ * b = r := by
    dsimp [r]
    rw [div_eq_inv_mul]
  have hrinv1 : r⁻¹ ≤ 1 := (inv_le_one₀ hrpos).2 hr1
  have hleft : |a * b⁻¹ - 1| ≤ u := by
    rw [hleftId, abs_of_nonpos (sub_nonpos.mpr hrinv1)]
    simpa only [neg_sub] using
      (Real.one_sub_inv_le_log_of_pos hrpos).trans hlog
  have hexpmul : Real.exp u - 1 ≤ u * Real.exp u := by
    have hbase := Real.add_one_le_exp (-u)
    have hmul := mul_le_mul_of_nonneg_left hbase (Real.exp_pos u).le
    rw [← Real.exp_add] at hmul
    ring_nf at hmul
    simp only [Real.exp_zero] at hmul
    linarith
  have hright : |a⁻¹ * b - 1| ≤ u * Real.exp u := by
    rw [hrightId, abs_of_nonneg (sub_nonneg.mpr hr1)]
    exact (sub_le_sub_right hre 1).trans hexpmul
  have hexp1 : 1 ≤ Real.exp u := by
    simpa using Real.exp_monotone hu
  nlinarith [mul_nonneg hu (sub_nonneg.mpr hexp1)]

/-- Paper display `e.annealed.ordering.ratio`, conditional only on its exact
two-sided annealed ordering input.  The sealed reciprocal lower bound supplies
the positivity needed to divide, and `tauSq_le_delta_sq` gives the displayed
small-contrast scale. -/
theorem annealedOrderingRatio_of_ordering {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n m : ℕ} (_hnm : n ≤ m)
    (horder : ahom M m ≤ ahom M n ∧
      ahom M n ≤ Real.exp
        (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ)) *
          ahom M m) :
    |ahom M m * (ahom M n)⁻¹ - 1| +
        |(ahom M m)⁻¹ * ahom M n - 1| ≤
      4 * M.delta ^ 2 * ((m - n : ℕ) : ℝ) *
        Real.exp (2 * M.delta ^ 2 * ((m - n : ℕ) : ℝ)) := by
  let gap : ℝ := ((m - n : ℕ) : ℝ)
  let u : ℝ := 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * gap
  let v : ℝ := 2 * M.delta ^ 2 * gap
  have hgap : 0 ≤ gap := by dsimp [gap]; positivity
  have hu : 0 ≤ u := by
    dsimp [u]
    exact mul_nonneg (mul_nonneg (by norm_num) M.G4.tauSq_pos.le) hgap
  have hmpos : 0 < ahom M m :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M m)
  have hnpos : 0 < ahom M n :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M n)
  have hbase :
      |ahom M m * (ahom M n)⁻¹ - 1| +
          |(ahom M m)⁻¹ * ahom M n - 1| ≤
        2 * u * Real.exp u := by
    exact ratio_defect_le_two_mul_exp hmpos hnpos hu horder.1 horder.2
  have hlog : Real.log 2 / 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta ^ 2 := by
    have hsq : 0 ≤ M.delta ^ 2 := sq_nonneg _
    exact (tauSq_le_delta_sq M).trans
      (mul_le_of_le_one_left hsq hlog)
  have huv : u ≤ v := by
    dsimp [u, v]
    gcongr
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hexp : Real.exp u ≤ Real.exp v := Real.exp_le_exp.mpr huv
  have hmul : u * Real.exp u ≤ v * Real.exp v :=
    mul_le_mul huv hexp (Real.exp_pos _).le hv
  calc
    |ahom M m * (ahom M n)⁻¹ - 1| +
          |(ahom M m)⁻¹ * ahom M n - 1| ≤
        2 * u * Real.exp u := hbase
    _ ≤ 2 * (v * Real.exp v) := by nlinarith
    _ = 4 * M.delta ^ 2 * ((m - n : ℕ) : ℝ) *
        Real.exp (2 * M.delta ^ 2 * ((m - n : ℕ) : ℝ)) := by
      dsimp [v, gap]
      ring

end SubdiffusiveProcess.CoarseGrainingVocab
