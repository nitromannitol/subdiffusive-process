module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.LocalMathcalE
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.AccumulatedErrorExtraction

@[expose] public section

/-!
# Holder Step 3: the concrete recurrence budget

This file names the two scalar families in `e.ep.j.z.def` and
`e.delta.j.z.def`.  It also proves the part of the interval summation which is
independent of the excess-decay theorem: the `epsilon` family is paid for by
the stopped accumulated-error row, after shifting `j` to `j + 2`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The literal `epsilon_{j,z}` in the ready-for-iteration display.  The
fixed powers of `s0` and the one-step constant are collected in `K`. -/
def holderRecurrenceEpsilon {d : ℕ}
    (K : ℝ) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (epsilon s : ℝ)
    (j : ℕ) (z : Vec d) (omega : Sample d) : ℝ :=
  K * min epsilon
      (M.delta ^ 2 + epsilon ^ 8 + accumulatedError M none (j + 2) z s omega) *
    (if omega ∈ goodEvent M none (j + 2) z epsilon s then 1 else 0)

/-- The literal `delta_{j,z}`.  `topForcing` and the two boundary data are
already normalized at the parent scale; `rho` is the geometric half-scale
factor and `boundary` is the window-contact indicator. -/
def holderRecurrenceDefect
    (K rho exponential topForcing epsilonJ hLinfty topBoundary boundary : ℝ) : ℝ :=
  K * rho * exponential * topForcing +
    K * (epsilonJ * hLinfty + rho * topBoundary) * boundary

/-- The expanded defect used by the concrete Hölder recurrence.  Keeping the
three dimensional constants separate makes its interval sum transparent. -/
def holderReadyDefect
    (forcingConst meanConst boundaryConst rho exponential topForcing
      epsilonJ hLinfty topBoundary boundary : ℝ) : ℝ :=
  forcingConst * rho * exponential * topForcing +
    meanConst * epsilonJ * hLinfty * boundary +
    boundaryConst * rho * topBoundary * boundary

theorem holderRecurrenceEpsilon_nonneg {d : ℕ}
    {K epsilon s : ℝ} (hK : 0 ≤ K) (hepsilon : 0 ≤ epsilon)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) (z : Vec d)
    (omega : Sample d) :
    0 ≤ holderRecurrenceEpsilon K M epsilon s j z omega := by
  unfold holderRecurrenceEpsilon
  have herr := accumulatedError_nonneg M none s (j + 2) z omega
  have hmin : 0 ≤ min epsilon
      (M.delta ^ 2 + epsilon ^ 8 + accumulatedError M none (j + 2) z s omega) :=
    le_min hepsilon (by positivity)
  split_ifs <;> positivity

theorem holderRecurrenceEpsilon_le_error {d : ℕ}
    {K epsilon s : ℝ} (hK : 0 ≤ K)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) (z : Vec d)
    (omega : Sample d) :
    holderRecurrenceEpsilon K M epsilon s j z omega ≤
      K * (M.delta ^ 2 + epsilon ^ 8 +
        accumulatedError M none (j + 2) z s omega) := by
  unfold holderRecurrenceEpsilon
  have herr := accumulatedError_nonneg M none s (j + 2) z omega
  have hB : 0 ≤ M.delta ^ 2 + epsilon ^ 8 +
      accumulatedError M none (j + 2) z s omega := by positivity
  have hmin := min_le_right epsilon
    (M.delta ^ 2 + epsilon ^ 8 + accumulatedError M none (j + 2) z s omega)
  split_ifs
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hmin hK
  · simp only [mul_zero]
    exact mul_nonneg hK hB

/-- Shifting the recurrence rows by two identifies their accumulated-error
sum with the literal subinterval `[n+2,m]`. -/
theorem sum_shiftTwo_accumulatedError_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ) (omega : Sample d)
    (z : Vec d) {n m : ℕ} (hm2 : 2 ≤ m) :
    (∑ j ∈ Finset.Icc n (m - 2),
        accumulatedError M none (j + 2) z s omega) =
      ∑ i ∈ Finset.Icc (n + 2) m,
        accumulatedError M none i z s omega := by
  calc
    (∑ j ∈ Finset.Icc n (m - 2),
        accumulatedError M none (j + 2) z s omega) =
      ∑ i ∈ Finset.map (addRightEmbedding 2) (Finset.Icc n (m - 2)),
        accumulatedError M none i z s omega := by
          rw [Finset.sum_map]
          simp only [addRightEmbedding_apply]
    _ = ∑ i ∈ Finset.Icc (n + 2) m,
        accumulatedError M none i z s omega := by
          rw [Finset.map_add_right_Icc, Nat.sub_add_cancel hm2]

theorem sum_shiftTwo_accumulatedError_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ) (omega : Sample d)
    (z : Vec d) {n m : ℕ} (hm2 : 2 ≤ m) :
    (∑ j ∈ Finset.Icc n (m - 2),
        accumulatedError M none (j + 2) z s omega) ≤
      ∑ i ∈ Finset.Icc n m,
        accumulatedError M none i z s omega := by
  rw [sum_shiftTwo_accumulatedError_eq M s omega z hm2]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  · intro i _hi _hout
    exact accumulatedError_nonneg M none s i z omega

/-- `e.ep.j.z.sum`, before the manuscript's parameter absorption. -/
theorem sum_holderRecurrenceEpsilon_le {d : ℕ}
    {K epsilon s : ℝ} (hK : 0 ≤ K)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (omega : Sample d) (z : Vec d)
    {n m : ℕ} (hm2 : 2 ≤ m) :
    (∑ j ∈ Finset.Icc n (m - 2),
        holderRecurrenceEpsilon K M epsilon s j z omega) ≤
      K * (((Finset.Icc n (m - 2)).card : ℝ) *
          (M.delta ^ 2 + epsilon ^ 8) +
        ∑ i ∈ Finset.Icc n m, accumulatedError M none i z s omega) := by
  calc
    (∑ j ∈ Finset.Icc n (m - 2),
        holderRecurrenceEpsilon K M epsilon s j z omega) ≤
      ∑ j ∈ Finset.Icc n (m - 2),
        K * (M.delta ^ 2 + epsilon ^ 8 +
          accumulatedError M none (j + 2) z s omega) := by
            exact Finset.sum_le_sum fun j _ ↦
              holderRecurrenceEpsilon_le_error hK M j z omega
    _ = K * (((Finset.Icc n (m - 2)).card : ℝ) *
          (M.delta ^ 2 + epsilon ^ 8) +
        ∑ j ∈ Finset.Icc n (m - 2),
          accumulatedError M none (j + 2) z s omega) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      ring
    _ ≤ K * (((Finset.Icc n (m - 2)).card : ℝ) *
          (M.delta ^ 2 + epsilon ^ 8) +
        ∑ i ∈ Finset.Icc n m, accumulatedError M none i z s omega) := by
      gcongr
      exact sum_shiftTwo_accumulatedError_le M s omega z hm2

/-- The parameter-absorbed form of `e.ep.j.z.sum`.  The harmless terminal
`+1` is retained so the statement also covers a one-point interval. -/
theorem sum_holderRecurrenceEpsilon_le_three_mul {d : ℕ}
    {K epsilon s lambda : ℝ} (hK : 0 ≤ K) (hlambda : 0 ≤ lambda)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (omega : Sample d) (z : Vec d)
    (hdelta : M.delta ^ 2 ≤ lambda) (hepsilon : epsilon ^ 8 ≤ lambda)
    {n m : ℕ} (hnm : n ≤ m) (hm2 : 2 ≤ m)
    (herrors : (∑ i ∈ Finset.Icc n m,
        accumulatedError M none i z s omega) ≤
          lambda * ((m : ℝ) - (n : ℝ))) :
    (∑ j ∈ Finset.Icc n (m - 2),
        holderRecurrenceEpsilon K M epsilon s j z omega) ≤
      3 * K * lambda * ((m : ℝ) - (n : ℝ) + 1) := by
  have hbase := sum_holderRecurrenceEpsilon_le
    (K := K) (epsilon := epsilon) (s := s) hK M omega z (n := n) (m := m) hm2
  have hcardNat : (Finset.Icc n (m - 2)).card ≤ m + 1 - n := by
    rw [Nat.card_Icc]
    omega
  have hcast : ((Finset.Icc n (m - 2)).card : ℝ) ≤
      (m : ℝ) - (n : ℝ) + 1 := by
    have hcardR : ((Finset.Icc n (m - 2)).card : ℝ) ≤
        ((m + 1 - n : ℕ) : ℝ) := by exact_mod_cast hcardNat
    rw [Nat.cast_sub (by omega : n ≤ m + 1), Nat.cast_add, Nat.cast_one] at hcardR
    linarith
  have hgap : 0 ≤ (m : ℝ) - (n : ℝ) :=
    sub_nonneg.mpr (Nat.cast_le.2 hnm)
  have hsum : M.delta ^ 2 + epsilon ^ 8 ≤ 2 * lambda := by linarith
  have hcard0 : 0 ≤ ((Finset.Icc n (m - 2)).card : ℝ) := by positivity
  have hproduct := mul_le_mul hcast hsum (by positivity) (by positivity)
  nlinarith

/-- The same absorbed `epsilon` budget on an arbitrary iteration subinterval
`[n,l]`, paid for by the stopped row on the full parent corridor `[n,m]`. -/
theorem sum_holderRecurrenceEpsilon_interval_le_three_mul {d : ℕ}
    {K epsilon s lambda : ℝ} (hK : 0 ≤ K) (hlambda : 0 ≤ lambda)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (omega : Sample d) (z : Vec d)
    {n l m : ℕ} (hnl : n ≤ l) (hlm : l + 2 ≤ m)
    (hdelta : M.delta ^ 2 ≤ lambda) (hepsilon : epsilon ^ 8 ≤ lambda)
    (herrors : (∑ i ∈ Finset.Icc n m,
        accumulatedError M none i z s omega) ≤
          lambda * ((m : ℝ) - (n : ℝ))) :
    (∑ j ∈ Finset.Icc n l,
        holderRecurrenceEpsilon K M epsilon s j z omega) ≤
      3 * K * lambda * ((m : ℝ) - (n : ℝ) + 1) := by
  have hbase := sum_holderRecurrenceEpsilon_le
    (K := K) (epsilon := epsilon) (s := s) hK M omega z
      (n := n) (m := l + 2) (by omega)
  norm_num only [Nat.add_sub_cancel] at hbase
  have herrorSub :
      (∑ i ∈ Finset.Icc n (l + 2), accumulatedError M none i z s omega) ≤
        ∑ i ∈ Finset.Icc n m, accumulatedError M none i z s omega := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_Icc] at hi ⊢
      omega
    · intro i _ _
      exact accumulatedError_nonneg M none s i z omega
  have hcardNat : (Finset.Icc n l).card ≤ m + 1 - n := by
    rw [Nat.card_Icc]
    omega
  have hcard : ((Finset.Icc n l).card : ℝ) ≤ (m : ℝ) - (n : ℝ) + 1 := by
    have hcast : ((Finset.Icc n l).card : ℝ) ≤ ((m + 1 - n : ℕ) : ℝ) := by
      exact_mod_cast hcardNat
    rw [Nat.cast_sub (by omega : n ≤ m + 1), Nat.cast_add, Nat.cast_one] at hcast
    linarith
  have hgap : 0 ≤ (m : ℝ) - (n : ℝ) := by
    exact sub_nonneg.mpr (Nat.cast_le.2 (hnl.trans (by omega)))
  have hpair : M.delta ^ 2 + epsilon ^ 8 ≤ 2 * lambda := by linarith
  have hcard0 : 0 ≤ ((Finset.Icc n l).card : ℝ) := by positivity
  have hproduct := mul_le_mul hcard hpair (by positivity) (by positivity)
  have herror := herrorSub.trans herrors
  nlinarith

theorem holderRecurrenceDefect_nonneg
    {K rho exponential topForcing epsilonJ hLinfty topBoundary boundary : ℝ}
    (hK : 0 ≤ K) (hrho : 0 ≤ rho) (hexponential : 0 ≤ exponential)
    (hforcing : 0 ≤ topForcing) (hepsilonJ : 0 ≤ epsilonJ)
    (hLinfty0 : 0 ≤ hLinfty) (hboundaryTop : 0 ≤ topBoundary)
    (hboundary : 0 ≤ boundary) :
    0 ≤ holderRecurrenceDefect K rho exponential topForcing epsilonJ
      hLinfty topBoundary boundary := by
  unfold holderRecurrenceDefect
  positivity

theorem holderReadyDefect_nonneg
    {forcingConst meanConst boundaryConst rho exponential topForcing
      epsilonJ hLinfty topBoundary boundary : ℝ}
    (hforcingConst : 0 ≤ forcingConst) (hmeanConst : 0 ≤ meanConst)
    (hboundaryConst : 0 ≤ boundaryConst) (hrho : 0 ≤ rho)
    (hexponential : 0 ≤ exponential) (hforcing : 0 ≤ topForcing)
    (hepsilonJ : 0 ≤ epsilonJ) (hLinfty0 : 0 ≤ hLinfty)
    (hboundaryTop : 0 ≤ topBoundary) (hboundary : 0 ≤ boundary) :
    0 ≤ holderReadyDefect forcingConst meanConst boundaryConst rho exponential
      topForcing epsilonJ hLinfty topBoundary boundary := by
  unfold holderReadyDefect
  positivity

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
