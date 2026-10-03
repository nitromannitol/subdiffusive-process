module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.IntervalGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.BadScales
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.BadScales
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.RecurrenceBudget

@[expose] public section

/-!
# Hölder Steps 3--4: concrete iteration families

The abstract iteration lemma is indexed by integers.  This file extends the
manuscript's natural-scale `epsilon_{j,z}` and `delta_{j,z}` rows by zero to
negative indices, and proves their interval budgets on the actual carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder

open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section

variable {L : ℕ}
attribute [local instance] Classical.propDecidable


/-- Integer extension of the concrete recurrence coefficient. -/
def holderIterationEpsilon_cut {d : ℕ} (L : ℕ)
    (K : ℝ) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (epsilon s : ℝ)
    (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (j : ℤ) : ℝ :=
  if 0 ≤ j then holderRecurrenceEpsilon_cut L K M epsilon s j.toNat z omega else 0

/-- Integer extension of the concrete recurrence defect. -/
def holderIterationDefect_cut {d : ℕ} (L : ℕ)
    (forcingConst meanConst boundaryConst exponential topForcing hLinfty
      topBoundary : ℝ)
    (K : ℝ) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (epsilon s : ℝ)
    (domain : ℕ) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (j : ℤ) : ℝ :=
  if 0 ≤ j then
    holderReadyDefect_cut forcingConst meanConst boundaryConst
      ((3 : ℝ) ^ (-(((domain : ℝ) - (j.toNat : ℝ)) / 2)))
      exponential topForcing
      (holderRecurrenceEpsilon_cut L K M epsilon s j.toNat z omega) hLinfty topBoundary
      (if BoundaryTouches (truncatedCube d domain j.toNat z) (cube d domain) then 1 else 0)
  else 0

theorem holderIterationEpsilon_of_nonneg_cut {d : ℕ}
    (K : ℝ) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (epsilon s : ℝ)
    (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {j : ℤ} (hj : 0 ≤ j) :
    holderIterationEpsilon_cut L K M epsilon s z omega j =
      holderRecurrenceEpsilon_cut L K M epsilon s j.toNat z omega := by
  simp only [holderIterationEpsilon_cut, if_pos hj]

theorem holderIterationDefect_of_nonneg_cut {d : ℕ}
    (forcingConst meanConst boundaryConst exponential topForcing hLinfty
      topBoundary : ℝ)
    (K : ℝ) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (epsilon s : ℝ)
    (domain : ℕ) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {j : ℤ} (hj : 0 ≤ j) :
    holderIterationDefect_cut L forcingConst meanConst boundaryConst exponential topForcing
        hLinfty topBoundary K M epsilon s domain z omega j =
      holderReadyDefect_cut forcingConst meanConst boundaryConst
        ((3 : ℝ) ^ (-(((domain : ℝ) - (j.toNat : ℝ)) / 2)))
        exponential topForcing
        (holderRecurrenceEpsilon_cut L K M epsilon s j.toNat z omega) hLinfty topBoundary
        (if BoundaryTouches (truncatedCube d domain j.toNat z) (cube d domain) then 1 else 0) := by
  simp only [holderIterationDefect_cut, if_pos hj]

theorem holderIterationEpsilon_nonneg_cut {d : ℕ}
    {K epsilon s : ℝ} (hK : 0 ≤ K) (hepsilon : 0 ≤ epsilon)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (j : ℤ) :
    0 ≤ holderIterationEpsilon_cut L K M epsilon s z omega j := by
  unfold holderIterationEpsilon_cut
  split_ifs with hj
  · exact holderRecurrenceEpsilon_nonneg_cut hK hepsilon M j.toNat z omega
  · exact le_rfl

theorem holderIterationDefect_nonneg_cut {d : ℕ}
    {forcingConst meanConst boundaryConst exponential topForcing hLinfty
      topBoundary K epsilon s : ℝ}
    (hforcingConst : 0 ≤ forcingConst) (hmeanConst : 0 ≤ meanConst)
    (hboundaryConst : 0 ≤ boundaryConst) (hexponential : 0 ≤ exponential)
    (htopForcing : 0 ≤ topForcing) (hLinfty0 : 0 ≤ hLinfty)
    (htopBoundary : 0 ≤ topBoundary) (hK : 0 ≤ K) (hepsilon : 0 ≤ epsilon)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (domain : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (j : ℤ) :
    0 ≤ holderIterationDefect_cut L forcingConst meanConst boundaryConst exponential
      topForcing hLinfty topBoundary K M epsilon s domain z omega j := by
  by_cases hj : 0 ≤ j
  · rw [holderIterationDefect_cut, if_pos hj]
    apply holderReadyDefect_nonneg_cut hforcingConst hmeanConst hboundaryConst
      (Real.rpow_nonneg (by norm_num) _) hexponential htopForcing
      (holderRecurrenceEpsilon_nonneg_cut hK hepsilon M j.toNat z omega)
      hLinfty0 htopBoundary
    by_cases hb : BoundaryTouches (truncatedCube d domain j.toNat z) (cube d domain) <;>
      simp only [hb, if_pos] <;> norm_num
  · rw [holderIterationDefect_cut, if_neg hj]

/-- Summation over a nonnegative integer interval is unchanged by passing to
the corresponding natural interval. -/
theorem sum_Icc_int_eq_sum_Icc_nat_cut (f : ℤ → ℝ) (n m : ℕ) :
    ∑ j ∈ Finset.Icc (n : ℤ) (m : ℤ), f j =
      ∑ j ∈ Finset.Icc n m, f (j : ℤ) := by
  refine Finset.sum_nbij' (fun j : ℤ ↦ j.toNat) (fun j : ℕ ↦ (j : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    constructor <;> omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    exact ⟨Int.ofNat_le.mpr hj.1, Int.ofNat_le.mpr hj.2⟩
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    exact Int.toNat_of_nonneg ((Int.natCast_nonneg n).trans hj.1)
  · intro j _
    simp
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    rw [Int.toNat_of_nonneg ((Int.natCast_nonneg n).trans hj.1)]

/-- Exact conversion of the integer recurrence row to the natural one. -/
theorem sum_holderIterationEpsilon_eq_cut {d : ℕ}
    (K : ℝ) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (epsilon s : ℝ)
    (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (n m : ℕ) :
    ∑ j ∈ Finset.Icc (n : ℤ) (m : ℤ),
        holderIterationEpsilon_cut L K M epsilon s z omega j =
      ∑ j ∈ Finset.Icc n m,
        holderRecurrenceEpsilon_cut L K M epsilon s j z omega := by
  rw [sum_Icc_int_eq_sum_Icc_nat_cut]
  apply Finset.sum_congr rfl
  intro j _
  rw [holderIterationEpsilon_of_nonneg_cut]
  · simp
  · exact Int.natCast_nonneg j

/-- The summed concrete defect, in the exact form of
`e.delta.j.z.sum` before the final parameter absorption. -/
theorem sum_holderIterationDefect_le_cut {d : ℕ}
    {forcingConst meanConst boundaryConst exponential topForcing hLinfty
      topBoundary K epsilon s E : ℝ}
    (hforcingConst : 0 ≤ forcingConst) (hmeanConst : 0 ≤ meanConst)
    (hboundaryConst : 0 ≤ boundaryConst) (hexponential : 0 ≤ exponential)
    (htopForcing : 0 ≤ topForcing) (hLinfty0 : 0 ≤ hLinfty)
    (htopBoundary : 0 ≤ topBoundary) (hK : 0 ≤ K) (hepsilon : 0 ≤ epsilon)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (domain n l : ℕ)
    (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hnl : n ≤ l)
    (hE : ∑ j ∈ Finset.Icc n l,
        holderRecurrenceEpsilon_cut L K M epsilon s j z omega ≤ E) :
    ∑ j ∈ Finset.Icc (n : ℤ) (l : ℤ),
        holderIterationDefect_cut L forcingConst meanConst boundaryConst exponential
          topForcing hLinfty topBoundary K M epsilon s domain z omega j ≤
      (5 / 2 : ℝ) * forcingConst *
          (3 : ℝ) ^ (-(((domain : ℝ) - (l : ℝ)) / 2)) *
          exponential * topForcing +
        meanConst * E * hLinfty *
          (if BoundaryTouches (truncatedCube d domain l z) (cube d domain) then 1 else 0) +
        (5 / 2 : ℝ) * boundaryConst *
          (3 : ℝ) ^ (-(((domain : ℝ) - (l : ℝ)) / 2)) * topBoundary *
          (if BoundaryTouches (truncatedCube d domain l z) (cube d domain) then 1 else 0) := by
  rw [sum_Icc_int_eq_sum_Icc_nat_cut]
  simp_rw [holderIterationDefect_cut, if_pos (Int.natCast_nonneg _)]
  let B : ℕ → ℝ := fun j ↦
    if BoundaryTouches (truncatedCube d domain j z) (cube d domain) then 1 else 0
  let rho : ℕ → ℝ := fun j ↦
    (3 : ℝ) ^ (-(((domain : ℝ) - (j : ℝ)) / 2))
  let ep : ℕ → ℝ := fun j ↦ holderRecurrenceEpsilon_cut L K M epsilon s j z omega
  have hB0 : ∀ j, 0 ≤ B j := by intro j; dsimp only [B]; split_ifs <;> norm_num
  have hBle : ∀ j ∈ Finset.Icc n l, B j ≤ B l := by
    intro j hj
    exact boundaryIndicator_truncatedCube_le (by exact_mod_cast (Finset.mem_Icc.1 hj).2)
  have hep0 : ∀ j, 0 ≤ ep j := fun j ↦
    holderRecurrenceEpsilon_nonneg_cut hK hepsilon M j z omega
  have hrho : ∑ j ∈ Finset.Icc n l, rho j ≤ (5 / 2 : ℝ) * rho l := by
    have hgeo := sum_Icc_three_parent_half_le (n := (n : ℤ)) (l := (l : ℤ))
      (m := (domain : ℤ)) (by exact_mod_cast hnl)
    rw [sum_Icc_int_eq_sum_Icc_nat_cut] at hgeo
    push_cast at hgeo
    simpa only [rho, Int.toNat_natCast] using! hgeo
  have hsumForcing :
      ∑ j ∈ Finset.Icc n l, forcingConst * rho j * exponential * topForcing ≤
        (5 / 2 : ℝ) * forcingConst * rho l * exponential * topForcing := by
    calc
      _ = (forcingConst * exponential * topForcing) *
          (∑ j ∈ Finset.Icc n l, rho j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ (forcingConst * exponential * topForcing) * ((5 / 2 : ℝ) * rho l) :=
        mul_le_mul_of_nonneg_left hrho
          (mul_nonneg (mul_nonneg hforcingConst hexponential) htopForcing)
      _ = _ := by ring
  have hsumMean :
      ∑ j ∈ Finset.Icc n l, meanConst * ep j * hLinfty * B j ≤
        meanConst * E * hLinfty * B l := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc n l, meanConst * ep j * hLinfty * B l := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hBle j hj)
          (mul_nonneg (mul_nonneg hmeanConst (hep0 j)) hLinfty0)
      _ = (meanConst * hLinfty * B l) * (∑ j ∈ Finset.Icc n l, ep j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ meanConst * E * hLinfty * B l := by
        have hcoef : 0 ≤ meanConst * hLinfty * B l := by positivity
        have := mul_le_mul_of_nonneg_left hE hcoef
        nlinarith
  have hsumBoundary :
      ∑ j ∈ Finset.Icc n l, boundaryConst * rho j * topBoundary * B j ≤
        (5 / 2 : ℝ) * boundaryConst * rho l * topBoundary * B l := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc n l, boundaryConst * rho j * topBoundary * B l := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hBle j hj)
          (mul_nonneg (mul_nonneg hboundaryConst (Real.rpow_nonneg (by norm_num) _))
            htopBoundary)
      _ = boundaryConst * topBoundary * B l * (∑ j ∈ Finset.Icc n l, rho j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ boundaryConst * topBoundary * B l * ((5 / 2 : ℝ) * rho l) := by
        gcongr
      _ = (5 / 2 : ℝ) * boundaryConst * rho l * topBoundary * B l := by ring
  simp only [Int.toNat_natCast, holderReadyDefect_cut]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith

/-- The paired interval budgets `e.ep.j.z.sum` and `e.delta.j.z.sum` for the
integer rows passed to the iteration lemma. -/
theorem holderIteration_interval_budgets_cut {d : ℕ}
    {forcingConst meanConst boundaryConst exponential topForcing hLinfty
      topBoundary K epsilon s lambda : ℝ}
    (hforcingConst : 0 ≤ forcingConst) (hmeanConst : 0 ≤ meanConst)
    (hboundaryConst : 0 ≤ boundaryConst) (hexponential : 0 ≤ exponential)
    (htopForcing : 0 ≤ topForcing) (hLinfty0 : 0 ≤ hLinfty)
    (htopBoundary : 0 ≤ topBoundary) (hK : 0 ≤ K) (hepsilon0 : 0 ≤ epsilon)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (domain n top : ℕ)
    (hlambda : 0 ≤ lambda) (hdelta : M.delta ^ 2 ≤ lambda)
    (hepsilon8 : epsilon ^ 8 ≤ lambda)
    (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hntop : n ≤ top) (htopDomain : top + 2 ≤ domain)
    (herrors : (∑ i ∈ Finset.Icc n domain,
        accumulatedError M (some L) i z s omega) ≤
          lambda * ((domain : ℝ) - (n : ℝ))) :
    let E := 3 * K * lambda * ((domain : ℝ) - (n : ℝ) + 1)
    (∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ),
        holderIterationEpsilon_cut L K M epsilon s z omega j) ≤ E ∧
    (∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ),
        holderIterationDefect_cut L forcingConst meanConst boundaryConst exponential
          topForcing hLinfty topBoundary K M epsilon s domain z omega j) ≤
      (5 / 2 : ℝ) * forcingConst *
          (3 : ℝ) ^ (-(((domain : ℝ) - (top : ℝ)) / 2)) *
          exponential * topForcing +
        meanConst * E * hLinfty *
          (if BoundaryTouches (truncatedCube d domain top z) (cube d domain) then 1 else 0) +
        (5 / 2 : ℝ) * boundaryConst *
          (3 : ℝ) ^ (-(((domain : ℝ) - (top : ℝ)) / 2)) * topBoundary *
          (if BoundaryTouches (truncatedCube d domain top z) (cube d domain) then 1 else 0) := by
  dsimp only
  have hepsNat := sum_holderRecurrenceEpsilon_interval_le_three_mul_cut hK hlambda
    M omega z hntop htopDomain hdelta hepsilon8 herrors
  have hepsInt :
      (∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ),
        holderIterationEpsilon_cut L K M epsilon s z omega j) ≤
      3 * K * lambda * ((domain : ℝ) - (n : ℝ) + 1) := by
    rw [sum_holderIterationEpsilon_eq_cut]
    exact hepsNat
  exact ⟨hepsInt, sum_holderIterationDefect_le_cut hforcingConst hmeanConst
    hboundaryConst hexponential htopForcing hLinfty0 htopBoundary hK hepsilon0
    M domain n top z omega hntop hepsNat⟩

/-- The explicit exponential budget in Step 4, obtained from the cardinality
of the bad set and the summed recurrence coefficients. -/
theorem holderIterationExponent_le_cut {d : ℕ}
    {K Citer epsilon s lambda : ℝ} (hK : 0 ≤ K) (hCiter : 0 ≤ Citer)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (domain n top k : ℕ)
    (hlambda : 0 ≤ lambda) (hdelta : M.delta ^ 2 ≤ lambda)
    (hepsilon8 : epsilon ^ 8 ≤ lambda)
    (z : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hntop : n ≤ top) (htopDomain : top + 2 ≤ domain)
    (herrors : (∑ i ∈ Finset.Icc n domain,
        accumulatedError M (some L) i z s omega) ≤
          lambda * ((domain : ℝ) - (n : ℝ)))
    (hfail : (∑ i ∈ Finset.Icc n domain,
        ((1 : ℝ) - if omega ∈ goodEvent M (some L) i z epsilon s then 1 else 0)) <
          1 + lambda * ((domain : ℝ) - (n : ℝ))) :
    let bad := holderBadScales_cut L M epsilon s n top k z omega
    let epsRow := holderIterationEpsilon_cut L K M epsilon s z omega
    let A := Citer * (k + 1) * (bad.card + 1) +
      Citer * ∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ), epsRow j
    A ≤ Citer * (k + 1) *
          ((k : ℝ) + 2 + lambda * ((domain : ℝ) - (n : ℝ))) +
        Citer * (3 * K * lambda * ((domain : ℝ) - (n : ℝ) + 1)) := by
  dsimp only
  have hfailSub := sum_shiftTwo_goodFailure_le_cut (L := L) M epsilon s z omega
    (n := n) (top := top) (domain := domain) htopDomain
  have hfailShift :
      (∑ j ∈ Finset.Icc n top,
        ((1 : ℝ) - if omega ∈ goodEvent M (some L) (j + 2) z epsilon s then 1 else 0)) <
          1 + lambda * ((domain : ℝ) - (n : ℝ)) := hfailSub.trans_lt hfail
  have hcard := holderBadScales_card_lt_of_bound_cut M epsilon s
    (1 + lambda * ((domain : ℝ) - (n : ℝ))) n top k z omega hfailShift
  have hcardOne :
      (((holderBadScales_cut L M epsilon s n top k z omega).card + 1 : ℕ) : ℝ) ≤
        (k : ℝ) + 2 + lambda * ((domain : ℝ) - (n : ℝ)) := by
    push_cast
    linarith
  have hepsNat := sum_holderRecurrenceEpsilon_interval_le_three_mul_cut hK hlambda
    M omega z hntop htopDomain hdelta hepsilon8 herrors
  have heps :
      (∑ j ∈ Finset.Icc (n : ℤ) (top : ℤ),
        holderIterationEpsilon_cut L K M epsilon s z omega j) ≤
      3 * K * lambda * ((domain : ℝ) - (n : ℝ) + 1) := by
    rw [sum_holderIterationEpsilon_eq_cut]
    exact hepsNat
  have hk0 : (0 : ℝ) ≤ k + 1 := by positivity
  have hfirst := mul_le_mul_of_nonneg_left hcardOne (mul_nonneg hCiter hk0)
  have hsecond := mul_le_mul_of_nonneg_left heps hCiter
  norm_num only [Nat.cast_add, Nat.cast_one] at hfirst ⊢
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder
