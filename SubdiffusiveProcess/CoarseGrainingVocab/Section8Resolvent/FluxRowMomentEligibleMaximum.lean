import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszFixedShell
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.MomentAggregation




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Omega Code : Type*} [MeasurableSpace Omega] [DecidableEq Code]

/-- The maximum of a nonnegative observable over a nonempty eligible family. -/
def fluxRowMomentEligibleMaximum
    (eligible : Finset Code) (X : Code → Omega → ℝ≥0∞) : Omega → ℝ≥0∞ :=
  if heligible : eligible.Nonempty then eligible.sup' heligible X else 0

omit [DecidableEq Code] in
/-- Measurability of the finite eligible maximum, including the empty-family
case. -/
theorem measurable_fluxRowMomentEligibleMaximum
    (eligible : Finset Code) (X : Code → Omega → ℝ≥0∞)
    (hX : ∀ c ∈ eligible, Measurable (X c)) :
    Measurable (fluxRowMomentEligibleMaximum eligible X) := by
  by_cases heligible : eligible.Nonempty
  · rw [fluxRowMomentEligibleMaximum, dif_pos heligible]
    exact Finset.measurable_sup' heligible hX
  · rw [fluxRowMomentEligibleMaximum, dif_neg heligible]
    exact measurable_const

/-- **Eligible-code maximal inequality.**  A uniform fixed-code `p`-moment
costs only `card^(1/p)` after taking the finite maximum. -/
theorem paperENNRealLpNorm_fluxRowMomentEligibleMaximum_le
    (mu : Measure Omega) {p : ℝ} (hp : 0 < p)
    (eligible : Finset Code)
    (X : Code → Omega → ℝ≥0∞)
    (hX : ∀ c ∈ eligible, Measurable (X c)) (A : ℝ≥0∞)
    (hA : ∀ c ∈ eligible, paperENNRealLpNorm mu p (X c) ≤ A) :
    paperENNRealLpNorm mu p
        (fluxRowMomentEligibleMaximum eligible X) ≤
      (eligible.card : ℝ≥0∞) ^ p⁻¹ * A := by
  by_cases heligible : eligible.Nonempty
  · rw [fluxRowMomentEligibleMaximum, dif_pos heligible]
    exact paperENNRealLpNorm_finset_sup'_le_card_rpow_mul
      mu hp eligible heligible X hX A hA
  · rw [fluxRowMomentEligibleMaximum, dif_neg heligible,
      Finset.not_nonempty_iff_eq_empty.mp heligible]
    simp [paperENNRealLpNorm, hp, inv_pos.mpr hp]

omit [MeasurableSpace Omega] [DecidableEq Code] in
/-- Every member observable is bounded pointwise by the eligible maximum. -/
theorem le_fluxRowMomentEligibleMaximum
    (eligible : Finset Code) (X : Code → Omega → ℝ≥0∞)
    {c : Code} (hc : c ∈ eligible)
    (omega : Omega) :
    X c omega ≤ fluxRowMomentEligibleMaximum eligible X omega := by
  have heligible : eligible.Nonempty := ⟨c, hc⟩
  rw [fluxRowMomentEligibleMaximum, dif_pos heligible, Finset.sup'_apply]
  exact Finset.le_sup' (fun q ↦ X q omega) hc

/-! ## The fixed repaired shell -/

open Homogenization
open SubdiffusiveProcess.Frozen.Assumptions

/-- The weighted fixed-code summand before exact-sphere selection. -/
def fluxRowMomentFixedCodeTerm {d : ℕ}
    (R : ℝ) (W : RepairedStoppingCellCode d → Omega → ℝ≥0∞)
    (c : RepairedStoppingCellCode d) (omega : Omega) : ℝ≥0∞ :=
  ENNReal.ofReal
      ((((3 : ℝ) ^ repairedStoppingCellCodeScale c) / R) ^ (d + 6)) *
    W c omega

omit [MeasurableSpace Omega] in
/-- A fixed repaired shell is bounded by the eligible-family cardinality
times the eligible maximum whenever every active code is eligible. -/
theorem fixedRepairedShellSum_le_card_mul_eligibleMaximum
    {d : ℕ} (failure : TriadicCube d → Set Omega) (base : ℤ)
    (x0 : Vec d) (R : ℝ)
    (W : RepairedStoppingCellCode d → Omega → ℝ≥0∞)
    (j : ℕ) (omega : Omega)
    (eligible : Finset (RepairedStoppingCellCode d))
    (hsubset : ∀ c,
      IsExactRepairedStoppingCodeSphere failure base x0 R j omega c →
        c ∈ eligible) :
    fixedRepairedShellSum failure base x0 R W j omega ≤
      (eligible.card : ℝ≥0∞) *
        fluxRowMomentEligibleMaximum eligible
          (fluxRowMomentFixedCodeTerm R W) omega := by
  let X := fluxRowMomentFixedCodeTerm R W
  let M := fluxRowMomentEligibleMaximum eligible X omega
  have hpoint : ∀ c : RepairedStoppingCellCode d,
      (if IsExactRepairedStoppingCodeSphere failure base x0 R j omega c then
          X c omega else 0) ≤
        if c ∈ eligible then M else 0 := by
    intro c
    by_cases hc : IsExactRepairedStoppingCodeSphere
        failure base x0 R j omega c
    · rw [if_pos hc, if_pos (hsubset c hc)]
      exact le_fluxRowMomentEligibleMaximum eligible X (hsubset c hc) omega
    · rw [if_neg hc]
      exact zero_le _
  unfold fixedRepairedShellSum
  change (∑' c : RepairedStoppingCellCode d,
    if IsExactRepairedStoppingCodeSphere failure base x0 R j omega c then
      X c omega else 0) ≤ _
  calc
    _ ≤ ∑' c : RepairedStoppingCellCode d,
        if c ∈ eligible then M else 0 := ENNReal.tsum_le_tsum hpoint
    _ = ∑ c ∈ eligible, M := by
      exact tsum_ite_eq_finset_sum_comp eligible id Function.injective_id
        (fun c ↦ c ∈ eligible) (fun c ↦ by simp) (fun _ ↦ M)
    _ = (eligible.card : ℝ≥0∞) * M := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
