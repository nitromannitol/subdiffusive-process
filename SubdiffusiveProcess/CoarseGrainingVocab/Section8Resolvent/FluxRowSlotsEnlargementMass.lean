/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszRepairedCellPrice

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.Frozen.Section8

noncomputable section

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- The dimension-only constant paid for moving the graph decay from a stopping
cell to its centred threefold enlargement: the closed-neighbour multiplicity
`D(d) + 1` times one inverse power of the pointwise contraction factor. -/
def fluxRowSlotsEnlargementConstant (d : ℕ) : ℝ :=
  ((repairedStoppingDegreeBound d : ℝ) + 1) *
    (repairedStoppingPointwiseContractionFactor d)⁻¹

omit [NeZero d] in
theorem fluxRowSlotsEnlargementConstant_pos :
    0 < fluxRowSlotsEnlargementConstant d := by
  unfold fluxRowSlotsEnlargementConstant
  have h1 : (0 : ℝ) < (repairedStoppingDegreeBound d : ℝ) + 1 := by positivity
  have h2 : 0 < repairedStoppingPointwiseContractionFactor d :=
    repairedStoppingPointwiseContractionFactor_pos
  positivity

/-- **The graph decay on the enlargement of a stopping cell.**

Same hypotheses as `wholeSpaceSolution_cell_mass_le_repairedStoppingPointwiseDecay`;
the conclusion is the same `θ^{dist/2}` slot, on the centred threefold
enlargement, at the cost of the dimension-only constant
`fluxRowSlotsEnlargementConstant d`. -/
theorem wholeSpaceSolution_enlargement_mass_le_repairedStoppingDecay
    {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsource q →
        ∫ x in translatedCube d (refinedStoppingScale q)
            (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
          repairedStoppingContractionFactor d *
            ∫ x in translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume)
    (q : RefinedStoppingCell failure omega base) :
    ∫ x in translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
      fluxRowSlotsEnlargementConstant d *
        Real.rpow (repairedStoppingPointwiseContractionFactor d ^ 2)
          ((stoppingGraphDistance repairedStoppingGraph source hsource q : ℝ)
            / 2) *
        ∫ x, f x ^ 2 ∂volume := by
  classical
  set theta : ℝ := repairedStoppingPointwiseContractionFactor d with htheta_def
  have hthetapos : 0 < theta := repairedStoppingPointwiseContractionFactor_pos
  have hthetalt : theta < 1 := repairedStoppingPointwiseContractionFactor_lt_one
  set level : RefinedStoppingCell failure omega base → ℕ :=
    stoppingGraphDistance repairedStoppingGraph source hsource with hlevel_def
  have hfEnergy : 0 ≤ ∫ x, f x ^ 2 ∂volume :=
    integral_nonneg fun x ↦ sq_nonneg (f x)
  obtain ⟨p, hp, hcov⟩ :=
    exists_mem_integral_sq_le_card_mul_of_finset_cover u.memL2_toFun
      (repairedStoppingClosedNeighbors q)
      (repairedStoppingClosedNeighbors_nonempty q)
      (fun p ↦ translatedCube d (refinedStoppingScale p)
        (refinedStoppingCenter p))
      (refinedStoppingCell_enlargement_subset_iUnion_closedNeighbors
        hinitial hrepair q)
  have hstep : level q ≤ level p + 1 := by
    rcases eq_or_adj_of_mem_repairedStoppingClosedNeighbors hp with rfl | hadj
    · omega
    · exact repairedStoppingGraphDistance_le_succ_of_adj hinitial hrepair
        source hsource hadj
  have hdecay := wholeSpaceSolution_cell_mass_le_repairedStoppingPointwiseDecay
    u hL2 hinitial hrepair source hsource hcell p
  have hmassp : 0 ≤ ∫ x in translatedCube d (refinedStoppingScale p)
      (refinedStoppingCenter p), u.toFun x ^ 2 ∂volume :=
    setIntegral_nonneg
      (isOpenBoundedConvexDomain_translatedCube (d := d)
        (refinedStoppingScale p) (refinedStoppingCenter p)).isOpen.measurableSet
      fun x _ ↦ sq_nonneg (u.toFun x)
  have hcard : ((repairedStoppingClosedNeighbors q).card : ℝ) ≤
      ((repairedStoppingDegreeBound d : ℝ) + 1) := by
    have := card_repairedStoppingClosedNeighbors_le (d := d) q
    exact_mod_cast this
  -- the decay exponent at `p` is at least `level q - 1`
  have hpow : theta ^ level p ≤ theta ^ (level q - 1) :=
    pow_le_pow_of_le_one hthetapos.le hthetalt.le (by omega)
  have hshift : theta ^ (level q - 1) ≤ theta⁻¹ * theta ^ level q := by
    rcases Nat.eq_zero_or_pos (level q) with hz | hz
    · rw [hz]
      have h1 : (1 : ℝ) ≤ theta⁻¹ := (one_le_inv₀ hthetapos).mpr hthetalt.le
      simpa using h1
    · obtain ⟨j, hj⟩ : ∃ j, level q = j + 1 := ⟨level q - 1, by omega⟩
      rw [hj]
      have : theta⁻¹ * theta ^ (j + 1) = theta ^ j := by
        field_simp [pow_succ]
        ring
      simp [this]
  have hthetaq : theta ^ level q =
      Real.rpow (theta ^ 2) ((level q : ℝ) / 2) :=
    (fluxRowRiesz_rpow_half_sq hthetapos.le (level q)).symm
  calc
    ∫ x in translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume
        ≤ ((repairedStoppingClosedNeighbors q).card : ℝ) *
            ∫ x in translatedCube d (refinedStoppingScale p)
              (refinedStoppingCenter p), u.toFun x ^ 2 ∂volume := hcov
    _ ≤ ((repairedStoppingDegreeBound d : ℝ) + 1) *
            ∫ x in translatedCube d (refinedStoppingScale p)
              (refinedStoppingCenter p), u.toFun x ^ 2 ∂volume := by
          exact mul_le_mul_of_nonneg_right hcard hmassp
    _ ≤ ((repairedStoppingDegreeBound d : ℝ) + 1) *
            (theta ^ level p * ∫ x, f x ^ 2 ∂volume) := by
          refine mul_le_mul_of_nonneg_left hdecay ?_
          positivity
    _ ≤ ((repairedStoppingDegreeBound d : ℝ) + 1) *
            (theta⁻¹ * theta ^ level q * ∫ x, f x ^ 2 ∂volume) := by
          have hle : theta ^ level p ≤ theta⁻¹ * theta ^ level q :=
            hpow.trans hshift
          have hnn : (0 : ℝ) ≤ (repairedStoppingDegreeBound d : ℝ) + 1 := by
            positivity
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hle hfEnergy) hnn
    _ = fluxRowSlotsEnlargementConstant d *
          Real.rpow (theta ^ 2) ((level q : ℝ) / 2) *
          ∫ x, f x ^ 2 ∂volume := by
          unfold fluxRowSlotsEnlargementConstant
          rw [← hthetaq]
          ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
