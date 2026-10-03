/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsRepairedDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsNinefoldMass

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The dimension-only constant of the ninefold forcing mass: one inverse power
of the pointwise contraction factor for the `f`-leg on the two innermost graph
spheres, plus the closed-neighbour constant for the `u`-leg. -/
def fluxRowSlotsNinefoldForcingConstant (d : ℕ) : ℝ :=
  (repairedStoppingPointwiseContractionFactor d)⁻¹ +
    fluxRowSlotsEnlargementConstant d

theorem fluxRowSlotsNinefoldForcingConstant_pos :
    0 < fluxRowSlotsNinefoldForcingConstant d := by
  unfold fluxRowSlotsNinefoldForcingConstant
  have h1 : 0 < (repairedStoppingPointwiseContractionFactor d)⁻¹ :=
    inv_pos.mpr repairedStoppingPointwiseContractionFactor_pos
  have h2 : 0 < fluxRowSlotsEnlargementConstant d :=
    fluxRowSlotsEnlargementConstant_pos
  linarith

section MassLeg

variable [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- **The source vanishes on the ninefold enlargement, two hops out.**

The closed neighbourhood covers the ninefold
(`refinedStoppingCell_ninefold_subset_iUnion_closedNeighbors`) and a neighbour
loses at most one unit of graph distance, so at graph distance at least two
every point of the ninefold lies in a cell that is itself at positive graph
distance, where the existing threefold hypothesis applies. -/
theorem forall_eq_zero_ninefold_of_two_le_stoppingGraphDistance
    {f : Vec d → ℝ}
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty)
    (hf0 : ∀ q, 0 < stoppingGraphDistance repairedStoppingGraph source hsource q →
      ∀ x ∈ translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q), f x = 0)
    {q : RefinedStoppingCell failure omega base}
    (hq : 2 ≤ stoppingGraphDistance repairedStoppingGraph source hsource q)
    {x : Vec d}
    (hx : x ∈ translatedCube d (refinedStoppingScale q + 2)
      (refinedStoppingCenter q)) :
    f x = 0 := by
  classical
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp
    (refinedStoppingCell_ninefold_subset_iUnion_closedNeighbors
      hinitial hrepair q hx)
  have hstep : stoppingGraphDistance repairedStoppingGraph source hsource q ≤
      stoppingGraphDistance repairedStoppingGraph source hsource p + 1 := by
    rcases eq_or_adj_of_mem_repairedStoppingClosedNeighbors hp with rfl | hadj
    · omega
    · exact repairedStoppingGraphDistance_le_succ_of_adj hinitial hrepair
        source hsource hadj
  have hppos : 0 < stoppingGraphDistance repairedStoppingGraph source hsource p := by
    omega
  exact hf0 p hppos x
    (translatedCube_subset_succ d (refinedStoppingScale p)
      (refinedStoppingCenter p) hxp)

/-- **The uniform forcing mass on the ninefold enlargement.**

Companion of `wholeSpaceSolution_enlargement_forcing_mass_le_repairedStoppingDecay`
with the carrier moved from `z + □_{m+1}` to `z + □_{m+2}`, at the cost of one
inverse power of the pointwise contraction factor.  The hypotheses are
*unchanged*: in particular the source-vanishing hypothesis is still the
threefold one. -/
theorem wholeSpaceSolution_ninefold_forcing_mass_le_repairedStoppingDecay
    {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hf : Integrable (fun x ↦ f x ^ 2) volume)
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
    (hf0 : ∀ q, 0 < stoppingGraphDistance repairedStoppingGraph source hsource q →
      ∀ x ∈ translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q), f x = 0)
    (q : RefinedStoppingCell failure omega base) :
    (∫ x in translatedCube d (refinedStoppingScale q + 2)
        (refinedStoppingCenter q), f x ^ 2 ∂volume) +
      (∫ x in translatedCube d (refinedStoppingScale q + 2)
        (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume) ≤
      fluxRowSlotsNinefoldForcingConstant d *
        (Real.rpow (repairedStoppingPointwiseContractionFactor d ^ 2)
            ((stoppingGraphDistance repairedStoppingGraph source hsource q : ℝ)
              / 2) *
          ∫ x, f x ^ 2 ∂volume) := by
  classical
  set theta : ℝ := repairedStoppingPointwiseContractionFactor d with htheta_def
  have hthetapos : 0 < theta := repairedStoppingPointwiseContractionFactor_pos
  have hthetalt : theta < 1 := repairedStoppingPointwiseContractionFactor_lt_one
  set gd : ℕ := stoppingGraphDistance repairedStoppingGraph source hsource q
    with hgd
  set fEnergy : ℝ := ∫ x, f x ^ 2 ∂volume with hfE
  have hfEnonneg : 0 ≤ fEnergy := integral_nonneg fun x ↦ sq_nonneg (f x)
  have hrpow : Real.rpow (theta ^ 2) ((gd : ℝ) / 2) = theta ^ gd :=
    fluxRowRiesz_rpow_half_sq hthetapos.le gd
  have hCenl : 0 < fluxRowSlotsEnlargementConstant d :=
    fluxRowSlotsEnlargementConstant_pos
  have hdecay := wholeSpaceSolution_ninefold_mass_le_repairedStoppingDecay
    u hL2 hinitial hrepair source hsource hcell q
  rw [← hgd, ← hfE, ← htheta_def, mul_assoc, hrpow] at hdecay
  have hthetapow : 0 < theta ^ gd := pow_pos hthetapos gd
  rcases le_or_gt 2 gd with hge | hlt
  · -- two hops out: the `f`-leg vanishes on the ninefold
    have hfzero : (∫ x in translatedCube d (refinedStoppingScale q + 2)
        (refinedStoppingCenter q), f x ^ 2 ∂volume) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero ?_
      intro x hx
      rw [forall_eq_zero_ninefold_of_two_le_stoppingGraphDistance
        hinitial hrepair source hsource hf0 (by omega) hx]
      ring
    rw [hfzero, zero_add, fluxRowSlotsNinefoldForcingConstant, hrpow]
    have hinv : 0 < theta⁻¹ := inv_pos.mpr hthetapos
    nlinarith [hdecay, mul_nonneg hthetapow.le hfEnonneg]
  · -- at most one hop out: one inverse power of `theta` absorbs the source
    have hfleg : (∫ x in translatedCube d (refinedStoppingScale q + 2)
        (refinedStoppingCenter q), f x ^ 2 ∂volume) ≤ fEnergy := by
      refine setIntegral_le_integral hf ?_
      exact Filter.Eventually.of_forall fun x ↦ sq_nonneg (f x)
    have habsorb : fEnergy ≤ theta⁻¹ * (theta ^ gd * fEnergy) := by
      have hle : theta ≤ theta ^ gd := by
        interval_cases gd
        · simpa using hthetalt.le
        · simp
      have : theta * fEnergy ≤ theta ^ gd * fEnergy :=
        mul_le_mul_of_nonneg_right hle hfEnonneg
      have hinvpos : 0 < theta⁻¹ := inv_pos.mpr hthetapos
      have := mul_le_mul_of_nonneg_left this hinvpos.le
      rw [← mul_assoc, inv_mul_cancel₀ hthetapos.ne', one_mul] at this
      exact this
    rw [fluxRowSlotsNinefoldForcingConstant, hrpow]
    have hsum := add_le_add hfleg hdecay
    refine hsum.trans ?_
    nlinarith [habsorb, mul_nonneg hthetapow.le hfEnonneg]

end MassLeg

/-! ## The datum antecedent with the ninefold carrier -/

section RepairedDatumSlot

variable [NeZero d] {base : ℤ}
  {failure : TriadicCube d → Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)}
  {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}

/-- **The `D²` datum slot on a refined stopping cell, with the ninefold
forcing mass.**

Identical to `wholeSpaceSolution_fluxRowSlots_datum_slot_coarse_repairedStoppingCell`
except that `hdatum`'s forcing mass is measured on `z + □_{m+2}` and the budget
constant is `fluxRowSlotsNinefoldForcingConstant d`. -/
theorem wholeSpaceSolution_fluxRowSlots_datum_slot_coarse_ninefoldCell
    {a f : Vec d → ℝ} {alpha t R sigma Ndatum : ℝ}
    {D : RefinedStoppingCell failure omega base → ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hf : Integrable (fun x ↦ f x ^ 2) volume)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsource q →
        ∫ x in translatedCube d (refinedStoppingScale q)
            (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
          repairedStoppingContractionFactor d *
            ∫ x in translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume)
    (hf0 : ∀ q, 0 < stoppingGraphDistance repairedStoppingGraph source hsource q →
      ∀ x ∈ translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q), f x = 0)
    (hN : 0 ≤ Ndatum)
    (q : RefinedStoppingCell failure omega base)
    (hdatum :
      (repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q *
          D q ^ 2 ≤
        Ndatum *
          ((∫ x in translatedCube d (refinedStoppingScale q + 2)
              (refinedStoppingCenter q), f x ^ 2 ∂volume) +
            ∫ x in translatedCube d (refinedStoppingScale q + 2)
              (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume))
    (hbudget : Ndatum * fluxRowSlotsNinefoldForcingConstant d ≤
      alpha * t⁻¹ * Real.rpow R (2 * sigma) *
        (((3 : ℝ) ^ refinedStoppingScale q) / R) ^ (d + 6)) :
    (repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q *
        D q ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma (∫ x, f x ^ 2 ∂volume)
        (repairedStoppingPointwiseContractionFactor d ^ 2)
        ((3 : ℝ) ^ refinedStoppingScale q)
        (stoppingGraphDistance repairedStoppingGraph source hsource q) d :=
  fluxRowSlots_datum_slot_of_inputs_const (d := d) hN
    fluxRowSlotsNinefoldForcingConstant_pos.le
    (integral_nonneg fun x ↦ sq_nonneg (f x)) (sq_nonneg _) hdatum
    (wholeSpaceSolution_ninefold_forcing_mass_le_repairedStoppingDecay u hf
      hL2 hinitial hrepair source hsource hcell hf0 q)
    hbudget

/-- **The ninefold datum antecedent in the literal `D = 3^{s n} [g₀]` shape.**

The exact companion of
`wholeSpaceSolution_fluxRowSlots_datum_slot_coarse_repairedStoppingCell_of_seminorm`
consumed by `exists_fluxRowSlots_repairedStoppingCell_enlargedLocalFluxPrice`. -/
theorem wholeSpaceSolution_fluxRowSlots_datum_slot_coarse_ninefoldCell_of_seminorm
    {a f : Vec d → ℝ} {alpha t R sigma Fac C Mn K Sem : ℝ} {n : ℤ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hf : Integrable (fun x ↦ f x ^ 2) volume)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsource q →
        ∫ x in translatedCube d (refinedStoppingScale q)
            (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
          repairedStoppingContractionFactor d *
            ∫ x in translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume)
    (hf0 : ∀ q, 0 < stoppingGraphDistance repairedStoppingGraph source hsource q →
      ∀ x ∈ translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q), f x = 0)
    (q : RefinedStoppingCell failure omega base)
    (hSem : 0 ≤ Sem) (hsem : Sem ≤ Fac * (C * Mn)) (hK : 0 ≤ K)
    (hMn : Mn ^ 2 ≤ K *
      ((∫ x in translatedCube d (refinedStoppingScale q + 2)
          (refinedStoppingCenter q), f x ^ 2 ∂volume) +
        ∫ x in translatedCube d (refinedStoppingScale q + 2)
          (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume))
    (hbudget :
      ((repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q *
          (Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) * (Fac * C)) ^ 2 * K) *
          fluxRowSlotsNinefoldForcingConstant d ≤
        alpha * t⁻¹ * Real.rpow R (2 * sigma) *
          (((3 : ℝ) ^ refinedStoppingScale q) / R) ^ (d + 6)) :
    (repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q *
        (Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) * Sem) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma (∫ x, f x ^ 2 ∂volume)
        (repairedStoppingPointwiseContractionFactor d ^ 2)
        ((3 : ℝ) ^ refinedStoppingScale q)
        (stoppingGraphDistance repairedStoppingGraph source hsource q) d :=
  by
  refine wholeSpaceSolution_fluxRowSlots_datum_slot_coarse_ninefoldCell
    (D := fun _ ↦ Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) * Sem)
    (Ndatum := (repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q *
      (Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) * (Fac * C)) ^ 2 * K)
    u hf hL2 hinitial hrepair chi source hsource hcell hf0 ?_ q ?_ hbudget
  · exact mul_nonneg (mul_nonneg
      ((repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume_pos q).le
      (sq_nonneg _)) hK
  · exact fluxRowSlots_repairedCell_hdatum_of_seminorm
      ((repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume_pos q).le
      (Real.rpow_nonneg (by norm_num) _) hSem hsem hMn

end RepairedDatumSlot

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
