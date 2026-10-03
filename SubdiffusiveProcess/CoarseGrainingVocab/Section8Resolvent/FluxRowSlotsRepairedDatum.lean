/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsSourceDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsEnlargementMass

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The datum slot with the mass constant carried -/

/-- **`fluxRowSlots_datum_slot_of_inputs` with the mass constant.**

The repaired family's mass leg
(`wholeSpaceSolution_enlargement_mass_le_repairedStoppingDecay`) delivers the
graph decay with a dimension-only prefactor `Cm`.  As on the energy side, `Cm`
is paid in the *budget* — `N · Cm ≤ α t⁻¹ R^{2σ}(size/R)^{d+6}` — never in the
source energy, which stays the frozen `‖f‖₂²`. -/
theorem fluxRowSlots_datum_slot_of_inputs_const
    {alpha t R sigma fEnergy theta cellSize D N Cm mass V : ℝ}
    {graphDistance : ℕ}
    (hN : 0 ≤ N) (hCm : 0 ≤ Cm) (hfEnergy : 0 ≤ fEnergy) (htheta : 0 ≤ theta)
    (hdatum : V * D ^ 2 ≤ N * mass)
    (hmass : mass ≤ Cm * (Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy))
    (hbudget : N * Cm ≤ alpha * t⁻¹ * Real.rpow R (2 * sigma) *
      (cellSize / R) ^ (d + 6)) :
    V * D ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
        graphDistance d := by
  refine fluxRowSlots_datum_slot_of_inputs (N := N * Cm)
    (mass := Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy)
    (mul_nonneg hN hCm) hfEnergy htheta ?_ le_rfl hbudget
  calc V * D ^ 2 ≤ N * mass := hdatum
    _ ≤ N * (Cm * (Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy)) :=
        mul_le_mul_of_nonneg_left hmass hN
    _ = N * Cm * (Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy) := by ring

/-! ## 2. The forcing mass on the enlargement, `f` and `u` together -/

section MassLeg

variable [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- **The uniform mass leg of the datum slot.**

The manuscript's datum on `Q̂ = z_q + □_{m_q+1}` is `-∇ψ` with
`-Δψ = t⁻¹(f - u)`, so its forcing mass is `∫_{Q̂} f² + ∫_{Q̂} u²`.  This
quantity obeys the repaired family's graph decay uniformly in `q`:

* at positive graph distance the `f`-leg vanishes (`hf0`) and the `u`-leg is
  `wholeSpaceSolution_enlargement_mass_le_repairedStoppingDecay`;
* at the source the decay factor is `θ^0 = 1` and the `f`-leg is bounded by the
  global `‖f‖₂²`.

The single constant `1 + fluxRowSlotsEnlargementConstant d` covers both. -/
theorem wholeSpaceSolution_enlargement_forcing_mass_le_repairedStoppingDecay
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
    (∫ x in translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q), f x ^ 2 ∂volume) +
      (∫ x in translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume) ≤
      (1 + fluxRowSlotsEnlargementConstant d) *
        (Real.rpow (repairedStoppingPointwiseContractionFactor d ^ 2)
            ((stoppingGraphDistance repairedStoppingGraph source hsource q : ℝ)
              / 2) *
          ∫ x, f x ^ 2 ∂volume) := by
  classical
  set gd : ℕ := stoppingGraphDistance repairedStoppingGraph source hsource q
    with hgd
  set fEnergy : ℝ := ∫ x, f x ^ 2 ∂volume with hfE
  have hfEnonneg : 0 ≤ fEnergy := integral_nonneg fun x ↦ sq_nonneg (f x)
  have hthetapow : 0 ≤ Real.rpow (repairedStoppingPointwiseContractionFactor d ^ 2)
      ((gd : ℝ) / 2) := Real.rpow_nonneg (sq_nonneg _) _
  have hdecay := wholeSpaceSolution_enlargement_mass_le_repairedStoppingDecay
    u hL2 hinitial hrepair source hsource hcell q
  rw [← hgd, ← hfE, mul_assoc] at hdecay
  rcases Nat.eq_zero_or_pos gd with hz | hpos
  · -- at the source: the decay factor is `1` and the `f`-leg is global
    have hfleg : (∫ x in translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q), f x ^ 2 ∂volume) ≤ fEnergy := by
      refine setIntegral_le_integral hf ?_
      exact Filter.Eventually.of_forall fun x ↦ sq_nonneg (f x)
    have hone : Real.rpow (repairedStoppingPointwiseContractionFactor d ^ 2)
        ((gd : ℝ) / 2) = 1 := by
      rw [hz]
      norm_num
    rw [hone, one_mul]
    have := add_le_add hfleg hdecay
    rw [hone, one_mul] at this
    refine this.trans ?_
    nlinarith [hfEnonneg, fluxRowSlotsEnlargementConstant_pos (d := d)]
  · -- away from the source: the `f`-leg vanishes
    have hfzero : (∫ x in translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q), f x ^ 2 ∂volume) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero ?_
      intro x hx
      rw [hf0 q hpos x hx]
      ring
    rw [hfzero, zero_add]
    refine hdecay.trans ?_
    have hprod : 0 ≤ Real.rpow (repairedStoppingPointwiseContractionFactor d ^ 2)
        ((gd : ℝ) / 2) * fEnergy := mul_nonneg hthetapow hfEnonneg
    nlinarith [hprod, fluxRowSlotsEnlargementConstant_pos (d := d)]

end MassLeg

/-! ## 3. The datum antecedent on a refined stopping cell -/

section RepairedDatumSlot

variable [NeZero d] {base : ℤ}
  {failure : TriadicCube d → Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)}
  {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}

/-- **The `D²` datum slot on a refined stopping cell, end to end.**

The companion of
`wholeSpaceSolution_fluxRowSlots_energy_slot_coarse_repairedStoppingCell`
(`FluxRowSlotsRepairedCell.lean`): same cell, same normalization, same decay
factor and graph distance, and the left side is the repaired partition's own
`cellVolume q`.  This is literally the second antecedent of
`exists_fluxRowRiesz_repairedStoppingCell_localFluxPrice`.

Everything stochastic and geometric is discharged here.  The one remaining leg
is `hdatum`, the elliptic regularity of the manuscript's `ψ` on the cell,
expressed against the forcing mass `∫_{Q̂} f² + ∫_{Q̂} u²` of `-Δψ = t⁻¹(f-u)`;
`hbudget` is the deterministic constant budget, in the same form as the energy
slot's, with `Cm := 1 + fluxRowSlotsEnlargementConstant d`. -/
theorem wholeSpaceSolution_fluxRowSlots_datum_slot_coarse_repairedStoppingCell
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
          ((∫ x in translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q), f x ^ 2 ∂volume) +
            ∫ x in translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume))
    (hbudget : Ndatum * (1 + fluxRowSlotsEnlargementConstant d) ≤
      alpha * t⁻¹ * Real.rpow R (2 * sigma) *
        (((3 : ℝ) ^ refinedStoppingScale q) / R) ^ (d + 6)) :
    (repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q *
        D q ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma (∫ x, f x ^ 2 ∂volume)
        (repairedStoppingPointwiseContractionFactor d ^ 2)
        ((3 : ℝ) ^ refinedStoppingScale q)
        (stoppingGraphDistance repairedStoppingGraph source hsource q) d :=
  fluxRowSlots_datum_slot_of_inputs_const (d := d) hN
    (by linarith [fluxRowSlotsEnlargementConstant_pos (d := d)])
    (integral_nonneg fun x ↦ sq_nonneg (f x)) (sq_nonneg _) hdatum
    (wholeSpaceSolution_enlargement_forcing_mass_le_repairedStoppingDecay u hf
      hL2 hinitial hrepair source hsource hcell hf0 q)
    hbudget

/-! ## 4. The frozen `D`-shape -/



theorem fluxRowSlots_repairedCell_hdatum_of_seminorm
    {V pref Sem Fac C Mn K mass : ℝ} (hV : 0 ≤ V) (hpref : 0 ≤ pref)
    (hSem : 0 ≤ Sem) (hsem : Sem ≤ Fac * (C * Mn)) (hMn : Mn ^ 2 ≤ K * mass) :
    V * (pref * Sem) ^ 2 ≤ (V * (pref * (Fac * C)) ^ 2 * K) * mass := by
  refine (fluxRowSlots_source_hdatum hV hpref hSem hsem).trans ?_
  calc (V * (pref * (Fac * C)) ^ 2) * Mn ^ 2
      ≤ (V * (pref * (Fac * C)) ^ 2) * (K * mass) :=
        mul_le_mul_of_nonneg_left hMn (by positivity)
    _ = (V * (pref * (Fac * C)) ^ 2 * K) * mass := by ring

/-- **The datum antecedent in the literal shape of the frozen price.**

`exists_fluxRowRiesz_repairedStoppingCell_localFluxPrice` abbreviates

```
D = 3^{((1+σ)/2)·n} · ([g₀]_{H^{(1+σ)/2}(□_{m_q})}).toReal ,
```

and this is §3 with that `D`, with the elliptic-regularity leg supplied in its
natural unsquared form: the cell seminorm is `Fac · C` times the `L²` size `Mn`
of the forcing of `-Δψ = t⁻¹(f-u)` on the enlargement (`Fac` the fractional
scaling factor `fluxRowSlotsSourceDatumFactor`, `C` the cube Dirichlet `H²`
constant of `exists_fluxRowSlots_source_datum_seminorm_le`). -/
theorem wholeSpaceSolution_fluxRowSlots_datum_slot_coarse_repairedStoppingCell_of_seminorm
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
      ((∫ x in translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q), f x ^ 2 ∂volume) +
        ∫ x in translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume))
    (hbudget :
      ((repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q *
          (Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) * (Fac * C)) ^ 2 * K) *
          (1 + fluxRowSlotsEnlargementConstant d) ≤
        alpha * t⁻¹ * Real.rpow R (2 * sigma) *
          (((3 : ℝ) ^ refinedStoppingScale q) / R) ^ (d + 6)) :
    (repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q *
        (Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) * Sem) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma (∫ x, f x ^ 2 ∂volume)
        (repairedStoppingPointwiseContractionFactor d ^ 2)
        ((3 : ℝ) ^ refinedStoppingScale q)
        (stoppingGraphDistance repairedStoppingGraph source hsource q) d :=
  by
  refine wholeSpaceSolution_fluxRowSlots_datum_slot_coarse_repairedStoppingCell
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
