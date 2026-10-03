/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PositiveFractionalDatum

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The scale factor of the manuscript's datum -/

/-- The extended-real prefactor of the positive fractional estimate for the
manuscript's scaled datum `G(y) = α 3^{-m} F(y/3^m)`: the interpolation
constant, the fractional scaling `3^{-ms}`, and the datum amplitude. -/
def fluxRowSlotsSourceDatumENormFactor (d : ℕ) (s : FractionalOrder) (alpha : ℝ)
    (m : ℤ) : ℝ≥0∞ :=
  scaledVectorDatumFractionalConstant s d *
    (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
      ‖alpha * (centeredCubeScale m)⁻¹‖ₑ

theorem fluxRowSlotsSourceDatumENormFactor_lt_top (d : ℕ) (s : FractionalOrder)
    (alpha : ℝ) (m : ℤ) :
    fluxRowSlotsSourceDatumENormFactor d s alpha m < ∞ := by
  unfold fluxRowSlotsSourceDatumENormFactor
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top
    (scaledVectorDatumFractionalConstant_lt_top s d) ?_) enorm_lt_top
  rw [ENNReal.ofReal_rpow_of_pos (centeredCubeScale_pos m)]
  exact ENNReal.ofReal_lt_top

/-- The real prefactor. -/
def fluxRowSlotsSourceDatumFactor (d : ℕ) (s : FractionalOrder) (alpha : ℝ)
    (m : ℤ) : ℝ :=
  (fluxRowSlotsSourceDatumENormFactor d s alpha m).toReal

theorem fluxRowSlotsSourceDatumFactor_nonneg (d : ℕ) (s : FractionalOrder)
    (alpha : ℝ) (m : ℤ) : 0 ≤ fluxRowSlotsSourceDatumFactor d s alpha m :=
  ENNReal.toReal_nonneg

/-! ## 2. The datum at the source, in real form -/

/-- **The manuscript's datum `g = -∇ψ`, with its fractional seminorm on the
cell.**

For every `L²` forcing `f` on the unit cube there is a vector field `F` with
`-div F = f` weakly and zero boundary data (the Poisson solve of `:11751-11753`,
recentred and rescaled to the unit cube), whose scaled dilation to `□_m` — the
manuscript's datum — has

```
[G]_{H^s(□_m)} ≤ fluxRowSlotsSourceDatumFactor d s α m · (C · ‖f‖_{L²(□_0)})
```

with `C` a dimension-only constant coming from the cube Dirichlet `H²`
endpoint.  This is the analytic input `hdatum` of
`fluxRowSlots_datum_slot_of_inputs`, in real form. -/
theorem exists_fluxRowSlots_source_datum_seminorm_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : Vec d → ℝ)
        (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))))
        (alpha : ℝ) (m : ℤ) (s : FractionalOrder),
        ∃ F : CubeVectorH1Function (originCube d 0),
          (∀ phi : H10Function (openCubeSet (originCube d 0)),
            ∫ x in openCubeSet (originCube d 0),
                f x * phi.toH1Function.toFun x ∂volume =
              -∫ x in openCubeSet (originCube d 0),
                vecDot (F.toField x) (phi.toH1Function.grad x) ∂volume) ∧
          (paperFractionalSeminorm (originCube d m) s FiniteLpExponent.two
              (centeredCubeScaledVectorDilation alpha m F).toField).toReal ≤
            fluxRowSlotsSourceDatumFactor d s alpha m * (C * ‖toScalarL2 hf‖) := by
  obtain ⟨C, hC, hlift⟩ :=
    exists_divergenceLift_paperFractionalSeminorm_scaled_le d
  refine ⟨C, hC, ?_⟩
  intro f hf alpha m s
  obtain ⟨F, hpair, hbound⟩ := hlift f hf alpha m s
  refine ⟨F, hpair, ?_⟩
  have hy : 0 ≤ C * ‖toScalarL2 hf‖ := mul_nonneg hC (norm_nonneg _)
  have hRHS :
      fluxRowSlotsSourceDatumENormFactor d s alpha m *
          ENNReal.ofReal (C * ‖toScalarL2 hf‖) ≠ ∞ := by
    refine (ENNReal.mul_lt_top (fluxRowSlotsSourceDatumENormFactor_lt_top d s
      alpha m) ENNReal.ofReal_lt_top).ne
  have hmono := ENNReal.toReal_mono hRHS hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hy] at hmono
  exact hmono

/-! ## 3. The datum slot at the source -/

/-- The bookkeeping step from the seminorm bound to the `hdatum` shape
`V · D² ≤ N · mass` of `fluxRowSlots_datum_slot_of_inputs`. -/
theorem fluxRowSlots_source_hdatum
    {V pref Sem Fac C Mn : ℝ} (hV : 0 ≤ V) (hpref : 0 ≤ pref)
    (hSem : 0 ≤ Sem) (hsem : Sem ≤ Fac * (C * Mn)) :
    V * (pref * Sem) ^ 2 ≤ (V * (pref * (Fac * C)) ^ 2) * Mn ^ 2 := by
  have hsq : (pref * Sem) ^ 2 ≤ (pref * (Fac * (C * Mn))) ^ 2 := by
    have h1 : pref * Sem ≤ pref * (Fac * (C * Mn)) :=
      mul_le_mul_of_nonneg_left hsem hpref
    have h0 : 0 ≤ pref * Sem := mul_nonneg hpref hSem
    nlinarith [h1, h0]
  calc V * (pref * Sem) ^ 2 ≤ V * (pref * (Fac * (C * Mn))) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hV
    _ = (V * (pref * (Fac * C)) ^ 2) * Mn ^ 2 := by ring

/-- **The datum slot of the local flux price, on a source cell.**

Everything is explicit: `N` is the constant produced by the Poisson solve and
the fractional scaling, and `mass` is the `L²` mass of the unit-cube forcing,
which the price's `hmass` leg then trades for `θ^{dist/2} ‖f‖₂²`. -/
theorem fluxRowSlots_datum_slot_at_source
    {alpha t R sigma fEnergy theta cellSize V pref Sem Fac C Mn mass : ℝ}
    {graphDistance : ℕ}
    (hV : 0 ≤ V) (hpref : 0 ≤ pref) (hSem : 0 ≤ Sem)
    (hfEnergy : 0 ≤ fEnergy) (htheta : 0 ≤ theta)
    (hsem : Sem ≤ Fac * (C * Mn))
    (hmass : Mn ^ 2 ≤ mass)
    (hmassdecay : mass ≤ Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy)
    (hbudget : V * (pref * (Fac * C)) ^ 2 ≤
      alpha * t⁻¹ * Real.rpow R (2 * sigma) * (cellSize / R) ^ (d + 6)) :
    V * (pref * Sem) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
        graphDistance d := by
  refine fluxRowSlots_datum_slot_of_inputs (N := V * (pref * (Fac * C)) ^ 2)
    (mass := mass) ?_ hfEnergy htheta ?_ hmassdecay hbudget
  · positivity
  · refine (fluxRowSlots_source_hdatum hV hpref hSem hsem).trans ?_
    exact mul_le_mul_of_nonneg_left hmass (by positivity)

/-- **The composite for the manuscript's `ψ`.**

The seminorm leg is supplied by `exists_fluxRowSlots_source_datum_seminorm_le`;
what remains at the source is only the two legs the *whole-space* row owes
anyway — the decay of the unit-cube forcing mass and the constant budget. -/
theorem exists_fluxRowSlots_datum_slot_at_source (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : Vec d → ℝ)
        (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))))
        (alpha0 : ℝ) (m : ℤ) (s : FractionalOrder),
        ∃ F : CubeVectorH1Function (originCube d 0),
          (∀ phi : H10Function (openCubeSet (originCube d 0)),
            ∫ x in openCubeSet (originCube d 0),
                f x * phi.toH1Function.toFun x ∂volume =
              -∫ x in openCubeSet (originCube d 0),
                vecDot (F.toField x) (phi.toH1Function.grad x) ∂volume) ∧
          ∀ (alpha t R sigma fEnergy theta cellSize V pref mass : ℝ)
            (graphDistance : ℕ),
            0 ≤ V → 0 ≤ pref → 0 ≤ fEnergy → 0 ≤ theta →
            ‖toScalarL2 hf‖ ^ 2 ≤ mass →
            mass ≤ Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy →
            V * (pref * (fluxRowSlotsSourceDatumFactor d s alpha0 m * C)) ^ 2 ≤
              alpha * t⁻¹ * Real.rpow R (2 * sigma) * (cellSize / R) ^ (d + 6) →
            V * (pref *
                (paperFractionalSeminorm (originCube d m) s FiniteLpExponent.two
                  (centeredCubeScaledVectorDilation alpha0 m F).toField).toReal) ^ 2 ≤
              fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
                graphDistance d := by
  obtain ⟨C, hC, hmain⟩ := exists_fluxRowSlots_source_datum_seminorm_le d
  refine ⟨C, hC, ?_⟩
  intro f hf alpha0 m s
  obtain ⟨F, hpair, hsem⟩ := hmain f hf alpha0 m s
  refine ⟨F, hpair, ?_⟩
  intro alpha t R sigma fEnergy theta cellSize V pref mass graphDistance
    hV hpref hfEnergy htheta hmass hmassdecay hbudget
  exact fluxRowSlots_datum_slot_at_source (d := d) hV hpref ENNReal.toReal_nonneg
    hfEnergy htheta hsem hmass hmassdecay hbudget

/-! ## 4. The frozen `D`-shape -/



theorem fluxRowSlots_datum_slot_at_source_frozenShape
    {sigma : ℝ} (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) {n m : ℤ}
    {alpha0 alpha t R fEnergy theta cellSize V Fac C Mn mass : ℝ}
    {graphDistance : ℕ} {F : CubeVectorH1Function (originCube d 0)}
    (hV : 0 ≤ V) (hfEnergy : 0 ≤ fEnergy) (htheta : 0 ≤ theta)
    (hsem : (paperFractionalSeminorm (originCube d m)
        (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two
        (centeredCubeScaledVectorDilation alpha0 m F).toField).toReal ≤
      Fac * (C * Mn))
    (hmass : Mn ^ 2 ≤ mass)
    (hmassdecay : mass ≤ Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy)
    (hbudget : V * (Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) * (Fac * C)) ^ 2 ≤
      alpha * t⁻¹ * Real.rpow R (2 * sigma) * (cellSize / R) ^ (d + 6)) :
    V * (Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) *
        (paperFractionalSeminorm (originCube d m)
          (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two
          (centeredCubeScaledVectorDilation alpha0 m F).toField).toReal) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
        graphDistance d :=
  fluxRowSlots_datum_slot_at_source hV (Real.rpow_nonneg (by norm_num) _)
    ENNReal.toReal_nonneg hfEnergy htheta hsem hmass hmassdecay hbudget

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
