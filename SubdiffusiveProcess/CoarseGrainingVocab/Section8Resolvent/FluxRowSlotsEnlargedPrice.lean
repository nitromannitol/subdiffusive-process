/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszEnlargedCellPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsNinefoldDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsEnlargedBudget
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsRepairedCell
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsWholeSpaceCell
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsRecentring

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization Homogenization.Book Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.Frozen.Section8
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The partition's cell volume is the enlargement cube's volume -/

/-- `|Q̂| = 3^{d(m+1)}` is literally `cubeVolume (originCube d (m + 1))`, the
normalization of `localSymmetricEnergyENorm` **on the enlargement**.  Unlike the
scale-`m` reading (`repairedFluxRowRieszPartition_cellVolume_eq`), no factor
`3 ^ d` is paid. -/
theorem cubeVolume_originCube_succ (m : ℤ) :
    cubeVolume (originCube d (m + 1)) =
      (3 : ℝ) ^ d * cubeVolume (originCube d m) := by
  rw [cubeVolume, cubeVolume, cubeScaleFactor_originCube,
    cubeScaleFactor_originCube, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), mul_pow]
  norm_num
  ring

theorem repairedFluxRowRieszPartition_cellVolume_eq_cubeVolume_succ [NeZero d]
    {base : ℤ} {failure : TriadicCube d → Set (PotentialSample d)}
    {omega : PotentialSample d}
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base)
    (q : RefinedStoppingCell failure omega base) :
    (repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q =
      cubeVolume (originCube d (refinedStoppingScale q + 1)) := by
  rw [repairedFluxRowRieszPartition_cellVolume_eq, cubeVolume_originCube_succ]

section Chain

variable [NeZero d] {base : ℤ}
  {failure : TriadicCube d → Set (PotentialSample d)}
  {omega : PotentialSample d}

/-! ## 2. The energy slot on the enlargement -/

/-- **The flux energy slot on the analytic enlargement `Q̂`, in the corrected
normalization.**

The left side carries the extra deterministic weight
`fluxRowRieszEnlargedNqWeight d m σ` which converts the repo's scale-normalized
local negative norm on `Q̂` into the physical dual coefficient
`Nq = √(2|Q̂|)·‖·‖_{H^{-σ}(Q̂)}` of the corrected cutoff pairing
(`FluxRowRieszEnlargedCellPrice.lean`).  The right side is unchanged: the
physical scale at the family's cell size `3 ^ refinedStoppingScale q`.  The
whole conversion is therefore paid inside this slot's budget. -/
theorem wholeSpaceSolution_fluxRowSlots_energy_slot_coarse_enlargedCell
    {a f : Vec d → ℝ} {alpha t eta Cm R sigma lambdaInv mass : ℝ} {n : ℤ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty)
    (halpha : 0 < alpha) (ht : 0 < t) (hR : 0 < R) (hRbase : R ≤ (3 : ℝ) ^ base)
    (heta : 0 ≤ eta) (hCm : 0 ≤ Cm) (haNonneg : ∀ x, 0 ≤ a x)
    (q : RefinedStoppingCell failure omega base)
    (hcacc : (∫ x in translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q), a x * vecNormSq (u.grad x) ∂volume) ≤
      eta * t⁻¹ * mass)
    (hmass : mass ≤ Cm *
      (Real.rpow (repairedStoppingPointwiseContractionFactor d ^ 2)
          ((stoppingGraphDistance repairedStoppingGraph source hsource q : ℝ)
            / 2) *
        ∫ x, f x ^ 2 ∂volume))
    (hn : n ≤ refinedStoppingScale q + 1)
    (acoeff : Ch02.CoeffOn
      (Ch02.cubeDomain (originCube d (refinedStoppingScale q + 1))))
    (ha : ∀ y, acoeff.toCoeffField y =
      scalarCoeffField (fun x ↦ a (x + refinedStoppingCenter q)) y)
    (u0 : H1Function (openCubeSet (originCube d (refinedStoppingScale q + 1))))
    (hu0 : u0.grad =ᵐ[volume.restrict
        (openCubeSet (originCube d (refinedStoppingScale q + 1)))]
      fun x ↦ u.grad (x + refinedStoppingCenter q))
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1)
    (Kcut : ℝ) (hKcut : 0 ≤ Kcut)
    (hbudget : Section6Dirichlet.dirichletWeightedEnergyFactor (3 * sigma / 4)
        sigma ^ 2 *
        (fluxRowRieszEnlargedNqRatio (refinedStoppingScale q) sigma * Kcut *
          (Cm * eta)) ≤ Real.rpow R (2 * sigma) *
        (((3 : ℝ) ^ refinedStoppingScale q) / R) ^ (d + 6)) :
    fluxRowRieszEnlargedNqWeight d (refinedStoppingScale q) sigma * Kcut *
        (Real.sqrt alpha *
          (weightedLocalSymmetricEnergyLp
            (originCube d (refinedStoppingScale q + 1)) n hn
            acoeff u0 (fluxRowLocalLowerOrder sigma hsigma)
            (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two).toReal) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma (∫ x, f x ^ 2 ∂volume)
          (repairedStoppingPointwiseContractionFactor d ^ 2)
          ((3 : ℝ) ^ refinedStoppingScale q)
          (stoppingGraphDistance repairedStoppingGraph source hsource q) d *
        (1 + (alpha * lambdaInv) ^ 2) := by
  set Wq := fluxRowRieszEnlargedNqRatio (refinedStoppingScale q) sigma * Kcut
    with hWq
  have hWqnn : 0 ≤ Wq :=
    mul_nonneg (fluxRowRieszEnlargedNqRatio_nonneg _ _) hKcut
  have hidentity : cubeVolume (originCube d (refinedStoppingScale q + 1)) *
      (localSymmetricEnergyENorm (originCube d (refinedStoppingScale q + 1))
        acoeff u0).toReal ^ 2 =
      ∫ x in translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q), a x * vecNormSq (u.grad x) ∂volume :=
    cubeVolume_mul_recentred_localSymmetricEnergy_sq_eq
      (refinedStoppingCenter q) acoeff ha haNonneg u0 u.grad hu0
  have hthetann : (0 : ℝ) ≤ repairedStoppingPointwiseContractionFactor d ^ 2 :=
    sq_nonneg _
  have hfEnergy : (0 : ℝ) ≤ ∫ x, f x ^ 2 ∂volume :=
    integral_nonneg fun x ↦ sq_nonneg (f x)
  -- the Caccioppoli in the weighted normalization
  have hcacc' : cubeVolume (originCube d (refinedStoppingScale q + 1)) * Wq *
      (localSymmetricEnergyENorm (originCube d (refinedStoppingScale q + 1))
        acoeff u0).toReal ^ 2 ≤
      (Wq * Cm * eta * t⁻¹) *
        (Real.rpow (repairedStoppingPointwiseContractionFactor d ^ 2)
            ((stoppingGraphDistance repairedStoppingGraph source hsource q : ℝ)
              / 2) *
          ∫ x, f x ^ 2 ∂volume) := by
    have hstep : Wq * (cubeVolume (originCube d (refinedStoppingScale q + 1)) *
        (localSymmetricEnergyENorm
          (originCube d (refinedStoppingScale q + 1)) acoeff u0).toReal ^ 2) ≤
        Wq * (eta * t⁻¹ * mass) := by
      rw [hidentity]
      exact mul_le_mul_of_nonneg_left hcacc hWqnn
    have hnn : (0 : ℝ) ≤ Wq * (eta * t⁻¹) :=
      mul_nonneg hWqnn (mul_nonneg heta (inv_pos.mpr ht).le)
    have hstep2 : Wq * (eta * t⁻¹ * mass) ≤
        (Wq * Cm * eta * t⁻¹) *
          (Real.rpow (repairedStoppingPointwiseContractionFactor d ^ 2)
              ((stoppingGraphDistance repairedStoppingGraph source hsource q : ℝ)
                / 2) *
            ∫ x, f x ^ 2 ∂volume) := by
      have := mul_le_mul_of_nonneg_left hmass hnn
      nlinarith [this]
    calc cubeVolume (originCube d (refinedStoppingScale q + 1)) * Wq *
          (localSymmetricEnergyENorm
            (originCube d (refinedStoppingScale q + 1)) acoeff u0).toReal ^ 2
        = Wq * (cubeVolume (originCube d (refinedStoppingScale q + 1)) *
            (localSymmetricEnergyENorm
              (originCube d (refinedStoppingScale q + 1))
              acoeff u0).toReal ^ 2) := by ring
      _ ≤ Wq * (eta * t⁻¹ * mass) := hstep
      _ ≤ _ := hstep2
  -- the budget, with the conversion weight paid
  have hsmall : Section6Dirichlet.dirichletWeightedEnergyFactor (3 * sigma / 4)
        sigma ^ 2 * (Wq * Cm * eta * t⁻¹) ≤ t⁻¹ * Real.rpow R (2 * sigma) *
          (((3 : ℝ) ^ refinedStoppingScale q) / R) ^ (d + 6) := by
    have htinv : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht
    have := mul_le_mul_of_nonneg_right hbudget htinv.le
    nlinarith [this]
  have hbud := fluxRowSlots_energy_budget_of_smallness_ratio (d := d)
    (lambdaInv := lambdaInv) (cellSize := (3 : ℝ) ^ refinedStoppingScale q)
    halpha ht hR
    (le_three_pow_refinedStoppingScale_of_le_three_pow_base hRbase q) hsmall
  have hV : fluxRowRieszEnlargedNqWeight d (refinedStoppingScale q) sigma * Kcut =
      cubeVolume (originCube d (refinedStoppingScale q + 1)) * Wq := by
    rw [hWq, fluxRowRieszEnlargedNqWeight]; ring
  rw [hV]
  exact fluxRowSlots_energy_slot_of_inputs (d := d) halpha
    (mul_nonneg (cubeVolume_nonneg _) hWqnn) ENNReal.toReal_nonneg
    (by positivity) hfEnergy hthetann
    (fluxRowSlots_weightedEnergy_toReal_le hn acoeff u0 hsigma) hcacc' le_rfl
    hbud

/-! ## 3. The enlarged local flux price, both slots discharged -/

/-- **The local flux price on the analytic enlargement of a refined stopping
cell, in the coefficient the corrected cutoff pairing consumes.**

The left side is

```text
|Q| * (sqrt (2 * cubeVolume Q̂) *
        (paperNegativeFractionalDual Q̂ (fluxRowLocalOrder σ hσ) 2 F).toReal) ^ 2
```

with `Q̂ = originCube d (refinedStoppingScale q + 1)` and `F` the recentred
root-flux defect on `Q̂`.  That is exactly
`P.cellVolume q * fluxRowAssemblyEnlargedNq (P.scale q) σ hσ (rootFlux q) ^ 2`,
the left side of
`FluxRowAssemblyEnlargedLocalPrice.cellVolume_mul_enlargedNq_sq_le`
(`FluxRowAssemblyEnlargedLocalPrice.lean`), with the definition unfolded — the
physical dual coefficient of `fluxRowDual_abs_re_enlargedCube_integral_le`, not
the repo's scale-normalized `fluxRowRieszLocalNegative`, which P-261/P-264
showed is off by the cell volume.

The right side is the manuscript's cell price, unchanged: the family's own cell
size `3 ^ refinedStoppingScale q`, repaired graph distance, and pointwise
contraction factor, so the shell summation and the coefficient budget consume it
verbatim.

Compared with the retired scale-`m` chain: the local representative `ucell`,
its force `g`, its recentring `u0` and the homogenization errors are all on
`Q̂`; the Caccioppoli `hcacc` is on `Q̂` against a free mass functional whose
decay is `hmassdecay`; and both slot budgets carry the deterministic conversion
weight `fluxRowRieszEnlargedNqWeight d (refinedStoppingScale q) σ =
2 |Q̂| · 3 ^ (2 σ (m+1))`, which is where the whole re-normalization is paid. -/
theorem exists_fluxRowSlots_repairedStoppingCell_enlargedLocalFluxPrice
    (hd : 2 ≤ d) :
    ∃ Ccoarse : ℝ, 0 < Ccoarse ∧
      ∀ (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
          cubeSet (triadicStoppingCandidate failure omega Q))
        (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
          cubeSet Q.1)
        (chi : RepairedStoppingCutoff failure omega base)
        (source : Finset (RefinedStoppingCell failure omega base))
        (hsource : source.Nonempty)
        (M : GMCModel d) (L : ℕ) {t : ℝ} {f : Vec d → ℝ}
        (u : WholeSpaceDivergenceResolventSolution (aCutoff M L omega) t f),
      (∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume) →
      Integrable (fun x ↦ f x ^ 2) volume →
      (∀ q, 0 < stoppingGraphDistance repairedStoppingGraph source hsource q →
        ∫ x in translatedCube d (refinedStoppingScale q)
            (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
          repairedStoppingContractionFactor d *
            ∫ x in translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume) →
      (∀ q, 0 < stoppingGraphDistance repairedStoppingGraph source hsource q →
        ∀ x ∈ translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q), f x = 0) →
      ∀ {alpha eta Cm R sigma : ℝ}, 0 < alpha → 0 < t → 0 < R →
        R ≤ (3 : ℝ) ^ base → 0 ≤ eta → 0 ≤ Cm →
      ∀ hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1,
      ∀ (q : RefinedStoppingCell failure omega base) (n : ℤ)
        (hnm : n < refinedStoppingScale q + 1) (Kcut : ℝ), 0 ≤ Kcut →
      (Section6Dirichlet.dirichletWeightedEnergyFactor (3 * sigma / 4) sigma ^ 2 *
        (fluxRowRieszEnlargedNqRatio (refinedStoppingScale q) sigma * Kcut *
          (Cm * eta)) ≤ Real.rpow R (2 * sigma) *
        (((3 : ℝ) ^ refinedStoppingScale q) / R) ^ (d + 6)) →
      ∀ (g : Vec d → Vec d)
        (ucell : H1Function (translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q))),
      MemCubeEuclideanFullWsp (originCube d (refinedStoppingScale q + 1))
          (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two
          (fun x ↦ g (x + refinedStoppingCenter q)) →
      IsDivFormWeakSolutionOn (aCutoff M L omega)
          (translatedCube d (refinedStoppingScale q + 1)
            (refinedStoppingCenter q)) ucell g →
      (ucell.grad =ᵐ[volume.restrict (translatedCube d
        (refinedStoppingScale q + 1) (refinedStoppingCenter q))] u.grad) →
      ∀ {mass : ℝ},
      ((∫ x in translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q),
            aCutoff M L omega x * vecNormSq (u.grad x) ∂volume) ≤
        eta * t⁻¹ * mass) →
      (mass ≤ Cm *
        (Real.rpow (repairedStoppingPointwiseContractionFactor d ^ 2)
            ((stoppingGraphDistance repairedStoppingGraph source hsource q : ℝ)
              / 2) *
          ∫ x, f x ^ 2 ∂volume)) →
      ∀ {Fac Cdat Mn K : ℝ}, 0 ≤ K →
      ((paperFractionalSeminorm (originCube d (refinedStoppingScale q + 1))
          (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two
          (fun x ↦ g (x + refinedStoppingCenter q))).toReal ≤
        Fac * (Cdat * Mn)) →
      (Mn ^ 2 ≤ K *
        ((∫ x in translatedCube d (refinedStoppingScale q + 2)
            (refinedStoppingCenter q), f x ^ 2 ∂volume) +
          ∫ x in translatedCube d (refinedStoppingScale q + 2)
            (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume)) →
      (((repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q *
            (fluxRowRieszEnlargedNqRatio (refinedStoppingScale q) sigma * Kcut) *
            (Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) * (Fac * Cdat)) ^ 2 * K) *
          fluxRowSlotsNinefoldForcingConstant d ≤
        alpha * t⁻¹ * Real.rpow R (2 * sigma) *
          (((3 : ℝ) ^ refinedStoppingScale q) / R) ^ (d + 6)) →
      ∃ (g0 : CubeEuclideanWspField (originCube d (refinedStoppingScale q + 1))
            (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two)
        (u0 v0 : H1Function
          (openCubeSet (originCube d (refinedStoppingScale q + 1)))),
        g0.toField = (fun x ↦ g (x + refinedStoppingCenter q)) ∧
        u0 = fluxRowRieszUntranslatedH1 (refinedStoppingCenter q) ucell ∧
        let afam := aCutoffFamily M L
          (translatePotentialSample (refinedStoppingCenter q) omega)
        ∀ lambdaInv : ℝ,
          paperHomogenizationError (originCube d (refinedStoppingScale q + 1)) n
            (3 * sigma / 4) .infinity (.finite 1) afam alpha ≠ ∞ →
          paperHomogenizationError (originCube d (refinedStoppingScale q + 1)) n
            ((3 * sigma / 4) / 2) .infinity (.finite 2) afam alpha ≠ ∞ →
          weightedLocalSymmetricEnergyLp
            (originCube d (refinedStoppingScale q + 1)) n
            (by simpa [originCube] using hnm.le)
            (afam.coeffOn (originCube d (refinedStoppingScale q + 1))) u0
            (fluxRowLocalLowerOrder sigma hsigma)
            (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two ≠ ∞ →
          paperFractionalSeminorm (originCube d (refinedStoppingScale q + 1))
            (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two
            g0.toField ≠ ∞ →
          Kcut *
              (Real.sqrt
                  (2 * cubeVolume (originCube d (refinedStoppingScale q + 1))) *
                (paperNegativeFractionalDual
                    (originCube d (refinedStoppingScale q + 1))
                    (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two
                    (centeredCubeRootFluxDefectL2Field
                      (refinedStoppingScale q + 1)
                      (afam.coeffOn
                        (originCube d (refinedStoppingScale q + 1)))
                      alpha u0)).toReal) ^ 2 ≤
            fluxRowRieszCellPrice
              (fluxRowRieszCoarsePriceConstant
                (fluxRowRieszCoarseFirstFactor Ccoarse sigma)
                (fluxRowRieszCoarseSecondFactor Ccoarse sigma))
              alpha t R sigma (∫ x, f x ^ 2 ∂volume)
              (repairedStoppingPointwiseContractionFactor d ^ 2)
              ((3 : ℝ) ^ refinedStoppingScale q)
              (stoppingGraphDistance repairedStoppingGraph source hsource q) d
              (paperHomogenizationError
                (originCube d (refinedStoppingScale q + 1))
                n (3 * sigma / 4) .infinity (.finite 1) afam alpha).toReal
              (paperHomogenizationError
                (originCube d (refinedStoppingScale q + 1))
                n ((3 * sigma / 4) / 2) .infinity (.finite 2) afam alpha).toReal
              lambdaInv := by
  obtain ⟨Ccoarse, hCcoarse, hprice⟩ :=
    exists_fluxRowRiesz_repairedStoppingCell_enlargedLocalFluxPrice d hd
  refine ⟨Ccoarse, hCcoarse, ?_⟩
  intro hinitial hrepair chi source hsource M L t f u hL2 hf hcell hf0
    alpha eta Cm R sigma halpha ht hR hRbase heta hCm hsigma q n hnm Kcut hKcut
    hbudget g ucell hg hu hgrad mass hcacc hmassdecay Fac Cdat Mn K hK hsem hMn
    hdbudget
  obtain ⟨g0, u0, v0, hg0, hu0eq, hforced, hscalar, htrace, hcoarse, hconvert⟩ :=
    hprice hinitial hrepair chi source hsource q M L n hnm alpha sigma halpha
      hsigma g ucell hg hu
  refine ⟨g0, u0, v0, hg0, hu0eq, ?_⟩
  intro afam lambdaInv hE1 hE2 hS hD
  have hRKnn : 0 ≤ fluxRowRieszEnlargedNqRatio (refinedStoppingScale q) sigma *
      Kcut :=
    mul_nonneg (fluxRowRieszEnlargedNqRatio_nonneg _ _) hKcut
  have hsqRK :
      Real.sqrt (fluxRowRieszEnlargedNqRatio (refinedStoppingScale q) sigma *
        Kcut) ^ 2 =
      fluxRowRieszEnlargedNqRatio (refinedStoppingScale q) sigma * Kcut :=
    Real.sq_sqrt hRKnn
  have hu0grad : u0.grad =ᵐ[volume.restrict
      (openCubeSet (originCube d (refinedStoppingScale q + 1)))]
      fun x ↦ u.grad (x + refinedStoppingCenter q) := by
    rw [hu0eq]
    exact wholeSpaceSolution_untranslatedCell_grad_ae_eq u ucell hgrad
  have henergy := wholeSpaceSolution_fluxRowSlots_energy_slot_coarse_enlargedCell
    (lambdaInv := lambdaInv) (n := n) u source hsource
    halpha ht hR hRbase heta hCm (fun x ↦ (aCutoff_pos M L omega x).le) q
    hcacc hmassdecay hnm.le
    ((aCutoffFamily M L
      (translatePotentialSample (refinedStoppingCenter q) omega)).coeffOn
        (originCube d (refinedStoppingScale q + 1)))
    (aCutoffFamily_translatePotentialSample_coeffOn_toCoeffField M L
      (refinedStoppingCenter q) omega
      (originCube d (refinedStoppingScale q + 1)))
    u0 hu0grad hsigma Kcut hKcut hbudget
  have hdatum0 :=
    wholeSpaceSolution_fluxRowSlots_datum_slot_coarse_ninefoldCell_of_seminorm
      (n := n)
      (Fac := Real.sqrt
        (fluxRowRieszEnlargedNqRatio (refinedStoppingScale q) sigma * Kcut) *
        Fac)
      (C := Cdat) (Mn := Mn) (K := K)
      (Sem := Real.sqrt
          (fluxRowRieszEnlargedNqRatio (refinedStoppingScale q) sigma * Kcut) *
        (paperFractionalSeminorm (originCube d (refinedStoppingScale q + 1))
          (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two
          g0.toField).toReal)
      u hf hL2 hinitial hrepair chi source hsource hcell hf0 q
      (mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg)
      (by
        have hbase : (paperFractionalSeminorm
            (originCube d (refinedStoppingScale q + 1))
            (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two
            g0.toField).toReal ≤ Fac * (Cdat * Mn) := by
          rw [hg0]; exact hsem
        refine (mul_le_mul_of_nonneg_left hbase
          (Real.sqrt_nonneg
            (fluxRowRieszEnlargedNqRatio (refinedStoppingScale q) sigma *
              Kcut))).trans (le_of_eq ?_)
        ring)
      hK hMn
      (by
        refine le_trans (le_of_eq ?_) hdbudget
        linear_combination
          ((repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q *
            Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) ^ 2 * Fac ^ 2 * Cdat ^ 2 *
            K * fluxRowSlotsNinefoldForcingConstant d) * hsqRK)
  have hdatum :
      fluxRowRieszEnlargedNqWeight d (refinedStoppingScale q) sigma * Kcut *
          (Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) *
            (paperFractionalSeminorm
              (originCube d (refinedStoppingScale q + 1))
              (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two
              g0.toField).toReal) ^ 2 ≤
        fluxRowRieszCellPhysicalScale alpha t R sigma (∫ x, f x ^ 2 ∂volume)
          (repairedStoppingPointwiseContractionFactor d ^ 2)
          ((3 : ℝ) ^ refinedStoppingScale q)
          (stoppingGraphDistance repairedStoppingGraph source hsource q) d := by
    rw [fluxRowRieszEnlargedNqWeight,
      repairedFluxRowRieszPartition_cellVolume_eq_cubeVolume_succ
        hinitial hrepair chi q] at *
    refine le_trans (le_of_eq ?_) hdatum0
    linear_combination
      (-(cubeVolume (originCube d (refinedStoppingScale q + 1)) *
        Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) ^ 2 *
        (paperFractionalSeminorm (originCube d (refinedStoppingScale q + 1))
          (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two
          g0.toField).toReal ^ 2)) * hsqRK
  refine fluxRowRiesz_cellVolume_mul_enlargedNq_sq_le_of_localNegative
    (hsigma := hsigma) ?_
  exact hconvert
    (fluxRowRieszEnlargedNqWeight d (refinedStoppingScale q) sigma * Kcut)
    t R (∫ x, f x ^ 2 ∂volume)
    (repairedStoppingPointwiseContractionFactor d ^ 2) lambdaInv
    (mul_nonneg (fluxRowRieszEnlargedNqWeight_nonneg _ _ _) hKcut)
    ht hR (integral_nonneg fun x ↦ sq_nonneg (f x)) (sq_nonneg _)
    hE1 hE2 hS hD henergy hdatum

end Chain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
