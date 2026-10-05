
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszPerCellClosure

@[expose] public section

/-!
# The local flux price on the **analytic enlargement** of a repaired stopping cell

`FluxRowRieszRepairedCellPrice.lean` proves the deterministic two-term
comparison with every analytic object placed on the scale-`m` cube
`originCube d (refinedStoppingScale q)`.  The flux-row dual pairing
(`FluxRowDualPairing.lean`) consumes the negative fractional dual on the
**enlargement** `Q̂ = z + □_{m+1}`, which is where the partition's cutoff is
supported (`FluxRowRieszPartition.cutoff_support`,
`FluxRowRieszPartition.cell`).  Domain monotonicity does not transfer the
scale-`m` price to `Q̂` — a field supported in the annulus `Q̂ \ Q` has zero
scale-`m` dual and a positive enlarged dual — so the price is
re-derived here **directly at scale `m + 1`**.

Nothing in the underlying chain is tied to the cell's own scale: the translated
coarse-graining anchor `exists_fluxRowRiesz_translatedCell_rootFlux_le` is
generic in the pair `(m, z)`, and the price algebra
`fluxRowRiesz_cellVolume_mul_coarseGrainingRHS_sq_le_price` is generic in the
cell volume, the cell size and the graph distance.  The enlarged price is
therefore obtained by instantiating both at `(refinedStoppingScale q + 1,
refinedStoppingCenter q)` while **keeping the right-hand price exactly the
family's own**: the partition's `cellVolume q` on the left, and the cell size
`3 ^ refinedStoppingScale q` inside `fluxRowRieszCellPrice`.  This is what the
shell summation and the coefficient budget consume, so the enlargement is paid
for entirely inside the two analytic slot antecedents, which are now stated on
`Q̂` and on the ninefold cube.

Source: `s.fixed.coefficient` and `mfd:sec-speed`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization Homogenization.Book
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open _root_.SubdiffusiveProcess.Section8
open scoped ENNReal

noncomputable section

/-! ## The physical dual coefficient on the enlargement

The corrected cutoff pairing (`fluxRowDual_abs_re_enlargedCube_integral_le`,
`fluxRowDual_abs_im_enlargedCube_integral_le`, `FluxRowDualPairing.lean`)
prices the physical pairing by

```text
Nq = sqrt (2 * cubeVolume Q̂) * (paperNegativeFractionalDual Q̂ …).toReal
```

on `Q̂ = originCube d (m + 1)`, **not** by the repo's scale-normalized
`fluxRowRieszLocalNegative`, which carries the factor `3 ^ (-σ (m+1))` and no
volume factor at all.  The two differ by the explicit deterministic weight
below, so the price transfers by pure algebra once the two analytic slots are
stated with that weight folded into the cell volume. -/

/-- The deterministic weight relating the repo's scale-normalized local
negative norm on `Q̂` to the physical dual coefficient `Nq` of the corrected
cutoff pairing:  `Nq ^ 2 = fluxRowRieszEnlargedNqWeight d m σ *
fluxRowRieszLocalNegative (m+1) σ hσ F ^ 2`. -/
def fluxRowRieszEnlargedNqRatio (m : ℤ) (sigma : ℝ) : ℝ :=
  2 * Real.rpow 3 (sigma * ((m + 1 : ℤ) : ℝ)) ^ 2

theorem fluxRowRieszEnlargedNqRatio_nonneg (m : ℤ) (sigma : ℝ) :
    0 ≤ fluxRowRieszEnlargedNqRatio m sigma := by
  unfold fluxRowRieszEnlargedNqRatio
  positivity

/-- The volume-carrying form of the same weight.  Splitting off the cell volume
matters downstream: the coarse Caccioppoli is stated with the cube volume, so
only the volume-free `fluxRowRieszEnlargedNqRatio` is actually paid by the
slot budgets. -/
def fluxRowRieszEnlargedNqWeight (d : ℕ) (m : ℤ) (sigma : ℝ) : ℝ :=
  cubeVolume (originCube d (m + 1)) * fluxRowRieszEnlargedNqRatio m sigma

theorem fluxRowRieszEnlargedNqWeight_nonneg (d : ℕ) (m : ℤ) (sigma : ℝ) :
    0 ≤ fluxRowRieszEnlargedNqWeight d m sigma :=
  mul_nonneg (cubeVolume_nonneg _) (fluxRowRieszEnlargedNqRatio_nonneg _ _)

/-- **The normalization identity.**  `Nq ^ 2` is the weighted square of the
repo's scale-normalized local negative norm at scale `m + 1`.  The two
normalizations differ by the cell volume and by `3 ^ (2 σ (m+1))`; in
particular the scale-normalized one is *not* the coefficient of the corrected
cutoff pairing. -/
theorem fluxRowRiesz_enlargedNq_sq_eq {d : ℕ} {m : ℤ} {sigma : ℝ}
    {hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1}
    (F : CubeEuclideanLpField (originCube d (m + 1)) FiniteLpExponent.two) :
    (Real.sqrt (2 * cubeVolume (originCube d (m + 1))) *
        (paperNegativeFractionalDual (originCube d (m + 1))
          (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two F).toReal) ^ 2 =
      fluxRowRieszEnlargedNqWeight d m sigma *
        fluxRowRieszLocalNegative (m + 1) sigma hsigma F ^ 2 := by
  have hvol : (0 : ℝ) ≤ 2 * cubeVolume (originCube d (m + 1)) := by
    have := cubeVolume_nonneg (originCube d (m + 1)); linarith
  have hnn : (0 : ℝ) ≤ Real.rpow 3 (-sigma * ((m + 1 : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hloc : fluxRowRieszLocalNegative (m + 1) sigma hsigma F =
      Real.rpow 3 (-sigma * ((m + 1 : ℤ) : ℝ)) *
        (paperNegativeFractionalDual (originCube d (m + 1))
          (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two F).toReal := by
    unfold fluxRowRieszLocalNegative
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn]
  have hprod : Real.rpow 3 (sigma * ((m + 1 : ℤ) : ℝ)) *
      Real.rpow 3 (-sigma * ((m + 1 : ℤ) : ℝ)) = 1 := by
    have h := (Real.rpow_add (show (0 : ℝ) < 3 by norm_num)
      (sigma * ((m + 1 : ℤ) : ℝ)) (-sigma * ((m + 1 : ℤ) : ℝ))).symm
    simpa using h
  have hp2 : Real.rpow 3 (sigma * ((m + 1 : ℤ) : ℝ)) ^ 2 *
      Real.rpow 3 (-sigma * ((m + 1 : ℤ) : ℝ)) ^ 2 = 1 := by
    rw [← mul_pow, hprod]; norm_num
  rw [hloc, mul_pow, Real.sq_sqrt hvol, fluxRowRieszEnlargedNqWeight,
    fluxRowRieszEnlargedNqRatio, mul_pow]
  linear_combination
    (2 * cubeVolume (originCube d (m + 1)) *
      (paperNegativeFractionalDual (originCube d (m + 1))
        (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two F).toReal ^ 2) *
      hp2.symm

/-- **Transfer of the price to the physical dual coefficient.**  A price proved
for the scale-normalized local negative norm at the *weighted* cell volume is a
price for `Nq` at the cell volume itself.  The conclusion is literally the left
side of `FluxRowAssemblyEnlargedLocalPrice.cellVolume_mul_enlargedNq_sq_le`
(`FluxRowAssemblyEnlargedLocalPrice.lean`) with `fluxRowAssemblyEnlargedNq`
unfolded. -/
theorem fluxRowRiesz_cellVolume_mul_enlargedNq_sq_le_of_localNegative
    {d : ℕ} {m : ℤ} {sigma cellVol price : ℝ}
    {hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1}
    {F : CubeEuclideanLpField (originCube d (m + 1)) FiniteLpExponent.two}
    (h : fluxRowRieszEnlargedNqWeight d m sigma * cellVol *
        fluxRowRieszLocalNegative (m + 1) sigma hsigma F ^ 2 ≤ price) :
    cellVol *
        (Real.sqrt (2 * cubeVolume (originCube d (m + 1))) *
          (paperNegativeFractionalDual (originCube d (m + 1))
            (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two F).toReal) ^ 2 ≤
      price := by
  refine le_trans (le_of_eq ?_) h
  rw [fluxRowRiesz_enlargedNq_sq_eq (hsigma := hsigma) F]
  ring

/-- **Enlarged-cell local flux price.**  Identical to
`exists_fluxRowRiesz_repairedStoppingCell_localFluxPrice` except that every
analytic object lives on the enlargement `Q̂ = refinedStoppingCenter q +
□_{refinedStoppingScale q + 1}`: the local representative `u`, its recentring
`u0`, the recentred force `g0`, the homogenization errors, the weighted local
energy `S`, the datum seminorm `D`, and — the point of the file — the negative
fractional dual `fluxRowRieszLocalNegative (refinedStoppingScale q + 1)`.

The right-hand side is unchanged: the partition's `cellVolume q` multiplies the
square of the enlarged dual, and the price keeps the family's own cell size
`3 ^ refinedStoppingScale q` and repaired graph distance.  This is exactly the
per-cell hypothesis `hlocal` of `repairedFluxRowRieszCoefficientBudget`, at
`localNegative i q` read on `Q̂`. -/
theorem exists_fluxRowRiesz_repairedStoppingCell_enlargedLocalFluxPrice
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Ccoarse : ℝ, 0 < Ccoarse ∧
      ∀ {base : ℤ} {failure : TriadicCube d → Set (PotentialSample d)}
        {omega : PotentialSample d},
      ∀ (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
          cubeSet (triadicStoppingCandidate failure omega Q))
        (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
          cubeSet Q.1)
        (chi : RepairedStoppingCutoff failure omega base)
        (source : Finset (RefinedStoppingCell failure omega base)),
      ∀ hsource : source.Nonempty, ∀ q : RefinedStoppingCell failure omega base,
      ∀ (M : GMCModel d) (L : ℕ) (n : ℤ),
      ∀ hnm : n < refinedStoppingScale q + 1,
      ∀ (alpha sigma : ℝ), 0 < alpha →
      ∀ hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1,
      ∀ (g : Vec d → Vec d)
        (u : H1Function (translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q))),
      MemCubeEuclideanFullWsp (originCube d (refinedStoppingScale q + 1))
          (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two
          (fun x ↦ g (x + refinedStoppingCenter q)) →
      IsDivFormWeakSolutionOn (aCutoff M L omega)
          (translatedCube d (refinedStoppingScale q + 1)
            (refinedStoppingCenter q)) u g →
      ∃ (g0 : CubeEuclideanWspField (originCube d (refinedStoppingScale q + 1))
            (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two)
        (u0 v0 : H1Function
          (openCubeSet (originCube d (refinedStoppingScale q + 1)))),
        g0.toField = (fun x ↦ g (x + refinedStoppingCenter q)) ∧
        u0 = fluxRowRieszUntranslatedH1 (refinedStoppingCenter q) u ∧
        IsForcedEquation (originCube d (refinedStoppingScale q + 1))
          ((aCutoffFamily M L
            (translatePotentialSample
              (refinedStoppingCenter q) omega)).coeffOn
                (originCube d (refinedStoppingScale q + 1))) u0 g0.toField ∧
        IsScalarForcedEquation (originCube d (refinedStoppingScale q + 1))
          alpha v0 g0.toField ∧
        HasH10Difference (originCube d (refinedStoppingScale q + 1)) u0 v0 ∧
        let afam := aCutoffFamily M L
          (translatePotentialSample (refinedStoppingCenter q) omega)
        let rhs := fluxRowLocalCoarseGrainingRHS Ccoarse
          (refinedStoppingScale q + 1) n hnm afam alpha sigma hsigma g0 u0
        let E1 := (paperHomogenizationError
          (originCube d (refinedStoppingScale q + 1))
          n (3 * sigma / 4) .infinity (.finite 1) afam alpha).toReal
        let E2 := (paperHomogenizationError
          (originCube d (refinedStoppingScale q + 1))
          n ((3 * sigma / 4) / 2) .infinity (.finite 2) afam alpha).toReal
        let S := (weightedLocalSymmetricEnergyLp
          (originCube d (refinedStoppingScale q + 1)) n
          (by simpa [originCube] using hnm.le)
          (afam.coeffOn (originCube d (refinedStoppingScale q + 1))) u0
          (fluxRowLocalLowerOrder sigma hsigma) (fluxRowLocalOrder sigma hsigma)
          FiniteLpExponent.two).toReal
        let D := Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) *
          (paperFractionalSeminorm (originCube d (refinedStoppingScale q + 1))
            (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two
            g0.toField).toReal
        ENNReal.ofReal
              (Real.rpow 3 (-sigma * ((refinedStoppingScale q + 1 : ℤ) : ℝ))) *
              paperNegativeFractionalDual
                (originCube d (refinedStoppingScale q + 1))
                (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two
                (centeredCubeRootFluxDefectL2Field (refinedStoppingScale q + 1)
                  (afam.coeffOn (originCube d (refinedStoppingScale q + 1)))
                  alpha u0) ≤
            rhs ∧
          ∀ (cellWeight t R fEnergy theta lambdaInv : ℝ),
            0 ≤ cellWeight → 0 < t → 0 < R →
            0 ≤ fEnergy → 0 ≤ theta →
            paperHomogenizationError (originCube d (refinedStoppingScale q + 1))
              n (3 * sigma / 4) .infinity (.finite 1) afam alpha ≠ ∞ →
            paperHomogenizationError (originCube d (refinedStoppingScale q + 1))
              n ((3 * sigma / 4) / 2) .infinity (.finite 2) afam alpha ≠ ∞ →
            weightedLocalSymmetricEnergyLp
              (originCube d (refinedStoppingScale q + 1)) n
              (by simpa [originCube] using hnm.le)
              (afam.coeffOn (originCube d (refinedStoppingScale q + 1))) u0
              (fluxRowLocalLowerOrder sigma hsigma)
              (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two ≠ ∞ →
            paperFractionalSeminorm (originCube d (refinedStoppingScale q + 1))
              (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two
              g0.toField ≠ ∞ →
            cellWeight * (Real.sqrt alpha * S) ^ 2 ≤
              fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta
                  ((3 : ℝ) ^ refinedStoppingScale q)
                  (stoppingGraphDistance repairedStoppingGraph source hsource q) d *
                (1 + (alpha * lambdaInv) ^ 2) →
            cellWeight * D ^ 2 ≤
              fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta
                ((3 : ℝ) ^ refinedStoppingScale q)
                (stoppingGraphDistance repairedStoppingGraph source hsource q) d →
            cellWeight *
                (fluxRowRieszLocalNegative (refinedStoppingScale q + 1) sigma
                  hsigma
                  (centeredCubeRootFluxDefectL2Field (refinedStoppingScale q + 1)
                    (afam.coeffOn (originCube d (refinedStoppingScale q + 1)))
                    alpha u0)) ^ 2 ≤
              fluxRowRieszCellPrice
                (fluxRowRieszCoarsePriceConstant
                  (fluxRowRieszCoarseFirstFactor Ccoarse sigma)
                  (fluxRowRieszCoarseSecondFactor Ccoarse sigma))
                alpha t R sigma fEnergy theta
                ((3 : ℝ) ^ refinedStoppingScale q)
                (stoppingGraphDistance repairedStoppingGraph source hsource q) d
                E1 E2 lambdaInv := by
  obtain ⟨Ccoarse, hCcoarse, hmain⟩ :=
    exists_fluxRowRiesz_translatedCell_rootFlux_le d hd
  refine ⟨Ccoarse, hCcoarse, ?_⟩
  intro base failure omega hinitial hrepair chi source hsource q M L n hnm alpha
    sigma halpha hsigma g u hg hu
  obtain ⟨g0, u0, v0, hg0, hu0, hforced, hscalar, htrace, hcoarse⟩ :=
    hmain M L omega (refinedStoppingScale q + 1) n hnm (refinedStoppingCenter q)
      alpha sigma halpha hsigma g u hg hu
  refine ⟨g0, u0, v0, hg0, hu0, hforced, hscalar, htrace, ?_⟩
  dsimp only
  refine ⟨hcoarse, ?_⟩
  intro cellWeight t R fEnergy theta lambdaInv hcw ht hR hfEnergy htheta
    hE1 hE2 hS hD henergy hdatum
  set afam := aCutoffFamily M L
    (translatePotentialSample (refinedStoppingCenter q) omega) with hafam
  have hrhs : fluxRowLocalCoarseGrainingRHS Ccoarse
      (refinedStoppingScale q + 1) n hnm afam alpha sigma hsigma g0 u0 ≠ ∞ := by
    unfold fluxRowLocalCoarseGrainingRHS
    finiteness
  have hprice := fluxRowRiesz_cellVolume_mul_coarseGrainingRHS_sq_le_price
    Ccoarse hCcoarse.le (refinedStoppingScale q + 1) n hnm afam alpha sigma
    halpha hsigma g0 u0 hE1 hE2 hS hD
    cellWeight t R
    fEnergy theta ((3 : ℝ) ^ refinedStoppingScale q) lambdaInv
    (stoppingGraphDistance repairedStoppingGraph source hsource q)
    hcw ht hR hfEnergy htheta (zpow_nonneg (by norm_num) _) henergy hdatum
  exact fluxRowRiesz_cellVolume_mul_localNegative_sq_le_cellPrice hcw
    hcoarse hrhs hprice

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
