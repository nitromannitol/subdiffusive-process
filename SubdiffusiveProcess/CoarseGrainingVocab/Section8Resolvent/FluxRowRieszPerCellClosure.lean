module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszRepairedInstantiation

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization Homogenization.Book
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- The first deterministic coefficient in the local coarse-graining bound. -/
def fluxRowRieszCoarseFirstFactor (C sigma : ℝ) : ℝ :=
  C * Real.rpow sigma (-(3 / 2 : ℝ))

/-- The second deterministic coefficient in the local coarse-graining bound. -/
def fluxRowRieszCoarseSecondFactor (C sigma : ℝ) : ℝ :=
  C * Real.rpow sigma (-(11 / 2 : ℝ)) * (((1 + sigma) / 2 - sigma)⁻¹)

/-- The deterministic constant after squaring the two coarse-graining terms. -/
def fluxRowRieszCoarsePriceConstant (k₁ k₂ : ℝ) : ℝ :=
  2 * (k₁ ^ 2 + k₂ ^ 2)

/-- The part of the local cell price before its random weight `W_Q`. -/
def fluxRowRieszCellPhysicalScale
    (ahom t R sigma fEnergy theta cellSize : ℝ)
    (graphDistance d : ℕ) : ℝ :=
  ahom * t⁻¹ * Real.rpow R (2 * sigma) * fEnergy *
    Real.rpow theta ((graphDistance : ℝ) / 2) *
    (cellSize / R) ^ (d + 6)

/-- Exact real readout of the two terms in `fluxRowLocalCoarseGrainingRHS`. -/
theorem fluxRowRiesz_localCoarseGrainingRHS_toReal_eq
    {d : ℕ} [NeZero d]
    (C : ℝ) (hC : 0 ≤ C) (m n : ℤ) (hnm : n < m)
    (a : Ch02.TriadicCoeffFamily d) (alpha sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1)
    (g : CubeEuclideanWspField (originCube d m)
      (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two)
    (u : H1Function (openCubeSet (originCube d m)))
    (hE1 : paperHomogenizationError (originCube d m) n (3 * sigma / 4)
      .infinity (.finite 1) a alpha ≠ ∞)
    (hE2 : paperHomogenizationError (originCube d m) n ((3 * sigma / 4) / 2)
      .infinity (.finite 2) a alpha ≠ ∞)
    (hS : weightedLocalSymmetricEnergyLp (originCube d m) n
      (by simpa [originCube] using hnm.le) (a.coeffOn (originCube d m)) u
      (fluxRowLocalLowerOrder sigma hsigma) (fluxRowLocalOrder sigma hsigma)
      FiniteLpExponent.two ≠ ∞)
    (hD : paperFractionalSeminorm (originCube d m)
      (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two g.toField ≠ ∞) :
    (fluxRowLocalCoarseGrainingRHS C m n hnm a alpha sigma hsigma g u).toReal =
      fluxRowRieszCoarseFirstFactor C sigma * Real.sqrt alpha *
          (paperHomogenizationError (originCube d m) n (3 * sigma / 4)
            .infinity (.finite 1) a alpha).toReal *
          (weightedLocalSymmetricEnergyLp (originCube d m) n
            (by simpa [originCube] using hnm.le) (a.coeffOn (originCube d m)) u
            (fluxRowLocalLowerOrder sigma hsigma) (fluxRowLocalOrder sigma hsigma)
            FiniteLpExponent.two).toReal +
        fluxRowRieszCoarseSecondFactor C sigma *
          (1 + (paperHomogenizationError (originCube d m) n
            ((3 * sigma / 4) / 2) .infinity (.finite 2) a alpha).toReal ^ 2) *
          (Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) *
            (paperFractionalSeminorm (originCube d m)
              (fluxRowLocalUpperOrder sigma hsigma)
              FiniteLpExponent.two g.toField).toReal) := by
  have hfront1 : 0 ≤ C * Real.rpow sigma (-(3 / 2 : ℝ)) * Real.sqrt alpha := by
    exact mul_nonneg
      (mul_nonneg hC (Real.rpow_nonneg hsigma.1.le _)) (Real.sqrt_nonneg _)
  have hgap : 0 ≤ ((1 + sigma) / 2 - sigma)⁻¹ := by
    apply inv_nonneg.mpr
    linarith [hsigma.2]
  have hfront2 : 0 ≤ C * Real.rpow sigma (-(11 / 2 : ℝ)) *
      ((1 + sigma) / 2 - sigma)⁻¹ *
      Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hsigma.1.le _)) hgap)
      (Real.rpow_nonneg (by norm_num) _)
  have hE2real :
      (1 + paperHomogenizationError (originCube d m) n
        ((3 * sigma / 4) / 2) .infinity (.finite 2) a alpha ^ 2).toReal =
        1 + (paperHomogenizationError (originCube d m) n
          ((3 * sigma / 4) / 2) .infinity (.finite 2) a alpha).toReal ^ 2 := by
    rw [ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.pow_ne_top hE2),
      ENNReal.toReal_one, ENNReal.toReal_pow]
  rw [fluxRowLocalCoarseGrainingRHS, ENNReal.toReal_add]
  · simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hfront1,
      ENNReal.toReal_ofReal hfront2, hE2real]
    unfold fluxRowRieszCoarseFirstFactor fluxRowRieszCoarseSecondFactor
    ring
  · finiteness
  · finiteness

/-- The elementary two-slot inequality which produces precisely the paper's
local random multiplier `W_Q`. -/
theorem fluxRowRiesz_localPriceAlgebra
    {cellVolume base k₁ k₂ E1 E2 alpha lambdaInv S D : ℝ}
    (hvolume : 0 ≤ cellVolume) (hbase : 0 ≤ base)
    (henergy : cellVolume * S ^ 2 ≤
      base * (1 + (alpha * lambdaInv) ^ 2))
    (hdatum : cellVolume * D ^ 2 ≤ base) :
    cellVolume * (k₁ * E1 * S + k₂ * (1 + E2 ^ 2) * D) ^ 2 ≤
      fluxRowRieszCoarsePriceConstant k₁ k₂ * base *
        fluxRowRieszCellWeight E1 E2 alpha lambdaInv := by
  unfold fluxRowRieszCoarsePriceConstant fluxRowRieszCellWeight
  have hE2p : 0 ≤ 1 + E2 ^ 2 := by nlinarith [sq_nonneg E2]
  have h1 := mul_le_mul_of_nonneg_left henergy (sq_nonneg E1)
  have h2 := mul_le_mul_of_nonneg_left hdatum (sq_nonneg (1 + E2 ^ 2))
  have h3inner : (1 + E2 ^ 2) ^ 2 + E1 ^ 2 * (1 + (alpha * lambdaInv) ^ 2) ≤
      (1 + E1 ^ 2 + E2 ^ 2) ^ 2 + E1 ^ 2 * (alpha * lambdaInv) ^ 2 := by
    nlinarith [sq_nonneg E1, hE2p, sq_nonneg (E1 * E2), sq_nonneg (E1 * E1)]
  have h3 := mul_le_mul_of_nonneg_left h3inner hbase
  have h4 := mul_le_mul_of_nonneg_left h1 (sq_nonneg k₁)
  have h5 := mul_le_mul_of_nonneg_left h2 (sq_nonneg k₂)
  have hW1 : E1 ^ 2 * (base * (1 + (alpha * lambdaInv) ^ 2)) ≤
      base * ((1 + E1 ^ 2 + E2 ^ 2) ^ 2 +
        E1 ^ 2 * (alpha * lambdaInv) ^ 2) := by
    nlinarith [h3, hbase, sq_nonneg (1 + E2 ^ 2)]
  have hW2 : (1 + E2 ^ 2) ^ 2 * base ≤
      base * ((1 + E1 ^ 2 + E2 ^ 2) ^ 2 +
        E1 ^ 2 * (alpha * lambdaInv) ^ 2) := by
    nlinarith [h3, hbase, sq_nonneg E1, sq_nonneg (E1 * (alpha * lambdaInv))]
  have h6 : k₁ ^ 2 * (E1 ^ 2 * (base * (1 + (alpha * lambdaInv) ^ 2))) +
      k₂ ^ 2 * ((1 + E2 ^ 2) ^ 2 * base) ≤
      (k₁ ^ 2 + k₂ ^ 2) *
        (base * ((1 + E1 ^ 2 + E2 ^ 2) ^ 2 +
          E1 ^ 2 * (alpha * lambdaInv) ^ 2)) := by
    nlinarith [mul_le_mul_of_nonneg_left hW1 (sq_nonneg k₁),
      mul_le_mul_of_nonneg_left hW2 (sq_nonneg k₂)]
  have hcross :
      0 ≤ cellVolume * (k₁ * E1 * S - k₂ * (1 + E2 ^ 2) * D) ^ 2 := by
    nlinarith [sq_nonneg (k₁ * E1 * S - k₂ * (1 + E2 ^ 2) * D), hvolume]
  nlinarith [h4, h5, h6, hcross]

/-- The two analytic slot estimates imply the complete graph-weighted local
cell price for the explicit coarse-graining right side. -/
theorem fluxRowRiesz_cellVolume_mul_coarseGrainingRHS_sq_le_price
    {d : ℕ} [NeZero d]
    (C : ℝ) (hC : 0 ≤ C) (m n : ℤ) (hnm : n < m)
    (a : Ch02.TriadicCoeffFamily d) (alpha sigma : ℝ)
    (halpha : 0 < alpha) (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1)
    (g : CubeEuclideanWspField (originCube d m)
      (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two)
    (u : H1Function (openCubeSet (originCube d m)))
    (hE1 : paperHomogenizationError (originCube d m) n (3 * sigma / 4)
      .infinity (.finite 1) a alpha ≠ ∞)
    (hE2 : paperHomogenizationError (originCube d m) n ((3 * sigma / 4) / 2)
      .infinity (.finite 2) a alpha ≠ ∞)
    (hS : weightedLocalSymmetricEnergyLp (originCube d m) n
      (by simpa [originCube] using hnm.le) (a.coeffOn (originCube d m)) u
      (fluxRowLocalLowerOrder sigma hsigma) (fluxRowLocalOrder sigma hsigma)
      FiniteLpExponent.two ≠ ∞)
    (hD : paperFractionalSeminorm (originCube d m)
      (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two g.toField ≠ ∞)
    (cellVolume t R fEnergy theta cellSize lambdaInv : ℝ)
    (graphDistance : ℕ)
    (hvolume : 0 ≤ cellVolume) (ht : 0 < t) (hR : 0 < R)
    (hfEnergy : 0 ≤ fEnergy) (htheta : 0 ≤ theta)
    (hcellSize : 0 ≤ cellSize)
    (henergy :
      cellVolume *
          (Real.sqrt alpha *
            (weightedLocalSymmetricEnergyLp (originCube d m) n
              (by simpa [originCube] using hnm.le) (a.coeffOn (originCube d m)) u
              (fluxRowLocalLowerOrder sigma hsigma)
              (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two).toReal) ^ 2 ≤
        fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
            graphDistance d * (1 + (alpha * lambdaInv) ^ 2))
    (hdatum :
      cellVolume *
          (Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) *
            (paperFractionalSeminorm (originCube d m)
              (fluxRowLocalUpperOrder sigma hsigma)
              FiniteLpExponent.two g.toField).toReal) ^ 2 ≤
        fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
          graphDistance d) :
    cellVolume *
        (fluxRowLocalCoarseGrainingRHS C m n hnm a alpha sigma hsigma g u).toReal ^ 2 ≤
      fluxRowRieszCellPrice
        (fluxRowRieszCoarsePriceConstant
          (fluxRowRieszCoarseFirstFactor C sigma)
          (fluxRowRieszCoarseSecondFactor C sigma))
        alpha t R sigma fEnergy theta cellSize graphDistance d
        (paperHomogenizationError (originCube d m) n (3 * sigma / 4)
          .infinity (.finite 1) a alpha).toReal
        (paperHomogenizationError (originCube d m) n ((3 * sigma / 4) / 2)
          .infinity (.finite 2) a alpha).toReal lambdaInv := by
  let physicalScale := fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy
    theta cellSize graphDistance d
  have hbase : 0 ≤ physicalScale := by
    have hthetaPow : 0 ≤ Real.rpow theta ((graphDistance : ℝ) / 2) :=
      Real.rpow_nonneg htheta _
    have hRPow : 0 ≤ Real.rpow R (2 * sigma) := Real.rpow_nonneg hR.le _
    have hsize : 0 ≤ (cellSize / R) ^ (d + 6) :=
      pow_nonneg (div_nonneg hcellSize hR.le) _
    dsimp only [physicalScale, fluxRowRieszCellPhysicalScale]
    positivity
  have hrhs := fluxRowRiesz_localCoarseGrainingRHS_toReal_eq
    C hC m n hnm a alpha sigma hsigma g u hE1 hE2 hS hD
  have hmain := fluxRowRiesz_localPriceAlgebra
    (cellVolume := cellVolume) (base := physicalScale)
    (k₁ := fluxRowRieszCoarseFirstFactor C sigma)
    (k₂ := fluxRowRieszCoarseSecondFactor C sigma)
    (E1 := (paperHomogenizationError (originCube d m) n (3 * sigma / 4)
      .infinity (.finite 1) a alpha).toReal)
    (E2 := (paperHomogenizationError (originCube d m) n ((3 * sigma / 4) / 2)
      .infinity (.finite 2) a alpha).toReal)
    (alpha := alpha) (lambdaInv := lambdaInv)
    (S := Real.sqrt alpha *
      (weightedLocalSymmetricEnergyLp (originCube d m) n
        (by simpa [originCube] using hnm.le) (a.coeffOn (originCube d m)) u
        (fluxRowLocalLowerOrder sigma hsigma) (fluxRowLocalOrder sigma hsigma)
        FiniteLpExponent.two).toReal)
    (D := Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) *
      (paperFractionalSeminorm (originCube d m)
        (fluxRowLocalUpperOrder sigma hsigma)
        FiniteLpExponent.two g.toField).toReal)
    hvolume hbase (by simpa only [physicalScale] using henergy)
    (by simpa only [physicalScale] using hdatum)
  calc
    cellVolume *
        (fluxRowLocalCoarseGrainingRHS C m n hnm a alpha sigma hsigma g u).toReal ^ 2 =
      cellVolume *
        (fluxRowRieszCoarseFirstFactor C sigma *
            (paperHomogenizationError (originCube d m) n (3 * sigma / 4)
              .infinity (.finite 1) a alpha).toReal *
            (Real.sqrt alpha *
              (weightedLocalSymmetricEnergyLp (originCube d m) n
                (by simpa [originCube] using hnm.le)
                (a.coeffOn (originCube d m)) u
                (fluxRowLocalLowerOrder sigma hsigma)
                (fluxRowLocalOrder sigma hsigma)
                FiniteLpExponent.two).toReal) +
          fluxRowRieszCoarseSecondFactor C sigma *
            (1 + (paperHomogenizationError (originCube d m) n
              ((3 * sigma / 4) / 2) .infinity (.finite 2) a alpha).toReal ^ 2) *
            (Real.rpow 3 (((1 + sigma) / 2) * (n : ℝ)) *
              (paperFractionalSeminorm (originCube d m)
                (fluxRowLocalUpperOrder sigma hsigma)
                FiniteLpExponent.two g.toField).toReal)) ^ 2 := by
        rw [hrhs]
        congr 2
        ring
    _ ≤ fluxRowRieszCoarsePriceConstant
          (fluxRowRieszCoarseFirstFactor C sigma)
          (fluxRowRieszCoarseSecondFactor C sigma) * physicalScale *
        fluxRowRieszCellWeight
          (paperHomogenizationError (originCube d m) n (3 * sigma / 4)
            .infinity (.finite 1) a alpha).toReal
          (paperHomogenizationError (originCube d m) n ((3 * sigma / 4) / 2)
            .infinity (.finite 2) a alpha).toReal alpha lambdaInv := hmain
    _ = fluxRowRieszCellPrice
        (fluxRowRieszCoarsePriceConstant
          (fluxRowRieszCoarseFirstFactor C sigma)
          (fluxRowRieszCoarseSecondFactor C sigma))
        alpha t R sigma fEnergy theta cellSize graphDistance d
        (paperHomogenizationError (originCube d m) n (3 * sigma / 4)
          .infinity (.finite 1) a alpha).toReal
        (paperHomogenizationError (originCube d m) n ((3 * sigma / 4) / 2)
          .infinity (.finite 2) a alpha).toReal lambdaInv := by
      unfold physicalScale fluxRowRieszCellPhysicalScale fluxRowRieszCellPrice
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
