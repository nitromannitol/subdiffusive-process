module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszTranslatedCell

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- The local random multiplier `W_Q` printed immediately before
`e.whole.resolvent.local.flux`. -/
def fluxRowRieszCellWeight (E1 E2 ahom lambdaInv : ℝ) : ℝ :=
  (1 + E1 ^ 2 + E2 ^ 2) ^ 2 + E1 ^ 2 * (ahom * lambdaInv) ^ 2

theorem fluxRowRieszCellWeight_nonneg (E1 E2 ahom lambdaInv : ℝ) :
    0 ≤ fluxRowRieszCellWeight E1 E2 ahom lambdaInv := by
  unfold fluxRowRieszCellWeight
  positivity

/-- The right side of `e.whole.resolvent.local.flux`, including graph
distance, relative cell size, and `W_Q`. -/
def fluxRowRieszCellPrice (C ahom t R sigma fEnergy theta cellSize : ℝ)
    (graphDistance d : ℕ) (E1 E2 lambdaInv : ℝ) : ℝ :=
  C * ahom * t⁻¹ * Real.rpow R (2 * sigma) * fEnergy *
    Real.rpow theta ((graphDistance : ℝ) / 2) *
    (cellSize / R) ^ (d + 6) *
    fluxRowRieszCellWeight E1 E2 ahom lambdaInv

/-- The scale-normalized local negative norm controlled by the translated
Section 2 coarse-graining theorem. -/
def fluxRowRieszLocalNegative {d : ℕ} (m : ℤ) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1)
    (F : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two) : ℝ :=
  (ENNReal.ofReal (Real.rpow 3 (-sigma * (m : ℝ))) *
    paperNegativeFractionalDual (originCube d m)
      (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two F).toReal

theorem fluxRowRieszLocalNegative_nonneg {d : ℕ} (m : ℤ) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1)
    (F : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two) :
    0 ≤ fluxRowRieszLocalNegative m sigma hsigma F :=
  ENNReal.toReal_nonneg

/-- Real readout of the local coarse-graining inequality. -/
theorem fluxRowRieszLocalNegative_le_rhs_toReal {d : ℕ} {m : ℤ}
    {sigma : ℝ} {hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1}
    {F : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two}
    {rhs : ℝ≥0∞}
    (hcoarse : ENNReal.ofReal (Real.rpow 3 (-sigma * (m : ℝ))) *
        paperNegativeFractionalDual (originCube d m)
          (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two F ≤ rhs)
    (hrhs : rhs ≠ ∞) :
    fluxRowRieszLocalNegative m sigma hsigma F ≤ rhs.toReal := by
  unfold fluxRowRieszLocalNegative
  exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hrhs hcoarse) hrhs).2 hcoarse

/-- **Per-cell flux estimate, conditional on graph decay.**  The only
remaining quantitative premise is the graph-decay bound for the explicit
coarse-graining right side.  Its conclusion has exactly the factor
`theta^(dist/2) (size(Q)/R)^(d+6) W_Q` printed in the paper. -/
theorem fluxRowRiesz_cellVolume_mul_localNegative_sq_le_cellPrice
    {d : ℕ} {m : ℤ} {sigma : ℝ}
    {hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1}
    {F : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two}
    {rhs : ℝ≥0∞}
    {cellVolume C ahom t R fEnergy theta cellSize E1 E2 lambdaInv : ℝ}
    {graphDistance : ℕ}
    (hvolume : 0 ≤ cellVolume)
    (hcoarse : ENNReal.ofReal (Real.rpow 3 (-sigma * (m : ℝ))) *
        paperNegativeFractionalDual (originCube d m)
          (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two F ≤ rhs)
    (hrhs : rhs ≠ ∞)
    (hgraphDecay : cellVolume * rhs.toReal ^ 2 ≤
      fluxRowRieszCellPrice C ahom t R sigma fEnergy theta cellSize
        graphDistance d E1 E2 lambdaInv) :
    cellVolume * (fluxRowRieszLocalNegative m sigma hsigma F) ^ 2 ≤
      fluxRowRieszCellPrice C ahom t R sigma fEnergy theta cellSize
        graphDistance d E1 E2 lambdaInv := by
  apply le_trans _ hgraphDecay
  exact mul_le_mul_of_nonneg_left
    (sq_le_sq₀ (fluxRowRieszLocalNegative_nonneg m sigma hsigma F)
      ENNReal.toReal_nonneg |>.2
        (fluxRowRieszLocalNegative_le_rhs_toReal hcoarse hrhs)) hvolume

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
