module

public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import Homogenization.Book.Ch01.Definitions
public import Homogenization.Book.Ch03.Definitions
public import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.CubeVectorH1
public import Homogenization.Sobolev.Fractional.EuclideanWspSmoothDual

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization.Book
open scoped BigOperators ENNReal

noncomputable section

/-- Scalar normalized `H⁻¹` dual. -/
noncomputable abbrev hMinusOne {d : ℕ} [NeZero d]
    (U : Set (Vec d)) (hU : Homogenization.IsOpenBoundedConvexDomain U)
    (hne : U.Nonempty) (f : Vec d → ℝ)
    (hf : MemLp f (ENNReal.conjExponent (2 : ENNReal))
      (hU.toBoundedMeasurableDomain hne).normalizedVolume) : ℝ≥0∞ :=
  Ch01.normalizedZeroBoundaryHMinusOneSeminorm U hU hne f hf

/-- Existing full inhomogeneous smooth-test dual formulation. -/
noncomputable abbrev wMinusFractional {d : ℕ}
    (Q : TriadicCube d) (s : Homogenization.FractionalOrder)
    (q : Homogenization.FiniteLpExponent)
    (F : Homogenization.CubeEuclideanLpField Q
      Homogenization.FiniteLpExponent.two) : ℝ≥0∞ :=
  Homogenization.cubeEuclideanNegativeWspSmoothDualENorm Q s q F

/-- The `q=2` hatted fractional negative Sobolev formulation. -/
noncomputable abbrev hMinusFractional {d : ℕ}
    (Q : TriadicCube d) (s : Homogenization.FractionalOrder)
    (F : Homogenization.CubeEuclideanLpField Q
      Homogenization.FiniteLpExponent.two) : ℝ≥0∞ :=
  wMinusFractional Q s Homogenization.FiniteLpExponent.two F

/-- Paper finite-`q` concrete negative Besov norm. -/
noncomputable def negativeBesovCircFinite {d : ℕ}
    (P : Ch01.CircNegativeBesovFiniteParameters) (Q : TriadicCube d)
    (f : Vec d → ℝ) (hf : Ch01.CircNegativeBesovIntegrable Q f) : ℝ≥0∞ :=
  (ENNReal.ofReal P.s) ^ P.q⁻¹ * Ch01.circNegativeBesovFiniteSeminorm P Q f hf

/-- Paper endpoint concrete negative Besov norm. -/
noncomputable abbrev negativeBesovCircTop {d : ℕ}
    (P : Ch01.CircNegativeBesovTopParameters) (Q : TriadicCube d)
    (f : Vec d → ℝ) (hf : Ch01.CircNegativeBesovIntegrable Q f) : ℝ≥0∞ :=
  Ch01.circNegativeBesovTopSeminorm P Q f hf

/-- Paper finite-`q` positive overlap seminorm. -/
noncomputable def positiveBesovFiniteSeminorm {d : ℕ}
    (P : Ch01.PositiveBesovFiniteParameters) (Q : TriadicCube d)
    (u : Vec d → ℝ) (hu : Ch01.PositiveBesovIntegrable Q u) : ℝ≥0∞ :=
  (ENNReal.ofReal P.s) ^ P.q⁻¹ * Ch01.positiveBesovFiniteSeminorm P Q u hu

/-- Paper finite-`q` positive overlap norm. -/
noncomputable def positiveBesovFiniteNorm {d : ℕ}
    (P : Ch01.PositiveBesovFiniteParameters) (Q : TriadicCube d)
    (u : Vec d → ℝ) (hu : Ch01.PositiveBesovIntegrable Q u) : ℝ≥0∞ :=
  positiveBesovFiniteSeminorm P Q u hu +
    Homogenization.exactOverlapRootWeight Q P.s *
      ENNReal.ofReal |Homogenization.exactOverlapRootMean Q u hu.root|

/-- Paper endpoint positive overlap seminorm. -/
noncomputable abbrev positiveBesovTopSeminorm {d : ℕ}
    (P : Ch01.PositiveBesovTopParameters) (Q : TriadicCube d)
    (u : Vec d → ℝ) (hu : Ch01.PositiveBesovIntegrable Q u) : ℝ≥0∞ :=
  Ch01.positiveBesovTopSeminorm P Q u hu

/-- Paper endpoint positive overlap norm. -/
noncomputable abbrev positiveBesovTopNorm {d : ℕ}
    (P : Ch01.PositiveBesovTopParameters) (Q : TriadicCube d)
    (u : Vec d → ℝ) (hu : Ch01.PositiveBesovIntegrable Q u) : ℝ≥0∞ :=
  Ch01.positiveBesovTopNorm P Q u hu

/-- Available three-index form on the diagonal `r=p`. -/
noncomputable abbrev positiveBesovThreeIndexDiagonalNorm {d : ℕ}
    (P : Ch01.PositiveBesovFiniteParameters) (r : ℝ) (_hr : r = P.p)
    (Q : TriadicCube d) (u : Vec d → ℝ)
    (hu : Ch01.PositiveBesovIntegrable Q u) : ℝ≥0∞ :=
  positiveBesovFiniteNorm P Q u hu

/-- The printed factor `c_{sq}^{-1/q}`. -/
noncomputable def paperPoincareGeometricFactor (s : ℝ)
    (q : Ch02.MultiscaleExponent) : ℝ :=
  match q with
  | .finite q => Real.rpow (Ch02.geometricDiscount s q) (-q⁻¹)
  | .infinity => 1

/-- Paper-normalized vector negative Besov seminorm. -/
noncomputable def paperScaleNormalizedNegativeBesovVectorNorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (q : Ch02.MultiscaleExponent)
    (F : Vec d → Vec d) : ℝ :=
  match q with
  | .finite q => Real.rpow s (1 / q) *
      Homogenization.Book.Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) F
  | .infinity =>
      Homogenization.Book.Ch03.scaleNormalizedNegativeBesovVectorNorm Q s .infinity F

/-- Normalized coefficient-energy norm. -/
noncomputable def coefficientEnergyNorm {d : ℕ} (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) (F : Vec d → Vec d) : ℝ :=
  Real.sqrt <| ∫ x, Homogenization.vecDot (F x)
    (Homogenization.matVecMul ((a.coeffOn Q).toCoeffField x) (F x))
    ∂Homogenization.normalizedCubeMeasure Q

/-- Normalized inverse-coefficient energy norm. -/
noncomputable def inverseCoefficientEnergyNorm {d : ℕ} (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) (F : Vec d → Vec d) : ℝ :=
  Real.sqrt <| ∫ x, Homogenization.vecDot (F x)
    (Homogenization.matVecMul ((a.coeffOn Q).toCoeffField x)⁻¹ (F x))
    ∂Homogenization.normalizedCubeMeasure Q

/-- Fractional seminorm with the paper's leading normalization. -/
noncomputable def paperFractionalSeminorm {d : ℕ} (Q : TriadicCube d)
    (s : Homogenization.FractionalOrder) (p : Homogenization.FiniteLpExponent)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  (ENNReal.ofReal s.1) ^ (p.exponent.toReal)⁻¹ *
    Homogenization.cubeEuclideanWspESeminorm Q s p F

/-- The exact additive full test norm printed in the paper. -/
noncomputable def paperFractionalFullNorm {d : ℕ} (Q : TriadicCube d)
    (s : Homogenization.FractionalOrder) (p : Homogenization.FiniteLpExponent)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  paperFractionalSeminorm Q s p F +
    (ENNReal.ofReal (Homogenization.cubeScaleFactor Q)) ^ (-s.1) *
      (Homogenization.cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
        p.exponent F

end

end SubdiffusiveProcess.CoarseGrainingVocab
