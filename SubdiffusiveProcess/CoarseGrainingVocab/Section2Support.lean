import SubdiffusiveProcess.CoarseGrainingVocab.Induction
import SubdiffusiveProcess.Frozen.Vocab.PaperNegativeFractionalDual
import Homogenization.Book.Ch03.ABK26.FluxComparisonDefinitions
import Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingDefinitions

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization.Book
open scoped ENNReal

noncomputable section

/-- Source-positive Sobolev carrier, including the first-order endpoint. -/
inductive PaperPositiveSobolevField {d : ℕ} (Q : TriadicCube d)
    (r : ℝ) (p : Homogenization.FiniteLpExponent) where
  | fractional (s : Homogenization.FractionalOrder) (hs : s.1 = r)
      (F : Homogenization.CubeEuclideanWspField Q s p)
  | firstOrder (hr : r = 1) (hp : p = Homogenization.FiniteLpExponent.two)
      (F : Homogenization.CubeVectorH1Function Q)

namespace PaperPositiveSobolevField

/-- Underlying vector field. -/
noncomputable def toField {d : ℕ} {Q : TriadicCube d} {r : ℝ}
    {p : Homogenization.FiniteLpExponent}
    (F : PaperPositiveSobolevField Q r p) : Vec d → Vec d :=
  match F with
  | .fractional _ _ G => G.toField
  | .firstOrder _ _ G => G.toField

/-- Additive normalized positive Sobolev norm. -/
noncomputable def norm {d : ℕ} {Q : TriadicCube d} {r : ℝ}
    {p : Homogenization.FiniteLpExponent}
    (F : PaperPositiveSobolevField Q r p) : ℝ≥0∞ :=
  match F with
  | .fractional s _ G => paperFractionalFullNorm Q s p G.toField
  | .firstOrder _ _ G =>
      ENNReal.ofReal
        ((Real.sqrt (Homogenization.cubeVolume Q))⁻¹ * G.gradientCoordL2NormSum +
          (Homogenization.cubeScaleFactor Q)⁻¹ *
            Homogenization.cubeLpNorm Q (2 : ℝ≥0∞) (G.toField : Vec d → Vec d))

end PaperPositiveSobolevField

/-- Average of local coefficient energies over scale-`k` descendants. -/
noncomputable def paperAverageLocalEnergyPow {d : ℕ} (m k : ℤ)
    (a : Ch02.TriadicCoeffFamily d)
    (u : Homogenization.H1Function
      (Homogenization.openCubeSet (Homogenization.originCube d m)))
    (p : ℝ) : ℝ :=
  Homogenization.descendantsAverage (Homogenization.originCube d m)
    (Int.toNat (m - k)) fun R => Real.rpow (coefficientEnergyNorm R a u.grad) p

end

end SubdiffusiveProcess.CoarseGrainingVocab
