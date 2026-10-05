module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section2Support
public import SubdiffusiveProcess.Providers.Section2.CoarseGrainedCaccioppoli

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal


theorem SubdiffusiveProcess.Section2.coarse_grained_caccioppoli {d : ℕ} :
    2 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∀ (s t : ℝ), 0 < s → s < 1 → 0 < t → t ≤ (1 / 4 : ℝ) → s + t < 1 →
        ∀ (a : Ch02.TriadicCoeffFamily d),
          (∀ Q, Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) →
          ∀ u : Homogenization.H1Function
              (Homogenization.openCubeSet (Homogenization.originCube d 0)),
            ∀ f : PaperPositiveSobolevField
                (Homogenization.originCube d 0) (2 * t)
                Homogenization.FiniteLpExponent.two,
              Homogenization.Book.Ch03.ABK26.IsForcedEquation
                (Homogenization.originCube d 0)
                (a.coeffOn (Homogenization.originCube d 0)) u f.toField →
              coefficientEnergyNorm (Homogenization.originCube d (-1)) a u.grad ^ 2 ≤
                Real.rpow (C / (1 - s - t))
                    (2 + 4 * s / (1 - s - t)) *
                  Real.rpow
                    (LambdaDefault (Homogenization.originCube d 0) s a /
                      lambdaDefault (Homogenization.originCube d 0) t a)
                    (s / (1 - s - t)) *
                  LambdaDefault (Homogenization.originCube d 0) s a *
                  Homogenization.cubeLpNorm (Homogenization.originCube d 0)
                    (2 : ℝ≥0∞) u.toFun ^ 2 +
                t ^ (-11 : ℤ) *
                  Real.rpow (C / (1 - s - t))
                    (2 + 4 * s / (1 - s - t)) *
                  Real.rpow
                    (LambdaDefault (Homogenization.originCube d 0) s a /
                      lambdaDefault (Homogenization.originCube d 0) t a)
                    ((1 - t) / (1 - s - t)) *
                  (lambdaDefault (Homogenization.originCube d 0) t a)⁻¹ *
                  f.norm.toReal ^ 2

:= SubdiffusiveProcess.Providers.Section2.coarse_grained_caccioppoli
