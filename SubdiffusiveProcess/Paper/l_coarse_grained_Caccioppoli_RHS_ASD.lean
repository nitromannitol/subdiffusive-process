module

public import SubdiffusiveProcess.Caccioppoli.SourceBoundary
public import SubdiffusiveProcess.Section2.CoarseGrainedCaccioppoli
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase



@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open Homogenization hiding Vec Mat TriadicCube
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem l_coarse_grained_Caccioppoli_RHS_ASD {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s t : ℝ), 0 < s → s < 1 → 0 < t → t < (1 / 2 : ℝ) → s + t < 1 →
        ∀ x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0),
        ∀ (a : Ch02.TriadicCoeffFamily d),
          (∀ Q, Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) →
          ∀ u : Homogenization.H1Function
              (Homogenization.openCubeSet (Homogenization.originCube d 0)),
          ∀ (gF Hh : PaperPositiveSobolevField (Homogenization.originCube d 0) (2 * t)
              Homogenization.FiniteLpExponent.two)
            (hh : Homogenization.H1Function
              (Homogenization.openCubeSet (Homogenization.originCube d 0))),
            Hh.toField = hh.grad →
            Homogenization.cubeAverage (Homogenization.originCube d 0) hh.toFun = 0 →
            Homogenization.Book.Ch03.ABK26.IsForcedEquation (Homogenization.originCube d 0)
              (a.coeffOn (Homogenization.originCube d 0)) u gF.toField →
            Homogenization.Book.Ch01.LocalizedZeroTraceFunctionOn
              (Ch02.cubeDomain (Homogenization.originCube d 0) : Set (Vec d))
              (Homogenization.Book.Ch03.openCubeAtScale x
                ((Homogenization.originCube d 0).scale - 1))
              (fun y => u.toFun y - hh.toFun y) →
            Ch03.localizedCoeffEnergyValue
                (Ch03.caccioppoliCoreSet (Homogenization.originCube d 0) x)
                (a.coeffOn (Homogenization.originCube d 0)) u ≤
              Real.rpow (C / (1 - s - t)) (2 + 4 * s / (1 - s - t)) *
                Real.rpow
                  (LambdaDefault (Homogenization.originCube d 0) s a /
                    lambdaDefault (Homogenization.originCube d 0) t a)
                  ((s + (1 - s - t)) / (1 - s - t)) *
                (lambdaDefault (Homogenization.originCube d 0) t a *
                    Homogenization.cubeLpNorm (Homogenization.originCube d 0) (2 : ℝ≥0∞)
                      u.toFun ^ 2 +
                  t ^ (-11 : ℤ) * (lambdaDefault (Homogenization.originCube d 0) t a)⁻¹ *
                    gF.norm.toReal ^ 2 +
                  t ^ (-3 : ℤ) * LambdaDefault (Homogenization.originCube d 0) t a *
                    Hh.norm.toReal ^ 2) := by
  exact SubdiffusiveProcess.Caccioppoli.source_boundary_caccioppoli hd

end SubdiffusiveProcess.Paper
