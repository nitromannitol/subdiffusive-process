module

public import SubdiffusiveProcess.Providers.Section6.FixedCutoffDirichletAlgebraic

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal


theorem SubdiffusiveProcess.Frozen.Section6.fixed_cutoff_dirichlet_algebraic
    (d : ℕ) [NeZero d] :
    ∃ alphaHom : ℝ, 0 < alphaHom ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ L : ℕ, ∀ q : ℝ, 1 ≤ q →
        ∃ C : ℝ, 0 < C ∧
          ∃ Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
          CoefficientMeasurable (_root_.SubdiffusiveProcess.Model.aCutoff M L) Y ∧
            (∀ omega, 1 ≤ Y omega) ∧
            eLpNorm Y (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal C ∧
            ∀ᵐ omega ∂M.P.toMeasure, ∀ N : ℕ, L ≤ N →
              ∀ (f : Vec d → ℝ),
                MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))) →
              ∀ h : H2Datum (originCube d 0),
                (∃ uLM : H1Function (openCubeSet (originCube d 0)),
                  IsScalarDirichletSolutionOn
                    (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                    (originCube d 0) uLM h.toH1 f) ∧
                (∀ uLM uLM' : H1Function (openCubeSet (originCube d 0)),
                  IsScalarDirichletSolutionOn
                      (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                      (originCube d 0) uLM h.toH1 f →
                  IsScalarDirichletSolutionOn
                      (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                      (originCube d 0) uLM' h.toH1 f →
                  uLM.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uLM'.toFun ∧
                    uLM.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uLM'.grad) ∧
                (∃ uHom : H1Function (openCubeSet (originCube d 0)),
                  IsScalarDirichletSolutionOn (fun _ ↦ 1)
                    (originCube d 0) uHom h.toH1 f) ∧
                (∀ uHom uHom' : H1Function (openCubeSet (originCube d 0)),
                  IsScalarDirichletSolutionOn (fun _ ↦ 1)
                      (originCube d 0) uHom h.toH1 f →
                  IsScalarDirichletSolutionOn (fun _ ↦ 1)
                      (originCube d 0) uHom' h.toH1 f →
                  uHom.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uHom'.toFun ∧
                    uHom.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uHom'.grad) ∧
                ∀ (uLM uHom : H1Function (openCubeSet (originCube d 0))),
                  IsScalarDirichletSolutionOn
                      (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                      (originCube d 0) uLM h.toH1 f →
                  IsScalarDirichletSolutionOn (fun _ ↦ 1)
                      (originCube d 0) uHom h.toH1 f →
                  ∃ gradDifference fluxDifference : L2VectorField (originCube d 0),
                    (∀ x, gradDifference.toFun x = uLM.grad x - uHom.grad x) ∧
                    (∀ x, fluxDifference.toFun x =
                      rescaledCutoffCoefficient M L N omega x • uLM.grad x - uHom.grad x) ∧
                    l2Size (originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                          ordinaryVectorHMinusOne (originCube d 0) gradDifference +
                        ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
                      ENNReal.ofReal
                          (Y omega * (3 : ℝ) ^ (-alphaHom * ((N : ℝ) - (L : ℝ)))) *
                        (l2Size (originCube d 0) f + h.norm)

:= SubdiffusiveProcess.Providers.Section6.fixed_cutoff_dirichlet_algebraic d
