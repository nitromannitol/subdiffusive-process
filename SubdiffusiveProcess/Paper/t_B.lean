module

public import SubdiffusiveProcess.Frozen.Main.DirichletHomogenization
public import SubdiffusiveProcess.Section6.UniformFixedCutoffDirichlet

@[expose] public section

/-! Theorem B, with the fixed-cutoff moment constant uniform over every
model of the same disorder strength. -/

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem t_B (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∀ vartheta q : ℝ, vartheta ∈ Set.Ioo (0 : ℝ) 1 → 1 ≤ q →
           ∃ delta0 C : ℝ, 0 < delta0 ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
             (M.delta ≤ delta0 →
             ∃ Z : ℕ → ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ,
               (∀ L N, L ≤ N →
                 CoefficientMeasurable
                   (fun omega ↦ rescaledCutoffCoefficient M L N omega) (Z L N)) ∧
               (∀ L N omega, L ≤ N → 1 ≤ Z L N omega) ∧
               (∀ L N, L ≤ N →
                 eLpNorm (Z L N) (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal C) ∧
               ∀ᵐ omega ∂M.P.toMeasure, ∀ L N : ℕ, L ≤ N →
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
                         ENNReal.ofReal (Z L N omega * M.delta ^ vartheta) *
                           (l2Size (originCube d 0) f + h.norm) ∧
                         (f = 0 →
                         l2Size (originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                               ordinaryVectorHMinusOne (originCube d 0) gradDifference +
                             ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
                           ENNReal.ofReal (Z L N omega * C * M.delta) * h.norm))) ∧
    (∃ alphaHom : ℝ, 0 < alphaHom ∧
           ∀ L : ℕ, ∀ q : ℝ, 1 ≤ q → ∀ delta : ℝ,
             ∃ C : ℝ, 0 < C ∧
               ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta = delta →
               ∃ Y : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ,
               CoefficientMeasurable (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L) Y ∧
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
                             (l2Size (originCube d 0) f + h.norm)) := by
  exact ⟨(SubdiffusiveProcess.Frozen.Main.dirichlet_homogenization d hd).1,
    SubdiffusiveProcess.Section6.fixed_cutoff_dirichlet_algebraic_uniform d hd⟩

end Paper
