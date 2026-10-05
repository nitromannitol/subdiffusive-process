module

public import SubdiffusiveProcess.Frozen.Section6.CutoffDirichletHomogenization
public import SubdiffusiveProcess.Frozen.Section6.FixedCutoffDirichletAlgebraic
public import SubdiffusiveProcess.Frozen.Section6.Defs.OrdinaryVectorHMinusOne
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
public import SubdiffusiveProcess.Model.ACutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
@[expose] public section

/-!
# Provider for `t.B` — Theorem B is the conjunction of two proved Section 6 theorems

The printed Theorem B has exactly two bullets, and the tree had already proved both:
`t.cutoff.Dirichlet.homogenization` (the uniform `δ^ϑ` estimate, with the `f = 0` improvement)
and `t.fixed.cutoff.Dirichlet.algebraic` (the `3^{-α_hom(M-L)}` rate at fixed cutoff).  Both
are `PROVED` and axiom-clean, both carry the `H²` boundary datum, and both are stated on
`cu_0` as the source is.

So the provider is the pair.  There is nothing to assemble: `t.B` v1's three deviations —
deferring the boundary datum, generalising the cube, and hand-writing the weak formulations —
were what made that invisible.
-/

set_option autoImplicit false

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal

noncomputable section

namespace SubdiffusiveProcess.Providers.Main

theorem dirichlet_homogenization (d : ℕ) [NeZero d] (_hd : 2 ≤ d) :
    (∀ vartheta q : ℝ, vartheta ∈ Set.Ioo (0 : ℝ) 1 → 1 ≤ q →
           ∃ delta0 C : ℝ, 0 < delta0 ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
             (M.delta ≤ delta0 →
             ∃ Z : ℕ → ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
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
                             (l2Size (originCube d 0) f + h.norm))
:= ⟨SubdiffusiveProcess.Frozen.Section6.cutoff_dirichlet_homogenization d,
    SubdiffusiveProcess.Frozen.Section6.fixed_cutoff_dirichlet_algebraic d⟩

end SubdiffusiveProcess.Providers.Main

end
