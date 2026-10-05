module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FixedCutoffConditionalConclusion

@[expose] public section

/-!
# The single named hypothesis: the AK.HC supply interfaceThe supply interface narrows the open
supply question to one missing external input: the conclusion of
[AK.HC, Proposition D.3] applied to the logarithmic input
`e.fixed.cutoff.logarithmic.input` (now proved in
`LogarithmicInput.lean`), combined with [Theorem B, Theorem 4.1] and
Definition `d.mathcal.E` to give the response envelope
`e.fixed.cutoff.response.algebraic`.

`FixedCutoffResponseSupply d` below is that input, and nothing else.  The
theorem `fixed_cutoff_dirichlet_algebraic_of_supply` shows it is *sufficient*:
it yields the conclusion of `t.fixed.cutoff.Dirichlet.algebraic`
verbatim, with `alphaHom = theta / 4` exactly as the manuscript records

## Correspondence with 

The manuscript states the envelope for the rescaled field
`Ahat_L(x) = D_L⁻¹ a_L(3^L x)` on `cu_N`, with decay `3^(-theta_0 N / 2)`,
simultaneously for `r in {1,2}` and `s in {1/4,1/2}`.  The carrier below is the
same statement in the development's coordinates: the `3^L` dilation is absorbed by
reindexing `N` to `N - L`, so the field is the unrescaled `aCutoffFamily M L`
with normalizer `ahom M L` and the decay is
`fixedCutoffDirichletResponseWeight theta (N - L) = 3^(-theta (N-L) / 2)`.  Only
the two `(s, r)` pairs the downstream chain consumes are required, `(1/2, 1)`
and `(1/4, 2)`; the manuscript's other two pairs are not needed.  This is the
rendering the Dirichlet argument already fixed as its stop boundary.

`theta` is quantified **before** `M` and `L`, matching the manuscript's
dimension-only `theta_0(d)` and the requirement that `alphaHom` be
independent of `L`.

**This file introduces a hypothesis; it discharges nothing.**  It is not a
provider and must not be used as one.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal

noncomputable section

/-- **The AK.HC supply interface** — `e.fixed.cutoff.response.algebraic`
 in the development's coordinates.

A dimension-only `theta > 0` such that for every model, cutoff level and moment
exponent there is a nonnegative, coefficient-measurable response prefactor with
a finite `4q`-th moment which dominates both raw homogenization errors
simultaneously at every outer scale `N ≥ L`. -/
def FixedCutoffResponseSupply (d : ℕ) : Prop :=
  ∃ theta : ℝ, 0 < theta ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (q : ℝ), 1 ≤ q →
      ∃ (W : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) (B : ℝ), 0 ≤ B ∧
        (∀ omega, 0 ≤ W omega) ∧
        CoefficientMeasurable
          (fun omega ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega) W ∧
        eLpNorm W (ENNReal.ofReal (4 * q)) M.P.toMeasure ≤ ENNReal.ofReal B ∧
        (∀ᵐ omega ∂M.P.toMeasure, ∀ N : ℕ, L ≤ N →
          paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
              Section6Dirichlet.fixedCutoffDirichletS1 .infinity (.finite 1)
              (aCutoffFamily M L omega) (ahom M L) ≤
            ENNReal.ofReal (W omega *
              Section6Dirichlet.fixedCutoffDirichletResponseWeight theta (N - L)) ∧
          paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
              (Section6Dirichlet.fixedCutoffDirichletS1 / 2) .infinity (.finite 2)
              (aCutoffFamily M L omega) (ahom M L) ≤
            ENNReal.ofReal (W omega *
              Section6Dirichlet.fixedCutoffDirichletResponseWeight theta (N - L)))

/-- **The supply is sufficient.**

`FixedCutoffResponseSupply d` implies the conclusion of
`t.fixed.cutoff.Dirichlet.algebraic` verbatim.  The exponent is
`alphaHom = theta / 4`, and the required `2 ≤ d` is read off each model's
`shellPrefix.dimension`, which is legitimate because `theta` — hence
`alphaHom` — is fixed before `M`. -/
theorem fixed_cutoff_dirichlet_algebraic_of_supply
    (d : ℕ) [NeZero d] (hsupply : FixedCutoffResponseSupply d) :
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
                        (l2Size (originCube d 0) f + h.norm) := by
  obtain ⟨theta, htheta, hmain⟩ := hsupply
  refine ⟨theta / 4, by positivity, ?_⟩
  intro M L q hq
  have hd : 2 ≤ d := M.shellPrefix.dimension
  obtain ⟨Ccg, Cenergy, _hCcg, _hCenergy, hadapt⟩ :=
    Section6Dirichlet.exists_fixedCutoffDirichletConclusion_of_responseEnvelope d hd
  obtain ⟨W, B, hB, hWnonneg, hWmeas, hWnorm, henvelope⟩ := hmain M L q hq
  exact hadapt M L htheta hq hB W hWnonneg hWmeas hWnorm henvelope

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
