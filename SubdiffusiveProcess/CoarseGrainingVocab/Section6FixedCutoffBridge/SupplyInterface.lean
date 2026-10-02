import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FixedCutoffConditionalConclusion




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal

noncomputable section



def FixedCutoffResponseSupply (d : ℕ) : Prop :=
  ∃ theta : ℝ, 0 < theta ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (q : ℝ), 1 ≤ q →
      ∃ (W : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ) (B : ℝ), 0 ≤ B ∧
        (∀ omega, 0 ≤ W omega) ∧
        CoefficientMeasurable
          (fun omega ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) W ∧
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

`FixedCutoffResponseSupply d` implies the frozen conclusion of
`t.fixed.cutoff.Dirichlet.algebraic` verbatim.  The exponent is
`alphaHom = theta / 4`, and the required `2 ≤ d` is read off each model's
`shellPrefix.dimension`, which is legitimate because `theta` — hence
`alphaHom` — is fixed before `M`. -/
theorem fixed_cutoff_dirichlet_algebraic_of_supply
    (d : ℕ) [NeZero d] (hsupply : FixedCutoffResponseSupply d) :
    ∃ alphaHom : ℝ, 0 < alphaHom ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ L : ℕ, ∀ q : ℝ, 1 ≤ q →
        ∃ C : ℝ, 0 < C ∧
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
