module

public import SubdiffusiveProcess.Section6.UniformResponseSupply
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FixedCutoffConditionalConclusion

@[expose] public section

/-!
# Model-uniform fixed-cutoff homogenization

`fixed_cutoff_dirichlet_algebraic_uniform` compares Dirichlet solutions on
the open unit cube for `L²` forcing and `H²` boundary data. It supplies existence,
a.e. uniqueness and algebraic decay in the scale gap. The deterministic moment
constant is chosen at fixed dimension, cutoff `L`, moment order `q ≥ 1` and
disorder strength, before the model. The response supply is then instantiated
for each model, so uniformity is part of the existential quantifier order.
`SubdiffusiveProcess.Paper.t_B` pairs this clause with the small-disorder estimate.
-/
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab hiding TriadicCube Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section6

/-- Theorem t.fixed.cutoff.Dirichlet.algebraic with its uniform constant. -/
theorem fixed_cutoff_dirichlet_algebraic_uniform (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ alphaHom : ℝ, 0 < alphaHom ∧
           ∀ L : ℕ, ∀ q : ℝ, 1 ≤ q → ∀ delta : ℝ,
             ∃ C : ℝ, 0 < C ∧
               ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta = delta →
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
  obtain ⟨theta, htheta, hmain⟩ := exists_law_uniform_response_supply d
  obtain ⟨Ccg, Cenergy, hCcg, hCenergy, hassembly⟩ :=
    exists_fixedCutoffDirichletAlmostSureAssembly d hd
  refine ⟨theta / 4, by positivity, ?_⟩
  intro L q hq delta
  obtain ⟨B, hB, hsupply⟩ := hmain L q hq delta
  let Csource := fixedCutoffDirichletSourceCoefficient d Ccg Cenergy
  let C := 1 +
    (dirichletFinalReadoutConstant fixedCutoffDirichletSOrder d).toReal * Csource *
      ((1 + 2 * fixedCutoffDirichletBalanceConstant) * (1 + B) ^ (4 : ℕ))
  refine ⟨C, ?_, ?_⟩
  · have hCsource : 0 ≤ Csource := by
      exact fixedCutoffDirichletSourceCoefficient_nonneg hCcg.le hCenergy.le
    have hreadout : 0 ≤
        (dirichletFinalReadoutConstant fixedCutoffDirichletSOrder d).toReal :=
      ENNReal.toReal_nonneg
    have hbalance : 0 ≤ 1 + 2 * fixedCutoffDirichletBalanceConstant := by
      linarith [fixedCutoffDirichletBalanceConstant_pos]
    have hBpow : 0 ≤ (1 + B) ^ (4 : ℕ) := by positivity
    dsimp only [C]
    positivity
  · intro M hdelta
    obtain ⟨W, hW, hWMeas, hWNorm, hresponse⟩ := hsupply M hdelta
    let Y := fixedCutoffDirichletFinalRandomFactor d Csource W
    have hassembled := hassembly M L htheta.le hq hB W hW hWMeas hWNorm hresponse
    dsimp only at hassembled
    refine ⟨Y, hassembled.1, hassembled.2.1, ?_, ?_⟩
    · simpa only [C, Y] using hassembled.2.2.1
    · filter_upwards [hassembled.2.2.2] with omega homega
      intro N hLN f hf h
      refine ⟨(cutoffDirichlet_wellPosed M L N omega f hf h).1,
        (cutoffDirichlet_wellPosed M L N omega f hf h).2.1,
        (cutoffDirichlet_wellPosed M L N omega f hf h).2.2.1,
        (cutoffDirichlet_wellPosed M L N omega f hf h).2.2.2, ?_⟩
      intro uLM uHom huLM huHom
      have hreadout := homega N hLN f hf h uLM uHom huLM huHom
      simpa only [Y, Csource, fixedCutoffDirichletTargetWeight,
        fixedCutoffDirichletTargetWeight_eq_gap hLN] using! hreadout

end SubdiffusiveProcess.Section6
