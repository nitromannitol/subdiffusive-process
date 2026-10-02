import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FixedCutoffAlmostSureAssembly
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.RescaledCoefficientEllipticity




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory
open Homogenization hiding Vec
open Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- A simultaneous raw fixed-cutoff response envelope implies the exact
one-cutoff conclusion, including samplewise well-posedness.  The theorem is
kept internal to the support layer so that the missing response construction
does not become a provider premise. -/
theorem exists_fixedCutoffDirichletConclusion_of_responseEnvelope
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Ccg Cenergy : ℝ, 0 < Ccg ∧ 0 < Cenergy ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        {theta q B : ℝ}, 0 < theta → 1 ≤ q → 0 ≤ B →
      ∀ (W : Sample d → ℝ), (∀ omega, 0 ≤ W omega) →
        CoefficientMeasurable
          (fun omega ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) W →
        eLpNorm W (ENNReal.ofReal (4 * q)) M.P.toMeasure ≤ ENNReal.ofReal B →
        (∀ᵐ omega ∂M.P.toMeasure, ∀ N : ℕ, L ≤ N →
          paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
              fixedCutoffDirichletS1 .infinity (.finite 1)
              (aCutoffFamily M L omega) (ahom M L) ≤
            ENNReal.ofReal
              (W omega * fixedCutoffDirichletResponseWeight theta (N - L)) ∧
          paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
              (fixedCutoffDirichletS1 / 2) .infinity (.finite 2)
              (aCutoffFamily M L omega) (ahom M L) ≤
            ENNReal.ofReal
              (W omega * fixedCutoffDirichletResponseWeight theta (N - L))) →
        ∃ C : ℝ, 0 < C ∧
          ∃ Y : Sample d → ℝ,
          CoefficientMeasurable
              (fun omega ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) Y ∧
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
                  uLM.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))]
                      uLM'.toFun ∧
                    uLM.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))]
                      uLM'.grad) ∧
                (∃ uHom : H1Function (openCubeSet (originCube d 0)),
                  IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                    (originCube d 0) uHom h.toH1 f) ∧
                (∀ uHom uHom' : H1Function (openCubeSet (originCube d 0)),
                  IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                      (originCube d 0) uHom h.toH1 f →
                  IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                      (originCube d 0) uHom' h.toH1 f →
                  uHom.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))]
                      uHom'.toFun ∧
                    uHom.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))]
                      uHom'.grad) ∧
                ∀ (uLM uHom : H1Function (openCubeSet (originCube d 0))),
                  IsScalarDirichletSolutionOn
                      (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                      (originCube d 0) uLM h.toH1 f →
                  IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                      (originCube d 0) uHom h.toH1 f →
                  ∃ gradDifference fluxDifference : L2VectorField (originCube d 0),
                    (∀ x, gradDifference.toFun x = uLM.grad x - uHom.grad x) ∧
                    (∀ x, fluxDifference.toFun x =
                      rescaledCutoffCoefficient M L N omega x • uLM.grad x -
                        uHom.grad x) ∧
                    l2Size (originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                          ordinaryVectorHMinusOne (originCube d 0) gradDifference +
                        ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
                      ENNReal.ofReal
                          (Y omega * (3 : ℝ) ^
                            (-(theta / 4) * ((N : ℝ) - (L : ℝ)))) *
                        (l2Size (originCube d 0) f + h.norm) := by
  obtain ⟨Ccg, Cenergy, hCcg, hCenergy, hassembly⟩ :=
    exists_fixedCutoffDirichletAlmostSureAssembly d hd
  refine ⟨Ccg, Cenergy, hCcg, hCenergy, ?_⟩
  intro M L theta q B htheta hq hB W hW hWMeas hWNorm hresponse
  let Csource := fixedCutoffDirichletSourceCoefficient d Ccg Cenergy
  let C := 1 +
    (dirichletFinalReadoutConstant fixedCutoffDirichletSOrder d).toReal * Csource *
      ((1 + 2 * fixedCutoffDirichletBalanceConstant) * (1 + B) ^ (4 : ℕ))
  let Y := fixedCutoffDirichletFinalRandomFactor d Csource W
  have hassembled := hassembly M L htheta.le hq hB W hW hWMeas hWNorm hresponse
  dsimp only at hassembled
  refine ⟨C, ?_, Y, hassembled.1, hassembled.2.1, ?_, ?_⟩
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
  · simpa only [C, Y] using hassembled.2.2.1
  · filter_upwards [hassembled.2.2.2] with omega homega
    intro N hLN f hf h
    refine ⟨(cutoffDirichlet_wellPosed M L N omega f hf h).1,
      (cutoffDirichlet_wellPosed M L N omega f hf h).2.1,
      (cutoffDirichlet_wellPosed M L N omega f hf h).2.2.1,
      (cutoffDirichlet_wellPosed M L N omega f hf h).2.2.2, ?_⟩
    intro uLM uHom huLM huHom
    have hreadout := homega N hLN f hf h uLM uHom huLM huHom
    simpa only [Y, fixedCutoffDirichletTargetWeight,
      fixedCutoffDirichletTargetWeight_eq_gap hLN] using hreadout

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
