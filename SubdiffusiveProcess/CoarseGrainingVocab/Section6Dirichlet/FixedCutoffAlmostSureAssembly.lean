module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FixedCutoffResponseMoment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourceEnergyPrice

@[expose] public section

/-!
# Almost-sure fixed-cutoff Dirichlet assembly

This file packages every local consequence of a simultaneous fixed-cutoff
response envelope.  The envelope itself remains the sole external analytic
input and is not promoted to a provider premise here.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private theorem coefficientSigma_aCutoff_le_ambient
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    coefficientSigma (fun omega ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) ≤
      (inferInstance : MeasurableSpace (Sample d)) := by
  unfold coefficientSigma
  refine iSup_le fun x ↦ ?_
  exact (SubdiffusiveProcess.Frozen.Assumptions.measurable_aCutoff M L x).comap_le

/-- A common algebraic response envelope implies the complete fixed-cutoff
Dirichlet conclusion at every outer scale, with one common random factor. -/
theorem exists_fixedCutoffDirichletAlmostSureAssembly
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Ccg Cenergy : ℝ, 0 < Ccg ∧ 0 < Cenergy ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        {theta q B : ℝ}, 0 ≤ theta → 1 ≤ q → 0 ≤ B →
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
        let Csource := fixedCutoffDirichletSourceCoefficient d Ccg Cenergy
        CoefficientMeasurable
            (fun omega ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (fixedCutoffDirichletFinalRandomFactor d Csource W) ∧
          (∀ omega, 1 ≤
            fixedCutoffDirichletFinalRandomFactor d Csource W omega) ∧
          eLpNorm (fixedCutoffDirichletFinalRandomFactor d Csource W)
              (ENNReal.ofReal q) M.P.toMeasure ≤
            ENNReal.ofReal
              (1 + (dirichletFinalReadoutConstant
                    fixedCutoffDirichletSOrder d).toReal * Csource *
                ((1 + 2 * fixedCutoffDirichletBalanceConstant) *
                  (1 + B) ^ (4 : ℕ))) ∧
          ∀ᵐ omega ∂M.P.toMeasure, ∀ N : ℕ, L ≤ N →
            ∀ (f : Vec d → ℝ)
              (_hf : MemLp f 2 (volume.restrict
                (openCubeSet (originCube d 0))))
              (h : H2Datum (originCube d 0))
              (u v : H1Function (openCubeSet (originCube d 0))),
              IsScalarDirichletSolutionOn
                  (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                  (originCube d 0) u h.toH1 f →
              IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                  (originCube d 0) v h.toH1 f →
              ∃ gradDifference fluxDifference : L2VectorField (originCube d 0),
                (∀ x, gradDifference.toFun x = u.grad x - v.grad x) ∧
                (∀ x, fluxDifference.toFun x =
                  rescaledCutoffCoefficient M L N omega x • u.grad x - v.grad x) ∧
                l2Size (originCube d 0) (fun x ↦ u.toFun x - v.toFun x) +
                      ordinaryVectorHMinusOne (originCube d 0) gradDifference +
                    ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
                  ENNReal.ofReal
                      (fixedCutoffDirichletFinalRandomFactor d Csource W omega *
                        fixedCutoffDirichletTargetWeight theta (N - L)) *
                    (l2Size (originCube d 0) f + h.norm) := by
  obtain ⟨Ccg, hCcg, hconditional⟩ :=
    exists_fixedCutoffDirichletConditionalReadout d hd
  obtain ⟨Cenergy, hCenergy, henergy⟩ :=
    exists_ae_cutoffPhysicalDirichletEnergy_le_sourcePrice d
  refine ⟨Ccg, Cenergy, hCcg, hCenergy, ?_⟩
  intro M L theta q B htheta hq hB W hW hWCoefficient hWNorm hresponse
  let Csource := fixedCutoffDirichletSourceCoefficient d Ccg Cenergy
  have hCsource : 0 ≤ Csource := by
    dsimp only [Csource]
    exact fixedCutoffDirichletSourceCoefficient_nonneg hCcg.le hCenergy.le
  have hWAmbient : Measurable W :=
    hWCoefficient.mono (coefficientSigma_aCutoff_le_ambient M L) le_rfl
  have hWStrong : AEStronglyMeasurable W M.P.toMeasure :=
    hWAmbient.aestronglyMeasurable
  refine ⟨coefficientMeasurable_fixedCutoffDirichletFinalRandomFactor
      (fun omega ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) Csource hWCoefficient,
    one_le_fixedCutoffDirichletFinalRandomFactor hCsource hW,
    eLpNorm_fixedCutoffDirichletFinalRandomFactor_le hCsource hq hB hW
      hWStrong hWNorm, ?_⟩
  rw [ae_all_iff]
  intro N
  by_cases hscale : L ≤ N
  · have hresponseN : ∀ᵐ omega ∂M.P.toMeasure,
        paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
              fixedCutoffDirichletS1 .infinity (.finite 1)
              (aCutoffFamily M L omega) (ahom M L) ≤
            ENNReal.ofReal
              (W omega * fixedCutoffDirichletResponseWeight theta (N - L)) ∧
          paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
              (fixedCutoffDirichletS1 / 2) .infinity (.finite 2)
              (aCutoffFamily M L omega) (ahom M L) ≤
            ENNReal.ofReal
              (W omega * fixedCutoffDirichletResponseWeight theta (N - L)) :=
      hresponse.mono fun omega homega ↦ homega N hscale
    have hTwoMoment : paperENNRealLpNorm M.P.toMeasure (4 * q)
        (fun omega ↦ paperHomogenizationError
          (originCube d (N : ℤ)) (N : ℤ) (fixedCutoffDirichletS1 / 2)
          .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L)) ≤
        ENNReal.ofReal B := by
      refine (paperENNRealLpNorm_le_responsePrefactor
        (by nlinarith : 0 < 4 * q) htheta (N - L) hW
        (hresponseN.mono fun _ homega ↦ homega.2)).trans ?_
      exact hWNorm
    have henergyN := henergy M L N fixedCutoffDirichletS1Order
      fixedCutoffDirichletS2Order
      (fixedCutoffDirichletS1Order_lt_fixedCutoffDirichletSOrder.trans
        fixedCutoffDirichletSOrder_lt_fixedCutoffDirichletS2Order)
      (by nlinarith : 0 < 4 * q) hTwoMoment
    filter_upwards [hresponseN, henergyN] with omega hresponseOmega henergyOmega
    intro _hLN f hf h u v hu hv
    exact hconditional hCenergy.le M L N htheta W hW omega
      hresponseOmega.1 hresponseOmega.2 henergyOmega f hf h u v hu hv
  · exact Filter.Eventually.of_forall fun _ hLNFalse ↦
      False.elim (hscale hLNFalse)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
