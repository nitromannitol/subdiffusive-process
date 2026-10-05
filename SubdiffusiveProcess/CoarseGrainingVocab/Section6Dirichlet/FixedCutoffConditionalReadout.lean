module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FixedCutoffFinalFactor
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.CanonicalFinalReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourceForcingPrice

@[expose] public section

/-!
# Conditional fixed-cutoff Dirichlet readout

This module composes the physical prebalance theorem with the fixed-cutoff
integer balance and final spectral readout.  Its response and energy
hypotheses are pointwise conclusions intended to be discharged on one common
almost-sure event once the simultaneous response envelope is available.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- One-scale PDE and readout composition downstream of a simultaneous
fixed-cutoff response estimate. -/
theorem exists_fixedCutoffDirichletConditionalReadout
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Ccg : ℝ, 0 < Ccg ∧
      ∀ {Cenergy : ℝ}, 0 ≤ Cenergy →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
        {theta : ℝ}, 0 ≤ theta →
      ∀ (W : Sample d → ℝ), (∀ omega, 0 ≤ W omega) →
      ∀ (omega : Sample d),
        paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
            fixedCutoffDirichletS1 .infinity (.finite 1)
            (aCutoffFamily M L omega) (ahom M L) ≤
          ENNReal.ofReal
            (W omega * fixedCutoffDirichletResponseWeight theta (N - L)) →
        paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
            (fixedCutoffDirichletS1 / 2) .infinity (.finite 2)
            (aCutoffFamily M L omega) (ahom M L) ≤
          ENNReal.ofReal
            (W omega * fixedCutoffDirichletResponseWeight theta (N - L)) →
        (∀ {u : H1Function (openCubeSet (originCube d 0))}
          (h : H2Datum (originCube d 0)) {f : Vec d → ℝ}
          (F : CubeVectorH1Function (originCube d 0))
          (hu : IsScalarDirichletSolutionOn
            (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
            (originCube d 0) u h.toH1 f)
          (hF : ∀ psi : H10Function (openCubeSet (originCube d 0)),
            ∫ x in openCubeSet (originCube d 0),
                f x * psi.toH1Function.toFun x ∂volume =
              -∫ x in openCubeSet (originCube d 0),
                vecDot (F.toField x) (psi.toH1Function.grad x) ∂volume),
          dirichletForcedSolutionEnergyNorm
              (originCube d (N : ℤ)) (aCutoffFamily M L omega)
              (cutoffPhysicalDirichletForcedCubeSolution M L N omega F hu hF) ≤
            dirichletEllipticityEnvelope M L N fixedCutoffDirichletS1 omega *
              Real.sqrt (ahom M L) * (centeredCubeScale (N : ℤ))⁻¹ *
                sourceDirichletEnergyDatumPrice Cenergy
                  fixedCutoffDirichletS1Order F h) →
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
                  (fixedCutoffDirichletFinalRandomFactor d
                    (fixedCutoffDirichletSourceCoefficient d Ccg Cenergy) W omega *
                    fixedCutoffDirichletTargetWeight theta (N - L)) *
                (l2Size (originCube d 0) f + h.norm) := by
  obtain ⟨Ccg, hCcg, hprebalance⟩ :=
    exists_cutoffDirichletSourcePrebalance d hd
  refine ⟨Ccg, hCcg, ?_⟩
  intro Cenergy hCenergy M L N theta htheta W hW omega hrawOne hrawTwo
    henergy f hf h u v hu hv
  let E1 := dirichletFullResponseOne M L N fixedCutoffDirichletS1 omega
  let E2 := dirichletFullResponseTwo M L N fixedCutoffDirichletS1 omega
  let R := fixedCutoffDirichletResponseWeight theta (N - L)
  let k := fixedCutoffDirichletBalanceScale theta (N - L)
  let Csource := fixedCutoffDirichletSourceCoefficient d Ccg Cenergy
  let D := ‖toScalarL2 hf‖ + h.norm.toReal
  have hR : 0 ≤ R := Real.rpow_nonneg (by norm_num) _
  have hWR : 0 ≤ W omega * R := mul_nonneg (hW omega) hR
  have hOneTop : paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
      fixedCutoffDirichletS1 .infinity (.finite 1)
      (aCutoffFamily M L omega) (ahom M L) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hrawOne
  have hTwoTop : paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
      (fixedCutoffDirichletS1 / 2) .infinity (.finite 2)
      (aCutoffFamily M L omega) (ahom M L) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hrawTwo
  have hOneEq : paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
      fixedCutoffDirichletS1 .infinity (.finite 1)
      (aCutoffFamily M L omega) (ahom M L) = ENNReal.ofReal E1 := by
    exact (ENNReal.ofReal_toReal hOneTop).symm
  have hTwoEq : paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
      (fixedCutoffDirichletS1 / 2) .infinity (.finite 2)
      (aCutoffFamily M L omega) (ahom M L) = ENNReal.ofReal E2 := by
    exact (ENNReal.ofReal_toReal hTwoTop).symm
  have hE1 : 0 ≤ E1 := dirichletFullResponseOne_nonneg M L N _ omega
  have hE2 : 0 ≤ E2 := dirichletFullResponseTwo_nonneg M L N _ omega
  have hE1Response : E1 ≤ W omega * R := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hrawOne).trans_eq
      (ENNReal.toReal_ofReal hWR)
  have hE2Response : E2 ≤ W omega * R := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hrawTwo).trans_eq
      (ENNReal.toReal_ofReal hWR)
  have hk : 0 < k := fixedCutoffDirichletBalanceScale_pos theta (N - L)
  obtain ⟨F, hF, hbudget⟩ := exists_unitDivergenceLift_with_real_budget d f hf
  have hsource : 0 ≤ ‖toScalarL2 hf‖ := norm_nonneg _
  have hpre := hprebalance (Cenergy := Cenergy) hCenergy
    M L N k hk omega fixedCutoffDirichletS1Order
    fixedCutoffDirichletSOrder fixedCutoffDirichletS2Order
    fixedCutoffDirichletS1Order
    fixedCutoffDirichletS1Order_lt_fixedCutoffDirichletSOrder
    fixedCutoffDirichletSOrder_lt_fixedCutoffDirichletS2Order
    h F hu hv hF E1 E2 ‖toScalarL2 hf‖ hE1 hE2 hsource
    (hOneEq.trans_le le_rfl) (hTwoEq.trans_le le_rfl)
    (henergy h F hu hF) hbudget
  have hcore := dirichletPrebalanceCore_le_fixedCutoffDirichletRandomFactor_mul
    (W := W)
    (E1 := dirichletFullResponseOne M L N fixedCutoffDirichletS1)
    (E2 := dirichletFullResponseTwo M L N fixedCutoffDirichletS1)
    (N - L) omega htheta (hW omega) hE2 hE1Response hE2Response
  have hCsource : 0 ≤ Csource := by
    dsimp only [Csource]
    exact fixedCutoffDirichletSourceCoefficient_nonneg hCcg.le hCenergy
  have hD : 0 ≤ D := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hT : 0 ≤ fixedCutoffDirichletTargetWeight theta (N - L) :=
    Real.rpow_nonneg (by norm_num) _
  have hbalanced :
      paperNegativeFractionalDual (originCube d 0) fixedCutoffDirichletSOrder
            FiniteLpExponent.two
            (scaledCenteredCubePullbackEuclideanL2Field (N : ℤ)
              (centeredCubeScale (N : ℤ))
              (centeredCubeGradientDifferenceL2Field (N : ℤ)
                (centeredCubeRawDilation (N : ℤ) u)
                (centeredCubeRawDilation (N : ℤ) v))) +
          paperNegativeFractionalDual (originCube d 0) fixedCutoffDirichletSOrder
            FiniteLpExponent.two
            (scaledCenteredCubePullbackEuclideanL2Field (N : ℤ)
              (centeredCubeScale (N : ℤ) * (ahom M L)⁻¹)
              (centeredCubeFluxDifferenceL2Field (N : ℤ)
                ((aCutoffFamily M L omega).coeffOn (originCube d (N : ℤ)))
                (ahom M L) (centeredCubeRawDilation (N : ℤ) u)
                (centeredCubeRawDilation (N : ℤ) v))) ≤
        ENNReal.ofReal
          (Csource * fixedCutoffDirichletRandomFactor W omega *
            fixedCutoffDirichletTargetWeight theta (N - L) * D) := by
    refine hpre.trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hmul := mul_le_mul_of_nonneg_left hcore hCsource
    have hmulD := mul_le_mul_of_nonneg_right hmul hD
    dsimp only [Csource, E1, E2, D] at hpre ⊢
    simp only [dirichletEllipticityEnvelope] at hpre
    simpa [fixedCutoffDirichletBalanceConstant, R, k, mul_assoc] using! hmulD
  have hU : 0 ≤ Csource * fixedCutoffDirichletRandomFactor W omega :=
    mul_nonneg hCsource
      (zero_le_one.trans (one_le_fixedCutoffDirichletRandomFactor hW omega))
  have hfinal := exists_cutoffDirichletDifferenceFields_of_balancedPrebalance
    M L N omega fixedCutoffDirichletSOrder u v
    (hasH10Difference_of_scalarDirichletSolutions hu hv)
    hU hT hD hbalanced
  simpa only [Csource, D, fixedCutoffDirichletFinalRandomFactor,
    ofReal_norm_toScalarL2_add_h2DatumNorm_toReal] using hfinal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
