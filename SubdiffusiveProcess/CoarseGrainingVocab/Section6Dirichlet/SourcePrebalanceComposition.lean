import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PhysicalPrebalance
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourcePrebalanceArithmetic

/-!
# Source-scale composition of the cutoff Dirichlet prebalance estimate

This file substitutes the physical energy and positive fractional datum
prices into the coarse-graining prebalance theorem.  The result is the exact
optimizing-scale stochastic core times the unit-cube source size.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- The fully normalized deterministic prebalance row.  All PDE and dilation
carriers have been discharged; the remaining numerical inputs are the two
literal full responses and the coefficient-only ellipticity envelope. -/
theorem exists_cutoffDirichletSourcePrebalance
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Ccg : ℝ, 0 < Ccg ∧
      ∀ {Cenergy : ℝ}, 0 ≤ Cenergy →
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N k : ℕ), 0 < k →
        ∀ (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
          (s1 s s2 sEnergy : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 →
        ∀ {u v : H1Function (openCubeSet (originCube d 0))}
          (h : H2Datum (originCube d 0)) {f : Vec d → ℝ}
          (F : CubeVectorH1Function (originCube d 0))
          (hu : IsScalarDirichletSolutionOn
            (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
            (originCube d 0) u h.toH1 f)
          (_hv : IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
            (originCube d 0) v h.toH1 f)
          (hF : ∀ psi : H10Function (openCubeSet (originCube d 0)),
            ∫ x in openCubeSet (originCube d 0),
                f x * psi.toH1Function.toFun x ∂volume =
              -∫ x in openCubeSet (originCube d 0),
                vecDot (F.toField x) (psi.toH1Function.grad x) ∂volume),
        ∀ (E1 E2 sourceSize : ℝ), 0 ≤ E1 → 0 ≤ E2 → 0 ≤ sourceSize →
          paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ) s1.1
              .infinity (.finite 1) (aCutoffFamily M L omega) (ahom M L) ≤
            ENNReal.ofReal E1 →
          paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ) (s1.1 / 2)
              .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L) ≤
            ENNReal.ofReal E2 →
          dirichletForcedSolutionEnergyNorm
              (originCube d (N : ℤ)) (aCutoffFamily M L omega)
              (cutoffPhysicalDirichletForcedCubeSolution M L N omega F hu hF) ≤
            dirichletEllipticityEnvelope M L N s1.1 omega *
              Real.sqrt (ahom M L) * (centeredCubeScale (N : ℤ))⁻¹ *
                sourceDirichletEnergyDatumPrice Cenergy sEnergy F h →
          (unitCubeVectorH1ENormBudget F).toReal ≤
            unitDivergenceLiftConstant d * sourceSize →
          paperNegativeFractionalDual (originCube d 0) s
                FiniteLpExponent.two
                (scaledCenteredCubePullbackEuclideanL2Field (N : ℤ)
                  (centeredCubeScale (N : ℤ))
                  (centeredCubeGradientDifferenceL2Field (N : ℤ)
                    (centeredCubeRawDilation (N : ℤ) u)
                    (centeredCubeRawDilation (N : ℤ) v))) +
              paperNegativeFractionalDual (originCube d 0) s
                FiniteLpExponent.two
                (scaledCenteredCubePullbackEuclideanL2Field (N : ℤ)
                  (centeredCubeScale (N : ℤ) * (ahom M L)⁻¹)
                  (centeredCubeFluxDifferenceL2Field (N : ℤ)
                    ((aCutoffFamily M L omega).coeffOn (originCube d (N : ℤ)))
                    (ahom M L) (centeredCubeRawDilation (N : ℤ) u)
                    (centeredCubeRawDilation (N : ℤ) v))) ≤
            ENNReal.ofReal
              (sourceDirichletPrebalanceConstant Ccg s.1 s2.1
                  (dirichletWeightedEnergyFactor s1.1 s.1)
                  (sourceDirichletEnergyConstant d Cenergy sEnergy)
                  (sourceDirichletFractionalDatumConstant d s2) *
                dirichletPrebalanceCore s1.1 s2.1 k E1 E2
                  (dirichletEllipticityEnvelope M L N s1.1 omega) *
                (sourceSize + h.norm.toReal)) := by
  obtain ⟨Ccg, hCcg, hpre⟩ :=
    exists_cutoffDirichletPrebalance_of_response_energy_bounds d hd
  refine ⟨Ccg, hCcg, ?_⟩
  intro Cenergy hCenergy M L N k hk omega s1 s s2 sEnergy hs1s hss2
    u v h f F hu hv hF E1 E2 sourceSize hE1 hE2 hsource
    hresponseOne hresponseTwo henergy hbudget
  let Y := dirichletEllipticityEnvelope M L N s1.1 omega
  let G := sourceDirichletEnergyDatumPrice Cenergy sEnergy F h
  let W := dirichletWeightedEnergyFactor s1.1 s.1
  let D := sourceForcingFractionalConstant d s2 *
    (unitCubeVectorH1ENormBudget F).toReal
  let S := Y * Real.sqrt (ahom M L) *
    (centeredCubeScale (N : ℤ))⁻¹ * G
  have hY : 0 ≤ Y := zero_le_one.trans
    (one_le_dirichletEllipticityEnvelope M L N s1.1 omega)
  have hG : 0 ≤ G :=
    sourceDirichletEnergyDatumPrice_nonneg hCenergy sEnergy F h
  have hW : 0 ≤ W := dirichletWeightedEnergyFactor_nonneg s1.1 s.1
  have hD : 0 ≤ D := mul_nonneg
    (sourceForcingFractionalConstant_nonneg d s2) ENNReal.toReal_nonneg
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hY (Real.sqrt_nonneg _))
        (inv_nonneg.mpr (centeredCubeScale_pos (N : ℤ)).le)) hG
  have hdual := hpre M L N k hk omega s1 s s2 hs1s hss2
    h F hu hv hF E1 E2 S hE1 hE2 hS hresponseOne hresponseTwo henergy
  have hdatum : scaledVectorDatumFractionalBound (ahom M L) (N : ℤ) s2 F =
      (centeredCubeScale (N : ℤ)) ^ (-s2.1) *
        (ahom M L * (centeredCubeScale (N : ℤ))⁻¹) * D := by
    rw [scaledVectorDatumFractionalBound_eq_sourceDatum,
      abs_of_pos (ahom_pos M L)]
    dsimp only [D]
    ring
  rw [hdatum] at hdual
  have hphysical := physicalDirichletPrebalanceRHS_eq_source
    (ahom_pos M L) N k Ccg s.1 s1.1 s2.1 E1 E2 W Y G D
  have hH : 0 ≤ sourceSize + h.norm.toReal :=
    add_nonneg hsource ENNReal.toReal_nonneg
  have hGprice : G ≤ sourceDirichletEnergyConstant d Cenergy sEnergy *
      (sourceSize + h.norm.toReal) := by
    dsimp only [G]
    exact sourceDirichletEnergyDatumPrice_le_sourceSizes
      hCenergy sEnergy F h hsource hbudget
  have hDprice : D ≤ sourceDirichletFractionalDatumConstant d s2 *
      (sourceSize + h.norm.toReal) := by
    dsimp only [D, sourceDirichletFractionalDatumConstant]
    calc
      sourceForcingFractionalConstant d s2 *
          (unitCubeVectorH1ENormBudget F).toReal ≤
        sourceForcingFractionalConstant d s2 *
          (unitDivergenceLiftConstant d * sourceSize) :=
        mul_le_mul_of_nonneg_left hbudget
          (sourceForcingFractionalConstant_nonneg d s2)
      _ = (sourceForcingFractionalConstant d s2 *
          unitDivergenceLiftConstant d) * sourceSize := by ring
      _ ≤ (sourceForcingFractionalConstant d s2 *
          unitDivergenceLiftConstant d) *
            (sourceSize + h.norm.toReal) :=
        mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right ENNReal.toReal_nonneg)
          (sourceDirichletFractionalDatumConstant_nonneg d s2)
  have hreal := sourceDirichletPrebalanceRHS_le_constant_mul_core_mul
    (C := Ccg) (s := s.1) (s1 := s1.1) (s2 := s2.1)
    (E1 := E1) (E2 := E2) (W := W) (Y := Y) (G := G) (D := D)
    (CG := sourceDirichletEnergyConstant d Cenergy sEnergy)
    (CD := sourceDirichletFractionalDatumConstant d s2)
    (H := sourceSize + h.norm.toReal) (k := k)
    hCcg.le s.2.1 hss2 hE1 hW hY
    (sourceDirichletEnergyConstant_nonneg d hCenergy sEnergy)
    (sourceDirichletFractionalDatumConstant_nonneg d s2)
    hH hGprice hDprice
  refine hdual.trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [show cutoffDirichletWeightedEnergyBound s1.1 s.1 S = W * S by rfl]
  change centeredCubeScale (N : ℤ) * (ahom M L)⁻¹ *
      dirichletCoarseGrainingRHS Ccg (ahom M L) s.1 s2.1
        (Real.rpow 3 (s1.1 * (k : ℝ)) * E1)
        (Real.rpow 3 ((s1.1 / 2) * (k : ℝ)) * E2)
        (W * (Y * Real.sqrt (ahom M L) *
          (centeredCubeScale (N : ℤ))⁻¹ * G))
        ((centeredCubeScale (N : ℤ)) ^ (-s2.1) *
          (ahom M L * (centeredCubeScale (N : ℤ))⁻¹) * D)
        ((N : ℤ) - (k : ℤ)) ≤ _
  rw [hphysical]
  exact hreal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
