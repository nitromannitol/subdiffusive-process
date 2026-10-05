module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PhysicalPrebalance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourceEnergyPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourcePrebalanceArithmetic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ZeroSourceArithmetic

@[expose] public section

/-!
# Physical zero-source Dirichlet prebalance
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- Reapply physical coarse graining at one scale with the zero divergence
lift.  The positive fractional-datum slot vanishes before source-price
aggregation, leaving only the linear first response. -/
theorem exists_cutoffDirichletZeroSourcePrebalance
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Ccg : ℝ, 0 < Ccg ∧
      ∀ {Cenergy : ℝ}, 0 ≤ Cenergy →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (s1 s s2 sEnergy : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 →
      ∀ {u v : H1Function (openCubeSet (originCube d 0))}
        (h : H2Datum (originCube d 0))
        (hu : IsScalarDirichletSolutionOn
          (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
          (originCube d 0) u h.toH1 0)
        (_hv : IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
          (originCube d 0) v h.toH1 0)
        (_henergy : ∀ (F : CubeVectorH1Function (originCube d 0)),
          ∀ hF : (∀ psi : H10Function (openCubeSet (originCube d 0)),
            ∫ x in openCubeSet (originCube d 0),
                (0 : Vec d → ℝ) x * psi.toH1Function.toFun x ∂volume =
              -∫ x in openCubeSet (originCube d 0),
                vecDot (F.toField x) (psi.toH1Function.grad x) ∂volume),
          dirichletForcedSolutionEnergyNorm
              (originCube d (N : ℤ)) (aCutoffFamily M L omega)
              (cutoffPhysicalDirichletForcedCubeSolution M L N omega F hu hF) ≤
            dirichletEllipticityEnvelope M L N s1.1 omega *
              Real.sqrt (ahom M L) * (centeredCubeScale (N : ℤ))⁻¹ *
                sourceDirichletEnergyDatumPrice Cenergy sEnergy F h),
      ∀ E1 E2 : ℝ, 0 ≤ E1 → 0 ≤ E2 →
        paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ) s1.1
            .infinity (.finite 1) (aCutoffFamily M L omega) (ahom M L) ≤
          ENNReal.ofReal E1 →
        paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ) (s1.1 / 2)
            .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L) ≤
          ENNReal.ofReal E2 →
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
              (Real.rpow 3 s1.1 * E1 *
                dirichletEllipticityEnvelope M L N s1.1 omega) *
              h.norm.toReal) := by
  obtain ⟨Ccg, hCcg, hpre⟩ :=
    exists_cutoffDirichletPrebalance_of_response_energy_bounds d hd
  refine ⟨Ccg, hCcg, ?_⟩
  intro Cenergy hCenergy M L N omega s1 s s2 sEnergy hs1s hss2
    u v h hu _hv _henergy E1 E2 hE1 hE2 hresponseOne hresponseTwo
  have hfzero : MemLp (0 : Vec d → ℝ) 2
      (volume.restrict (openCubeSet (originCube d 0))) :=
    MeasureTheory.MemLp.zero
  obtain ⟨F, hF, hbudgetRaw⟩ :=
    exists_unitDivergenceLift_with_real_budget d (0 : Vec d → ℝ) hfzero
  have hzeroL2 : toScalarL2 hfzero = 0 := by
    simp [toScalarL2]
  have hbudget : (unitCubeVectorH1ENormBudget F).toReal ≤
      unitDivergenceLiftConstant d * 0 := by
    simpa only [hzeroL2, norm_zero] using hbudgetRaw
  have hbudgetEq : (unitCubeVectorH1ENormBudget F).toReal = 0 :=
    le_antisymm (by simpa only [mul_zero] using hbudget) ENNReal.toReal_nonneg
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
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hY (Real.sqrt_nonneg _))
        (inv_nonneg.mpr (centeredCubeScale_pos (N : ℤ)).le)) hG
  have hdual := hpre M L N 1 (by omega) omega s1 s s2 hs1s hss2
    h F hu _hv hF E1 E2 S hE1 hE2 hS hresponseOne hresponseTwo
      (_henergy F hF)
  have hDzero : D = 0 := by
    simp only [D, hbudgetEq, mul_zero]
  have hdatum : scaledVectorDatumFractionalBound (ahom M L) (N : ℤ) s2 F =
      (centeredCubeScale (N : ℤ)) ^ (-s2.1) *
        (ahom M L * (centeredCubeScale (N : ℤ))⁻¹) * D := by
    rw [scaledVectorDatumFractionalBound_eq_sourceDatum,
      abs_of_pos (ahom_pos M L), hbudgetEq, hDzero]
    simp
  rw [hdatum] at hdual
  have hphysical := physicalDirichletPrebalanceRHS_eq_source
    (ahom_pos M L) N 1 Ccg s.1 s1.1 s2.1 E1 E2 W Y G D
  have hGprice : G ≤ sourceDirichletEnergyConstant d Cenergy sEnergy *
      h.norm.toReal := by
    have := sourceDirichletEnergyDatumPrice_le_sourceSizes
      hCenergy sEnergy F h (show (0 : ℝ) ≤ 0 by rfl) hbudget
    simpa only [zero_add] using this
  have hreal := sourceDirichletPrebalanceRHS_zeroDatum_le
    (C := Ccg) (s := s.1) (s1 := s1.1) (s2 := s2.1)
    (E1 := E1) (E2 := E2) (W := W) (Y := Y) (G := G)
    (CG := sourceDirichletEnergyConstant d Cenergy sEnergy)
    (CD := sourceDirichletFractionalDatumConstant d s2)
    (H := h.norm.toReal) (k := 1)
    hCcg.le s.2.1 hss2 hE1 hW hY
    (sourceDirichletFractionalDatumConstant_nonneg d s2)
    ENNReal.toReal_nonneg hGprice
  refine hdual.trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [show cutoffDirichletWeightedEnergyBound s1.1 s.1 S = W * S by rfl]
  dsimp only [S]
  rw [hphysical, hDzero]
  simpa only [Nat.cast_one, mul_one] using hreal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
